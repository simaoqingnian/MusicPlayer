package com.musicplayer.app;

import android.app.Activity;
import android.Manifest;
import android.content.ComponentName;
import android.content.Context;
import android.content.Intent;
import android.content.ServiceConnection;
import android.content.SharedPreferences;
import android.content.pm.PackageManager;
import android.content.res.ColorStateList;
import android.database.Cursor;
import android.graphics.Color;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.graphics.drawable.StateListDrawable;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.IBinder;
import android.os.Looper;
import android.provider.DocumentsContract;
import android.provider.Settings;
import android.text.TextUtils;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.view.ViewParent;
import android.widget.LinearLayout;
import android.widget.ImageView;
import android.widget.ScrollView;
import android.widget.SeekBar;
import android.widget.TextView;
import android.widget.Toast;

import org.json.JSONArray;
import org.json.JSONException;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;

public class MainActivity extends Activity {
    private static final int REQUEST_OPEN_TREE = 1001;
    private static final int REQUEST_READ_STORAGE = 1002;
    private static final int REQUEST_POST_NOTIFICATIONS = 1003;

    private static final String PREFS_NAME = "musicplayer";
    private static final String PREF_ACCESS_MODE = "access_mode";
    private static final String ACCESS_MODE_SAF = "saf";
    private static final String ACCESS_MODE_FILE = "file";
    private static final String PREF_ROOT_TREE_URI = "root_tree_uri";
    private static final String PREF_ROOT_DOC_ID = "root_doc_id";
    private static final String PREF_NAV_DOC_IDS = "nav_doc_ids";
    private static final String PREF_NAV_NAMES = "nav_names";
    private static final String PREF_FILE_ROOT_PATH = "file_root_path";
    private static final String PREF_FILE_CURRENT_PATH = "file_current_path";
    private static final String PREF_SLEEP_MINUTES = "sleep_minutes";
    private static final int[] SLEEP_OPTIONS_MINUTES = {30, 60, 90, 120};

    private static final int COLOR_BACKGROUND = Color.rgb(245, 247, 250);
    private static final int COLOR_SURFACE = Color.rgb(255, 255, 255);
    private static final int COLOR_SURFACE_ALT = Color.rgb(237, 243, 247);
    private static final int COLOR_TEXT = Color.rgb(17, 24, 39);
    private static final int COLOR_MUTED = Color.rgb(86, 99, 116);
    private static final int COLOR_DIVIDER = Color.rgb(214, 224, 232);
    private static final int COLOR_PRIMARY = Color.rgb(7, 91, 108);
    private static final int COLOR_PRIMARY_DARK = Color.rgb(4, 68, 82);
    private static final int COLOR_PRIMARY_LIGHT = Color.rgb(225, 241, 244);
    private static final int COLOR_ACCENT = Color.rgb(188, 164, 104);
    private static final int COLOR_PLAYING = Color.rgb(6, 100, 118);
    private static final int COLOR_PLAYING_PRESSED = Color.rgb(4, 81, 96);

    private static final Set<String> AUDIO_EXTENSIONS = new HashSet<>(Arrays.asList(
            "mp3", "m4a", "aac", "wav", "flac", "ogg", "opus", "wma", "amr", "mid", "midi"
    ));

    private SharedPreferences prefs;
    private boolean usingFileAccess;
    private boolean waitingForAllFilesAccess;
    private File fileRoot;
    private File currentDirectory;
    private Uri rootTreeUri;
    private String rootDocId;
    private final ArrayList<String> navDocIds = new ArrayList<>();
    private final ArrayList<String> navNames = new ArrayList<>();

    private final ArrayList<BrowserItem> currentItems = new ArrayList<>();
    private final ArrayList<BrowserItem> currentAudioFiles = new ArrayList<>();
    private final ArrayList<PlaybackService.Track> playingAudioFiles = new ArrayList<>();
    private final ArrayList<String> playingNavDocIds = new ArrayList<>();
    private final ArrayList<String> playingNavNames = new ArrayList<>();

    private String playingDirectoryDocId;
    private PlaybackService.Track currentTrack;
    private int currentPlayingIndex = -1;
    private boolean isPlaying;
    private boolean playerReady;
    private boolean playerPreparing;
    private boolean sleepTimerEnabled;
    private long sleepEndAtMillis;
    private int sleepMinutes = 30;
    private boolean userSeeking;
    private int playbackPositionMs;
    private int playbackDurationMs;
    private boolean playbackServiceBound;
    private boolean scrollToPlayingAfterSnapshot;
    private PlaybackService playbackService;

    private ScrollView listScrollView;
    private LinearLayout listContainer;
    private View currentPlayingRow;
    private TextView pathText;
    private TextView currentTrackText;
    private TextView playPauseButton;
    private SeekBar playbackSeekBar;
    private TextView remainingTimeText;
    private TextView upButton;
    private TextView sleepValueText;
    private final TextView[] sleepOptionButtons = new TextView[SLEEP_OPTIONS_MINUTES.length];

    private final Handler handler = new Handler(Looper.getMainLooper());
    private final Runnable progressRunnable = new Runnable() {
        @Override
        public void run() {
            refreshPlaybackSnapshotFromService();
        }
    };

    private final PlaybackService.Listener playbackListener = new PlaybackService.Listener() {
        @Override
        public void onPlaybackStateChanged(PlaybackService.Snapshot snapshot) {
            runOnUiThread(() -> applyPlaybackSnapshot(snapshot, false));
        }

        @Override
        public void onPlaybackMessage(int stringResId) {
            runOnUiThread(() -> Toast.makeText(MainActivity.this, stringResId, Toast.LENGTH_LONG).show());
        }
    };

    private final ServiceConnection playbackConnection = new ServiceConnection() {
        @Override
        public void onServiceConnected(ComponentName name, IBinder service) {
            playbackService = ((PlaybackService.LocalBinder) service).getService();
            playbackServiceBound = true;
            playbackService.registerListener(playbackListener);
            applyPlaybackSnapshot(playbackService.getSnapshot(), false);
        }

        @Override
        public void onServiceDisconnected(ComponentName name) {
            playbackServiceBound = false;
            playbackService = null;
            stopProgressUpdates();
        }
    };

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        prefs = getSharedPreferences(PREFS_NAME, MODE_PRIVATE);
        sleepMinutes = normalizeSleepMinutes(prefs.getInt(PREF_SLEEP_MINUTES, 30));

        getWindow().setStatusBarColor(Color.rgb(5, 16, 29));
        getWindow().setNavigationBarColor(COLOR_BACKGROUND);

        setContentView(createContentView());
        restoreDirectoryState();
        ensureDefaultDirectoryAccess();
        loadCurrentDirectory();
        if (!waitingForAllFilesAccess) {
            requestNotificationPermissionIfNeeded();
        }
        updatePlaybackUi();
    }

    @Override
    protected void onStart() {
        super.onStart();
        bindService(
                new Intent(this, PlaybackService.class),
                playbackConnection,
                Context.BIND_AUTO_CREATE);
    }

    @Override
    protected void onResume() {
        super.onResume();
        if (!waitingForAllFilesAccess) {
            return;
        }

        waitingForAllFilesAccess = false;
        if (hasAllFilesAccess()) {
            stopPlayback();
            startDirectFileBrowsing(getPreferredFileStartDirectory());
            requestNotificationPermissionIfNeeded();
        } else {
            Toast.makeText(this, R.string.toast_all_files_permission_denied, Toast.LENGTH_LONG).show();
            requestNotificationPermissionIfNeeded();
        }
    }

    @Override
    protected void onPause() {
        if (playbackServiceBound && playbackService != null) {
            playbackService.savePlaybackStateNow();
        }
        super.onPause();
    }

    @Override
    protected void onStop() {
        if (playbackServiceBound && playbackService != null) {
            playbackService.savePlaybackStateNow();
            playbackService.unregisterListener(playbackListener);
            unbindService(playbackConnection);
            playbackServiceBound = false;
            playbackService = null;
        }
        stopProgressUpdates();
        super.onStop();
    }

    @Override
    protected void onDestroy() {
        handler.removeCallbacks(progressRunnable);
        super.onDestroy();
    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, Intent data) {
        super.onActivityResult(requestCode, resultCode, data);
        if (requestCode != REQUEST_OPEN_TREE || resultCode != RESULT_OK || data == null || data.getData() == null) {
            return;
        }

        Uri treeUri = data.getData();
        if ((data.getFlags() & Intent.FLAG_GRANT_READ_URI_PERMISSION) != 0) {
            try {
                getContentResolver().takePersistableUriPermission(treeUri, Intent.FLAG_GRANT_READ_URI_PERMISSION);
            } catch (SecurityException ignored) {
                Toast.makeText(this, R.string.toast_directory_permission_failed, Toast.LENGTH_LONG).show();
            }
        }

        rootTreeUri = treeUri;
        rootDocId = DocumentsContract.getTreeDocumentId(treeUri);
        usingFileAccess = false;
        fileRoot = null;
        currentDirectory = null;
        navDocIds.clear();
        navNames.clear();
        navDocIds.add(rootDocId);
        navNames.add(queryDocumentName(rootDocId));
        saveDirectoryState();
        stopPlayback();
        loadCurrentDirectory();
    }

    @Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        if (requestCode == REQUEST_POST_NOTIFICATIONS) {
            return;
        }
        if (requestCode != REQUEST_READ_STORAGE) {
            return;
        }
        if (grantResults.length > 0 && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
            stopPlayback();
            startDirectFileBrowsing(getPreferredFileStartDirectory());
            requestNotificationPermissionIfNeeded();
        } else {
            Toast.makeText(this, R.string.toast_read_storage_permission_denied, Toast.LENGTH_LONG).show();
            requestNotificationPermissionIfNeeded();
        }
    }

    private View createContentView() {
        LinearLayout root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL);
        root.setBackgroundColor(COLOR_BACKGROUND);
        root.setPadding(dp(12), dp(8), dp(12), dp(12));
        root.setLayoutParams(new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.MATCH_PARENT));

        root.addView(createFolderCard());

        listScrollView = new ScrollView(this);
        listScrollView.setFillViewport(false);
        listScrollView.setClipToPadding(false);
        LinearLayout content = new LinearLayout(this);
        content.setOrientation(LinearLayout.VERTICAL);
        content.setPadding(0, dp(8), 0, dp(10));
        listScrollView.addView(content, new ScrollView.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT));

        content.addView(createListCard());

        root.addView(listScrollView, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                0,
                1));

        root.addView(createPlayerPanel());
        return root;
    }

    private View createHeader() {
        LinearLayout header = new LinearLayout(this);
        header.setOrientation(LinearLayout.HORIZONTAL);
        header.setGravity(Gravity.CENTER_VERTICAL);

        TextView title = new TextView(this);
        title.setText(R.string.app_name);
        title.setTextColor(COLOR_TEXT);
        title.setTextSize(40);
        title.setTypeface(Typeface.DEFAULT, Typeface.BOLD);
        title.setSingleLine(true);
        header.addView(title, new LinearLayout.LayoutParams(
                0,
                ViewGroup.LayoutParams.WRAP_CONTENT,
                1));

        TextView menu = new TextView(this);
        menu.setText("...");
        menu.setGravity(Gravity.CENTER);
        menu.setTextColor(COLOR_MUTED);
        menu.setTextSize(30);
        menu.setTypeface(Typeface.DEFAULT, Typeface.BOLD);
        header.addView(menu, new LinearLayout.LayoutParams(dp(52), dp(52)));

        return header;
    }

    private View createFolderCard() {
        LinearLayout card = createCard(dp(8));

        LinearLayout header = new LinearLayout(this);
        header.setOrientation(LinearLayout.HORIZONTAL);
        header.setGravity(Gravity.TOP);
        card.addView(header, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT));

        TextView label = new TextView(this);
        label.setText(R.string.current_directory);
        label.setTextColor(COLOR_TEXT);
        label.setTextSize(15);
        label.setTypeface(Typeface.DEFAULT, Typeface.BOLD);
        header.addView(label, new LinearLayout.LayoutParams(
                0,
                ViewGroup.LayoutParams.WRAP_CONTENT,
                1));

        upButton = createRaisedButton(getString(R.string.go_up), 15, COLOR_SURFACE_ALT, COLOR_TEXT);
        upButton.setOnClickListener(view -> goUpDirectory());
        header.addView(upButton, new LinearLayout.LayoutParams(dp(86), dp(36)));

        pathText = new TextView(this);
        pathText.setTextColor(COLOR_PRIMARY);
        pathText.setTextSize(16);
        pathText.setTypeface(Typeface.DEFAULT, Typeface.BOLD);
        pathText.setPadding(0, dp(1), 0, 0);
        pathText.setSingleLine(true);
        pathText.setEllipsize(TextUtils.TruncateAt.MIDDLE);
        card.addView(pathText, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT));

        return wrapWithTopMargin(card, 0);
    }

    private View createListCard() {
        LinearLayout card = createCard(dp(8));
        listContainer = new LinearLayout(this);
        listContainer.setOrientation(LinearLayout.VERTICAL);
        card.addView(listContainer, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT));
        return wrapWithTopMargin(card, 0);
    }

    private View createPlayerPanel() {
        LinearLayout panel = createCard(dp(10));
        panel.setBackground(createRoundedBackground(COLOR_SURFACE, COLOR_DIVIDER, 18));
        panel.setElevation(dp(6));

        LinearLayout sleepHeader = new LinearLayout(this);
        sleepHeader.setOrientation(LinearLayout.HORIZONTAL);
        sleepHeader.setGravity(Gravity.CENTER_VERTICAL);
        panel.addView(sleepHeader, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT));

        TextView sleepTitle = new TextView(this);
        sleepTitle.setText(R.string.sleep_title);
        sleepTitle.setTextColor(COLOR_TEXT);
        sleepTitle.setTextSize(19);
        sleepTitle.setTypeface(Typeface.DEFAULT, Typeface.BOLD);
        sleepHeader.addView(sleepTitle, new LinearLayout.LayoutParams(
                0,
                ViewGroup.LayoutParams.WRAP_CONTENT,
                1));

        sleepValueText = new TextView(this);
        sleepValueText.setGravity(Gravity.RIGHT | Gravity.CENTER_VERTICAL);
        sleepValueText.setTextColor(COLOR_PRIMARY);
        sleepValueText.setTextSize(18);
        sleepValueText.setTypeface(Typeface.DEFAULT, Typeface.BOLD);
        sleepValueText.setPadding(0, 0, 0, 0);
        sleepHeader.addView(sleepValueText, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT,
                ViewGroup.LayoutParams.WRAP_CONTENT));

        LinearLayout sleepButtons = new LinearLayout(this);
        sleepButtons.setOrientation(LinearLayout.HORIZONTAL);
        sleepButtons.setGravity(Gravity.CENTER);
        LinearLayout.LayoutParams sleepButtonsParams = new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                dp(42));
        sleepButtonsParams.topMargin = dp(6);
        panel.addView(sleepButtons, sleepButtonsParams);

        for (int index = 0; index < SLEEP_OPTIONS_MINUTES.length; index++) {
            int minutes = SLEEP_OPTIONS_MINUTES[index];
            TextView button = createPillButton(getString(R.string.sleep_button_format, minutes), 15, COLOR_SURFACE_ALT, COLOR_TEXT);
            button.setOnClickListener(view -> toggleSleepTimer(minutes));
            sleepOptionButtons[index] = button;
            LinearLayout.LayoutParams buttonParams = new LinearLayout.LayoutParams(
                    0,
                    ViewGroup.LayoutParams.MATCH_PARENT,
                    1);
            if (index > 0) {
                buttonParams.leftMargin = dp(6);
            }
            sleepButtons.addView(button, buttonParams);
        }

        currentTrackText = new TextView(this);
        currentTrackText.setTextColor(COLOR_MUTED);
        currentTrackText.setTextSize(17);
        currentTrackText.setGravity(Gravity.CENTER);
        currentTrackText.setSingleLine(true);
        currentTrackText.setEllipsize(TextUtils.TruncateAt.MIDDLE);
        currentTrackText.setMarqueeRepeatLimit(-1);
        currentTrackText.setHorizontallyScrolling(true);
        currentTrackText.setSelected(true);
        LinearLayout.LayoutParams trackParams = new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT);
        trackParams.topMargin = dp(6);
        panel.addView(currentTrackText, trackParams);

        LinearLayout progressRow = new LinearLayout(this);
        progressRow.setOrientation(LinearLayout.HORIZONTAL);
        progressRow.setGravity(Gravity.CENTER_VERTICAL);
        LinearLayout.LayoutParams progressParams = new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                dp(34));
        progressParams.topMargin = dp(4);
        panel.addView(progressRow, progressParams);

        playbackSeekBar = new SeekBar(this);
        playbackSeekBar.setMax(1000);
        playbackSeekBar.setProgress(0);
        playbackSeekBar.setEnabled(false);
        playbackSeekBar.setProgressTintList(ColorStateList.valueOf(COLOR_PRIMARY));
        playbackSeekBar.setThumbTintList(ColorStateList.valueOf(COLOR_PRIMARY));
        playbackSeekBar.setProgressBackgroundTintList(ColorStateList.valueOf(COLOR_DIVIDER));
        playbackSeekBar.setPadding(dp(14), 0, dp(14), 0);
        playbackSeekBar.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
            @Override
            public void onProgressChanged(SeekBar seekBar, int progress, boolean fromUser) {
                if (fromUser) {
                    updateRemainingTimeText(progress, seekBar.getMax());
                }
            }

            @Override
            public void onStartTrackingTouch(SeekBar seekBar) {
                userSeeking = true;
            }

            @Override
            public void onStopTrackingTouch(SeekBar seekBar) {
                userSeeking = false;
                seekToPosition(seekBar.getProgress());
            }
        });
        progressRow.addView(playbackSeekBar, new LinearLayout.LayoutParams(
                0,
                ViewGroup.LayoutParams.MATCH_PARENT,
                1));

        remainingTimeText = new TextView(this);
        remainingTimeText.setText(R.string.remaining_time_empty);
        remainingTimeText.setTextColor(COLOR_MUTED);
        remainingTimeText.setTextSize(15);
        remainingTimeText.setTypeface(Typeface.DEFAULT, Typeface.BOLD);
        remainingTimeText.setGravity(Gravity.RIGHT | Gravity.CENTER_VERTICAL);
        LinearLayout.LayoutParams remainingParams = new LinearLayout.LayoutParams(dp(78), ViewGroup.LayoutParams.MATCH_PARENT);
        remainingParams.leftMargin = dp(8);
        progressRow.addView(remainingTimeText, remainingParams);

        LinearLayout controls = new LinearLayout(this);
        controls.setOrientation(LinearLayout.HORIZONTAL);
        controls.setGravity(Gravity.CENTER);
        controls.setPadding(dp(18), 0, dp(18), 0);
        LinearLayout.LayoutParams controlsParams = new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                dp(58));
        controlsParams.topMargin = dp(6);
        panel.addView(controls, controlsParams);

        TextView previous = createPillButton(getString(R.string.previous_track), 17, COLOR_SURFACE_ALT, COLOR_PRIMARY);
        previous.setOnClickListener(view -> playPrevious());
        controls.addView(previous, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1));

        playPauseButton = createPillButton(getString(R.string.play), 19, COLOR_PRIMARY, Color.WHITE);
        playPauseButton.setOnClickListener(view -> togglePlayback());
        LinearLayout.LayoutParams playParams = new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1.12f);
        playParams.leftMargin = dp(10);
        playParams.rightMargin = dp(10);
        controls.addView(playPauseButton, playParams);

        TextView next = createPillButton(getString(R.string.next_track), 17, COLOR_SURFACE_ALT, COLOR_PRIMARY);
        next.setOnClickListener(view -> playNextByUser());
        controls.addView(next, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1));

        updateSleepUi();
        return panel;
    }

    private LinearLayout createCard(int padding) {
        LinearLayout card = new LinearLayout(this);
        card.setOrientation(LinearLayout.VERTICAL);
        card.setPadding(padding, padding, padding, padding);
        card.setBackground(createRoundedBackground(COLOR_SURFACE, COLOR_DIVIDER, 16));
        card.setElevation(dp(3));
        return card;
    }

    private View wrapWithTopMargin(View view, int topMargin) {
        LinearLayout.LayoutParams params = new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT);
        params.topMargin = topMargin;
        view.setLayoutParams(params);
        return view;
    }

    private TextView createRaisedButton(String text, int textSize, int backgroundColor, int textColor) {
        TextView button = new TextView(this);
        button.setText(text);
        button.setTextSize(textSize);
        button.setTextColor(textColor);
        button.setTypeface(Typeface.DEFAULT, Typeface.BOLD);
        button.setGravity(Gravity.CENTER);
        button.setClickable(true);
        button.setBackground(createStateBackground(backgroundColor, darken(backgroundColor), COLOR_DIVIDER, 12));
        button.setElevation(dp(5));
        return button;
    }

    private TextView createPillButton(String text, int textSize, int backgroundColor, int textColor) {
        TextView button = new TextView(this);
        button.setText(text);
        button.setTextSize(textSize);
        button.setTextColor(textColor);
        button.setTypeface(Typeface.DEFAULT, Typeface.BOLD);
        button.setGravity(Gravity.CENTER);
        button.setClickable(true);
        button.setSingleLine(true);
        button.setIncludeFontPadding(false);
        button.setBackground(createStateBackground(backgroundColor, darken(backgroundColor), COLOR_DIVIDER, 28));
        button.setElevation(dp(4));
        return button;
    }

    private GradientDrawable createRoundedBackground(int color, int strokeColor, int radiusDp) {
        GradientDrawable drawable = new GradientDrawable();
        drawable.setColor(color);
        drawable.setCornerRadius(dp(radiusDp));
        drawable.setStroke(dp(1), strokeColor);
        return drawable;
    }

    private StateListDrawable createStateBackground(int color, int pressedColor, int strokeColor, int radiusDp) {
        StateListDrawable stateList = new StateListDrawable();
        stateList.addState(new int[]{android.R.attr.state_pressed}, createRoundedBackground(pressedColor, strokeColor, radiusDp));
        stateList.addState(new int[]{}, createRoundedBackground(color, strokeColor, radiusDp));
        return stateList;
    }

    private int darken(int color) {
        float factor = 0.86f;
        return Color.rgb(
                Math.max(0, Math.round(Color.red(color) * factor)),
                Math.max(0, Math.round(Color.green(color) * factor)),
                Math.max(0, Math.round(Color.blue(color) * factor)));
    }

    private void openDirectoryPicker() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
            if (hasAllFilesAccess()) {
                stopPlayback();
                startDirectFileBrowsing(getPreferredFileStartDirectory());
            } else {
                requestAllFilesAccess();
            }
            return;
        }

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M
                && checkSelfPermission(Manifest.permission.READ_EXTERNAL_STORAGE) != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(new String[]{Manifest.permission.READ_EXTERNAL_STORAGE}, REQUEST_READ_STORAGE);
            return;
        }

        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.Q) {
            stopPlayback();
            startDirectFileBrowsing(getPreferredFileStartDirectory());
            return;
        }

        Intent intent = new Intent(Intent.ACTION_OPEN_DOCUMENT_TREE);
        intent.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION);
        intent.addFlags(Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION);
        intent.addFlags(Intent.FLAG_GRANT_PREFIX_URI_PERMISSION);
        startActivityForResult(intent, REQUEST_OPEN_TREE);
    }

    private void ensureDefaultDirectoryAccess() {
        if (usingFileAccess || waitingForAllFilesAccess) {
            return;
        }

        if (canUseDirectFileBrowsing()) {
            startDirectFileBrowsing(getPreferredFileStartDirectory());
            return;
        }

        if (rootTreeUri != null) {
            return;
        }

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
            requestAllFilesAccess();
            return;
        }

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M
                && Build.VERSION.SDK_INT < Build.VERSION_CODES.R
                && checkSelfPermission(Manifest.permission.READ_EXTERNAL_STORAGE) != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(new String[]{Manifest.permission.READ_EXTERNAL_STORAGE}, REQUEST_READ_STORAGE);
        }
    }

    private void requestAllFilesAccess() {
        waitingForAllFilesAccess = true;
        Toast.makeText(this, R.string.toast_all_files_permission_needed, Toast.LENGTH_LONG).show();

        try {
            Intent intent = new Intent(Settings.ACTION_MANAGE_APP_ALL_FILES_ACCESS_PERMISSION);
            intent.setData(Uri.parse("package:" + getPackageName()));
            startActivity(intent);
        } catch (RuntimeException exception) {
            Intent intent = new Intent(Settings.ACTION_MANAGE_ALL_FILES_ACCESS_PERMISSION);
            startActivity(intent);
        }
    }

    private void requestNotificationPermissionIfNeeded() {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.TIRAMISU) {
            return;
        }
        if (checkSelfPermission(Manifest.permission.POST_NOTIFICATIONS) == PackageManager.PERMISSION_GRANTED) {
            return;
        }
        requestPermissions(new String[]{Manifest.permission.POST_NOTIFICATIONS}, REQUEST_POST_NOTIFICATIONS);
    }

    private boolean hasAllFilesAccess() {
        return Build.VERSION.SDK_INT < Build.VERSION_CODES.R || Environment.isExternalStorageManager();
    }

    private boolean canUseDirectFileBrowsing() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
            return Environment.isExternalStorageManager();
        }
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.M) {
            return true;
        }
        return checkSelfPermission(Manifest.permission.READ_EXTERNAL_STORAGE) == PackageManager.PERMISSION_GRANTED;
    }

    private File getPreferredFileStartDirectory() {
        String savedCurrent = prefs.getString(PREF_FILE_CURRENT_PATH, null);
        if (!TextUtils.isEmpty(savedCurrent)) {
            return new File(savedCurrent);
        }
        return Environment.getExternalStorageDirectory();
    }

    private void startDirectFileBrowsing(File preferredDirectory) {
        fileRoot = Environment.getExternalStorageDirectory();
        currentDirectory = preferredDirectory;
        if (currentDirectory == null || !currentDirectory.isDirectory() || !isWithinRoot(currentDirectory, fileRoot)) {
            currentDirectory = fileRoot;
        }

        usingFileAccess = true;
        rootTreeUri = null;
        rootDocId = null;
        rebuildFileNavigation();
        saveDirectoryState();
        loadCurrentDirectory();
    }

    private void rebuildFileNavigation() {
        navDocIds.clear();
        navNames.clear();
        if (fileRoot == null || currentDirectory == null) {
            return;
        }

        File root = normalizeFile(fileRoot);
        File cursor = normalizeFile(currentDirectory);
        ArrayList<File> descendants = new ArrayList<>();
        while (cursor != null && !sameFile(cursor, root)) {
            descendants.add(0, cursor);
            cursor = cursor.getParentFile();
        }

        navDocIds.add(root.getAbsolutePath());
        navNames.add(getString(R.string.storage_root));
        for (File file : descendants) {
            navDocIds.add(file.getAbsolutePath());
            navNames.add(file.getName());
        }
    }

    private boolean canGoUpFileDirectory() {
        return currentDirectory != null
                && fileRoot != null
                && currentDirectory.getParentFile() != null
                && !sameFile(currentDirectory, fileRoot)
                && isWithinRoot(currentDirectory.getParentFile(), fileRoot);
    }

    private boolean isWithinRoot(File file, File root) {
        if (file == null || root == null) {
            return false;
        }
        try {
            String filePath = file.getCanonicalPath();
            String rootPath = root.getCanonicalPath();
            return filePath.equals(rootPath) || filePath.startsWith(rootPath + File.separator);
        } catch (IOException exception) {
            String filePath = file.getAbsolutePath();
            String rootPath = root.getAbsolutePath();
            return filePath.equals(rootPath) || filePath.startsWith(rootPath + File.separator);
        }
    }

    private boolean sameFile(File left, File right) {
        if (left == null || right == null) {
            return false;
        }
        return normalizeFile(left).getAbsolutePath().equals(normalizeFile(right).getAbsolutePath());
    }

    private File normalizeFile(File file) {
        try {
            return file.getCanonicalFile();
        } catch (IOException exception) {
            return file.getAbsoluteFile();
        }
    }

    private void restoreDirectoryState() {
        String accessMode = prefs.getString(PREF_ACCESS_MODE, null);
        if (ACCESS_MODE_FILE.equals(accessMode) && canUseDirectFileBrowsing()) {
            fileRoot = new File(prefs.getString(
                    PREF_FILE_ROOT_PATH,
                    Environment.getExternalStorageDirectory().getAbsolutePath()));
            currentDirectory = new File(prefs.getString(
                    PREF_FILE_CURRENT_PATH,
                    fileRoot.getAbsolutePath()));
            if (fileRoot.isDirectory() && currentDirectory.isDirectory() && isWithinRoot(currentDirectory, fileRoot)) {
                usingFileAccess = true;
                rebuildFileNavigation();
                return;
            }
        }

        String uriString = prefs.getString(PREF_ROOT_TREE_URI, null);
        if (TextUtils.isEmpty(uriString)) {
            return;
        }

        Uri savedUri = Uri.parse(uriString);
        if (!hasPersistedReadPermission(savedUri)) {
            return;
        }

        usingFileAccess = false;
        fileRoot = null;
        currentDirectory = null;
        rootTreeUri = savedUri;
        rootDocId = prefs.getString(PREF_ROOT_DOC_ID, null);
        if (TextUtils.isEmpty(rootDocId)) {
            rootDocId = DocumentsContract.getTreeDocumentId(rootTreeUri);
        }

        navDocIds.clear();
        navNames.clear();
        navDocIds.addAll(readJsonArray(prefs.getString(PREF_NAV_DOC_IDS, null)));
        navNames.addAll(readJsonArray(prefs.getString(PREF_NAV_NAMES, null)));
        if (navDocIds.isEmpty()) {
            navDocIds.add(rootDocId);
            navNames.add(queryDocumentName(rootDocId));
        }
        while (navNames.size() < navDocIds.size()) {
            navNames.add(queryDocumentName(navDocIds.get(navNames.size())));
        }
    }

    private void saveDirectoryState() {
        SharedPreferences.Editor editor = prefs.edit();
        if (usingFileAccess) {
            if (fileRoot == null || currentDirectory == null) {
                editor.remove(PREF_ACCESS_MODE)
                        .remove(PREF_FILE_ROOT_PATH)
                        .remove(PREF_FILE_CURRENT_PATH)
                        .apply();
                return;
            }
            editor.putString(PREF_ACCESS_MODE, ACCESS_MODE_FILE)
                    .putString(PREF_FILE_ROOT_PATH, fileRoot.getAbsolutePath())
                    .putString(PREF_FILE_CURRENT_PATH, currentDirectory.getAbsolutePath())
                    .remove(PREF_ROOT_TREE_URI)
                    .remove(PREF_ROOT_DOC_ID)
                    .remove(PREF_NAV_DOC_IDS)
                    .remove(PREF_NAV_NAMES)
                    .apply();
            return;
        }

        if (rootTreeUri == null || TextUtils.isEmpty(rootDocId)) {
            editor.remove(PREF_ACCESS_MODE)
                    .remove(PREF_ROOT_TREE_URI)
                    .remove(PREF_ROOT_DOC_ID)
                    .remove(PREF_NAV_DOC_IDS)
                    .remove(PREF_NAV_NAMES)
                    .remove(PREF_FILE_ROOT_PATH)
                    .remove(PREF_FILE_CURRENT_PATH)
                    .apply();
            return;
        }
        editor.putString(PREF_ACCESS_MODE, ACCESS_MODE_SAF)
                .putString(PREF_ROOT_TREE_URI, rootTreeUri.toString())
                .putString(PREF_ROOT_DOC_ID, rootDocId)
                .putString(PREF_NAV_DOC_IDS, toJsonArray(navDocIds))
                .putString(PREF_NAV_NAMES, toJsonArray(navNames))
                .remove(PREF_FILE_ROOT_PATH)
                .remove(PREF_FILE_CURRENT_PATH)
                .apply();
    }

    private void clearDirectoryState() {
        usingFileAccess = false;
        fileRoot = null;
        currentDirectory = null;
        rootTreeUri = null;
        rootDocId = null;
        navDocIds.clear();
        navNames.clear();
        currentItems.clear();
        currentAudioFiles.clear();
        saveDirectoryState();
    }

    private boolean hasPersistedReadPermission(Uri uri) {
        for (android.content.UriPermission permission : getContentResolver().getPersistedUriPermissions()) {
            if (permission.isReadPermission() && permission.getUri().equals(uri)) {
                return true;
            }
        }
        return false;
    }

    private void loadCurrentDirectory() {
        currentItems.clear();
        currentAudioFiles.clear();

        if (usingFileAccess) {
            if (!canUseDirectFileBrowsing() || currentDirectory == null || !currentDirectory.isDirectory()) {
                renderNoDirectorySelected();
                updateDirectoryHeader();
                return;
            }

            rebuildFileNavigation();
            currentItems.addAll(listPlayableFileChildren(currentDirectory));
            for (BrowserItem item : currentItems) {
                if (item.isAudio) {
                    currentAudioFiles.add(item);
                }
            }
            renderCurrentList();
            updateDirectoryHeader();
            saveDirectoryState();
            return;
        }

        if (rootTreeUri == null || TextUtils.isEmpty(getCurrentDocId())) {
            renderNoDirectorySelected();
            updateDirectoryHeader();
            return;
        }

        try {
            currentItems.addAll(listPlayableChildren(getCurrentDocId()));
        } catch (SecurityException | IllegalArgumentException exception) {
            Toast.makeText(this, R.string.toast_directory_unavailable, Toast.LENGTH_LONG).show();
            clearDirectoryState();
            renderNoDirectorySelected();
            updateDirectoryHeader();
            return;
        }

        for (BrowserItem item : currentItems) {
            if (item.isAudio) {
                currentAudioFiles.add(item);
            }
        }

        renderCurrentList();
        updateDirectoryHeader();
        saveDirectoryState();
    }

    private void updateDirectoryHeader() {
        if (usingFileAccess) {
            if (currentDirectory == null) {
                pathText.setText(R.string.no_directory_selected);
                upButton.setAlpha(0.42f);
                return;
            }

            pathText.setText(buildDisplayPath());
            upButton.setAlpha(canGoUpFileDirectory() ? 1f : 0.42f);
            return;
        }

        if (rootTreeUri == null) {
            pathText.setText(R.string.no_directory_selected);
            upButton.setAlpha(0.42f);
            return;
        }

        pathText.setText(buildDisplayPath());
        boolean canGoUp = navDocIds.size() > 1;
        upButton.setAlpha(canGoUp ? 1f : 0.42f);
    }

    private void renderNoDirectorySelected() {
        listContainer.removeAllViews();
        TextView empty = createEmptyText(getString(R.string.empty_permission_required));
        listContainer.addView(empty, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT));
    }

    private void renderCurrentList() {
        listContainer.removeAllViews();
        currentPlayingRow = null;
        if (currentItems.isEmpty()) {
            listContainer.addView(createEmptyText(getString(R.string.empty_current_directory)), new LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT,
                    ViewGroup.LayoutParams.WRAP_CONTENT));
            return;
        }

        for (BrowserItem item : currentItems) {
            int audioIndex = item.isAudio ? indexOfAudio(currentAudioFiles, item.docId) : -1;
            View row = createItemRow(item, audioIndex);
            LinearLayout.LayoutParams rowParams = new LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT,
                    ViewGroup.LayoutParams.WRAP_CONTENT);
            rowParams.bottomMargin = dp(4);
            listContainer.addView(row, rowParams);
        }
    }

    private TextView createEmptyText(String text) {
        TextView empty = new TextView(this);
        empty.setText(text);
        empty.setTextColor(COLOR_MUTED);
        empty.setTextSize(24);
        empty.setGravity(Gravity.CENTER);
        empty.setPadding(dp(10), dp(30), dp(10), dp(30));
        return empty;
    }

    private void scrollToCurrentTrackRow() {
        if (listScrollView == null || currentPlayingRow == null) {
            return;
        }

        listScrollView.post(() -> {
            if (currentPlayingRow == null) {
                return;
            }
            int targetTop = getRelativeTop(currentPlayingRow, listScrollView) - dp(10);
            listScrollView.smoothScrollTo(0, Math.max(0, targetTop));
        });
    }

    private int getRelativeTop(View child, View ancestor) {
        int top = 0;
        View cursor = child;
        while (cursor != null && cursor != ancestor) {
            top += cursor.getTop();
            ViewParent parent = cursor.getParent();
            if (!(parent instanceof View)) {
                break;
            }
            cursor = (View) parent;
        }
        return top;
    }

    private View createItemRow(BrowserItem item, int audioIndex) {
        boolean playingHere = item.isAudio
                && currentTrack != null
                && item.docId.equals(currentTrack.docId)
                && getCurrentDocId().equals(playingDirectoryDocId);

        LinearLayout row = new LinearLayout(this);
        row.setOrientation(LinearLayout.HORIZONTAL);
        row.setGravity(Gravity.CENTER_VERTICAL);
        row.setPadding(dp(10), dp(4), dp(10), dp(4));
        row.setClickable(true);
        row.setBackground(createStateBackground(
                playingHere ? COLOR_PLAYING : COLOR_SURFACE_ALT,
                playingHere ? COLOR_PLAYING_PRESSED : Color.rgb(225, 233, 239),
                playingHere ? COLOR_ACCENT : COLOR_DIVIDER,
                12));
        row.setMinimumHeight(dp(48));
        row.setOnClickListener(view -> {
            if (item.isDirectory) {
                enterDirectory(item);
            } else if (item.isAudio) {
                playAudioAt(audioIndex);
            }
        });
        if (playingHere) {
            currentPlayingRow = row;
        }

        ImageView type = new ImageView(this);
        type.setImageResource(item.isDirectory ? R.drawable.ic_folder_32 : R.drawable.ic_music_note_32);
        type.setColorFilter(playingHere ? Color.WHITE : COLOR_PRIMARY);
        type.setPadding(dp(8), dp(7), dp(8), dp(7));
        type.setBackground(createRoundedBackground(
                playingHere ? Color.rgb(11, 120, 140) : COLOR_SURFACE,
                playingHere ? COLOR_ACCENT : COLOR_DIVIDER,
                10));
        row.addView(type, new LinearLayout.LayoutParams(dp(42), dp(36)));

        TextView name = new TextView(this);
        name.setText(item.name);
        name.setTextSize(item.isDirectory ? 18 : 20);
        name.setTypeface(Typeface.DEFAULT, Typeface.BOLD);
        name.setTextColor(playingHere ? Color.WHITE : COLOR_TEXT);
        name.setSingleLine(true);
        name.setEllipsize(playingHere ? TextUtils.TruncateAt.MARQUEE : TextUtils.TruncateAt.MIDDLE);
        name.setMarqueeRepeatLimit(-1);
        name.setHorizontallyScrolling(playingHere);
        name.setSelected(playingHere);
        LinearLayout.LayoutParams nameParams = new LinearLayout.LayoutParams(
                0,
                ViewGroup.LayoutParams.WRAP_CONTENT,
                1);
        nameParams.leftMargin = dp(10);
        row.addView(name, nameParams);

        return row;
    }

    private void enterDirectory(BrowserItem directory) {
        if (usingFileAccess) {
            if (directory.file == null || !directory.file.isDirectory()) {
                Toast.makeText(this, R.string.toast_directory_unavailable, Toast.LENGTH_LONG).show();
                return;
            }
            currentDirectory = directory.file;
            rebuildFileNavigation();
            loadCurrentDirectory();
            return;
        }

        navDocIds.add(directory.docId);
        navNames.add(directory.name);
        loadCurrentDirectory();
    }

    private void goUpDirectory() {
        if (usingFileAccess) {
            if (!canGoUpFileDirectory()) {
                Toast.makeText(this, R.string.toast_already_root, Toast.LENGTH_SHORT).show();
                return;
            }
            currentDirectory = currentDirectory.getParentFile();
            rebuildFileNavigation();
            loadCurrentDirectory();
            return;
        }

        if (navDocIds.size() <= 1) {
            Toast.makeText(this, R.string.toast_already_root, Toast.LENGTH_SHORT).show();
            return;
        }
        navDocIds.remove(navDocIds.size() - 1);
        navNames.remove(navNames.size() - 1);
        loadCurrentDirectory();
    }

    private List<BrowserItem> listPlayableChildren(String docId) {
        if (usingFileAccess) {
            return listPlayableFileChildren(new File(docId));
        }

        List<BrowserItem> folders = new ArrayList<>();
        List<BrowserItem> audios = new ArrayList<>();
        Uri childrenUri = DocumentsContract.buildChildDocumentsUriUsingTree(rootTreeUri, docId);
        String[] projection = {
                DocumentsContract.Document.COLUMN_DOCUMENT_ID,
                DocumentsContract.Document.COLUMN_DISPLAY_NAME,
                DocumentsContract.Document.COLUMN_MIME_TYPE,
                DocumentsContract.Document.COLUMN_SIZE,
                DocumentsContract.Document.COLUMN_LAST_MODIFIED
        };

        try (Cursor cursor = getContentResolver().query(childrenUri, projection, null, null, null)) {
            if (cursor == null) {
                return new ArrayList<>();
            }
            int idColumn = cursor.getColumnIndex(DocumentsContract.Document.COLUMN_DOCUMENT_ID);
            int nameColumn = cursor.getColumnIndex(DocumentsContract.Document.COLUMN_DISPLAY_NAME);
            int mimeColumn = cursor.getColumnIndex(DocumentsContract.Document.COLUMN_MIME_TYPE);
            while (cursor.moveToNext()) {
                String childDocId = cursor.getString(idColumn);
                String name = cursor.getString(nameColumn);
                String mimeType = cursor.getString(mimeColumn);
                if (TextUtils.isEmpty(childDocId) || TextUtils.isEmpty(name)) {
                    continue;
                }
                boolean isDirectory = DocumentsContract.Document.MIME_TYPE_DIR.equals(mimeType);
                boolean isAudio = !isDirectory && isAudioFile(name, mimeType);
                Uri uri = DocumentsContract.buildDocumentUriUsingTree(rootTreeUri, childDocId);
                BrowserItem item = new BrowserItem(childDocId, name, mimeType, uri, isDirectory, isAudio);
                if (isDirectory) {
                    folders.add(item);
                } else if (isAudio) {
                    audios.add(item);
                }
            }
        }

        Collections.sort(folders, (left, right) -> compareNatural(left.name, right.name));
        Collections.sort(audios, (left, right) -> compareNatural(left.name, right.name));

        List<BrowserItem> items = new ArrayList<>(folders.size() + audios.size());
        items.addAll(folders);
        items.addAll(audios);
        return items;
    }

    private List<BrowserItem> listPlayableFileChildren(File directory) {
        List<BrowserItem> folders = new ArrayList<>();
        List<BrowserItem> audios = new ArrayList<>();
        if (directory == null || !directory.isDirectory()) {
            return new ArrayList<>();
        }

        File[] children = directory.listFiles();
        if (children == null) {
            return new ArrayList<>();
        }

        for (File child : children) {
            if (child == null || child.isHidden() || !child.canRead()) {
                continue;
            }
            String name = child.getName();
            if (TextUtils.isEmpty(name)) {
                continue;
            }
            if (child.isDirectory()) {
                folders.add(new BrowserItem(
                        child.getAbsolutePath(),
                        name,
                        DocumentsContract.Document.MIME_TYPE_DIR,
                        Uri.fromFile(child),
                        child,
                        true,
                        false));
            } else if (child.isFile() && isAudioFile(name, null)) {
                audios.add(new BrowserItem(
                        child.getAbsolutePath(),
                        name,
                        "audio/*",
                        Uri.fromFile(child),
                        child,
                        false,
                        true));
            }
        }

        Collections.sort(folders, (left, right) -> compareNatural(left.name, right.name));
        Collections.sort(audios, (left, right) -> compareNatural(left.name, right.name));

        List<BrowserItem> items = new ArrayList<>(folders.size() + audios.size());
        items.addAll(folders);
        items.addAll(audios);
        return items;
    }

    private boolean isAudioFile(String name, String mimeType) {
        if (mimeType != null && mimeType.toLowerCase(Locale.US).startsWith("audio/")) {
            return true;
        }
        int dot = name.lastIndexOf('.');
        if (dot < 0 || dot == name.length() - 1) {
            return false;
        }
        String extension = name.substring(dot + 1).toLowerCase(Locale.US);
        return AUDIO_EXTENSIONS.contains(extension);
    }

    private void playAudioAt(int index) {
        playAudioAt(index, 0, true);
    }

    private void playAudioAt(int index, int startPositionMs, boolean autoStart) {
        if (index < 0 || index >= currentAudioFiles.size()) {
            Toast.makeText(this, R.string.toast_no_audio_here, Toast.LENGTH_SHORT).show();
            return;
        }

        ArrayList<PlaybackService.Track> queue = buildPlaybackQueue();
        playingDirectoryDocId = getCurrentDocId();
        playingAudioFiles.clear();
        playingAudioFiles.addAll(queue);
        playingNavDocIds.clear();
        playingNavDocIds.addAll(navDocIds);
        playingNavNames.clear();
        playingNavNames.addAll(navNames);
        currentPlayingIndex = index;
        currentTrack = queue.get(index);
        playbackPositionMs = Math.max(0, startPositionMs);
        playbackDurationMs = 0;
        playerReady = false;
        playerPreparing = true;
        isPlaying = autoStart;
        scrollToPlayingAfterSnapshot = true;
        updatePlaybackUi();
        updatePlaybackProgress();
        renderCurrentList();
        scrollToCurrentTrackRow();

        PlaybackService.startPlayQueue(
                this,
                queue,
                index,
                startPositionMs,
                autoStart,
                playingDirectoryDocId,
                playingNavDocIds,
                playingNavNames,
                usingFileAccess,
                rootTreeUri,
                rootDocId);
        startProgressUpdates();
    }

    private ArrayList<PlaybackService.Track> buildPlaybackQueue() {
        ArrayList<PlaybackService.Track> queue = new ArrayList<>();
        for (BrowserItem item : currentAudioFiles) {
            queue.add(new PlaybackService.Track(
                    item.docId,
                    item.name,
                    item.mimeType,
                    item.uri == null ? "" : item.uri.toString(),
                    item.file == null ? "" : item.file.getAbsolutePath()));
        }
        return queue;
    }

    private void refreshPlaybackSnapshotFromService() {
        if (playbackServiceBound && playbackService != null) {
            applyPlaybackSnapshot(playbackService.getSnapshot(), false);
        }
    }

    private void applyPlaybackSnapshot(PlaybackService.Snapshot snapshot, boolean forceScrollToPlaying) {
        if (snapshot == null) {
            return;
        }

        String oldTrackDocId = currentTrack == null ? null : currentTrack.docId;
        String oldDirectoryDocId = playingDirectoryDocId;
        PlaybackService.Track snapshotTrack = snapshot.currentTrack;

        currentTrack = snapshotTrack;
        currentPlayingIndex = snapshot.currentIndex;
        playbackPositionMs = snapshot.positionMs;
        playbackDurationMs = snapshot.durationMs;
        isPlaying = snapshot.isPlaying;
        playerReady = snapshot.playerReady;
        playerPreparing = snapshot.playerPreparing;
        sleepTimerEnabled = snapshot.sleepTimerEnabled;
        sleepMinutes = snapshot.sleepMinutes;
        sleepEndAtMillis = snapshot.sleepTimerEnabled
                ? System.currentTimeMillis() + snapshot.sleepRemainingMillis
                : 0L;

        playingDirectoryDocId = snapshot.playingDirectoryDocId;
        playingAudioFiles.clear();
        playingAudioFiles.addAll(snapshot.queue);
        playingNavDocIds.clear();
        playingNavDocIds.addAll(snapshot.navDocIds);
        playingNavNames.clear();
        playingNavNames.addAll(snapshot.navNames);

        boolean shouldJumpToPlaying = forceScrollToPlaying || scrollToPlayingAfterSnapshot;
        boolean directoryChanged = shouldJumpToPlaying && jumpToPlayingDirectoryFromSnapshot(snapshot);

        boolean playingRowChanged = !TextUtils.equals(oldTrackDocId, snapshotTrack == null ? null : snapshotTrack.docId)
                || !TextUtils.equals(oldDirectoryDocId, playingDirectoryDocId);
        updatePlaybackUi();
        updatePlaybackProgress();
        updateSleepUi();
        if (!directoryChanged && playingRowChanged && isCurrentDirectory(playingDirectoryDocId)) {
            renderCurrentList();
        }
        if (shouldJumpToPlaying) {
            if (!directoryChanged) {
                renderCurrentList();
            }
            scrollToCurrentTrackRow();
            scrollToPlayingAfterSnapshot = false;
        }
        scheduleProgressUpdatesIfNeeded();
    }

    private boolean jumpToPlayingDirectoryFromSnapshot(PlaybackService.Snapshot snapshot) {
        if (snapshot.currentTrack == null
                || TextUtils.isEmpty(snapshot.playingDirectoryDocId)
                || snapshot.navDocIds.isEmpty()
                || isCurrentDirectory(snapshot.playingDirectoryDocId)) {
            return false;
        }

        usingFileAccess = snapshot.usingFileAccess;
        navDocIds.clear();
        navDocIds.addAll(snapshot.navDocIds);
        navNames.clear();
        navNames.addAll(snapshot.navNames);
        if (snapshot.usingFileAccess) {
            fileRoot = Environment.getExternalStorageDirectory();
            currentDirectory = new File(snapshot.playingDirectoryDocId);
            rootTreeUri = null;
            rootDocId = null;
        } else {
            rootTreeUri = TextUtils.isEmpty(snapshot.rootTreeUriString) ? rootTreeUri : Uri.parse(snapshot.rootTreeUriString);
            rootDocId = TextUtils.isEmpty(snapshot.rootDocId) ? rootDocId : snapshot.rootDocId;
            currentDirectory = null;
            fileRoot = null;
        }
        loadCurrentDirectory();
        return true;
    }

    private boolean isCurrentDirectory(String directoryDocId) {
        return !TextUtils.isEmpty(directoryDocId) && TextUtils.equals(directoryDocId, getCurrentDocId());
    }

    private void togglePlayback() {
        if (currentTrack == null) {
            if (currentAudioFiles.isEmpty()) {
                Toast.makeText(this, R.string.toast_no_audio_here, Toast.LENGTH_SHORT).show();
            } else {
                playAudioAt(0);
            }
            return;
        }
        if (playerPreparing) {
            Toast.makeText(this, R.string.toast_player_preparing, Toast.LENGTH_SHORT).show();
            return;
        }

        if (playbackServiceBound && playbackService != null) {
            scrollToPlayingAfterSnapshot = true;
            playbackService.togglePlayback();
        }
    }

    private void playPrevious() {
        if (currentTrack == null && playingAudioFiles.isEmpty()) {
            if (!currentAudioFiles.isEmpty()) {
                playAudioAt(0);
            }
            return;
        }

        scrollToPlayingAfterSnapshot = true;
        if (playbackServiceBound && playbackService != null) {
            playbackService.playPrevious();
        }
    }

    private void playNextByUser() {
        if (currentTrack == null && playingAudioFiles.isEmpty()) {
            if (!currentAudioFiles.isEmpty()) {
                playAudioAt(0);
            }
            return;
        }
        scrollToPlayingAfterSnapshot = true;
        if (playbackServiceBound && playbackService != null) {
            playbackService.playNextByUser();
        }
    }

    private void stopPlayback() {
        if (playbackServiceBound && playbackService != null) {
            playbackService.stopPlaybackByUser();
        } else {
            PlaybackService.requestStop(this);
        }
        currentTrack = null;
        currentPlayingIndex = -1;
        playingDirectoryDocId = null;
        playingAudioFiles.clear();
        playingNavDocIds.clear();
        playingNavNames.clear();
        playbackPositionMs = 0;
        playbackDurationMs = 0;
        isPlaying = false;
        playerReady = false;
        playerPreparing = false;
        updatePlaybackUi();
        updatePlaybackProgress();
        renderCurrentList();
    }

    private void toggleSleepTimer(int minutes) {
        if (playbackServiceBound && playbackService != null) {
            playbackService.toggleSleepTimer(minutes);
            return;
        }

        minutes = normalizeSleepMinutes(minutes);
        boolean closingCurrent = sleepTimerEnabled && sleepMinutes == minutes;
        sleepMinutes = minutes;
        sleepTimerEnabled = !closingCurrent;
        sleepEndAtMillis = sleepTimerEnabled ? System.currentTimeMillis() + sleepMinutes * 60L * 1000L : 0L;
        prefs.edit().putInt(PREF_SLEEP_MINUTES, sleepMinutes).apply();
        updateSleepUi();
    }

    private void startProgressUpdates() {
        handler.removeCallbacks(progressRunnable);
        updatePlaybackProgress();
        if (playbackServiceBound && (isPlaying || sleepTimerEnabled || playerPreparing)) {
            handler.postDelayed(progressRunnable, 1000L);
        }
    }

    private void stopProgressUpdates() {
        handler.removeCallbacks(progressRunnable);
    }

    private void scheduleProgressUpdatesIfNeeded() {
        handler.removeCallbacks(progressRunnable);
        if (playbackServiceBound && (isPlaying || sleepTimerEnabled || playerPreparing)) {
            handler.postDelayed(progressRunnable, 1000L);
        }
    }

    private void updatePlaybackProgress() {
        if (playbackSeekBar == null || remainingTimeText == null) {
            return;
        }

        if (currentTrack == null || playbackDurationMs <= 0) {
            playbackSeekBar.setEnabled(false);
            if (!userSeeking) {
                playbackSeekBar.setMax(1000);
                playbackSeekBar.setProgress(0);
            }
            remainingTimeText.setText(R.string.remaining_time_empty);
            return;
        }

        playbackSeekBar.setEnabled(true);
        if (playbackSeekBar.getMax() != playbackDurationMs) {
            playbackSeekBar.setMax(playbackDurationMs);
        }
        if (!userSeeking) {
            playbackSeekBar.setProgress(Math.min(playbackPositionMs, playbackDurationMs));
            updateRemainingTimeText(playbackPositionMs, playbackDurationMs);
        }
    }

    private void updateRemainingTimeText(int positionMs, int durationMs) {
        if (remainingTimeText == null) {
            return;
        }
        if (durationMs <= 0) {
            remainingTimeText.setText(R.string.remaining_time_empty);
            return;
        }
        int remainingMs = Math.max(0, durationMs - Math.max(0, positionMs));
        remainingTimeText.setText(getString(R.string.remaining_time_format, formatDurationMs(remainingMs)));
    }

    private void seekToPosition(int positionMs) {
        int target = playbackDurationMs > 0
                ? Math.min(Math.max(0, positionMs), playbackDurationMs)
                : Math.max(0, positionMs);
        playbackPositionMs = target;
        if (playbackServiceBound && playbackService != null) {
            playbackService.seekToPosition(target);
        }
        updatePlaybackProgress();
        startProgressUpdates();
    }

    private void updatePlaybackUi() {
        String desiredTrackText;
        TextUtils.TruncateAt desiredEllipsize;
        boolean desiredHorizontalScrolling;
        if (currentTrack == null) {
            desiredTrackText = getString(R.string.player_idle);
            desiredEllipsize = TextUtils.TruncateAt.MIDDLE;
            desiredHorizontalScrolling = false;
        } else if (playerPreparing) {
            desiredTrackText = getString(R.string.player_preparing_format, currentTrack.name);
            desiredEllipsize = TextUtils.TruncateAt.MARQUEE;
            desiredHorizontalScrolling = true;
        } else {
            desiredTrackText = getString(
                    isPlaying ? R.string.player_now_playing_format : R.string.player_paused_format,
                    currentTrack.name);
            desiredEllipsize = TextUtils.TruncateAt.MARQUEE;
            desiredHorizontalScrolling = true;
        }

        boolean desiredSelected = currentTrack != null;
        if (!TextUtils.equals(currentTrackText.getText(), desiredTrackText)) {
            currentTrackText.setText(desiredTrackText);
            currentTrackText.setHorizontallyScrolling(desiredHorizontalScrolling);
            currentTrackText.setEllipsize(desiredEllipsize);
        }
        if (currentTrackText.isSelected() != desiredSelected) {
            currentTrackText.setSelected(desiredSelected);
        }

        String desiredPlayPauseText = getString(isPlaying ? R.string.pause : R.string.play);
        if (!TextUtils.equals(playPauseButton.getText(), desiredPlayPauseText)) {
            playPauseButton.setText(desiredPlayPauseText);
        }
    }

    private void updateSleepUi() {
        if (sleepValueText == null) {
            return;
        }

        if (!sleepTimerEnabled) {
            sleepValueText.setTextColor(COLOR_MUTED);
            sleepValueText.setText(R.string.sleep_closed);
        } else {
            sleepValueText.setTextColor(COLOR_PRIMARY);
            long remainingMillis = Math.max(0L, sleepEndAtMillis - System.currentTimeMillis());
            sleepValueText.setText(getString(R.string.sleep_countdown_format, formatRemainingSeconds(remainingMillis)));
        }
        updateSleepButtons();
    }

    private void updateSleepButtons() {
        for (int index = 0; index < sleepOptionButtons.length; index++) {
            TextView button = sleepOptionButtons[index];
            if (button == null) {
                continue;
            }
            boolean active = sleepTimerEnabled && sleepMinutes == SLEEP_OPTIONS_MINUTES[index];
            int backgroundColor = active ? COLOR_PRIMARY : COLOR_SURFACE_ALT;
            int textColor = active ? Color.WHITE : COLOR_TEXT;
            button.setTextColor(textColor);
            button.setBackground(createStateBackground(backgroundColor, darken(backgroundColor), COLOR_DIVIDER, 28));
        }
    }

    private String formatRemainingSeconds(long millis) {
        long totalSeconds = Math.max(0L, (millis + 999L) / 1000L);
        long minutes = totalSeconds / 60L;
        long seconds = totalSeconds % 60L;
        return String.format(Locale.US, "%02d:%02d", minutes, seconds);
    }

    private String formatDurationMs(int millis) {
        long totalSeconds = Math.max(0L, (millis + 999L) / 1000L);
        long hours = totalSeconds / 3600L;
        long minutes = (totalSeconds % 3600L) / 60L;
        long seconds = totalSeconds % 60L;
        if (hours > 0L) {
            return String.format(Locale.US, "%d:%02d:%02d", hours, minutes, seconds);
        }
        return String.format(Locale.US, "%02d:%02d", minutes, seconds);
    }

    private String getCurrentDocId() {
        if (navDocIds.isEmpty()) {
            return null;
        }
        return navDocIds.get(navDocIds.size() - 1);
    }

    private String buildDisplayPath() {
        if (navNames.isEmpty()) {
            return getString(R.string.no_directory_selected);
        }
        return TextUtils.join(" / ", navNames);
    }

    private String queryDocumentName(String docId) {
        if (rootTreeUri == null || TextUtils.isEmpty(docId)) {
            return getString(R.string.storage_root);
        }

        Uri documentUri = DocumentsContract.buildDocumentUriUsingTree(rootTreeUri, docId);
        String[] projection = {DocumentsContract.Document.COLUMN_DISPLAY_NAME};
        try (Cursor cursor = getContentResolver().query(documentUri, projection, null, null, null)) {
            if (cursor != null && cursor.moveToFirst()) {
                String name = cursor.getString(0);
                if (!TextUtils.isEmpty(name)) {
                    return name;
                }
            }
        } catch (RuntimeException ignored) {
        }
        return friendlyNameFromDocId(docId);
    }

    private String friendlyNameFromDocId(String docId) {
        String decoded = Uri.decode(docId);
        int slash = decoded.lastIndexOf('/');
        if (slash >= 0 && slash < decoded.length() - 1) {
            return decoded.substring(slash + 1);
        }
        int colon = decoded.lastIndexOf(':');
        if (colon >= 0 && colon < decoded.length() - 1) {
            return decoded.substring(colon + 1);
        }
        return decoded;
    }

    private int indexOfAudio(List<BrowserItem> audios, String docId) {
        for (int index = 0; index < audios.size(); index++) {
            if (audios.get(index).docId.equals(docId)) {
                return index;
            }
        }
        return -1;
    }

    private int normalizeSleepMinutes(int minutes) {
        if (minutes <= 30) {
            return 30;
        }
        if (minutes <= 60) {
            return 60;
        }
        if (minutes <= 90) {
            return 90;
        }
        return 120;
    }

    private ArrayList<String> readJsonArray(String value) {
        ArrayList<String> result = new ArrayList<>();
        if (TextUtils.isEmpty(value)) {
            return result;
        }
        try {
            JSONArray array = new JSONArray(value);
            for (int index = 0; index < array.length(); index++) {
                result.add(array.optString(index));
            }
        } catch (JSONException ignored) {
        }
        return result;
    }

    private String toJsonArray(List<String> values) {
        JSONArray array = new JSONArray();
        for (String value : values) {
            array.put(value);
        }
        return array.toString();
    }

    private int compareNatural(String left, String right) {
        int leftIndex = 0;
        int rightIndex = 0;
        while (leftIndex < left.length() && rightIndex < right.length()) {
            char leftChar = left.charAt(leftIndex);
            char rightChar = right.charAt(rightIndex);
            if (Character.isDigit(leftChar) && Character.isDigit(rightChar)) {
                int leftStart = leftIndex;
                int rightStart = rightIndex;
                while (leftIndex < left.length() && Character.isDigit(left.charAt(leftIndex))) {
                    leftIndex++;
                }
                while (rightIndex < right.length() && Character.isDigit(right.charAt(rightIndex))) {
                    rightIndex++;
                }
                String leftNumber = stripLeadingZeroes(left.substring(leftStart, leftIndex));
                String rightNumber = stripLeadingZeroes(right.substring(rightStart, rightIndex));
                if (leftNumber.length() != rightNumber.length()) {
                    return leftNumber.length() - rightNumber.length();
                }
                int numberCompare = leftNumber.compareTo(rightNumber);
                if (numberCompare != 0) {
                    return numberCompare;
                }
            } else {
                int compare = Character.toLowerCase(leftChar) - Character.toLowerCase(rightChar);
                if (compare != 0) {
                    return compare;
                }
                leftIndex++;
                rightIndex++;
            }
        }
        return left.length() - right.length();
    }

    private String stripLeadingZeroes(String value) {
        int index = 0;
        while (index < value.length() - 1 && value.charAt(index) == '0') {
            index++;
        }
        return value.substring(index);
    }

    private int dp(int value) {
        return Math.round(value * getResources().getDisplayMetrics().density);
    }

    private static class BrowserItem {
        final String docId;
        final String name;
        final String mimeType;
        final Uri uri;
        final File file;
        final boolean isDirectory;
        final boolean isAudio;

        BrowserItem(String docId, String name, String mimeType, Uri uri, boolean isDirectory, boolean isAudio) {
            this(docId, name, mimeType, uri, null, isDirectory, isAudio);
        }

        BrowserItem(String docId, String name, String mimeType, Uri uri, File file, boolean isDirectory, boolean isAudio) {
            this.docId = docId;
            this.name = name;
            this.mimeType = mimeType;
            this.uri = uri;
            this.file = file;
            this.isDirectory = isDirectory;
            this.isAudio = isAudio;
        }
    }

}
