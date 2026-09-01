package com.musicplayer.app;

import android.Manifest;
import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.app.Service;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.content.pm.PackageManager;
import android.database.Cursor;
import android.graphics.Color;
import android.media.AudioAttributes;
import android.media.AudioManager;
import android.media.MediaMetadata;
import android.media.MediaPlayer;
import android.media.session.MediaSession;
import android.media.session.PlaybackState;
import android.net.Uri;
import android.os.Binder;
import android.os.Build;
import android.os.Environment;
import android.os.Handler;
import android.os.IBinder;
import android.os.Looper;
import android.os.PowerManager;
import android.provider.DocumentsContract;
import android.text.TextUtils;
import android.util.Log;

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

public class PlaybackService extends Service {
    private static final String TAG = "MusicPlayer";

    private static final String ACTION_PLAY_QUEUE = "com.musicplayer.app.action.PLAY_QUEUE";
    private static final String ACTION_TOGGLE = "com.musicplayer.app.action.TOGGLE";
    private static final String ACTION_PREVIOUS = "com.musicplayer.app.action.PREVIOUS";
    private static final String ACTION_NEXT = "com.musicplayer.app.action.NEXT";
    private static final String ACTION_STOP = "com.musicplayer.app.action.STOP";

    private static final String EXTRA_DOC_IDS = "doc_ids";
    private static final String EXTRA_NAMES = "names";
    private static final String EXTRA_MIME_TYPES = "mime_types";
    private static final String EXTRA_URI_STRINGS = "uri_strings";
    private static final String EXTRA_FILE_PATHS = "file_paths";
    private static final String EXTRA_INDEX = "index";
    private static final String EXTRA_START_MS = "start_ms";
    private static final String EXTRA_AUTO_START = "auto_start";
    private static final String EXTRA_DIRECTORY_DOC_ID = "directory_doc_id";
    private static final String EXTRA_NAV_DOC_IDS = "nav_doc_ids";
    private static final String EXTRA_NAV_NAMES = "nav_names";
    private static final String EXTRA_USING_FILE_ACCESS = "using_file_access";
    private static final String EXTRA_ROOT_TREE_URI = "root_tree_uri";
    private static final String EXTRA_ROOT_DOC_ID = "root_doc_id";

    private static final String CHANNEL_ID = "musicplayer_playback";
    private static final int NOTIFICATION_ID = 2001;
    private static final long PLAYBACK_STATE_SAVE_INTERVAL_MS = 5000L;

    private static final String PREFS_NAME = "musicplayer";
    private static final String PREF_ACCESS_MODE = "access_mode";
    private static final String ACCESS_MODE_SAF = "saf";
    private static final String ACCESS_MODE_FILE = "file";
    private static final String PREF_ROOT_TREE_URI = "root_tree_uri";
    private static final String PREF_ROOT_DOC_ID = "root_doc_id";
    private static final String PREF_FILE_ROOT_PATH = "file_root_path";
    private static final String PREF_FILE_CURRENT_PATH = "file_current_path";
    private static final String PREF_SLEEP_MINUTES = "sleep_minutes";
    private static final String PREF_PLAYBACK_TRACK_DOC_ID = "playback_track_doc_id";
    private static final String PREF_PLAYBACK_TRACK_NAME = "playback_track_name";
    private static final String PREF_PLAYBACK_TRACK_URI = "playback_track_uri";
    private static final String PREF_PLAYBACK_TRACK_FILE_PATH = "playback_track_file_path";
    private static final String PREF_PLAYBACK_DIRECTORY_DOC_ID = "playback_directory_doc_id";
    private static final String PREF_PLAYBACK_NAV_DOC_IDS = "playback_nav_doc_ids";
    private static final String PREF_PLAYBACK_NAV_NAMES = "playback_nav_names";
    private static final String PREF_PLAYBACK_INDEX = "playback_index";
    private static final String PREF_PLAYBACK_POSITION_MS = "playback_position_ms";
    private static final String PREF_PLAYBACK_WAS_PLAYING = "playback_was_playing";

    private static final Set<String> AUDIO_EXTENSIONS = new HashSet<>(Arrays.asList(
            "mp3", "m4a", "aac", "wav", "flac", "ogg", "opus", "wma", "amr", "mid", "midi"
    ));

    private final IBinder binder = new LocalBinder();
    private final ArrayList<Listener> listeners = new ArrayList<>();
    private final ArrayList<Track> queue = new ArrayList<>();
    private final ArrayList<String> playingNavDocIds = new ArrayList<>();
    private final ArrayList<String> playingNavNames = new ArrayList<>();
    private final Handler handler = new Handler(Looper.getMainLooper());

    private SharedPreferences prefs;
    private NotificationManager notificationManager;
    private MediaSession mediaSession;
    private AudioManager audioManager;
    private MediaPlayer mediaPlayer;

    private boolean serviceStarted;
    private boolean foregroundStarted;
    private boolean usingFileAccess;
    private boolean isPlaying;
    private boolean playerReady;
    private boolean playerPreparing;
    private boolean retryingCurrentTrack;
    private boolean sleepTimerEnabled;
    private boolean resumeAfterAudioFocusGain;
    private Uri rootTreeUri;
    private String rootDocId;
    private String playingDirectoryDocId;
    private int currentIndex = -1;
    private int lastKnownPositionMs;
    private int durationMs;
    private int playbackGeneration;
    private int sleepMinutes = 30;
    private long sleepEndAtMillis;
    private long lastPlaybackStateSaveAtMillis;

    private final Runnable progressRunnable = new Runnable() {
        @Override
        public void run() {
            updatePlaybackProgressFromPlayer();
            if (isPlaying) {
                handler.postDelayed(this, 1000L);
            }
        }
    };

    private final Runnable sleepRunnable = new Runnable() {
        @Override
        public void run() {
            updateSleepCountdown();
        }
    };

    private final AudioManager.OnAudioFocusChangeListener audioFocusChangeListener = focusChange -> {
        if (focusChange == AudioManager.AUDIOFOCUS_LOSS
                || focusChange == AudioManager.AUDIOFOCUS_LOSS_TRANSIENT) {
            resumeAfterAudioFocusGain = isPlaying;
            pausePlayback(false);
            return;
        }
        if (focusChange == AudioManager.AUDIOFOCUS_LOSS_TRANSIENT_CAN_DUCK) {
            setPlayerVolume(0.35f);
            return;
        }
        if (focusChange == AudioManager.AUDIOFOCUS_GAIN) {
            setPlayerVolume(1f);
            if (resumeAfterAudioFocusGain) {
                resumeAfterAudioFocusGain = false;
                startCurrentPlayer();
            }
        }
    };

    public static void startPlayQueue(
            Context context,
            List<Track> tracks,
            int index,
            int startPositionMs,
            boolean autoStart,
            String directoryDocId,
            List<String> navDocIds,
            List<String> navNames,
            boolean usingFileAccess,
            Uri rootTreeUri,
            String rootDocId) {
        Intent intent = new Intent(context, PlaybackService.class);
        intent.setAction(ACTION_PLAY_QUEUE);
        putTrackList(intent, tracks);
        intent.putExtra(EXTRA_INDEX, index);
        intent.putExtra(EXTRA_START_MS, Math.max(0, startPositionMs));
        intent.putExtra(EXTRA_AUTO_START, autoStart);
        intent.putExtra(EXTRA_DIRECTORY_DOC_ID, directoryDocId);
        intent.putStringArrayListExtra(EXTRA_NAV_DOC_IDS, new ArrayList<>(navDocIds));
        intent.putStringArrayListExtra(EXTRA_NAV_NAMES, new ArrayList<>(navNames));
        intent.putExtra(EXTRA_USING_FILE_ACCESS, usingFileAccess);
        intent.putExtra(EXTRA_ROOT_TREE_URI, rootTreeUri == null ? "" : rootTreeUri.toString());
        intent.putExtra(EXTRA_ROOT_DOC_ID, rootDocId == null ? "" : rootDocId);
        startForegroundCommand(context, intent);
    }

    public static void requestStop(Context context) {
        Intent intent = new Intent(context, PlaybackService.class);
        intent.setAction(ACTION_STOP);
        context.startService(intent);
    }

    private static void putTrackList(Intent intent, List<Track> tracks) {
        ArrayList<String> docIds = new ArrayList<>();
        ArrayList<String> names = new ArrayList<>();
        ArrayList<String> mimeTypes = new ArrayList<>();
        ArrayList<String> uriStrings = new ArrayList<>();
        ArrayList<String> filePaths = new ArrayList<>();
        for (Track track : tracks) {
            docIds.add(track.docId);
            names.add(track.name);
            mimeTypes.add(track.mimeType);
            uriStrings.add(track.uriString);
            filePaths.add(track.filePath);
        }
        intent.putStringArrayListExtra(EXTRA_DOC_IDS, docIds);
        intent.putStringArrayListExtra(EXTRA_NAMES, names);
        intent.putStringArrayListExtra(EXTRA_MIME_TYPES, mimeTypes);
        intent.putStringArrayListExtra(EXTRA_URI_STRINGS, uriStrings);
        intent.putStringArrayListExtra(EXTRA_FILE_PATHS, filePaths);
    }

    private static ArrayList<Track> readTrackList(Intent intent) {
        ArrayList<String> docIds = intent.getStringArrayListExtra(EXTRA_DOC_IDS);
        ArrayList<String> names = intent.getStringArrayListExtra(EXTRA_NAMES);
        ArrayList<String> mimeTypes = intent.getStringArrayListExtra(EXTRA_MIME_TYPES);
        ArrayList<String> uriStrings = intent.getStringArrayListExtra(EXTRA_URI_STRINGS);
        ArrayList<String> filePaths = intent.getStringArrayListExtra(EXTRA_FILE_PATHS);
        ArrayList<Track> tracks = new ArrayList<>();
        if (docIds == null || names == null || mimeTypes == null || uriStrings == null || filePaths == null) {
            return tracks;
        }
        int size = Math.min(docIds.size(), Math.min(names.size(), Math.min(mimeTypes.size(), Math.min(uriStrings.size(), filePaths.size()))));
        for (int index = 0; index < size; index++) {
            tracks.add(new Track(
                    docIds.get(index),
                    names.get(index),
                    mimeTypes.get(index),
                    uriStrings.get(index),
                    filePaths.get(index)));
        }
        return tracks;
    }

    private static void startForegroundCommand(Context context, Intent intent) {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            context.startForegroundService(intent);
        } else {
            context.startService(intent);
        }
    }

    @Override
    public void onCreate() {
        super.onCreate();
        prefs = getSharedPreferences(PREFS_NAME, MODE_PRIVATE);
        sleepMinutes = normalizeSleepMinutes(prefs.getInt(PREF_SLEEP_MINUTES, 30));
        notificationManager = (NotificationManager) getSystemService(NOTIFICATION_SERVICE);
        audioManager = (AudioManager) getSystemService(AUDIO_SERVICE);
        createNotificationChannel();
        createMediaSession();
        restoreSavedPlaybackIfPossible();
    }

    @Override
    public int onStartCommand(Intent intent, int flags, int startId) {
        serviceStarted = true;
        if (intent == null || TextUtils.isEmpty(intent.getAction())) {
            if (isPlaying || playerPreparing || getCurrentTrack() != null) {
                updateForegroundNotification();
            }
            return START_STICKY;
        }

        String action = intent.getAction();
        if (ACTION_PLAY_QUEUE.equals(action)) {
            playQueueFromIntent(intent);
        } else if (ACTION_TOGGLE.equals(action)) {
            togglePlayback();
        } else if (ACTION_PREVIOUS.equals(action)) {
            playPrevious();
        } else if (ACTION_NEXT.equals(action)) {
            playNextByUser();
        } else if (ACTION_STOP.equals(action)) {
            stopPlayback(true, true);
        }
        return START_STICKY;
    }

    @Override
    public IBinder onBind(Intent intent) {
        return binder;
    }

    @Override
    public void onDestroy() {
        savePlaybackState();
        handler.removeCallbacks(progressRunnable);
        handler.removeCallbacks(sleepRunnable);
        releasePlayer();
        abandonAudioFocus();
        if (mediaSession != null) {
            mediaSession.setActive(false);
            mediaSession.release();
            mediaSession = null;
        }
        super.onDestroy();
    }

    public void registerListener(Listener listener) {
        if (listener == null || listeners.contains(listener)) {
            return;
        }
        listeners.add(listener);
        listener.onPlaybackStateChanged(getSnapshot());
    }

    public void unregisterListener(Listener listener) {
        listeners.remove(listener);
    }

    public Snapshot getSnapshot() {
        refreshPlaybackProgressFields();
        return getSnapshotWithoutRefreshing();
    }

    public void togglePlayback() {
        if (getCurrentTrack() == null) {
            return;
        }
        if (isPlaying) {
            pausePlayback(true);
            return;
        }
        if (mediaPlayer == null || !playerReady) {
            playCurrent(lastKnownPositionMs, true, true);
            return;
        }
        startCurrentPlayer();
    }

    public void playPrevious() {
        if (queue.isEmpty()) {
            return;
        }
        currentIndex = Math.max(0, currentIndex - 1);
        playCurrent(0, true, true);
    }

    public void playNextByUser() {
        if (queue.isEmpty()) {
            return;
        }
        playNextAfterCompletion();
    }

    public void stopPlaybackByUser() {
        stopPlayback(true, true);
    }

    public void seekToPosition(int positionMs) {
        int target = durationMs > 0
                ? Math.min(Math.max(0, positionMs), durationMs)
                : Math.max(0, positionMs);
        lastKnownPositionMs = target;
        if (mediaPlayer != null && playerReady) {
            try {
                mediaPlayer.seekTo(target);
            } catch (IllegalStateException exception) {
                Log.e(TAG, "Failed to seek current track: " + describeTrackForLog(getCurrentTrack()), exception);
            }
        }
        savePlaybackState();
        updateMediaSessionState();
        notifyStateChanged();
    }

    public void toggleSleepTimer(int minutes) {
        if (sleepTimerEnabled && sleepMinutes == minutes) {
            disableSleepTimer();
            return;
        }
        sleepMinutes = normalizeSleepMinutes(minutes);
        sleepTimerEnabled = true;
        sleepEndAtMillis = System.currentTimeMillis() + sleepMinutes * 60L * 1000L;
        prefs.edit().putInt(PREF_SLEEP_MINUTES, sleepMinutes).apply();
        scheduleSleepTimer();
        notifyStateChanged();
        updateForegroundNotification();
    }

    public void disableSleepTimer() {
        sleepTimerEnabled = false;
        sleepEndAtMillis = 0L;
        handler.removeCallbacks(sleepRunnable);
        notifyStateChanged();
        updateForegroundNotification();
    }

    public void savePlaybackStateNow() {
        savePlaybackState();
    }

    private void playQueueFromIntent(Intent intent) {
        ArrayList<Track> tracks = readTrackList(intent);
        if (tracks.isEmpty()) {
            return;
        }
        queue.clear();
        queue.addAll(tracks);
        currentIndex = Math.min(Math.max(0, intent.getIntExtra(EXTRA_INDEX, 0)), queue.size() - 1);
        lastKnownPositionMs = Math.max(0, intent.getIntExtra(EXTRA_START_MS, 0));
        durationMs = 0;
        playingDirectoryDocId = intent.getStringExtra(EXTRA_DIRECTORY_DOC_ID);
        playingNavDocIds.clear();
        ArrayList<String> navDocIds = intent.getStringArrayListExtra(EXTRA_NAV_DOC_IDS);
        if (navDocIds != null) {
            playingNavDocIds.addAll(navDocIds);
        }
        playingNavNames.clear();
        ArrayList<String> navNames = intent.getStringArrayListExtra(EXTRA_NAV_NAMES);
        if (navNames != null) {
            playingNavNames.addAll(navNames);
        }
        usingFileAccess = intent.getBooleanExtra(EXTRA_USING_FILE_ACCESS, false);
        String rootTreeUriString = intent.getStringExtra(EXTRA_ROOT_TREE_URI);
        rootTreeUri = TextUtils.isEmpty(rootTreeUriString) ? null : Uri.parse(rootTreeUriString);
        rootDocId = intent.getStringExtra(EXTRA_ROOT_DOC_ID);
        if (TextUtils.isEmpty(rootDocId)) {
            rootDocId = null;
        }
        playCurrent(lastKnownPositionMs, intent.getBooleanExtra(EXTRA_AUTO_START, true), true);
    }

    private void playCurrent(int startPositionMs, boolean autoStart, boolean resetErrorRetry) {
        Track track = getCurrentTrack();
        if (track == null) {
            stopPlayback(true, true);
            return;
        }
        if (resetErrorRetry) {
            retryingCurrentTrack = false;
        }
        lastKnownPositionMs = Math.max(0, startPositionMs);
        lastPlaybackStateSaveAtMillis = 0L;
        releasePlayer();

        MediaPlayer nextPlayer = new MediaPlayer();
        mediaPlayer = nextPlayer;
        final int generation = ++playbackGeneration;
        playerReady = false;
        playerPreparing = true;
        durationMs = 0;
        ensureServiceStartedForPlayback();
        updateForegroundNotification();
        updateMediaSessionState();
        notifyStateChanged();

        nextPlayer.setAudioAttributes(new AudioAttributes.Builder()
                .setContentType(AudioAttributes.CONTENT_TYPE_MUSIC)
                .setUsage(AudioAttributes.USAGE_MEDIA)
                .build());
        try {
            nextPlayer.setWakeMode(getApplicationContext(), PowerManager.PARTIAL_WAKE_LOCK);
        } catch (RuntimeException exception) {
            Log.w(TAG, "Unable to set MediaPlayer wake mode", exception);
        }
        nextPlayer.setOnPreparedListener(player -> {
            if (!isCurrentPlayer(player, generation)) {
                return;
            }
            playerReady = true;
            playerPreparing = false;
            retryingCurrentTrack = false;
            durationMs = Math.max(0, player.getDuration());
            if (lastKnownPositionMs > 0) {
                int targetPosition = durationMs > 0
                        ? Math.min(lastKnownPositionMs, Math.max(0, durationMs - 1000))
                        : lastKnownPositionMs;
                try {
                    player.seekTo(targetPosition);
                    lastKnownPositionMs = targetPosition;
                } catch (IllegalStateException ignored) {
                }
            }
            if (autoStart) {
                startCurrentPlayer();
            } else {
                isPlaying = false;
                stopProgressUpdates();
                savePlaybackState();
                updateMediaSessionState();
                updateForegroundNotification();
                notifyStateChanged();
            }
        });
        nextPlayer.setOnCompletionListener(player -> {
            if (!isCurrentPlayer(player, generation)) {
                return;
            }
            retryingCurrentTrack = false;
            lastKnownPositionMs = 0;
            playNextAfterCompletion();
        });
        nextPlayer.setOnErrorListener((player, what, extra) -> handlePlaybackError(player, generation, what, extra));

        try {
            if (!TextUtils.isEmpty(track.filePath)) {
                nextPlayer.setDataSource(track.filePath);
            } else {
                nextPlayer.setDataSource(this, Uri.parse(track.uriString));
            }
            Log.i(TAG, "Preparing track in service: " + describeTrackForLog(track)
                    + ", startMs=" + lastKnownPositionMs + ", autoStart=" + autoStart);
            nextPlayer.prepareAsync();
        } catch (IOException | SecurityException | IllegalArgumentException exception) {
            handlePrepareFailure(nextPlayer, generation, track, exception);
        }
    }

    private void startCurrentPlayer() {
        if (mediaPlayer == null || !playerReady) {
            return;
        }
        if (!requestAudioFocus()) {
            notifyMessage(R.string.toast_playback_error);
            return;
        }
        try {
            mediaPlayer.start();
            isPlaying = true;
            playerPreparing = false;
            scheduleSleepTimer();
            startProgressUpdates();
            savePlaybackState();
            updateMediaSessionState();
            updateForegroundNotification();
            notifyStateChanged();
        } catch (IllegalStateException exception) {
            Log.e(TAG, "Failed to start track: " + describeTrackForLog(getCurrentTrack()), exception);
            keepCurrentTrackAfterPlaybackFailure(lastKnownPositionMs);
            notifyMessage(R.string.toast_playback_error);
        }
    }

    private void pausePlayback(boolean userRequested) {
        boolean paused = false;
        if (mediaPlayer != null && playerReady && isPlaying) {
            try {
                mediaPlayer.pause();
                paused = true;
            } catch (IllegalStateException exception) {
                Log.w(TAG, "Failed to pause track: " + describeTrackForLog(getCurrentTrack()), exception);
            }
        }
        updatePlaybackProgressFromPlayer();
        isPlaying = false;
        playerPreparing = false;
        stopProgressUpdates();
        if (userRequested) {
            abandonAudioFocus();
        }
        savePlaybackState();
        updateMediaSessionState();
        updateForegroundNotification();
        notifyStateChanged();
        if (paused && sleepTimerEnabled) {
            scheduleSleepTimer();
        }
    }

    private void playNextAfterCompletion() {
        if (currentIndex + 1 < queue.size()) {
            currentIndex++;
            playCurrent(0, true, true);
            return;
        }

        if (!moveToNextPlayableDirectoryAndPlay()) {
            clearSavedPlaybackState();
            stopPlayback(false, true);
            notifyMessage(R.string.toast_all_finished);
        }
    }

    private boolean moveToNextPlayableDirectoryAndPlay() {
        if (playingNavDocIds.isEmpty() || TextUtils.isEmpty(playingDirectoryDocId)) {
            return false;
        }

        NextDirectory nextDirectory = findNextPlayableDirectory(playingNavDocIds, playingNavNames);
        if (nextDirectory == null) {
            return false;
        }

        List<Track> nextTracks = listAudioTracks(nextDirectory.docId);
        if (nextTracks.isEmpty()) {
            return false;
        }

        playingDirectoryDocId = nextDirectory.docId;
        playingNavDocIds.clear();
        playingNavDocIds.addAll(nextDirectory.navDocIds);
        playingNavNames.clear();
        playingNavNames.addAll(nextDirectory.navNames);
        queue.clear();
        queue.addAll(nextTracks);
        currentIndex = 0;
        lastKnownPositionMs = 0;
        playCurrent(0, true, true);
        return true;
    }

    private void stopPlayback(boolean clearSavedState, boolean stopService) {
        releasePlayer();
        abandonAudioFocus();
        queue.clear();
        playingNavDocIds.clear();
        playingNavNames.clear();
        playingDirectoryDocId = null;
        currentIndex = -1;
        lastKnownPositionMs = 0;
        durationMs = 0;
        isPlaying = false;
        playerReady = false;
        playerPreparing = false;
        retryingCurrentTrack = false;
        disableSleepTimerSilently();
        if (clearSavedState) {
            clearSavedPlaybackState();
        }
        updateMediaSessionState();
        notifyStateChanged();
        if (foregroundStarted) {
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.N) {
                stopForeground(STOP_FOREGROUND_REMOVE);
            } else {
                stopForeground(true);
            }
            foregroundStarted = false;
        }
        if (stopService) {
            serviceStarted = false;
            stopSelf();
        }
    }

    private boolean handlePlaybackError(MediaPlayer player, int generation, int what, int extra) {
        if (!isCurrentPlayer(player, generation)) {
            Log.w(TAG, "Ignoring stale MediaPlayer error: what=" + what + ", extra=" + extra);
            return true;
        }

        int resumePositionMs = Math.max(lastKnownPositionMs, getPositionFromPlayer(player));
        boolean shouldAutoStart = isPlaying;
        Track failedTrack = getCurrentTrack();
        Log.e(TAG, "MediaPlayer service error: what=" + describeMediaError(what)
                + ", extra=" + describeMediaError(extra)
                + ", resumeMs=" + resumePositionMs
                + ", track=" + describeTrackForLog(failedTrack));

        if (failedTrack != null && !retryingCurrentTrack && what == MediaPlayer.MEDIA_ERROR_SERVER_DIED) {
            retryingCurrentTrack = true;
            notifyMessage(R.string.toast_playback_recovering);
            playCurrent(resumePositionMs, shouldAutoStart, false);
            return true;
        }

        keepCurrentTrackAfterPlaybackFailure(resumePositionMs);
        notifyMessage(R.string.toast_playback_error);
        return true;
    }

    private void handlePrepareFailure(
            MediaPlayer player,
            int generation,
            Track track,
            Exception exception) {
        if (!isCurrentPlayer(player, generation)) {
            Log.w(TAG, "Ignoring stale prepare failure: " + describeTrackForLog(track), exception);
            return;
        }
        Log.e(TAG, "Failed to prepare track in service: " + describeTrackForLog(track), exception);
        keepCurrentTrackAfterPlaybackFailure(lastKnownPositionMs);
        notifyMessage(R.string.toast_playback_error);
    }

    private void keepCurrentTrackAfterPlaybackFailure(int resumePositionMs) {
        lastKnownPositionMs = Math.max(0, resumePositionMs);
        releasePlayer();
        playerPreparing = false;
        isPlaying = false;
        abandonAudioFocus();
        savePlaybackState();
        updateMediaSessionState();
        updateForegroundNotification();
        notifyStateChanged();
    }

    private boolean isCurrentPlayer(MediaPlayer player, int generation) {
        return player != null && player == mediaPlayer && generation == playbackGeneration;
    }

    private void releasePlayer() {
        playbackGeneration++;
        stopProgressUpdates();
        if (mediaPlayer != null) {
            try {
                mediaPlayer.release();
            } catch (RuntimeException ignored) {
            }
            mediaPlayer = null;
        }
        playerReady = false;
        playerPreparing = false;
        isPlaying = false;
    }

    private void startProgressUpdates() {
        handler.removeCallbacks(progressRunnable);
        updatePlaybackProgressFromPlayer();
        if (isPlaying) {
            handler.postDelayed(progressRunnable, 1000L);
        }
    }

    private void stopProgressUpdates() {
        handler.removeCallbacks(progressRunnable);
    }

    private void updatePlaybackProgressFromPlayer() {
        refreshPlaybackProgressFields();
        maybeSavePlaybackStateDuringPlayback();
        updateMediaSessionState();
        notifyStateChanged();
    }

    private void refreshPlaybackProgressFields() {
        if (mediaPlayer == null || !playerReady) {
            return;
        }
        lastKnownPositionMs = getPositionFromPlayer(mediaPlayer);
        durationMs = getDurationFromPlayer(mediaPlayer);
    }

    private int getPositionFromPlayer(MediaPlayer player) {
        if (player == null) {
            return 0;
        }
        try {
            return Math.max(0, player.getCurrentPosition());
        } catch (IllegalStateException exception) {
            return 0;
        }
    }

    private int getDurationFromPlayer(MediaPlayer player) {
        if (player == null) {
            return 0;
        }
        try {
            return Math.max(0, player.getDuration());
        } catch (IllegalStateException exception) {
            return durationMs;
        }
    }

    private void maybeSavePlaybackStateDuringPlayback() {
        if (!isPlaying || getCurrentTrack() == null || prefs == null) {
            return;
        }
        long now = System.currentTimeMillis();
        if (now - lastPlaybackStateSaveAtMillis < PLAYBACK_STATE_SAVE_INTERVAL_MS) {
            return;
        }
        lastPlaybackStateSaveAtMillis = now;
        savePlaybackState();
    }

    private void scheduleSleepTimer() {
        handler.removeCallbacks(sleepRunnable);
        if (!sleepTimerEnabled || sleepEndAtMillis <= 0L) {
            notifyStateChanged();
            return;
        }
        handler.postDelayed(sleepRunnable, 1000L);
        notifyStateChanged();
    }

    private void updateSleepCountdown() {
        if (!sleepTimerEnabled) {
            handler.removeCallbacks(sleepRunnable);
            notifyStateChanged();
            return;
        }

        long remainingMillis = sleepEndAtMillis - System.currentTimeMillis();
        if (remainingMillis <= 0L) {
            disableSleepTimerSilently();
            pausePlayback(false);
            notifyMessage(R.string.toast_sleep_finished);
            return;
        }

        notifyStateChanged();
        handler.postDelayed(sleepRunnable, 1000L);
    }

    private void disableSleepTimerSilently() {
        sleepTimerEnabled = false;
        sleepEndAtMillis = 0L;
        handler.removeCallbacks(sleepRunnable);
    }

    private void createMediaSession() {
        mediaSession = new MediaSession(this, TAG);
        mediaSession.setCallback(new MediaSession.Callback() {
            @Override
            public void onPlay() {
                if (!isPlaying) {
                    togglePlayback();
                }
            }

            @Override
            public void onPause() {
                if (isPlaying) {
                    pausePlayback(true);
                }
            }

            @Override
            public void onSkipToPrevious() {
                playPrevious();
            }

            @Override
            public void onSkipToNext() {
                playNextByUser();
            }

            @Override
            public void onSeekTo(long pos) {
                seekToPosition((int) Math.min(Integer.MAX_VALUE, Math.max(0L, pos)));
            }

            @Override
            public void onStop() {
                stopPlayback(true, true);
            }
        });
        mediaSession.setActive(true);
        updateMediaSessionState();
    }

    private void updateMediaSessionState() {
        if (mediaSession == null) {
            return;
        }
        Track track = getCurrentTrack();
        int state;
        if (isPlaying) {
            state = PlaybackState.STATE_PLAYING;
        } else if (track != null) {
            state = PlaybackState.STATE_PAUSED;
        } else {
            state = PlaybackState.STATE_NONE;
        }

        long actions = PlaybackState.ACTION_PLAY
                | PlaybackState.ACTION_PAUSE
                | PlaybackState.ACTION_PLAY_PAUSE
                | PlaybackState.ACTION_SKIP_TO_PREVIOUS
                | PlaybackState.ACTION_SKIP_TO_NEXT
                | PlaybackState.ACTION_SEEK_TO
                | PlaybackState.ACTION_STOP;
        mediaSession.setPlaybackState(new PlaybackState.Builder()
                .setActions(actions)
                .setState(state, lastKnownPositionMs, isPlaying ? 1f : 0f)
                .build());

        if (track != null) {
            mediaSession.setMetadata(new MediaMetadata.Builder()
                    .putString(MediaMetadata.METADATA_KEY_TITLE, track.name)
                    .putLong(MediaMetadata.METADATA_KEY_DURATION, durationMs)
                    .build());
        } else {
            mediaSession.setMetadata(null);
        }
    }

    private void createNotificationChannel() {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.O || notificationManager == null) {
            return;
        }
        NotificationChannel channel = new NotificationChannel(
                CHANNEL_ID,
                getString(R.string.app_name),
                NotificationManager.IMPORTANCE_LOW);
        channel.setDescription(getString(R.string.notification_channel_description));
        channel.setShowBadge(false);
        notificationManager.createNotificationChannel(channel);
    }

    private void updateForegroundNotification() {
        if (getCurrentTrack() == null) {
            return;
        }
        Notification notification = buildNotification();
        if (!foregroundStarted) {
            try {
                startForeground(NOTIFICATION_ID, notification);
                foregroundStarted = true;
            } catch (RuntimeException exception) {
                Log.e(TAG, "Unable to start foreground playback service", exception);
            }
            return;
        }
        if (notificationManager != null) {
            notificationManager.notify(NOTIFICATION_ID, notification);
        }
    }

    private void ensureServiceStartedForPlayback() {
        if (serviceStarted) {
            return;
        }
        try {
            startService(new Intent(this, PlaybackService.class));
            serviceStarted = true;
        } catch (RuntimeException exception) {
            Log.w(TAG, "Unable to mark playback service as started", exception);
        }
    }

    private Notification buildNotification() {
        Track track = getCurrentTrack();
        Intent contentIntent = new Intent(this, MainActivity.class);
        contentIntent.setFlags(Intent.FLAG_ACTIVITY_SINGLE_TOP | Intent.FLAG_ACTIVITY_CLEAR_TOP);
        PendingIntent contentPendingIntent = PendingIntent.getActivity(
                this,
                0,
                contentIntent,
                pendingIntentFlags());

        PendingIntent previousIntent = getServicePendingIntent(ACTION_PREVIOUS, 1);
        PendingIntent toggleIntent = getServicePendingIntent(ACTION_TOGGLE, 2);
        PendingIntent nextIntent = getServicePendingIntent(ACTION_NEXT, 3);
        PendingIntent stopIntent = getServicePendingIntent(ACTION_STOP, 4);

        Notification.Action previousAction = new Notification.Action.Builder(
                android.R.drawable.ic_media_previous,
                getString(R.string.previous_track),
                previousIntent).build();
        Notification.Action toggleAction = new Notification.Action.Builder(
                isPlaying ? android.R.drawable.ic_media_pause : android.R.drawable.ic_media_play,
                getString(isPlaying ? R.string.pause : R.string.play),
                toggleIntent).build();
        Notification.Action nextAction = new Notification.Action.Builder(
                android.R.drawable.ic_media_next,
                getString(R.string.next_track),
                nextIntent).build();
        Notification.Action stopAction = new Notification.Action.Builder(
                android.R.drawable.ic_menu_close_clear_cancel,
                getString(R.string.stop_playback),
                stopIntent).build();

        Notification.Builder builder = Build.VERSION.SDK_INT >= Build.VERSION_CODES.O
                ? new Notification.Builder(this, CHANNEL_ID)
                : new Notification.Builder(this);
        builder.setSmallIcon(R.drawable.ic_notification)
                .setContentTitle(track == null ? getString(R.string.app_name) : track.name)
                .setContentText(getString(isPlaying ? R.string.notification_playing : R.string.notification_paused))
                .setContentIntent(contentPendingIntent)
                .setVisibility(Notification.VISIBILITY_PUBLIC)
                .setCategory(Notification.CATEGORY_TRANSPORT)
                .setOnlyAlertOnce(true)
                .setOngoing(isPlaying)
                .addAction(previousAction)
                .addAction(toggleAction)
                .addAction(nextAction)
                .addAction(stopAction)
                .setDeleteIntent(stopIntent)
                .setStyle(new Notification.MediaStyle()
                        .setMediaSession(mediaSession == null ? null : mediaSession.getSessionToken())
                        .setShowActionsInCompactView(0, 1, 2));
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            builder.setForegroundServiceBehavior(Notification.FOREGROUND_SERVICE_IMMEDIATE);
        }
        return builder.build();
    }

    private PendingIntent getServicePendingIntent(String action, int requestCode) {
        Intent intent = new Intent(this, PlaybackService.class);
        intent.setAction(action);
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            return PendingIntent.getForegroundService(this, requestCode, intent, pendingIntentFlags());
        }
        return PendingIntent.getService(this, requestCode, intent, pendingIntentFlags());
    }

    private int pendingIntentFlags() {
        int flags = PendingIntent.FLAG_UPDATE_CURRENT;
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
            flags |= PendingIntent.FLAG_IMMUTABLE;
        }
        return flags;
    }

    private boolean requestAudioFocus() {
        if (audioManager == null) {
            return true;
        }
        int result = audioManager.requestAudioFocus(
                audioFocusChangeListener,
                AudioManager.STREAM_MUSIC,
                AudioManager.AUDIOFOCUS_GAIN);
        return result == AudioManager.AUDIOFOCUS_REQUEST_GRANTED;
    }

    private void abandonAudioFocus() {
        if (audioManager != null) {
            audioManager.abandonAudioFocus(audioFocusChangeListener);
        }
    }

    private void setPlayerVolume(float volume) {
        if (mediaPlayer == null) {
            return;
        }
        try {
            mediaPlayer.setVolume(volume, volume);
        } catch (IllegalStateException ignored) {
        }
    }

    private void savePlaybackState() {
        Track track = getCurrentTrack();
        if (prefs == null || track == null) {
            return;
        }

        prefs.edit()
                .putString(PREF_PLAYBACK_TRACK_DOC_ID, track.docId)
                .putString(PREF_PLAYBACK_TRACK_NAME, track.name)
                .putString(PREF_PLAYBACK_TRACK_URI, track.uriString)
                .putString(PREF_PLAYBACK_TRACK_FILE_PATH, track.filePath)
                .putString(PREF_PLAYBACK_DIRECTORY_DOC_ID, playingDirectoryDocId == null ? "" : playingDirectoryDocId)
                .putString(PREF_PLAYBACK_NAV_DOC_IDS, toJsonArray(playingNavDocIds))
                .putString(PREF_PLAYBACK_NAV_NAMES, toJsonArray(playingNavNames))
                .putInt(PREF_PLAYBACK_INDEX, currentIndex)
                .putInt(PREF_PLAYBACK_POSITION_MS, Math.max(0, lastKnownPositionMs))
                .putBoolean(PREF_PLAYBACK_WAS_PLAYING, isPlaying)
                .apply();
    }

    private void clearSavedPlaybackState() {
        if (prefs == null) {
            return;
        }
        prefs.edit()
                .remove(PREF_PLAYBACK_TRACK_DOC_ID)
                .remove(PREF_PLAYBACK_TRACK_NAME)
                .remove(PREF_PLAYBACK_TRACK_URI)
                .remove(PREF_PLAYBACK_TRACK_FILE_PATH)
                .remove(PREF_PLAYBACK_DIRECTORY_DOC_ID)
                .remove(PREF_PLAYBACK_NAV_DOC_IDS)
                .remove(PREF_PLAYBACK_NAV_NAMES)
                .remove(PREF_PLAYBACK_INDEX)
                .remove(PREF_PLAYBACK_POSITION_MS)
                .remove(PREF_PLAYBACK_WAS_PLAYING)
                .apply();
    }

    private void restoreSavedPlaybackIfPossible() {
        if (prefs == null) {
            return;
        }
        String savedTrackDocId = prefs.getString(PREF_PLAYBACK_TRACK_DOC_ID, null);
        if (TextUtils.isEmpty(savedTrackDocId)) {
            return;
        }

        restoreAccessStateFromPrefs();
        String savedDirectoryDocId = prefs.getString(PREF_PLAYBACK_DIRECTORY_DOC_ID, null);
        if (TextUtils.isEmpty(savedDirectoryDocId)) {
            return;
        }

        ArrayList<String> savedNavDocIds = readJsonArray(prefs.getString(PREF_PLAYBACK_NAV_DOC_IDS, null));
        ArrayList<String> savedNavNames = readJsonArray(prefs.getString(PREF_PLAYBACK_NAV_NAMES, null));
        if (savedNavDocIds.isEmpty()) {
            savedNavDocIds.add(savedDirectoryDocId);
        }
        if (savedNavNames.isEmpty()) {
            savedNavNames.add(queryDocumentName(savedDirectoryDocId));
        }

        List<Track> tracks = listAudioTracks(savedDirectoryDocId);
        int savedIndex = prefs.getInt(PREF_PLAYBACK_INDEX, -1);
        int restoreIndex = indexOfTrack(tracks, savedTrackDocId);
        if (restoreIndex < 0 && savedIndex >= 0 && savedIndex < tracks.size()) {
            restoreIndex = savedIndex;
        }
        if (restoreIndex < 0) {
            clearSavedPlaybackState();
            return;
        }

        queue.clear();
        queue.addAll(tracks);
        currentIndex = restoreIndex;
        playingDirectoryDocId = savedDirectoryDocId;
        playingNavDocIds.clear();
        playingNavDocIds.addAll(savedNavDocIds);
        playingNavNames.clear();
        playingNavNames.addAll(savedNavNames);
        lastKnownPositionMs = Math.max(0, prefs.getInt(PREF_PLAYBACK_POSITION_MS, 0));
        durationMs = 0;
        boolean wasPlaying = prefs.getBoolean(PREF_PLAYBACK_WAS_PLAYING, false);
        notifyStateChanged();
        if (wasPlaying) {
            playCurrent(lastKnownPositionMs, true, true);
        } else {
            updateMediaSessionState();
        }
    }

    private void restoreAccessStateFromPrefs() {
        String accessMode = prefs.getString(PREF_ACCESS_MODE, null);
        if (ACCESS_MODE_FILE.equals(accessMode) && canUseDirectFileBrowsing()) {
            usingFileAccess = true;
            rootTreeUri = null;
            rootDocId = null;
            return;
        }
        usingFileAccess = false;
        String uriString = prefs.getString(PREF_ROOT_TREE_URI, null);
        rootTreeUri = TextUtils.isEmpty(uriString) ? null : Uri.parse(uriString);
        rootDocId = prefs.getString(PREF_ROOT_DOC_ID, null);
        if (TextUtils.isEmpty(rootDocId) && rootTreeUri != null) {
            rootDocId = DocumentsContract.getTreeDocumentId(rootTreeUri);
        }
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

    private boolean hasPersistedReadPermission(Uri uri) {
        if (uri == null) {
            return false;
        }
        for (android.content.UriPermission permission : getContentResolver().getPersistedUriPermissions()) {
            if (permission.isReadPermission() && permission.getUri().equals(uri)) {
                return true;
            }
        }
        return false;
    }

    private List<Track> listAudioTracks(String docId) {
        List<Track> tracks = new ArrayList<>();
        for (PlaybackItem item : listPlayableChildren(docId)) {
            if (item.isAudio) {
                tracks.add(item.toTrack());
            }
        }
        return tracks;
    }

    private List<PlaybackItem> listPlayableChildren(String docId) {
        if (TextUtils.isEmpty(docId)) {
            return new ArrayList<>();
        }
        if (usingFileAccess) {
            return listPlayableFileChildren(new File(docId));
        }
        if (rootTreeUri == null || !hasPersistedReadPermission(rootTreeUri)) {
            return new ArrayList<>();
        }

        List<PlaybackItem> folders = new ArrayList<>();
        List<PlaybackItem> audios = new ArrayList<>();
        Uri childrenUri = DocumentsContract.buildChildDocumentsUriUsingTree(rootTreeUri, docId);
        String[] projection = {
                DocumentsContract.Document.COLUMN_DOCUMENT_ID,
                DocumentsContract.Document.COLUMN_DISPLAY_NAME,
                DocumentsContract.Document.COLUMN_MIME_TYPE
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
                PlaybackItem item = new PlaybackItem(childDocId, name, mimeType, uri.toString(), "", isDirectory, isAudio);
                if (isDirectory) {
                    folders.add(item);
                } else if (isAudio) {
                    audios.add(item);
                }
            }
        } catch (RuntimeException exception) {
            Log.e(TAG, "Unable to list SAF directory: " + docId, exception);
        }

        Collections.sort(folders, (left, right) -> compareNatural(left.name, right.name));
        Collections.sort(audios, (left, right) -> compareNatural(left.name, right.name));
        List<PlaybackItem> items = new ArrayList<>(folders.size() + audios.size());
        items.addAll(folders);
        items.addAll(audios);
        return items;
    }

    private List<PlaybackItem> listPlayableFileChildren(File directory) {
        List<PlaybackItem> folders = new ArrayList<>();
        List<PlaybackItem> audios = new ArrayList<>();
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
                folders.add(new PlaybackItem(
                        child.getAbsolutePath(),
                        name,
                        DocumentsContract.Document.MIME_TYPE_DIR,
                        Uri.fromFile(child).toString(),
                        child.getAbsolutePath(),
                        true,
                        false));
            } else if (child.isFile() && isAudioFile(name, null)) {
                audios.add(new PlaybackItem(
                        child.getAbsolutePath(),
                        name,
                        "audio/*",
                        Uri.fromFile(child).toString(),
                        child.getAbsolutePath(),
                        false,
                        true));
            }
        }

        Collections.sort(folders, (left, right) -> compareNatural(left.name, right.name));
        Collections.sort(audios, (left, right) -> compareNatural(left.name, right.name));
        List<PlaybackItem> items = new ArrayList<>(folders.size() + audios.size());
        items.addAll(folders);
        items.addAll(audios);
        return items;
    }

    private NextDirectory findNextPlayableDirectory(List<String> baseDocIds, List<String> baseNames) {
        if (baseDocIds == null || baseDocIds.isEmpty()) {
            return null;
        }

        String parentDocId;
        String currentDocId;
        int prefixSize;
        if (baseDocIds.size() == 1) {
            parentDocId = baseDocIds.get(0);
            currentDocId = null;
            prefixSize = 1;
        } else {
            parentDocId = baseDocIds.get(baseDocIds.size() - 2);
            currentDocId = baseDocIds.get(baseDocIds.size() - 1);
            prefixSize = baseDocIds.size() - 1;
        }

        List<PlaybackItem> siblingItems = listPlayableChildren(parentDocId);
        List<PlaybackItem> siblingDirectories = new ArrayList<>();
        for (PlaybackItem item : siblingItems) {
            if (item.isDirectory) {
                siblingDirectories.add(item);
            }
        }

        int startIndex = 0;
        if (currentDocId != null) {
            startIndex = -1;
            for (int index = 0; index < siblingDirectories.size(); index++) {
                if (siblingDirectories.get(index).docId.equals(currentDocId)) {
                    startIndex = index + 1;
                    break;
                }
            }
            if (startIndex < 0) {
                startIndex = 0;
            }
        }

        for (int index = startIndex; index < siblingDirectories.size(); index++) {
            PlaybackItem directory = siblingDirectories.get(index);
            if (!listAudioTracks(directory.docId).isEmpty()) {
                ArrayList<String> nextDocIds = new ArrayList<>(baseDocIds.subList(0, prefixSize));
                ArrayList<String> nextNames = new ArrayList<>(baseNames.subList(0, Math.min(prefixSize, baseNames.size())));
                nextDocIds.add(directory.docId);
                nextNames.add(directory.name);
                return new NextDirectory(directory.docId, directory.name, nextDocIds, nextNames);
            }
        }

        return null;
    }

    private String queryDocumentName(String docId) {
        if (usingFileAccess) {
            File file = new File(docId);
            return TextUtils.isEmpty(file.getName()) ? getString(R.string.storage_root) : file.getName();
        }
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
        return docId;
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

    private int indexOfTrack(List<Track> tracks, String docId) {
        for (int index = 0; index < tracks.size(); index++) {
            if (tracks.get(index).docId.equals(docId)) {
                return index;
            }
        }
        return -1;
    }

    private Track getCurrentTrack() {
        if (currentIndex < 0 || currentIndex >= queue.size()) {
            return null;
        }
        return queue.get(currentIndex);
    }

    private void notifyStateChanged() {
        if (listeners.isEmpty()) {
            return;
        }
        Snapshot snapshot = getSnapshotWithoutRefreshing();
        for (Listener listener : new ArrayList<>(listeners)) {
            listener.onPlaybackStateChanged(snapshot);
        }
    }

    private Snapshot getSnapshotWithoutRefreshing() {
        return new Snapshot(
                getCurrentTrack(),
                currentIndex,
                lastKnownPositionMs,
                durationMs,
                isPlaying,
                playerReady,
                playerPreparing,
                sleepTimerEnabled,
                sleepMinutes,
                Math.max(0L, sleepEndAtMillis - System.currentTimeMillis()),
                playingDirectoryDocId,
                new ArrayList<>(queue),
                new ArrayList<>(playingNavDocIds),
                new ArrayList<>(playingNavNames),
                usingFileAccess,
                rootTreeUri == null ? null : rootTreeUri.toString(),
                rootDocId);
    }

    private void notifyMessage(int stringResId) {
        for (Listener listener : new ArrayList<>(listeners)) {
            listener.onPlaybackMessage(stringResId);
        }
    }

    private String describeMediaError(int errorCode) {
        switch (errorCode) {
            case MediaPlayer.MEDIA_ERROR_UNKNOWN:
                return "MEDIA_ERROR_UNKNOWN(" + errorCode + ")";
            case MediaPlayer.MEDIA_ERROR_SERVER_DIED:
                return "MEDIA_ERROR_SERVER_DIED(" + errorCode + ")";
            case MediaPlayer.MEDIA_ERROR_IO:
                return "MEDIA_ERROR_IO(" + errorCode + ")";
            case MediaPlayer.MEDIA_ERROR_MALFORMED:
                return "MEDIA_ERROR_MALFORMED(" + errorCode + ")";
            case MediaPlayer.MEDIA_ERROR_UNSUPPORTED:
                return "MEDIA_ERROR_UNSUPPORTED(" + errorCode + ")";
            case MediaPlayer.MEDIA_ERROR_TIMED_OUT:
                return "MEDIA_ERROR_TIMED_OUT(" + errorCode + ")";
            default:
                return "code(" + errorCode + ")";
        }
    }

    private String describeTrackForLog(Track track) {
        if (track == null) {
            return "none";
        }
        String source = !TextUtils.isEmpty(track.filePath) ? track.filePath : track.uriString;
        return "\"" + track.name + "\" [" + source + "]";
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

    public interface Listener {
        void onPlaybackStateChanged(Snapshot snapshot);

        void onPlaybackMessage(int stringResId);
    }

    public class LocalBinder extends Binder {
        PlaybackService getService() {
            return PlaybackService.this;
        }
    }

    public static class Track {
        final String docId;
        final String name;
        final String mimeType;
        final String uriString;
        final String filePath;

        Track(String docId, String name, String mimeType, String uriString, String filePath) {
            this.docId = emptyIfNull(docId);
            this.name = emptyIfNull(name);
            this.mimeType = emptyIfNull(mimeType);
            this.uriString = emptyIfNull(uriString);
            this.filePath = emptyIfNull(filePath);
        }
    }

    public static class Snapshot {
        final Track currentTrack;
        final int currentIndex;
        final int positionMs;
        final int durationMs;
        final boolean isPlaying;
        final boolean playerReady;
        final boolean playerPreparing;
        final boolean sleepTimerEnabled;
        final int sleepMinutes;
        final long sleepRemainingMillis;
        final String playingDirectoryDocId;
        final ArrayList<Track> queue;
        final ArrayList<String> navDocIds;
        final ArrayList<String> navNames;
        final boolean usingFileAccess;
        final String rootTreeUriString;
        final String rootDocId;

        Snapshot(
                Track currentTrack,
                int currentIndex,
                int positionMs,
                int durationMs,
                boolean isPlaying,
                boolean playerReady,
                boolean playerPreparing,
                boolean sleepTimerEnabled,
                int sleepMinutes,
                long sleepRemainingMillis,
                String playingDirectoryDocId,
                ArrayList<Track> queue,
                ArrayList<String> navDocIds,
                ArrayList<String> navNames,
                boolean usingFileAccess,
                String rootTreeUriString,
                String rootDocId) {
            this.currentTrack = currentTrack;
            this.currentIndex = currentIndex;
            this.positionMs = positionMs;
            this.durationMs = durationMs;
            this.isPlaying = isPlaying;
            this.playerReady = playerReady;
            this.playerPreparing = playerPreparing;
            this.sleepTimerEnabled = sleepTimerEnabled;
            this.sleepMinutes = sleepMinutes;
            this.sleepRemainingMillis = sleepRemainingMillis;
            this.playingDirectoryDocId = playingDirectoryDocId;
            this.queue = queue;
            this.navDocIds = navDocIds;
            this.navNames = navNames;
            this.usingFileAccess = usingFileAccess;
            this.rootTreeUriString = rootTreeUriString;
            this.rootDocId = rootDocId;
        }
    }

    private static class PlaybackItem {
        final String docId;
        final String name;
        final String mimeType;
        final String uriString;
        final String filePath;
        final boolean isDirectory;
        final boolean isAudio;

        PlaybackItem(String docId, String name, String mimeType, String uriString, String filePath, boolean isDirectory, boolean isAudio) {
            this.docId = emptyIfNull(docId);
            this.name = emptyIfNull(name);
            this.mimeType = emptyIfNull(mimeType);
            this.uriString = emptyIfNull(uriString);
            this.filePath = emptyIfNull(filePath);
            this.isDirectory = isDirectory;
            this.isAudio = isAudio;
        }

        Track toTrack() {
            return new Track(docId, name, mimeType, uriString, filePath);
        }
    }

    private static class NextDirectory {
        final String docId;
        final String name;
        final ArrayList<String> navDocIds;
        final ArrayList<String> navNames;

        NextDirectory(String docId, String name, ArrayList<String> navDocIds, ArrayList<String> navNames) {
            this.docId = docId;
            this.name = name;
            this.navDocIds = navDocIds;
            this.navNames = navNames;
        }
    }

    private static String emptyIfNull(String value) {
        return value == null ? "" : value;
    }
}
