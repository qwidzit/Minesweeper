package com.minesweeper.archive;

import android.annotation.SuppressLint;
import android.app.Activity;
import android.os.Bundle;
import android.view.View;
import android.webkit.JavascriptInterface;
import android.webkit.WebSettings;
import android.webkit.WebView;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;

/** Hosts the game (assets/index.html) in a full-window WebView. */
public class MainActivity extends Activity {

    private static final String ARCHIVE_FILE = "archive.json";

    private WebView web;

    @SuppressLint("SetJavaScriptEnabled")
    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);

        web = new WebView(this);
        web.setBackgroundColor(0xFF14171D);
        web.setOverScrollMode(View.OVER_SCROLL_NEVER);
        web.setVerticalScrollBarEnabled(false);
        web.setHorizontalScrollBarEnabled(false);
        web.setHapticFeedbackEnabled(false);

        WebSettings settings = web.getSettings();
        settings.setJavaScriptEnabled(true);
        settings.setDomStorageEnabled(true);
        settings.setSupportZoom(false);
        settings.setTextZoom(100);   // ignore the system font scale so the layout stays as designed

        web.addJavascriptInterface(new Storage(), "Android");
        setContentView(web);
        web.loadUrl("file:///android_asset/index.html");
    }

    @Override
    public void onBackPressed() {
        // The page closes its own overlays; back only leaves the app from the setup screen.
        web.evaluateJavascript("window.handleBack ? window.handleBack() : 'exit'", result -> {
            if ("\"exit\"".equals(result)) finish();
        });
    }

    @Override
    protected void onDestroy() {
        web.destroy();
        super.onDestroy();
    }

    /** Persists the archive as a JSON file in the app's private storage. */
    private final class Storage {

        @JavascriptInterface
        public synchronized String load() {
            File file = new File(getFilesDir(), ARCHIVE_FILE);
            if (!file.exists()) return "";
            try {
                return new String(Files.readAllBytes(file.toPath()), StandardCharsets.UTF_8);
            } catch (IOException e) {
                return "";
            }
        }

        @JavascriptInterface
        public synchronized void save(String json) {
            File file = new File(getFilesDir(), ARCHIVE_FILE);
            File tmp = new File(getFilesDir(), ARCHIVE_FILE + ".tmp");
            try {
                try (FileOutputStream out = new FileOutputStream(tmp)) {
                    out.write(json.getBytes(StandardCharsets.UTF_8));
                    out.getFD().sync();
                }
                if (!tmp.renameTo(file)) tmp.delete();
            } catch (IOException e) {
                tmp.delete();
            }
        }
    }
}
