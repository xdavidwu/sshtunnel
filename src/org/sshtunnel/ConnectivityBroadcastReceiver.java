package org.sshtunnel;

import java.util.List;
import java.util.Set;

import android.os.Handler;
import org.sshtunnel.db.Profile;
import org.sshtunnel.db.ProfileFactory;
import org.sshtunnel.utils.Constraints;
import org.sshtunnel.utils.Utils;

import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.content.SharedPreferences.Editor;
import android.net.ConnectivityManager;
import android.net.NetworkInfo;
import android.net.wifi.WifiInfo;
import android.net.wifi.WifiManager;
import android.os.Bundle;
import android.preference.PreferenceManager;
import android.util.Log;

public class ConnectivityBroadcastReceiver extends BroadcastReceiver {

    private static final String TAG = "SSHTunnel";

    public String onlineSSID(Context context, Set<String> ssids) {
	if (ssids.isEmpty())
            return null;
        ConnectivityManager manager = (ConnectivityManager) context
                .getSystemService(Context.CONNECTIVITY_SERVICE);
        NetworkInfo networkInfo = manager.getActiveNetworkInfo();
        if (networkInfo == null)
            return null;
        if (!networkInfo.getTypeName().equals("WIFI")) {
            for (String item : ssids) {
                if (item.equals(Constraints.WIFI_AND_3G))
                    return item;
                if (item.equals(Constraints.ONLY_3G))
                    return item;
            }
            return null;
        }
        WifiManager wm = (WifiManager) context.getApplicationContext()
                .getSystemService(Context.WIFI_SERVICE);
        WifiInfo wInfo = wm.getConnectionInfo();
        if (wInfo == null)
            return null;
        String current = wInfo.getSSID();
        if (current == null || current.equals(""))
            return null;
        for (String item : ssids) {
            if (item.equals(Constraints.WIFI_AND_3G))
                return item;
            if (item.equals(Constraints.ONLY_WIFI))
                return item;
            if (item.equals(current))
                return item;
        }
        return null;
    }

    @Override
    public void onReceive(final Context context, final Intent intent) {
        String action = intent.getAction();
        if (!action.equals(ConnectivityManager.CONNECTIVITY_ACTION)) {
            Log.w(TAG, "onReceived() called uncorrectly");
            return;
        }

        Handler handler = new Handler(context.getMainLooper());

        handler.postDelayed(new Runnable() {
            @Override
            public void run() {
                SharedPreferences settings = PreferenceManager
                        .getDefaultSharedPreferences(context);

                if (SSHTunnelService.isConnecting
                        || SSHTunnelService.isStopping)
                    return;

                // only switching profiles when needed
                ConnectivityManager manager = (ConnectivityManager) context
                        .getSystemService(Context.CONNECTIVITY_SERVICE);
                NetworkInfo networkInfo = manager.getActiveNetworkInfo();
                if (networkInfo == null) {
                    if (Utils.isWorked()) {
                        Log.d(TAG, "onConnectionLost");
                        context.stopService(new Intent(context, SSHTunnelService.class));
                        return;
                    }
                }

                // Save current settings first
                ProfileFactory.getProfile();
                ProfileFactory.loadFromPreference();

                String curSSID = null;
                List<Profile> profileList = ProfileFactory.loadAllProfilesFromDao();
                int profileId = -1;

                if (profileList == null)
                    return;

                // Test on each profile
                for (Profile profile : profileList) {

                    curSSID = onlineSSID(context, profile.getSsid());
                    if (profile.isAutoConnect() && curSSID != null) {

                        // Then switch profile values
                        profileId = profile.getId();
                        break;
                    }
                }

                if (curSSID != null && profileId != -1) {
                    if (!Utils.isWorked()) {

                        Editor ed = settings.edit();
                        ed.putString("lastSSID", curSSID);
                        ed.apply();

                        Utils.notifyConnect();

                        Intent it = new Intent(context, SSHTunnelService.class);
                        Bundle bundle = new Bundle();
                        bundle.putInt(Constraints.ID, profileId);
                        it.putExtras(bundle);
                        context.startService(it);
                        SSHTunnelService.isConnecting = true;
                        Log.d(TAG, "onConnected");
                    }
                }
            }
        }, 2000);
    }

}
