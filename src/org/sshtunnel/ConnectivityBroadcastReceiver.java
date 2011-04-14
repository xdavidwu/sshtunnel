package org.sshtunnel;

import java.util.ArrayList;

import android.app.ActivityManager;
import android.app.AlertDialog;
import android.app.Notification;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.app.ActivityManager.RunningServiceInfo;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.DialogInterface;
import android.content.Intent;
import android.content.SharedPreferences;
import android.net.ConnectivityManager;
import android.net.NetworkInfo;
import android.preference.PreferenceManager;
import android.util.Log;

public class ConnectivityBroadcastReceiver extends BroadcastReceiver {

	private static final String TAG = "ConnectivityBroadcastReceiver";

	public boolean isWorked(Context context, String service) {
		ActivityManager myManager = (ActivityManager) context
				.getSystemService(Context.ACTIVITY_SERVICE);
		ArrayList<RunningServiceInfo> runningService = (ArrayList<RunningServiceInfo>) myManager
				.getRunningServices(30);
		for (int i = 0; i < runningService.size(); i++) {
			if (runningService.get(i).service.getClassName().toString()
					.equals(service)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public synchronized void onReceive(Context context, Intent intent) {
		String action = intent.getAction();

		if (!action.equals(ConnectivityManager.CONNECTIVITY_ACTION)) {
			Log.w(TAG, "onReceived() called uncorrectly");
			return;
		}

		Log.e(TAG, "Connection Test");

		if (!isOnline(context)) {
			if (isWorked(context, SSHTunnel.SERVICE_NAME)) {
				try {
					context.stopService(new Intent(context,
							SSHTunnelService.class));
				} catch (Exception e) {
					// Nothing
				}
			}
		} else {

			NotificationManager notificationManager = (NotificationManager) context
					.getSystemService(context.NOTIFICATION_SERVICE);
			Notification notification = new Notification();
			intent = new Intent(context, SSHTunnel.class);
			intent.setFlags(Intent.FLAG_ACTIVITY_CLEAR_TOP);
			PendingIntent pendIntent = PendingIntent.getActivity(context, 0, intent, 0);
			
			notification.icon = R.drawable.ic_stat;
			notification.tickerText = context.getString(R.string.auto_connecting);
			notification.flags = Notification.FLAG_ONGOING_EVENT;
			
			notification.setLatestEventInfo(context, context.getString(R.string.app_name),
					context.getString(R.string.auto_connecting), pendIntent);
			notificationManager.notify(1, notification);
			
//			// Wait for connection stable
//			try {
//				Thread.sleep();
//			} catch (InterruptedException ignore) {
//				// Nothing
//			}
			
			if (!isWorked(context, SSHTunnel.SERVICE_NAME)) {
				SSHTunnelReceiver sshr = new SSHTunnelReceiver();
				sshr.onReceive(context, intent);
			}
		}

	}

	public boolean isOnline(Context context) {
		ConnectivityManager manager = (ConnectivityManager) context
				.getSystemService(Context.CONNECTIVITY_SERVICE);
		NetworkInfo networkInfo = manager.getActiveNetworkInfo();
		if (networkInfo == null)
			return false;
		return true;
	}

}