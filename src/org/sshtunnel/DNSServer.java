package org.sshtunnel;

import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.preference.PreferenceManager;
import android.util.Log;
import org.apache.commons.validator.routines.DomainValidator;
import org.sshtunnel.utils.Base64;
import org.sshtunnel.utils.InnerSocketBuilder;
import org.sshtunnel.utils.Utils;

import java.io.*;
import java.net.*;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Random;
import java.util.regex.Pattern;
import java.util.regex.Matcher;

/**
 * 此类封装了一个Dns回应
 *
 * @author biaji
 */
class DnsResponse implements Serializable {

    private static final long serialVersionUID = -6693216674221293274L;
    private String request = null;
    private long timestamp = System.currentTimeMillis();
    private int reqTimes = 0;
    private byte[] dnsResponse = null;

    public DnsResponse(String request) {
        this.request = request;
    }

    /**
     * @return the dnsResponse
     */
    public byte[] getDnsResponse() {
        this.reqTimes++;
        return dnsResponse;
    }

    /**
     * @param dnsResponse the dnsResponse to set
     */
    public void setDnsResponse(byte[] dnsResponse) {
        this.dnsResponse = dnsResponse;
    }

    /**
     * @return IP string
     */
    public String getIPString() {
        String ip = null;
        int i;

        if (dnsResponse == null) {
            return null;
        }

        i = dnsResponse.length - 4;

        if (i < 0) {
            return null;
        }

        ip = "" + (dnsResponse[i] & 0xFF); /* Unsigned byte to int */

        for (i++; i < dnsResponse.length; i++) {
            ip += "." + (dnsResponse[i] & 0xFF);
        }

        return ip;
    }

    /**
     * @return the reqTimes
     */
    public int getReqTimes() {
        return reqTimes;
    }

    public String getRequest() {
        return this.request;
    }

    /**
     * @return the timestamp
     */
    public long getTimestamp() {
        return timestamp;
    }
}

/**
 * 此类实现了DNS代理
 *
 * @author biaji
 */
public class DNSServer implements Runnable {

    private final static int MAX_THREAD_NUM = 5;
    private static final String CANT_RESOLVE = "Error";
    final protected int DNS_PKG_HEADER_LEN = 12;
    private final String TAG = "SSHTunnel";
    private final String CACHE_PATH = "/cache";
    private final String CACHE_FILE = "/dnscache";
    final private int[] DNS_HEADERS = {0, 0, 0x81, 0x80, 0, 0, 0, 0, 0, 0, 0,
            0};
    final private int[] DNS_PAYLOAD = {0xc0, 0x0c, 0x00}; //0x01, NAME and first byte of TYPE
    final private int[] DNS_PAYLOAD_2 = {0x00, 0x01, 0x00, 0x00, 0x00, 0x3c, 0x00};
    					//--CLASS-- -----------TTL--------- RDLENGTH first byte
    final private int IP_SECTION_LEN = 4;
    final private int TYPE_A = 0x01;
    final private int TYPE_AAAA = 0x1c;
    public HashSet<String> domains;
    protected Context context;
    private String homePath;
    private DatagramSocket srvSocket;
    private int srvPort = 0;
    private volatile int threadNum = 0;
    private boolean inService = false;
    private Hashtable<String, DnsResponse> dnsCache = new Hashtable<String, DnsResponse>();

    public DNSServer(Context context) {
        this.context = context;

        domains = new HashSet<String>();

    }

   /**
     * 在缓存中添加一个域名解析
     *
     * @param questDomainName 域名
     * @param answer          解析结果
     */
    private synchronized void addToCache(String questDomainName, byte[] answer) {
        DnsResponse response = new DnsResponse(questDomainName);
        response.setDnsResponse(answer);
        dnsCache.put(questDomainName, response);
        saveCache();
    }

    public void close() throws IOException {
        inService = false;
        if (srvSocket != null) {
            srvSocket.close();
            srvSocket = null;
        }
        saveCache();
        Log.i(TAG, "DNS Stopped");
    }

    /*
     * Create a DNS response packet, which will send back to application.
     *
     * @author yanghong
     *
     * Reference to:
     *
     * Mini Fake DNS server (Python)
     * http://code.activestate.com/recipes/491264-mini-fake-dns-server/
     *
     * DOMAIN NAMES - IMPLEMENTATION AND SPECIFICATION
     * http://www.ietf.org/rfc/rfc1035.txt
     */
    protected byte[] createDNSResponse(byte[] quest, byte[] ips, int type) {
        byte[] response = null;
        int start = 0;

        response = new byte[128];

        for (int val : DNS_HEADERS) {
            response[start] = (byte) val;
            start++;
        }

        System.arraycopy(quest, 0, response, 0, 2); /* 0:2 */
        System.arraycopy(quest, 4, response, 4, 2); /* 4:6 -> 4:6 QDCOUNT */
        System.arraycopy(quest, 4, response, 6, 2); /* 4:6 -> 6:8 ANCOUNT */
        System.arraycopy(quest, DNS_PKG_HEADER_LEN, response, start,
                quest.length - DNS_PKG_HEADER_LEN); /* 12:~ -> 15:~ */
        start += quest.length - DNS_PKG_HEADER_LEN;

        if (ips == null) { //NXDOMAIN
		response[3] = (byte) 0x83; // name error 3 in RCODE
		response[6] = (byte) 0x00; // clear ANCOUNT
		response[7] = (byte) 0x00;
		Log.e(TAG, "NXDOMAIN TYPE: " + type);
	}
	else {

		for (int val : DNS_PAYLOAD) {
			response[start] = (byte) val;
			start++;
		}
		response[start] = (byte) type;
		start++;

		for (int val : DNS_PAYLOAD_2) {
			response[start] = (byte) val;
			start++;
		}
		/* RFC 1035: name is 255 octets or less, which is our max
		 * so edit last 1 byte of RDLENGTH should be enough */
		Log.d(TAG, "TYPE: " + type + " RDLENGTH: " + ips.length);
		response[start] = (byte) ips.length;
		start++;

		/* IP address in response */
		for (byte ip : ips) {
			response[start] = ip;
			start++;
		}
	}

        byte[] result = new byte[start];
        System.arraycopy(response, 0, result, 0, start);

        return result;
    }

    public byte[] fetchAnswerHTTP(byte[] quest, int type) {
        byte[] result = null;
        String domain = getRequestDomain(quest);
        String ip = null;

        DomainValidator dv = DomainValidator.getInstance();

		/* Not support reverse domain name query */
        if (domain.endsWith("in-addr.arpa") || domain.endsWith("ip6.arpa") || !dv.isValid(domain)) {
            return createDNSResponse(quest, parseIPString("127.0.0.1"), TYPE_A);
            // return null;
        }

	if (type != TYPE_AAAA) type = TYPE_A;

        ip = resolveDomainName(domain,type);

        if (ip == null) {
            Log.e(TAG, "Failed to resolve domain name: " + domain);
            return null;
        }

        if (ip.equals(CANT_RESOLVE)) {
            return createDNSResponse(quest, null, type);
        }

	byte[] ips = null;

        if (type == TYPE_A) ips = parseIPString(ip);
	else if (type == TYPE_AAAA) {
		try {
			ips = InetAddress.getByName(ip).getAddress();
		}
		catch (UnknownHostException e) {
			Log.e(TAG, e.getLocalizedMessage(), e);
		}
	}

        if (ips != null) {
            result = createDNSResponse(quest, ips, type);
        }

        return result;
    }

    /**
     * 获取UDP DNS请求的域名
     *
     * @param request dns udp包
     * @return 请求的域名
     */
    protected String getRequestDomain(byte[] request) {
        String requestDomain = "";
        int reqLength = request.length;
        if (reqLength > 13) { // 包含包体
            byte[] question = new byte[reqLength - 12];
            System.arraycopy(request, 12, question, 0, reqLength - 12);
            requestDomain = parseDomain(question);
            if (requestDomain.length() > 1)
                requestDomain = requestDomain.substring(0,
                        requestDomain.length() - 1);
        }
        return requestDomain;
    }

    public int getServPort() {
        return this.srvPort;
    }

    public int init() {
        try {
            srvSocket = new DatagramSocket(0,
                    InetAddress.getByName("127.0.0.1"));
            inService = true;
            srvPort = srvSocket.getLocalPort();
        } catch (SocketException e) {
            Log.e(TAG, "DNSServer init error: " + srvPort, e);
        } catch (UnknownHostException e) {
            Log.e(TAG, "DNSServer init error: " + srvPort, e);
        }
        return srvPort;
    }

    public boolean isClosed() {
        return srvSocket.isClosed();
    }

    public boolean isInService() {
        return inService;
    }

    /**
     * 由缓存载入域名解析缓存
     */
    private void loadCache() {
        ObjectInputStream ois = null;
        File cache = new File(homePath + CACHE_PATH + CACHE_FILE);
        try {
            if (!cache.exists())
                return;
            ois = new ObjectInputStream(new FileInputStream(cache));
            dnsCache = (Hashtable<String, DnsResponse>) ois.readObject();
            ois.close();
            ois = null;

            Hashtable<String, DnsResponse> tmpCache = (Hashtable<String, DnsResponse>) dnsCache
                    .clone();
            for (DnsResponse resp : dnsCache.values()) {
                // 检查缓存时效(五天)
                if ((System.currentTimeMillis() - resp.getTimestamp()) > 432000000L) {
                    Log.d(TAG, "Delete " + resp.getRequest());
                    tmpCache.remove(resp.getRequest());
                }
            }

            dnsCache = tmpCache;
            tmpCache = null;

        } catch (ClassCastException e) {
            Log.e(TAG, e.getLocalizedMessage(), e);
        } catch (FileNotFoundException e) {
            Log.e(TAG, e.getLocalizedMessage(), e);
        } catch (IOException e) {
            Log.e(TAG, e.getLocalizedMessage(), e);
        } catch (ClassNotFoundException e) {
            Log.e(TAG, e.getLocalizedMessage(), e);
        } finally {
            try {
                if (ois != null)
                    ois.close();
            } catch (IOException e) {
            }
        }
    }

    /**
     * 解析域名
     *
     * @param request
     * @return
     */
    private String parseDomain(byte[] request) {

        String result = "";
        int length = request.length;
        int partLength = request[0];
        if (partLength == 0)
            return result;
        try {
            byte[] left = new byte[length - partLength - 1];
            System.arraycopy(request, partLength + 1, left, 0, length
                    - partLength - 1);
            result = new String(request, 1, partLength) + ".";
            result += parseDomain(left);
        } catch (Exception e) {
            Log.e(TAG, e.getLocalizedMessage());
        }
        return result;
    }

    /*
     * Parse IP string into byte, do validation.
     *
     * @param ip IP string
     *
     * @return IP in byte array
     */
    protected byte[] parseIPString(String ip) {
        byte[] result = null;
        int value;
        int i = 0;
        String[] ips = null;

        ips = ip.split("\\.");

        Log.d(TAG, "Start parse ip string: " + ip + ", Sectons: " + ips.length);

        if (ips.length != IP_SECTION_LEN) {
            Log.e(TAG, "Malformed IP string number of sections is: "
                    + ips.length);
            return null;
        }

        result = new byte[IP_SECTION_LEN];

        for (String section : ips) {
            try {
                value = Integer.parseInt(section);

				/* 0.*.*.* and *.*.*.0 is invalid */
                if ((i == 0 || i == 3) && value == 0) {
                    return null;
                }

                result[i] = (byte) value;
                i++;
            } catch (NumberFormatException e) {
                Log.e(TAG, "Malformed IP string section: " + section);
                return null;
            }
        }

        return result;
    }

    /*
     * Resolve host name by dotnul.com:
     *
     */
    private String resolveDomainName(String domain, int type) {
        String ip = null;

        InputStream is;

        String url = "http://80.92.90.248/api/dns/8.8.8.8/IN/"
                + domain;
	if (type == TYPE_A) url += "/A";
	else if (type == TYPE_AAAA) url += "/AAAA";

        try {
            URL aURL = new URL(url);
            HttpURLConnection conn = (HttpURLConnection) aURL.openConnection();
            conn.setConnectTimeout(2000);
            conn.connect();
            is = conn.getInputStream();
            BufferedReader br = new BufferedReader(new InputStreamReader(is));
            String tmp = br.readLine();
	    Log.d(TAG, "Get response: " + tmp);
	    String ps = "\"type\":\"";
	    if (type == TYPE_A) ps += "A";
	    else if (type == TYPE_AAAA) ps += "AAAA";
	    Pattern p = Pattern.compile(ps + "\",\"class\":\"IN\",\"ttl\":([0-9]*?),\"rdata\":\"(.*?)\"");
	    Matcher m = p.matcher(tmp);
	    if (m.find()){
		    Log.d(TAG, "Regex matches");
		    ip = m.group(2);
	    }
	    else{
		    p = Pattern.compile("\"rcode\":\"NXDOMAIN\"");
		    m = p.matcher(tmp);
		    if (m.find()){
			    Log.d(TAG, domain + ": NXDOMAIN");
			    ip = CANT_RESOLVE;
		    }
	    }
        } catch (SocketException e) {
            Log.e(TAG, "Failed to request URI: " + url, e);
        } catch (IOException e) {
            Log.e(TAG, "Failed to request URI: " + url, e);
        } catch (NullPointerException e) {
            Log.e(TAG, "Failed to request URI: " + url, e);
        }

        return ip;
    }

	/*
     * Implement with http based DNS.
	 */

    @Override
    public void run() {

        loadCache();

        byte[] qbuffer = new byte[576];

        SharedPreferences settings = PreferenceManager
                .getDefaultSharedPreferences(context);

        threadNum = 0;
        while (true) {
            try {
                final DatagramPacket dnsq = new DatagramPacket(qbuffer,
                        qbuffer.length);

                if (!settings.getBoolean("isRunning", false))
                    break;

                srvSocket.receive(dnsq);
                // 连接外部DNS进行解析。

                byte[] data = dnsq.getData();
                //int dnsqLength = dnsq.getLength();

		// find the end of question section, ignore others below
		int idx = 12;
		while (data[idx] != 0x00) idx++; // end of QNAME
		final int dnsqLength = idx + 4 + 1;
		
		if (dnsqLength != dnsq.getLength()) Log.d(TAG, "Extra sections ignored");

                final byte[] udpreq = new byte[dnsqLength];
                System.arraycopy(data, 0, udpreq, 0, dnsqLength);
                // 尝试从缓存读取域名解析
                final String questDomain = getRequestDomain(data);

                Log.d(TAG, "Resolve: " + questDomain + " QTYPE: " + udpreq[dnsqLength-4] + udpreq[dnsqLength-3]);

                if (dnsCache.containsKey(questDomain + udpreq[dnsqLength-3])) {

                    sendDns(dnsCache.get(questDomain + udpreq[dnsqLength-3]).getDnsResponse(), dnsq,
                            srvSocket);

                } else {
                    synchronized (this) {
                        if (domains.contains(questDomain))
                            continue;
                        else
                            domains.add(questDomain);
                    }

                    while (threadNum >= MAX_THREAD_NUM) {
                        Thread.sleep(2000);
                    }

                    threadNum++;
                    new Thread() {
                        @Override
                        public void run() {
                            long startTime = System.currentTimeMillis();
                            try {
                                byte[] answer;
                                answer = fetchAnswerHTTP(udpreq, udpreq[dnsqLength-3]);
                                if (answer != null && answer.length != 0) {
                                    addToCache(questDomain + udpreq[dnsqLength-3], answer);
                                    sendDns(answer, dnsq, srvSocket);
                                    Log.d(TAG, "DNS response, length: "
                                            + answer.length
                                            + "  cost: "
                                            + (System.currentTimeMillis() - startTime)
                                            / 1000 + "s");
                                } else {
                                    Log.e(TAG, "DNS Packet size is zero");
                                }
                            } catch (Exception e) {
                                // Nothing
                            }
                            synchronized (DNSServer.this) {
                                domains.remove(questDomain);
                            }
                            threadNum--;
                        }
                    }.start();

                }

            } catch (IOException e) {
                Log.e(TAG, "IO Exception", e);
            } catch (NullPointerException e) {
                Log.e(TAG, "Srvsocket wrong", e);
                break;
            } catch (InterruptedException e) {
                Log.e(TAG, "Interuppted");
                break;
            }
        }

        if (srvSocket != null) {
            srvSocket.close();
            srvSocket = null;
        }

        if (Utils.isWorked()) {
            Log.d(TAG, "DNS try to stop service");
            context.stopService(new Intent(context, SSHTunnelService.class));
        }

    }

    /**
     * 保存域名解析内容缓存
     */
    private void saveCache() {
        ObjectOutputStream oos = null;
        File cache = new File(homePath + CACHE_PATH + CACHE_FILE);
        try {
            if (!cache.exists()) {
                File cacheDir = new File(homePath + CACHE_PATH);
                if (!cacheDir.exists()) { // android的createNewFile这个方法真够恶心的啊
                    cacheDir.mkdir();
                }
                cache.createNewFile();
            }
            oos = new ObjectOutputStream(new FileOutputStream(cache));
            oos.writeObject(dnsCache);
            oos.flush();
            oos.close();
            oos = null;
        } catch (FileNotFoundException e) {
            Log.e(TAG, e.getLocalizedMessage(), e);
        } catch (IOException e) {
            Log.e(TAG, e.getLocalizedMessage(), e);
        } finally {
            try {
                if (oos != null)
                    oos.close();
            } catch (IOException e) {
            }
        }
    }

    /**
     * 向来源发送dns应答
     *
     * @param response  应答包
     * @param dnsq      请求包
     * @param srvSocket 侦听Socket
     */
    private void sendDns(byte[] response, DatagramPacket dnsq,
                         DatagramSocket srvSocket) {

        // 同步identifier
        System.arraycopy(dnsq.getData(), 0, response, 0, 2);

        DatagramPacket resp = new DatagramPacket(response, 0, response.length);
        resp.setPort(dnsq.getPort());
        resp.setAddress(dnsq.getAddress());

        try {
            srvSocket.send(resp);
        } catch (IOException e) {
            Log.e(TAG, "", e);
        }
    }

    public void setBasePath(String path) {
        this.homePath = path;
    }

    public boolean test(String domain, String ip) {
        boolean ret = true;

        // TODO: Implement test case

        return ret;
    }

}
