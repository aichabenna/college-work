import java.net.*;
import java.io.*;
import java.util.Random;


public class LoadBalancer {
	static String hosts[] = {"localhost", "localhost"};
    static int ports[] = {8081,8082};
    static int nbHosts = 2;
    static Random rand = new Random();
    static Socket s;

	public static void main (String[] args) throws IOException{
        ServerSocket ss = new ServerSocket(8080);
        while(true) {
            Slave sl = new Slave(ss.accept());
            sl.start();
        }	
    }
}