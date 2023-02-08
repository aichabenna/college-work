import java.net.*;
import java.io.*;
import java.util.Random;

public class Slave extends Thread {
    Socket s;

    public Slave(Socket s){
        this.s = s;
    }

    public void run(){
        try{
            int i = LoadBalancer.rand.nextInt(LoadBalancer.nbHosts);
            Socket server = new Socket(LoadBalancer.hosts[i], LoadBalancer.ports[i]);

            InputStream s_in = s.getInputStream();
            OutputStream s_out = s.getOutputStream();

            InputStream server_in = server.getInputStream();
            OutputStream server_out = server.getOutputStream();

            byte[] buffer = new byte[1024];
            int bytesRead = s_in.read(buffer);
            if (bytesRead > 0){
                server_out.write(buffer,0,bytesRead);
            }
            //System.out.println(bytesRead);
            bytesRead = server_in.read(buffer);
            if (bytesRead > 0){
                s_out.write(buffer,0,bytesRead);
            }

            server.close();
            s.close();
        }catch(IOException e){
            System.out.println("An error has occurred ... ");
        }
    }
}