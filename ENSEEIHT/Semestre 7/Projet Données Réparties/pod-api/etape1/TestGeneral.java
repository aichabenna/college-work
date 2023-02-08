import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
public class TestGeneral{
	@SuppressWarnings("deprecation")
	public static void main(String[] args) {
		List<Thread> ths = new ArrayList<>(); //liste des threads des clients à lancer
		List<String> objs = new ArrayList<>(); // liste des objets
		int nbClient = Integer.parseInt(args[0]);
		int nbObject = Integer.parseInt(args[1]);
		
        Thread server = new Thread(new Runnable() {
            public void run() {
            	try {
            	    Class<?> clazz = Class.forName("Server");
            	    Method mainMethod = clazz.getMethod("main", String[].class);
            	    mainMethod.invoke(null, (Object) new String[] {});
            	} catch (ClassNotFoundException | NoSuchMethodException | 
            	        IllegalAccessException | InvocationTargetException e) {
            	    e.printStackTrace();
            	}
            }
        });
        
        for(int i = 0;i < nbObject;i++) {
        	objs.add("Obj"+i);
        }
        
        for(int i = 0;i < nbClient;i++) {
        	int j = new Random().nextInt(1, 3); //choose if the client is a writer or a reader  
        	int o = new Random().nextInt(0, nbObject); //choose an object
        	ths.add(new Thread(new ClientTest(i,j,objs.get(o))));
        }
        server.start();
        
        /////////////////////////////////////////////////////////
        Client.init(); //add every object on the server
        for(String obj : objs) {
        	Sentence sn = new Sentence();
    		sn.write("Etat initial "+obj);
    		Client.register(obj, Client.create(sn));
        }
		
        /////////////////////////////////////////////////////////

        
        for(Thread t : ths) {
        	t.start();
        }
        for(Thread t : ths) {
        	try {
				t.join();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
        }
        server.stop();
        System.out.println("TEST TERMINE");
    }
}
