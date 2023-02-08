import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Random;
public class TestSpecific {
	public static void main(String[] args) {
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
		
		
        Thread t1 = new Thread(new Runnable() {
            public void run() {
            	Client.init();
            	SharedObject s = Client.lookup("Obj");;
            	while(s == null){
	        		s = Client.lookup("Obj");
	        		if (s == null) {
	        			Sentence sn = new Sentence();
	        			sn.write("Etat initial");
	        			s = Client.create(sn);
	        			Client.register("Obj", s);
	        		}
        		}
        		s.lock_read();
        		String s_m = ((Sentence)(s.obj)).read();
        		s.unlock();
        		System.out.println(s_m);
            }
        });
        
        Thread t2 = new Thread(new Runnable() {
            public void run() {
            	Client.init();
        		SharedObject s = Client.lookup("Obj");
        		while(s == null){
        			s = Client.lookup("Obj");
        			if (s == null) {
            			Sentence sn = new Sentence();
            			sn.write("Etat initial");
            			s = Client.create(sn);
            			Client.register("Obj", s);
            		}
        		}
        		s.lock_write();
        		((Sentence)(s.obj)).write("Etat modifié");
        		s.unlock();
            }
        });
        
        server.start();
        t1.start();
        t2.start();
        try {
			t1.join();
			t2.join();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
        server.stop();
        
        System.out.println("TEST TERMINE");
    }
}
