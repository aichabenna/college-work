
public class ClientTest implements Runnable{
	private int id;
	private int type;
	private String Object;
	public ClientTest (int id, int typ, String Obj) {
		this.id = id;
		this.type = typ; //writer or reader
		this.Object = Obj;
	}
	
	@Override
	public synchronized void run() {
		Client.init();
    	SharedObject s = Client.lookup(Object);
    	if(s == null) {
    		System.out.println(Object+":"+s);
    	}
    	if(type == 1) {
    		s.lock_read();
    		String s_m = ((Sentence)(s.obj)).read();
    		s.unlock();
    		System.out.println(id+" a lu "+s_m);
    	}else if (type == 2) {
    		s.lock_write();
    		((Sentence)(s.obj)).write("Etat modifié " + id);
    		s.unlock();
    		System.out.println(id+" a écris ");
    	}
    }
		
	
}
