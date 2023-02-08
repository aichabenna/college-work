import java.rmi.*;
import java.rmi.server.UnicastRemoteObject;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.rmi.registry.*;
import java.net.*;
import java.lang.reflect.*;

// classe à modifier : 3 méthodes lookup - create
// créer une classe pour générer les stubs

public class Client extends UnicastRemoteObject implements Client_itf {
	//server
	private static Server_itf serveur;
	//client
	private static Client_itf client;
	// objects with an id
	private static Map<Integer, SharedObject> annuaire;

	public Client() throws RemoteException {
		super();
		//self = this;// why?
	}

	public static SharedObject getSharedObject(int obj_id){
		return annuaire.get(obj_id);
	}

///////////////////////////////////////////////////
// Etape 2: Creation d une instance de stub
///////////////////////////////////////////////////
	public static SharedObject stub(Object obj, int obj_id) {
		try{
			String className = obj.getClass().getName();
			Class<?> classe = Class.forName(className + "_stub");
			Constructor<?> classConstructor = classe.getConstructor(new Class[] { int.class, Object.class });
			SharedObject newobj = (SharedObject) classConstructor.newInstance(new Object[] { obj_id, obj });
			annuaire.put(obj_id, newobj);
			return newobj;
		}catch(Exception e){
			e.printStackTrace();
		}
		return null;
	}

///////////////////////////////////////////////////
//         Interface to be used by applications
///////////////////////////////////////////////////

	// initialization of the client layer
	public static void init() {
		annuaire = new HashMap<Integer, SharedObject> ();
		try {
			client = new Client();
		} catch (RemoteException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		try {
			Registry r = LocateRegistry.getRegistry(1099);
			serveur = (Server_itf) r.lookup("Serveur"); // a voir
			Role.setRole("Client");
		} catch ( Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	// lookup in the name server
	// to be changed lock_read -> createstub -> unlock
	public static SharedObject lookup(String name) {
		try {
			int obj_id = serveur.lookup(name);
			if (obj_id >= 0){
				/* Modification étape 2 */				
				// appel à generateStub
				Object obj = lock_read(obj_id);
				SharedObject newobj = stub(obj,obj_id);
				newobj.unlock();
				return newobj;
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}		
	
	// binding in the name server
	public static void register(String name, SharedObject_itf so) {
		try {
			for (Integer i : annuaire.keySet()) {
				if (annuaire.get(i) == so) {
					serveur.register(name, i);
				}
			}
		} catch (RemoteException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	// creation of a shared object
	// to be changed -> createStub no need to use annuaire anymore
	public static SharedObject create(Object o) {
		try{
			int id = serveur.create(o);
			// appel à stub
			SharedObject newobj = stub(o, id);
			return newobj;
		} catch (Exception e){
			e.printStackTrace();
		}
		return null;
	}
	
/////////////////////////////////////////////////////////////
//    Interface to be used by the consistency protocol
////////////////////////////////////////////////////////////

	// request a read lock from the server
	public static Object lock_read(int id) {
		try {
			return serveur.lock_read(id, client);
		} catch (RemoteException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}

	// request a write lock from the server
	public static Object lock_write (int id) {
		try {
			return serveur.lock_write(id, client);
		} catch (RemoteException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}

	// receive a lock reduction request from the server
	public Object reduce_lock(int id) throws java.rmi.RemoteException {
		return annuaire.get(id).reduce_lock();
	}


	// receive a reader invalidation request from the server
	public void invalidate_reader(int id) throws java.rmi.RemoteException {
		annuaire.get(id).invalidate_reader();
	}


	// receive a writer invalidation request from the server
	public Object invalidate_writer(int id) throws java.rmi.RemoteException {
		return annuaire.get(id).invalidate_writer();

	}

}
