import java.rmi.*;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.rmi.server.UnicastRemoteObject;
import java.util.HashMap;
import java.util.Map;

public class Server extends UnicastRemoteObject implements Server_itf {
	// name of the object + id
	private Map<String, Integer> annuaire;
	// object + id
	private Map<Integer, ServerObject> annuaire_serverobj_id;
	private int ident;
	
	protected Server () throws RemoteException {
		super();
		annuaire = new HashMap<String, Integer>();
		annuaire_serverobj_id = new HashMap<Integer, ServerObject>();
		ident = 0;
	}

	@Override
	public int lookup(String name) throws RemoteException {
		Integer id =  annuaire.get(name);
		if (id == null){
			return -1;
		}
		return id;
	}

	@Override
	public void register(String name, int id) throws RemoteException {
		annuaire.put(name, id);
	}

	@Override
	public int create(Object o) throws RemoteException {
		ServerObject so = new ServerObject(ident, o);
		annuaire_serverobj_id.put(ident, so);
		ident++;
		return ident-1;
	}

	@Override
	public Object lock_read(int id, Client_itf client) throws RemoteException {
		// TODO Auto-generated method stub
		ServerObject s =annuaire_serverobj_id.get(id);
		return s.lock_read(client);
	}

	@Override
	public Object lock_write(int id, Client_itf client) throws RemoteException {
		// TODO Auto-generated method stub
		ServerObject s = annuaire_serverobj_id.get(id);
		return s.lock_write(client);
	}

	public static void main(String args[]) {
		try {
			Registry registry = LocateRegistry.createRegistry(1099);
			// Create an instance of the server object
			Server sv = new Server();
			// Register the object with the naming service
			//Naming.rebind("//localhost:1099/Serveur", sv);
			registry.bind("Serveur", sv);
			Role.setRole("Server");
		}catch(Exception exc) {
			
		}
	}

}
