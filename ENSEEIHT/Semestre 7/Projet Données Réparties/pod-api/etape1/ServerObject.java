import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.List;

public class ServerObject{
	enum states {NL,RL,WL};
	private int id;
	private states lockType;
	private Client_itf writer; 
	private List<Client_itf> readers;
	private Object obj;
	
	public ServerObject (int id, Object initObj) {
		this.id = id;
		this.obj =initObj;
		this.lockType = states.NL;
		this.readers = new ArrayList<Client_itf>();
	}

	public Object lock_read(Client_itf c) throws RemoteException{
		if (this.lockType == states.NL ){
			lockType = states.RL;
		} 
		else if(this.lockType == states.WL){
			this.obj = writer.reduce_lock(id);
			readers.add(writer);
			lockType =states.RL;
		}
		readers.add(c);
		return this.obj;
	}

	public Object lock_write(Client_itf c) throws RemoteException{
		if (this.lockType == states.NL){
			lockType = states.WL;
		}else if(this.lockType == states.WL){
			this.obj = writer.invalidate_writer(this.id);
		}else if(this.lockType == states.RL) {
			for(Client_itf r : readers){
				r.invalidate_reader(id);
			}
			lockType = states.WL;
		}
		writer = c;
		return this.obj;
	}
}
