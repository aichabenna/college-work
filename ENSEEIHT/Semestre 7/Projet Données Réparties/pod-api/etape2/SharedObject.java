import java.io.*;

public class SharedObject implements Serializable, SharedObject_itf {
	private enum states {NL,RLC,RLT,WLC,WLT,WLC_RLT};
	private int id;
	public Object obj;
	private states state;
	
	public SharedObject (int initId, Object initObj) {
		this.id = initId;
		this.obj = initObj;
		this.state = states.NL;
	}
	
	// invoked by the user program on the client node
	public void lock_read() {
		if (state == states.RLC) {
			state = states.RLT;
		}
		else if (state == states.WLC) {
			state = states.WLC_RLT;
		} 
		else {
			this.obj = Client.lock_read(id);
			state =states.RLT;
		}
	}

	// invoked by the user program on the client node
	public void lock_write() {
		if (state == states.WLC) {
			state = states.WLT;
		}
		else {
			this.obj = Client.lock_write(id);
			state = states.WLT;
		}
	}

	// invoked by the user program on the client node
	public synchronized void unlock() {
		if (state == states.RLT) {
			state = states.RLC;
		}
		else if(state == states.WLT) {
			state = states.WLC;
		}
		else if (state == states.WLC_RLT) {
			state = states.WLC;
		}
		notify();
	}

	// callback invoked remotely by the server
	public synchronized Object reduce_lock() {
		if (state == states.WLC ) {
			state = states.RLC;
		} else if(state == states.WLC_RLT){
			state = states.RLT;
		} else if (state == states.WLT){
			try {
				wait();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			state = states.RLC;
		} else {
			System.exit(1);
		}
		return this.obj;
	}

	// callback invoked remotely by the server
	public synchronized void invalidate_reader() {
		if (state == states.RLC){
			state = states.NL;
		}
		else if (state == states.RLT) {
			try {
				wait();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			state = states.NL;
		}
	}

	public synchronized Object invalidate_writer() {
		if (state == states.WLC ) {
			state = states.NL;
		} else if (state == states.WLT || state == states.WLC_RLT){
			try {
				wait();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			state = states.NL;
		}
		return this.obj;
	}
}
