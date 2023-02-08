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
		System.out.println("lock read");
		if (state == states.RLC) {
			System.out.println("RLC");
			state = states.RLT;
		}
		else if (state == states.WLC) {
			System.out.println("WLC");
			state = states.WLC_RLT;
		} 
		else {
			System.out.println("AUTRE");
			this.obj = Client.lock_read(id);
			state =states.RLT;
		}
	}

	// invoked by the user program on the client node
	public void lock_write() {
		System.out.println("lock write");
		if (state == states.WLC) {
			System.out.println("WLC");
			state = states.WLT;
		}
		else {
			System.out.println("AUTRE");

			this.obj = Client.lock_write(id);
			state = states.WLT;
		}
	}

	// invoked by the user program on the client node
	public synchronized void unlock() {
		System.out.println("Unlock");

		if (state == states.RLT) {
			System.out.println("RLT");

			state = states.RLC;
		}
		else if(state == states.WLT) {
			System.out.println("WLT");

			state = states.WLC;
		}
		else if (state == states.WLC_RLT) {
			System.out.println("WLC_RLT");

			state = states.WLC;
		}
		notify();
	}

	// callback invoked remotely by the server
	public synchronized Object reduce_lock() {
		System.out.println("reduce lock");

		if (state == states.WLC ) {
			System.out.println("WLC");

			state = states.RLC;
		} else if(state == states.WLC_RLT){
			System.out.println("WLC_RLT");

			state = states.RLT;
		} else if (state == states.WLT){
			System.out.println("WLT");

			try {
				wait();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			state = states.RLC;
		} else {
			System.out.println("AUTRE");

			System.exit(1);
		}
		return this.obj;
	}

	// callback invoked remotely by the server
	public synchronized void invalidate_reader() {
		System.out.println("invalidate reader");

		if (state == states.RLC){
			System.out.println(">RLC");

			state = states.NL;
		}
		else if (state == states.RLT) {
			System.out.println("RLT");

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
		System.out.println("invalidate writer");

		if (state == states.WLC ) {
			System.out.println("WLC");

			state = states.NL;
		} else if (state == states.WLT || state == states.WLC_RLT){
			System.out.println("WLC_RLC WLT");

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
