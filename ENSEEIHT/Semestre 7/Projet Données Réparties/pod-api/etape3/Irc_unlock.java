import java.awt.*;
import java.awt.event.*;
import java.rmi.*;
import java.io.*;
import java.net.*;
import java.util.*;
import java.lang.*;
import java.rmi.registry.*;


public class Irc_unlock extends Frame {
	public TextArea		text;
	public TextField	data;
	Sentence_itf		sentence;
	static String		myName;

	public static void main(String argv[]) {
		
		if (argv.length != 1) {
			System.out.println("java Irc <name>");
			return;
		}
		myName = argv[0];
	
		// initialize the system
		Client.init();
		
		// look up the IRC object in the name server
		// if not found, create it, and register it in the name server
		Sentence_itf s = (Sentence_itf)Client.lookup("IRC");
		if (s == null) {
			s = (Sentence_itf)Client.create(new Sentence());
			Client.register("IRC", s);
		}
		// create the graphical part
		new Irc_unlock(s);
	}

	public Irc_unlock(Sentence_itf s) {
	
		setLayout(new FlowLayout());
	
		text=new TextArea(10,60);
		text.setEditable(false);
		text.setForeground(Color.red);
		add(text);
	
		data=new TextField(60);
		add(data);
	
		Button write_button = new Button("write");
		write_button.addActionListener(new writeListenerv2(this));
		add(write_button);
		Button read_button = new Button("read");
		read_button.addActionListener(new readListenerv2(this));
		add(read_button);
		Button unlock_button = new Button("unlock");
        unlock_button.addActionListener(new unlockListener(this));
        add(unlock_button);

		setSize(650,300);
		text.setBackground(Color.black); 
		show();		
		
		sentence = s;
	}
}



class readListenerv2 implements ActionListener {
	Irc_unlock irc;
	public readListenerv2 (Irc_unlock i) {
		irc = i;
	}
	public void actionPerformed (ActionEvent e) {
		
		// lock the object in read mode
		irc.sentence.lock_read();
		
		// invoke the method
		String s = irc.sentence.read();
		
		// unlock the object
		//irc.sentence.unlock();
		
		// display the read value
		irc.text.append(s+"\n");
	}
}

class writeListenerv2 implements ActionListener {
	Irc_unlock irc;
	public writeListenerv2 (Irc_unlock i) {
        	irc = i;
	}
	public void actionPerformed (ActionEvent e) {
		
		// get the value to be written from the buffer
        	String s = irc.data.getText();
        	
        	// lock the object in write mode
		irc.sentence.lock_write();
		
		// invoke the method
		irc.sentence.write(Irc_unlock.myName+" wrote "+s);
		irc.data.setText("");
		
		// unlock the object
		//irc.sentence.unlock();
	}
}

class unlockListener implements ActionListener {
	Irc_unlock irc;
	public unlockListener (Irc_unlock i) {
        	irc = i;
	}
	public void actionPerformed (ActionEvent e) {
		
		// unlock the object
		irc.sentence.unlock();
	}
}



