import java.rmi.*;
import java.util.*;

public class CarnetImpl extends Remote implements Carnet {

    private Hashtable<String,RFiche> fiche ;
    private int nbCarnet;
    private Carnet carnetBis;
    //RFiche fiche

    public CarnetImpl (int n) {
        this.nbCarnet=n;
        this.fiche = new HashMap<String,RFiche>;
    }

	public void Ajouter(SFiche sf) throws RemoteException {
        try {
            RFiche rf = new RFicheImpl(sf.getNom(), sf.getEmail());
            this.fiche.put(sf.getNom(), rf);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
	public RFiche Consulter(String n, boolean forward) throws RemoteException{
        try {
            if(this.fiche.containsKey(n)){
                SFiche sf = fiche.get(n);
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
	

    public static void main(String args[]) {

    }

}
