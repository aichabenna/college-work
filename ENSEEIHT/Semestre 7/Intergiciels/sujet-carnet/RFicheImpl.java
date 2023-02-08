import java.rmi.*;

public class RFicheImpl implements RFiche extends Remote {
    private String nom;
    private String email;

    public RFicheImpl(String nom, String email) {
        this.nom = nom;
        this.email = email;
    }

	public String getNom () throws RemoteException{
        return this.nom;
    }

	public String getEmail () throws RemoteException{
        return this.email;
    }
}



