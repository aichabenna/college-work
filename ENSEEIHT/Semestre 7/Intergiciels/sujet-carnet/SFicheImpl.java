import java.io.*;

public class SFicheImpl implements SFiche extends Serializable {

    private String nom;
    private String email;

    public SFicheImpl(String nom, String email) {
        this.nom = nom;
        this.email = email;
    }


	public String getNom (){
        return this.nom;
    }
	public String getEmail (){
        return this.email;
    }
}



