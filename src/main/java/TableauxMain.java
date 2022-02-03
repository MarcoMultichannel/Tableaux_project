import org.semanticweb.owlapi.model.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class TableauxMain {
    public static final String terminologyPath="ontology/T.owl";
    public static final String conceptPath="ontology/C.owl";

    public static void main(String[] args) {
        MyOWLParser parser=new MyOWLParser();
        try {
            OWLOntology concept = parser.loadOntologyFromFile(conceptPath);
            Tableaux tab=new Tableaux(concept);
            tab.execute();
            tab.print();
        } catch (OWLException e) {
            System.out.println("Errore.");
            e.printStackTrace();
        }
    }
}
