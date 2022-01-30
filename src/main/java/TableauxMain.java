import org.semanticweb.owlapi.apibinding.*;
import org.semanticweb.owlapi.model.*;

import java.io.File;

public class TableauxMain {
    public static void main(String[] args) throws OWLOntologyCreationException {
        final OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        final OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new File("/home/galigator/myLocalDir/aura.owl"));
    }
}
