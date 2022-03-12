import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLOntology;

import javax.swing.*;
import java.awt.image.BufferedImage;
import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

public class TableauxMain {
    static {
        System.setProperty("java.awt.headless", "false");
    }
    public static final String terminologyPath="ontology/T.owl";

    public static void showImage(BufferedImage img){
        JFrame frame = new JFrame("Tableaux");
        frame.setSize(1700,600);
        frame.setLocation(100,100);
        frame.add(new JLabel(new ImageIcon(img)));
        frame.setVisible(true);
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    }
    public static void main(String[] args) {
        String conceptString="ALC:A and (ALC:R some (not(ALC:A)))";
        MyOWLParser parser=new MyOWLParser();
        try {
            OWLOntology terminology = parser.loadOntologyFromFile(terminologyPath);
            OWLClassExpression concept = parser.parseConcept(terminology, conceptString);
            Tableaux tab=new Tableaux(parser, terminology);
            boolean sat=tab.isSatisfiable(concept);
            float timeElapsed=tab.getTimeElapsed();
            System.out.println("Concetto in input: "+tab.getConcept());
            System.out.println("Tempo impiegato: "+timeElapsed+"ms");

            if(sat)
                System.out.println("Il concetto C è soddisfacibile");
            else {
                System.out.println("Il concetto C è insoddisfacibile");

                System.out.println("Clash: "+tab.getClashes());
            }

            tab.save("result.rdf");
            BufferedImage img=tab.toImage(false);
            showImage(img);
        } catch (OWLException e) {
            System.out.println("Errore.");
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
