import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLOntology;

import javax.swing.*;
import java.awt.image.BufferedImage;
import java.io.IOException;

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
        String conceptOntology= """
                Prefix: ALC: <urn://alc/>
                Class: ALC:A
                Class: ALC:B
                Class: ALC:C
                Class: ALC:D
                ObjectProperty: ALC:R
                Class: ALC:Concept
                   EquivalentTo: ALC:A and ((not(ALC:A) and ALC:R some ALC:B) or (ALC:R some ALC:C)) and ((ALC:R only ALC:B) or (ALC:R only (not(ALC:A))))""";
        MyOWLParser parser=new MyOWLParser();
        try {
            OWLOntology concept = parser.loadOntologyFromString(conceptOntology);
            OWLOntology terminology = parser.loadOntologyFromFile(terminologyPath);
            Tableaux tab=new Tableaux(parser, concept, terminology);
            System.out.println("Concetto in input: "+tab.getConcept());
            float timeElapsed=tab.execute();
            System.out.println("Tempo impiegato: "+timeElapsed+"ms");

            if(tab.isClashFree())
                System.out.println("Il concetto C è soddisfacibile");
            else
                System.out.println("Il concetto C è insoddisfacibile");

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
