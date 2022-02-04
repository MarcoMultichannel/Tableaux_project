import org.semanticweb.owlapi.model.*;

import javax.swing.*;
import java.awt.image.BufferedImage;
import java.io.IOException;

public class TableauxMain {
    static {
        System.setProperty("java.awt.headless", "false");
    }

    public static final String terminologyPath="ontology/T.owl";
    public static final String conceptPath="ontology/C.owl";

    public static void showImage(BufferedImage img){
        JFrame frame = new JFrame("Tableaux");
        frame.setSize(1500,600);
        frame.setLocation(200,100);
        frame.add(new JLabel(new ImageIcon(img)));
        frame.setVisible(true);
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    }
    public static void main(String[] args) {
        MyOWLParser parser=new MyOWLParser();
        try {
            OWLOntology concept = parser.loadOntologyFromFile(conceptPath);
            Tableaux tab=new Tableaux(concept);
            tab.execute();
            tab.save("result.rdf");
            BufferedImage img=tab.toImage();
            showImage(img);
        } catch (OWLException e) {
            System.out.println("Errore.");
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
