import org.semanticweb.owlapi.model.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class TableauxMain {
    public static final String terminologyPath="ontology/T.owl";
    public static final String conceptPath="ontology/C.owl";

    public static void main(String[] args) throws OWLException {
        MyOWLParser parser=new MyOWLParser();
        OWLOntology conceptOntology= null;
        try {
            conceptOntology = parser.loadOntologyFromFile(conceptPath);
        } catch (OWLOntologyCreationException e) {
            e.printStackTrace();
        }
        List<OWLEquivalentClassesAxiom> axioms=parser.getEquivalentClassesAxioms(conceptOntology);
        if(axioms.isEmpty())
            return;
        OWLClassExpression C=null;
        try {
            if(axioms.size()==1) {
                C=parser.unpackEquilvalentClassesAxiom(axioms.get(0)).get(1);
            }
        } catch (OWLException e){
        }
        //TABLEAUX TEST
        List<OWLClassExpression> L=new ArrayList<>();
        Set<OWLClassExpression> temp_set=new HashSet<>();
        L.add(C);
        System.out.println(L);
        if(parser.isIntersection(C)) {//AND
            try {
                L.addAll(parser.unpackIntersection(C));
                System.out.println(L);
            } catch (OWLException e) {
            }
        }
        for(OWLClassExpression ce:L){
            if(parser.isUnion(ce)){ //OR
                temp_set.addAll(parser.unpackUnion(ce));
            }
        }
        L.addAll(temp_set);
        temp_set.clear();
        System.out.println(L);
        for(OWLClassExpression ce:L){
            if(parser.isExists(ce)){ //ESISTE
                temp_set.add(parser.getExistClassExpression(ce));
                System.out.println(parser.getExistRole(ce));
            }
        }
        L.addAll(temp_set);
        temp_set.clear();
        System.out.println(L);
        for(OWLClassExpression ce:L){
            if(parser.isForeach(ce)){ //PEROGNI
                temp_set.add(parser.getForeachClassExpression(ce));
                System.out.println(parser.getForeachRole(ce));
            }
        }
        L.addAll(temp_set);
        temp_set.clear();
        System.out.println(L);
    }
}
