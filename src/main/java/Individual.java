import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;

import java.util.*;

public class Individual {
    public int id;
    public HashSet<OWLClassExpression> ors, exists, foreachs;
    public ArrayList<OWLClassExpression> label;
    public HashMap<OWLObjectPropertyExpression, Individual> arches;

    private final MyOWLParser parser;
    public Individual(int id){
        this.id=id;
        arches=new HashMap<>();
        parser=new MyOWLParser();

        label=new ArrayList<>();
        ors=new HashSet<>();
        exists=new HashSet<>();
        foreachs=new HashSet<>();
    }
    public void addConcept(OWLClassExpression ce){
        if(!label.contains(ce)){
            if (parser.isUnion(ce))
                ors.add(ce);
            else if (parser.isExists(ce))
                exists.add(ce);
            else if (parser.isForeach(ce))
                foreachs.add(ce);
            label.add(ce);
        }
    }
    public void addConcepts(Collection<OWLClassExpression> ce_list){
        for(OWLClassExpression ce:ce_list)
            addConcept(ce);
    }
    public void removeConcept(OWLClassExpression ce){
        label.remove(ce);
    }
    public void markAsVisited(OWLClassExpression ce){
        ors.remove(ce);
        exists.remove(ce);
        foreachs.remove(ce);
    }
}
