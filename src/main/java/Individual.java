import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;

import java.util.*;

public class Individual {
    public int id;
    public HashSet<OWLClassExpression> ands, ors, exists, foreachs, visited;
    public ArrayList<OWLClassExpression> label;
    public HashMap<OWLObjectPropertyExpression, HashSet<Individual>> arches;
    public HashSet<Individual> individualsConnected;
    public static int numIndividuals=0;

    private final MyOWLParser parser;
    public Individual(){
        this.id=numIndividuals;
        numIndividuals++;
        arches=new HashMap<>();
        parser=new MyOWLParser();

        label=new ArrayList<>();
        ands=new HashSet<>();
        ors=new HashSet<>();
        exists=new HashSet<>();
        foreachs=new HashSet<>();
        visited=new HashSet<>();
        individualsConnected=new HashSet<>();
    }
    public void addConcept(OWLClassExpression ce){
        if(!label.contains(ce)){
            if (parser.isIntersection(ce))
                ands.add(ce);
            else if (parser.isUnion(ce))
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
        visited.add(ce);
    }
    public boolean isVisited(OWLClassExpression ce){
        return visited.contains(ce);
    }
    public void newArchTo(OWLObjectPropertyExpression role, Individual y){
        this.individualsConnected.add(y);
        if(this.arches.containsKey(role)){
            HashSet<Individual> individuals=this.arches.get(role);
            individuals.add(y);
        }
        else{
            HashSet<Individual> individuals=new HashSet<>();
            individuals.add(y);
            this.arches.put(role,individuals);
        }
    }
}
