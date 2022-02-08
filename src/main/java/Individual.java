import org.jetbrains.annotations.NotNull;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;

import java.util.*;

public class Individual {
    public int id;
    public Queue<OWLClassExpression> ands, ors, exists, foreaches;
    public ArrayList<OWLClassExpression> label;
    public HashMap<OWLObjectPropertyExpression, HashSet<Individual>> arches;
    public HashSet<Individual> individualsConnected;
    public ArrayList<ArrayList<OWLClassExpression>> previousLabels;
    public static int numIndividuals=0;
    public boolean blocked;
    private final MyOWLParser parser;
    public Individual(){
        this.id=numIndividuals;
        numIndividuals++;
        parser=new MyOWLParser();

        ands = new LinkedList<>();
        ors = new LinkedList<>();
        exists = new LinkedList<>();
        foreaches = new LinkedList<>();

        arches=new HashMap<>();
        individualsConnected=new HashSet<>();

        previousLabels=new ArrayList<>();
        label=new ArrayList<>();
    }
    public Individual(@NotNull Individual x){
        this.id=x.id;
        this.arches=new HashMap<>(x.arches);
        this.parser=new MyOWLParser();
        this.label=new ArrayList<>(x.label);
        this.ands=new LinkedList<>(x.ands);
        this.ors=new LinkedList<>(x.ors);
        this.exists=new LinkedList<>(x.exists);
        this.foreaches=new LinkedList<>(x.foreaches);
        this.individualsConnected=new HashSet<>(x.individualsConnected);
        this.previousLabels=new ArrayList<>(x.previousLabels);
        this.blocked=x.blocked;
    }
    public boolean equals(Object ogg) {
        if(ogg instanceof Individual){
            return ((Individual) ogg).id==this.id;
        }else return false;
    }
    public static void setNextID(int id){
        Individual.numIndividuals=id;
    }
    public void addConcept(OWLClassExpression ce){
        if(ce==null) return;
        if(!label.contains(ce)){
            if (parser.isIntersection(ce))
                ands.add(ce);
            else if (parser.isUnion(ce))
                ors.add(ce);
            else if (parser.isExists(ce))
                exists.add(ce);
            else if (parser.isForeach(ce))
                foreaches.add(ce);
            label.add(ce);
        }
    }
    public void addConcepts(@NotNull Collection<OWLClassExpression> ce_list){
        for(OWLClassExpression ce:ce_list)
            addConcept(ce);
    }
    public void addClashLabel(ArrayList<OWLClassExpression> label){
        previousLabels.add(new ArrayList<>(label));
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

    public boolean isBlocked(@NotNull HashSet<Individual> individuals) {
        //TODO trova un modo più furbo per il blocking
        boolean result=false;
        for(Individual x:individuals){
            if(this.id>x.id && x.label.containsAll(this.label)) {
                result = true;
                break;
            }
        }
        return result;
    }
    public void markAsBlocked(){
        blocked=true;
    }
}
