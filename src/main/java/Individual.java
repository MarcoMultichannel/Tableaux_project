import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import org.jetbrains.annotations.NotNull;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;

public class Individual {
    public int id;
    public Queue<OWLClassExpression> ands, ors, exists, foreaches;
    public ArrayList<OWLClassExpression> label;
    public OWLClassExpression lastOR;
    public HashMap<OWLObjectPropertyExpression, HashSet<Individual>> arches;
    public HashSet<Individual> individualsConnected;
    public HashMap<OWLClassExpression, HashSet<ArrayList<OWLClassExpression>>> previousLabelsMap;
    public static int numIndividuals = 0;
    public boolean blocked;
    private final MyOWLParser parser;

    public Individual() {
        this.id = numIndividuals;
        numIndividuals++;
        parser = new MyOWLParser();
        ands = new LinkedList<>();
        ors = new LinkedList<>();
        exists = new LinkedList<>();
        foreaches = new LinkedList<>();
        arches = new HashMap<>();
        individualsConnected = new HashSet<>();
        previousLabelsMap = new HashMap<>();
        label = new ArrayList<>();
    }

    public Individual(@NotNull Individual individual) {
        this.id = individual.id;
        this.arches = new HashMap<>(individual.arches);
        this.parser = new MyOWLParser();
        this.label = new ArrayList<>(individual.label);
        this.ands = new LinkedList<>(individual.ands);
        this.ors = new LinkedList<>(individual.ors);
        this.exists = new LinkedList<>(individual.exists);
        this.foreaches = new LinkedList<>(individual.foreaches);
        this.individualsConnected = new HashSet<>(individual.individualsConnected);
        this.previousLabelsMap = new HashMap<>(individual.previousLabelsMap);
        this.blocked = individual.blocked;
    }

    @Override
    public boolean equals(Object obj) {
        if(obj instanceof Individual) {
            return ((Individual) obj).id == this.id;
        } else return false;
    }

    public static void setNextID(int id) {
        Individual.numIndividuals = id;
    }

    public void addConcept(OWLClassExpression ce) {
        if(ce == null) return;
        if(!label.contains(ce)) {
            if(parser.isIntersection(ce))
                ands.add(ce);
            else if(parser.isUnion(ce))
                ors.add(ce);
            else if(parser.isExists(ce))
                exists.add(ce);
            else if(parser.isForeach(ce))
                foreaches.add(ce);
            label.add(ce);
        }
    }

    public void addConcepts(@NotNull Collection<OWLClassExpression> ce_list) {
        for(OWLClassExpression ce: ce_list)
            addConcept(ce);
    }

    public void addClashLabel(OWLClassExpression or , ArrayList<OWLClassExpression> label) {
        if(previousLabelsMap.containsKey( or)) {
            HashSet<ArrayList<OWLClassExpression>> labelsSet = previousLabelsMap.get( or);
            labelsSet.add(label);
        } else {
            HashSet<ArrayList<OWLClassExpression>> labelsSet = new HashSet<>();
            labelsSet.add(label);
            previousLabelsMap.put( or , labelsSet);
        }
        lastOR = or;
    }

    public void newArchTo(OWLObjectPropertyExpression role, Individual individual) {
        this.individualsConnected.add(individual);
        if(this.arches.containsKey(role)) {
            HashSet<Individual> individuals = this.arches.get(role);
            individuals.add(individual);
        } else {
            HashSet<Individual> individuals = new HashSet<>();
            individuals.add(individual);
            this.arches.put(role, individuals);
        }
    }



    public boolean isBlocked(@NotNull HashSet<Individual> individuals) {
        boolean isBlocked = false;
        ArrayList<OWLClassExpression> labelNoANDs = removeANDs(this.label);
        for(Individual individual: individuals) {
            if(this.id > individual.id && individual.label.containsAll(labelNoANDs)) {
                isBlocked = true;
                break;
            }
        }
        return isBlocked;
    }

    private ArrayList<OWLClassExpression> removeANDs(ArrayList<OWLClassExpression> label) {
        ArrayList<OWLClassExpression> newLabel = new ArrayList<>();
        for(OWLClassExpression ce: label) {
            if(!parser.isIntersection(ce))
                newLabel.add(ce);
        }
        return newLabel;
    }

    public void markAsBlocked() {
        blocked = true;
    }

}

