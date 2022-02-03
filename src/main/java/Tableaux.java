import org.eclipse.rdf4j.model.vocabulary.OWL;
import org.semanticweb.owlapi.model.*;

import java.util.*;

public class Tableaux {
    private static final String CONCEPT_NAME="<#Concept>";

    private final OWLClassExpression concept;
    private OWLOntology terminology;
    private final MyOWLParser parser;
    private HashSet<Individual> individuals;

    public Tableaux(OWLOntology C) throws OWLException {
        //Carico il concetto C
        this.parser=new MyOWLParser();
        List<OWLEquivalentClassesAxiom> axioms=parser.getEquivalentClassesAxioms(C);
        if(axioms.isEmpty())
            //Se l'ontologia del concetto C non è del tipo C equivalente <concept>
            throw new OWLException("Errore nel concetto C");
        else{
            List<OWLClassExpression> classExpressions=parser.unpackEquilvalentClassesAxiom(axioms.get(0));
            OWLClassExpression left=classExpressions.get(0);
            OWLClassExpression right=classExpressions.get(1);
            if(left.toString().equals(CONCEPT_NAME))
                //Trasformiamo in forma NNF
                concept=right.getNNF();
            else
                throw new OWLException("Errore nel concetto C");
        }
    }
    public Tableaux(OWLOntology C, OWLOntology T) throws OWLException {
        this(C);
        this.terminology=T;
        //TODO parsing della terminologia
    }
    public void execute(){
        individuals=new HashSet<>();
        try {
            Set<OWLClass> result=computeTableaux(new Individual(0),concept);
            if(result!=null && !result.isEmpty())
                System.out.println("Il concetto ha un clash nelle seguenti classi:"+result);
            else
                System.out.println("Il concetto è soddisfacibile");
        } catch (OWLException e) {
            System.out.println("Errore nel tableaux");
            e.printStackTrace();
        }
    }

    private Set<OWLClass> computeTableaux(Individual x, OWLClassExpression concept) throws OWLException {
        individuals.add(x);
        //SCOMPONGO L'AND
        x.addConcept(concept);
        if(parser.isIntersection(concept)) {
            x.addConcepts(parser.unpackIntersection(concept));
        }

        //SCOMPONGO GLI OR
        for(OWLClassExpression ce:x.ors){
            x.markAsVisited(ce);
            List<OWLClassExpression> disjoints = parser.unpackUnion(ce);
            Set<OWLClass> clashes=null;
            for(OWLClassExpression disjoint:disjoints){
                clashes=computeTableaux(x, disjoint);
                if (clashes==null || clashes.isEmpty()) break;
                else x.removeConcept(disjoint);
            }
            if (clashes==null || !clashes.isEmpty()) return clashes;
        }

        //CLASH CHECK
        if(!getClashes(x).isEmpty()) return getClashes(x);

        for(OWLClassExpression ce:x.exists){
            //TODO: Si può ottimizzare l'esiste ed i perogni
            //TODO: mappa tutti gli esiste R.A, R.B, R.C
            x.markAsVisited(ce);
            Individual y=new Individual(x.id+1);
            individuals.add(y);
            OWLObjectPropertyExpression role=parser.getExistRole(ce);
            x.arches.put(role,y);
            OWLClassExpression classExpression=parser.getExistClassExpression(ce);
            y.addConcept(classExpression);

            for(OWLClassExpression ce_for:x.foreachs){
                x.markAsVisited(ce_for);
                OWLObjectPropertyExpression role_for=parser.getForeachRole(ce_for);
                OWLClassExpression classExpression_for=parser.getForeachClassExpression(ce_for);
                if(x.arches.containsKey(role)){
                    Individual z=x.arches.get(role);
                    z.addConcept(classExpression);
                    //TODO: bisogna fare la chiamata ricorsiva al punto giusto
                    //CLASH CHECK
                    if(!getClashes(x).isEmpty()) return getClashes(x);
                }
            }
        }
        return null;
    }
    public void print(){
        for(Individual i:individuals){
            System.out.println(i+": "+i.label);
            System.out.println(i.arches);
        }

        //TODO esporta con grafo RDF e mostra con graphviz
    }
    private Set<OWLClass> getClashes(Individual x) throws OWLException {
        //TODO restituisci concetto in clash
        HashSet<OWLClass> atomicClasses=new HashSet<>();
        HashSet<OWLClass> clashClasses=new HashSet<>();
        for(OWLClassExpression ce:x.label){
            if(parser.isClass(ce)){
                OWLClass c=(OWLClass)ce;
                atomicClasses.add(c);
            }
        }
        for(OWLClassExpression ce:x.label){
            if(parser.isNegation(ce)){
                OWLClassExpression c=parser.unpackNegation(ce);
                if(parser.isClass(c) && atomicClasses.contains(c))
                    clashClasses.add((OWLClass)c);
            }
        }
        return clashClasses;
    }
}
