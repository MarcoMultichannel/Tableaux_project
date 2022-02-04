import guru.nidi.graphviz.attribute.Attributes;
import guru.nidi.graphviz.attribute.Color;
import guru.nidi.graphviz.attribute.ForNode;
import guru.nidi.graphviz.attribute.Label;
import guru.nidi.graphviz.engine.Format;
import guru.nidi.graphviz.engine.Graphviz;
import guru.nidi.graphviz.engine.GraphvizCmdLineEngine;
import guru.nidi.graphviz.engine.GraphvizV8Engine;
import guru.nidi.graphviz.model.LinkTarget;
import guru.nidi.graphviz.model.MutableGraph;
import org.apache.jena.graph.Graph;
import org.apache.jena.graph.Triple;
import org.apache.jena.rdf.model.*;
import org.semanticweb.owlapi.model.*;

import java.awt.image.BufferedImage;
import java.io.*;
import java.util.*;

import static guru.nidi.graphviz.model.Factory.*;

public class Tableaux {
    private static final String ALC_NAMESPACE="urn://alc/";
    private static final String NAMESPACE="urn://talbeaux_project#";
    private static final String CONCEPT_NAME="<"+ALC_NAMESPACE+"Concept>";
    private final OWLClassExpression concept;
    private OWLOntology terminology;
    private final MyOWLParser parser;
    private HashSet<Individual> individuals;
    private Model model;

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
            Set<OWLClass> result=computeTableaux(new Individual(),concept);
            if(result!=null && !result.isEmpty())
                System.out.println("Il concetto ha un clash nelle seguenti classi:"+result);
            else
                System.out.println("Il concetto è soddisfacibile");
            createRDFmodel();
        } catch (OWLException e) {
            System.out.println("Errore nel tableaux");
            e.printStackTrace();
        }
    }

    private Set<OWLClass> computeTableaux(Individual x, OWLClassExpression concept) throws OWLException {
        //INPUT: individuo e concetto da aggiungere
        //OUTPUT: Se insoddisfacibile, insieme di classi in Clash
                //Altrimenti NULL

        individuals.add(x);

        //AND
        if(concept!=null){
            x.addConcept(concept);
            if(parser.isIntersection(concept)) {
                x.addConcepts(parser.unpackIntersection(concept));
            }
        }

        //OR
        for(OWLClassExpression ce:x.ors){
            //Marco l'OR come visitato
            if(x.isVisited(ce)) break;
            x.markAsVisited(ce);

            List<OWLClassExpression> disjoints = parser.unpackUnion(ce);
            Set<OWLClass> clashes=null;
            for(OWLClassExpression disjoint:disjoints){
                //Vedo se il disgiuto selezionato ha un CLASH
                clashes=computeTableaux(x, disjoint);

                //Se è clash free, esco da loop
                if (clashes==null || clashes.isEmpty()) break;

                //Altrimenti lo rimuovo e provo un altro disgiunto
                else x.removeConcept(disjoint);
            }
            //Se ha trovato un clash provando tutti i disgiunti restituisce l'ultimo clash
            if (clashes==null || !clashes.isEmpty()) return clashes;
        }

        //CLASH CHECK
        if(!getClashes(x).isEmpty()) return getClashes(x);

        //Creo una mappa per utilizzare un solo individuo per ogni ruolo
        HashMap<OWLObjectPropertyExpression, Individual> newArches=new HashMap<>();

        for(OWLClassExpression ce:x.exists) {
            //Estraggo il ruolo ed il concetto dall'esiste
            OWLObjectPropertyExpression role = parser.getExistRole(ce);
            OWLClassExpression classExpression = parser.getExistClassExpression(ce);

            //Se già c'è un individuo con quel ruolo uso quello
            Individual y=newArches.get(role);

            //Altrimenti ne creo un nuovo
            if (y==null) {
                y = new Individual();
                newArches.put(role, y);
            }
            //Aggiungo il concetto al nuovo individuo e aggiungo l'arco R(x,y)
            y.addConcept(classExpression);
            x.newArchTo(role,y);
        }

        //PerOgni
        for(OWLClassExpression ce:x.foreachs){
            //Estraggo il ruolo ed il concetto dal per ogni
            OWLObjectPropertyExpression role=parser.getForeachRole(ce);
            OWLClassExpression classExpression=parser.getForeachClassExpression(ce);

            //per ogni z tale che R(x,z) aggiungo il concetto
            for(Individual z:x.arches.get(role))
                z.addConcept(classExpression);
        }

        //CLASH CHECK sui nuovi individui y
        for(Individual y:x.individualsConnected){
            Set<OWLClass> clashes=computeTableaux(y, null);
            if (clashes==null || clashes.isEmpty()) break;
            else return clashes;
        }
        return null;
    }
    private Set<OWLClass> getClashes(Individual x) throws OWLException {
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
    private void createRDFmodel() throws OWLException {
        model = ModelFactory.createDefaultModel();
        for(Individual i:individuals){
            String individualURI = NAMESPACE+"x"+i.id;
            Resource individualResource = model.createResource(individualURI);
            Property hasLabel=model.createProperty( NAMESPACE + "L" );
            individualResource.addLiteral(hasLabel, formatLabel(i.label));
        }
        for(Individual x:individuals){
            for(OWLObjectPropertyExpression role:x.arches.keySet()){
                String roleURI=formatRole(role);
                Property hasArch=model.createProperty(roleURI);
                for(Individual y:x.arches.get(role)) {
                    Resource x_resource = model.getResource(NAMESPACE+"x"+x.id);
                    Resource y_resource = model.getResource(NAMESPACE+"x"+y.id);
                    x_resource.addProperty(hasArch, y_resource);
                }
            }
        }
        model.setNsPrefix( "tab", NAMESPACE );
        model.setNsPrefix( "alc", ALC_NAMESPACE );
    }
    public void save(String path) throws OWLException, IOException {
        Writer f = new FileWriter(path);
        model.write(f,"TURTLE");
    }

    public BufferedImage toImage() throws IOException {
        Graphviz.useEngine(new GraphvizCmdLineEngine());
        MutableGraph g = mutGraph("Tableaux");
        g.setDirected(true);
        Graph rdfGraph=model.getGraph();
        for(Triple triple:rdfGraph.stream().toList()){
            String subject=triple.getSubject().toString();
            String predicate=triple.getPredicate().toString();
            String object=triple.getObject().toString();
            g.add(mutNode(subject).addLink(to(mutNode(object).add(Attributes.attr("charset","UTF-8"))).with(Label.of(predicate))));
            //TODO prefissi, unicode e formattazione
        }
        return Graphviz.fromGraph(g).render(Format.PNG).toImage();
    }
    private String formatLabel(List<OWLClassExpression> label) throws OWLException {
        StringBuilder result= new StringBuilder();
        for(int i=0;i<label.size();i++) {
            result.append(formatClassExpression(label.get(i)));
            if(i!=label.size()-1)
                result.append(", ");
        }
        return result.toString();
    }
    private String formatClassExpression(OWLClassExpression ce) throws OWLException {
        StringBuilder result= new StringBuilder();
        if(parser.isClass(ce))
            result.append(formatAtomicClass(ce).split(ALC_NAMESPACE)[1]);
        else if (parser.isNegation(ce)) {
            result.append("¬(");
            result.append(formatClassExpression(ce));
            result.append(")");
        }
        else if(parser.isIntersection(ce)){
            List<OWLClassExpression> ands=parser.unpackIntersection(ce);
            for(int i=0;i<ands.size();i++){
                result.append("(");
                result.append(formatClassExpression(ands.get(i)));
                result.append(")");
                if(i!=ands.size()-1)
                    result.append(" ⊓ ");
            }
        }
        else if(parser.isUnion(ce)){
            List<OWLClassExpression> ors=parser.unpackUnion(ce);
            for(int i=0;i<ors.size();i++){
                result.append("(");
                result.append(formatClassExpression(ors.get(i)));
                result.append(")");
                if(i!=ors.size()-1)
                    result.append(" ⊔ ");
            }
        }
        else if(parser.isExists(ce)){
            OWLClassExpression existsConcept=parser.getExistClassExpression(ce);
            OWLObjectPropertyExpression existsRole=parser.getExistRole(ce);
            result.append("(∃");
            result.append(formatRole(existsRole).split(ALC_NAMESPACE)[1]);
            result.append(".(");
            result.append(formatClassExpression(existsConcept));
            result.append(")");
        }
        else if(parser.isForeach(ce)){
            OWLClassExpression foreachConcept=parser.getForeachClassExpression(ce);
            OWLObjectPropertyExpression foreachRole=parser.getForeachRole(ce);
            result.append("(∀");
            result.append(formatRole(foreachRole).split(ALC_NAMESPACE)[1]);
            result.append(".(");
            result.append(formatClassExpression(foreachConcept));
            result.append(")");
        }
        return result.toString();
    }
    private String formatRole(OWLObjectPropertyExpression role){
        return role.toString().replaceAll("[<>]", "");
    }
    private String formatAtomicClass(OWLClassExpression ce){
        return ce.toString().replaceAll("[<>]", "");
    }
}
