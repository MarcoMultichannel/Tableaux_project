import guru.nidi.graphviz.attribute.Attributes;
import guru.nidi.graphviz.attribute.Label;
import guru.nidi.graphviz.engine.Format;
import guru.nidi.graphviz.engine.Graphviz;
import guru.nidi.graphviz.engine.GraphvizCmdLineEngine;
import guru.nidi.graphviz.model.MutableGraph;
import org.apache.jena.graph.Graph;
import org.apache.jena.graph.Triple;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.Resource;
import org.semanticweb.owlapi.model.*;

import java.awt.image.BufferedImage;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.*;

import static guru.nidi.graphviz.model.Factory.*;

public class Tableaux {
    private static final String TAB_NAMESPACE="urn://tableaux_project#";
    private static final String ALC_NAMESPACE="urn://alc/";
    private static final String CONCEPT_NAME="<"+ALC_NAMESPACE+"Concept>";
    private final Map<String, String> prefix_nsMap;
    private final OWLClassExpression concept;
    private OWLOntology terminology;
    private final MyOWLParser parser;
    private HashSet<Individual> individuals;
    private Model model;
    private Set<OWLClass> clashes;
    public Tableaux(MyOWLParser parser, OWLOntology C) throws OWLException {
        this.parser=parser;
        //Carico i prefissi del namespace
        prefix_nsMap=parser.getPrefixMap(C);
        //Carico il concetto C
        List<OWLEquivalentClassesAxiom> axioms=parser.getEquivalentClassesAxioms(C);
        if(axioms.isEmpty())
            //Se l'ontologia del concetto C non è del tipo C equivalente <concept>
            throw new OWLException("Errore nel concetto C");
        else{
            List<OWLClassExpression> classExpressions=parser.unpackEquilvalentClassesAxiom(axioms.get(0));
            OWLClassExpression left=classExpressions.get(0);
            OWLClassExpression right=classExpressions.get(1);
            if(left.toString().equals(CONCEPT_NAME)) {
                //Trasformiamo in forma NNF
                concept = right.getNNF();
            }
            else
                throw new OWLException("Errore nel concetto C");
        }
    }
    public Tableaux(MyOWLParser parser, OWLOntology C, OWLOntology T) throws OWLException {
        this(parser, C);
        this.terminology=T;
        //TODO parsing della terminologia
    }
    public float execute(){
        individuals=new HashSet<>();
        float timeElapsed=0;
        try {
            long start = System.nanoTime();
            Individual x=new Individual();
            x.addConcept(concept);
            clashes=computeTableaux(x);
            long finish = System.nanoTime();
            timeElapsed=(finish - start)/1000000f;
            createRDFmodel();
        } catch (OWLException e) {
            System.out.println("Errore nel tableaux");
            e.printStackTrace();
        }
        return timeElapsed;
    }
    public String getConcept() throws OWLException {
        return replaceNSwithPrefixes(formatClassExpression(concept));
    }

    public boolean isClashFree(){
        return (clashes==null || clashes.isEmpty());
    }
    private Set<OWLClass> computeTableaux(Individual x) throws OWLException {
        //INPUT: individuo e concetto da aggiungere
        //OUTPUT: Se insoddisfacibile, insieme di classi in Clash
                //Altrimenti NULL
        individuals.add(x);
        //AND
        while (!x.ands.isEmpty()) {
            x.addConcepts(parser.unpackIntersection(x.ands.remove()));
        }
        //OR
        while (!x.ors.isEmpty()) {
            List<OWLClassExpression> disjoints = parser.unpackUnion(x.ors.remove());
            Set<OWLClass> clashes=null;
            for(OWLClassExpression disjoint:disjoints){
                //Mi salvo lo stato corrente per fare backtracking nel caso il disgiunto non va bene
                Individual old_x=new Individual(x);
                HashSet<Individual> old_individuals=new HashSet<>(individuals);

                //Vedo se il disgiuto selezionato ha un CLASH
                x.addConcept(disjoint);
                clashes=computeTableaux(x);

                //Se è clash free, esco da loop
                if (clashes==null || clashes.isEmpty()) break;

                //Altrimenti faccio backtracking
                else
                {
                    individuals=old_individuals;
                    individuals.remove(x);
                    ArrayList<OWLClassExpression> clashLabel=x.label;
                    x=old_x;
                    x.addClashLabel(clashLabel);
                }
            }
            //Se ha trovato un clash provando tutti i disgiunti restituisce l'ultimo clash
            if (clashes!=null && !clashes.isEmpty()) return clashes;
        }

        //CLASH CHECK
        if(!getClashes(x).isEmpty()) return getClashes(x);

        //Creo una mappa per utilizzare un solo individuo per ogni ruolo
        HashMap<OWLObjectPropertyExpression, Individual> newArches=new HashMap<>();

        while(!x.exists.isEmpty()){
            OWLClassExpression ce=x.exists.remove();
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
        while(!x.foreaches.isEmpty()){
            OWLClassExpression ce=x.foreaches.remove();
            //Estraggo il ruolo ed il concetto dal per ogni
            OWLObjectPropertyExpression role=parser.getForeachRole(ce);
            OWLClassExpression classExpression=parser.getForeachClassExpression(ce);
            //per ogni z tale che R(x,z) aggiungo il concetto
            for(Individual z:x.arches.get(role))
                z.addConcept(classExpression);
        }

        //CLASH CHECK sui nuovi individui y
        for(Individual y:x.individualsConnected){
            Set<OWLClass> clashes=computeTableaux(y);
            if (clashes==null || clashes.isEmpty()) break;
            else return clashes;
        }
        return null;
    }
    private Set<OWLClass> getClashes(Individual x) throws OWLException {
        HashSet<OWLClass> atomicClasses=new HashSet<>();
        HashSet<OWLClass> clashClasses=new HashSet<>();
        for(OWLClassExpression ce:x.label){
            if(parser.isBottom(ce)){
                clashClasses.add((OWLClass)ce);
            }
            else if(parser.isClass(ce)){
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
        for(Individual x:individuals){
            for(OWLObjectPropertyExpression role:x.arches.keySet()){
                String roleURI=formatRole(role);
                Property hasArch=model.createProperty(roleURI);
                for(Individual y:x.arches.get(role)) {
                    Resource x_resource = model.getResource(TAB_NAMESPACE+"x"+x.id);
                    Resource y_resource = model.getResource(TAB_NAMESPACE+"x"+y.id);
                    x_resource.addProperty(hasArch, y_resource);
                }
            }
        }
        for(Individual i:individuals){
            String individualURI = TAB_NAMESPACE+"x"+i.id;
            Resource individualResource = model.createResource(individualURI);
            Property clash=model.createProperty( TAB_NAMESPACE + "CLASH" );
            Property hasLabel=model.createProperty( TAB_NAMESPACE + "L" );
            Property disjointLabel=model.createProperty( TAB_NAMESPACE + "OR" );
            if(getClashes(i).isEmpty())
                individualResource.addLiteral(hasLabel, formatLabel(i.label));
            else {
                individualResource.addLiteral(clash, formatClashes(getClashes(i)));
                individualResource.addLiteral(hasLabel, formatLabel(i.label) + ", CLASH.");
            }
            for(ArrayList<OWLClassExpression> oldLabel:i.previousLabels)
                individualResource.addLiteral(disjointLabel, formatLabel(oldLabel)+", CLASH.");
        }
        model.setNsPrefix( "tab", TAB_NAMESPACE );
        for(String prefix:prefix_nsMap.keySet()) {
            model.setNsPrefix(prefix.split(":")[0], prefix_nsMap.get(prefix));
        }
    }
    public void save(String path) throws OWLException, IOException {
        Writer f = new FileWriter(path);
        model.write(f,"TURTLE");
    }

    public BufferedImage toImage(boolean addPrefixes) throws IOException {
        Graphviz.useEngine(new GraphvizCmdLineEngine());
        MutableGraph g = mutGraph("Tableaux");
        g.setDirected(true);
        Graph rdfGraph=model.getGraph();
        Map<String,String> prefixMap=model.getNsPrefixMap();
        for(Triple triple:rdfGraph.stream().toList()){
            String subject=triple.getSubject().toString();
            String predicate=triple.getPredicate().toString();
            String object=htmlEncode(triple.getObject().toString());
            for(String prefix:prefixMap.keySet()){
                String replacement="";
                if(addPrefixes) replacement=prefix+":";
                subject=subject.replaceAll(prefixMap.get(prefix),replacement);
                predicate=predicate.replaceAll(prefixMap.get(prefix),replacement);
                object=object.replaceAll(prefixMap.get(prefix),replacement);
                if(!addPrefixes)
                    object=object.replaceAll(prefix+":",replacement);
            }
            g.add(mutNode(subject).add(Attributes.attr("shape","rectangle")).addLink(to(
                    mutNode(object).add(Attributes.attr("shape","rectangle"))
                            .add(Attributes.attr("fontname","Cambria Math")))
                                .with(Label.of(predicate))));
            g.graphAttrs().add(Attributes.attr("rankdir","LR"));
        }
        return Graphviz.fromGraph(g).scale(1.4).render(Format.SVG).toImage();
    }
    private String formatLabel(List<OWLClassExpression> label) throws OWLException {
        StringBuilder result= new StringBuilder();
        for(int i=0;i<label.size();i++) {
            result.append(formatClassExpression(label.get(i)));
            if(i!=label.size()-1)
                result.append(", ");
        }
        return replaceNSwithPrefixes(result.toString());
    }
    private String formatClashes(Set<OWLClass> clashes) {
        StringBuilder result= new StringBuilder();
        Iterator<OWLClass> clashes_iterator=clashes.iterator();
        for(int i=0;i<clashes.size();i++){
            OWLClass clash=clashes_iterator.next();
            if (parser.isBottom(clash))
                result.append("⊥");
            else{
                result.append(formatAtomicClass(clash));
                result.append(", ¬");
                result.append(formatAtomicClass(clash));
            }

            if(i!=clashes.size()-1)
                result.append(", ");
        }
        return result.toString();
    }
    private String formatClassExpression(OWLClassExpression ce) throws OWLException {
        StringBuilder result= new StringBuilder();
        if (parser.isTop(ce))
            result.append("⊤");
        else if (parser.isBottom(ce))
            result.append("⊥");
        else if(parser.isClass(ce))
            result.append(formatAtomicClass(ce));
        else if (parser.isNegation(ce)) {
            result.append("¬");
            OWLClassExpression operand=parser.unpackNegation(ce);
            if(parser.isClass(operand) || parser.isNegation(operand))
                result.append(formatClassExpression(operand));
            else{
                result.append("(");
                result.append(formatClassExpression(operand));
                result.append(")");
            }
        }
        else if(parser.isIntersection(ce)){
            List<OWLClassExpression> ands=parser.unpackIntersection(ce);
            for(int i=0;i<ands.size();i++){
                OWLClassExpression operand=ands.get(i);
                if(parser.isClass(operand) || parser.isNegation(operand))
                    result.append(formatClassExpression(operand));
                else{
                    result.append("(");
                    result.append(formatClassExpression(operand));
                    result.append(")");
                }
                if(i!=ands.size()-1)
                    result.append(" ⊓ ");
            }
        }
        else if(parser.isUnion(ce)){
            List<OWLClassExpression> ors=parser.unpackUnion(ce);
            for(int i=0;i<ors.size();i++){
                OWLClassExpression operand=ors.get(i);
                if(parser.isClass(operand) || parser.isNegation(operand))
                    result.append(formatClassExpression(operand));
                else{
                    result.append("(");
                    result.append(formatClassExpression(operand));
                    result.append(")");
                }
                if(i!=ors.size()-1)
                    result.append(" ⊔ ");
            }
        }
        else if(parser.isExists(ce)){
            OWLClassExpression existsConcept=parser.getExistClassExpression(ce);
            OWLObjectPropertyExpression existsRole=parser.getExistRole(ce);
            result.append("∃");
            result.append(formatRole(existsRole));
            result.append(".");
            if(parser.isClass(existsConcept) || parser.isNegation(existsConcept))
                result.append(formatClassExpression(existsConcept));
            else{
                result.append("(");
                result.append(formatClassExpression(existsConcept));
                result.append(")");
            }
        }
        else if(parser.isForeach(ce)){
            OWLClassExpression foreachConcept=parser.getForeachClassExpression(ce);
            OWLObjectPropertyExpression foreachRole=parser.getForeachRole(ce);
            result.append("∀");
            result.append(formatRole(foreachRole));
            result.append(".");
            if(parser.isClass(foreachConcept) || parser.isNegation(foreachConcept))
                result.append(formatClassExpression(foreachConcept));
            else{
                result.append("(");
                result.append(formatClassExpression(foreachConcept));
                result.append(")");
            }
        }
        return result.toString();
    }
    private String formatRole(OWLObjectPropertyExpression role){
        return role.toString().replaceAll("[<>]", "");
    }
    private String formatAtomicClass(OWLClassExpression ce){
        return ce.toString().replaceAll("[<>]", "");
    }
    private String replaceNSwithPrefixes(String string){
        for(String prefix:prefix_nsMap.keySet())
            string=string.replaceAll(prefix_nsMap.get(prefix), prefix);
        return string;
    }
    private String htmlEncode(final String string) {
        String result=string;
        for (int i = 0; i < string.length(); i++) {
            result=result.replace("⊤","&#x22a4;");
            result=result.replace("⊥","&#x22a5;");
            result=result.replace("∀","&#x2200;");
            result=result.replace("∃","&#x2203;");
            result=result.replace("⊔","&#x2294;");
            result=result.replace("⊓","&#x2293;");
            result=result.replace("¬","&#xac;");
        }
        return result;
    }
}
