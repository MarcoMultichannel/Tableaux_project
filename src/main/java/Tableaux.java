
import guru.nidi.graphviz.attribute.Attributes;
import guru.nidi.graphviz.attribute.Label;
import guru.nidi.graphviz.engine.Format;
import guru.nidi.graphviz.engine.Graphviz;
import guru.nidi.graphviz.engine.GraphvizCmdLineEngine;
import static guru.nidi.graphviz.model.Factory.*;
import guru.nidi.graphviz.model.MutableGraph;
import java.awt.image.BufferedImage;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.apache.jena.graph.Graph;
import org.apache.jena.graph.Triple;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.Resource;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.BufferingMode;
import org.semanticweb.owlapi.reasoner.FreshEntityPolicy;
import org.semanticweb.owlapi.reasoner.IndividualNodeSetPolicy;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.util.Version;
import uk.ac.manchester.cs.owl.owlapi.*;

public class Tableaux implements OWLReasoner {

    private static final String TAB_NAMESPACE = "urn://tableaux_project#";
    private static final String TAB_PREFIX = "tab";
    private static final GraphUnfoldable unfoldableGraphTBox = new GraphUnfoldable();
    private final Map<String, String> prefix_nsMap;
    private final OWLClassExpression concept_Tbox;
    private final List<OWLAxiom> fullTbox;
    private final List<OWLAxiom> Tbox_unfoldable;
    private final MyOWLParser parser;
    private OWLClassExpression concept;
    private HashSet<Individual> individuals;

    private Model model;
    private Set<OWLClass> clashes;
    private float timeElapsed;

    
    public Tableaux(MyOWLParser parser, OWLOntology T) throws OWLException {
        this.parser = parser;
        //Carico i prefissi del namespace dalla TBox
        prefix_nsMap = parser.getPrefixMap(T);
        //Aggiungo il prefisso TAB
        prefix_nsMap.put(TAB_PREFIX + ":", TAB_NAMESPACE);
        //Carico l'intera TBox
        fullTbox = parser.getAxioms(T);
        ArrayList<OWLAxiom> axioms = new ArrayList<>(fullTbox);
        //Estraggo la componente unfoldable
        Tbox_unfoldable = getUnfoldableComponent(axioms);
        //Tolgo ciò che è stato preso nella TBox unfoldable
        axioms.removeAll(Tbox_unfoldable);
        //Separa inclusioni ed equivalenze
        List<OWLSubClassOfAxiom> subclassAxioms = parser.getSubClassAxioms(axioms);
        List<OWLEquivalentClassesAxiom> equivalenceAxioms = parser.getEquivalentClassesAxioms(axioms);
        //Converto equivalenze in doppie inclusioni
        for(OWLEquivalentClassesAxiom eqAxiom : equivalenceAxioms) {
            List<OWLClassExpression> classes = parser.unpackEquilvalentClassesAxiom(eqAxiom);
            subclassAxioms.add(new OWLSubClassOfAxiomImpl(classes.get(0), classes.get(1), new HashSet<>()));
            subclassAxioms.add(new OWLSubClassOfAxiomImpl(classes.get(1), classes.get(0), new HashSet<>()));
        }
        //Costruisco componente general
        concept_Tbox = getTboxConcept(subclassAxioms);
    }



    private @Nullable

    OWLClassExpression getTboxConcept(@NotNull List<OWLSubClassOfAxiom> subclassAxioms) throws OWLException {
        ArrayList<OWLClassExpression> operands = new ArrayList<>();
        for(OWLSubClassOfAxiom axiom : subclassAxioms) {
            //Prendo la parte di sinsitra e di destra dell'inclusione
            List<OWLClassExpression> ce = parser.unpackSubClassAxioms(axiom);
            OWLClassExpression subclass = ce.get(0);
            OWLClassExpression superclass = ce.get(1);
            //La converto nella forma in OR
            ArrayList<OWLClassExpression> disjoints = new ArrayList<>();
            disjoints.add(new OWLObjectComplementOfImpl(subclass));
            disjoints.add(superclass);
            operands.add(new OWLObjectUnionOfImpl(disjoints));
        }
        if(operands.isEmpty()) {
            return null;
        } else {
            //La converto in forma NNF
            return new OWLObjectIntersectionOfImpl(operands).getNNF();
        }
    }



    private @NotNull

    List<OWLAxiom> getUnfoldableComponent(List<OWLAxiom> axioms) {
        List<OWLAxiom> result = new ArrayList<>();
        for(OWLAxiom axiom : axioms) {
            if(parser.isSubClassOfAxiom(axiom) && !checkIfGraphAcyclic(axiom)) {
                //Se è vera posso aggiungere l'inclusione alla componente unfoldable
                createAndAddVertex(axiom);
                result.add(axiom);
            }
            if(parser.isEquivalentClassesAxiom(axiom) && !checkEquivalenceMethod(axiom, result)) {
                //Per equivalenze
                result.add(axiom);
            }
        }
        return result;
    }



    public void createAndAddVertex(OWLAxiom axiomTemp) {
        //Aggiungiamo l'assioma al grafo per check futuri
        try {
            List<OWLClassExpression> ce = parser.unpackSubClassAxioms((OWLSubClassOfAxiom) axiomTemp);
            OWLClassExpression subclass = ce.get(0);
            OWLClassExpression superclass = ce.get(1);
            unfoldableGraphTBox.addVertex(subclass);
            unfoldableGraphTBox.addVertex(superclass);
            unfoldableGraphTBox.addEdge(subclass, superclass);
        } catch(OWLException ex) {
            Logger.getLogger(Tableaux.class.getName()).log(Level.SEVERE, null, ex);
        }
    }



    public boolean checkEquivalenceMethod(OWLAxiom axiomTemp, List<OWLAxiom> unfoldableAxioms) {
        //Vediamo se la parte sinistra dell'equivalenza è già presente
        //nella parte di sinistra negli assiomi nella componente unfoldable
        boolean res = false;
        try {
            List<OWLClassExpression> ce = parser.unpackEquilvalentClassesAxiom((OWLEquivalentClassesAxiom)axiomTemp);
            List<OWLClassExpression> ceTemp = null;
            OWLClassExpression sxTemp = ce.get(0);
            for(OWLAxiom axiomUnfoldable : unfoldableAxioms) {
                if(parser.isSubClassOfAxiom(axiomUnfoldable))
                    ceTemp = parser.unpackSubClassAxioms((OWLSubClassOfAxiom)axiomUnfoldable);
                else if(parser.isEquivalentClassesAxiom(axiomUnfoldable))
                    ceTemp = parser.unpackEquilvalentClassesAxiom((OWLEquivalentClassesAxiom)axiomUnfoldable);
                else break;
                if(ceTemp != null) {
                    OWLClassExpression sxUnfoldableAxiom = ceTemp.get(0);
                    if(sxUnfoldableAxiom.equals(sxTemp)) {
                        res = true;
                        break;
                    }
                }
            }
        } catch(OWLException ex) {
            Logger.getLogger(Tableaux.class.getName()).log(Level.SEVERE, null, ex);
        }
        return res;
    }



    public boolean checkIfGraphAcyclic(OWLAxiom axiomTemp) {
        //Controlliamo se aggiungere axiomTemp al grafo causa un ciclo
        boolean res = false;
        try {
            //Crea un grafo temporaneo simile a unfoldableGraphTBox
            GraphUnfoldable unfoldableGraphTemp =  new GraphUnfoldable(unfoldableGraphTBox);
            //Prendiamo la parte sinistra e destra dell'assioma
            List<OWLClassExpression> ce = parser.unpackSubClassAxioms((OWLSubClassOfAxiom) axiomTemp);
            OWLClassExpression subclass = ce.get(0);
            OWLClassExpression superclass = ce.get(1);
            //Aggiungiamo i vertici e gli archi
            unfoldableGraphTemp.addVertex(subclass);
            unfoldableGraphTemp.addVertex(superclass);
            unfoldableGraphTemp.addEdge(subclass, superclass);
            //Controlliamo se ha un ciclo
            res = unfoldableGraphTemp.hasCycle();
        } catch(OWLException ex) {
            Logger.getLogger(Tableaux.class.getName()).log(Level.SEVERE, null, ex);
        }
        return res;
    }



    public float execute(OWLClassExpression ce) {
        //Inizializziamo la lista degli individui
        individuals = new HashSet<>();
        float timeElapsed = 0;
        try {
            long start = System.nanoTime();
            Individual individual = new Individual();
            concept = ce;
            individual.addConcept(concept);
            if(concept_Tbox != null)  individual.addConcepts(parser.unpackIntersection(concept_Tbox));
            clashes = computeTableaux(individual);
            long finish = System.nanoTime();
            timeElapsed = (finish - start) / 1000000f;
            createRDFmodel();
            Individual.setNextID(0);
        } catch(OWLException e) {
            System.out.println("Errore nel tableaux");
        }
        return timeElapsed;
    }



    public String getConcept() throws OWLException {
        return concept_Tbox != null ?  replaceNSwithPrefixes(formatClassExpression(concept)) + ", " + replaceNSwithPrefixes(formatClassExpression(concept_Tbox)) :  replaceNSwithPrefixes(formatClassExpression(concept)) ;
    }



    public boolean isClashFree() {
        return (clashes.isEmpty());
    }



    public String getClashes() {
        return replaceNSwithPrefixes(formatClashes(clashes));
    }



    private Set<OWLClass> computeTableaux(Individual individual) throws OWLException {
        //INPUT: individuo e concetto da aggiungere
        //OUTPUT: Se insoddisfacibile, insieme di classi in Clash
        //Altrimenti NULL
        individuals.add(individual);
        //AND
        while(!individual.ands.isEmpty()) {
            individual.addConcepts(parser.unpackIntersection(individual.ands.remove()));
        }
        Set<OWLClass> clashes = unfoldableExpantionRules(individual);
        if(!clashes.isEmpty()) {
            return clashes;
        }
        if(individual.isBlocked(individuals)) {
            individual.markAsBlocked();
            return clashes;
        }
        //OR
        while(!individual.ors.isEmpty()) {
            OWLClassExpression or = individual.ors.remove();
            Queue<OWLClassExpression> disjoints = new LinkedList<>(parser.unpackUnion( or));
            while(!disjoints.isEmpty()) {
                OWLClassExpression disjoint = disjoints.remove();
                //Mi salvo lo stato corrente per fare backtracking nel caso il disgiunto non va bene
                Individual oldIndividual = new Individual(individual);
                HashSet<Individual> oldIndividuals = new HashSet<>(individuals);
                //Vedo se il disgiuto selezionato ha un CLASH
                individual.addConcept(disjoint);
                clashes = computeTableaux(individual);
                //Se è clash free, esco da loop
                if(clashes.isEmpty()) {
                    break;
                } //Altrimenti faccio backtracking
                else if(!disjoints.isEmpty()) {
                    individuals = oldIndividuals;
                    individuals.remove(individual);
                    individuals.add(oldIndividual);
                    ArrayList<OWLClassExpression> clashLabel = individual.label;
                    individual = oldIndividual;
                    individual.addClashLabel( or , clashLabel);
                    Individual.setNextID(individual.id + 1);
                }
            }
            //Se ha trovato un clash provando tutti i disgiunti restituisce l'ultimo clash
            if(!clashes.isEmpty()) {
                return clashes;
            }
        }
        //CLASH CHECK
        if(!getClashes(individual).isEmpty()) {
            return getClashes(individual);
        }
        //EXISTS
        while(!individual.exists.isEmpty()) {
            OWLClassExpression ce = individual.exists.remove();
            //Estraggo il ruolo ed il concetto dall'esiste
            OWLObjectPropertyExpression role = parser.getExistRole(ce);
            OWLClassExpression classExpression = parser.getExistClassExpression(ce);
            Individual newIndividual = new Individual();
            if(concept_Tbox != null)  newIndividual.addConcepts(parser.unpackIntersection(concept_Tbox));
            //Aggiungo il concetto al nuovo individuo e aggiungo l'arco R(x,y)
            newIndividual.addConcept(classExpression);
            individual.newArchTo(role, newIndividual);
        }
        //FOREACH
        while(!individual.foreaches.isEmpty()) {
            OWLClassExpression ceFor = individual.foreaches.remove();
            //Estraggo il ruolo ed il concetto dal per ogni
            OWLObjectPropertyExpression roleFor = parser.getForeachRole(ceFor);
            OWLClassExpression classExpressionFor = parser.getForeachClassExpression(ceFor);
            //Per ogni individuo z tale che x---roleFor-->z) aggiungo il concetto classExpressionFor
            //Sfrutto la mappa (ruolo,individui) dell'individuo corrente per ottimizzare le performance
            for(Individual connectedIndividual: individual.arches.get(roleFor))
                connectedIndividual.addConcept(classExpressionFor);
        }
        for(Individual singleIndividual : individual.individualsConnected) {
            //CLASH CHECK sui nuovi individui y
            clashes = computeTableaux(singleIndividual);
            if(!clashes.isEmpty())
                return clashes;
        }
        return clashes;
    }



    private @NotNull

    Set<OWLClass> unfoldableExpantionRules(Individual individual) {
        Set<OWLClass> clashes = new HashSet<>();
        try {
            List<OWLSubClassOfAxiom> subclassAxioms = parser.getSubClassAxioms(Tbox_unfoldable);
            List<OWLEquivalentClassesAxiom> equivalenceAxioms = parser.getEquivalentClassesAxioms(Tbox_unfoldable);
            // veifichiamo prima le inclusioni
            for(OWLSubClassOfAxiom subclassAxiom : subclassAxioms) {
                try {
                    // per ogni inclusione prendiamo parte sx e dx
                    List<OWLClassExpression> ceAxiom = parser.unpackSubClassAxioms((OWLSubClassOfAxiom) subclassAxiom);
                    OWLClassExpression sxAxiom = ceAxiom.get(0);
                    OWLClassExpression dxAxiom = ceAxiom.get(1);
                    // applico regole espansione per le inclusioni
                    if(individual.label.contains(sxAxiom))
                        individual.addConcept(dxAxiom);
                } catch(OWLException ex) {
                    Logger.getLogger(Tableaux.class.getName()).log(Level.SEVERE, null, ex);
                }
            }
            // verifichiamo ora le equivalenze
            for(OWLEquivalentClassesAxiom equivalenceAxiom : equivalenceAxioms) {
                try {
                    // per ogni inclusione prendiamo parte sx e dx
                    List<OWLClassExpression> ceAxiom = parser.unpackEquilvalentClassesAxiom((OWLEquivalentClassesAxiom) equivalenceAxiom);
                    OWLClassExpression sxAxiom = ceAxiom.get(0);
                    OWLClassExpression dxAxiom = ceAxiom.get(1);
                    // applico regole espansione per le inclusioni
                    if(individual.label.contains(sxAxiom))
                        individual.addConcept(dxAxiom);
                } catch(OWLException ex) {
                    Logger.getLogger(Tableaux.class.getName()).log(Level.SEVERE, null, ex);
                }
            }
            // clash Check
            clashes = getClashes(individual);
        } catch(OWLException ex) {
            Logger.getLogger(Tableaux.class.getName()).log(Level.SEVERE, null, ex);
        }
        return clashes;
    }



    private @NotNull

    Set<OWLClass> getClashes(@NotNull Individual individual) throws OWLException {
        HashSet<OWLClass> atomicClasses = new HashSet<>();
        HashSet<OWLClass> clashClasses = new HashSet<>();
        for(OWLClassExpression ce : individual.label) {
            if(parser.isBottom(ce)) {
                clashClasses.add((OWLClass) ce);
            } else if(parser.isClass(ce)) {
                OWLClass c = (OWLClass) ce;
                atomicClasses.add(c);
            }
        }
        for(OWLClassExpression ce : individual.label) {
            if(parser.isNegation(ce)) {
                OWLClassExpression c = parser.unpackNegation(ce);
                if(parser.isClass(c) && atomicClasses.contains((OWLClass)c)) {
                    clashClasses.add((OWLClass) c);
                }
            }
        }
        return clashClasses;
    }



    private void createRDFmodel() throws OWLException {
        model = ModelFactory.createDefaultModel();
        for(Individual individual : individuals) {
            for(OWLObjectPropertyExpression role : individual.arches.keySet()) {
                String roleURI = formatRole(role);
                Property hasArch = model.createProperty(roleURI);
                for(Individual singleIndividual : individual.arches.get(role)) {
                    Resource individualResource = model.getResource(TAB_NAMESPACE + "x" + individual.id);
                    Resource singleIndividualResource = model.getResource(TAB_NAMESPACE + "x" + singleIndividual.id);
                    individualResource.addProperty(hasArch, singleIndividualResource);
                }
            }
        }
        for(Individual individual : individuals) {
            String individualURI = TAB_NAMESPACE + "x" + individual.id;
            Resource individualResource = model.createResource(individualURI);
            Property blockedLabel = model.createProperty(TAB_NAMESPACE + "BLOCKED");
            if(individual.blocked) {
                individualResource.addLiteral(blockedLabel, "Yes");
            }
            Property disjointLabel;
            int i = 1;
            for(OWLClassExpression or : individual.previousLabelsMap.keySet()) {
                for(ArrayList<OWLClassExpression> oldLabel : individual.previousLabelsMap.get( or)) {
                    disjointLabel = model.createProperty(TAB_NAMESPACE + "OR" + i);
                    i++;
                    individualResource.addLiteral(disjointLabel, formatLabel(oldLabel, or) + ", CLASH.");
                }
            }
            Property lastLabel = model.createProperty(TAB_NAMESPACE + "OR" + i);
            String labelStr;
            if(individual.lastOR != null) {
                labelStr = formatLabel(individual.label, individual.lastOR);
            } else {
                labelStr = formatLabel(individual.label);
            }
            if(getClashes(individual).isEmpty()) {
                individualResource.addLiteral(lastLabel, labelStr);
            } else {
                individualResource.addLiteral(lastLabel, labelStr + ", CLASH.");
            }
        }
        model.setNsPrefix("tab", TAB_NAMESPACE);
        for(String prefix : prefix_nsMap.keySet()) {
            model.setNsPrefix(prefix.split(":")[0], prefix_nsMap.get(prefix));
        }
    }



    public void save(String path) throws OWLException, IOException {
        Writer f = new FileWriter(path);
        model.write(f, "TURTLE");
    }



    public BufferedImage toImage(boolean addPrefixes) throws IOException {
        Graphviz.useEngine(new GraphvizCmdLineEngine());
        MutableGraph g = mutGraph("Tableaux");
        g.setDirected(true);
        Graph rdfGraph = model.getGraph();
        for(Triple triple : rdfGraph.stream().toList()) {
            String subject = replaceNSwithPrefixes(triple.getSubject().toString());
            String predicate = replaceNSwithPrefixes(triple.getPredicate().toString());
            String object = replaceNSwithPrefixes(htmlEncode(triple.getObject().toString()));
            object = object.replace("[", "<font color=\"red\">");
            object = object.replace("]", "</font>");
            if(!addPrefixes) {
                subject = removePrefixes(subject);
                predicate = removePrefixes(predicate);
                object = removePrefixes(object);
            }
            g.add(mutNode(subject).add(Attributes.attr("shape", "rectangle")).addLink(to(
                        mutNode(Label.html(object))
                        .add(Attributes.attr("shape", "rectangle"))
                        .add(Attributes.attr("fontname", "Cambria Math")))
                    .with(Label.of(predicate))));
            g.graphAttrs().add(Attributes.attr("rankdir", "LR"));
        }
        try {
            String Tbox_unfoldableStr = htmlEncode(formatAxioms(Tbox_unfoldable));
            String fullTboxStr = replaceNSwithPrefixes(htmlEncode(formatAxioms(fullTbox)));
            String conceptStr = replaceNSwithPrefixes(htmlEncode(formatClassExpression(concept)));
            String TBox_generalStr = null;
            if(concept_Tbox != null)  TBox_generalStr = replaceNSwithPrefixes(htmlEncode(formatClassExpression(concept_Tbox)));
            if(!addPrefixes) {
                Tbox_unfoldableStr = removePrefixes(Tbox_unfoldableStr);
                fullTboxStr = removePrefixes(fullTboxStr);
                if(concept_Tbox != null)  TBox_generalStr = removePrefixes(TBox_generalStr);
                conceptStr = removePrefixes(conceptStr);
            }
            g.add(mutNode("C: " + conceptStr + "\nT: " + fullTboxStr + "\nTu: " + Tbox_unfoldableStr+ "\nTg: " + TBox_generalStr)
            .add(Attributes.attr("fontname", "Cambria Math"))
            .add(Attributes.attr("shape", "rectangle")));
        } catch(OWLException ex) {
            Logger.getLogger(Tableaux.class.getName()).log(Level.SEVERE, null, ex);
        }
        return Graphviz.fromGraph(g).scale(1.4).render(Format.PNG).toImage();
    }



    private String formatLabel(@NotNull List<OWLClassExpression> label) throws OWLException {
        StringBuilder result = new StringBuilder();
        for(int i = 0; i < label.size(); i++) {
            result.append(formatClassExpression(label.get(i)));
            if(i != label.size() - 1) {
                result.append(", ");
            }
        }
        return replaceNSwithPrefixes(result.toString());
    }



    private String formatLabel(@NotNull List<OWLClassExpression> label, OWLClassExpression highlightCe) throws OWLException {
        String result = formatLabel(label);
        String or = replaceNSwithPrefixes(formatClassExpression(highlightCe));
        String newOr = '[' + or + ']';
        result = result.replace( or , newOr);
        return result;
    }

    private String formatAxioms(@NotNull List<OWLAxiom> axioms) throws OWLException {
        StringBuilder result = new StringBuilder();
        for(int i = 0; i < axioms.size(); i++) {
            if(parser.isSubClassOfAxiom(axioms.get(i)) || parser.isEquivalentClassesAxiom(axioms.get(i))) {
                result.append(formatAxiom(axioms.get(i)));
                if(i != axioms.size() - 1) {
                    result.append(", ");
                }
            }
        }
        return replaceNSwithPrefixes(result.toString());
    }



    private @NotNull

    String formatClashes(@NotNull Set<OWLClass> clashes) {
        StringBuilder result = new StringBuilder();
        Iterator<OWLClass> clashes_iterator = clashes.iterator();
        for(int i = 0; i < clashes.size(); i++) {
            OWLClass clash = clashes_iterator.next();
            if(parser.isBottom(clash)) {
                result.append("⊥");
            } else {
                result.append(formatAtomicClass(clash));
                result.append(", ¬");
                result.append(formatAtomicClass(clash));
            }
            if(i != clashes.size() - 1) {
                result.append(", ");
            }
        }
        return result.toString();
    }



    private @NotNull

    String formatClassExpression(OWLClassExpression ce) throws OWLException {
        StringBuilder result = new StringBuilder();
        if(parser.isTop(ce)) {
            result.append("⊤");
        } else if(parser.isBottom(ce)) {
            result.append("⊥");
        } else if(parser.isClass(ce)) {
            result.append(formatAtomicClass(ce));
        } else if(parser.isNegation(ce)) {
            result.append("¬");
            OWLClassExpression operand = parser.unpackNegation(ce);
            if(parser.isClass(operand) || parser.isNegation(operand)) {
                result.append(formatClassExpression(operand));
            } else {
                result.append("(");
                result.append(formatClassExpression(operand));
                result.append(")");
            }
        } else if(parser.isIntersection(ce)) {
            List<OWLClassExpression> ands = parser.unpackIntersection(ce);
            for(int i = 0; i < ands.size(); i++) {
                OWLClassExpression operand = ands.get(i);
                if(parser.isClass(operand) || parser.isNegation(operand)) {
                    result.append(formatClassExpression(operand));
                } else {
                    result.append("(");
                    result.append(formatClassExpression(operand));
                    result.append(")");
                }
                if(i != ands.size() - 1) {
                    result.append(" ⊓ ");
                }
            }
        } else if(parser.isUnion(ce)) {
            List<OWLClassExpression> ors = parser.unpackUnion(ce);
            for(int i = 0; i < ors.size(); i++) {
                OWLClassExpression operand = ors.get(i);
                if(parser.isClass(operand) || parser.isNegation(operand)) {
                    result.append(formatClassExpression(operand));
                } else {
                    result.append("(");
                    result.append(formatClassExpression(operand));
                    result.append(")");
                }
                if(i != ors.size() - 1) {
                    result.append(" ⊔ ");
                }
            }
        } else if(parser.isExists(ce)) {
            OWLClassExpression existsConcept = parser.getExistClassExpression(ce);
            OWLObjectPropertyExpression existsRole = parser.getExistRole(ce);
            result.append("∃");
            result.append(formatRole(existsRole));
            result.append(".");
            if(parser.isClass(existsConcept) || parser.isNegation(existsConcept)) {
                result.append(formatClassExpression(existsConcept));
            } else {
                result.append("(");
                result.append(formatClassExpression(existsConcept));
                result.append(")");
            }
        } else if(parser.isForeach(ce)) {
            OWLClassExpression foreachConcept = parser.getForeachClassExpression(ce);
            OWLObjectPropertyExpression foreachRole = parser.getForeachRole(ce);
            result.append("∀");
            result.append(formatRole(foreachRole));
            result.append(".");
            if(parser.isClass(foreachConcept) || parser.isNegation(foreachConcept)) {
                result.append(formatClassExpression(foreachConcept));
            } else {
                result.append("(");
                result.append(formatClassExpression(foreachConcept));
                result.append(")");
            }
        }
        return result.toString();
    }

    private @NotNull

    String formatAxiom(OWLAxiom ax) throws OWLException {
        StringBuilder result = new StringBuilder();
        if(parser.isSubClassOfAxiom(ax)) {
            List<OWLClassExpression> list = parser.unpackSubClassAxioms((OWLSubClassOfAxiom)ax);
            OWLClassExpression left = list.get(0);
            OWLClassExpression right = list.get(1);
            result.append(formatClassExpression(left));
            result.append("⊑");
            result.append(formatClassExpression(right));
        } else if(parser.isEquivalentClassesAxiom(ax)) {
            List<OWLClassExpression> list = parser.unpackEquilvalentClassesAxiom((OWLEquivalentClassesAxiom)ax);
            OWLClassExpression left = list.get(0);
            OWLClassExpression right = list.get(1);
            result.append(formatClassExpression(left));
            result.append("≡");
            result.append(formatClassExpression(right));
        }
        return result.toString();
    }

    private @NotNull

    String formatRole(@NotNull OWLObjectPropertyExpression role) {
        return role.toString().replaceAll("[<>]", "");
    }



    private @NotNull

    String formatAtomicClass(@NotNull OWLClassExpression ce) {
        return ce.toString().replaceAll("[<>]", "");
    }



    private String replaceNSwithPrefixes(String string) {
        for(String prefix : prefix_nsMap.keySet())
            string = string.replaceAll(prefix_nsMap.get(prefix), prefix);
        return string;
    }

    private String removePrefixes(String string) {
        for(String prefix : prefix_nsMap.keySet())
            string = string.replaceAll(prefix, "");
        return string;
    }

    public String htmlEncode(final @NotNull String string) {
        String result = string;
        for(int i = 0; i < string.length(); i++) {
            result = result.replace("⊤", "&#x22a4;");
            result = result.replace("⊥", "&#x22a5;");
            result = result.replace("∀", "&#x2200;");
            result = result.replace("∃", "&#x2203;");
            result = result.replace("⊔", "&#x2294;");
            result = result.replace("⊓", "&#x2293;");
            result = result.replace("¬", "&#xac;");
            result = result.replace("⊑", "&#x2291;");
            result = result.replace("≡", "&#x2261;");
        }
        return result;
    }



    public float getTimeElapsed() {
        return this.timeElapsed;
    }



    @Override

    public boolean isSatisfiable(OWLClassExpression classExpression) {
        timeElapsed = execute(classExpression);
        return clashes.isEmpty();
    }



    @Override

    public String getReasonerName() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Version getReasonerVersion() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public BufferingMode getBufferingMode() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public void flush() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public List<OWLOntologyChange> getPendingChanges() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Set<OWLAxiom> getPendingAxiomAdditions() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Set<OWLAxiom> getPendingAxiomRemovals() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public OWLOntology getRootOntology() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public void interrupt() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public void precomputeInferences(InferenceType... inferenceTypes) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public boolean isPrecomputed(InferenceType inferenceType) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Set<InferenceType> getPrecomputableInferenceTypes() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public boolean isConsistent() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Node<OWLClass> getUnsatisfiableClasses() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public boolean isEntailed(OWLAxiom axiom) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public boolean isEntailed(Set <? extends OWLAxiom > axioms) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public boolean isEntailmentCheckingSupported(AxiomType<?> axiomType) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Node<OWLClass> getTopClassNode() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Node<OWLClass> getBottomClassNode() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLClass> getSubClasses(OWLClassExpression ce, boolean direct) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLClass> getSuperClasses(OWLClassExpression ce, boolean direct) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Node<OWLClass> getEquivalentClasses(OWLClassExpression ce) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLClass> getDisjointClasses(OWLClassExpression ce) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Node<OWLObjectPropertyExpression> getTopObjectPropertyNode() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Node<OWLObjectPropertyExpression> getBottomObjectPropertyNode() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLObjectPropertyExpression> getSubObjectProperties(OWLObjectPropertyExpression pe, boolean direct) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLObjectPropertyExpression> getSuperObjectProperties(OWLObjectPropertyExpression pe, boolean direct) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Node<OWLObjectPropertyExpression> getEquivalentObjectProperties(OWLObjectPropertyExpression pe) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLObjectPropertyExpression> getDisjointObjectProperties(OWLObjectPropertyExpression pe) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Node<OWLObjectPropertyExpression> getInverseObjectProperties(OWLObjectPropertyExpression pe) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLClass> getObjectPropertyDomains(OWLObjectPropertyExpression pe, boolean direct) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLClass> getObjectPropertyRanges(OWLObjectPropertyExpression pe, boolean direct) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Node<OWLDataProperty> getTopDataPropertyNode() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Node<OWLDataProperty> getBottomDataPropertyNode() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLDataProperty> getSubDataProperties(OWLDataProperty pe, boolean direct) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLDataProperty> getSuperDataProperties(OWLDataProperty pe, boolean direct) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Node<OWLDataProperty> getEquivalentDataProperties(OWLDataProperty pe) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLDataProperty> getDisjointDataProperties(OWLDataPropertyExpression pe) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLClass> getDataPropertyDomains(OWLDataProperty pe, boolean direct) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLClass> getTypes(OWLNamedIndividual ind, boolean direct) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLNamedIndividual> getInstances(OWLClassExpression ce, boolean direct) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLNamedIndividual> getObjectPropertyValues(OWLNamedIndividual ind, OWLObjectPropertyExpression pe) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Set<OWLLiteral> getDataPropertyValues(OWLNamedIndividual ind, OWLDataProperty pe) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public Node<OWLNamedIndividual> getSameIndividuals(OWLNamedIndividual ind) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public NodeSet<OWLNamedIndividual> getDifferentIndividuals(OWLNamedIndividual ind) {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public long getTimeOut() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public FreshEntityPolicy getFreshEntityPolicy() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public IndividualNodeSetPolicy getIndividualNodeSetPolicy() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    @Override

    public void dispose() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }

}


