import org.jetbrains.annotations.NotNull;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.semanticweb.owlapi.expression.ShortFormEntityChecker;
import org.semanticweb.owlapi.manchestersyntax.renderer.ManchesterOWLSyntaxPrefixNameShortFormProvider;
import org.semanticweb.owlapi.util.BidirectionalShortFormProvider;
import org.semanticweb.owlapi.util.BidirectionalShortFormProviderAdapter;
import org.semanticweb.owlapi.util.ShortFormProvider;
import org.semanticweb.owlapi.util.mansyntax.ManchesterOWLSyntaxParser;

public class MyOWLParser {
    private final OWLOntologyManager manager;
    public MyOWLParser(){
        this.manager=OWLManager.createOWLOntologyManager();
    }
    public OWLOntology loadOntologyFromFile(String path) throws OWLOntologyCreationException {
        return manager.loadOntologyFromOntologyDocument(new File(path));
    }
    public OWLOntology loadOntologyFromString(String document) throws OWLOntologyCreationException {
        StringDocumentSource ontologyString=new StringDocumentSource(document);
        return manager.loadOntologyFromOntologyDocument(ontologyString);
    }
    public OWLClassExpression parseConcept(OWLOntology ont, String ce){
        ManchesterOWLSyntaxParser manchesterParser=OWLManager.createManchesterParser();
        manchesterParser.setDefaultOntology(ont);
        manchesterParser.setStringToParse(ce);
        ShortFormEntityChecker checker = new ShortFormEntityChecker(getShortFormProvider(ont));
        manchesterParser.setOWLEntityChecker(checker);
        return manchesterParser.parseClassExpression();
    }
    private BidirectionalShortFormProvider getShortFormProvider(OWLOntology ont) {
        Set<OWLOntology> ontologies = manager.getOntologies();
        ShortFormProvider sfp = new ManchesterOWLSyntaxPrefixNameShortFormProvider(manager.getOntologyFormat(ont));
        BidirectionalShortFormProvider shortFormProvider = new BidirectionalShortFormProviderAdapter(ontologies, sfp);
        return shortFormProvider;
    }
    public Map<String, String> getPrefixMap(OWLOntology ontology){
        OWLDocumentFormat format = manager.getOntologyFormat(ontology);
        Map<String, String> map = new HashMap<>();
        if (format!=null && format.isPrefixOWLDocumentFormat())
            map = format.asPrefixOWLDocumentFormat().getPrefixName2PrefixMap();
        return map;
    }
    public List<OWLAxiom> getAxioms(@NotNull OWLOntology ont){
        return new ArrayList<>(ont.getAxioms(Imports.EXCLUDED));
    }
    public List<OWLEquivalentClassesAxiom> getEquivalentClassesAxioms(@NotNull OWLOntology ont){
        return new ArrayList<>(ont.getAxioms(AxiomType.EQUIVALENT_CLASSES,Imports.EXCLUDED));
    }
    public List<OWLSubClassOfAxiom> getSubClassAxioms(@NotNull OWLOntology ont){
        return new ArrayList<>(ont.getAxioms(AxiomType.SUBCLASS_OF,Imports.EXCLUDED));
    }
    public List<OWLEquivalentClassesAxiom> getEquivalentClassesAxioms(@NotNull List<OWLAxiom> axioms){
        ArrayList<OWLEquivalentClassesAxiom> result=new ArrayList<>();
        for(OWLAxiom ax:axioms){
            if(this.isEquivalentClassesAxiom(ax))
                result.add((OWLEquivalentClassesAxiom)ax);
        }
        return result;
    }
    public List<OWLSubClassOfAxiom> getSubClassAxioms(@NotNull List<OWLAxiom> axioms){
        ArrayList<OWLSubClassOfAxiom> result=new ArrayList<>();
        for(OWLAxiom ax:axioms){
            if(this.isSubClassOfAxiom(ax))
                result.add((OWLSubClassOfAxiom)ax);
        }
        return result;
    }
    public List<OWLClassExpression> unpackEquilvalentClassesAxiom(@NotNull OWLEquivalentClassesAxiom axiom) throws OWLException {
        if(axiom.getAxiomType()!=AxiomType.EQUIVALENT_CLASSES){
            throw new OWLException("Not EQUIVALENT_CLASSES");
        }
        return new ArrayList<>(axiom.getClassExpressions());
    }
    public List<OWLClassExpression> unpackSubClassAxioms(@NotNull OWLSubClassOfAxiom axiom) throws OWLException {
        if(axiom.getAxiomType()!=AxiomType.SUBCLASS_OF){
            throw new OWLException("Not SUBCLASS_OF");
        }
        ArrayList<OWLClassExpression> array=new ArrayList<>();
        array.add(axiom.getSubClass());
        array.add(axiom.getSuperClass());
        return array;
    }
    public List<OWLClassExpression> unpackIntersection(@NotNull OWLClassExpression and) throws OWLException {
        if(and.getClassExpressionType()!= ClassExpressionType.OBJECT_INTERSECTION_OF){
            throw new OWLException("Not an OBJECT_INTERSECTION_OF");
        }
        ArrayList<OWLClassExpression> resultList=new ArrayList<>();
        for(OWLClassExpression ce:((OWLObjectIntersectionOf) and).getOperands())
            if(isIntersection(ce))
                resultList.addAll(unpackIntersection(ce));
            else
                resultList.add(ce);
        return resultList;
    }
    public List<OWLClassExpression> unpackUnion(@NotNull OWLClassExpression or) throws OWLException {
        if(or.getClassExpressionType()!= ClassExpressionType.OBJECT_UNION_OF){
            throw new OWLException("Not an OBJECT_UNION_OF");
        }
        ArrayList<OWLClassExpression> resultList=new ArrayList<>();
        for(OWLClassExpression ce:((OWLObjectUnionOf) or).getOperands())
            if(isUnion(ce))
                resultList.addAll(unpackUnion(ce));
            else
                resultList.add(ce);
        return resultList;
    }
    public OWLClassExpression unpackNegation(@NotNull OWLClassExpression not) throws OWLException {
        if(not.getClassExpressionType()!= ClassExpressionType.OBJECT_COMPLEMENT_OF){
            throw new OWLException("Not an OBJECT_UNION_OF");
        }
        return ((OWLObjectComplementOf)not).getOperand();
    }
    public OWLClassExpression getExistClassExpression(OWLClassExpression exists) {
        OWLObjectSomeValuesFrom ce= (OWLObjectSomeValuesFrom) exists;
        return ce.getFiller();
    }
    public OWLClassExpression getForeachClassExpression(OWLClassExpression foreach) {
        OWLObjectAllValuesFrom ce= (OWLObjectAllValuesFrom) foreach;
        return ce.getFiller();
    }
    public OWLObjectPropertyExpression getExistRole(OWLClassExpression exists) throws OWLException {
        OWLObjectSomeValuesFrom ce= (OWLObjectSomeValuesFrom) exists;
        OWLObjectPropertyExpression propExpr=ce.getProperty();
        if(propExpr.isOWLObjectProperty())
            return propExpr;
        else
            throw new OWLException("This is not ALC logic");
    }
    public OWLObjectPropertyExpression getForeachRole(OWLClassExpression exists) throws OWLException {
        OWLObjectAllValuesFrom ce= (OWLObjectAllValuesFrom) exists;
        OWLObjectPropertyExpression propExpr=ce.getProperty();
        if(propExpr.isOWLObjectProperty())
            return propExpr;
        else
            throw new OWLException("This is not ALC logic");
    }

//isSomething methods
    public boolean isIntersection(@NotNull OWLClassExpression ce){
        return ce.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF;
    }
    public boolean isUnion(@NotNull OWLClassExpression ce){
        return ce.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF;
    }
    public boolean isExists(@NotNull OWLClassExpression ce){
        return ce.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM;
    }
    public boolean isForeach(@NotNull OWLClassExpression ce){
        return ce.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM;
    }
    public boolean isNegation(@NotNull OWLClassExpression ce){
        return ce.getClassExpressionType() == ClassExpressionType.OBJECT_COMPLEMENT_OF;
    }
    public boolean isClass(@NotNull OWLClassExpression ce){
        return ce.isOWLClass();
    }
    public boolean isTop(@NotNull OWLClassExpression ce){
        return ce.isOWLThing();
    }
    public boolean isBottom(@NotNull OWLClassExpression ce){
        return ce.isOWLNothing();
    }
    public boolean isSubClassOfAxiom(@NotNull OWLAxiom ax){
        return ax.isOfType(AxiomType.SUBCLASS_OF);
    }
    public boolean isEquivalentClassesAxiom(@NotNull OWLAxiom ax){
        return ax.isOfType(AxiomType.EQUIVALENT_CLASSES);
    }
}
