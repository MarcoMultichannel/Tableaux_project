import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
    public Map<String, String> getPrefixMap(OWLOntology ontology){
        OWLDocumentFormat format = manager.getOntologyFormat(ontology);
        Map<String, String> map = new HashMap<>();
        if (format!=null && format.isPrefixOWLDocumentFormat())
            map = format.asPrefixOWLDocumentFormat().getPrefixName2PrefixMap();
        return map;
    }
    public List<OWLEquivalentClassesAxiom> getEquivalentClassesAxioms(OWLOntology ont){
        return new ArrayList<>(ont.getAxioms(AxiomType.EQUIVALENT_CLASSES,Imports.EXCLUDED));
    }
    public List<OWLSubClassOfAxiom> getSubClassAxioms(OWLOntology ont){
        return new ArrayList<>(ont.getAxioms(AxiomType.SUBCLASS_OF,Imports.EXCLUDED));
    }
    public List<OWLClassExpression> unpackEquilvalentClassesAxiom(OWLEquivalentClassesAxiom axiom) throws OWLException {
        if(axiom.getAxiomType()!=AxiomType.EQUIVALENT_CLASSES){
            throw new OWLException("Not EQUIVALENT_CLASSES");
        }
        return new ArrayList<>(axiom.getClassExpressions());
    }
    public List<OWLClassExpression> unpackSubClassAxioms(OWLSubClassOfAxiom axiom) throws OWLException {
        if(axiom.getAxiomType()!=AxiomType.SUBCLASS_OF){
            throw new OWLException("Not SUBCLASS_OF");
        }
        ArrayList<OWLClassExpression> array=new ArrayList<>();
        array.add(axiom.getSubClass());
        array.add(axiom.getSuperClass());
        return array;
    }
    public List<OWLClassExpression> unpackIntersection(OWLClassExpression and) throws OWLException {
        if(and.getClassExpressionType()!= ClassExpressionType.OBJECT_INTERSECTION_OF){
            throw new OWLException("Not an OBJECT_INTERSECTION_OF");
        }
        ArrayList<OWLClassExpression> resultList=new ArrayList<>(((OWLObjectIntersectionOf)and).getOperands());
        ArrayList<OWLClassExpression> recursiveIntersections=new ArrayList<>();
        for(OWLClassExpression ce:resultList)
            if(isIntersection(ce))
                recursiveIntersections.addAll(unpackIntersection(ce));
        resultList.addAll(recursiveIntersections);
        return resultList;
    }
    public List<OWLClassExpression> unpackUnion(OWLClassExpression or) throws OWLException {
        if(or.getClassExpressionType()!= ClassExpressionType.OBJECT_UNION_OF){
            throw new OWLException("Not an OBJECT_UNION_OF");
        }
        return new ArrayList<>(((OWLObjectUnionOf)or).getOperands());
    }
    public OWLClassExpression unpackNegation(OWLClassExpression not) throws OWLException {
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
    public boolean isIntersection(OWLClassExpression ce){
        return ce.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF;
    }
    public boolean isUnion(OWLClassExpression ce){
        return ce.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF;
    }
    public boolean isExists(OWLClassExpression ce){
        return ce.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM;
    }
    public boolean isForeach(OWLClassExpression ce){
        return ce.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM;
    }
    public boolean isNegation(OWLClassExpression ce){
        return ce.getClassExpressionType() == ClassExpressionType.OBJECT_COMPLEMENT_OF;
    }
    public boolean isClass(OWLClassExpression ce){
        return ce.isOWLClass();
    }
    public boolean isTop(OWLClassExpression ce){
        return ce.isOWLThing();
    }
    public boolean isBottom(OWLClassExpression ce){
        return ce.isOWLNothing();
    }
}
