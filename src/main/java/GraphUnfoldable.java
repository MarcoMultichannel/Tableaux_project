
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;

/*
 * Click nbfs://nbhost/SystemFileSystem/Templates/Licenses/license-default.txt to change this license
 * Click nbfs://nbhost/SystemFileSystem/Templates/Classes/Class.java to edit this template
 */

/**
 *
 * @author cirom
 */
public class GraphUnfoldable {

    private HashMap<OWLClassExpression,Vertex> verticesMap;

    public GraphUnfoldable() {
        this.verticesMap = new HashMap<>();
    }
    
    public GraphUnfoldable(GraphUnfoldable unfoldable) {
        this.verticesMap = new HashMap<>(unfoldable.verticesMap);
    }


    public void addVertex( OWLClassExpression  ce) {
     if( verticesMap.get(ce) == null) {
        this.verticesMap.put(ce,new Vertex(ce));
     }
    }

    public void addEdge(OWLClassExpression from, OWLClassExpression to) {
        verticesMap.get(from).addNeighbour(verticesMap.get(to));
    }

    public boolean hasCycle() {
        for (Vertex vertex : verticesMap.values()) {
            if (!vertex.isVisited() && hasCycle(vertex)) {
                return true;
            }
        }
        return false;
    }

    public boolean hasCycle(Vertex sourceVertex) {
        sourceVertex.setBeingVisited(true);

        for (Vertex neighbour : sourceVertex.getAdjacencyList()) {
            if (neighbour.isBeingVisited()) {
                // backward edge exists
                return true;
            } else if (!neighbour.isVisited() && hasCycle(neighbour)) {
                return true;
            }
        }

        sourceVertex.setBeingVisited(false);
        sourceVertex.setVisited(true);
        return false;
    }
}