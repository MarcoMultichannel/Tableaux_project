
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
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
    public HashMap<OWLClassExpression, Vertex> verticesMap;

    public GraphUnfoldable() {
        this.verticesMap = new HashMap<>();
    }



    public GraphUnfoldable(GraphUnfoldable unfoldable) {
        this.verticesMap = new HashMap<>();
        for(OWLClassExpression ce: unfoldable.verticesMap.keySet()){
            addVertex(ce);
            for(Vertex adj:unfoldable.verticesMap.get(ce).getAdjacencyList()){
                OWLClassExpression target=adj.getLabel();
                addVertex(target);
                addEdge(ce, target);
            }
        }
    }





    public void addVertex(OWLClassExpression  ce) {
        if(verticesMap.get(ce) == null) {
            this.verticesMap.put(ce, new Vertex(ce));
        }
    }



    public void addEdge(OWLClassExpression from, OWLClassExpression to) {
        verticesMap.get(from).addNeighbour(verticesMap.get(to));
    }



    public boolean hasCycle() {
        for(Vertex vertex : verticesMap.values()) {
            if(!vertex.isVisited() && hasCycle(vertex)) {
                return true;
            }
        }
        return false;
    }



    public boolean hasCycle(Vertex sourceVertex) {
        sourceVertex.setBeingVisited(true);
        for(Vertex neighbour : sourceVertex.getAdjacencyList()) {
            if(neighbour.isBeingVisited()) {
                // backward edge exists
                return true;
            } else if(!neighbour.isVisited() && hasCycle(neighbour)) {
                return true;
            }
        }
        sourceVertex.setBeingVisited(false);
        sourceVertex.setVisited(true);
        return false;
    }


    public String printGraph(){
        String result="";
        for(OWLClassExpression ce:verticesMap.keySet()){
            List<Vertex> nodes=verticesMap.get(ce).getAdjacencyList();
            List<OWLClassExpression> labels=new ArrayList<>();
            for(Vertex v:nodes)
                labels.add(v.getLabel());
            if(!labels.isEmpty()) result=ce+" -> "+labels+"\n"+result;
        }
        return result;
    }

}