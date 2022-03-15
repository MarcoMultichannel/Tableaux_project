
import java.util.ArrayList;
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
public class Vertex {

    private OWLClassExpression label;

    private boolean visited;

    private boolean beingVisited;

    private List<Vertex> adjacencyList;

    public Vertex(OWLClassExpression label) {
        this.label = label;
        this.adjacencyList = new ArrayList<>();
    }

    public OWLClassExpression getLabel() {
        return label;
    }

    public void setLabel(OWLClassExpression label) {
        this.label = label;
    }

    public boolean isVisited() {
        return visited;
    }

    public void setVisited(boolean visited) {
        this.visited = visited;
    }

    public boolean isBeingVisited() {
        return beingVisited;
    }

    public void setBeingVisited(boolean beingVisited) {
        this.beingVisited = beingVisited;
    }

    public List<Vertex> getAdjacencyList() {
        return adjacencyList;
    }

    public void setAdjacencyList(List<Vertex> adjacencyList) {
        this.adjacencyList = adjacencyList;
    }

    public void addNeighbour(Vertex adjacent) {
        this.adjacencyList.add(adjacent);
    }
}