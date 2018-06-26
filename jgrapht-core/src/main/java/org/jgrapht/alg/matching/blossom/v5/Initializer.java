/*
 * (C) Copyright 2018-2018, by Timofey Chudakov and Contributors.
 *
 * JGraphT : a free Java graph-theory library
 *
 * This program and the accompanying materials are dual-licensed under
 * either
 *
 * (a) the terms of the GNU Lesser General Public License version 2.1
 * as published by the Free Software Foundation, or (at your option) any
 * later version.
 *
 * or (per the licensee's choosing)
 *
 * (b) the terms of the Eclipse Public License v1.0 as published by
 * the Eclipse Foundation.
 */
package org.jgrapht.alg.matching.blossom.v5;

import org.jgrapht.Graph;
import org.jgrapht.util.FibonacciHeap;
import org.jgrapht.util.FibonacciHeapNode;

import java.util.HashMap;
import java.util.Map;

import static org.jgrapht.alg.matching.blossom.v5.Initializer.Action.*;
import static org.jgrapht.alg.matching.blossom.v5.KolmogorovMinimumWeightPerfectMatching.DEBUG;
import static org.jgrapht.alg.matching.blossom.v5.KolmogorovMinimumWeightPerfectMatching.INFINITY;
import static org.jgrapht.alg.matching.blossom.v5.Node.Label.MINUS;
import static org.jgrapht.alg.matching.blossom.v5.Node.Label.PLUS;

/**
 * Is used to start the Kolmogorov's Blossom V algorithm.
 * Performs initialization of the algorithm's internal data structures and finds an initial matching
 * according to the strategy specified in {@code options}
 *
 * @param <V> the graph vertex type
 * @param <E> the graph edge type
 * @author Timofey Chudakov
 * @see KolmogorovMinimumWeightPerfectMatching
 * @since June 2018
 */
class Initializer<V, E> {
    /**
     * The graph to search matching in
     */
    private final Graph<V, E> graph;
    /**
     * Number of nodes in the graph
     */
    private int nodeNum;
    /**
     * Number of edges in the graph
     */
    private int edgeNum;
    /**
     * An array of nodes that will be passes to the resulting state object
     */
    private Node[] nodes;
    /**
     * An array of edges that will be passes to the resulting state object
     */
    private Edge[] edges;
    /**
     * A mapping from initial graph's vertices to nodes that will be passes to the resulting state object
     */
    private Map<V, Node> vertexMap;
    /**
     * A mapping from the initial graph's edges to the internal edge representations that will be passes
     * to the resulting state object
     */
    private Map<E, Edge> edgeMap;
    private State<V, E> state;// TODO remove

    /**
     * Creates a new Initializer instance
     *
     * @param graph the graph to search matching in
     */
    public Initializer(Graph<V, E> graph) {
        this.graph = graph;
    }

    /**
     * Converts the generic graph representation into the data structure form convenient for the algorithm
     * and initializes the matching according to the strategy specified in {@code options}
     *
     * @param options the options of the algorithm
     * @return the state object with all necessary for the algorithm information
     */
    public State<V, E> initialize(KolmogorovMinimumWeightPerfectMatching.Options options) {
        switch (options.initializationType) {
            case NONE:
                return simpleInitialization(options);
            case GREEDY:
                return greedyInitialization(options);
            case FRACTIONAL:
                return fractionalMatchingInitialization(options);
        }
        return null;
    }

    private State<V, E> simpleInitialization(KolmogorovMinimumWeightPerfectMatching.Options options) {
        initGraph();
        for (Node node : nodes) {
            node.isOuter = true;
        }
        allocateTrees();
        return new State<>(graph, nodes, edges, nodeNum, edgeNum, graph.vertexSet().size(), vertexMap, edgeMap, options);
    }

    private State<V, E> greedyInitialization(KolmogorovMinimumWeightPerfectMatching.Options options) {
        initGraph();
        int treeNum = initGreedy();
        allocateTrees();
        return new State<>(graph, nodes, edges, nodeNum, edgeNum, treeNum, vertexMap, edgeMap, options);
    }

    private State<V, E> fractionalMatchingInitialization(KolmogorovMinimumWeightPerfectMatching.Options options) {
        initGraph();
        initGreedy();
        allocateTrees();
        state = new State<>(graph, nodes, edges, nodeNum, edgeNum, 0, vertexMap, edgeMap, options);
        int treeNum = initFractional();
        return new State<>(graph, nodes, edges, nodeNum, edgeNum, treeNum, vertexMap, edgeMap, options);
    }

    /**
     * Helper method to convert the generic graph representation into the form convenient for the algorithm
     */
    private void initGraph() {
        nodeNum = graph.vertexSet().size();
        nodes = new Node[nodeNum + 1];
        nodes[nodeNum] = new Node();  // auxiliary node to keep track of the first item in the linked list of tree roots
        edges = new Edge[graph.edgeSet().size()];
        vertexMap = new HashMap<>(nodeNum);
        edgeMap = new HashMap<>(edgeNum);
        int i = 0;
        // mapping nodes
        for (V vertex : graph.vertexSet()) {
            nodes[i] = new Node();
            vertexMap.put(vertex, nodes[i]);
            i++;
        }
        i = 0;
        // mapping edges
        for (E e : graph.edgeSet()) {
            Node source = vertexMap.get(graph.getEdgeSource(e));
            Node target = vertexMap.get(graph.getEdgeTarget(e));
            if (source != target) { // we avoid self-loops in order to support pseudographs
                edgeNum++;
                Edge edge = State.addEdge(source, target, graph.getEdgeWeight(e));
                edges[i] = edge;
                edgeMap.put(e, edge);
                i++;
            }
        }
    }

    /**
     * Method for greedy matching initialization.
     * <p>
     * For every node we choose an incident edge of minimum slack and set its dual to the half of this slack.
     * This maintains the nonnegativity of edge slacks. After that we go through all nodes again, greedily
     * increase their dual variables and match them if it is possible.
     *
     * @return the number of unmatched nodes, which equals to the number of trees
     */
    private int initGreedy() {
        int dir;
        Edge edge;
        // set all dual variables to infinity
        for (int i = 0; i < nodeNum; i++) {
            nodes[i].dual = INFINITY;
        }
        // set dual variables to the half of the minimum weight of the incident edges
        for (int i = 0; i < edgeNum; i++) {
            edge = edges[i];
            if (edge.head[0].dual > edge.slack) {
                edge.head[0].dual = edge.slack;
            }
            if (edge.head[1].dual > edge.slack) {
                edge.head[1].dual = edge.slack;
            }
        }
        // divide dual variables by to, this ensures nonnegativity of all slacks
        // decrease edge slacks accordingly
        for (int i = 0; i < edgeNum; i++) {
            edge = edges[i];
            Node source = edge.head[0];
            Node target = edge.head[1];
            if (!source.isOuter) {
                source.isOuter = true;
                source.dual /= 2;
            }
            edge.slack -= source.dual;
            if (!target.isOuter) {
                target.isOuter = true;
                target.dual /= 2;
            }
            edge.slack -= target.dual;
        }
        // go through all vertices, greedily increase their dual variables to the minimum slack of incident edges
        // if there exist a tight unmatched edge in the neighborhood, match it
        int treeNum = nodeNum;
        Node node;
        for (int i = 0; i < nodeNum; i++) {
            node = nodes[i];
            if (!node.isInfinityNode()) {
                double minSlack = INFINITY;
                // find the minimum slack of incident edges
                for (Node.IncidentEdgeIterator incidentEdgeIterator = node.incidentEdgesIterator(); incidentEdgeIterator.hasNext(); ) {
                    edge = incidentEdgeIterator.next();
                    if (edge.slack < minSlack) {
                        minSlack = edge.slack;
                    }
                }
                node.dual += minSlack;
                double resultMinSlack = minSlack;
                // subtract minimum slack from the slacks of all incident edges
                for (Node.IncidentEdgeIterator incidentEdgeIterator = node.incidentEdgesIterator(); incidentEdgeIterator.hasNext(); ) {
                    edge = incidentEdgeIterator.next();
                    dir = incidentEdgeIterator.getDir();
                    if (edge.slack <= resultMinSlack && node.isPlusNode() && edge.head[dir].isPlusNode()) {
                        node.label = Node.Label.INFINITY;
                        edge.head[dir].label = Node.Label.INFINITY;
                        node.matched = edge;
                        edge.head[dir].matched = edge;
                        treeNum -= 2;
                    }
                    edge.slack -= resultMinSlack;
                }
            }
        }

        return treeNum;
    }

    /**
<<<<<<< HEAD
     * Initializes an auxiliary graph by adding tree edges between trees and adding (+, +) cross-tree edges
     * and (+, inf) edges to the appropriate heaps
     */
    private void initAuxiliaryGraph() {
        Node opposite;
        Tree tree;
        Edge edge;
        TreeEdge treeEdge;
        // go through all tree roots and visit all incident edges of those roots.
        // if a (+, inf) edge is encountered => add it to the infinity heap
        // if a (+, +) edge is encountered and the opposite node hasn't been processed yet =>
        // add this edge to the heap of (+, +) cross-tree edges
        for (Node root = nodes[nodeNum].treeSiblingNext; root != null; root = root.treeSiblingNext) {
            tree = root.tree;
            for (Node.IncidentEdgeIterator edgeIterator = root.incidentEdgesIterator(); edgeIterator.hasNext(); ) {
                edge = edgeIterator.next();
                opposite = edge.head[edgeIterator.getDir()];
                if (opposite.isInfinityNode()) {
                    tree.addPlusInfinityEdge(edge, edge.slack);
                } else if (!opposite.isProcessed) {
                    if (opposite.tree.currentEdge == null) {
                        State.addTreeEdge(tree, opposite.tree);
                    }
                    opposite.tree.currentEdge.addPlusPlusEdge(edge, edge.slack);
                }
            }
            root.isProcessed = true;
            for (Tree.TreeEdgeIterator treeEdgeIterator = tree.treeEdgeIterator(); treeEdgeIterator.hasNext(); ) {
                treeEdge = treeEdgeIterator.next();
                treeEdge.head[treeEdgeIterator.getCurrentDirection()].currentEdge = null;
            }
        }
        // clearing isProcessed flags
        for (Node root = nodes[nodeNum].treeSiblingNext; root != null; root = root.treeSiblingNext) {
            root.isProcessed = false;
        }
    }

    /**
=======
>>>>>>> primal operations of fractional matching
     * Helper method for allocating trees. Initializes the doubly linked list of tree roots
     * via treeSiblingPrev and treeSiblingNext. The same mechanism is used for keeping track
     * of the children of a node in the tree. The node nodes[nodeNum] is used to quichly find
     * the first root in the linked list
     */
    private void allocateTrees() {
        Node lastRoot = nodes[nodeNum];
        for (int i = 0; i < nodeNum; i++) {
            Node node = nodes[i];
            if (node.isPlusNode()) {
                node.treeSiblingPrev = lastRoot;
                lastRoot.treeSiblingNext = node;
                lastRoot = node;
                new Tree(node);
            }
        }
        lastRoot.treeSiblingNext = null;
    }

    private int initFractional() {
        Node root;
        Node root2;
        Node root3 = null;
        Node varNode;
        int varDir;
        Edge varEdge;
        Node oppositeNode;
        Node.IncidentEdgeIterator iterator;

        if (DEBUG) {
            state.printMap();
            state.printState();
        }
        /*
         * For every free node u, which is adjacent to at least one "+" node in the current tree, we keep track
         * of an edge, that has minimum slack and connects node u and some "+" node in the current tree.
         */
        FibonacciHeap<Edge> fibHeap = new FibonacciHeap<>();

        for (root = nodes[nodeNum].treeSiblingNext; root != null; ) {
            root2 = root.treeSiblingNext;
            if (root2 != null) {
                root3 = root2.treeSiblingNext;
            }
            varNode = root;

            fibHeap.clear();

            double eps = 0;
            Action flag = NONE;
            Node branchRoot = varNode;
            Edge criticalEdge = null;
            double criticalEps = INFINITY;
            int criticalDir = -1;
            boolean primalOperation = false;

            /*
             * Growing a tree while is it possible. Main goal is to apply a primal operation. Therefore,
             * If we encounter a tight (+, +) cross-tree or in-tree edge => we won't be able to increase
             * dual objective function anymore (can't increase eps of the current tree)
             * => we go out of the loop, apply lazy dual changes to the current branch and perform an
             * augment or shrink operation.
             *
             * Tree is been growing in phases. Each phase starts with a new "branch" the reason to
             * start a new branch is that the tree can't be grown any further and there no primal opetation
             * can be applied. Therefore, we choose an edge of minimum slack from fibHeap, set the eps of the branch
             * so that this edge becomes tight
             */
            while (true) {
                varNode.isProcessed = true;
                varNode.dual -= eps; // applying lazy delta spreading

                if (!varNode.isTreeRoot) {
                    // applying lazy delta spreading to the matched "-" node
                    varNode.matched.getOpposite(varNode).dual += eps;
                }

                /*
                 * Processing edges incident to the current node.
                 */
                for (iterator = varNode.incidentEdgesIterator(); iterator.hasNext(); ) {
                    varEdge = iterator.next();
                    varDir = iterator.getDir();

                    varEdge.slack += eps; // applying lazy delta spreading
                    oppositeNode = varEdge.head[varDir];

                    if (oppositeNode.tree == root.tree) {
                        // opposite node is in the same tree
                        if (oppositeNode.isPlusNode()) {
                            double slack = varEdge.slack;
                            if (!oppositeNode.isProcessed) {
                                slack += eps;
                            }
                            if (2 * criticalEps > slack || criticalEdge == null) {
                                flag = Action.SHRINK;
                                criticalEps = slack / 2;
                                criticalEdge = varEdge;
                                criticalDir = varDir;
                                if (criticalEps <= eps) {
                                    // found a tight (+, +) in-tree edge to shrink => go out of the loop
                                    primalOperation = true;
                                    break;
                                }
                            }
                        }

                    } else if (oppositeNode.isPlusNode()) {
                        // varEdge is a (+, +) cross-tree edge
                        if (criticalEps >= varEdge.slack || criticalEdge == null) {
                            //
                            flag = AUGMENT;
                            criticalEps = varEdge.slack;
                            criticalEdge = varEdge;
                            criticalDir = varDir;
                            if (criticalEps <= eps) {
                                // found a tight (+, +) cross-tree edge to augment
                                primalOperation = true;
                                break;
                            }
                        }

                    } else {
                        // opposite node is an infinity node
                        handleInfinityEdgeInit(fibHeap, varEdge, varDir, eps, criticalEps);
                    }
                }
                if (primalOperation) {
                    // finish processing incident edges
                    while (iterator.hasNext()) {
                        iterator.next().slack += eps;
                    }
                    // exit the loop since we can perform shrink or augment operation
                    break;
                } else {
                    /*
                     * Moving currentNode to the next unprocessed "+" node in the tree
                     * growing the tree if it is possible. Starting a new branch if all nodes have
                     * been processed. Exit the loop, if the slack of fibHeap.min().getData() is >=
                     * than the slack of critical edge (in this case we can perform primal operation
                     * after updating the duals).
                     */
                    if (varNode.firstTreeChild != null) {
                        // moving to the next grandchild
                        varNode = varNode.firstTreeChild.getOppositeMatched();
                    } else {
                        // trying to find another unprocessed node
                        while (varNode != branchRoot && varNode.treeSiblingNext == null) {
                            varNode = varNode.getTreeParent();
                        }
                        if (varNode.isMinusNode()) {
                            // found an unprocessed node
                            varNode = varNode.treeSiblingNext.getOppositeMatched();
                        } else if (varNode == branchRoot) {
                            // we've processed all nodes in the current branch
                            Edge minSlackEdge = fibHeap.isEmpty() ? null : fibHeap.min().getData();
                            if (minSlackEdge == null || minSlackEdge.slack >= criticalEps) {
                                // can perform primal operation after updating duals
                                eps = criticalEps;
                                break;
                            } else {
                                // growing minimum slack edge
                                if(DEBUG){
                                    System.out.println("Growing an edge " + minSlackEdge);
                                }
                                int dirToFreeNode = minSlackEdge.head[0].isInfinityNode() ? 0 : 1;
                                varNode = minSlackEdge.head[1 - dirToFreeNode];
                                Node minusNode = minSlackEdge.head[dirToFreeNode];
                                removeFromHeap(fibHeap, minusNode);
                                minusNode.label = MINUS;
                                varNode.addChild(minusNode, minSlackEdge, true);
                                eps = minSlackEdge.slack;

                                Node plusNode = minusNode.getOppositeMatched();
                                if (plusNode.bestEdge != null) {
                                    removeFromHeap(fibHeap, plusNode);
                                }
                                plusNode.label = PLUS;
                                minusNode.addChild(plusNode, minusNode.matched, true);

                                //Starting a new branch
                                if(DEBUG){
                                    System.out.println("New branch root is " + plusNode);
                                }
                                varNode = branchRoot = plusNode;
                            }
                        }
                    }
                }
            }

            // updating duals
            updateDuals(root, eps);
            if (DEBUG) {
                state.printState();
            }

            // applying primal operation
            Node from = criticalEdge.head[1 - criticalDir];
            Node to = criticalEdge.head[criticalDir];
            if (flag == SHRINK) {
                shrinkInit(criticalEdge, root);
            } else {
                if(DEBUG){
                    System.out.println("Augmenting an edge " + criticalEdge);
                }
                augmentBranchInit(root, from, criticalEdge);
                if (to.isOuter) {
                    augmentBranchInit(to, to, criticalEdge);
                } else {
                    expandInit(to);
                }
            }


            root = root2;
            if (root != null && !root.isTreeRoot) {
                root = root3;
            }
        }

        return finish();
    }

    private int finish() {
        Node varNode;
        Node prevRoot = nodes[nodeNum];
        int treeNum = 0;
        for (int i = 0; i < nodeNum; i++) {
            varNode = nodes[i];
            varNode.firstTreeChild = varNode.treeSiblingNext = varNode.treeSiblingPrev = null;
            if (!varNode.isOuter) {
                expandInit(varNode);
                varNode.label = PLUS;
                new Tree(varNode);

                prevRoot.treeSiblingNext = varNode;
                varNode.treeSiblingPrev = prevRoot;
                prevRoot = varNode;
                treeNum++;
            }
        }
        return treeNum;
    }

    private void updateDuals(Node root, double eps) {
        Node varNode, oppositeNode;
        for (Tree.TreeNodeIterator treeNodeIterator = new Tree.TreeNodeIterator(root); treeNodeIterator.hasNext(); ) {
            varNode = treeNodeIterator.next();
            if (varNode.isProcessed) {
                varNode.dual += eps;
                if (!varNode.isTreeRoot) {
                    oppositeNode = varNode.getOppositeMatched();
                    oppositeNode.dual -= eps;
                    double delta = eps - varNode.matched.slack;
                    for (Node.IncidentEdgeIterator incidentEdgeIterator = oppositeNode.incidentEdgesIterator(); incidentEdgeIterator.hasNext(); ) {
                        incidentEdgeIterator.next().slack += delta;
                    }
                    oppositeNode.bestEdge = null;
                }
                // TODO find out whether the loop is needed
                varNode.isProcessed = false;
            } else if (varNode.isPlusNode() && !varNode.isTreeRoot) {
                varNode.getOppositeMatched().bestEdge = null;
            }
        }
    }

    private void handleInfinityEdgeInit(FibonacciHeap<Edge> fibHeap, Edge varEdge, int dir, double eps, double criticalEps) {
        Node varNode = varEdge.head[1 - dir];
        Node oppositeNode = varEdge.head[dir];
        if (varEdge.slack > eps) {
            // this edge isn't tight
            if (varEdge.slack < criticalEps) {
                if (oppositeNode.fibNode == null) {
                    addToHead(fibHeap, oppositeNode, varEdge);
                } else {
                    if (varEdge.slack < oppositeNode.bestEdge.slack) {
                        removeFromHeap(fibHeap, oppositeNode);
                        addToHead(fibHeap, oppositeNode, varEdge);
                    }
                }
            }
        } else {
            if(DEBUG){
                System.out.println("Growing an edge " + varEdge);
            }
            // this is a tight edge, can grow it
            if (oppositeNode.bestEdge != null) {
                removeFromHeap(fibHeap, oppositeNode);
            }
            oppositeNode.label = MINUS;
            varNode.addChild(oppositeNode, varEdge, true);

            Node plusNode = oppositeNode.matched.getOpposite(oppositeNode);
            if (plusNode.bestEdge != null) {
                removeFromHeap(fibHeap, plusNode);
            }
            plusNode.label = PLUS;
            oppositeNode.addChild(plusNode, plusNode.matched, true);
        }
    }

    private void addToHead(FibonacciHeap<Edge> heap, Node node, Edge edge) {
        FibonacciHeapNode<Edge> fibNode = new FibonacciHeapNode<>(edge);
        edge.fibNode = fibNode;
        node.bestEdge = edge;
        heap.insert(fibNode, edge.slack);
    }

    private void removeFromHeap(FibonacciHeap<Edge> heap, Node node) {
        heap.delete(node.bestEdge.fibNode);
        node.bestEdge.fibNode = null;
        node.bestEdge = null;
    }

    private void augmentBranchInit(Node root, Node branchStart, Edge augmentEdge) {
        for (Tree.TreeNodeIterator iterator = new Tree.TreeNodeIterator(root); iterator.hasNext(); ) {
            iterator.next().label = Node.Label.INFINITY;
        }

        Node plusNode = branchStart;
        Node minusNode = branchStart.getTreeParent();
        Edge matchedEdge = augmentEdge;
        while (minusNode != null) {
            plusNode.matched = matchedEdge;
            minusNode.matched = matchedEdge = minusNode.parentEdge;
            plusNode = minusNode.getTreeParent();
            minusNode = plusNode.getTreeParent();
        }
        root.matched = matchedEdge;

        root.isTreeRoot = false;
        root.treeSiblingPrev.treeSiblingNext = root.treeSiblingNext;
        if (root.treeSiblingNext != null) {
            root.treeSiblingNext.treeSiblingPrev = root.treeSiblingPrev;
        }
        // TODO: decrement treeNum
    }

    private void shrinkInit(Edge blossomFormingEdge, Node treeRoot) {
        for (Tree.TreeNodeIterator iterator = new Tree.TreeNodeIterator(treeRoot); iterator.hasNext(); ) {
            iterator.next().label = Node.Label.INFINITY;
        }
        Node blossomRoot = findBlossomRootInit(blossomFormingEdge);

        if (!blossomRoot.isTreeRoot) {
            Node minusNode = blossomRoot.getTreeParent();
            Edge prevEdge = minusNode.parentEdge;
            minusNode.matched = minusNode.parentEdge;
            Node plusNode = minusNode.getTreeParent();
            while (plusNode != treeRoot) {
                minusNode = plusNode.getTreeParent();
                plusNode.matched = prevEdge;
                minusNode.matched = prevEdge = minusNode.parentEdge;
                plusNode = minusNode.getTreeParent();
            }
            plusNode.matched = prevEdge;
        }

        Edge prevEdge = blossomFormingEdge;
        for (State.BlossomNodesIterator iterator = new State.BlossomNodesIterator(blossomRoot, blossomFormingEdge); iterator.hasNext(); ) {
            Node current = iterator.next();
            if (iterator.getCurrentDirection() == 0) {
                current.blossomSibling = prevEdge;
                prevEdge = current.parentEdge;
            } else {
                current.blossomSibling = current.parentEdge;
            }
        }

    }

    private void expandInit(Node blossomNode) {
        Node currentNode = blossomNode.blossomSibling.getOpposite(blossomNode);
        Edge prevEdge;

        blossomNode.isOuter = true;
        blossomNode.label = Node.Label.INFINITY;
        do {
            currentNode.matched = prevEdge = currentNode.blossomSibling;
            currentNode.isOuter = true;
            currentNode.label = Node.Label.INFINITY;
            currentNode = currentNode.blossomSibling.getOpposite(currentNode);

            currentNode.matched = prevEdge;
            currentNode.isOuter = true;
            currentNode.label = Node.Label.INFINITY;
            currentNode = currentNode.blossomSibling.getOpposite(currentNode);
        } while (currentNode != blossomNode);
    }

    private Node findBlossomRootInit(Edge blossomFormingEdge) {
        Node[] branches = new Node[]{blossomFormingEdge.head[0], blossomFormingEdge.head[1]};
        Node varNode;
        Node root;
        Node upperBound;
        int dir = 0;
        while (true) {
            if (!branches[dir].isOuter) {
                root = branches[dir];
                upperBound = branches[1 - dir];
                break;
            }
            branches[dir].isOuter = false;
            if (branches[dir].isTreeRoot) {
                upperBound = branches[dir];
                varNode = branches[1 - dir];
                while (varNode.isOuter) {
                    varNode.isOuter = false;
                    varNode = varNode.getTreeParent();
                    varNode.isOuter = false;
                    varNode = varNode.getTreeParent();
                }
                root = varNode;
                break;
            }
            varNode = branches[dir].getTreeParent();
            varNode.isOuter = false;
            branches[dir] = varNode.getTreeParent();
            dir = 1 - dir;
        }
        varNode = root;
        while (varNode != upperBound) {
            varNode = varNode.getTreeParent();
            varNode.isOuter = true;
            varNode = varNode.getTreeParent();
            varNode.isOuter = true;
        }
        return root;
    }

    /**
     * Enum for types of matching initialization
     */
    enum InitializationType {
        GREEDY, NONE, FRACTIONAL,
    }

    enum Action {
        NONE, SHRINK, AUGMENT,
    }
}
