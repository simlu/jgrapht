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
import org.jgrapht.Graphs;
import org.jgrapht.graph.DefaultUndirectedWeightedGraph;
import org.jgrapht.graph.DefaultWeightedEdge;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import static org.jgrapht.alg.matching.blossom.v5.Initializer.InitializationType.NONE;
import static org.jgrapht.alg.matching.blossom.v5.Node.Label.MINUS;
import static org.junit.Assert.*;

public class TreeTest {

    private KolmogorovMinimumWeightPerfectMatching.Options noneOptions = new KolmogorovMinimumWeightPerfectMatching.Options(NONE);

    @Test
    public void testTreeNodeIterator() {
        Graph<Integer, DefaultWeightedEdge> graph = new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        DefaultWeightedEdge e12 = Graphs.addEdgeWithVertices(graph, 1, 2, 0);
        DefaultWeightedEdge e23 = Graphs.addEdgeWithVertices(graph, 2, 3, 0);
        DefaultWeightedEdge e34 = Graphs.addEdgeWithVertices(graph, 3, 4, 0);
        DefaultWeightedEdge e45 = Graphs.addEdgeWithVertices(graph, 4, 5, 0);
        DefaultWeightedEdge e36 = Graphs.addEdgeWithVertices(graph, 3, 6, 0);
        DefaultWeightedEdge e67 = Graphs.addEdgeWithVertices(graph, 6, 7, 0);

        Initializer<Integer, DefaultWeightedEdge> initializer = new Initializer<>(graph);
        State<Integer, DefaultWeightedEdge> state = initializer.initialize(noneOptions);
        PrimalUpdater<Integer, DefaultWeightedEdge> primalUpdater = new PrimalUpdater<>(state);

        Node node1 = state.vertexMap.get(1);
        Node node2 = state.vertexMap.get(2);
        Node node3 = state.vertexMap.get(3);
        Node node4 = state.vertexMap.get(4);
        Node node5 = state.vertexMap.get(5);
        Node node6 = state.vertexMap.get(6);
        Node node7 = state.vertexMap.get(7);

        Edge edge12 = state.edgeMap.get(e12);
        Edge edge23 = state.edgeMap.get(e23);
        Edge edge34 = state.edgeMap.get(e34);
        Edge edge45 = state.edgeMap.get(e45);
        Edge edge36 = state.edgeMap.get(e36);
        Edge edge67 = state.edgeMap.get(e67);

        primalUpdater.augment(edge23);
        primalUpdater.augment(edge45);
        primalUpdater.augment(edge67);
        state.setCurrentEdges(node1.tree);
        primalUpdater.grow(edge12, true);

        int i = 0;
        Set<Node> actualNodes = new HashSet<>();
        for (Tree.TreeNodeIterator iterator = node1.tree.treeNodeIterator(); iterator.hasNext(); ) {
            i++;
            actualNodes.add(iterator.next());
        }
        assertEquals(7, i);
        assertEquals(new HashSet<>(Arrays.asList(node1, node2, node3, node4, node5, node6, node7)), actualNodes);
    }

    @Test
    public void testTreeEdgeIterator() {
        Node node1 = new Node();
        Node node2 = new Node();
        Node node3 = new Node();
        Node node4 = new Node();
        Node node5 = new Node();
        Tree tree1 = new Tree(node1);
        Tree tree2 = new Tree(node2);
        Tree tree3 = new Tree(node3);
        Tree tree4 = new Tree(node4);
        Tree tree5 = new Tree(node5);
        TreeEdge treeEdge1 = State.addTreeEdge(tree1, tree2);
        TreeEdge treeEdge2 = State.addTreeEdge(tree1, tree3);
        TreeEdge treeEdge3 = State.addTreeEdge(tree4, tree1);
        TreeEdge treeEdge4 = State.addTreeEdge(tree5, tree1);
        Set<TreeEdge> expectedOutEdges = new HashSet<>(Arrays.asList(treeEdge1, treeEdge2));
        Set<TreeEdge> expectedInEdges = new HashSet<>(Arrays.asList(treeEdge3, treeEdge4));
        Set<TreeEdge> actualOutEdges = new HashSet<>();
        Set<TreeEdge> actualInEdges = new HashSet<>();
        for (Tree.TreeEdgeIterator iterator = tree1.treeEdgeIterator(); iterator.hasNext(); ) {
            TreeEdge edge = iterator.next();
            int currentDir = iterator.getCurrentDirection();
            if (currentDir == 0) {
                actualOutEdges.add(edge);
            } else {
                actualInEdges.add(edge);
            }
            assertSame(tree1, edge.head[1 - currentDir]);
        }
        assertEquals(expectedOutEdges, actualOutEdges);
        assertEquals(expectedInEdges, actualInEdges);
    }

    @Test
    public void testAddMinusBlossom() {
        Node root = new Node();
        Tree tree = new Tree(root);

        Node blossom = new Node();
        blossom.label = MINUS;
        blossom.isOuter = true;
        blossom.isBlossom = true;
        tree.addMinusBlossom(blossom, blossom.dual);

        assertNotNull(blossom.fibNode);
        assertSame(blossom.fibNode.getData(), blossom);
    }

}
