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
import org.jgrapht.alg.interfaces.MatchingAlgorithm;
import org.jgrapht.graph.DefaultUndirectedWeightedGraph;
import org.jgrapht.graph.DefaultWeightedEdge;
import org.junit.Test;

import java.util.*;

import static org.jgrapht.alg.matching.blossom.v5.Initializer.InitializationType.*;
import static org.jgrapht.alg.matching.blossom.v5.KolmogorovMinimumWeightPerfectMatching.EPS;
import static org.jgrapht.alg.matching.blossom.v5.KolmogorovMinimumWeightPerfectMatchingTest.checkMatchingAndDualSolution;
import static org.junit.Assert.*;

public class InitializerTest {

    private KolmogorovMinimumWeightPerfectMatching.Options fractionalOptions = new KolmogorovMinimumWeightPerfectMatching.Options(FRACTIONAL);

    /**
     * Tests greedy initialization
     */
    @Test
    public void testGreedyInitialization() {
        DefaultUndirectedWeightedGraph<Integer, DefaultWeightedEdge> graph = new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        DefaultWeightedEdge e12 = Graphs.addEdgeWithVertices(graph, 1, 2, 5);
        Initializer<Integer, DefaultWeightedEdge> initializer = new Initializer<>(graph);
        State<Integer, DefaultWeightedEdge> state = initializer.initialize(new KolmogorovMinimumWeightPerfectMatching.Options(GREEDY));

        Node node1 = state.vertexMap.get(1);
        Node node2 = state.vertexMap.get(2);

        Edge edge12 = state.edgeMap.get(e12);

        assertEquals(5, node1.dual + node2.dual, EPS);
        assertEquals(0, edge12.slack, EPS);

        assertTrue(node1.isOuter);
        assertTrue(node2.isOuter);

        assertFalse(node1.isTreeRoot);
        assertFalse(node2.isTreeRoot);

        assertEquals(2, state.nodeNum);
        assertEquals(1, state.edgeNum);
        assertEquals(0, state.treeNum);

        assertEquals(Collections.emptySet(), BlossomVDebugger.treeRoots(state));
        assertEquals(new HashSet<>(Collections.singletonList(edge12)), BlossomVDebugger.edgesOf(node1));
        assertEquals(new HashSet<>(Collections.singletonList(edge12)), BlossomVDebugger.edgesOf(node2));

        assertEquals(edge12, node1.matched);
        assertEquals(edge12, node2.matched);
    }

    /**
     * Tests simple initialization
     */
    @Test
    public void testSimpleInitialization() {
        Graph<Integer, DefaultWeightedEdge> graph = new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        DefaultWeightedEdge e12 = Graphs.addEdgeWithVertices(graph, 1, 2, 1);
        DefaultWeightedEdge e23 = Graphs.addEdgeWithVertices(graph, 2, 3, 2);
        DefaultWeightedEdge e25 = Graphs.addEdgeWithVertices(graph, 2, 5, 3);
        DefaultWeightedEdge e45 = Graphs.addEdgeWithVertices(graph, 4, 5, 4);
        DefaultWeightedEdge e56 = Graphs.addEdgeWithVertices(graph, 5, 6, 5);
        graph.addVertex(7);

        Initializer<Integer, DefaultWeightedEdge> initializer = new Initializer<>(graph);
        State<Integer, DefaultWeightedEdge> state = initializer.initialize(new KolmogorovMinimumWeightPerfectMatching.Options(NONE));

        assertEquals(7, state.nodeNum);
        assertEquals(7, state.treeNum);
        assertEquals(5, state.edgeNum);

        Node node1 = state.vertexMap.get(1);
        Node node2 = state.vertexMap.get(2);
        Node node3 = state.vertexMap.get(3);
        Node node4 = state.vertexMap.get(4);
        Node node5 = state.vertexMap.get(5);
        Node node6 = state.vertexMap.get(6);
        Node node7 = state.vertexMap.get(7);

        Tree tree1 = node1.tree;
        Tree tree2 = node2.tree;
        Tree tree3 = node3.tree;
        Tree tree4 = node4.tree;
        Tree tree5 = node5.tree;
        Tree tree6 = node6.tree;
        Tree tree7 = node7.tree;


        Edge edge12 = state.edgeMap.get(e12);
        Edge edge23 = state.edgeMap.get(e23);
        Edge edge25 = state.edgeMap.get(e25);
        Edge edge45 = state.edgeMap.get(e45);
        Edge edge56 = state.edgeMap.get(e56);

        assertEquals(0, node1.dual, EPS);
        assertEquals(0, node2.dual, EPS);
        assertEquals(0, node3.dual, EPS);
        assertEquals(0, node4.dual, EPS);
        assertEquals(0, node5.dual, EPS);
        assertEquals(0, node6.dual, EPS);
        assertEquals(0, node7.dual, EPS);

        assertTrue(node1.isOuter);
        assertTrue(node2.isOuter);
        assertTrue(node3.isOuter);
        assertTrue(node4.isOuter);
        assertTrue(node5.isOuter);
        assertTrue(node6.isOuter);
        assertTrue(node7.isOuter);

        assertTrue(node1.isTreeRoot);
        assertTrue(node2.isTreeRoot);
        assertTrue(node3.isTreeRoot);
        assertTrue(node4.isTreeRoot);
        assertTrue(node5.isTreeRoot);
        assertTrue(node6.isTreeRoot);
        assertTrue(node7.isTreeRoot);

        assertEquals(1, edge12.slack, EPS);
        assertEquals(2, edge23.slack, EPS);
        assertEquals(3, edge25.slack, EPS);
        assertEquals(4, edge45.slack, EPS);
        assertEquals(5, edge56.slack, EPS);

        Set<Node> actualRoots = BlossomVDebugger.treeRoots(state);
        Collection<Node> expectedRoots = state.vertexMap.values();
        assertEquals(expectedRoots.size(), actualRoots.size());
        assertTrue(actualRoots.containsAll(expectedRoots));

        assertEquals(Collections.singleton(edge12), BlossomVDebugger.edgesOf(node1));
        assertEquals(new HashSet<>(Arrays.asList(edge12, edge23, edge25)), BlossomVDebugger.edgesOf(node2));
        assertEquals(Collections.singleton(edge23), BlossomVDebugger.edgesOf(node3));
        assertEquals(Collections.singleton(edge45), BlossomVDebugger.edgesOf(node4));
        assertEquals(new HashSet<>(Arrays.asList(edge25, edge45, edge56)), BlossomVDebugger.edgesOf(node5));
        assertEquals(Collections.singleton(edge56), BlossomVDebugger.edgesOf(node6));
        assertEquals(new HashSet<>(), BlossomVDebugger.edgesOf(node7));

        assertEquals(0, BlossomVDebugger.treeEdgesOf(tree1).size());
        assertEquals(0, BlossomVDebugger.treeEdgesOf(tree2).size());
        assertEquals(0, BlossomVDebugger.treeEdgesOf(tree3).size());
        assertEquals(0, BlossomVDebugger.treeEdgesOf(tree4).size());
        assertEquals(0, BlossomVDebugger.treeEdgesOf(tree5).size());
        assertEquals(0, BlossomVDebugger.treeEdgesOf(tree6).size());
        assertEquals(0, BlossomVDebugger.treeEdgesOf(tree7).size());
    }

    /**
     * Tests fractional matching initialization on a bipartite graph with $V = {0,1,2}\cup{4,5,6}$
     */
    @Test
    public void testFractionalInitialization1() {
        Graph<Integer, DefaultWeightedEdge> graph = new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        int[][] edges = new int[][]{{0, 3, 8}, {0, 4, 3}, {0, 5, 3}, {1, 3, 2}, {1, 4, 5}, {1, 5, 2}, {2, 3, 7}, {2, 4, 3},
                {2, 5, 4}};
        for (int[] edge : edges) {
            Graphs.addEdgeWithVertices(graph, edge[0], edge[1], edge[2]);
        }
        KolmogorovMinimumWeightPerfectMatching<Integer, DefaultWeightedEdge> perfectMatching = new KolmogorovMinimumWeightPerfectMatching<>(graph, fractionalOptions);
        MatchingAlgorithm.Matching<Integer, DefaultWeightedEdge> matching = perfectMatching.getMatching();
        KolmogorovMinimumWeightPerfectMatching.Statistics statistics = perfectMatching.getStatistics();

        assertEquals(8, matching.getWeight(), EPS);
        assertEquals(0, statistics.growNum);
        assertEquals(0, statistics.shrinkNum);
        assertEquals(0, statistics.expandNum);
        assertTrue(perfectMatching.testOptimality());
        checkMatchingAndDualSolution(matching, perfectMatching.getDualSolution());
    }

    /**
     * Tests fractional matching initialization on a bipartite graph with $V = {0,1,2}\cup{4,5,6}$
     */
    @Test
    public void testFractionalInitialization2() {
        Graph<Integer, DefaultWeightedEdge> graph = new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        int[][] edges = new int[][]{{0, 3, 4}, {0, 4, 4}, {0, 5, 4}, {1, 3, 5}, {1, 4, 8}, {1, 5, 10}, {2, 3, 4}, {2, 4, 6},
                {2, 5, 5}};
        for (int[] edge : edges) {
            Graphs.addEdgeWithVertices(graph, edge[0], edge[1], edge[2]);
        }
        KolmogorovMinimumWeightPerfectMatching<Integer, DefaultWeightedEdge> perfectMatching = new KolmogorovMinimumWeightPerfectMatching<>(graph, fractionalOptions);
        MatchingAlgorithm.Matching<Integer, DefaultWeightedEdge> matching = perfectMatching.getMatching();
        KolmogorovMinimumWeightPerfectMatching.Statistics statistics = perfectMatching.getStatistics();

        assertEquals(14, matching.getWeight(), EPS);
        assertEquals(0, statistics.growNum);
        assertEquals(0, statistics.shrinkNum);
        assertEquals(0, statistics.expandNum);
        assertTrue(perfectMatching.testOptimality());
        checkMatchingAndDualSolution(matching, perfectMatching.getDualSolution());
    }

    /**
     * Tests fractional matching initialization on a bipartite graph with $V = {0,1,2,3}\cup{4,5,6,7}$
     */
    @Test
    public void testFractionalInitialization3() {
        Graph<Integer, DefaultWeightedEdge> graph = new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        int[][] edges = new int[][]{{0, 5, 6}, {0, 6, 8}, {1, 5, 5}, {1, 6, 5}, {1, 7, 3}, {2, 4, 2}, {2, 5, 1}, {2, 6, 8},
                {3, 5, 5}, {3, 7, 9}};
        for (int[] edge : edges) {
            Graphs.addEdgeWithVertices(graph, edge[0], edge[1], edge[2]);
        }
        KolmogorovMinimumWeightPerfectMatching<Integer, DefaultWeightedEdge> perfectMatching = new KolmogorovMinimumWeightPerfectMatching<>(graph, fractionalOptions);
        MatchingAlgorithm.Matching<Integer, DefaultWeightedEdge> matching = perfectMatching.getMatching();
        KolmogorovMinimumWeightPerfectMatching.Statistics statistics = perfectMatching.getStatistics();

        assertEquals(18, matching.getWeight(), EPS);
        assertEquals(0, statistics.growNum);
        assertEquals(0, statistics.shrinkNum);
        assertEquals(0, statistics.expandNum);
        assertTrue(perfectMatching.testOptimality());
        checkMatchingAndDualSolution(matching, perfectMatching.getDualSolution());
    }

    /**
     * Tests fractional matching initialization on a bipartite graph with $V = {0,1,2,3}\cup{4,5,6,7}$
     */
    @Test
    public void testFractionalInitialization4() {
        Graph<Integer, DefaultWeightedEdge> graph = new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        int[][] edges = new int[][]{{0, 5, 2}, {0, 6, 2}, {0, 7, 1}, {1, 4, 6}, {1, 7, 10}, {2, 4, 7}, {2, 6, 8}, {2, 7, 10},
                {3, 4, 5}, {3, 5, 9}};
        for (int[] edge : edges) {
            Graphs.addEdgeWithVertices(graph, edge[0], edge[1], edge[2]);
        }
        KolmogorovMinimumWeightPerfectMatching<Integer, DefaultWeightedEdge> perfectMatching = new KolmogorovMinimumWeightPerfectMatching<>(graph, fractionalOptions);
        MatchingAlgorithm.Matching<Integer, DefaultWeightedEdge> matching = perfectMatching.getMatching();
        KolmogorovMinimumWeightPerfectMatching.Statistics statistics = perfectMatching.getStatistics();

        assertEquals(24, matching.getWeight(), EPS);
        assertEquals(0, statistics.growNum);
        assertEquals(0, statistics.shrinkNum);
        assertEquals(0, statistics.expandNum);
        assertTrue(perfectMatching.testOptimality());
        checkMatchingAndDualSolution(matching, perfectMatching.getDualSolution());
    }

    /**
     * Tests fractional matching initialization on triangulation of 8 points
     */
    @Test
    public void testFractionalInitialization5() {
        Graph<Integer, DefaultWeightedEdge> graph = new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        int[][] edges = new int[][]{{1, 0, 2}, {1, 2, 5}, {0, 2, 4}, {1, 4, 5}, {2, 4, 2}, {1, 3, 2}, {1, 5, 4}, {3, 5, 3},
                {4, 5, 5}, {3, 6, 4}, {5, 6, 2}, {5, 7, 3}, {6, 7, 4}, {4, 7, 4}};
        for (int[] edge : edges) {
            Graphs.addEdgeWithVertices(graph, edge[0], edge[1], edge[2]);
        }
        KolmogorovMinimumWeightPerfectMatching<Integer, DefaultWeightedEdge> perfectMatching = new KolmogorovMinimumWeightPerfectMatching<>(graph, fractionalOptions);
        MatchingAlgorithm.Matching<Integer, DefaultWeightedEdge> matching = perfectMatching.getMatching();

        assertEquals(11, matching.getWeight(), EPS);
        assertTrue(perfectMatching.testOptimality());
        checkMatchingAndDualSolution(matching, perfectMatching.getDualSolution());
    }

    /**
     * Tests fractional matching initialization on triangulation of 8 points
     */
    @Test
    public void testFractionalInitialization6() {
        Graph<Integer, DefaultWeightedEdge> graph = new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        int[][] edges = new int[][]{{0, 1, 5}, {0, 2, 9}, {1, 2, 6}, {2, 3, 4}, {2, 4, 5}, {3, 4, 3}, {1, 4, 8}, {1, 5, 8},
                {0, 5, 11}, {4, 5, 7}, {4, 6, 3}, {5, 6, 5}, {6, 7, 3}, {5, 7, 6}, {4, 7, 6}, {3, 7, 9}};
        for (int[] edge : edges) {
            Graphs.addEdgeWithVertices(graph, edge[0], edge[1], edge[2]);
        }
        KolmogorovMinimumWeightPerfectMatching<Integer, DefaultWeightedEdge> perfectMatching = new KolmogorovMinimumWeightPerfectMatching<>(graph, fractionalOptions);
        MatchingAlgorithm.Matching<Integer, DefaultWeightedEdge> matching = perfectMatching.getMatching();

        assertEquals(18, matching.getWeight(), EPS);
        assertTrue(perfectMatching.testOptimality());
        checkMatchingAndDualSolution(matching, perfectMatching.getDualSolution());

    }

    /**
     * Tests fractional matching initialization on triangulation of 8 points
     */
    @Test
    public void testFractionalInitialization7() {
        Graph<Integer, DefaultWeightedEdge> graph = new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        int[][] edges = new int[][]{{0, 1, 2}, {0, 2, 8}, {1, 2, 7}, {0, 4, 8}, {1, 4, 7}, {2, 4, 6}, {2, 3, 9}, {2, 5, 6},
                {3, 5, 6}, {2, 6, 6}, {5, 6, 5}, {4, 6, 2}, {5, 7, 9}, {6, 7, 7}, {3, 7, 14}, {4, 7, 7}, {0, 7, 15}};
        for (int[] edge : edges) {
            Graphs.addEdgeWithVertices(graph, edge[0], edge[1], edge[2]);
        }
        KolmogorovMinimumWeightPerfectMatching<Integer, DefaultWeightedEdge> perfectMatching = new KolmogorovMinimumWeightPerfectMatching<>(graph, fractionalOptions);
        MatchingAlgorithm.Matching<Integer, DefaultWeightedEdge> matching = perfectMatching.getMatching();

        assertEquals(21, matching.getWeight(), EPS);
        assertTrue(perfectMatching.testOptimality());
        checkMatchingAndDualSolution(matching, perfectMatching.getDualSolution());
    }

    /**
     * Tests fractional matching initialization on triangulation of 8 points
     */
    @Test
    public void testFractionalInitialization8() {
        Graph<Integer, DefaultWeightedEdge> graph = new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        int[][] edges = new int[][]{{0, 1, 7}, {0, 2, 8}, {0, 3, 8}, {1, 3, 4}, {1, 5, 9}, {1, 6, 13}, {2, 4, 6}, {2, 3, 11},
                {3, 4, 10}, {3, 5, 6}, {4, 5, 8}, {4, 7, 7}, {5, 6, 4}, {5, 7, 4}, {6, 7, 1}};
        for (int[] edge : edges) {
            Graphs.addEdgeWithVertices(graph, edge[0], edge[1], edge[2]);
        }
        KolmogorovMinimumWeightPerfectMatching<Integer, DefaultWeightedEdge> perfectMatching = new KolmogorovMinimumWeightPerfectMatching<>(graph, fractionalOptions);
        MatchingAlgorithm.Matching<Integer, DefaultWeightedEdge> matching = perfectMatching.getMatching();

        assertEquals(20, matching.getWeight(), EPS);
        assertTrue(perfectMatching.testOptimality());
        checkMatchingAndDualSolution(matching, perfectMatching.getDualSolution());
    }

    /**
     * Tests fractional matching initialization on triangulation of 8 points
     */
    @Test
    public void testFractionalInitialization9() {
        Graph<Integer, DefaultWeightedEdge> graph = new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        int[][] edges = new int[][]{{0, 1, 4}, {0, 2, 4}, {0, 5, 14}, {1, 2, 3}, {1, 3, 1}, {1, 5, 11}, {2, 3, 4}, {2, 4, 4},
                {2, 7, 11}, {3, 4, 1}, {3, 5, 10}, {4, 5, 10}, {4, 6, 10}, {4, 7, 9}, {5, 6, 3}, {6, 7, 8}};
        for (int[] edge : edges) {
            Graphs.addEdgeWithVertices(graph, edge[0], edge[1], edge[2]);
        }
        KolmogorovMinimumWeightPerfectMatching<Integer, DefaultWeightedEdge> perfectMatching = new KolmogorovMinimumWeightPerfectMatching<>(graph, fractionalOptions);
        MatchingAlgorithm.Matching<Integer, DefaultWeightedEdge> matching = perfectMatching.getMatching();

        assertEquals(17, matching.getWeight(), EPS);
        assertTrue(perfectMatching.testOptimality());
        checkMatchingAndDualSolution(matching, perfectMatching.getDualSolution());

    }

}
