package org.jgrapht.alg.blossom;

import org.junit.Test;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import static org.jgrapht.alg.blossom.Node.Label.MINUS;
import static org.junit.Assert.*;

public class TreeTest {
    @Test
    public void testTreeNodeIterator() {
        Node node1 = new Node();
        Node node2 = new Node();
        Node node3 = new Node();
        Node node4 = new Node();
        Node node5 = new Node();
        Node node6 = new Node();
        Node node7 = new Node();

        Tree tree = new Tree(node1);
        node1.addChild(node7);
        node1.addChild(node6);
        node1.addChild(node2);
        node2.addChild(node5);
        node2.addChild(node4);
        node2.addChild(node3);

        Tree.TreeNodeIterator iterator = tree.treeNodeIterator();
        assertSame(iterator.next(), node1);
        assertSame(iterator.next(), node2);
        assertSame(iterator.next(), node3);
        assertSame(iterator.next(), node4);
        assertSame(iterator.next(), node5);
        assertSame(iterator.next(), node6);
        assertSame(iterator.next(), node7);
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
