package org.jgrapht.alg.blossom;

import org.jgrapht.alg.util.Pair;
import org.jgrapht.util.FibonacciHeap;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import static org.jgrapht.alg.blossom.Node.Label.*;

class PrimalUpdater<V, E> {
    private State<V, E> state;

    public PrimalUpdater(State<V, E> state) {
        this.state = state;
    }

    public void grow(Edge growEdge, boolean manyGrows) {
        if (state.options.verbose) {
            System.out.println("Growing edge " + growEdge);
        }
        int dirToMinusNode = growEdge.head[0].isInfinityNode() ? 0 : 1;
        Node nodeInTheTree = growEdge.head[1 - dirToMinusNode];

        Node minusNode = growEdge.head[dirToMinusNode];
        Node plusNode = minusNode.matched.getOpposite(minusNode);

        minusNode.setLabel(MINUS);
        plusNode.setLabel(PLUS);

        minusNode.parentEdge = growEdge;
        plusNode.parentEdge = plusNode.matched;

        nodeInTheTree.addChild(minusNode, growEdge);
        minusNode.addChild(plusNode, minusNode.matched);


        processMinusNodeGrow(minusNode);
        processPlusNodeGrow(plusNode, manyGrows);

    }

    public void augment(Edge augmentEdge) {
        if (state.options.verbose) {
            System.out.println("Augmenting edge " + augmentEdge);
        }
        Node node;
        // augmenting trees on both sides
        for (int dir = 0; dir < 2; dir++) {
            node = augmentEdge.head[dir];
            augmentBranch(node, augmentEdge);
            node.matched = augmentEdge;
        }

    }

    public Node shrink(Edge blossomFormingEdge) {
        if (state.options.verbose) {
            System.out.println("Shrinking edge " + blossomFormingEdge);
        }
        Node blossomRoot = findBlossomRoot(blossomFormingEdge);
        Tree tree = blossomRoot.tree;
        Node blossom = new Node();
        // initializing blossom
        blossom.tree = tree;
        blossom.isBlossom = true;
        blossom.isOuter = true;
        blossom.isTreeRoot = blossomRoot.isTreeRoot;
        blossom.dual = -tree.eps;
        if (blossom.isTreeRoot) {
            tree.root = blossom;
        } else {
            blossom.matched = blossomRoot.matched;
        }

        // mark all blossom nodes
        for (State.BlossomNodesIterator iterator = state.blossomNodesIterator(blossomRoot, blossomFormingEdge); iterator.hasNext(); ) {
            iterator.next().isMarked = true;
        }

        updateTreeStructure(blossomRoot, blossomFormingEdge, blossom);

        setBlossomSiblings(blossomRoot, blossomFormingEdge);

        // resetting marks of blossom nodes
        blossomRoot.isMarked = false;
        blossomRoot.isProcessed = false;
        for (Node current = blossomRoot.blossomSibling.getOpposite(blossomRoot); current != blossomRoot; current = current.blossomSibling.getOpposite(current)) {
            current.isMarked = false;
            current.isProcessed = false;
        }
        blossomRoot.matched = null; // now new blossom is matched (used when finishing the matching
        state.statistics.shrinkNum++;
        state.blossomNum++;
        return blossom;
    }

    public void expand(Node blossom) {
        if (state.options.verbose) {
            System.out.println("Expanding blossom " + blossom);
        }
        Tree tree = blossom.tree;
        double eps = tree.eps;
        blossom.dual -= eps;
        blossom.tree.removeMinusBlossom(blossom);

        Edge parentEdge = blossom.parentEdge;
        int dirToBlossomFromParent = parentEdge.getDirTo(blossom);  // (parentEdge + dirToBlossom) points to blossom
        Node branchesEndpoint = parentEdge.headOriginal[dirToBlossomFromParent].getPenultimateBlossom();

        if (state.options.verbose) {
            State.printBlossonNodes(branchesEndpoint);
        }

        Edge matchedEdge = blossom.matched;
        int dirToBlossomFromMatched = matchedEdge.getDirTo(blossom);
        Node blossomRoot = matchedEdge.headOriginal[dirToBlossomFromMatched].getPenultimateBlossom();

        // marking blossom nodes
        Node current = blossomRoot;
        do {
            current.isMarked = true;
            current = current.blossomSibling.getOpposite(current);
        } while (current != blossomRoot);

        // moving all edge from blossom to penultimate children
        blossom.removeFromChildList();
        Set<Pair<Edge, Integer>> edges = blossom.getEdges();
        Edge edge;
        for (Pair<Edge, Integer> pair : edges) {
            edge = pair.getFirst();
            int dir = pair.getSecond();
            Node penultimateChild = edge.headOriginal[1 - dir].getPenultimateBlossom();
            state.moveEdge(blossom, penultimateChild, edge);
        }

        // reversing the circular blossomSibling references so that the first branch in even branch
        if (!forwardDirection(blossomRoot, branchesEndpoint)) {
            reverseBlossomSiblings(blossomRoot);
        }

        // changing the matching, the labeling and the dual information on the odd branch
        processOddBranchExpand(blossomRoot, branchesEndpoint, eps, tree);

        // changing the matching, the labeling and dual information on the even branch
        processEvenBranchExpand(blossomRoot, branchesEndpoint, blossom);

        // resetting marks of blossom nodes
        current = blossomRoot;
        do {
            current.isMarked = false;
            current.isProcessed = false;
            current = current.blossomSibling.getOpposite(current);
        } while (current != blossomRoot);
        blossom.isRemoved = true;
        state.statistics.expandNum++;
        state.removedNum++;
        if (state.removedNum > 4 * state.nodeNum) {
            freeRemoved();
        }
        if (state.options.verbose) {
            State.printTreeNodes(tree);
        }
    }

    private void processEvenBranchExpand(Node blossomRoot, Node branchesEndpoint, Node blossom) {
        Tree tree = blossom.tree;
        double eps = tree.eps;
        blossomRoot.matched = blossom.matched;
        blossomRoot.tree = tree;
        blossomRoot.addChild(blossom.matched.getOpposite(blossomRoot), blossomRoot.matched);

        Node current = blossomRoot;
        current.label = MINUS;
        current.isOuter = true;
        current.parentEdge = blossom.parentEdge;
        Edge prevMatched;
        Node prevNode = current;
        while (current != branchesEndpoint) {
            // processing "+" node
            current = current.blossomSibling.getOpposite(current);
            current.label = PLUS;
            current.isOuter = true;
            current.tree = tree;
            current.matched = prevMatched = current.blossomSibling;
            current.addChild(prevNode, prevNode.blossomSibling);
            prevNode = current;

            // processing "-" node
            current = current.blossomSibling.getOpposite(current);
            current.label = MINUS;
            current.isOuter = true;
            current.tree = tree;
            current.matched = prevMatched;
            current.addChild(prevNode, prevNode.blossomSibling);
            prevNode = current;
        }
        blossom.parentEdge.getOpposite(branchesEndpoint).addChild(branchesEndpoint, blossom.parentEdge);

        current = blossomRoot;
        processMinusNodeExpand(current, eps);
        while (current != branchesEndpoint) {
            current = current.blossomSibling.getOpposite(current);
            processPlusNodeExpand(current, eps);
            current.isProcessed = true;

            current = current.blossomSibling.getOpposite(current);
            processMinusNodeExpand(current, eps);
        }
    }

    private void processOddBranchExpand(Node blossomRoot, Node branchesEndpoint, double eps, Tree tree) {
        Node current = branchesEndpoint.blossomSibling.getOpposite(branchesEndpoint);
        Edge prevMatched;
        while (current != blossomRoot) {
            current.label = INFTY;
            current.isOuter = true;
            current.tree = null;
            current.matched = prevMatched = current.blossomSibling;
            processInfinityNodeExpand(current, eps, tree);
            current = current.blossomSibling.getOpposite(current);

            current.label = INFTY;
            current.isOuter = true;
            current.tree = null;
            current.matched = prevMatched;
            processInfinityNodeExpand(current, eps, tree);
            current = current.blossomSibling.getOpposite(current);
        }
    }

    private void processPlusNodeExpand(Node plusNode, double eps) {
        plusNode.dual -= eps; // applying lazy delta spreading
        Edge edge;
        for (Node.AdjacentEdgeIterator iterator = plusNode.adjacentEdgesIterator(); iterator.hasNext(); ) {
            edge = iterator.next();
            Node opposite = edge.head[iterator.getDir()];
            if (opposite.isMarked && opposite.isPlusNode()) {
                // this is an inner (+, +) edge
                if (!opposite.isProcessed) {
                    // we encounter this edge for the first time
                    edge.slack += 2 * eps;
                }
            } else if (!opposite.isMarked) {
                // this is boundary edge
                edge.slack += 2 * eps; // the endpoint changes its label to "+"
            } else if (!opposite.isMinusNode()) {
                // this edge is inner edge between even and odd branches or it is an inner (+, +) edge
                edge.slack += eps;
            }
            if (opposite.isPlusNode()) {
                if (opposite.tree == plusNode.tree) {
                    // this edge becomes a (+, +) in-tree edge
                    if (!opposite.isProcessed) {
                        // if opposite.isProcessed = true => this is an inner (+, +) edge => its slack has been
                        // updated already and it has been added to the plus-plus edges heap already
                        plusNode.tree.addPlusPlusEdge(edge, edge.slack);
                    }
                } else {
                    // opposite is from another tree since it's label is "+"
                    opposite.tree.currentEdge.removeFromCurrentMinusPlusHeap(edge, opposite.tree.currentDirection);
                    opposite.tree.currentEdge.addPlusPlusEdge(edge, edge.slack);
                }
            } else if (opposite.isMinusNode()) {
                if (opposite.tree != plusNode.tree) {
                    // this edge becomes a (+, -) cross-tree edge
                    if (opposite.tree.currentEdge == null) {
                        State.addTreeEdge(plusNode.tree, opposite.tree);
                    }
                    opposite.tree.currentEdge.addToCurrentPlusMinusHeap(edge, edge.slack, opposite.tree.currentDirection);
                }
            } else {
                // this is either an inner edge, that becomes a (+, inf) edge, or it is a former (-, +) edge,
                // that also becomes a (+, inf) edge
                plusNode.tree.addPlusInfinityEdge(edge, edge.slack); // updating edge's key
            }
        }
    }

    private void processMinusNodeExpand(Node minusNode, double eps) {
        minusNode.dual += eps;
        if (minusNode.isBlossom) {
            minusNode.tree.addMinusBlossom(minusNode, minusNode.dual);
        }
        Edge edge;
        Node opposite;
        for (Node.AdjacentEdgeIterator iterator = minusNode.adjacentEdgesIterator(); iterator.hasNext(); ) {
            edge = iterator.next();
            opposite = edge.head[iterator.getDir()];
            if (opposite.isMarked && !opposite.isPlusNode()) {
                // this is an (-, inf) inner edge
                edge.slack -= eps;
            }
        }
    }

    private void processInfinityNodeExpand(Node infinityNode, double eps, Tree tree) {
        Edge edge;
        for (Node.AdjacentEdgeIterator iterator = infinityNode.adjacentEdgesIterator(); iterator.hasNext(); ) {
            edge = iterator.next();
            Node opposite = edge.head[iterator.getDir()];
            if (!opposite.isMarked) {
                edge.slack += eps; // since edge's label changes to inf and this is a boundary edge
                if (opposite.isPlusNode()) {
                    // if this node is marked => it's a blossom node => this edge has been processed already
                    if (opposite.tree != tree) {
                        opposite.tree.currentEdge.removeFromCurrentMinusPlusHeap(edge, opposite.tree.currentDirection);
                    }
                    opposite.tree.addPlusInfinityEdge(edge, edge.slack);
                }
            }
        }
    }

    private void processMinusNodeGrow(Node minusNode) {
        // maintaining heap of "-" blossoms
        double eps = minusNode.tree.eps;
        minusNode.dual += eps;
        Edge edge;
        int dir;
        // maintaining heap of "-" blossoms
        if (minusNode.isBlossom) {
            minusNode.tree.addMinusBlossom(minusNode, minusNode.dual);
        }
        // maintaining minus-plus edges in the minus-plus heaps in the tree edges
        for (Node.AdjacentEdgeIterator iterator = minusNode.adjacentEdgesIterator(); iterator.hasNext(); ) {
            edge = iterator.next();
            dir = iterator.getDir();
            Node opposite = edge.head[dir];
            edge.slack -= eps;
            if (opposite.isPlusNode()) {
                if (opposite.tree != minusNode.tree) {
                    // encountered (-,+) cross-tree edge
                    if (opposite.tree.currentEdge == null) {
                        State.addTreeEdge(minusNode.tree, opposite.tree);
                    }
                    opposite.tree.removePlusInfinityEdge(edge);
                    opposite.tree.currentEdge.addToCurrentMinusPlusHeap(edge, edge.slack, opposite.tree.currentDirection);
                } else if (opposite != minusNode.matched.getOpposite(minusNode)) {
                    // encountered a former (+, inf) edge
                    minusNode.tree.removePlusInfinityEdge(edge);
                }
            }
        }
    }

    private void processPlusNodeGrow(Node plusNode, boolean manyGrows) {
        double eps = plusNode.tree.eps;
        plusNode.dual -= eps;
        Edge edge;
        int dir;
        List<Edge> growEdges = new LinkedList<>();
        for (Node.AdjacentEdgeIterator iterator = plusNode.adjacentEdgesIterator(); iterator.hasNext(); ) {
            edge = iterator.next();
            dir = iterator.getDir();
            Node opposite = edge.head[dir];
            // maintaining heap of plus-infinity edges
            edge.slack += eps;
            if (opposite.isPlusNode()) {
                // this is a (+,+) edge
                if (opposite.tree == plusNode.tree) {
                    // this is blossom-forming edge
                    plusNode.tree.removePlusInfinityEdge(edge);
                    plusNode.tree.addPlusPlusEdge(edge, edge.slack);
                } else {
                    // this is plus-plus edge to another trees
                    if (opposite.tree.currentEdge == null) {
                        State.addTreeEdge(plusNode.tree, opposite.tree);
                    }
                    opposite.tree.removePlusInfinityEdge(edge);
                    opposite.tree.currentEdge.addPlusPlusEdge(edge, edge.slack);
                }
            } else if (opposite.isMinusNode()) {
                // this is a (+,-) edge
                if (opposite.tree != plusNode.tree) {
                    // this is (+,-) edge to another trees
                    if (opposite.tree.currentEdge == null) {
                        State.addTreeEdge(plusNode.tree, opposite.tree);
                    }
                    opposite.tree.currentEdge.addToCurrentPlusMinusHeap(edge, edge.slack, opposite.tree.currentDirection);
                }
            } else if (opposite.isInfinityNode()) {
                plusNode.tree.addPlusInfinityEdge(edge, edge.slack);
                if (edge.slack <= eps && manyGrows) {
                    growEdges.add(edge);
                }
            }
        }
        for (Edge growEdge : growEdges) {
            // it can be the case when this edge can't be grown because opposite vertex is already added
            // to this tree via some other grow operation
            if (growEdge.getOpposite(plusNode).isInfinityNode()) {
                grow(growEdge, false);
            }
        }
        state.statistics.growNum++;
    }

    private void augmentBranch(Node firstNode, Edge augmentEdge) {
        Tree tree = firstNode.tree;
        double eps = tree.eps;
        Node root = tree.root;
        TreeEdge treeEdge;
        Edge edge;
        Node node;
        int dir;

        // setting currentEdge and currentDirection of all opposite trees connected via treeEdge
        state.setCurrentEdges(tree);

        // applying tree.eps to all tree nodes and updating slacks of all incident edges
        for (Tree.TreeNodeIterator treeNodeIterator = tree.treeNodeIterator(); treeNodeIterator.hasNext(); ) {
            node = treeNodeIterator.next();
            // applying lazy delta spreading
            if (node.isPlusNode()) {
                node.dual += eps;
            } else {
                node.dual -= eps;
            }
            for (Node.AdjacentEdgeIterator adjacentEdgeIterator = node.adjacentEdgesIterator(); adjacentEdgeIterator.hasNext(); ) {
                edge = adjacentEdgeIterator.next();
                dir = adjacentEdgeIterator.getDir();
                Node opposite = edge.head[dir];
                Tree oppositeTree = opposite.tree;
                if (node.isPlusNode()) {
                    edge.slack -= eps;
                    if (oppositeTree != null && oppositeTree != tree) {
                        // if this edge is a cross-tree edge
                        treeEdge = oppositeTree.currentEdge;
                        int currentDir = oppositeTree.currentDirection;
                        if (opposite.isPlusNode()) {
                            // this is a (+,+) cross-tree edge
                            treeEdge.removeFromPlusPlusHeap(edge);
                            oppositeTree.addPlusInfinityEdge(edge, edge.slack);
                        } else if (opposite.isMinusNode()) {
                            // this is a (+,-) cross-tree edge
                            treeEdge.removeFromCurrentPlusMinusHeap(edge, currentDir);
                        }
                    }
                } else {
                    // current node is a "-" node
                    if (oppositeTree != null && oppositeTree != tree && opposite.isPlusNode()) {
                        // this is a (-,+) cross-tree edge
                        treeEdge = oppositeTree.currentEdge;
                        int currentDir = oppositeTree.currentDirection;
                        treeEdge.removeFromCurrentMinusPlusHeap(edge, currentDir);
                        oppositeTree.addPlusInfinityEdge(edge, edge.slack + eps);
                    }
                    edge.slack += eps;

                }
            }
            node.setLabel(Node.Label.INFTY);
        }

        // adding all elements from the (-,+) and (+,+) heaps to (+, inf) heaps of the opposite trees and
        // deleting tree edges
        for (Tree.TreeEdgeIterator treeEdgeIterator = tree.treeEdgeIterator(); treeEdgeIterator.hasNext(); ) {
            treeEdge = treeEdgeIterator.next();
            dir = treeEdgeIterator.getCurrentDirection();
            Tree opposite = treeEdge.head[dir];
            opposite.currentEdge = null;

            opposite.plusInfinityEdges = FibonacciHeap.union(opposite.plusInfinityEdges, treeEdge.plusPlusEdges);
            opposite.plusInfinityEdges = FibonacciHeap.union(opposite.plusInfinityEdges, treeEdge.getCurrentMinusPlusHeap(dir));
            treeEdge.removeFromTreeEdgeList();
        }

        // updating matching

        Edge matchedEdge = augmentEdge;
        Node plusNode = firstNode;
        Node minusNode = plusNode.getTreeParent();
        while (minusNode != null) {
            plusNode.matched = matchedEdge;
            matchedEdge = minusNode.parentEdge;
            minusNode.matched = matchedEdge;
            plusNode = minusNode.getTreeParent();
            minusNode = plusNode.getTreeParent();
        }
        root.matched = matchedEdge;

        // removing root from the linked list of roots;
        root.treeSiblingPrev.treeSiblingNext = root.treeSiblingNext;
        if (root.treeSiblingNext != null) {
            root.treeSiblingNext.treeSiblingPrev = root.treeSiblingPrev;
        }
        root.isTreeRoot = false;
        Set<Node> treeNodes = new HashSet<>();
        for (Tree.TreeNodeIterator iterator = firstNode.tree.treeNodeIterator(); iterator.hasNext(); ) {
            treeNodes.add(iterator.next());
        }
        for (Node treeNode : treeNodes) {
            treeNode.tree = null;
            treeNode.firstTreeChild = null;
            treeNode.treeSiblingPrev = null;
            treeNode.treeSiblingNext = null;
        }

        state.treeNum--;
    }

    Node findBlossomRoot(Edge edge) {
        Node root;
        Node upperBound;
        Node varNode;
        Node[] endPoints = new Node[2];
        endPoints[0] = edge.head[0];
        endPoints[1] = edge.head[1];
        int branch = 0;
        while (true) {
            if (endPoints[branch].isMarked) {
                root = endPoints[branch];
                upperBound = endPoints[1 - branch];
                break;
            }
            endPoints[branch].isMarked = true;
            if (endPoints[branch].isTreeRoot) {
                upperBound = endPoints[branch];
                varNode = endPoints[1 - branch];
                while (!varNode.isMarked) {
                    varNode = varNode.getTreeGrandparent();
                }
                root = varNode;
                break;
            }
            endPoints[branch] = endPoints[branch].getTreeGrandparent();
            branch = 1 - branch;
        }
        varNode = root;
        while (varNode != upperBound) {
            varNode = varNode.getTreeGrandparent();
            varNode.isMarked = false;
        }
        clearIsMarkedAndSetIsOuter(root, edge.head[0]);
        clearIsMarkedAndSetIsOuter(root, edge.head[1]);

        return root;
    }

    private void clearIsMarkedAndSetIsOuter(Node root, Node start) {
        while (start != root) {
            start.isMarked = false;
            start.isOuter = false;
            start = start.getTreeParent();
            start.isOuter = false;
            start = start.getTreeParent();
        }
        root.isOuter = false;
        root.isMarked = false;
    }

    private void setBlossomSiblings(Node blossomRoot, Edge blossomFormingEdge) {
        // setting blossom sibling nodes
        Edge prevEdge = blossomFormingEdge;
        for (State.BlossomNodesIterator iterator = state.blossomNodesIterator(blossomRoot, blossomFormingEdge); iterator.hasNext(); ) {
            Node current = iterator.next();
            if (iterator.getCurrentDirection() == 0) {
                current.blossomSibling = prevEdge;
                prevEdge = current.parentEdge;
            } else {
                current.blossomSibling = current.parentEdge;
            }
        }
    }

    private void updateTreeStructure(Node blossomRoot, Edge blossomFormingEdge, Node blossom) {
        // going through every vertex in the blossom and moving its child list to
        // blossom child list
        Node varNode;
        Tree tree = blossomRoot.tree;
        double eps = tree.eps;
        // handling all blossom nodes except for the blossom root
        for (State.BlossomNodesIterator iterator = state.blossomNodesIterator(blossomRoot, blossomFormingEdge); iterator.hasNext(); ) {
            varNode = iterator.next();
            if (varNode != blossomRoot) {
                if (varNode.isPlusNode()) {
                    // substituting varNode with the blossom in the tree structure
                    varNode.removeFromChildList();
                    varNode.moveChildrenTo(blossom);
                    shrinkPlusNode(varNode, blossom);
                    varNode.isProcessed = true;
                } else {
                    if (varNode.isBlossom) {
                        tree.removeMinusBlossom(varNode);
                    }
                    varNode.removeFromChildList();
                    shrinkMinusNode(varNode, blossom);
                }
            }
            varNode.blossomGrandparent = varNode.blossomParent = blossom;
        }
        // substituting varNode with the blossom in the tree structure
        blossomRoot.removeFromChildList();
        if (!blossomRoot.isTreeRoot) {
            blossomRoot.getTreeParent().addChild(blossom, blossomRoot.parentEdge);
        } else {
            blossom.treeSiblingNext = blossomRoot.treeSiblingNext;
            blossom.treeSiblingPrev = blossomRoot.treeSiblingPrev;
            blossomRoot.treeSiblingPrev.treeSiblingNext = blossom;
            if (blossomRoot.treeSiblingNext != null) {
                blossomRoot.treeSiblingNext.treeSiblingPrev = blossom;
            }
        }
        blossomRoot.moveChildrenTo(blossom);
        shrinkPlusNode(blossomRoot, blossom);
        blossomRoot.isTreeRoot = false;
    }

    private void shrinkPlusNode(Node node, Node blossom) {
        Tree tree = node.tree;
        double eps = tree.eps;
        node.dual += eps;

        Set<Pair<Edge, Integer>> edges = node.getEdges();
        for (Pair<Edge, Integer> pair : edges) {
            Edge edge = pair.getFirst();
            int direction = pair.getSecond();
            Node opposite = edge.head[direction];

            if (!opposite.isMarked) {
                // opposite isn't a node inside the blossom
                state.moveEdge(node, blossom, edge);
                if (opposite.tree == tree) {
                    // edge to the node from the same tree
                } else if (opposite.tree != null) {
                    // cross-tree edge

                }
            } else if (opposite.isPlusNode()) {
                // inner edge, subtract eps only in the case the opposite node is a "+" node
                if (!opposite.isProcessed) {
                    // remove this edge when it is encountered for the first time
                    tree.removePlusPlusEdge(edge);
                }
                edge.slack -= eps;
            }
        }

    }

    private void shrinkMinusNode(Node node, Node blossom) {
        Tree tree = node.tree;
        double eps = tree.eps;
        node.dual -= eps;

        Set<Pair<Edge, Integer>> edges = node.getEdges();
        for (Pair<Edge, Integer> pair : edges) {
            Edge edge = pair.getFirst();
            int direction = pair.getSecond();
            Node opposite = edge.head[direction];
            Tree oppositeTree = opposite.tree;

            if (!opposite.isMarked) {
                // opposite isn't a node inside the blossom
                state.moveEdge(node, blossom, edge);
                edge.slack += 2 * eps;
                if (opposite.tree == tree) {
                    // edge to the node from the same tree, need only to add it to "++" heap if opposite is "+" node
                    if (opposite.isPlusNode()) {
                        tree.addPlusPlusEdge(edge, edge.slack);
                    }
                } else {
                    // cross-tree edge or infinity edge
                    if (opposite.isPlusNode()) {
                        oppositeTree.currentEdge.removeFromCurrentMinusPlusHeap(edge, oppositeTree.currentDirection);
                        oppositeTree.currentEdge.addPlusPlusEdge(edge, edge.slack);
                    } else if (opposite.isMinusNode()) {
                        if (oppositeTree.currentEdge == null) {
                            State.addTreeEdge(tree, oppositeTree);
                        }
                        oppositeTree.currentEdge.addToCurrentPlusMinusHeap(edge, edge.slack, oppositeTree.currentDirection);
                    } else {
                        tree.addPlusInfinityEdge(edge, edge.slack);
                    }

                }
            } else if (opposite.isMinusNode()) {
                // this is an inner edge
                edge.slack += eps;
            }
        }
    }

    private void reverseBlossomSiblings(Node blossomNode) {
        Edge prevEdge = blossomNode.blossomSibling;
        Node current = blossomNode;
        Node tmp;
        Edge tmpEdge;
        do {
            current = prevEdge.getOpposite(current);
            tmpEdge = prevEdge;
            prevEdge = current.blossomSibling;
            current.blossomSibling = tmpEdge;
        } while (current != blossomNode);
    }

    private boolean forwardDirection(Node blossomRoot, Node stopNode) {
        int hops = 0;
        Node current = blossomRoot;
        while (current != stopNode) {
            ++hops;
            current = current.blossomSibling.getOpposite(current);
        }
        return (hops & 1) == 0;
    }

    private void freeRemoved() {
        Node[] nodes = state.nodes;
        Node iterNode;
        Node jumpNode;
        for (int i = 0; i < state.nodeNum; i++) {
            iterNode = nodes[i];
            for (jumpNode = iterNode; !jumpNode.isOuter && !jumpNode.isMarked; jumpNode = jumpNode.blossomParent) {
                jumpNode.isMarked = true;
                if (jumpNode.blossomGrandparent.isRemoved) {
                    jumpNode.blossomGrandparent = jumpNode.blossomParent;
                }
            }
        }
        for (int i = 0; i < state.nodeNum; i++) {
            iterNode = nodes[i];
            for (jumpNode = iterNode; !jumpNode.isOuter && jumpNode.isMarked; jumpNode = jumpNode.blossomParent) {
                jumpNode.isMarked = false;
            }
        }
    }
}
