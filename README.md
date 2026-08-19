a simple, verified Gallina implementation of DFS algorithms

## DFS

The main idea here is `Definition dfs_fold`, which folds over a directed unweighted graph (as `fold_left` folds over a list), in an order given by depth-first search.
Actually, it doesn't fold over the whole graph---just the subgraph reachable from the starting node.
It is given a nice specification (`dfs_fold_spec`) in terms of an inductive characterisation of DFS graph explorations.

The idea is that any algorithm which can be expressed as "do a DFS on the graph, and do X" should be relatively easy to write and verify using `dfs_fold` and `dfs_fold_spec`.

## Examples

I used `dfs_fold` to define and prove correct a few simple functions.
* `check_locally_tree` checks that the number of nodes is one more than the number of edges
* `get_reachable_nodes`
* `tree_of` returns a rose tree which is a spanning tree of the graph.

From `tree_of`, we get a constructive proof that a graph arises from a rose tree in the natural way iff it is a `tree` in the sense checked by `check_locally_tree`.

## Datatypes

This library axiomatizes a graph datatype (GraphInterface.v).
Graph implementations are required to be extensional but are otherwise arbitrary.
An implementation, in terms of coqutil maps, is provided in GraphImpl.v.

## Building

* Works with Rocq 9.1.1.
* You should do a recursive clone to get the submodule.
* Run `dune build` to build.
It should automatically generate a _RocqProject file.
* `dune clean` also exists.
