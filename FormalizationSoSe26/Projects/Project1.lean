import Mathlib.Combinatorics.Digraph.Orientation

/-!
# Basic graph theory exercises in Lean 4

This worksheet is about reading graph-theory definitions in mathlib
and then proving small lemmas from those definitions.

The main object below is `SimpleGraph V`.

Mathematically, a simple undirected graph on a vertex type `V`
is represented by an adjacency relation

  G.Adj : V → V → Prop

with two built-in properties:

1. Symmetry:
   if `G.Adj u v`, then `G.Adj v u`.

2. Irreflexivity / looplessness:
   no vertex is adjacent to itself.

In Lean, these are not just informal facts. They are part of the API,
and there are named lemmas for using them.

Useful things to inspect before starting:
-/

#check SimpleGraph
#check SimpleGraph.Adj
#check SimpleGraph.adj_symm
#check SimpleGraph.ne_of_adj
#check SimpleGraph.compl_adj
#check SimpleGraph.sup_adj

/-
Some notation:

* `G.Adj u v` means that `u` and `v` are adjacent in `G`.
* `Gᶜ` is the complement graph.
* `G ⊔ H` is the graph union / supremum.
* `u ≠ v` says that the two vertices are distinct.

For comparison, mathlib also has directed graphs:
-/

#check Digraph
#check Digraph.Adj
#check Digraph.toSimpleGraphInclusive
#check Digraph.toSimpleGraphStrict

/-
A `Digraph V` does not automatically reverse edges.
So from `D.Adj u v`, you should not expect to prove `D.Adj v u`
unless you have an extra hypothesis.
-/

section DirectedVsUndirected

/-!
A tiny directed graph example.

There is an edge from `false` to `true`,
but there is no edge from `true` to `false`.
This is impossible behavior for `SimpleGraph`, but normal for `Digraph`.
-/

def oneWayBoolDigraph : Digraph Bool :=
  { Adj := fun x y => x = false ∧ y = true }

theorem oneWay_forward :
    oneWayBoolDigraph.Adj false true := by
  exact ⟨rfl, rfl⟩

theorem oneWay_not_backward :
    ¬ oneWayBoolDigraph.Adj true false := by
  intro h
  cases h.1

end DirectedVsUndirected

section Exercises

variable {V : Type*}
variable (G H : SimpleGraph V)
variable {u v : V}

-- Exercise 1:
-- In a simple graph, adjacency is symmetric.
theorem ex01_adj_symmetric
    (h : G.Adj u v) : G.Adj v u := by
  exact h.symm

-- Exercise 2:
-- Adjacent vertices are distinct.
theorem ex02_adjacent_vertices_distinct
    (h : G.Adj u v) : u ≠ v := by
  by_contra
  rw[this] at h
  simp only [SimpleGraph.irrefl] at h


-- Exercise 3:
-- If two distinct vertices are not adjacent in `G`,
-- then they are adjacent in the complement graph `Gᶜ`.
theorem ex03_edge_in_complement
    (hne : u ≠ v) (hnot : ¬ G.Adj u v) : Gᶜ.Adj u v := by
  rw[SimpleGraph.compl_adj]
  exact ⟨hne, hnot⟩

-- Exercise 4:
-- If an edge is in `G`, then it is in the union graph `G ⊔ H`.
theorem ex04_edge_in_union_left
    (h : G.Adj u v) : (G ⊔ H).Adj u v := by
  rw[SimpleGraph.sup_adj]
  left
  exact h

end Exercises

section ExtraExercise

/-!
This one is not part of the four main exercises, but it is useful
for explaining how directed graphs relate to undirected graphs.

`D.toSimpleGraphInclusive` forgets directions:
if `D` has either directed edge `u → v` or `v → u`,
then the resulting simple graph has an undirected edge between `u` and `v`.
Because `SimpleGraph` is loopless, we still need `u ≠ v`.
-/

variable {V : Type*}
variable (D : Digraph V)
variable {u v : V}

theorem directed_edge_becomes_undirected_in_inclusive_forget
    (h : D.Adj u v) (hne : u ≠ v) :
    D.toSimpleGraphInclusive.Adj u v := by
  rw[Digraph.toSimpleGraphInclusive]
  simp only [SimpleGraph.fromRel_adj, ne_eq]
  constructor
  · exact hne
  · left
    exact h

end ExtraExercise
