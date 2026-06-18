import Mathlib.Combinatorics.Digraph.Orientation

/-!
# More graph theory exercises in Lean 4

These exercises build on the first worksheet.  They still use only a small
part of the graph API, but the statements combine symmetry, looplessness,
complements, graph unions, and directed graphs.

Useful lemmas from the first sheet:

* `SimpleGraph.ne_of_adj`
* `SimpleGraph.compl_adj`
* `SimpleGraph.sup_adj`
* `Digraph.toSimpleGraphInclusive`
* `SimpleGraph.fromRel_adj`
-/

section MoreUndirectedExercises

variable {V : Type*}
variable (G H K : SimpleGraph V)
variable {u v : V}

-- Exercise 1:
-- From one undirected edge, prove both the reversed edge and distinctness.
theorem ex01_adj_symm_and_distinct
    (h : G.Adj u v) : G.Adj v u ∧ u ≠ v := by
  constructor
  · exact h.symm
  · exact h.ne

-- Exercise 2:
-- A complement edge remembers both that the vertices are distinct
-- and that the original graph did not have the edge.
theorem ex02_complement_edge_gives_information
    (h : Gᶜ.Adj u v) : u ≠ v ∧ ¬ G.Adj u v := by
  rw [SimpleGraph.compl_adj] at h
  exact h

-- Exercise 3:
-- An edge cannot be in a graph and in its complement at the same time.
theorem ex03_graph_edge_not_complement_edge
    (h : G.Adj u v) : ¬ Gᶜ.Adj u v := by
  rw [SimpleGraph.compl_adj]
  -- intro f
  -- obtain ⟨fl, fr⟩ := f
  tauto

-- Exercise 4:
-- If `u` and `v` are distinct and not adjacent in `G`,
-- then the reversed pair is adjacent in the complement graph.
theorem ex04_reverse_complement_edge_from_nonedge
    (hne : u ≠ v) (hnot : ¬ G.Adj u v) : Gᶜ.Adj v u := by
  rw [SimpleGraph.compl_adj]
  tauto

-- Exercise 5:
-- A complement edge also rules out the reversed original edge,
-- because original graph adjacency is symmetric.
theorem ex05_complement_edge_forbids_reverse_original
    (h : Gᶜ.Adj u v) : ¬ G.Adj v u := by
  rw [SimpleGraph.compl_adj] at h
  tauto

-- Exercise 6:
-- If an edge is in the right-hand graph, it is in the union.
theorem ex06_edge_in_union_right
    (h : H.Adj u v) : (G ⊔ H).Adj u v := by
  rw [SimpleGraph.sup_adj]
  right
  exact h

-- Exercise 7:
-- On adjacency, the order of a graph union does not matter.
theorem ex07_union_adj_comm
    : (G ⊔ H).Adj u v ↔ (H ⊔ G).Adj u v := by
  rw [SimpleGraph.sup_adj, SimpleGraph.sup_adj]
  tauto


-- Exercise 8:
-- If a union edge did not come from the left graph,
-- then it must have come from the right graph.
theorem ex08_union_edge_of_not_left
    (h : (G ⊔ H).Adj u v) (hnot : ¬ G.Adj u v) : H.Adj u v := by
  rw [SimpleGraph.sup_adj] at h
  tauto

-- Exercise 9:
-- Not being adjacent in a union is the same as being non-adjacent
-- in both component graphs.
theorem ex09_not_union_edge_iff_not_each
    : ¬ (G ⊔ H).Adj u v ↔ ¬ G.Adj u v ∧ ¬ H.Adj u v := by
  rw [SimpleGraph.sup_adj]
  tauto

-- Exercise 10:
-- Every pair of distinct vertices is adjacent in `G ⊔ Gᶜ`.
theorem ex10_union_with_complement_contains_every_distinct_pair
    (hne : u ≠ v) : (G ⊔ Gᶜ).Adj u v := by
  rw [SimpleGraph.sup_adj, SimpleGraph.compl_adj]
  tauto

-- Exercise 11:
-- Characterize adjacency in the complement of a union.
theorem ex11_complement_of_union_adj
    : (G ⊔ H)ᶜ.Adj u v ↔ u ≠ v ∧ ¬ G.Adj u v ∧ ¬ H.Adj u v := by
  rw [SimpleGraph.compl_adj, SimpleGraph.sup_adj]
  tauto

-- Exercise 12:
-- Reassociate a union edge by unpacking and repacking the disjunctions.
theorem ex12_union_assoc_adj_forward
    (h : ((G ⊔ H) ⊔ K).Adj u v) : (G ⊔ (H ⊔ K)).Adj u v := by
  simp only [SimpleGraph.sup_adj] at h ⊢
  tauto

-- Exercise 13:
-- A union graph is still loopless.
theorem ex13_no_loop_in_union
    (h : (G ⊔ H).Adj u u) : False := by
  rw [SimpleGraph.sup_adj] at h
  rcases h with hG | hH
  · apply SimpleGraph.ne_of_adj at hG
    contradiction
  · apply SimpleGraph.ne_of_adj at hH
    contradiction

end MoreUndirectedExercises

section MoreDirectedExercises

variable {V : Type*}
variable (D : Digraph V)
variable {u v : V}

-- Exercise 14:
-- If the inclusive forgotten simple graph has an edge,
-- then at least one of the two directed edges was present.
theorem ex14_inclusive_adj_gives_directed_case
    (h : D.toSimpleGraphInclusive.Adj u v) : D.Adj u v ∨ D.Adj v u := by
  rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] at h
  tauto


#check SimpleGraph.fromRel_adj

-- Exercise 15:
-- One directed edge gives both orientations in the inclusive forgotten
-- simple graph, provided the endpoints are distinct.
theorem ex15_directed_edge_gives_both_simple_directions
    (h : D.Adj u v) (hne : u ≠ v) :
    D.toSimpleGraphInclusive.Adj u v ∧ D.toSimpleGraphInclusive.Adj v u := by
  rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  tauto

-- Exercise 16:
-- The inclusive forgotten simple graph is still loopless.
theorem ex16_inclusive_has_no_loops
    (u : V) : ¬ D.toSimpleGraphInclusive.Adj u u := by
  rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
  tauto

end MoreDirectedExercises

section OneWayBoolInclusiveExercises

/-!
A one-way directed graph on `Bool` again.  The point of these exercises is
that forgetting directions inclusively creates an undirected edge in both
simple-graph orientations, while the original digraph still has only one
directed edge.
-/

def moreOneWayBoolDigraph : Digraph Bool :=
  { Adj := fun x y => x = false ∧ y = true }

-- Exercise 17:
-- The forward directed edge appears in the inclusive forgotten simple graph.
theorem ex17_moreOneWay_inclusive_forward :
    moreOneWayBoolDigraph.toSimpleGraphInclusive.Adj false true := by
  rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
  tauto

-- Exercise 18:
-- After inclusively forgetting directions, the same edge is also available
-- in the reverse simple-graph orientation.
theorem ex18_moreOneWay_inclusive_backward :
    moreOneWayBoolDigraph.toSimpleGraphInclusive.Adj true false := by
  rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
  tauto

-- Exercise 19:
-- But the original digraph still does not contain the backward directed edge.
theorem ex19_moreOneWay_original_not_backward :
    ¬ moreOneWayBoolDigraph.Adj true false := by
  by_contra h
  -- unfold?
  -- unfold h
  obtain ⟨hl, hr⟩ := h
  tauto

end OneWayBoolInclusiveExercises
