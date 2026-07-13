/-
Every finite simple graph admits a proper vertex coloring using at most one more color than its maximum degree.

As a corollary, the chromatic number of every finite simple graph is at most one more than its maximum degree.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
-- import Mathlib.Combinatorics.SimpleGraph.Basic

variable {V : Type*} (G : SimpleGraph V)

theorem Färbungszahl_zu_Knotengrad {n m : ℕ} [DecidableRel G.Adj] [Fintype V]
(h : G.maxDegree = n) (k : m = Fintype.card V):
G.Colorable (n + 1) := by
    -- sorry
    classical
    rw [← h]
    -- -- rw [show G.Colorable = fun n ↦ Nonempty (G.Coloring (Fin n)) from rfl]
    -- -- rw [show G.Coloring = fun α ↦ G →g SimpleGraph.completeGraph α from rfl]
    -- -- simp only [SimpleGraph.completeGraph_eq_top]
    -- -- refine Nonempty.intro ?_
    -- -- -- rw [show (G →g ⊤) = (G.Adj →r ⊤.Adj) from rfl]
    -- -- refine SimpleGraph.Copy.toHom ?_
    -- -- unfold?
    -- let m :=  Fintype.card V
    -- induction (Fintype.card V) with
    --  | zero =>
    --   --have k : m = 0 := by sorry
    --   have g : IsEmpty V := by
    --     exact Fintype.card_eq_zero_iff.mp k
    --   simp only [SimpleGraph.maxDegree_of_isEmpty, zero_add]
    --   exact SimpleGraph.Colorable.of_isEmpty 1
    --  | succ m mh =>
    -- --   exact mh
    --   sorry

    -- let m := Fintype.card V
    -- let mm := Fintype.card V
    -- have kk : mm = Fintype.card V :=  by rfl
    induction m with
    | zero =>
      have g : IsEmpty V := by
        exact Fintype.card_eq_zero_iff.mp (id (Eq.symm k))
      simp only [SimpleGraph.maxDegree_of_isEmpty, zero_add]
      exact SimpleGraph.Colorable.of_isEmpty 1
    | succ m mh =>
      have V_gro_0 : 0 < Fintype.card V := by
        exact Nat.lt_of_sub_eq_succ (id (Eq.symm k))
    -- im folgenden sind Z.49,51,60-67 mit KI Hilfe, schafft reduzierten Graph + card
      have h_nonempty : Nonempty V := by
        exact Fintype.card_pos_iff.mp V_gro_0
      let v : V := Classical.choice h_nonempty
      -- -- let s : Set V := {x | x ≠ v}
      -- -- let G' :  SimpleGraph s := G.induce s
      -- -- -- have G'_vert_card : m = Fintype.card s := by
      -- -- have G'_vert_card : Fintype.card s = m := by
      -- --   have h_minus_one := Fintype.card_subtype_compl_is_compl_singleton v
      -- --     rw [h_minus_one, h_card]
      -- --   exact Nat.succ_sub_one n

      let V' : Type _ := { x : V // x ≠ v }
      haveI : Fintype V' := Subtype.fintype (fun x => x ≠ v)
      let G' : SimpleGraph V' := SimpleGraph.induce { x | x ≠ v } G

      have G'_vert_card : Fintype.card V' = m := by
        have h_compl := Fintype.card_subtype_compl (fun x => x = v)
        change Fintype.card {x // x ≠ v} = m
        rw [h_compl]
        exact (Nat.sub_eq_iff_eq_add V_gro_0).mpr (id (Eq.symm k))

      have G'_vert_card_reverse : m = Fintype.card V' := by
        exact Eq.symm G'_vert_card

      have mh_G' : m = Fintype.card V' → G'.Colorable (G.maxDegree + 1) := by
        -- exact mh
        sorry

      have G'_col : G'.Colorable (G.maxDegree + 1) := by
        -- hier müssen eigentlich nur noch mh und G'_vert_card zusammengeführt werden
        exact mh_G' G'_vert_card_reverse

-- revert V !!!

      -- let G' := G.deleteEdges (G.incidenceSet v)
      -- have G'subgraph : G' ≤ G := by
      --   exact SimpleGraph.deleteEdges_le (G.incidenceSet v)
      -- have G'_col : G'.Colorable (G.maxDegree + 1) := by
      --   -- exact?
      --   -- möchte sowas wie Colorable.mono_left nutzen, lean scheint G' ≤ G nicht automatisch zu erkennen
      --   -- refine SimpleGraph.Colorable.mono_left G'subgraph mh
      --   -- funktioniert nicht, da es die Färbbarkeit von G vorraussetzt, un die Färbbarkeit
      --   -- von G' als Teilgraph abzuleiten. Wir müssen hier dringend auf die Induktionsbehauptung
      --   -- zurückkommen. Die Färbbarkeit von G anzunekmen um am Ende die Färbbatkeit von G zu
      --   -- zeigen wäre ein Zirkelschluss.
