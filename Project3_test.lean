/-
Every finite simple graph admits a proper vertex coloring using at most one more color than its maximum degree.

As a corollary, the chromatic number of every finite simple graph is at most one more than its maximum degree.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Basic

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma inductivestep : ∀ n : ℕ, ∀ {W : Type*} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj], Fintype.card W = n → ∀ {D : ℕ},
  (∀ v : W, G.degree v ≤ D) → G.Colorable (D + 1) := by
  intro n
  induction n with
  | zero =>
      intro V fin G decid indA nat degle
      have g : IsEmpty V := by
        exact Fintype.card_eq_zero_iff.mp indA
      exact SimpleGraph.Colorable.of_isEmpty (nat + 1)
  | succ m mh =>
      intro V fin G decid ind nat degle

      have mhG : ∀ {W : Type u_2} [inst : Fintype W] (G : SimpleGraph W)
      [inst_1 : DecidableRel G.Adj],
      Fintype.card W = m → ∀ {D : ℕ}, (∀ (v : W), G.degree v ≤ D) →
      G.Colorable (D + 1) := mh
      specialize mhG G

      have V_gro_0 : 0 < Fintype.card V := by
        exact Nat.lt_of_sub_eq_succ ind
      have V_nonempty : Nonempty V := by
        exact Fintype.card_pos_iff.mp V_gro_0

      let v : V := Classical.choice V_nonempty
      let V' : Type _ := { x : V // x ≠ v }
      have FinV' : Fintype V' := by
        exact Fintype.ofFinite V'
      let G' : SimpleGraph V' := SimpleGraph.induce { x | x ≠ v } G

      have G'_vert_card : Fintype.card V' = m := by
        have h_compl := Fintype.card_subtype_compl (fun x => x = v)
        change Fintype.card {x // x ≠ v} = m
        rw [h_compl]
        exact (Nat.sub_eq_iff_eq_add V_gro_0).mpr ind
      have G'_vert_card_reverse : m = Fintype.card V' := by
        exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (id (Eq.symm G'_vert_card))) m)
      -- -- have G'_col : G'.Colorable (G.maxDegree + 1) := by
      -- --   -- simp?
      -- --   exact?
      -- let G' := G.deleteEdges (G.incidenceSet v)

-- Beweis zu G'degLeGdeg mit Hilfe KI
      have G'degLeGdeg : G'.maxDegree ≤ G.maxDegree := by
        apply SimpleGraph.maxDegree_le_of_forall_degree_le
        intro x
        trans G.degree x.val
        · rw [SimpleGraph.degree, SimpleGraph.degree, ← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
          apply Finset.card_le_card
          simp [Finset.subset_iff]
          tauto
        · exact SimpleGraph.degree_le_maxDegree G x.val

      have mhG' : ∀ {W : Type u_2} [inst : Fintype W] (G : SimpleGraph W)
      [inst_1 : DecidableRel G.Adj],
      Fintype.card W = m → ∀ {D : ℕ}, (∀ (v : W), G.degree v ≤ D) →
      G.Colorable (D + 1) := mh
      specialize mhG' G'

      have G'_col : G'.Colorable (G.maxDegree + 1) := by
        apply SimpleGraph.Colorable.mono (Nat.add_le_add_right G'degLeGdeg 1)   --diese Zeile KI, macht aus G.maxDegree + 1 zu Zeigen G'.maxDegree + 1
        apply mhG' G'_vert_card   -- komisch, dass apply? diese einfache Zeile nicht findet
        exact fun v_2 ↦ SimpleGraph.degree_le_maxDegree G' v_2

      have v_degLeGmaxdeg : G.degree v ≤ G.maxDegree := by
        exact SimpleGraph.degree_le_maxDegree G v

      have GcolEqG'colANDvdeg : G'.Colorable (G.maxDegree + 1) ∧
      G.degree v ≤ G.maxDegree → G.Colorable (G.maxDegree + 1) := by
        simp only [and_imp]
        intro h hh
        refine (SimpleGraph.colorable_iff_exists_bdd_nat_coloring (G.maxDegree + 1)).mpr ?_
        -- suchen hier also gültige Färbung für G (so dass die Zahl(=Farbe) für jeden Knoten kleiner G.maxDegree + 1 ist).
        -- müssten also bereits bestehene gültige Färbung für G' nehmen können (existiert nach G'_col)
        -- da eine gültige Färbung für lean mit der "nullten" Farbe beginnt, kann wegen "G.degree v ≤ G.maxDegree" (v_degLeGmaxdeg)
        -- auch v mit einer Farbe ≤ G.maxDegree gefärbt werden.
        -- die folgende Umsetzung ist mit KI untersützt

        obtain ⟨c'⟩ := h

        classical
        use ⟨fun (w : V) ↦
          if h : w ≠ v then
            (c' ⟨w, h⟩).val
          else
            0, -- Temporärer Platzhalter für deine freie Farbe, damit es kompiliert
          by
            -- Hier fordert Lean den Beweis, dass die Färbung gültig ist (c w1 ≠ c w2 für benachbarte Knoten)
            sorry⟩

        intro v_1
        dsimp
        split_ifs with h
        · -- Fall 1: v_1 ≠ v ist WAHR (h : v_1 ≠ v)
          -- Zeigt direkt, dass die Farbe aus c' kleiner als die Farbanzahl ist
          omega
        · -- Fall 2: v_1 ≠ v ist FALSCH (also v_1 = v, der Pivot-Knoten)
          -- Zeigt, dass die Platzhalterfarbe 0 kleiner als G.maxDegree + 1 ist
          exact (c' ⟨v_1, h⟩).isLt

      have G_col : G.Colorable (G.maxDegree + 1) := by
        -- komischerweise findet exact? die untere Zeile nicht. And.intro von KI
        exact GcolEqG'colANDvdeg (And.intro G'_col v_degLeGmaxdeg)

      have h_le : G.maxDegree + 1 ≤ nat + 1 := by
        apply Nat.succ_le_succ
        exact SimpleGraph.maxDegree_le_of_forall_degree_le G nat degle

      refine SimpleGraph.Colorable.mono ?_ G_col
      exact Order.add_one_le_iff.mpr h_le

theorem faerbbar_zu_knotengrad : G.Colorable (G.maxDegree + 1) := by
  have hD : ∀ v : V, G.degree v ≤ G.maxDegree := by
    intro v
    exact G.degree_le_maxDegree v
  exact inductivestep (Fintype.card V) G rfl hD
