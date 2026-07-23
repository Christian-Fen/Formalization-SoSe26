/-
Every finite simple graph admits a proper vertex coloring using at most one more color than its maximum degree.

As a corollary, the chromatic number of every finite simple graph is at most one more than its maximum degree.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Basic

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

universe u v -- !!! statt type u_2

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

        -- stattdessen .symm

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

      have mhG' : ∀ {W : Type u_2} [Fintype W] (G : SimpleGraph W)
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

        let colAdj_v := Finset.image (fun (w : {x // x ≠ v}) ↦ (c' w).val)
          (Finset.filter (fun w ↦ G.Adj w.val v) Finset.univ)
        have colAdj_vCard : colAdj_v.card < G.maxDegree + 1 := by
          let n := (Finset.filter (fun (w : { x : V // x ≠ v }) ↦ G.Adj w.val v)
          (Finset.univ : Finset { x : V // x ≠ v })).card
          calc
            colAdj_v.card ≤ n := by
              exact @Finset.card_image_le _ ℕ _ _ _
            _ ≤ G.degree v := by
              rw [SimpleGraph.degree]
              dsimp [n]
              rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
              apply Finset.card_le_card
              · intro x hx
                simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
                 true_and, Function.Embedding.coeFn_mk] at hx
                rcases hx with ⟨w, hw_adj, rfl⟩
                simp only [SimpleGraph.mem_neighborFinset]
                exact hw_adj.symm
            _ < G.maxDegree + 1 := by
              omega

        have h_range : ¬ (Finset.range (G.maxDegree + 1) ⊆ colAdj_v) := by
          intro h_sub
          have h_le := Finset.card_le_card h_sub
          rw [Finset.card_range] at h_le
          omega

        have colExists : ∃ f : ℕ, f ∉ colAdj_v ∧ f < G.maxDegree + 1 := by
          rcases Finset.not_subset.mp h_range with ⟨f, hf_range, hf_not_mem⟩
          rw [Finset.mem_range] at hf_range
          use f

        let f := Classical.choose colExists
        have h_f := Classical.choose_spec colExists

        classical
        use ⟨fun (w : V) ↦
          if h : w ≠ v then
            (c' ⟨w, h⟩).val
          else
            f, -- Temporärer Platzhalter für deine freie Farbe, damit es kompiliert
          by
            -- Hier fordert Lean den Beweis, dass die Färbung gültig ist (c w1 ≠ c w2 für benachbarte Knoten)
            intro v_1 v_2 h_adj
            dsimp
            split_ifs with h1 h2
            · -- Fall 1: Beide Knoten liegen im Subgraphen
              subst h1
              subst h2
                  -- Wir erzeugen zuerst das False im Kontext aus dem Schleifen-Widerspruch
              have h_false : False := G.loopless.irrefl v h_adj
                  -- Ein Widerspruch im Kontext schließt jedes beliebige Ziel
              exact False.elim h_false
            · -- Fall 2: v_1 im Subgraphen, v_2 ist der Pivot-Knoten (v_2 = v)
              -- Da v_2 = v, ist v_1 über h_adj ein Nachbar von v.
              -- Deshalb MUSS die Farbe von v_1 in 'verbotene_farben' liegen!
              subst v_1
                  -- h_adj zeigt nun, dass v_1 ein Nachbar von v ist.
                  -- Damit liegt seine Farbe per Definition in 'verbotene_farben'.
              intro h_kollision
              have h_in_verboten : (c' ⟨v_2, h2⟩).val ∈ colAdj_v := by
                simp only [colAdj_v, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
                use ⟨v_2, h2⟩
                exact And.symm ⟨rfl, id (SimpleGraph.adj_symm G h_adj)⟩
                -- exact ⟨h_adj, rfl⟩
                  -- Widerspruch! f darf nicht in verbotene_farben liegen (h_f.1), aber h_kollision behauptet das Gegenteil.
              rw [← h_kollision] at h_in_verboten
              exact h_f.1 h_in_verboten
            · -- Fall 3: v_1 ist der Pivot-Knoten (v_1 = v), v_2 im Subgraphen
                  -- Symmetrisch zu Fall 2
              subst v_2
                  -- h_adj zeigt nun, dass v_1 ein Nachbar von v ist.
                  -- Damit liegt seine Farbe per Definition in 'verbotene_farben'.
              intro h_kollision
              have h_in_verboten : (c' ⟨v_1, h1⟩).val ∈ colAdj_v := by
                simp only [colAdj_v, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
                use ⟨v_1, h1⟩
                -- exact ⟨h_adj, rfl⟩
                  -- Widerspruch! f darf nicht in verbotene_farben liegen (h_f.1), aber h_kollision behauptet das Gegenteil.
              rw [h_kollision] at h_in_verboten
              exact h_f.1 h_in_verboten
            · -- Fall 4: Beide Knoten wären der Pivot (Widerspruch wegen loopless)
              rename_i h2
              have h_adj_prime : G'.Adj ⟨v_1, h1⟩ ⟨v_2, h2⟩ := h_adj
              exact Fin.ext_iff.not.mp (c'.valid h_adj_prime)⟩

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
