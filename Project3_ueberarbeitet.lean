/-
Every finite simple graph admits a proper vertex coloring using at most one more color than its maximum degree.

As a corollary, the chromatic number of every finite simple graph is at most one more than its maximum degree.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Basic

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

universe u

lemma inductivestep : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj],
Fintype.card W = n → ∀ {D : ℕ}, (∀ v : W, G.degree v ≤ D) → G.Colorable (D + 1) := by
  intro n
  induction n with
  | zero =>
      intro V fin G decid indA nat degle
      have g : IsEmpty V := by
        exact Fintype.card_eq_zero_iff.mp indA
      exact SimpleGraph.Colorable.of_isEmpty (nat + 1)
  | succ m mh =>
      intro V fin G decid ind nat degle
-- Zeigen, dass V im Induktionsschritt nicht leer ist
      have V_gro_0 : 0 < Fintype.card V := by
        exact Nat.lt_of_sub_eq_succ ind
      have V_nonempty : Nonempty V := by
        exact Fintype.card_pos_iff.mp V_gro_0
-- Wählen nun ein v aus V und setzen G' als G ohne v
      let v : V := Classical.choice V_nonempty
      let V' : Type _ := { x : V // x ≠ v }
      have FinV' : Fintype V' := by
        exact Fintype.ofFinite V'
      let G' : SimpleGraph V' := SimpleGraph.induce { x | x ≠ v } G
-- Zeigen, dass G' m Knoten hat, dies entspricht dem Graph der Induktionsannahme
      have G'_vert_card : Fintype.card V' = m := by
        have h_compl := Fintype.card_subtype_compl (fun x => x = v)
        change Fintype.card {x // x ≠ v} = m
        rw [h_compl]
        exact (Nat.sub_eq_iff_eq_add V_gro_0).mpr ind
-- Zeigen, dass der Maximalgrad des induzierten Graphens kleiner gleich dem des Ursprünglichen ist
-- Beweis zu G'degLeGdeg mit Hilfe KI
      have G'degLeGdeg : G'.maxDegree ≤ G.maxDegree := by
        apply SimpleGraph.maxDegree_le_of_forall_degree_le
        intro x
        trans G.degree x.val
        · rw [SimpleGraph.degree, SimpleGraph.degree,
          ← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
          apply Finset.card_le_card
          simp [Finset.subset_iff]
          tauto
        · exact SimpleGraph.degree_le_maxDegree G x.val
-- Die Induktionsannahme, angewendet auf den induzierten Graphen G'
      have mhG' : ∀ {W : Type u} [Fintype W] (G : SimpleGraph W)
      [inst_1 : DecidableRel G.Adj],
      Fintype.card W = m → ∀ {D : ℕ}, (∀ (v : W), G.degree v ≤ D) →
      G.Colorable (D + 1) := mh
      specialize mhG' G'
-- Zeigen mit der Induktionsannahme, dass G' färbbar ist
      have G'_col : G'.Colorable (G.maxDegree + 1) := by
        -- nächste Zeile KI, macht aus G.maxDegree + 1 zu Zeigen G'.maxDegree + 1
        apply SimpleGraph.Colorable.mono (Nat.add_le_add_right G'degLeGdeg 1)
        apply mhG' G'_vert_card   -- komisch, dass apply? diese einfache Zeile nicht findet
        exact fun v_2 ↦ SimpleGraph.degree_le_maxDegree G' v_2
-- der Grad eines beliebigen Knotens ist kleiner gleich dem Maximalgrad der Graphen
      have v_degLeGmaxdeg : G.degree v ≤ G.maxDegree := by
        exact SimpleGraph.degree_le_maxDegree G v
-- wir wählen eine Färbung für G' aus, diese ist c'
      let c' := G'_col.some
-- geben den an den Knoten v angrenzenden Knoten die Farbe aus der Färbung c'
      let colAdj_v := Finset.image (fun (w : {x // x ≠ v}) ↦ (c' w).val)
        (Finset.filter (fun w ↦ G.Adj w.val v) Finset.univ)
-- zeigen, dass strikt weniger als der (Maximalgrad von G) + 1 Farben in der obigen
-- Färbung verwendet wurden
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
-- im folgenden Block bekommen wir eine Farbe f für den Knoten v und zeigen mit h_f,
-- dass diese Farbe von den Farben der angrenzenen Knoten verschieden ist
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
-- der eigentliche Hauptschritt, wir zeigen, dass aus der Induktionsannahme
-- die Induktionsbehauptung folgt
      have GcolEqG'colANDvdeg : G'.Colorable (G.maxDegree + 1) ∧
      G.degree v ≤ G.maxDegree → G.Colorable (G.maxDegree + 1) := by
        simp only [and_imp]
        intro h hh
        refine (SimpleGraph.colorable_iff_exists_bdd_nat_coloring (G.maxDegree + 1)).mpr ?_
        -- suchen hier also gültige Färbung für G (so dass die Zahl(=Farbe) für jeden Knoten
        -- kleiner G.maxDegree + 1 ist). Müssten also bereits bestehene gültige Färbung für G'
        -- nehmen können (existiert nach G'_col) da eine gültige Färbung für lean mit der
        -- "nullten" Farbe beginnt, kann wegen "G.degree v ≤ G.maxDegree" (v_degLeGmaxdeg)
        -- auch v mit einer Farbe ≤ G.maxDegree gefärbt werden.
        -- Die folgende Umsetzung ist mit KI untersützt
        classical
        use ⟨fun (w : V) ↦
          if h : w ≠ v then
            -- Für alle Knoten außer v übernehmen wir die Färbung aus der Induktionsannahme
            (c' ⟨w, h⟩).val
          else
            -- Fü v nehmen wir die in zuvor bestimmte Farbe
            f,
          by
            -- Hier folgt der Beweis, dass die Färbung gültig ist (c w1 ≠ c w2 wenn benachbart)
            intro v_1 v_2 h_adj
            dsimp
            split_ifs with h1 h2
            · -- Fall 1: Beide Knoten wären der Pivot (Widerspruch wegen loopless)
              subst h1
              subst h2
                  -- Wir erzeugen zuerst das False im Kontext aus dem Schleifen-Widerspruch
              have h_false : False := G.loopless.irrefl v h_adj
                  -- Ein Widerspruch im Kontext schließt jedes beliebige Ziel
              exact False.elim h_false
            · -- Fall 2: v_1 ist der Pivot-Knoten (v_1 = v), v_2 im Subgraphen
              -- Da v_1 = v, ist v_2 über h_adj ein Nachbar von v.
              -- Deshalb MUSS die Farbe von v_2 in 'verbotene_farben' liegen!
              subst v_1
              -- h_adj zeigt nun, dass v_2 ein Nachbar von v ist.
              -- Damit liegt seine Farbe per Definition in 'verbotene_farben'.
              intro h_kollision
              have h_in_verboten : (c' ⟨v_2, h2⟩).val ∈ colAdj_v := by
                simp only [colAdj_v, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
                use ⟨v_2, h2⟩
                exact And.symm ⟨rfl, id (SimpleGraph.adj_symm G h_adj)⟩
                -- Widerspruch! f darf nicht in verbotene_farben liegen (h_f.1), aber h_kollision
                -- behauptet das Gegenteil.
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
                -- Widerspruch! f darf nicht in verbotene_farben liegen (h_f.1), aber h_kollision
                -- behauptet das Gegenteil.
              rw [h_kollision] at h_in_verboten
              exact h_f.1 h_in_verboten
            · -- Fall 4: Beide Knoten liegen im Subgraphen
              rename_i h2
              have h_adj_prime : G'.Adj ⟨v_1, h1⟩ ⟨v_2, h2⟩ := h_adj
              exact Fin.ext_iff.not.mp (c'.valid h_adj_prime)⟩
        -- Nun zeigen wir die obere Schranke für die Farbanzahl
        intro v_1
        dsimp
        split_ifs with h
        · -- Fall 1: v_1 = v ist WAHR (also v_1 = v, der Pivot-Knoten)
          -- Zeigt, dass die Platzhalterfarbe f kleiner als G.maxDegree + 1 ist
          omega
        · -- Fall 2: v_1 = v ist FALSCH (h : v_1 ≠ v)
          -- Zeigt direkt, dass die Farbe aus c' kleiner als die Farbanzahl ist
          exact (c' ⟨v_1, h⟩).isLt
-- Ziehen die Schlussfolgerung (G.Colorable (G.maxDegree + 1)) aus dem obigen heraus, indem
-- wir die bereits davor gezeigten Annahmen nutzen
      have G_col : G.Colorable (G.maxDegree + 1) := by
        -- komischerweise findet exact? die untere Zeile nicht. And.intro von KI
        exact GcolEqG'colANDvdeg (And.intro G'_col v_degLeGmaxdeg)
-- Passen die obere Schranke (G.maxDegree + 1) so an, dass es dem zu Zeigenden entspricht
      have h_le : G.maxDegree + 1 ≤ nat + 1 := by
        apply Nat.succ_le_succ
        exact SimpleGraph.maxDegree_le_of_forall_degree_le G nat degle
-- Hier schließen wir den Beweis ab
      refine SimpleGraph.Colorable.mono ?_ G_col
      exact Order.add_one_le_iff.mpr h_le

theorem faerbbar_zu_knotengrad : G.Colorable (G.maxDegree + 1) := by
  have hD : ∀ v : V, G.degree v ≤ G.maxDegree := by
    intro v
    exact G.degree_le_maxDegree v
  exact inductivestep (Fintype.card V) G rfl hD

-- Hier zeigen wir das Corollar
theorem chromatischeZahlZuMaximalgrad : G.chromaticNumber ≤ G.maxDegree + 1 := by
  -- schreiben die Definition der chromatischen Zahl um, so dass wir die
  -- Färbbarkeit einsetzen können
  rw [show G.chromaticNumber = ⨅ n ∈ setOf G.Colorable, ↑n from rfl]
  -- Mit "iInf₂_le" nutzen wir das Infimum über n
  apply iInf₂_le (G.maxDegree + 1)
  exact faerbbar_zu_knotengrad G
