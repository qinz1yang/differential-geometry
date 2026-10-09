/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TubeGeneralPosition

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_generic_polygonal_path {K O₀ O₁ : Set E3} (hK : IsClosed K) (hO₀ : IsOpen O₀)
    (hO₁ : IsOpen O₁) {p q : E3} (hp : p ∈ O₀) (hq : q ∈ O₁) (hpq : JoinedIn Kᶜ p q)
    (F : Finset E3) {ℋ : Set (Set E3)} (hℋ : ℋ.Finite) (hℋc : ∀ B ∈ ℋ, IsClosed B)
    (hℋi : ∀ B ∈ ℋ, interior B = ∅) :
    ∃ (N : ℕ) (w : ℕ → E3), 0 < N ∧ w 0 ∈ O₀ ∧ w N ∈ O₁ ∧
      (∀ k < N, segment ℝ (w k) (w (k + 1)) ⊆ Kᶜ) ∧
      (∀ k ≤ N, ∀ B ∈ ℋ, w k ∉ B) ∧
      ∀ k ≤ N, ∀ s : Finset E3, s ⊆ F ∪ (Finset.range k).image w → s.card ≤ 3 →
        w k ∉ affineSpan ℝ (s : Set E3) := by
  classical
  set γ := hpq.somePath with hγdef
  have hγ : ∀ t, γ t ∈ Kᶜ := hpq.somePath_mem
  have hrange : IsCompact (range γ) := isCompact_range γ.continuous
  obtain ⟨ε, hε, hεsub⟩ :=
    hrange.exists_cthickening_subset_open hK.isOpen_compl (range_subset_iff.mpr hγ)
  obtain ⟨δ, hδ, hδγ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := lt_trans (by positivity) hN
    exact_mod_cast this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  set y : ℕ → E3 := fun k => γ (projIcc 0 1 zero_le_one ((k : ℝ) / N)) with hydef
  have hy0 : y 0 = p := by
    simp only [hydef, Nat.cast_zero, zero_div]
    rw [projIcc_left]
    exact γ.source
  have hyN : y N = q := by
    simp only [hydef]
    rw [div_self hNr.ne', projIcc_right]
    exact γ.target
  have hyk : ∀ k < N, dist (y k) (y (k + 1)) < ε / 3 := by
    intro k hk
    apply hδγ
    have hk1 : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hNr).mpr (by exact_mod_cast hk.le)⟩
    have hk2 : ((k + 1 : ℕ) : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hNr).mpr (by exact_mod_cast hk)⟩
    rw [projIcc_of_mem _ hk1, projIcc_of_mem _ hk2, Subtype.dist_eq]
    change dist ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N) < δ
    rw [Real.dist_eq, Nat.cast_add, Nat.cast_one, ← sub_div, abs_div, abs_of_pos hNr]
    have : |(k : ℝ) - (k + 1)| = 1 := by
      rw [show (k : ℝ) - (k + 1) = -1 by ring, abs_neg, abs_one]
    rw [this]
    rw [div_lt_iff₀ hNr]
    rw [div_lt_iff₀ hδ] at hN
    linarith
  have hchoose : ∀ (G : Finset E3) (O : Set E3), IsOpen O → O.Nonempty →
      ∃ x ∈ O, (∀ B ∈ ℋ, x ∉ B) ∧
        ∀ s : Finset E3, s ⊆ G → s.card ≤ 3 → x ∉ affineSpan ℝ (s : Set E3) := by
    intro G O hO hne
    set 𝒮 := ℋ ∪ ((G.powerset.filter fun s : Finset E3 => s.card ≤ 3).image
      fun s : Finset E3 => (affineSpan ℝ (↑s : Set E3) : Set E3) : Set (Set E3)) with h𝒮
    have h𝒮f : 𝒮.Finite := hℋ.union (Finset.finite_toSet _)
    obtain ⟨x, hxO, hx⟩ := exists_mem_forall_notMem_of_finite h𝒮f (by
      rintro B (hB | hB)
      · exact hℋc B hB
      · obtain ⟨s, -, rfl⟩ := Finset.mem_coe.mp hB |> Finset.mem_image.mp
        exact AffineSubspace.closed_of_finiteDimensional _) (by
      rintro B (hB | hB)
      · exact hℋi B hB
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_coe.mp hB |> Finset.mem_image.mp
        exact interior_affineSpan_eq_empty (Finset.mem_filter.mp hs).2) hO hne
    refine ⟨x, hxO, fun B hB => hx B (Or.inl hB), fun s hs hcard hxs => hx _ (Or.inr ?_) hxs⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs, hcard⟩, rfl⟩)
  have hrec : ∀ m ≤ N, ∃ w : ℕ → E3, ∀ k ≤ m, w k ∈ ball (y k) (ε / 3) ∧ (k = 0 → w k ∈ O₀) ∧
      (k = N → w k ∈ O₁) ∧ (∀ B ∈ ℋ, w k ∉ B) ∧
      ∀ s : Finset E3, s ⊆ F ∪ (Finset.range k).image w → s.card ≤ 3 →
        w k ∉ affineSpan ℝ (s : Set E3) := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨x, ⟨hxb, hxO⟩, hxB, hxs⟩ := hchoose F (ball (y 0) (ε / 3) ∩ O₀)
        (isOpen_ball.inter hO₀) ⟨p, by rw [← hy0]; exact mem_ball_self (by positivity),
          hp⟩
      refine ⟨fun _ => x, fun k hk => ?_⟩
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      refine ⟨hxb, fun _ => hxO, fun h => absurd h hN0.ne, hxB, fun s hs hcard => hxs s ?_ hcard⟩
      simpa using hs
    | succ m ih =>
      intro hm
      obtain ⟨w, hw⟩ := ih (by omega)
      set O := ball (y (m + 1)) (ε / 3) ∩ (if m + 1 = N then O₁ else univ) with hOdef
      have hOo : IsOpen O := isOpen_ball.inter (by split_ifs; exacts [hO₁, isOpen_univ])
      have hOne : O.Nonempty := by
        refine ⟨y (m + 1), mem_ball_self (by positivity), ?_⟩
        split_ifs with h
        · rw [h, hyN]
          exact hq
        · exact mem_univ _
      obtain ⟨x, ⟨hxb, hxO⟩, hxB, hxs⟩ :=
        hchoose (F ∪ (Finset.range (m + 1)).image w) O hOo hOne
      refine ⟨Function.update w (m + 1) x, fun k hk => ?_⟩
      have himg : ∀ j ≤ m + 1, (Finset.range j).image (Function.update w (m + 1) x) =
          (Finset.range j).image w := by
        intro j hj
        refine Finset.image_congr fun i hi => ?_
        have : i ≠ m + 1 := by
          have := Finset.mem_range.mp hi
          omega
        exact Function.update_of_ne this _ _
      rcases (Nat.lt_or_eq_of_le hk) with hk' | hk'
      · have hkm : k ≤ m := by omega
        have hne : k ≠ m + 1 := by omega
        rw [Function.update_of_ne hne, himg k (by omega)]
        exact hw k hkm
      · subst hk'
        rw [Function.update_self, himg (m + 1) le_rfl]
        refine ⟨hxb, fun h => absurd h (Nat.succ_ne_zero m), fun h => ?_, hxB, hxs⟩
        rw [ite_eq_left h] at hxO
        exact hxO
  obtain ⟨w, hw⟩ := hrec N le_rfl
  refine ⟨N, w, hN0, (hw 0 (Nat.zero_le _)).2.1 rfl, (hw N le_rfl).2.2.1 rfl, ?_,
    fun k hk => (hw k hk).2.2.2.1, fun k hk => (hw k hk).2.2.2.2⟩
  intro k hk
  have h1 := (hw k hk.le).1
  have h2 := (hw (k + 1) hk).1
  have h3 := hyk k hk
  have hsub : segment ℝ (w k) (w (k + 1)) ⊆ ball (y k) ε := by
    refine (convex_ball (y k) ε).segment_subset ?_ ?_
    · exact ball_subset_ball (by linarith) h1
    · rw [mem_ball] at h2 ⊢
      have := dist_triangle (w (k + 1)) (y (k + 1)) (y k)
      rw [dist_comm (y (k + 1))] at this
      linarith
  intro z hz
  apply hεsub
  exact mem_cthickening_of_dist_le z (y k) ε _ ⟨_, rfl⟩ (le_of_lt (hsub hz))

theorem inter_segment_subset_of_notMem_affineSpan {a b c : E3}
    (hc : c ∉ affineSpan ℝ ({a, b} : Set E3)) : segment ℝ a b ∩ segment ℝ b c ⊆ {b} := by
  rintro x ⟨hxab, hxbc⟩
  rw [segment_eq_image'] at hxbc
  obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := hxbc
  rcases ht0.lt_or_eq with htpos | htz
  · exfalso
    apply hc
    have hxA : b + t • (c - b) ∈ affineSpan ℝ ({a, b} : Set E3) :=
      convexHull_subset_affineSpan _ (by rw [convexHull_pair]; exact hxab)
    have hbA : b ∈ affineSpan ℝ ({a, b} : Set E3) := mem_affineSpan ℝ (mem_insert_of_mem _ rfl)
    have hc' : c = AffineMap.lineMap b (b + t • (c - b)) (1 / t) := by
      rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, smul_smul, one_div,
        inv_mul_cancel₀ htpos.ne', one_smul]
      abel
    rw [hc']
    exact AffineMap.lineMap_mem _ hbA hxA
  · subst htz
    simp

theorem generic_polygonal_path_facts {w : ℕ → E3} {N : ℕ} {F : Finset E3}
    (hgen : ∀ k ≤ N, ∀ s : Finset E3, s ⊆ F ∪ (Finset.range k).image w → s.card ≤ 3 →
      w k ∉ affineSpan ℝ (s : Set E3)) :
    (∀ k < N, ∀ e₁ ∈ F, ∀ e₂ ∈ F,
      Disjoint (segment ℝ (w k) (w (k + 1))) (segment ℝ e₁ e₂)) ∧
    (∀ i k, k < N → i + 1 < k →
      Disjoint (segment ℝ (w i) (w (i + 1))) (segment ℝ (w k) (w (k + 1)))) ∧
    (∀ k, k + 1 < N →
      segment ℝ (w k) (w (k + 1)) ∩ segment ℝ (w (k + 1)) (w (k + 2)) ⊆ {w (k + 1)}) ∧
    (∀ k, 0 < k → k < N → w (k + 1) ∉ affineSpan ℝ ({w (k - 1), w k} : Set E3)) := by
  classical
  have hmem : ∀ i k, i < k → w i ∈ F ∪ (Finset.range k).image w := fun i k hik =>
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hik, rfl⟩)
  refine ⟨fun k hk e₁ he₁ e₂ he₂ => ?_, fun i k hk hik => ?_, fun k hk => ?_,
    fun k hk0 hk => ?_⟩
  · refine disjoint_segment_of_notMem_affineSpan ?_ ?_
    · have := hgen k hk.le {e₁, e₂} (by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact Finset.mem_union_left _ he₁
        · rw [Finset.mem_singleton.mp he]
          exact Finset.mem_union_left _ he₂) (Finset.card_le_two.trans (by norm_num))
      simpa using this
    · have := hgen (k + 1) hk {w k, e₁, e₂} (by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hmem k (k + 1) (Nat.lt_succ_self k)
        rcases Finset.mem_insert.mp he with rfl | he
        · exact Finset.mem_union_left _ he₁
        · rw [Finset.mem_singleton.mp he]
          exact Finset.mem_union_left _ he₂) (Finset.card_le_three)
      simpa using this
  · refine (disjoint_segment_of_notMem_affineSpan ?_ ?_).symm
    · have := hgen k hk.le {w i, w (i + 1)} (by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hmem i k (by omega)
        · rw [Finset.mem_singleton.mp he]
          exact hmem (i + 1) k hik) (Finset.card_le_two.trans (by norm_num))
      simpa using this
    · have := hgen (k + 1) hk {w k, w i, w (i + 1)} (by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hmem k (k + 1) (Nat.lt_succ_self k)
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hmem i (k + 1) (by omega)
        · rw [Finset.mem_singleton.mp he]
          exact hmem (i + 1) (k + 1) (by omega)) (Finset.card_le_three)
      simpa using this
  · refine inter_segment_subset_of_notMem_affineSpan ?_
    have := hgen (k + 2) hk {w k, w (k + 1)} (by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hmem k (k + 2) (by omega)
      · rw [Finset.mem_singleton.mp he]
        exact hmem (k + 1) (k + 2) (by omega)) (Finset.card_le_two.trans (by norm_num))
    simpa using this
  · have := hgen (k + 1) hk {w (k - 1), w k} (by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hmem (k - 1) (k + 1) (by omega)
      · rw [Finset.mem_singleton.mp he]
        exact hmem k (k + 1) (by omega)) (Finset.card_le_two.trans (by norm_num))
    simpa using this

theorem exists_last_mem_segment {X : Set E3} (hX : IsClosed X) {u v : E3}
    (h : ∃ t ∈ Icc (0 : ℝ) 1, u + t • (v - u) ∈ X) :
    ∃ t ∈ Icc (0 : ℝ) 1, u + t • (v - u) ∈ X ∧ ∀ t' ∈ Ioc t 1, u + t' • (v - u) ∉ X := by
  set T := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ u + t • (v - u) ∈ X} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (hX.preimage (by fun_prop))
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, htX⟩ := h
    exact ⟨t, ht, htX⟩
  have hTb : BddAbove T := ⟨1, fun t ht => ht.1.2⟩
  have hmem := hTc.csSup_mem hTne hTb
  refine ⟨sSup T, hmem.1, hmem.2, fun t' ht' ht'X => ?_⟩
  have := le_csSup hTb ⟨⟨(hmem.1.1.trans ht'.1.le), ht'.2⟩, ht'X⟩
  linarith [ht'.1]

theorem exists_first_notMem_segment {O : Set E3} (hO : IsOpen O) {u v : E3} (hu : u ∈ O)
    (hv : ∃ t ∈ Icc (0 : ℝ) 1, u + t • (v - u) ∉ O) :
    ∃ t ∈ Ioc (0 : ℝ) 1, u + t • (v - u) ∉ O ∧ ∀ t' ∈ Ico 0 t, u + t' • (v - u) ∈ O := by
  set T := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ u + t • (v - u) ∉ O} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (hO.isClosed_compl.preimage (by fun_prop))
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, htO⟩ := hv
    exact ⟨t, ht, htO⟩
  have hTb : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  have hmem := hTc.csInf_mem hTne hTb
  have hpos : 0 < sInf T := by
    rcases hmem.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hmem.2
      rw [← h, zero_smul, add_zero]
      exact hu
  refine ⟨sInf T, ⟨hpos, hmem.1.2⟩, hmem.2, fun t' ht' => ?_⟩
  by_contra hno
  have := csInf_le hTb ⟨⟨ht'.1, (ht'.2.le.trans hmem.1.2)⟩, hno⟩
  linarith [ht'.2]

theorem inter_ball_eq_of_frontier_subset_plane_of_mem_interior {X : Set E3} {a n q : E3}
    {ρ : ℝ} (hXc : IsClosed X) (ha : a ∈ frontier X) (hn : n ≠ 0)
    (hfr : frontier X ∩ ball a ρ ⊆ {x | inner ℝ n (x - a) = 0}) (hq : q ∈ ball a ρ)
    (hqn : inner ℝ n (q - a) < 0) (hqX : q ∈ interior X) :
    X ∩ ball a ρ = {x | inner ℝ n (x - a) ≤ 0} ∩ ball a ρ := by
  have hρ : 0 < ρ := pos_of_mem_ball hq
  have hnn : 0 < inner ℝ n n := real_inner_self_pos.mpr hn
  set Hp := {x : E3 | 0 < inner ℝ n (x - a)} ∩ ball a ρ with hHp
  set Hm := {x : E3 | inner ℝ n (x - a) < 0} ∩ ball a ρ with hHm
  have hHpc : IsPreconnected Hp := by
    have h1 : {x : E3 | 0 < inner ℝ n (x - a)} = {x | inner ℝ n a < innerₗ E3 n x} := by
      ext x
      simp only [mem_ofPred_eq, innerₗ_apply_apply, inner_sub_right, sub_pos]
    rw [hHp, h1]
    exact ((convex_halfSpace_gt (innerₗ E3 n).isLinear _).inter (convex_ball a ρ)).isPreconnected
  have hHmc : IsPreconnected Hm := by
    have h1 : {x : E3 | inner ℝ n (x - a) < 0} = {x | innerₗ E3 n x < inner ℝ n a} := by
      ext x
      simp only [mem_ofPred_eq, innerₗ_apply_apply, inner_sub_right, sub_neg]
    rw [hHm, h1]
    exact ((convex_halfSpace_lt (innerₗ E3 n).isLinear _).inter (convex_ball a ρ)).isPreconnected
  have hdisj : ∀ H ⊆ ball a ρ, H ⊆ {x | inner ℝ n (x - a) ≠ 0} → Disjoint H (frontier X) :=
    fun H hHb hH0 => Set.disjoint_left.mpr fun x hxH hxF =>
      hH0 hxH (hfr ⟨hxF, hHb hxH⟩)
  have hHmX : Hm ⊆ interior X := by
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hXc hHmc
      (hdisj Hm inter_subset_right fun x hx => hx.1.ne) with h | h
    · exact h
    · exact absurd (interior_subset hqX) (h ⟨hqn, hq⟩)
  have hplane : ∀ x ∈ ball a ρ, inner ℝ n (x - a) = 0 → x ∈ X := by
    intro x hxb heq
    rw [← hXc.closure_eq]
    have hdx : 0 < ρ - dist x a := sub_pos.mpr (mem_ball.mp hxb)
    refine mem_closure_iff.mpr fun U hU hxU => ?_
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hxU
    set t := min r (ρ - dist x a) / (2 * (‖n‖ + 1)) with ht
    have ht0 : 0 < t := div_pos (lt_min hr hdx) (by positivity)
    have hdist : dist (x - t • n) x < min r (ρ - dist x a) := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht0, ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg n, lt_min hr hdx]
    have hmb : x - t • n ∈ ball a ρ := by
      rw [mem_ball]
      have := dist_triangle (x - t • n) x a
      have := min_le_right r (ρ - dist x a)
      linarith
    have hneg : inner ℝ n (x - t • n - a) < 0 := by
      have : x - t • n - a = (x - a) - t • n := by abel
      rw [this, inner_sub_right, heq, real_inner_smul_right]
      nlinarith
    exact ⟨x - t • n, hrU (lt_of_lt_of_le hdist (min_le_left _ _)),
      interior_subset (hHmX ⟨hneg, hmb⟩)⟩
  have hHpX : Hp ⊆ Xᶜ := by
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hXc hHpc
      (hdisj Hp inter_subset_right fun x hx => hx.1.ne') with h | h
    · exfalso
      apply ha.2
      refine interior_maximal (fun x hxb => ?_) isOpen_ball (mem_ball_self hρ)
      rcases lt_trichotomy (inner ℝ n (x - a)) 0 with h' | h' | h'
      · exact interior_subset (hHmX ⟨h', hxb⟩)
      · exact hplane x hxb h'
      · exact interior_subset (h ⟨h', hxb⟩)
    · exact h
  ext x
  constructor
  · rintro ⟨hxX, hxb⟩
    refine ⟨?_, hxb⟩
    change inner ℝ n (x - a) ≤ 0
    by_contra hpos
    push Not at hpos
    exact hHpX ⟨hpos, hxb⟩ hxX
  · rintro ⟨hle, hxb⟩
    change inner ℝ n (x - a) ≤ 0 at hle
    refine ⟨?_, hxb⟩
    rcases hle.lt_or_eq with hlt | heq
    · exact interior_subset (hHmX ⟨hlt, hxb⟩)
    · exact hplane x hxb heq

theorem exists_flat_of_mem_frontier_of_mem_segment {X : Set E3} (hX : IsPLBall 3 X)
    (L : Geometry.SimplicialComplex ℝ E3) [Finite L.faces] (hL : L.space = frontier X)
    {nrm g : Finset E3 → E3}
    (hnrm : ∀ τ ∈ L.faces, τ.card = 3 → nrm τ ≠ 0 ∧
      ∀ x ∈ convexHull ℝ (τ : Set E3), inner ℝ (nrm τ) (x - g τ) = 0)
    {u v : E3} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (haX : u + t • (v - u) ∈ frontier X)
    (hedge : ∀ σ ∈ L.faces, σ.card ≤ 2 →
      Disjoint (segment ℝ u v) (convexHull ℝ (σ : Set E3)))
    (hu : ∀ τ ∈ L.faces, τ.card = 3 → inner ℝ (nrm τ) (u - g τ) ≠ 0)
    (hside : (∃ ε > 0, ∀ s, t < s → s < t + ε → u + s • (v - u) ∉ X) ∨
      (∃ ε > 0, ∀ s, t - ε < s → s < t → u + s • (v - u) ∈ interior X)) :
    ∃ ρ > 0, ∃ n : E3, 0 < inner ℝ n (v - u) ∧
      X ∩ ball (u + t • (v - u)) ρ =
        {x | inner ℝ n (x - (u + t • (v - u))) ≤ 0} ∩ ball (u + t • (v - u)) ρ := by
  set a := u + t • (v - u) with hadef
  have hXc : IsClosed X := hX.isPolyhedron.isClosed
  have hint : interior L.space = ∅ := by rw [hL]; exact interior_frontier hXc
  have haseg : a ∈ segment ℝ u v := by
    rw [segment_eq_image']
    exact ⟨t, ⟨ht0.le, ht1.le⟩, rfl⟩
  obtain ⟨τ, hτ, hτ3, haτ, ρ, hρ, hsub⟩ :=
    exists_card_eq_three_inter_ball_subset L hint (hL ▸ haX) haseg hedge
  obtain ⟨hn0, hplane⟩ := hnrm τ hτ hτ3
  have hfr : frontier X ∩ ball a ρ ⊆ {x | inner ℝ (nrm τ) (x - a) = 0} := by
    rintro x ⟨hxF, hxb⟩
    have hx := hplane x (hsub ⟨hL ▸ hxF, hxb⟩)
    have ha := hplane a haτ
    change inner ℝ (nrm τ) (x - a) = 0
    have : x - a = (x - g τ) - (a - g τ) := by abel
    rw [this, inner_sub_right, hx, ha, sub_zero]
  have hc : inner ℝ (nrm τ) (v - u) ≠ 0 := by
    intro hc0
    apply hu τ hτ hτ3
    have ha := hplane a haτ
    have : a - g τ = (u - g τ) + t • (v - u) := by rw [hadef]; abel
    rw [this, inner_add_right, real_inner_smul_right, hc0, mul_zero, add_zero] at ha
    exact ha
  set n := if 0 < inner ℝ (nrm τ) (v - u) then nrm τ else -nrm τ with hndef
  have hnpos : 0 < inner ℝ n (v - u) := by
    rw [hndef]
    split_ifs with h
    · exact h
    · rw [inner_neg_left]
      push Not at h
      exact neg_pos.mpr (lt_of_le_of_ne h hc)
  have hn0' : n ≠ 0 := by
    rw [hndef]
    split_ifs
    · exact hn0
    · exact neg_ne_zero.mpr hn0
  have hfr' : frontier X ∩ ball a ρ ⊆ {x | inner ℝ n (x - a) = 0} := by
    intro x hx
    have h0 : inner ℝ (nrm τ) (x - a) = 0 := hfr hx
    change inner ℝ n (x - a) = 0
    rw [hndef]
    split_ifs
    · exact h0
    · rw [inner_neg_left, h0, neg_zero]
  have hvu : 0 < ‖v - u‖ := norm_pos_iff.mpr (by
    intro h0
    rw [h0, inner_zero_right] at hnpos
    exact lt_irrefl _ hnpos)
  set δ := ρ / (2 * (‖v - u‖ + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hρ (by positivity)
  have hdist : ∀ s : ℝ, |s - t| ≤ δ → u + s • (v - u) ∈ ball a ρ := by
    intro s hs
    rw [mem_ball, dist_eq_norm, hadef]
    have : u + s • (v - u) - (u + t • (v - u)) = (s - t) • (v - u) := by rw [sub_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs]
    calc |s - t| * ‖v - u‖ ≤ δ * ‖v - u‖ := by gcongr
      _ < ρ := by
        rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  have hinner : ∀ s : ℝ, inner ℝ n (u + s • (v - u) - a) = (s - t) * inner ℝ n (v - u) := by
    intro s
    have : u + s • (v - u) - a = (s - t) • (v - u) := by rw [hadef, sub_smul]; abel
    rw [this, real_inner_smul_right]
  refine ⟨ρ, hρ, n, hnpos, ?_⟩
  rcases hside with ⟨ε, hε, hside⟩ | ⟨ε, hε, hside⟩
  · set s := t + min (ε / 2) δ with hs
    have hm : 0 < min (ε / 2) δ := lt_min (half_pos hε) hδ0
    have hs1 : t < s := by rw [hs]; linarith
    have hs2 : s < t + ε := by rw [hs]; linarith [min_le_left (ε / 2) δ]
    refine inter_ball_eq_of_frontier_subset_plane hXc (hX.closure_interior_of_finrank (by simp))
      haX hn0' hfr' (hdist s ?_) ?_ (hside s hs1 hs2)
    · rw [hs, add_sub_cancel_left, abs_of_pos hm]
      exact min_le_right _ _
    · rw [hinner]
      exact mul_pos (by linarith) hnpos
  · set s := t - min (ε / 2) δ with hs
    have hm : 0 < min (ε / 2) δ := lt_min (half_pos hε) hδ0
    have hs1 : t - ε < s := by rw [hs]; linarith [min_le_left (ε / 2) δ]
    have hs2 : s < t := by rw [hs]; linarith
    refine inter_ball_eq_of_frontier_subset_plane_of_mem_interior hXc haX hn0' hfr'
      (hdist s ?_) ?_ (hside s hs1 hs2)
    · rw [hs, sub_sub_cancel_left, abs_neg, abs_of_pos hm]
      exact min_le_right _ _
    · rw [hinner]
      exact mul_neg_of_neg_of_pos (by linarith) hnpos

end DifferentialGeometry.Topology.PiecewiseLinear
