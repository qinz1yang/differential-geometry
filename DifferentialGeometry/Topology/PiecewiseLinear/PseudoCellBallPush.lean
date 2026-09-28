/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.ChartPush
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellFlatChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem exists_side_of_regular_closed_chart {C U : Set E3}
    {V : Set (ℝ × ℝ × ℝ)} {φ : E3 → ℝ × ℝ × ℝ}
    (hCc : IsClosed C) (hreg : closure (interior C) = C)
    (hφ : IsPLHomeomorphOn φ U V) (hU : IsOpen U) {x : E3} (hx : x ∈ U)
    (hxC : x ∈ frontier C) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (φ x) r ⊆ V)
    (hUC : ∀ y ∈ U, y ∈ frontier C ↔ (φ y).2.2 = (φ x).2.2) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ y ∈ U, φ y ∈ Metric.ball (φ x) r →
      (y ∈ C ↔ 0 ≤ s * ((φ y).2.2 - (φ x).2.2)) := by
  let g := Function.invFunOn φ U
  have hg : IsPLHomeomorphOn g V U := hφ.symm
  have hgφ : ∀ y ∈ U, g (φ y) = y := fun y hy => hφ.bijOn.invOn_invFunOn.1 hy
  have hφg : ∀ w ∈ V, φ (g w) = w := fun w hw => hφ.bijOn.invOn_invFunOn.2 hw
  let c₀ := (φ x).2.2
  let B := Metric.ball (φ x) r
  have hBV : B ⊆ V := Metric.ball_subset_closedBall.trans hball
  have hhalf : ∀ t : ℝ,
      IsPreconnected (g '' (B ∩ {w | 0 < t * (w.2.2 - c₀)})) ∧
      g '' (B ∩ {w | 0 < t * (w.2.2 - c₀)}) ⊆ interior C ∪ Cᶜ := by
    intro t
    have hlin : IsLinearMap ℝ fun w : ℝ × ℝ × ℝ => t * w.2.2 :=
      ⟨fun a b => by simp [mul_add], fun c a => by simp; ring⟩
    have hconv : Convex ℝ (B ∩ {w : ℝ × ℝ × ℝ | 0 < t * (w.2.2 - c₀)}) := by
      refine (convex_ball _ _).inter ?_
      have heq : {w : ℝ × ℝ × ℝ | 0 < t * (w.2.2 - c₀)} =
          {w | t * c₀ < t * w.2.2} := by
        ext w
        simp only [mem_ofPred_eq]
        constructor <;> intro hw <;> nlinarith
      rw [heq]
      exact convex_halfSpace_gt hlin _
    refine ⟨hconv.isPreconnected.image g
      (hg.isPiecewiseAffineOn.continuousOn.mono (inter_subset_left.trans hBV)), ?_⟩
    rintro _ ⟨w, ⟨hwB, hw⟩, rfl⟩
    by_cases hwC : g w ∈ C
    · left
      apply (mem_interior_iff_notMem_frontier hwC).mpr
      intro hwfr
      have hz := (hUC (g w) (hg.bijOn.mapsTo (hBV hwB))).mp hwfr
      rw [hφg w (hBV hwB)] at hz
      change w.2.2 = c₀ at hz
      simp only [mem_ofPred_eq, hz, sub_self, mul_zero, lt_self_iff_false] at hw
    · exact Or.inr hwC
  have hside : ∀ t : ℝ,
      g '' (B ∩ {w | 0 < t * (w.2.2 - c₀)}) ⊆ interior C ∨
      g '' (B ∩ {w | 0 < t * (w.2.2 - c₀)}) ⊆ Cᶜ := by
    intro t
    exact (hhalf t).1.subset_or_subset isOpen_interior hCc.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) (hhalf t).2
  have hBg : U ∩ φ ⁻¹' B ∈ 𝓝 x := Filter.inter_mem (hU.mem_nhds hx)
    ((hφ.isPiecewiseAffineOn.continuousAt hU hx).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr))
  have hhalfmem : ∀ z ∈ U, φ z ∈ B → ∀ t : ℝ, 0 < t * ((φ z).2.2 - c₀) →
      z ∈ g '' (B ∩ {w | 0 < t * (w.2.2 - c₀)}) := fun z hz hzB t ht =>
    ⟨φ z, ⟨hzB, ht⟩, hgφ z hz⟩
  have hxcl : x ∈ closure (interior C) := hreg.symm ▸ hCc.frontier_subset hxC
  obtain ⟨y, ⟨hyU, hyB⟩, hyC⟩ := mem_closure_iff_nhds.mp hxcl _ hBg
  obtain ⟨y', ⟨hy'U, hy'B⟩, hy'C⟩ := mem_closure_iff_nhds.mp
    (frontier_eq_closure_inter_closure.subset hxC).2 _ hBg
  have hy0 : (φ y).2.2 ≠ c₀ := fun hz =>
    Set.disjoint_left.mp disjoint_interior_frontier hyC ((hUC y hyU).mpr hz)
  have hy'0 : (φ y').2.2 ≠ c₀ := fun hz =>
    hy'C (hCc.frontier_subset ((hUC y' hy'U).mpr hz))
  have hsign : ∀ a : ℝ, a ≠ 0 → ∃ t : ℝ, (t = 1 ∨ t = -1) ∧ 0 < t * a := by
    intro a ha
    rcases lt_or_gt_of_ne ha with hlt | hgt
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  obtain ⟨t, ht, hty⟩ := hsign _ (sub_ne_zero.mpr hy0)
  have ht0 : t ≠ 0 := by rcases ht with rfl | rfl <;> norm_num
  have hpos : g '' (B ∩ {w | 0 < t * (w.2.2 - c₀)}) ⊆ interior C := by
    rcases hside t with h | h
    · exact h
    · exact (h (hhalfmem y hyU hyB t hty) (interior_subset hyC)).elim
  have hy't : ¬ 0 < t * ((φ y').2.2 - c₀) := fun hz =>
    hy'C (interior_subset (hpos (hhalfmem y' hy'U hy'B t hz)))
  have hy'neg : 0 < -t * ((φ y').2.2 - c₀) := by
    have hne := mul_ne_zero ht0 (sub_ne_zero.mpr hy'0)
    have := lt_of_le_of_ne (not_lt.mp hy't) hne
    linarith
  have hneg : g '' (B ∩ {w | 0 < -t * (w.2.2 - c₀)}) ⊆ Cᶜ := by
    rcases hside (-t) with h | h
    · exact (hy'C (interior_subset (h (hhalfmem y' hy'U hy'B (-t) hy'neg)))).elim
    · exact h
  refine ⟨t, ht, fun z hz hzB => ⟨fun hzC => ?_, fun hz0 => ?_⟩⟩
  · by_contra hn
    have hn' : 0 < -t * ((φ z).2.2 - c₀) := by linarith [not_le.mp hn]
    exact hneg (hhalfmem z hz hzB (-t) hn') hzC
  · rcases hz0.lt_or_eq with hpos' | hzero
    · exact interior_subset (hpos (hhalfmem z hz hzB t hpos'))
    · have h0 : (φ z).2.2 = c₀ := by
        have := (mul_eq_zero.mp hzero.symm).resolve_left ht0
        linarith
      exact hCc.frontier_subset ((hUC z hz).mpr h0)

theorem IsPseudoCell.exists_push_of_ball_frontier {Ec Eint Ebd C Z O : Set E3} {P : E3}
    (hpc : IsPseudoCell Ec Eint Ebd P) (hC : IsPLBall 3 C) (hZ : IsCompact Z)
    (hZE : Z ⊆ Eint \ {P}) (hO : IsOpen O) (hZO : Z ⊆ O)
    (hfront : O ∩ Ec = O ∩ frontier C) :
    ∃ Φ : E3 → E3, IsPLHomeomorphOn Φ univ univ ∧ (∀ y, y ∉ O → Φ y = y) ∧
      ∀ y ∈ C, Φ y ∈ C ∧ (Φ y ∈ Ec → y ∉ Z ∧ Φ y = y) := by
  have hloc : ∀ x ∈ Z, ∃ (Ψ : E3 → E3) (W : Set E3),
      IsPLHomeomorphOn Ψ univ univ ∧ W ∈ 𝓝 x ∧
      (∀ y, y ∉ O → Ψ y = y) ∧ (∀ y, Ψ y ∈ (∅ : Set E3) ↔ y ∈ (∅ : Set E3)) ∧
      ∀ y ∈ C, Ψ y ∈ C ∧ (Ψ y ∈ Ec → y ∈ Ec ∧ y ∉ W ∧ Ψ y = y) := by
    intro x hx
    obtain ⟨U, V, φ, hU, hV, hxU, hUO, hφ, hE⟩ :=
      hpc.exists_flatChart (hZE hx).1 (hZE hx).2 (hO.mem_nhds (hZO hx))
    have hxE : x ∈ Ec := hpc.carrierEq.symm ▸ Or.inl (hZE hx).1
    have hφx : (φ x).2.2 = 0 := (hE x hxU).mp hxE
    have hUE : ∀ y ∈ U, y ∈ Ec ↔ (φ y).2.2 = (φ x).2.2 := by
      intro y hy
      rw [hφx]
      exact hE y hy
    have hUC : ∀ y ∈ U, y ∈ frontier C ↔ (φ y).2.2 = (φ x).2.2 := by
      intro y hy
      rw [← hUE y hy]
      exact ⟨fun hyC => (hfront.symm.subset ⟨hUO hy, hyC⟩).2,
        fun hyE => (hfront.subset ⟨hUO hy, hyE⟩).2⟩
    obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV (φ x) (hφ.bijOn.mapsTo hxU)
    have hr : 0 < ε / 2 := half_pos hε
    have hball : Metric.closedBall (φ x) (ε / 2) ⊆ V :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεV
    obtain ⟨s, hs, hside⟩ := exists_side_of_regular_closed_chart hC.isPolyhedron.isClosed
      hC.closure_interior hφ hU hxU ((hfront.subset ⟨hZO hx, hxE⟩).2) hr hball hUC
    obtain ⟨Ψ, W, hΨ, hW, hΨU, hΨX, hΨC⟩ :=
      exists_isPLHomeomorphOn_push_of_chart hU hφ hxU hr hball hs
        (fun y hy _ => hUE y hy) hside (X := ∅) (by intros; rfl)
    exact ⟨Ψ, W, hΨ, hW, fun y hy => hΨU y fun hyU => hy (hUO hyU), hΨX, hΨC⟩
  obtain ⟨Φ, hΦ, hΦO, -, hΦC⟩ := exists_isPLHomeomorphOn_push_of_forall hZ hloc
  exact ⟨Φ, hΦ, hΦO, hΦC⟩

theorem IsPseudoCell.exists_disk_push_of_ball_frontier {Ec Eint Ebd C Z O Δ : Set E3}
    {P : E3} (hpc : IsPseudoCell Ec Eint Ebd P) (hC : IsPLBall 3 C) (hZ : IsCompact Z)
    (hZE : Z ⊆ Eint \ {P}) (hO : IsOpen O) (hZO : Z ⊆ O)
    (hfront : O ∩ Ec = O ∩ frontier C) {r : (Fin 3 → ℝ) → E3}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hΔC : Δ ∩ O ⊆ C) (hΔZ : Δ ∩ O ∩ Ec ⊆ Z)
    (hbdO : Disjoint (r '' stdSimplexBoundary 2) O) :
    ∃ (Δ' : Set E3) (q : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ' ∧
      q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
      Δ' ⊆ Δ ∪ O ∧ Δ' ∩ Ec = (Δ \ O) ∩ Ec := by
  obtain ⟨Φ, hΦ, hΦO, hΦC⟩ := hpc.exists_push_of_ball_frontier hC hZ hZE hO hZO hfront
  have hmapO : ∀ y ∈ O, Φ y ∈ O := by
    intro y hy
    by_contra hn
    have hyy := hΦ.bijOn.injOn (mem_univ y) (mem_univ (Φ y)) (hΦO (Φ y) hn).symm
    exact hn (hyy ▸ hy)
  have hΦΔ := hΦ.restrict (show IsPLBall 2 Δ from ⟨r, hr⟩).isPolyhedron (subset_univ Δ)
  have hfix : EqOn Φ id (r '' stdSimplexBoundary 2) :=
    fun y hy => hΦO y (Set.disjoint_left.mp hbdO hy)
  refine ⟨Φ '' Δ, Φ ∘ r, hr.trans hΦΔ, ?_, ?_, ?_⟩
  · rw [image_comp, hfix.image_eq, image_id]
  · rintro _ ⟨y, hy, rfl⟩
    by_cases hyO : y ∈ O
    · exact Or.inr (hmapO y hyO)
    · rw [hΦO y hyO]
      exact Or.inl hy
  · ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxE⟩
      by_cases hxO : x ∈ O
      · obtain ⟨hxZ, hfixx⟩ := (hΦC x (hΔC ⟨hx, hxO⟩)).2 hxE
        rw [hfixx] at hxE
        exact (hxZ (hΔZ ⟨⟨hx, hxO⟩, hxE⟩)).elim
      · rw [hΦO x hxO] at hxE ⊢
        exact ⟨⟨hx, hxO⟩, hxE⟩
    · rintro ⟨⟨hy, hyO⟩, hyE⟩
      exact ⟨⟨y, hy, hΦO y hyO⟩, hyE⟩

end DifferentialGeometry.Topology.PiecewiseLinear
