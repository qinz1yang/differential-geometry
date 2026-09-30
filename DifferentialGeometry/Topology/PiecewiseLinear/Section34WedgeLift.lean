/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.AdaptedCapPrism
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.AdaptedCapSource
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskCircleStep
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_bentDisk_centeredPrism {D A V : Set E3} {q : (Fin 3 → ℝ) → E3}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) {ρ : E3 × ℝ → E3}
    (hρ : IsPLHomeomorphOn ρ ((q '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) A)
    (hρ0 : ∀ x ∈ q '' stdSimplexBoundary 2, ρ (x, 0) = x)
    (hAD : A ∩ D = q '' stdSimplexBoundary 2) (hV : IsOpen V) (hDAV : D ∪ A ⊆ V) :
    ∃ (E₁ : Set (EuclideanSpace ℝ (Fin 2))) (β : EuclideanSpace ℝ (Fin 2) → E3)
      (prism : (Fin 3 → ℝ) × ℝ → E3) (b : EuclideanSpace ℝ (Fin 2) → (Fin 3 → ℝ)),
      IsPLBall 2 E₁ ∧
      IsPLHomeomorphOn β E₁ (D ∪ ρ '' ((q '' stdSimplexBoundary 2) ×ˢ Icc 0 (1 / 2))) ∧
      ContinuousOn prism (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∧
      InjOn prism (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∧
      prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ⊆ V ∧
      (∀ x ∈ E₁, prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∈ 𝓝 (β x)) ∧
      prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(0 : ℝ)}) =
        (D ∪ A) ∩ prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∧
      MapsTo b E₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ∧ IsPiecewiseAffineOn b E₁ ∧
      (∀ x ∈ E₁, prism (b x, 0) = β x) ∧
      ∀ (G : EuclideanSpace ℝ (Fin 2) → (Fin 3 → ℝ) × ℝ) (S : Set (EuclideanSpace ℝ (Fin 2))),
        IsPiecewiseAffineOn G S → MapsTo G S (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) →
          IsPiecewiseAffineOn (prism ∘ G) S := by
  set J := q '' stdSimplexBoundary 2 with hJdef
  have hJpoly : IsPolyhedron J := (hq.isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron
  have hIpoly : IsPolyhedron (J ×ˢ Icc (0 : ℝ) (1 / 2)) := hJpoly.prod isHPolytope_Icc.isPolyhedron
  have hIsub : J ×ˢ Icc (0 : ℝ) (1 / 2) ⊆ J ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono Subset.rfl (Icc_subset_Icc le_rfl (by norm_num))
  have hρh := hρ.restrict hIpoly hIsub
  have hJD : J ⊆ D := (image_mono fun _ hx => hx.1).trans hq.image_eq.subset
  have hAh : ρ '' (J ×ˢ Icc (0 : ℝ) (1 / 2)) ∩ D = J := by
    apply Subset.antisymm
    · exact (inter_subset_inter_left _ ((image_mono hIsub).trans hρ.image_eq.subset)).trans
        hAD.subset
    · intro x hx
      exact ⟨⟨(x, 0), ⟨hx, by norm_num, by norm_num⟩, hρ0 x hx⟩, hJD hx⟩
  obtain ⟨qb, hqb, hqbJ, hqbD⟩ :=
    hq.exists_isPLHomeomorphOn_union_collar (a := 0) (b := 1) one_pos hρ hρ0 hAD
  obtain ⟨qh, hqh, -, -⟩ :=
    hq.exists_isPLHomeomorphOn_union_collar (a := 0) (b := 1 / 2) (by norm_num) hρh hρ0 hAh
  obtain ⟨Pl, β, hPl, hβ, hβfr⟩ := hqb.exists_planarModel
  set Bh := D ∪ ρ '' (J ×ˢ Icc (0 : ℝ) (1 / 2)) with hBhdef
  have hBh : Bh ⊆ D ∪ A :=
    union_subset_union_right _ ((image_mono hIsub).trans hρ.image_eq.subset)
  have hβ' : IsPLHomeomorphOn (Function.invFunOn β Pl) (D ∪ A) Pl := hβ.symm
  have hBhpoly : IsPolyhedron Bh := IsPLBall.isPolyhedron ⟨qh, hqh⟩
  have hβ'h := hβ'.restrict hBhpoly hBh
  set E₁ := Function.invFunOn β Pl '' Bh with hE₁def
  have hE₁ : IsPLBall 2 E₁ := ⟨Function.invFunOn β Pl ∘ qh, hqh.trans hβ'h⟩
  have hE₁Pl : E₁ ⊆ Pl := (image_mono hBh).trans hβ'.image_eq.subset
  have hβE₁ : IsPLHomeomorphOn β E₁ Bh := by
    have h1 := hβ.restrict hE₁.isPolyhedron hE₁Pl
    have h2 : β '' E₁ = Bh := by
      ext y
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        rw [hβ.bijOn.invOn_invFunOn.2 (hBh hz)]
        exact hz
      · intro hy
        exact ⟨Function.invFunOn β Pl y, ⟨y, hy, rfl⟩, hβ.bijOn.invOn_invFunOn.2 (hBh hy)⟩
    rwa [h2] at h1
  have hPlc : IsClosed Pl := hPl.isPolyhedron.isClosed
  have hE₁int : E₁ ⊆ interior Pl := by
    intro z hz
    have hzPl := hE₁Pl hz
    refine (mem_interior_iff_notMem_frontier hzPl).mpr fun hzfr => ?_
    have hβz : β z ∈ ρ '' (J ×ˢ {(1 : ℝ)}) := by
      rw [← hqbJ, ← hβfr]
      exact mem_image_of_mem β hzfr
    have hβzB : β z ∈ Bh := hβE₁.bijOn.mapsTo hz
    obtain ⟨⟨x, u⟩, ⟨hx, hu⟩, hxu⟩ := hβz
    have hu1 : u = 1 := hu
    rcases hβzB with hD | ⟨⟨x', u'⟩, ⟨hx', hu'⟩, hx'u'⟩
    · have hmem : β z ∈ qb '' stdSimplexBoundary 2 := by
        rw [hqbJ]
        exact ⟨(x, u), ⟨hx, hu⟩, hxu⟩
      exact Set.disjoint_left.mp hqbD hD hmem
    · have heq := hρ.bijOn.injOn (hIsub ⟨hx', hu'⟩) ⟨hx, by rw [hu1]; norm_num⟩
        (hx'u'.trans hxu.symm)
      have hueq : u' = u := congrArg Prod.snd heq
      have h2 := hu'.2
      rw [hueq, hu1] at h2
      norm_num at h2
  have hβpl : IsPLOn 2 3 β Pl := isPLOn_iff_isPiecewiseAffineOn.mpr hβ.isPiecewiseAffineOn
  have hβV : β '' Pl ⊆ V := by
    rw [hβ.image_eq]
    exact hDAV
  obtain ⟨prism, b, hPc, hPi, hPV, hPn, hPcen, hbm, hbpa, hbβ, hPpl⟩ :=
    exists_centeredPrism_of_isPLOn hE₁ hPl hE₁int hβpl hβ.bijOn.injOn hV hβV
  refine ⟨E₁, β, prism, b, hE₁, hβE₁, hPc, hPi, hPV, hPn, ?_, hbm, hbpa, hbβ, fun G S hG hGS =>
    isPLOn_iff_isPiecewiseAffineOn.mp (hPpl G S hG hGS)⟩
  rw [hPcen, hβ.image_eq]

theorem exists_prism_side_of_bentChart {C U : Set E3} {prism : (Fin 3 → ℝ) × ℝ → E3}
    (hPc : ContinuousOn prism (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1))
    (hPi : InjOn prism (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1))
    (hCen : prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(0 : ℝ)}) =
      C ∩ prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1))
    {a₀ : Fin 3 → ℝ} (ha₀ : a₀ ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
    (hN : prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∈ 𝓝 (prism (a₀, 0)))
    {φ : E3 → ℝ × ℝ × ℝ} {r ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hU : IsOpen U)
    (hpU : prism (a₀, 0) ∈ U) (hr : 0 < r) (hφ : IsPLHomeomorphOn φ U (Metric.ball 0 r))
    (hφp : φ (prism (a₀, 0)) = 0)
    (hC : ∀ y ∈ U, y ∈ C ↔
      ((φ y).2.2 = 0 ∧ (φ y).2.1 ≤ 0) ∨ ((φ y).2.1 = 0 ∧ 0 ≤ ε * (φ y).2.2)) :
    ∃ (s : ℝ) (O : Set E3), (s = 1 ∨ s = -1) ∧ IsOpen O ∧ prism (a₀, 0) ∈ O ∧ O ⊆ U ∧
      (∀ a ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), ∀ t ∈ Ioc (0 : ℝ) 1, prism (a, s * t) ∈ O →
        (φ (prism (a, s * t))).2.1 < 0 ∧ 0 < ε * (φ (prism (a, s * t))).2.2) ∧
      (∀ a ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), ∀ t ∈ Ioc (0 : ℝ) 1, prism (a, -s * t) ∈ O →
        0 < (φ (prism (a, -s * t))).2.1 ∨ ε * (φ (prism (a, -s * t))).2.2 < 0) := by
  classical
  set Δ := Convexity.StdSimplex.coordinateSet ℝ (Fin 3) with hΔdef
  set N := prism '' (Δ ×ˢ Icc (-1 : ℝ) 1) with hNdef
  set p := prism (a₀, 0) with hpdef
  set ψ := Function.invFunOn φ U with hψdef
  have hψc : ContinuousOn ψ (Metric.ball 0 r) := hφ.isPiecewiseAffineOn_invFunOn.continuousOn
  have hψ0 : ψ 0 = p := by
    rw [← hφp]
    exact hφ.bijOn.invOn_invFunOn.1 hpU
  have hφψ : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r, φ (ψ z) = z := fun z hz =>
    hφ.bijOn.invOn_invFunOn.2 hz
  have hψU : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r, ψ z ∈ U := fun z hz =>
    hφ.symm.bijOn.mapsTo hz
  obtain ⟨r', hr', hr'r, hsubN⟩ : ∃ r', 0 < r' ∧ r' ≤ r ∧ ψ '' Metric.ball 0 r' ⊆ N := by
    have hcont : ContinuousAt ψ 0 := hψc.continuousAt (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hr))
    have hpre : ψ ⁻¹' N ∈ 𝓝 (0 : ℝ × ℝ × ℝ) := hcont (by rw [hψ0]; exact hN)
    obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp hpre
    refine ⟨min e r, lt_min he hr, min_le_right _ _, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hball (Metric.ball_subset_ball (min_le_left _ _) hz)
  have hballr : Metric.ball (0 : ℝ × ℝ × ℝ) r' ⊆ Metric.ball 0 r := Metric.ball_subset_ball hr'r
  set O := ψ '' Metric.ball (0 : ℝ × ℝ × ℝ) r' with hOdef
  have hOo : IsOpen O := hφ.symm.isOpen_image_of_isOpen hU Metric.isOpen_ball hballr
  have hpO : p ∈ O := ⟨0, Metric.mem_ball_self hr', hψ0⟩
  have hOU : O ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hψU z (hballr hz)
  have hΔc : IsCompact Δ := Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)
  set Kup := prism '' (Δ ×ˢ Icc (0 : ℝ) 1) with hKupdef
  set Klo := prism '' (Δ ×ˢ Icc (-1 : ℝ) 0) with hKlodef
  have hupsub : Δ ×ˢ Icc (0 : ℝ) 1 ⊆ Δ ×ˢ Icc (-1 : ℝ) 1 :=
    prod_mono Subset.rfl (Icc_subset_Icc (by norm_num) le_rfl)
  have hlosub : Δ ×ˢ Icc (-1 : ℝ) 0 ⊆ Δ ×ˢ Icc (-1 : ℝ) 1 :=
    prod_mono Subset.rfl (Icc_subset_Icc le_rfl (by norm_num))
  have hKupc : IsClosed Kup :=
    ((hΔc.prod isCompact_Icc).image_of_continuousOn (hPc.mono hupsub)).isClosed
  have hKloc : IsClosed Klo :=
    ((hΔc.prod isCompact_Icc).image_of_continuousOn (hPc.mono hlosub)).isClosed
  have hNcov : N ⊆ Kup ∪ Klo := by
    rintro _ ⟨⟨a, t⟩, ⟨ha, ht⟩, rfl⟩
    rcases le_total 0 t with h0 | h0
    · exact Or.inl ⟨(a, t), ⟨ha, h0, ht.2⟩, rfl⟩
    · exact Or.inr ⟨(a, t), ⟨ha, ht.1, h0⟩, rfl⟩
  have hoff : ∀ a ∈ Δ, ∀ t ∈ Icc (-1 : ℝ) 1, t ≠ 0 → prism (a, t) ∉ C := by
    intro a ha t ht ht0 hC'
    have hmem : prism (a, t) ∈ C ∩ N := ⟨hC', ⟨(a, t), ⟨ha, ht⟩, rfl⟩⟩
    rw [← hCen] at hmem
    obtain ⟨⟨a', t'⟩, ⟨ha', ht'⟩, heq⟩ := hmem
    have ht'0 : t' = 0 := ht'
    have h := hPi ⟨ha', by rw [ht'0]; norm_num⟩ ⟨ha, ht⟩ heq
    exact ht0 ((congrArg Prod.snd h).symm.trans ht'0)
  have hKint : ∀ y ∈ Kup, y ∈ Klo → y ∈ C := by
    rintro _ ⟨⟨a, t⟩, ⟨ha, ht⟩, rfl⟩ ⟨⟨a', t'⟩, ⟨ha', ht'⟩, heq⟩
    have h := hPi (hlosub ⟨ha', ht'⟩) (hupsub ⟨ha, ht⟩) heq
    have hteq : t' = t := congrArg Prod.snd h
    have ht0 : t = 0 := le_antisymm (hteq ▸ ht'.2) ht.1
    have hmem : prism (a, t) ∈ C ∩ N := by
      rw [← hCen]
      exact ⟨(a, t), ⟨ha, ht0⟩, rfl⟩
    exact hmem.1
  have hsplit : ∀ X : Set E3, IsPreconnected X → X ⊆ N → (∀ y ∈ X, y ∉ C) →
      X ⊆ Kup ∨ X ⊆ Klo := by
    intro X hX hXN hXC
    refine isPreconnected_iff_subset_of_disjoint_closed.mp hX Kup Klo hKupc hKloc
      (hXN.trans hNcov) ?_
    refine eq_empty_iff_forall_notMem.mpr fun y ⟨hyX, hyu, hyl⟩ => hXC y hyX ?_
    exact hKint y hyu hyl
  set Wz : Set (ℝ × ℝ × ℝ) := Metric.ball 0 r' ∩ {z | z.2.1 < 0 ∧ 0 < ε * z.2.2} with hWzdef
  set R₁ : Set (ℝ × ℝ × ℝ) := Metric.ball 0 r' ∩ {z | 0 < z.2.1} with hR₁def
  set R₂ : Set (ℝ × ℝ × ℝ) := Metric.ball 0 r' ∩ {z | ε * z.2.2 < 0} with hR₂def
  have hWzc : IsPreconnected Wz := by
    refine (Convex.inter (convex_ball 0 r') ?_).isPreconnected
    intro a ha b hb s t hs ht hst
    have ha1 : a.2.1 < 0 := ha.1
    have ha2 : 0 < ε * a.2.2 := ha.2
    have hb1 : b.2.1 < 0 := hb.1
    have hb2 : 0 < ε * b.2.2 := hb.2
    refine ⟨?_, ?_⟩
    · change s * a.2.1 + t * b.2.1 < 0
      rcases eq_or_lt_of_le hs with hs0 | hs0
      · rw [← hs0] at hst ⊢
        have ht1 : t = 1 := by linarith
        rw [ht1]
        linarith
      · have h1 : s * a.2.1 < 0 := mul_neg_of_pos_of_neg hs0 ha1
        have h2 : t * b.2.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hb1.le
        linarith
    · change 0 < ε * (s * a.2.2 + t * b.2.2)
      have heq : ε * (s * a.2.2 + t * b.2.2) = s * (ε * a.2.2) + t * (ε * b.2.2) := by ring
      rw [heq]
      rcases eq_or_lt_of_le hs with hs0 | hs0
      · rw [← hs0] at hst ⊢
        have ht1 : t = 1 := by linarith
        rw [ht1]
        linarith
      · have h1 : 0 < s * (ε * a.2.2) := mul_pos hs0 ha2
        have h2 : 0 ≤ t * (ε * b.2.2) := mul_nonneg ht hb2.le
        linarith
  have hR₁c : IsPreconnected R₁ := by
    refine (Convex.inter (convex_ball 0 r') ?_).isPreconnected
    intro a ha b hb s t hs ht hst
    have ha1 : 0 < a.2.1 := ha
    have hb1 : 0 < b.2.1 := hb
    change 0 < s * a.2.1 + t * b.2.1
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · rw [← hs0] at hst ⊢
      have ht1 : t = 1 := by linarith
      rw [ht1]
      linarith
    · have h1 : 0 < s * a.2.1 := mul_pos hs0 ha1
      have h2 : 0 ≤ t * b.2.1 := mul_nonneg ht hb1.le
      linarith
  have hR₂c : IsPreconnected R₂ := by
    refine (Convex.inter (convex_ball 0 r') ?_).isPreconnected
    intro a ha b hb s t hs ht hst
    have ha2 : ε * a.2.2 < 0 := ha
    have hb2 : ε * b.2.2 < 0 := hb
    change ε * (s * a.2.2 + t * b.2.2) < 0
    have heq : ε * (s * a.2.2 + t * b.2.2) = s * (ε * a.2.2) + t * (ε * b.2.2) := by ring
    rw [heq]
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · rw [← hs0] at hst ⊢
      have ht1 : t = 1 := by linarith
      rw [ht1]
      linarith
    · have h1 : s * (ε * a.2.2) < 0 := mul_neg_of_pos_of_neg hs0 ha2
      have h2 : t * (ε * b.2.2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hb2.le
      linarith
  have hx₀ : ((0 : ℝ), r' / 4, -(ε * (r' / 4))) ∈ R₁ ∩ R₂ := by
    have hr4 : (0 : ℝ) < r' / 4 := by positivity
    have habs : |-(ε * (r' / 4))| = r' / 4 := by
      rw [abs_neg, abs_mul, abs_of_pos hr4]
      rcases hε with rfl | rfl <;> simp
    have hnorm : ‖((0 : ℝ), r' / 4, -(ε * (r' / 4)))‖ < r' := by
      rw [Prod.norm_def, Prod.norm_def]
      simp only [norm_zero, Real.norm_eq_abs]
      rw [habs, abs_of_pos hr4, max_self]
      exact max_lt hr' (by linarith)
    have hball : ((0 : ℝ), r' / 4, -(ε * (r' / 4))) ∈ Metric.ball (0 : ℝ × ℝ × ℝ) r' := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hnorm
    refine ⟨⟨hball, hr4⟩, hball, ?_⟩
    change ε * -(ε * (r' / 4)) < 0
    rcases hε with rfl | rfl <;> linarith
  have hRzc : IsPreconnected (R₁ ∪ R₂) := hR₁c.union _ hx₀.1 hx₀.2 hR₂c
  have hWc : IsPreconnected (ψ '' Wz) :=
    hWzc.image ψ (hψc.mono (inter_subset_left.trans hballr))
  have hRball : R₁ ∪ R₂ ⊆ Metric.ball 0 r' := union_subset inter_subset_left inter_subset_left
  have hRc : IsPreconnected (ψ '' (R₁ ∪ R₂)) :=
    hRzc.image ψ (hψc.mono (hRball.trans hballr))
  have hWN : ψ '' Wz ⊆ N := (image_mono inter_subset_left).trans hsubN
  have hRN : ψ '' (R₁ ∪ R₂) ⊆ N := (image_mono hRball).trans hsubN
  have hWC : ∀ y ∈ ψ '' Wz, y ∉ C := by
    rintro _ ⟨z, ⟨hzb, hzw⟩, rfl⟩ hyC
    have hzr := hballr hzb
    rw [hC _ (hψU z hzr), hφψ z hzr] at hyC
    have hz1 : z.2.1 < 0 := hzw.1
    have hz2 : 0 < ε * z.2.2 := hzw.2
    rcases hyC with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1, mul_zero] at hz2
      exact lt_irrefl 0 hz2
    · rw [h1] at hz1
      exact lt_irrefl 0 hz1
  have hRC : ∀ y ∈ ψ '' (R₁ ∪ R₂), y ∉ C := by
    rintro _ ⟨z, hz, rfl⟩ hyC
    have hzr := hballr (hRball hz)
    rw [hC _ (hψU z hzr), hφψ z hzr] at hyC
    rcases hz with ⟨-, hz3⟩ | ⟨-, hz3⟩ <;> rcases hyC with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hz3' : 0 < z.2.1 := hz3
      linarith
    · have hz3' : 0 < z.2.1 := hz3
      rw [h1] at hz3'
      exact lt_irrefl 0 hz3'
    · have hz3' : ε * z.2.2 < 0 := hz3
      rw [h1, mul_zero] at hz3'
      exact lt_irrefl 0 hz3'
    · have hz3' : ε * z.2.2 < 0 := hz3
      linarith
  have hcov : ∀ y ∈ O, y ∉ C → y ∈ ψ '' Wz ∨ y ∈ ψ '' (R₁ ∪ R₂) := by
    rintro _ ⟨z, hzb, rfl⟩ hyC
    have hzr := hballr hzb
    rw [hC _ (hψU z hzr), hφψ z hzr] at hyC
    rcases lt_or_ge 0 z.2.1 with hv | hv
    · exact Or.inr ⟨z, Or.inl ⟨hzb, hv⟩, rfl⟩
    rcases lt_or_ge (ε * z.2.2) 0 with hw | hw
    · exact Or.inr ⟨z, Or.inr ⟨hzb, hw⟩, rfl⟩
    rcases eq_or_lt_of_le hv with hv0 | hv0
    · exact absurd (Or.inr ⟨hv0, hw⟩) hyC
    rcases eq_or_lt_of_le hw with hw0 | hw0
    · have hz2 : z.2.2 = 0 := by rcases hε with rfl | rfl <;> linarith
      exact absurd (Or.inl ⟨hz2, hv⟩) hyC
    · exact Or.inl ⟨z, ⟨hzb, hv0, hw0⟩, rfl⟩
  have hcw : ContinuousWithinAt (fun t : ℝ => prism (a₀, t)) (Icc (-1 : ℝ) 1) 0 := by
    have h1 : ContinuousWithinAt prism (Δ ×ˢ Icc (-1 : ℝ) 1) (a₀, 0) :=
      hPc (a₀, 0) ⟨ha₀, by norm_num, by norm_num⟩
    exact h1.comp (Continuous.continuousWithinAt (by fun_prop)) (fun t ht => ⟨ha₀, ht⟩)
  obtain ⟨e, he, hOe⟩ := Metric.mem_nhds_iff.mp (hOo.mem_nhds hpO)
  obtain ⟨δ, hδ, hδe⟩ := Metric.continuousWithinAt_iff.mp hcw e he
  set t₀ := min (δ / 2) 1 with ht₀def
  have ht₀pos : 0 < t₀ := lt_min (half_pos hδ) one_pos
  have ht₀1 : t₀ ≤ 1 := min_le_right _ _
  have ht₀δ : t₀ < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hup : prism (a₀, t₀) ∈ O := by
    refine hOe (hδe ⟨by linarith, ht₀1⟩ ?_)
    rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]
    exact ht₀δ
  have hlo : prism (a₀, -t₀) ∈ O := by
    refine hOe (hδe ⟨by linarith, by linarith⟩ ?_)
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos ht₀pos]
    exact ht₀δ
  have hupC : prism (a₀, t₀) ∉ C := hoff a₀ ha₀ t₀ ⟨by linarith, ht₀1⟩ ht₀pos.ne'
  have hloC : prism (a₀, -t₀) ∉ C := hoff a₀ ha₀ (-t₀) ⟨by linarith, by linarith⟩ (by linarith)
  have hupK : prism (a₀, t₀) ∈ Kup := ⟨(a₀, t₀), ⟨ha₀, ht₀pos.le, ht₀1⟩, rfl⟩
  have hloK : prism (a₀, -t₀) ∈ Klo := ⟨(a₀, -t₀), ⟨ha₀, by linarith, by linarith⟩, rfl⟩
  have hwedge : ∀ y ∈ ψ '' Wz, (φ y).2.1 < 0 ∧ 0 < ε * (φ y).2.2 := by
    rintro _ ⟨z, ⟨hzb, hzw⟩, rfl⟩
    rw [hφψ z (hballr hzb)]
    exact hzw
  have hreflex : ∀ y ∈ ψ '' (R₁ ∪ R₂), 0 < (φ y).2.1 ∨ ε * (φ y).2.2 < 0 := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hφψ z (hballr (hRball hz))]
    rcases hz with ⟨-, hz⟩ | ⟨-, hz⟩
    · exact Or.inl hz
    · exact Or.inr hz
  have hupmem : ∀ a ∈ Δ, ∀ t ∈ Ioc (0 : ℝ) 1, prism (a, t) ∈ Kup := fun a ha t ht =>
    ⟨(a, t), ⟨ha, ht.1.le, ht.2⟩, rfl⟩
  have hlomem : ∀ a ∈ Δ, ∀ t ∈ Ioc (0 : ℝ) 1, prism (a, -t) ∈ Klo := fun a ha t ht =>
    ⟨(a, -t), ⟨ha, by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  have hoff' : ∀ a ∈ Δ, ∀ t ∈ Ioc (0 : ℝ) 1, prism (a, t) ∉ C ∧ prism (a, -t) ∉ C :=
    fun a ha t ht => ⟨hoff a ha t ⟨by linarith [ht.1], ht.2⟩ ht.1.ne',
      hoff a ha (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ (by linarith [ht.1])⟩
  rcases hsplit _ hWc hWN hWC with hW | hW <;> rcases hsplit _ hRc hRN hRC with hR | hR
  · exfalso
    rcases hcov _ hlo hloC with h | h
    · exact hloC (hKint _ (hW h) hloK)
    · exact hloC (hKint _ (hR h) hloK)
  · refine ⟨1, O, Or.inl rfl, hOo, hpO, hOU, fun a ha t ht hy => ?_, fun a ha t ht hy => ?_⟩
    · rw [one_mul] at hy ⊢
      rcases hcov _ hy (hoff' a ha t ht).1 with hyW | hyR
      · exact hwedge _ hyW
      · exact absurd (hKint _ (hupmem a ha t ht) (hR hyR)) (hoff' a ha t ht).1
    · rw [neg_mul, one_mul] at hy ⊢
      rcases hcov _ hy (hoff' a ha t ht).2 with hyW | hyR
      · exact absurd (hKint _ (hW hyW) (hlomem a ha t ht)) (hoff' a ha t ht).2
      · exact hreflex _ hyR
  · refine ⟨-1, O, Or.inr rfl, hOo, hpO, hOU, fun a ha t ht hy => ?_, fun a ha t ht hy => ?_⟩
    · rw [neg_mul, one_mul] at hy ⊢
      rcases hcov _ hy (hoff' a ha t ht).2 with hyW | hyR
      · exact hwedge _ hyW
      · exact absurd (hKint _ (hR hyR) (hlomem a ha t ht)) (hoff' a ha t ht).2
    · rw [neg_neg, one_mul] at hy ⊢
      rcases hcov _ hy (hoff' a ha t ht).1 with hyW | hyR
      · exact absurd (hKint _ (hupmem a ha t ht) (hW hyW)) (hoff' a ha t ht).1
      · exact hreflex _ hyR
  · exfalso
    rcases hcov _ hup hupC with h | h
    · exact hupC (hKint _ hupK (hW h))
    · exact hupC (hKint _ hupK (hR h))

theorem exists_bentDisk_wedgeSide {D A V₀ P V T : Set E3} {q : (Fin 3 → ℝ) → E3}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) {ρ : E3 × ℝ → E3}
    (hρ : IsPLHomeomorphOn ρ ((q '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) A)
    (hρ0 : ∀ x ∈ q '' stdSimplexBoundary 2, ρ (x, 0) = x)
    (hAD : A ∩ D = q '' stdSimplexBoundary 2) (hV₀ : IsOpen V₀) (hDAV : D ∪ A ⊆ V₀)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hchart : ∀ p ∈ q '' stdSimplexBoundary 2, ∃ (U : Set E3) (φ : E3 → ℝ × ℝ × ℝ) (r : ℝ),
      IsOpen U ∧ p ∈ U ∧ 0 < r ∧ IsPLHomeomorphOn φ U (Metric.ball 0 r) ∧ φ p = 0 ∧
      ∀ y ∈ U, (y ∈ D ∪ A ↔
        ((φ y).2.2 = 0 ∧ (φ y).2.1 ≤ 0) ∨ ((φ y).2.1 = 0 ∧ 0 ≤ ε * (φ y).2.2)) ∧
        (y ∈ T ↔ (φ y).2.1 = 0 ∨ (φ y).2.2 = 0) ∧ (y ∈ P ↔ 0 ≤ (φ y).2.1) ∧
        (y ∈ V ↔ (φ y).2.2 ≤ 0))
    (hint : ∀ z ∈ (D ∪ ρ '' ((q '' stdSimplexBoundary 2) ×ˢ Icc 0 (1 / 2))) \
      q '' stdSimplexBoundary 2, ∃ O : Set E3, IsOpen O ∧ z ∈ O ∧ O ∩ T ⊆ D ∪ A) :
    ∃ (E₁ : Set (EuclideanSpace ℝ (Fin 2))) (β : EuclideanSpace ℝ (Fin 2) → E3)
      (prism : (Fin 3 → ℝ) × ℝ → E3) (b : EuclideanSpace ℝ (Fin 2) → (Fin 3 → ℝ))
      (σ s₀ : ℝ),
      IsPLBall 2 E₁ ∧
      IsPLHomeomorphOn β E₁ (D ∪ ρ '' ((q '' stdSimplexBoundary 2) ×ˢ Icc 0 (1 / 2))) ∧
      ContinuousOn prism (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∧
      InjOn prism (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∧
      prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ⊆ V₀ ∧
      (∀ x ∈ E₁, prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∈ 𝓝 (β x)) ∧
      prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(0 : ℝ)}) =
        (D ∪ A) ∩ prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∧
      MapsTo b E₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ∧ IsPiecewiseAffineOn b E₁ ∧
      (∀ x ∈ E₁, prism (b x, 0) = β x) ∧
      (∀ (G : EuclideanSpace ℝ (Fin 2) → (Fin 3 → ℝ) × ℝ) (S : Set (EuclideanSpace ℝ (Fin 2))),
        IsPiecewiseAffineOn G S → MapsTo G S (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) →
          IsPiecewiseAffineOn (prism ∘ G) S) ∧
      (σ = 1 ∨ σ = -1) ∧ 0 < s₀ ∧ s₀ ≤ 1 ∧
      (∀ x ∈ E₁, ∀ t ∈ Ioc (0 : ℝ) s₀, prism (b x, σ * t) ∉ T) ∧
      ∃ x₀ ∈ E₁, ∃ t₀ ∈ Ioc (0 : ℝ) s₀,
        prism (b x₀, σ * t₀) ∉ P ∧ (prism (b x₀, σ * t₀) ∈ V ↔ ε = -1) := by
  classical
  set J := q '' stdSimplexBoundary 2 with hJdef
  set Δ := Convexity.StdSimplex.coordinateSet ℝ (Fin 3) with hΔdef
  obtain ⟨E₁, β, prism, b, hE₁, hβ, hPc, hPi, hPV, hPn, hPcen, hbm, hbpa, hbβ, hPpl⟩ :=
    exists_bentDisk_centeredPrism hq hρ hρ0 hAD hV₀ hDAV
  set Bh := D ∪ ρ '' (J ×ˢ Icc (0 : ℝ) (1 / 2)) with hBhdef
  have hJD : J ⊆ D := (image_mono fun _ hx => hx.1).trans hq.image_eq.subset
  have hJBh : J ⊆ Bh := hJD.trans subset_union_left
  have hpre : ∀ z ∈ Bh, ∃ x ∈ E₁, β x = z := fun z hz => by
    rw [← hβ.image_eq] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, hx, rfl⟩
  have hJsph : IsPLSphere 1 J := hq.isPLSphere_image_stdSimplexBoundary (n := 1)
  have hwedgeInt : ∀ p ∈ J, ∀ (U : Set E3) (φ : E3 → ℝ × ℝ × ℝ),
      (∀ y ∈ U, (y ∈ P ↔ 0 ≤ (φ y).2.1) ∧ (y ∈ V ↔ (φ y).2.2 ≤ 0)) → ∀ y ∈ U,
      ((φ y).2.1 < 0 ∧ 0 < ε * (φ y).2.2 → y ∉ P ∧ (y ∈ V ↔ ε = -1)) ∧
      (0 < (φ y).2.1 ∨ ε * (φ y).2.2 < 0 → ¬ (y ∉ P ∧ (y ∈ V ↔ ε = -1))) := by
    intro p _ U φ hloc y hy
    obtain ⟨hPy, hVy⟩ := hloc y hy
    refine ⟨fun ⟨h1, h2⟩ => ⟨fun h => ?_, ?_⟩, fun h ⟨h1, h2⟩ => ?_⟩
    · linarith [hPy.mp h]
    · rw [hVy]
      rcases hε with rfl | rfl
      · constructor
        · intro h3
          linarith
        · intro h3
          norm_num at h3
      · constructor
        · intro _
          rfl
        · intro _
          linarith
    · rcases h with h | h
      · exact h1 (hPy.mpr h.le)
      · rw [hVy] at h2
        rcases hε with rfl | rfl
        · have h4 : (φ y).2.2 < 0 := by linarith
          have h5 := h2.mp h4.le
          norm_num at h5
        · have h4 : 0 < (φ y).2.2 := by linarith
          have h5 := h2.mpr rfl
          linarith
  have hside : ∀ p ∈ J, ∃ (s : ℝ) (O : Set E3), (s = 1 ∨ s = -1) ∧ IsOpen O ∧ p ∈ O ∧
      (∀ a ∈ Δ, ∀ t ∈ Ioc (0 : ℝ) 1, prism (a, s * t) ∈ O →
        prism (a, s * t) ∉ T ∧ (prism (a, s * t) ∉ P ∧ (prism (a, s * t) ∈ V ↔ ε = -1))) ∧
      (∀ a ∈ Δ, ∀ t ∈ Ioc (0 : ℝ) 1, prism (a, -s * t) ∈ O →
        ¬ (prism (a, -s * t) ∉ P ∧ (prism (a, -s * t) ∈ V ↔ ε = -1))) := by
    intro p hp
    obtain ⟨U, φ, r, hU, hpU, hr, hφ, hφp, hloc⟩ := hchart p hp
    obtain ⟨x₀, hx₀, hx₀p⟩ := hpre p (hJBh hp)
    have ha₀ : b x₀ ∈ Δ := hbm hx₀
    have hpa : prism (b x₀, 0) = p := (hbβ x₀ hx₀).trans hx₀p
    obtain ⟨s, O, hs, hO, hpO, hOU, hw, hrf⟩ :=
      exists_prism_side_of_bentChart (C := D ∪ A) hPc hPi hPcen ha₀
        (by rw [hpa, ← hx₀p]; exact hPn x₀ hx₀) hε hU (by rw [hpa]; exact hpU) hr hφ
        (by rw [hpa]; exact hφp) fun y hy => (hloc y hy).1
    have hPV' : ∀ y ∈ U, (y ∈ P ↔ 0 ≤ (φ y).2.1) ∧ (y ∈ V ↔ (φ y).2.2 ≤ 0) :=
      fun y hy => ⟨(hloc y hy).2.2.1, (hloc y hy).2.2.2⟩
    refine ⟨s, O, hs, hO, by rw [← hpa]; exact hpO, fun a ha t ht hy => ?_,
      fun a ha t ht hy => ?_⟩
    · have hyU := hOU hy
      obtain ⟨h1, h2⟩ := hw a ha t ht hy
      refine ⟨fun hT => ?_, (hwedgeInt p hp U φ hPV' _ hyU).1 ⟨h1, h2⟩⟩
      rcases ((hloc _ hyU).2.1).mp hT with h | h
      · rw [h] at h1
        exact lt_irrefl 0 h1
      · rw [h, mul_zero] at h2
        exact lt_irrefl 0 h2
    · exact (hwedgeInt p hp U φ hPV' _ (hOU hy)).2 (hrf a ha t ht hy)
  choose! sJ OJ hsJ hOJ hpOJ hwJ hrJ using hside
  have hcurve : ∀ p ∈ J, ∀ (O : Set E3), IsOpen O → p ∈ O → ∀ c : ℝ, (c = 1 ∨ c = -1) →
      ∀ m : ℝ, 0 < m → m ≤ 1 → ∃ x₀ ∈ E₁, β x₀ = p ∧ ∃ t ∈ Ioc (0 : ℝ) m,
        prism (b x₀, c * t) ∈ O := by
    intro p hp O hO hpO c hc m hm hm1
    obtain ⟨x₀, hx₀, hx₀p⟩ := hpre p (hJBh hp)
    have ha₀ : b x₀ ∈ Δ := hbm hx₀
    have hpa : prism (b x₀, 0) = p := (hbβ x₀ hx₀).trans hx₀p
    have hcw : ContinuousWithinAt (fun t : ℝ => prism (b x₀, c * t)) (Icc (-1 : ℝ) 1) 0 := by
      have hf : ContinuousWithinAt (fun t : ℝ => (b x₀, c * t)) (Icc (-1 : ℝ) 1) 0 :=
        (by fun_prop : Continuous fun t : ℝ => (b x₀, c * t)).continuousWithinAt
      have hmaps : MapsTo (fun t : ℝ => (b x₀, c * t)) (Icc (-1 : ℝ) 1) (Δ ×ˢ Icc (-1 : ℝ) 1) := by
        intro t ht
        refine ⟨ha₀, ?_⟩
        rcases hc with rfl | rfl <;> constructor <;> linarith [ht.1, ht.2]
      have h1 : ContinuousWithinAt prism (Δ ×ˢ Icc (-1 : ℝ) 1)
          ((fun t : ℝ => (b x₀, c * t)) 0) := by
        simp only [mul_zero]
        exact hPc (b x₀, 0) ⟨ha₀, by norm_num, by norm_num⟩
      exact ContinuousWithinAt.comp (f := fun t : ℝ => (b x₀, c * t)) (x := 0) h1 hf hmaps
    obtain ⟨e, he, hOe⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hpO)
    obtain ⟨δ, hδ, hδe⟩ := Metric.continuousWithinAt_iff.mp hcw e he
    set t₀ := min (δ / 2) m with ht₀def
    have ht₀pos : 0 < t₀ := lt_min (half_pos hδ) hm
    have ht₀m : t₀ ≤ m := min_le_right _ _
    have ht₀δ : t₀ < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    refine ⟨x₀, hx₀, hx₀p, t₀, ⟨ht₀pos, ht₀m⟩, ?_⟩
    have hmem := hδe (x := t₀) ⟨by linarith, ht₀m.trans hm1⟩ (by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]
      exact ht₀δ)
    have h0 : prism (b x₀, c * 0) = p := by
      rw [mul_zero]
      exact hpa
    rw [h0] at hmem
    exact hOe hmem
  have hconst : ∀ p ∈ J, ∀ p' ∈ J, p' ∈ OJ p → sJ p' = sJ p := by
    intro p hp p' hp' hp'O
    by_contra hne
    obtain ⟨x₀, hx₀, -, t, ht, hmem⟩ := hcurve p' hp' (OJ p ∩ OJ p')
      ((hOJ p hp).inter (hOJ p' hp')) ⟨hp'O, hpOJ p' hp'⟩ (sJ p) (hsJ p hp) 1 one_pos le_rfl
    have hsp : sJ p = -sJ p' := by
      rcases hsJ p hp with h1 | h1 <;> rcases hsJ p' hp' with h2 | h2
      · exact absurd (h2.trans h1.symm) hne
      · norm_num [h1, h2]
      · norm_num [h1, h2]
      · exact absurd (h2.trans h1.symm) hne
    have h1 := (hwJ p hp (b x₀) (hbm hx₀) t ht hmem.1).2
    have h2 := hrJ p' hp' (b x₀) (hbm hx₀) t ht (by rw [← hsp]; exact hmem.2)
    rw [← hsp] at h2
    exact h2 h1
  obtain ⟨p₁, hp₁⟩ := hJsph.nonempty
  set σ := sJ p₁ with hσdef
  have hσall : ∀ p ∈ J, sJ p = σ := by
    have hJconn : IsPreconnected J := hJsph.isConnected.isPreconnected
    set Opos := ⋃ p ∈ {p | p ∈ J ∧ sJ p = σ}, OJ p with hOposdef
    set Oneg := ⋃ p ∈ {p | p ∈ J ∧ sJ p ≠ σ}, OJ p with hOnegdef
    have hOpos : IsOpen Opos := isOpen_biUnion fun p hp => hOJ p hp.1
    have hOneg : IsOpen Oneg := isOpen_biUnion fun p hp => hOJ p hp.1
    have hcover : J ⊆ Opos ∪ Oneg := by
      intro p hp
      by_cases h : sJ p = σ
      · exact Or.inl (mem_iUnion₂.mpr ⟨p, ⟨hp, h⟩, hpOJ p hp⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨p, ⟨hp, h⟩, hpOJ p hp⟩)
    have hdisj : J ∩ (Opos ∩ Oneg) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun p' ⟨hp', hposm, hnegm⟩ => ?_
      obtain ⟨p, ⟨hp, hps⟩, hp'O⟩ := mem_iUnion₂.mp hposm
      obtain ⟨p'', ⟨hp'', hp''s⟩, hp'O'⟩ := mem_iUnion₂.mp hnegm
      exact hp''s ((hconst p'' hp'' p' hp' hp'O').symm.trans ((hconst p hp p' hp' hp'O).trans hps))
    rcases isPreconnected_iff_subset_of_disjoint.mp hJconn Opos Oneg hOpos hOneg hcover hdisj
      with h | h
    · intro p hp
      obtain ⟨p', ⟨hp', hp's⟩, hpO⟩ := mem_iUnion₂.mp (h hp)
      exact (hconst p' hp' p hp hpO).trans hp's
    · exfalso
      obtain ⟨p', ⟨hp', hp's⟩, hpO⟩ := mem_iUnion₂.mp (h hp₁)
      exact hp's (hconst p' hp' p₁ hp₁ hpO).symm
  have hσ : σ = 1 ∨ σ = -1 := hsJ p₁ hp₁
  have hfree : ∀ z ∈ Bh, ∃ O : Set E3, IsOpen O ∧ z ∈ O ∧
      ∀ a ∈ Δ, ∀ t ∈ Ioc (0 : ℝ) 1, prism (a, σ * t) ∈ O → prism (a, σ * t) ∉ T := by
    intro z hz
    by_cases hzJ : z ∈ J
    · refine ⟨OJ z, hOJ z hzJ, hpOJ z hzJ, fun a ha t ht hy => ?_⟩
      have h := hwJ z hzJ a ha t ht
      rw [hσall z hzJ] at h
      exact (h hy).1
    · obtain ⟨O, hO, hzO, hOT⟩ := hint z ⟨hz, hzJ⟩
      refine ⟨O, hO, hzO, fun a ha t ht hy hT => ?_⟩
      have hst : σ * t ∈ Icc (-1 : ℝ) 1 := by
        rcases hσ with h | h <;> rw [h] <;> constructor <;> linarith [ht.1, ht.2]
      have hmem : prism (a, σ * t) ∈ (D ∪ A) ∩ prism '' (Δ ×ˢ Icc (-1 : ℝ) 1) :=
        ⟨hOT ⟨hy, hT⟩, (a, σ * t), ⟨ha, hst⟩, rfl⟩
      rw [← hPcen] at hmem
      obtain ⟨⟨a', t'⟩, ⟨ha', ht'⟩, heq⟩ := hmem
      have ht'0 : t' = 0 := ht'
      have h := hPi ⟨ha', by rw [ht'0]; norm_num⟩ ⟨ha, hst⟩ heq
      have h0 : σ * t = 0 := (congrArg Prod.snd h).symm.trans ht'0
      rcases hσ with h1 | h1 <;> rw [h1] at h0 <;> linarith [ht.1]
  choose! Oz hOz hzOz hOzfree using hfree
  set Oall := ⋃ z ∈ Bh, Oz z with hOalldef
  have hOall : IsOpen Oall := isOpen_biUnion fun z hz => hOz z hz
  have hfc : ContinuousOn (fun w : EuclideanSpace ℝ (Fin 2) × ℝ => prism (b w.1, σ * w.2))
      (E₁ ×ˢ Icc (-1 : ℝ) 1) := by
    refine hPc.comp ((hbpa.continuousOn.comp continuous_fst.continuousOn
      fun w hw => hw.1).prodMk (continuous_const.mul continuous_snd).continuousOn) ?_
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨hbm hx, ?_⟩
    rcases hσ with h | h <;> rw [h] <;> constructor <;> linarith [ht.1, ht.2]
  obtain ⟨s₀, hs₀, hs₀1, hs₀O⟩ := exists_pos_forall_prod_Icc_mem_of_isCompact
    hE₁.isPolyhedron.isCompact hfc hOall fun x hx => by
      change prism (b x, σ * 0) ∈ Oall
      rw [mul_zero, hbβ x hx]
      exact mem_iUnion₂.mpr ⟨β x, hβ.bijOn.mapsTo hx, hzOz (β x) (hβ.bijOn.mapsTo hx)⟩
  have hfreeT : ∀ x ∈ E₁, ∀ t ∈ Ioc (0 : ℝ) s₀, prism (b x, σ * t) ∉ T := by
    intro x hx t ht
    have hmem := hs₀O x hx t ⟨by linarith [ht.1], ht.2⟩
    obtain ⟨z, hz, hzO⟩ := mem_iUnion₂.mp hmem
    exact hOzfree z hz (b x) (hbm hx) t ⟨ht.1, ht.2.trans hs₀1⟩ hzO
  obtain ⟨x₀, hx₀, -, t₀, ht₀, hmem₀⟩ := hcurve p₁ hp₁ (OJ p₁) (hOJ p₁ hp₁) (hpOJ p₁ hp₁) σ hσ
    s₀ hs₀ hs₀1
  refine ⟨E₁, β, prism, b, σ, s₀, hE₁, hβ, hPc, hPi, hPV, hPn, hPcen, hbm, hbpa, hbβ, hPpl, hσ,
    hs₀, hs₀1, hfreeT, x₀, hx₀, t₀, ht₀, ?_⟩
  exact (hwJ p₁ hp₁ (b x₀) (hbm hx₀) t₀ ⟨ht₀.1, ht₀.2.trans hs₀1⟩ hmem₀).2

theorem exists_wedgeLift {D A V₀ P V T : Set E3} {q : (Fin 3 → ℝ) → E3}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) {ρ : E3 × ℝ → E3}
    (hρ : IsPLHomeomorphOn ρ ((q '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) A)
    (hρ0 : ∀ x ∈ q '' stdSimplexBoundary 2, ρ (x, 0) = x)
    (hAD : A ∩ D = q '' stdSimplexBoundary 2) (hV₀ : IsOpen V₀) (hDAV : D ∪ A ⊆ V₀)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hchart : ∀ p ∈ q '' stdSimplexBoundary 2, ∃ (U : Set E3) (φ : E3 → ℝ × ℝ × ℝ) (r : ℝ),
      IsOpen U ∧ p ∈ U ∧ 0 < r ∧ IsPLHomeomorphOn φ U (Metric.ball 0 r) ∧ φ p = 0 ∧
      ∀ y ∈ U, (y ∈ D ∪ A ↔
        ((φ y).2.2 = 0 ∧ (φ y).2.1 ≤ 0) ∨ ((φ y).2.1 = 0 ∧ 0 ≤ ε * (φ y).2.2)) ∧
        (y ∈ T ↔ (φ y).2.1 = 0 ∨ (φ y).2.2 = 0) ∧ (y ∈ P ↔ 0 ≤ (φ y).2.1) ∧
        (y ∈ V ↔ (φ y).2.2 ≤ 0))
    (hint : ∀ z ∈ (D ∪ ρ '' ((q '' stdSimplexBoundary 2) ×ˢ Icc 0 (1 / 2))) \
      q '' stdSimplexBoundary 2, ∃ O : Set E3, IsOpen O ∧ z ∈ O ∧ O ∩ T ⊆ D ∪ A)
    (hPT : frontier P ⊆ T) (hVT : frontier V ⊆ T) :
    ∃ (E₁ : Set (EuclideanSpace ℝ (Fin 2))) (β : EuclideanSpace ℝ (Fin 2) → E3)
      (prism : (Fin 3 → ℝ) × ℝ → E3) (b : EuclideanSpace ℝ (Fin 2) → (Fin 3 → ℝ))
      (μ : EuclideanSpace ℝ (Fin 2) → ℝ) (σ c : ℝ) (q' : (Fin 3 → ℝ) → E3),
      IsPLBall 2 E₁ ∧
      IsPLHomeomorphOn β E₁ (D ∪ ρ '' ((q '' stdSimplexBoundary 2) ×ˢ Icc 0 (1 / 2))) ∧
      ContinuousOn prism (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∧
      InjOn prism (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∧
      prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ⊆ V₀ ∧
      prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(0 : ℝ)}) =
        (D ∪ A) ∩ prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∧
      MapsTo b E₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ∧ ContinuousOn b E₁ ∧ InjOn b E₁ ∧
      (∀ x ∈ E₁, prism (b x, 0) = β x) ∧
      (σ = 1 ∨ σ = -1) ∧ 0 < c ∧ c ≤ 1 / 2 ∧
      (∀ x ∈ E₁, ∀ t ∈ Icc (-(2 * c)) (2 * c),
        prism (b x, t) ∈ interior (prism '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1))) ∧
      (∀ x ∈ E₁, ∀ t ∈ Ioc (0 : ℝ) (2 * c), prism (b x, σ * t) ∉ T ∧
        prism (b x, σ * t) ∉ P ∧ (prism (b x, σ * t) ∈ V ↔ ε = -1)) ∧
      ContinuousOn μ E₁ ∧ (∀ x ∈ E₁, 0 ≤ μ x ∧ μ x ≤ 1) ∧
      (∀ x ∈ E₁, μ x = 0 ↔
        β x ∈ ρ '' ((q '' stdSimplexBoundary 2) ×ˢ {(1 / 2 : ℝ)})) ∧
      IsPLHomeomorphOn q' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        ((fun x => prism (b x, σ * (c * μ x))) '' E₁) ∧
      q' '' stdSimplexBoundary 2 = ρ '' ((q '' stdSimplexBoundary 2) ×ˢ {(1 / 2 : ℝ)}) := by
  classical
  set J := q '' stdSimplexBoundary 2 with hJdef
  set Δ := Convexity.StdSimplex.coordinateSet ℝ (Fin 3) with hΔdef
  set far := ρ '' (J ×ˢ {(1 / 2 : ℝ)}) with hfardef
  obtain ⟨E₁, β, prism, b, σ, s₀, hE₁, hβ, hPc, hPi, hPV, hPn, hPcen, hbm, hbpa, hbβ, hPpl, hσ,
    hs₀, hs₀1, hfreeT, x₀, hx₀, t₀, ht₀, hwit⟩ :=
    exists_bentDisk_wedgeSide hq hρ hρ0 hAD hV₀ hDAV hε hchart hint
  set Bh := D ∪ ρ '' (J ×ˢ Icc (0 : ℝ) (1 / 2)) with hBhdef
  have hJpoly : IsPolyhedron J := (hq.isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron
  have hIsub : J ×ˢ Icc (0 : ℝ) (1 / 2) ⊆ J ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono Subset.rfl (Icc_subset_Icc le_rfl (by norm_num))
  have hρh := hρ.restrict (hJpoly.prod isHPolytope_Icc.isPolyhedron) hIsub
  have hJD : J ⊆ D := (image_mono fun _ hx => hx.1).trans hq.image_eq.subset
  have hAh : ρ '' (J ×ˢ Icc (0 : ℝ) (1 / 2)) ∩ D = J := by
    apply Subset.antisymm
    · exact (inter_subset_inter_left _ ((image_mono hIsub).trans hρ.image_eq.subset)).trans
        hAD.subset
    · intro x hx
      exact ⟨⟨(x, 0), ⟨hx, by norm_num, by norm_num⟩, hρ0 x hx⟩, hJD hx⟩
  obtain ⟨qh, hqh, hqhJ, -⟩ :=
    hq.exists_isPLHomeomorphOn_union_collar (a := 0) (b := 1 / 2) (by norm_num) hρh hρ0 hAh
  have hE₁c : IsCompact E₁ := hE₁.isPolyhedron.isCompact
  have hbc : ContinuousOn b E₁ := hbpa.continuousOn
  have hβc : ContinuousOn β E₁ := hβ.isPiecewiseAffineOn.continuousOn
  have hbinj : InjOn b E₁ := by
    intro x hx y hy hxy
    apply hβ.bijOn.injOn hx hy
    rw [← hbβ x hx, ← hbβ y hy, hxy]
  set N := prism '' (Δ ×ˢ Icc (-1 : ℝ) 1) with hNdef
  have hfc : ContinuousOn (fun w : EuclideanSpace ℝ (Fin 2) × ℝ => prism (b w.1, w.2))
      (E₁ ×ˢ Icc (-1 : ℝ) 1) := by
    refine hPc.comp ((hbc.comp continuous_fst.continuousOn fun w hw => hw.1).prodMk
      continuous_snd.continuousOn) ?_
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨hbm hx, ht⟩
  obtain ⟨η, hη, hη1, hηN⟩ := exists_pos_forall_prod_Icc_mem_of_isCompact hE₁c hfc
    isOpen_interior fun x hx => by
      change prism (b x, 0) ∈ interior N
      rw [hbβ x hx]
      exact mem_interior_iff_mem_nhds.mpr (hPn x hx)
  set c := min s₀ η / 2 with hcdef
  have hc : 0 < c := by positivity
  have hcs : 2 * c ≤ s₀ := by
    rw [hcdef]
    linarith [min_le_left s₀ η]
  have hcη : 2 * c ≤ η := by
    rw [hcdef]
    linarith [min_le_right s₀ η]
  have hc1 : c ≤ 1 / 2 := by linarith
  have hconn : IsPreconnected ((fun w : EuclideanSpace ℝ (Fin 2) × ℝ => prism (b w.1, σ * w.2)) ''
      (E₁ ×ˢ Ioc (0 : ℝ) s₀)) := by
    refine ((hE₁.isConnected.isPreconnected).prod isPreconnected_Ioc).image _ ?_
    refine hPc.comp ((hbc.comp continuous_fst.continuousOn fun w hw => hw.1).prodMk
      (continuous_const.mul continuous_snd).continuousOn) ?_
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨hbm hx, ?_⟩
    rcases hσ with h | h <;> rw [h] <;> constructor <;> linarith [ht.1, ht.2]
  set R := (fun w : EuclideanSpace ℝ (Fin 2) × ℝ => prism (b w.1, σ * w.2)) ''
      (E₁ ×ˢ Ioc (0 : ℝ) s₀) with hRdef
  have hRT : ∀ y ∈ R, y ∉ T := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact hfreeT x hx t ht
  have hwR : prism (b x₀, σ * t₀) ∈ R := ⟨(x₀, t₀), ⟨hx₀, ht₀⟩, rfl⟩
  have hRP : ∀ y ∈ R, y ∉ P := by
    intro y hy hyP
    have hsub := IsPreconnected.subset_of_disjoint_frontier hconn ⟨y, hy, hyP⟩
      (Set.disjoint_left.mpr fun z hz hzf => hRT z hz (hPT hzf))
    exact hwit.1 (hsub hwR)
  have hRV : ∀ y ∈ R, (y ∈ V ↔ ε = -1) := by
    intro y hy
    constructor
    · intro hyV
      have hsub := IsPreconnected.subset_of_disjoint_frontier hconn ⟨y, hy, hyV⟩
        (Set.disjoint_left.mpr fun z hz hzf => hRT z hz (hVT hzf))
      exact hwit.2.mp (hsub hwR)
    · intro hεv
      have hwV := hwit.2.mpr hεv
      have hsub := IsPreconnected.subset_of_disjoint_frontier hconn ⟨_, hwR, hwV⟩
        (Set.disjoint_left.mpr fun z hz hzf => hRT z hz (hVT hzf))
      exact hsub hy
  set τ : E3 → ℝ := fun z => (Function.invFunOn ρ (J ×ˢ Icc (0 : ℝ) 1) z).2 with hτdef
  have hτ : ∀ x ∈ J, ∀ u ∈ Icc (0 : ℝ) 1, τ (ρ (x, u)) = u := by
    intro x hx u hu
    have h := hρ.bijOn.injOn.leftInvOn_invFunOn (show (x, u) ∈ J ×ˢ Icc (0 : ℝ) 1 from ⟨hx, hu⟩)
    change (Function.invFunOn ρ (J ×ˢ Icc (0 : ℝ) 1) (ρ (x, u))).2 = u
    rw [h]
  set P₁ := E₁ ∩ β ⁻¹' D with hP₁def
  set Q₁ := E₁ ∩ β ⁻¹' (ρ '' (J ×ˢ Icc (0 : ℝ) (1 / 2))) with hQ₁def
  have hDpoly : IsPolyhedron D := IsPLBall.isPolyhedron ⟨q, hq⟩
  have hHpoly : IsPolyhedron (ρ '' (J ×ˢ Icc (0 : ℝ) (1 / 2))) :=
    (hJpoly.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      (hρh.isPiecewiseAffineOn) hρh.bijOn.injOn
  have hP₁poly : IsPolyhedron P₁ := hβ.isPolyhedron_preimage hDpoly subset_union_left
  have hQ₁poly : IsPolyhedron Q₁ := hβ.isPolyhedron_preimage hHpoly subset_union_right
  set μ : EuclideanSpace ℝ (Fin 2) → ℝ :=
    P₁.piecewise (fun _ => 1) (fun x => 1 - 2 * τ (β x)) with hμdef
  have hμpa : IsPiecewiseAffineOn μ E₁ := by
    have hf : IsPiecewiseAffineOn (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) P₁ :=
      ((hβ.isPiecewiseAffineOn.mono_of_isPolyhedron hP₁poly inter_subset_left).affine_comp
        (AffineMap.const ℝ E3 (1 : ℝ))).congr fun _ _ => rfl
    have hg : IsPiecewiseAffineOn (fun x => 1 - 2 * τ (β x)) Q₁ := by
      have h1 : IsPiecewiseAffineOn (Function.invFunOn ρ (J ×ˢ Icc (0 : ℝ) 1) ∘ β)
          (Q₁ ∩ β ⁻¹' A) :=
        hρ.isPiecewiseAffineOn_invFunOn.comp
          (hβ.isPiecewiseAffineOn.mono_of_isPolyhedron hQ₁poly inter_subset_left)
      have hQA : Q₁ ∩ β ⁻¹' A = Q₁ := inter_eq_left.mpr fun x hx =>
        (image_mono hIsub).trans hρ.image_eq.subset hx.2
      rw [hQA] at h1
      let aff : (E3 × ℝ) →ᵃ[ℝ] ℝ :=
        (AffineMap.const ℝ (E3 × ℝ) (1 : ℝ)) - (2 : ℝ) • (LinearMap.snd ℝ E3 ℝ).toAffineMap
      refine (h1.affine_comp aff).congr fun x _ => ?_
      simp [aff, τ, sub_eq_add_neg]
    have hPc₁ : IsClosed P₁ := hP₁poly.isClosed
    have hQc₁ : IsClosed Q₁ := hQ₁poly.isClosed
    have hfg : EqOn (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) (fun x => 1 - 2 * τ (β x))
        (P₁ ∩ Q₁) := by
      rintro x ⟨⟨-, hxD⟩, ⟨-, hxH⟩⟩
      have hxJ : β x ∈ J := by
        rw [← hAh]
        exact ⟨hxH, hxD⟩
      have : τ (β x) = 0 := by
        rw [← hρ0 _ hxJ, hτ _ hxJ 0 ⟨le_rfl, zero_le_one⟩]
      simp [this]
    have h := hf.piecewise_of_isClosed hg hPc₁ hQc₁ hfg
    have hE₁eq : P₁ ∪ Q₁ = E₁ := by
      apply Subset.antisymm
      · exact union_subset inter_subset_left inter_subset_left
      · intro x hx
        rcases hβ.bijOn.mapsTo hx with h1 | h1
        · exact Or.inl ⟨hx, h1⟩
        · exact Or.inr ⟨hx, h1⟩
    rw [hE₁eq] at h
    refine h.congr fun x _ => ?_
    by_cases hxP : x ∈ P₁ <;> simp [hμdef, Set.piecewise, hxP]
  have hfarBh : far ⊆ Bh := fun z hz => Or.inr (image_mono (prod_mono Subset.rfl
    (show ({(1 / 2 : ℝ)} : Set ℝ) ⊆ Icc 0 (1 / 2) from by
      rintro u rfl
      constructor <;> norm_num)) hz)
  have hμcases : ∀ x ∈ E₁, (x ∈ P₁ ∧ μ x = 1) ∨ (x ∉ P₁ ∧ ∃ j ∈ J, ∃ u ∈ Icc (0 : ℝ) (1 / 2),
      β x = ρ (j, u) ∧ μ x = 1 - 2 * u) := by
    intro x hx
    by_cases hxP : x ∈ P₁
    · exact Or.inl ⟨hxP, by simp [hμdef, hxP]⟩
    · right
      have hxB := hβ.bijOn.mapsTo hx
      rcases hxB with hxD | ⟨⟨j, u⟩, ⟨hj, hu⟩, hju⟩
      · exact absurd ⟨hx, hxD⟩ hxP
      · refine ⟨hxP, j, hj, u, hu, hju.symm, ?_⟩
        have hτu : τ (β x) = u := by
          rw [← hju]
          exact hτ j hj u ⟨hu.1, hu.2.trans (by norm_num)⟩
        simp [hμdef, hxP, hτu]
  have hμbd : ∀ x ∈ E₁, 0 ≤ μ x ∧ μ x ≤ 1 := by
    intro x hx
    rcases hμcases x hx with ⟨-, h⟩ | ⟨-, j, -, u, hu, -, h⟩
    · rw [h]
      norm_num
    · rw [h]
      constructor <;> linarith [hu.1, hu.2]
  have hμ0 : ∀ x ∈ E₁, μ x = 0 ↔ β x ∈ far := by
    intro x hx
    constructor
    · intro h0
      rcases hμcases x hx with ⟨-, h⟩ | ⟨-, j, hj, u, hu, hju, h⟩
      · rw [h] at h0
        norm_num at h0
      · have hu2 : u = 1 / 2 := by linarith
        rw [hju, hu2]
        exact ⟨(j, 1 / 2), ⟨hj, rfl⟩, rfl⟩
    · rintro ⟨⟨j, u⟩, ⟨hj, hu⟩, hju⟩
      have hu2 : u = 1 / 2 := hu
      rcases hμcases x hx with ⟨hxP, -⟩ | ⟨-, j', hj', u', hu', hju', h⟩
      · have hxJ : β x ∈ J := by
          rw [← hAD]
          exact ⟨hρ.image_eq.subset ⟨(j, u), ⟨hj, by rw [hu2]; constructor <;> norm_num⟩, hju⟩,
            hxP.2⟩
        obtain ⟨j₀, hj₀, hj₀x⟩ : ∃ j₀ ∈ J, ρ (j₀, 0) = β x := ⟨β x, hxJ, hρ0 _ hxJ⟩
        have heq := hρ.bijOn.injOn ⟨hj, by rw [hu2]; constructor <;> norm_num⟩
          ⟨hj₀, le_rfl, zero_le_one⟩ (hju.trans hj₀x.symm)
        have := congrArg Prod.snd heq
        rw [hu2] at this
        norm_num at this
      · have heq := hρ.bijOn.injOn ⟨hj, by rw [hu2]; constructor <;> norm_num⟩
          ⟨hj', hu'.1, hu'.2.trans (by norm_num)⟩ (hju.trans hju')
        have hu'2 : u' = 1 / 2 := by
          have := congrArg Prod.snd heq
          simp only at this
          linarith
        rw [h, hu'2]
        norm_num
  set F : EuclideanSpace ℝ (Fin 2) → E3 := fun x => prism (b x, σ * (c * μ x)) with hFdef
  have hGmaps : MapsTo (fun x => (b x, σ * (c * μ x))) E₁ (Δ ×ˢ Icc (-1 : ℝ) 1) := by
    intro x hx
    refine ⟨hbm hx, ?_⟩
    have h1 := hμbd x hx
    have h2 : 0 ≤ c * μ x := mul_nonneg hc.le h1.1
    have h3 : c * μ x ≤ 1 := by nlinarith
    rcases hσ with h | h <;> rw [h] <;> constructor <;> linarith
  have hFpa : IsPiecewiseAffineOn F E₁ := by
    have hG : IsPiecewiseAffineOn (fun x => (b x, σ * (c * μ x))) E₁ := by
      refine hbpa.prod_mk ((hμpa.affine_comp (LinearMap.mulLeft ℝ (σ * c)).toAffineMap).congr
        fun x _ => ?_)
      change σ * (c * μ x) = (σ * c) * μ x
      ring
    exact hPpl _ E₁ hG hGmaps
  have hFinj : InjOn F E₁ := by
    intro x hx y hy hxy
    have h := hPi (hGmaps hx) (hGmaps hy) hxy
    exact hbinj hx hy (congrArg Prod.fst h)
  have hFpl : IsPLHomeomorphOn F E₁ (F '' E₁) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hE₁.isPolyhedron hFpa hFinj.bijOn_image
  have hparam : IsPLHomeomorphOn (Function.invFunOn β E₁ ∘ qh) Δ E₁ := hqh.trans hβ.symm
  refine ⟨E₁, β, prism, b, μ, σ, c, F ∘ (Function.invFunOn β E₁ ∘ qh), hE₁, hβ, hPc, hPi, hPV,
    hPcen, hbm, hbc, hbinj, hbβ, hσ, hc, hc1, fun x hx t ht => hηN x hx t
      ⟨by linarith [ht.1], by linarith [ht.2]⟩, fun x hx t ht => ?_, hμpa.continuousOn,
    hμbd, hμ0, hparam.trans hFpl, ?_⟩
  · have htR : prism (b x, σ * t) ∈ R := ⟨(x, t), ⟨hx, ht.1, ht.2.trans hcs⟩, rfl⟩
    exact ⟨hRT _ htR, hRP _ htR, hRV _ htR⟩
  · rw [image_comp, image_comp, hqhJ]
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have hzB := hfarBh hz
      have hx := hβ.symm.bijOn.mapsTo hzB
      have hβx : β (Function.invFunOn β E₁ z) = z := hβ.bijOn.invOn_invFunOn.2 hzB
      have hμx : μ (Function.invFunOn β E₁ z) = 0 := (hμ0 _ hx).mpr (by rw [hβx]; exact hz)
      change prism (b (Function.invFunOn β E₁ z), σ * (c * μ (Function.invFunOn β E₁ z))) ∈ far
      rw [hμx, mul_zero, mul_zero, hbβ _ hx, hβx]
      exact hz
    · intro z hz
      have hzB := hfarBh hz
      have hx := hβ.symm.bijOn.mapsTo hzB
      have hβx : β (Function.invFunOn β E₁ z) = z := hβ.bijOn.invOn_invFunOn.2 hzB
      have hμx : μ (Function.invFunOn β E₁ z) = 0 := (hμ0 _ hx).mpr (by rw [hβx]; exact hz)
      refine ⟨Function.invFunOn β E₁ z, ⟨z, hz, rfl⟩, ?_⟩
      change prism (b (Function.invFunOn β E₁ z), σ * (c * μ (Function.invFunOn β E₁ z))) = z
      rw [hμx, mul_zero, mul_zero, hbβ _ hx, hβx]

end DifferentialGeometry.Topology.PiecewiseLinear
