import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SlopeEstimateReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductIntegralBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductLengthEvolution

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem exp_sub_one_div_mul_le (k L ε : ℝ) (hk : 0 ≤ k) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ,
      (Real.exp (k * h) - 1) / h * L ≤ k * L + ε := by
  have hC : 0 ≤ k ^ 2 * Real.exp k * L := by positivity
  have hpos : 0 < k ^ 2 * Real.exp k * L + 1 := by positivity
  refine ⟨min 1 (ε / (k ^ 2 * Real.exp k * L + 1)),
    lt_min one_pos (div_pos hε hpos), fun h hh => ?_⟩
  have hh1 : h < 1 := lt_of_lt_of_le hh.2 (min_le_left _ _)
  have hh2 : h < ε / (k ^ 2 * Real.exp k * L + 1) :=
    lt_of_lt_of_le hh.2 (min_le_right _ _)
  have hh0 : 0 < h := hh.1
  have hinc : Real.exp (k * h) - 1 ≤ k * Real.exp (k * h) * h :=
    exp_increment_le k h h hk hh0.le le_rfl
  have hexp : Real.exp (k * h) ≤ Real.exp k :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h1 : (Real.exp (k * h) - 1) / h * L ≤ k * Real.exp (k * h) * L := by
    have h2 : (Real.exp (k * h) - 1) / h ≤ k * Real.exp (k * h) := by
      rw [div_le_iff₀ hh0]
      linarith [hinc]
    calc (Real.exp (k * h) - 1) / h * L ≤ (k * Real.exp (k * h)) * L :=
          mul_le_mul_of_nonneg_right h2 hL
      _ = k * Real.exp (k * h) * L := by ring
  have h3 : k * Real.exp (k * h) * L ≤ k * L + ε := by
    have hA : k * (Real.exp (k * h) - 1) * L ≤ k ^ 2 * Real.exp k * L * h := by
      have ha : k * (Real.exp (k * h) - 1) * L ≤ k * (k * Real.exp (k * h) * h) * L :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinc hk) hL
      have hb : k * (k * Real.exp (k * h) * h) * L = k ^ 2 * Real.exp (k * h) * h * L := by
        ring
      have hnon : 0 ≤ k ^ 2 * h * L := by positivity
      have hc : k ^ 2 * Real.exp (k * h) * h * L ≤ k ^ 2 * Real.exp k * h * L := by
        calc k ^ 2 * Real.exp (k * h) * h * L = (k ^ 2 * h * L) * Real.exp (k * h) := by ring
          _ ≤ (k ^ 2 * h * L) * Real.exp k := mul_le_mul_of_nonneg_left hexp hnon
          _ = k ^ 2 * Real.exp k * h * L := by ring
      linarith [ha, hb.le, hb.ge, hc]
    have he : k ^ 2 * Real.exp k * L * h ≤ ε := by
      have hf : k ^ 2 * Real.exp k * L * h ≤
          k ^ 2 * Real.exp k * L * (ε / (k ^ 2 * Real.exp k * L + 1)) :=
        mul_le_mul_of_nonneg_left hh2.le hC
      have hg : k ^ 2 * Real.exp k * L * (ε / (k ^ 2 * Real.exp k * L + 1)) ≤ ε := by
        rw [← mul_div_assoc]
        rw [div_le_iff₀ hpos]
        linarith [hε.le, hC]
      linarith [hf, hg]
    have hd : k * Real.exp (k * h) * L = k * L + k * (Real.exp (k * h) - 1) * L := by ring
    linarith [hA, he, hd.le, hd.ge]
  exact h1.trans h3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

omit [CompactSpace M] [Nonempty M] in
theorem ProductCurve.length_upper_right_slope
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc a b))
    (t : ℝ) (ht : t ∈ Ico a b) :
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (c.length B.family.metric lambda (t + h) - c.length B.family.metric lambda t) / h ≤
        B.B₀ * c.length B.family.metric lambda t + ε := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := exp_sub_one_div_mul_le B.B₀
    (c.length B.family.metric lambda t) ε B.B₀_nonneg
    (ProductCurve.length_nonneg B.family.metric lambda t c) hε
  refine ⟨δ, hδ, fun h hh htb => ?_⟩
  have hLt : 0 ≤ c.length B.family.metric lambda t :=
    ProductCurve.length_nonneg B.family.metric lambda t c
  have hgrowth := (ProductCurve.length_energy_bounds B c lambda hlambda (uniqueDiffOn_Icc B.lt) hc
      (J := Icc a b) (s := a) (u := b) B.lt Subset.rfl Subset.rfl).2.2
    t ⟨ht.1, ht.2.le⟩ (t + h) ⟨by linarith [hh.1], htb⟩
  have h1 : c.length B.family.metric lambda (t + h) ≤
      Real.exp (B.B₀ * h) * c.length B.family.metric lambda t := by
    simpa only [add_sub_cancel_left] using hgrowth.1
  have h2 : c.length B.family.metric lambda (t + h) - c.length B.family.metric lambda t ≤
      (Real.exp (B.B₀ * h) - 1) * c.length B.family.metric lambda t := by
    linarith [h1]
  have h3 : (Real.exp (B.B₀ * h) - 1) * c.length B.family.metric lambda t ≤
      (B.B₀ * c.length B.family.metric lambda t + ε) * h := by
    have h4 := hbound h hh
    have h5 : (Real.exp (B.B₀ * h) - 1) / h * c.length B.family.metric lambda t * h ≤
        (B.B₀ * c.length B.family.metric lambda t + ε) * h :=
      mul_le_mul_of_nonneg_right h4 hh.1.le
    have h6 : (Real.exp (B.B₀ * h) - 1) / h * c.length B.family.metric lambda t * h =
        (Real.exp (B.B₀ * h) - 1) * c.length B.family.metric lambda t := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt hh.1)]
    linarith [h5, h6.le, h6.ge]
  rw [div_le_iff₀ hh.1]
  linarith [h2, h3]

omit [CompactSpace M] [Nonempty M] in
theorem ProductCurve.totalCurvature_upper_right_slope
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc a b))
    (t : ℝ) (ht : t ∈ Ico a b) :
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ b →
      (c.totalCurvature B.family.metric lambda (t + h) -
          c.totalCurvature B.family.metric lambda t) / h ≤
        (B.C + B.B₀) * c.totalCurvature B.family.metric lambda t +
          B.C * c.length B.family.metric lambda t + ε := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hB⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hf, h0, _, _, hC⟩ := hB lambda hlambda
  have hm : Bhat.family.metric =
      fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun F => F.metric) hf
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Icc a b) := by
    rw [hm]
    exact c.isSolutionOn_map A B.family.metric lambda hlambda (uniqueDiffOn_Icc B.lt) hc
  have hΘ : ∀ v ∈ Icc a b,
      c.map.totalCurvature Bhat.family.metric v = c.totalCurvature B.family.metric lambda v := by
    intro v hv
    rw [hm]
    exact c.map_totalCurvature_eq A B.family.metric lambda hlambda hc.smooth hc.immersed v hv
  have hLen : ∀ v ∈ Icc a b,
      c.map.length Bhat.family.metric v = c.length B.family.metric lambda v := by
    intro v hv
    rw [hm]
    exact c.map_length_eq A B.family.metric lambda hlambda hc.smooth v hv
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.totalCurvature_upper_right_slope
      (D := D') Bhat B.lt (Subset.rfl) c.map hsol t ht ε hε
  refine ⟨δ, hδ, fun h hh htb => ?_⟩
  have h1 := hb h hh htb
  rw [hΘ (t + h) ⟨by linarith [ht.1, hh.1], htb⟩, hΘ t ⟨ht.1, ht.2.le⟩,
    hLen t ⟨ht.1, ht.2.le⟩, hC, h0] at h1
  exact h1

omit [CompactSpace M] [Nonempty M] in
private theorem ProductCurve.continuousOn_totalCurvature_add_length
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc a b)) :
    ContinuousOn (fun v => c.totalCurvature B.family.metric lambda v +
      c.length B.family.metric lambda v) (Icc a b) := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hB⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hf, _, _, _, _⟩ := hB lambda hlambda
  have hm : Bhat.family.metric =
      fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun F => F.metric) hf
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Icc a b) := by
    rw [hm]
    exact c.isSolutionOn_map A B.family.metric lambda hlambda (uniqueDiffOn_Icc B.lt) hc
  have hΘ : ∀ v ∈ Icc a b,
      c.map.totalCurvature Bhat.family.metric v = c.totalCurvature B.family.metric lambda v := by
    intro v hv
    rw [hm]
    exact c.map_totalCurvature_eq A B.family.metric lambda hlambda hc.smooth hc.immersed v hv
  have hLen : ∀ v ∈ Icc a b,
      c.map.length Bhat.family.metric v = c.length B.family.metric lambda v := by
    intro v hv
    rw [hm]
    exact c.map_length_eq A B.family.metric lambda hlambda hc.smooth v hv
  obtain ⟨hLcont, hΘcont, -, -, -⟩ := rfs_csf_integral_bounds Bhat B.lt Subset.rfl c.map hsol
  exact (hΘcont.add hLcont.continuousOn).congr
    (fun v hv => by
      change c.totalCurvature B.family.metric lambda v + c.length B.family.metric lambda v =
        c.map.totalCurvature Bhat.family.metric v + c.map.length Bhat.family.metric v
      rw [hΘ v hv, hLen v hv])

omit [CompactSpace M] [Nonempty M] in
theorem rfs_csf_total_curvature_slope
    (B : RicciBackground (I := I) (M := M) D a b) :
    curveShorteningTotalCurvatureSlope (I := I) (M := M) B := by
  intro lambda hlambda _ c hc
  refine ⟨ProductCurve.continuousOn_totalCurvature_add_length B c lambda hlambda hc, ?_⟩
  intro t ht ε hε
  obtain ⟨δΘ, hδΘ, hΘ⟩ :=
    ProductCurve.totalCurvature_upper_right_slope B c lambda hlambda hc t ht (ε / 2)
      (half_pos hε)
  obtain ⟨δL, hδL, hL⟩ :=
    ProductCurve.length_upper_right_slope B c lambda hlambda hc t ht (ε / 2) (half_pos hε)
  refine ⟨min δΘ δL, lt_min hδΘ hδL, fun h hh htb => ?_⟩
  have hh1 : h < δΘ := lt_of_lt_of_le hh.2 (min_le_left _ _)
  have hh2 : h < δL := lt_of_lt_of_le hh.2 (min_le_right _ _)
  have h1 := hΘ h ⟨hh.1, hh1⟩ htb
  have h2 := hL h ⟨hh.1, hh2⟩ htb
  have hsplit : (c.totalCurvature B.family.metric lambda (t + h) +
        c.length B.family.metric lambda (t + h)) -
        (c.totalCurvature B.family.metric lambda t + c.length B.family.metric lambda t) =
      (c.totalCurvature B.family.metric lambda (t + h) -
        c.totalCurvature B.family.metric lambda t) +
      (c.length B.family.metric lambda (t + h) - c.length B.family.metric lambda t) := by
    ring
  have hkey : (B.C + B.B₀) * c.totalCurvature B.family.metric lambda t +
        B.C * c.length B.family.metric lambda t + ε / 2 +
        (B.B₀ * c.length B.family.metric lambda t + ε / 2) =
      (B.C + B.B₀) * (c.totalCurvature B.family.metric lambda t +
        c.length B.family.metric lambda t) + ε := by
    ring
  rw [hsplit, add_div]
  linarith [h1, h2, hkey.le, hkey.ge]

omit [CompactSpace M] [Nonempty M] in
theorem rfs_csf_total_curvature_bound
    (B : RicciBackground (I := I) (M := M) D a b) :
    curveShorteningTotalCurvatureBound (I := I) (M := M) B :=
  curveShorteningTotalCurvatureBound_of_slope (I := I) (M := M) B
    (rfs_csf_total_curvature_slope B)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
