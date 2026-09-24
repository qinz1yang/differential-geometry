import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductBackground
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.IntegralBounds

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    {D : RealTimeInterval} {a b s u : ℝ}

omit [SigmaCompactSpace M] in
theorem map_energy_eq (c : ProductCurve M) (A : QuotientProductAtlas I M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.energy (fun τ => quotientProductMetric A (g τ) lambda hlambda) t =
      c.energy g lambda t := by
  let _ := A.charts
  let _ := A.smoothManifold
  simp only [CurveMap.energy, CurveMap.integral, ProductCurve.energy, ProductCurve.integral]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [c.map_curvatureSq_eq A g lambda hlambda hc hi x t ht,
    c.map_speed_eq A g lambda hlambda hc x t ht]

theorem length_energy_bounds
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hc : c.IsSolutionOn B.family.metric lambda J)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (hinterval : Icc s u ⊆ J) :
    ContDiffOn ℝ ∞ (c.length B.family.metric lambda) (Icc s u) ∧
      ContinuousOn (c.energy B.family.metric lambda) (Icc s u) ∧
      ∀ r ∈ Icc s u, ∀ t ∈ Icc r u,
        c.length B.family.metric lambda t ≤
          Real.exp (B.B₀ * (t - r)) * c.length B.family.metric lambda r ∧
        (∫ v in r..t, c.energy B.family.metric lambda v) ≤
          Real.exp (B.B₀ * (t - r)) * c.length B.family.metric lambda r := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hB⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hf, h0, _, _, _⟩ := hB lambda hlambda
  have hm : Bhat.family.metric = fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun F => F.metric) hf
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Icc s u) := by
    rw [hm]
    exact (c.isSolutionOn_map A B.family.metric lambda hlambda hJ hc).mono hinterval
      (fun t ht => ((uniqueDiffOn_Icc hsu) t ht).uniqueMDiffWithinAt)
  have hlength (t : ℝ) (ht : t ∈ Icc s u) :
      c.map.length Bhat.family.metric t = c.length B.family.metric lambda t := by
    rw [hm]
    exact c.map_length_eq A B.family.metric lambda hlambda hc.smooth t (hinterval ht)
  have henergy (t : ℝ) (ht : t ∈ Icc s u) :
      c.map.energy Bhat.family.metric t = c.energy B.family.metric lambda t := by
    rw [hm]
    exact c.map_energy_eq A B.family.metric lambda hlambda hc.smooth hc.immersed t (hinterval ht)
  obtain ⟨hL, _, hE, _, hbound⟩ := rfs_csf_integral_bounds Bhat hsu hwindow c.map hsol
  refine ⟨hL.congr (fun t ht => (hlength t ht).symm),
    hE.congr (fun t ht => (henergy t ht).symm), ?_⟩
  intro r hr t ht
  have htt : t ∈ Icc s u := ⟨hr.1.trans ht.1, ht.2⟩
  have hq := hbound r hr t ht
  have heq : (∫ v in r..t, c.map.energy Bhat.family.metric v) =
      ∫ v in r..t, c.energy B.family.metric lambda v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le ht.1] at hv
    exact henergy v ⟨hr.1.trans hv.1, hv.2.trans ht.2⟩
  constructor
  · simpa only [h0, hlength r hr, hlength t htt] using hq.1
  · simpa only [h0, hlength r hr, heq] using hq.2.1

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
