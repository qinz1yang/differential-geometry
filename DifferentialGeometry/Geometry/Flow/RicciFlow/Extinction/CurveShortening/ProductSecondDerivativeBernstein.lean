import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SecondDerivativeBernstein
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolution

noncomputable section

open Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] {T : RealTimeInterval} {a b : ℝ}

theorem exists_uniform_iteratedDs_two_curvature_bound_of_lower_derivative_bounds
    (B : RicciBackground (I := I) (M := M) T a b) {D : ℝ} (hD : 1 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∀ lambda : ℝ, 0 < lambda → ∀ c : ProductCurve M,
      ∀ J : Set ℝ, UniqueDiffOn ℝ J → c.IsSolutionOn B.family.metric lambda J →
      ∀ s u : ℝ, s < u → Icc s u ⊆ Icc a b → Icc s u ⊆ J → u - s ≤ 1 →
      (∀ x t, t ∈ Ioc s u → ∀ j ≤ 1,
        c.normSq B.family.metric lambda
          (c.iteratedDs B.family.metric lambda j (c.curvatureVector B.family.metric lambda)) x t ≤
          D ^ 2 / (t - s) ^ (j + 1)) →
      ∀ x, c.normSq B.family.metric lambda
        (c.iteratedDs B.family.metric lambda 2 (c.curvatureVector B.family.metric lambda)) x u ≤
        A / (u - s) ^ 3 := by
  let Q : QuotientProductAtlas I M := quotientProductAtlas
  obtain ⟨C₀, hC₀, _, hprod⟩ := B.exists_uniform_product_curvature_bounds Q 3
  let C := max C₀ B.C
  have hC : 1 ≤ C := hC₀.trans (le_max_left C₀ B.C)
  have hBC : B.C ≤ C := le_max_right C₀ B.C
  let α := max (64 * (1 + C) * D ^ 2)
    (2 * (curvatureForcingConstant 2 C D) ^ 2 +
      2 * curvatureForcingConstant 2 C D + 2 * C)
  have hfirst : 64 * (1 + C) * D ^ 2 ≤ α := le_max_left _ _
  have hnext : 2 * (curvatureForcingConstant 2 C D) ^ 2 +
      2 * curvatureForcingConstant 2 C D + 2 * C ≤ α := le_max_right _ _
  have hα : 0 ≤ α := (by positivity : 0 ≤ 64 * (1 + C) * D ^ 2).trans hfirst
  refine ⟨(1 + 2 * D ^ 2 * (1 + 3 * α)) * 8, by positivity, ?_⟩
  intro lambda hlambda c J hJ hc s u hsu hwindow hinterval hlen hjets
  let _ := Q.charts
  let _ := Q.smoothManifold
  obtain ⟨T', _, _, hBG⟩ := exists_quotientProduct_ricciBackground_on_regular Q B
  obtain ⟨Bhat, hfamily, _, _, _, hBCeq⟩ := hBG lambda hlambda
  have hm : Bhat.family.metric =
      fun τ => quotientProductMetric Q (B.family.metric τ) lambda hlambda :=
    congrArg (fun G => G.metric) hfamily
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Icc s u) := by
    rw [hm]
    exact (c.isSolutionOn_map Q B.family.metric lambda hlambda hJ hc).mono hinterval
      (fun t ht => (uniqueDiffOn_Icc hsu t ht).uniqueMDiffWithinAt)
  have hambient (x t : ℝ) (ht : t ∈ Icc s u) (kind : CurvatureTensorKind)
      (j : ℕ) (hj : j ≤ 3) :
      Real.sqrt (normSq0S (Bhat.family.metric t) (c.map.lift x t) (kind.arity + j)
        (kind.field Bhat.family j t (c.map.lift x t))) ≤ C := by
    rw [hfamily]
    exact (hprod lambda hlambda t (hwindow ht) (c.map.lift x t) kind j hj).trans
      (le_max_left C₀ B.C)
  have hjets' (x t : ℝ) (ht : t ∈ Ioc s u) (j : ℕ) (hj : j ≤ 1) :
      c.map.normSq Bhat.family.metric
        (c.map.iteratedDs Bhat.family.metric j (c.map.curvatureVector Bhat.family.metric)) x t ≤
        D ^ 2 / (t - s) ^ (j + 1) := by
    rw [hm, c.map_iteratedDs_curvature_normSq Q B.family.metric lambda hlambda
      hc.smooth hc.immersed x t (hinterval ⟨ht.1.le, ht.2⟩) j]
    exact hjets x t ht j hj
  have hh := c.map.iteratedDs_two_curvature_bernstein_bound_of_normSq_le_div Bhat hsu
    hwindow hsol hC (hBCeq.trans_le hBC) hD hfirst hnext hlen hambient hjets'
  intro x
  have hresult := hh x
  rw [hm, c.map_iteratedDs_curvature_normSq Q B.family.metric lambda hlambda
    hc.smooth hc.immersed x u (hinterval ⟨hsu.le, le_rfl⟩) 2] at hresult
  exact hresult

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
