import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.HigherDerivativeBernstein
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolution

noncomputable section

open Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.Tensor0SBundle (normSq0S)

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] {T : RealTimeInterval} {a b : ℝ}

theorem exists_uniform_iteratedDs_curvature_bound_of_lower_derivative_bounds
    (B : RicciBackground (I := I) (M := M) T a b) {m : ℕ} (hm : 2 ≤ m)
    {D : ℝ} (hD : 1 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∀ lambda : ℝ, 0 < lambda → ∀ c : ProductCurve M,
      ∀ J : Set ℝ, UniqueDiffOn ℝ J → c.IsSolutionOn B.family.metric lambda J →
      ∀ s u : ℝ, s < u → Icc s u ⊆ Icc a b → Icc s u ⊆ J → u - s ≤ 1 →
      (∀ x t, t ∈ Ioc s u → ∀ j ≤ m,
        c.normSq B.family.metric lambda
          (c.iteratedDs B.family.metric lambda j (c.curvatureVector B.family.metric lambda)) x t ≤
          D ^ 2 / (t - s) ^ (j + 1)) →
      ∀ x, c.normSq B.family.metric lambda
        (c.iteratedDs B.family.metric lambda (m + 1)
          (c.curvatureVector B.family.metric lambda)) x u ≤ A / (u - s) ^ (m + 2) := by
  let Q : QuotientProductAtlas I M := quotientProductAtlas
  obtain ⟨C, hC, _, hprod⟩ := B.exists_uniform_product_curvature_bounds Q (m + 2)
  let F := fun j => 2 * (curvatureForcingConstant j C D) ^ 2 +
    2 * curvatureForcingConstant j C D + 2 * C
  let α := max (F m) (F (m + 1))
  have hcoeff : ∀ j ∈ ({m, m + 1} : Set ℕ),
      2 * (curvatureForcingConstant j C D) ^ 2 +
        2 * curvatureForcingConstant j C D + 2 * C ≤ α := by
    intro j hj
    rcases (show j = m ∨ j = m + 1 by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hj) with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hK : 0 ≤ curvatureForcingConstant m C D :=
    (zero_le_one.trans hC).trans (le_curvatureForcingConstant m (zero_le_one.trans hC) hD)
  have hα : 0 ≤ α := by
    have hh := hcoeff m (by simp)
    nlinarith only [hh, hK, hC, sq_nonneg (curvatureForcingConstant m C D)]
  refine ⟨(3 + 2 * D ^ 2 * (1 + 2 * α)) * 2 ^ (m + 2), by positivity, ?_⟩
  intro lambda hlambda c J hJ hc s u hsu hwindow hinterval hlen hjets
  let _ := Q.charts
  let _ := Q.smoothManifold
  obtain ⟨T', _, _, hBG⟩ := exists_quotientProduct_ricciBackground_on_regular Q B
  obtain ⟨Bhat, hfamily, _, _, _, _⟩ := hBG lambda hlambda
  have hmtr : Bhat.family.metric =
      fun t => quotientProductMetric Q (B.family.metric t) lambda hlambda :=
    congrArg (fun G => G.metric) hfamily
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Icc s u) := by
    rw [hmtr]
    exact (c.isSolutionOn_map Q B.family.metric lambda hlambda hJ hc).mono hinterval
      (fun t ht => (uniqueDiffOn_Icc hsu t ht).uniqueMDiffWithinAt)
  have hambient : ∀ x t, t ∈ Icc s u → ∀ (kind : CurvatureTensorKind) (j : ℕ), j ≤ m + 2 →
      Real.sqrt (normSq0S (Bhat.family.metric t) (c.map.lift x t) (kind.arity + j)
        (kind.field Bhat.family j t (c.map.lift x t))) ≤ C := by
    intro x t ht kind j hj
    rw [hfamily]
    exact hprod lambda hlambda t (hwindow ht) (c.map.lift x t) kind j hj
  have hjets' : ∀ x t, t ∈ Ioc s u → ∀ j ≤ m,
      c.map.normSq Bhat.family.metric
        (c.map.iteratedDs Bhat.family.metric j (c.map.curvatureVector Bhat.family.metric)) x t ≤
        D ^ 2 / (t - s) ^ (j + 1) := by
    intro x t ht j hj
    rw [hmtr]
    rw [c.map_iteratedDs_curvature_normSq Q B.family.metric lambda hlambda hc.smooth hc.immersed
      x t (hinterval ⟨ht.1.le, ht.2⟩) j]
    exact hjets x t ht j hj
  have hh := c.map.iteratedDs_curvature_bernstein_bound_of_normSq_le_div Bhat hsu hwindow hsol
    hm hC hD hcoeff hlen hambient hjets'
  intro x
  have hhx := hh x
  rw [hmtr] at hhx
  rwa [c.map_iteratedDs_curvature_normSq Q B.family.metric lambda hlambda hc.smooth hc.immersed
    x u (hinterval ⟨hsu.le, le_rfl⟩) (m + 1)] at hhx

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
