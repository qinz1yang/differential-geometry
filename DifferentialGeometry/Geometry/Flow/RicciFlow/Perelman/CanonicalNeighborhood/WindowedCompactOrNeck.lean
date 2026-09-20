import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniformSpatialNeckCenters
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedStaticComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSpatialNeckTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_windowed_scalar_comparison_or_spatial_neck
    (kappa : ℝ) {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ delta0 r C : ℝ, 0 < delta0 ∧ 0 < r ∧ 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (delta : ℝ) (x : M) (t : ℝ) (W : WindowedModelWitness delta kappa S x t),
        delta ≤ delta0 → TangentOrientationSection W.model.M →
        (∀ z : M, S.scalar t x ≤ C * S.scalar t z) ∨
        ∃ y : W.model.M, Nonempty (SpatialNeck (S.base.metric t) (2 * alpha) (W.embedding y)) ∧
          C⁻¹ * S.scalar t x ≤ S.scalar t (W.embedding y) ∧
          S.scalar t (W.embedding y) ≤ C * S.scalar t x ∧
          Real.sqrt (S.scalar t x) * metricDistance (S.base.metric t) x (W.embedding y) ≤ r := by
  let beta := neckModelTolerance alpha / 2
  have htol : neckModelTolerance alpha < alpha :=
    (neckModelTolerance_le_smallness alpha).trans_lt
      (backgroundJetSmallness_ceil_lt_self _ ha hsmall)
  have hb : 0 < beta := half_pos (neckModelTolerance_pos ha)
  have hbsmall : beta < 1 / 32 := by dsimp only [beta]; linarith
  obtain ⟨rho, C0, hrho, hC0, hmodel⟩ :=
    exists_uniform_compact_or_spatial_neck_of_oriented_ancient_kappa.{u} kappa hb hbsmall
  let K := 2 * max C0 1
  have hK : 1 ≤ K := by dsimp only [K]; linarith [le_max_right C0 1]
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hC0K : C0 ≤ K := by dsimp only [K]; linarith [le_max_left C0 1, le_max_right C0 1]
  obtain ⟨d, hd, htransfer⟩ :=
    exists_windowed_spatial_neck_center_transfer_threshold.{u} ha hsmall hrho.le hK
  let A := 486 * K * (1 + 3 * K)
  have hA : 0 < A := by dsimp [A]; positivity
  let delta0 := min d (min ((rho + 1)⁻¹ ^ 2) A⁻¹)
  refine ⟨delta0, 2 * rho, 2 * K,
    lt_min hd (lt_min (by positivity) (inv_pos.mpr hA)), by positivity, by positivity, ?_⟩
  intro M _ _ _ _ _ _ D S delta x t W hdelta orient
  have hdd : delta ≤ d := hdelta.trans (min_le_left _ _)
  have hrest := hdelta.trans (min_le_right _ _)
  have hdR : delta ≤ (rho + 1)⁻¹ ^ 2 := hrest.trans (min_le_left _ _)
  have hdA : delta ≤ A⁻¹ := hrest.trans (min_le_right _ _)
  have hscalar : 486 * K * (1 + 3 * K) * delta ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdA hA.le
    rwa [mul_inv_cancel₀ hA.ne'] at hh
  have hbuffer : rho ≤ modelRadius delta := by
    have hh := modelRadius_anti W.eps_pos hdR
    have heq : modelRadius ((rho + 1)⁻¹ ^ 2) = rho + 1 := by
      rw [modelRadius, Real.sqrt_sq (by positivity), inv_inv]
    rw [heq] at hh
    linarith
  have hqlo (y : W.model.M) (hy : C0⁻¹ ≤ W.model.S.scalar 0 y) :
      K⁻¹ ≤ W.model.S.scalar 0 y := (inv_anti₀ hC0 hC0K).trans hy
  have hrm (y : W.model.M) (hy : W.model.S.scalar 0 y ≤ C0) :
      W.model.rmNormSq 0 y ≤ K ^ 2 := by
    have hnorm := ancientKappa_rmNormLeScalar W.model (by simp [ThreeSpace])
      W.model_ancient 0 (by simp) y
    have hsqrt3 : Real.sqrt (3 : ℝ) ≤ 2 := by
      apply (Real.sqrt_le_iff).mpr
      norm_num
    have hnonneg := ancientKappa_scalar_nonneg W.model W.model_ancient le_rfl y
    have hupper : Real.sqrt (W.model.rmNormSq 0 y) ≤ K := by
      have hmul := mul_le_mul hsqrt3 hy hnonneg (by norm_num : (0 : ℝ) ≤ 2)
      exact hnorm.trans (hmul.trans (by dsimp [K]; nlinarith [le_max_left C0 1]))
    have heq := Real.sq_sqrt (pointedFlow_rmNormSq_nonneg W.model 0 y)
    nlinarith [Real.sqrt_nonneg (W.model.rmNormSq 0 y)]
  rcases hmodel W.model W.model_ancient W.model_scalar_base orient with hcompact | hneck
  · left
    intro z
    exact W.scalar_le_of_bounded_model hK hscalar hbuffer (fun y =>
      ⟨(hcompact.2 y).1, hqlo y (hcompact.2 y).2.1,
        (hcompact.2 y).2.2.trans hC0K, hrm y (hcompact.2 y).2.2⟩)
  · obtain ⟨y, hy, hlo, hhi, ⟨neck⟩⟩ := hneck
    have hnktol : 2 * beta = neckModelTolerance alpha := by dsimp [beta]; ring
    rw [hnktol] at neck
    obtain ⟨nk, hmap, hlow, hhigh, hdist⟩ :=
      htransfer M D S delta kappa x t W hdd y hy (hqlo y hlo) (hhi.trans hC0K) (hrm y hhi) neck
    exact Or.inr ⟨y, ⟨nk⟩, hlow, hhigh, hdist⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
