import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryFlowExitDomain
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback

/-!
Ricci curvature transports across actual local isometries on genuine boundaryless spaces.
The old corners model is retained on the original true interior, without changing original M.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

section LocalRicci

variable {E : Type*} [sourceNorm : NormedAddCommGroup E]
  [sourceSpace : NormedSpace ℝ E] [sourceFinite : FiniteDimensional ℝ E]
  {F : Type*} [targetNorm : NormedAddCommGroup F]
  [targetSpace : NormedSpace ℝ F] [targetFinite : FiniteDimensional ℝ F]
  {H : Type*} [sourceModelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [targetModelTopology : TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {P : Type*} [sourceTopology : TopologicalSpace P] [sourceCharts : ChartedSpace H P]
  [sourceSmooth : IsManifold I ∞ P] [sourceT2 : T2Space P]
  [sourceInterior : BoundarylessManifold I P]
  {Q : Type*} [targetTopology : TopologicalSpace Q] [targetCharts : ChartedSpace G Q]
  [targetSmooth : IsManifold J ∞ Q] [targetT2 : T2Space Q]
  [targetInterior : BoundarylessManifold J Q]

theorem boundaryInterior_ricci_localPull (g : SmoothRiemannianMetric J Q) (f : P → Q)
    (hf : IsLocalDiffeomorph I J ∞ f) (x : P) (v w : TangentSpace I x) :
    ricciTensor (DifferentialGeometry.localPullMetric g f hf) x v w =
      ricciTensor g (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
  classical
  let sourceComplete : CompleteSpace E := FiniteDimensional.complete ℝ E
  let targetComplete : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis
    (DifferentialGeometry.localPullMetric g f hf) x
  let df : TangentSpace I x ≃L[ℝ] TangentSpace J (f x) :=
    hf.mfderivToContinuousLinearEquiv (by simp) x
  let e : Fin (Module.finrank ℝ (TangentSpace I x)) ≃
      Fin (Module.finrank ℝ (TangentSpace J (f x))) := finCongr df.toLinearEquiv.finrank_eq
  let basis' : Module.Basis (Fin (Module.finrank ℝ (TangentSpace J (f x)))) ℝ
      (TangentSpace J (f x)) := (basis.map df.toLinearEquiv).reindex e
  have hdf (z : TangentSpace I x) : df z = mfderiv I J f x z := by
    have hc := hf.mfderivToContinuousLinearEquiv_coe (x := x) (by simp)
    exact congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace J (f x) => L z) hc
  have hbasis (j : Fin (Module.finrank ℝ (TangentSpace J (f x)))) :
      basis' j = mfderiv I J f x (basis (e.symm j)) := by
    change ((basis.map df.toLinearEquiv).reindex e) j = _
    rw [Module.Basis.reindex_apply, Module.Basis.map_apply]
    exact hdf _
  have hON' : ∀ i j, g.inner (f x) (basis' i) (basis' j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hbasis, hbasis, ← DifferentialGeometry.localPullMetric_inner g f hf x]
    simpa using hON (e.symm i) (e.symm j)
  rw [ricciTensor_eq_orthonormal_trace (DifferentialGeometry.localPullMetric g f hf)
      x v w (fun i => basis i) hON,
    ricciTensor_eq_orthonormal_trace g (f x) (mfderiv I J f x v) (mfderiv I J f x w)
      (fun i => basis' i) hON']
  refine Fintype.sum_equiv e _ _ ?_
  intro i
  have hcomp : basis' (e i) = mfderiv I J f x (basis i) := by
    simpa using hbasis (e i)
  rw [hcomp]
  rw [(DifferentialGeometry.localPullMetric g f hf).symm x,
    ← metricRm04StandardAt_eq_inner_riemannOp,
    metricRm04StandardAt_localPullMetric g f hf x,
    metricRm04StandardAt_eq_inner_riemannOp,
    g.symm (f x)]

end LocalRicci

section OriginalInterior

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem interiorRicci_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryInteriorAtlas_ricci (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      interiorRicci_infty_ne_zero (M := M)
    let Φ := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    ∀ (x : U) (v w : TangentSpace 𝓘(ℝ, E) x),
      ricciTensor (boundaryInteriorAtlasMetric g) x v w =
        ricciTensor (g.restrictOpen U) (Φ.symm x)
          (mfderiv 𝓘(ℝ, E) I Φ.symm x v) (mfderiv 𝓘(ℝ, E) I Φ.symm x w) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    interiorRicci_infty_ne_zero (M := M)
  let Φ := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  dsimp only
  intro x v w
  have hRic := boundaryInterior_ricci_localPull (g.restrictOpen U) Φ.symm
    Φ.symm.isLocalDiffeomorph x v w
  rw [← DifferentialGeometry.Diffeomorph.pullbackMetricCross_eq_localPullMetric] at hRic
  exact hRic

theorem boundaryInteriorAtlas_ricci_lower (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      interiorRicci_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    ∀ κ : ℝ, (∀ (x : U) (v : TangentSpace I x),
      -2 * κ ^ 2 * (g.restrictOpen U).inner x v v ≤ ricciTensor (g.restrictOpen U) x v v) →
      ∀ (x : U) (v : TangentSpace 𝓘(ℝ, E) x),
        -2 * κ ^ 2 * (boundaryInteriorAtlasMetric g).inner x v v ≤
          ricciTensor (boundaryInteriorAtlasMetric g) x v v := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    interiorRicci_infty_ne_zero (M := M)
  let Φ := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  dsimp only
  intro κ hRic x v
  have hcurve := boundaryInteriorAtlas_ricci g x v v
  have hinner := DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner
    (g.restrictOpen U) Φ.symm x v v
  change (boundaryInteriorAtlasMetric g).inner x v v = _ at hinner
  rw [hcurve, hinner]
  exact hRic (Φ.symm x) (mfderiv 𝓘(ℝ, E) I Φ.symm x v)

end OriginalInterior

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
