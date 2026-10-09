import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinderGauge
import DifferentialGeometry.Geometry.Neck.BufferedRotation
import DifferentialGeometry.Geometry.Neck.Orientation

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Neck

private instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) :=
  ⟨by simp⟩

theorem shrinkingCylinderMetric_eq_flow (t : Set.Iio (1 : ℝ)) :
    shrinkingCylinderMetric t =
      DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t.val := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hs := (Classical.choose_spec (exists_unique_shrinkingCylinderMetric t)).1 x v w
  have hf := DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_inner t.property x v w
  apply hs.trans
  apply Eq.trans _ hf.symm
  unfold shrinkingCylinderInner
  have hfst (u : TangentSpace NeckCylinderModel x) :
      mfderiv NeckCylinderModel ThreeModel (fun p : NeckCylinder => p.1.1) x u =
        dIncl x.1 u.1 := by
    rw [show (fun p : NeckCylinder => (p.1.1 : ThreeSpace)) =
      ((↑) : Sphere 2 → ThreeSpace) ∘ Prod.fst from rfl]
    rw [mfderiv_comp x
      ((contMDiff_coe_sphere (E := ThreeSpace) (n := 2) (m := ∞)).mdifferentiableAt
        (by simp)) mdifferentiableAt_fst, mfderiv_fst]
    rfl
  rw [hfst v, hfst w, mfderiv_snd]
  rfl

theorem pullback_shrinkingCylinderMetric_bufferedCylinderRotation
    (δ : ℝ) (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (t : Set.Iio (1 : ℝ)) :
    Diffeomorph.pullbackMetric ((shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ))
      (bufferedCylinderRotation δ e) =
        (shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ) := by
  rw [shrinkingCylinderMetric_eq_flow]
  apply DifferentialGeometry.PDE.RicciFlow.pullback_shrinkingCylinderMetric_of_initial
    (bufferedCylinder δ) (bufferedCylinder δ) (bufferedCylinderRotation δ e) _ t.property
  simpa only [DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_zero,
    referenceMetric] using
    pullback_referenceMetric_bufferedCylinderRotation δ e

theorem pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderRotation
    (δ : ℝ) (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (t : Set.Iio (1 : ℝ)) :
    Diffeomorph.pullbackMetricCross
      ((shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ))
      (bufferedCylinderRotation δ e) =
        (shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ) := by
  rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
  exact pullback_shrinkingCylinderMetric_bufferedCylinderRotation δ e t

theorem image_bufferedCylinderRotation_neckClosedTest
    (δ : ℝ) (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) :
    bufferedCylinderRotation δ e '' neckClosedTest δ = neckClosedTest δ :=
  image_bufferedCylinderRotation_controlledCylinder δ e

theorem pullback_shrinkingCylinderMetric_bufferedCylinderOrientation
    (δ σ : ℝ) (hσ : σ ^ 2 = 1) (t : Set.Iio (1 : ℝ)) :
    Diffeomorph.pullbackMetric ((shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ))
      (bufferedCylinderOrientation δ σ hσ) =
        (shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ) := by
  rw [shrinkingCylinderMetric_eq_flow]
  apply DifferentialGeometry.PDE.RicciFlow.pullback_shrinkingCylinderMetric_of_initial
    (bufferedCylinder δ) (bufferedCylinder δ) (bufferedCylinderOrientation δ σ hσ) _ t.property
  simpa only [DifferentialGeometry.PDE.RicciFlow.shrinkingCylinderMetric_zero,
    referenceMetric] using
    pullback_referenceMetric_bufferedCylinderOrientation δ σ hσ

theorem pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderOrientation
    (δ σ : ℝ) (hσ : σ ^ 2 = 1) (t : Set.Iio (1 : ℝ)) :
    Diffeomorph.pullbackMetricCross
      ((shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ))
      (bufferedCylinderOrientation δ σ hσ) =
        (shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ) := by
  rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
  exact pullback_shrinkingCylinderMetric_bufferedCylinderOrientation δ σ hσ t

theorem image_bufferedCylinderOrientation_neckClosedTest
    (δ σ : ℝ) (hσ : σ ^ 2 = 1) :
    bufferedCylinderOrientation δ σ hσ '' neckClosedTest δ = neckClosedTest δ :=
  image_bufferedCylinderOrientation_controlledCylinder δ σ hσ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
