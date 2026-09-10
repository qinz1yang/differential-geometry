import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold
open DifferentialGeometry.Geometry
open scoped Manifold ContDiff Topology


abbrev SpatialNeckSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1


abbrev SpatialNeckCylinder := SpatialNeckSphere × ℝ


abbrev SpatialNeckCylinderModel := (𝓡 2).prod 𝓘(ℝ, ℝ)

private local instance unitCylinderSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private abbrev SphereModelSpace := EuclideanSpace ℝ (Fin 2)
private abbrev CylinderModelSpace := SphereModelSpace × ℝ

private def unitCylinderInner (p : SpatialNeckCylinder) :
    TangentSpace SpatialNeckCylinderModel p →L[ℝ]
      TangentSpace SpatialNeckCylinderModel p →L[ℝ] ℝ :=
  ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1).bilinearComp
      (ContinuousLinearMap.fst ℝ SphereModelSpace ℝ)
      (ContinuousLinearMap.fst ℝ SphereModelSpace ℝ) +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (ContinuousLinearMap.snd ℝ SphereModelSpace ℝ)
      (ContinuousLinearMap.snd ℝ SphereModelSpace ℝ)

private theorem unitCylinderInner_apply (p : SpatialNeckCylinder)
    (V W : TangentSpace SpatialNeckCylinderModel p) :
    unitCylinderInner p V W =
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1 V.1 W.1 +
        V.2 * W.2 := rfl

private theorem unitCylinderInner_pos (p : SpatialNeckCylinder)
    (V : TangentSpace SpatialNeckCylinderModel p) (hV : V ≠ 0) :
    0 < unitCylinderInner p V V := by
  rw [unitCylinderInner_apply]
  by_cases hhorizontal : V.1 = 0
  · have hvertical : V.2 ≠ 0 := by
      intro hv
      exact hV (Prod.ext hhorizontal hv)
    have hzero :
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1 V.1 V.1 = 0 := by
      exact (congrArg (fun v : TangentSpace (𝓡 2) p.1 =>
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1 v v)
        hhorizontal).trans
          (map_zero ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1 0))
    rw [hzero, zero_add]
    nlinarith [sq_pos_of_ne_zero hvertical]
  · have hround := (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).pos
      p.1 V.1 hhorizontal
    nlinarith [sq_nonneg V.2]

private theorem unitCylinder_horizontal_section
    (Y : ContMDiffSection SpatialNeckCylinderModel CylinderModelSpace ∞
      (TangentSpace SpatialNeckCylinderModel : SpatialNeckCylinder → Type _)) :
    ContMDiff SpatialNeckCylinderModel ((𝓡 2).prod 𝓘(ℝ, SphereModelSpace)) ∞
      (fun p : SpatialNeckCylinder => TotalSpace.mk' SphereModelSpace
        (E := TangentSpace (𝓡 2)) p.1 (Y p).1) := by
  have hf : ContMDiff SpatialNeckCylinderModel (𝓡 2) ∞
      (Prod.fst : SpatialNeckCylinder → SpatialNeckSphere) := contMDiff_fst
  have ht : ContMDiff SpatialNeckCylinderModel ((𝓡 2).prod 𝓘(ℝ, SphereModelSpace)) ∞
      (fun p : SpatialNeckCylinder => TotalSpace.mk' SphereModelSpace
        (E := TangentSpace (𝓡 2)) p.1
        (mfderiv SpatialNeckCylinderModel (𝓡 2) Prod.fst p (Y p))) :=
    (hf.contMDiff_tangentMap (le_refl _)).comp Y.contMDiff
  have heq : (fun p : SpatialNeckCylinder => TotalSpace.mk' SphereModelSpace
      (E := TangentSpace (𝓡 2)) p.1
      (mfderiv SpatialNeckCylinderModel (𝓡 2) Prod.fst p (Y p))) =
      (fun p : SpatialNeckCylinder => TotalSpace.mk' SphereModelSpace
        (E := TangentSpace (𝓡 2)) p.1 (Y p).1) := by
    funext p
    rw [mfderiv_fst]
    rfl
  rw [heq] at ht
  exact ht

private theorem unitCylinder_vertical_section
    (Y : ContMDiffSection SpatialNeckCylinderModel CylinderModelSpace ∞
      (TangentSpace SpatialNeckCylinderModel : SpatialNeckCylinder → Type _)) :
    ContMDiff SpatialNeckCylinderModel 𝓘(ℝ, ℝ) ∞
      (fun p : SpatialNeckCylinder => (Y p).2) := by
  have hf : ContMDiff SpatialNeckCylinderModel 𝓘(ℝ, ℝ) ∞
      (Prod.snd : SpatialNeckCylinder → ℝ) := contMDiff_snd
  have ht' : ContMDiff SpatialNeckCylinderModel (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : SpatialNeckCylinder => TotalSpace.mk' ℝ
        (E := TangentSpace 𝓘(ℝ, ℝ)) p.2
        (mfderiv SpatialNeckCylinderModel 𝓘(ℝ, ℝ) Prod.snd p (Y p))) :=
    (hf.contMDiff_tangentMap (le_refl _)).comp Y.contMDiff
  have heq : (fun p : SpatialNeckCylinder => TotalSpace.mk' ℝ
      (E := TangentSpace 𝓘(ℝ, ℝ)) p.2
      (mfderiv SpatialNeckCylinderModel 𝓘(ℝ, ℝ) Prod.snd p (Y p))) =
      (fun p : SpatialNeckCylinder => TotalSpace.mk' ℝ
        (E := TangentSpace 𝓘(ℝ, ℝ)) p.2 (Y p).2) := by
    funext p
    rw [mfderiv_snd]
    rfl
  have ht : ContMDiff SpatialNeckCylinderModel (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : SpatialNeckCylinder => TotalSpace.mk' ℝ
        (E := TangentSpace 𝓘(ℝ, ℝ)) p.2 (Y p).2) := by
    rw [heq] at ht'
    exact ht'
  intro p
  have hp := ht p
  rw [contMDiffAt_totalSpace] at hp
  simpa only [trivializationAt_model_space_apply] using hp.2

private theorem unitCylinder_evaluation_smooth
    (Y W : ContMDiffSection SpatialNeckCylinderModel CylinderModelSpace ∞
      (TangentSpace SpatialNeckCylinderModel : SpatialNeckCylinder → Type _)) :
    ContMDiff SpatialNeckCylinderModel 𝓘(ℝ, ℝ) ∞
      (fun p : SpatialNeckCylinder => unitCylinderInner p (Y p) (W p)) := by
  have hv := unitCylinder_horizontal_section Y
  have hw := unitCylinder_horizontal_section W
  have hg : ContMDiff SpatialNeckCylinderModel
      ((𝓡 2).prod 𝓘(ℝ, SphereModelSpace →L[ℝ] SphereModelSpace →L[ℝ] ℝ)) ∞
      (fun p : SpatialNeckCylinder => TotalSpace.mk'
        (SphereModelSpace →L[ℝ] SphereModelSpace →L[ℝ] ℝ)
        (E := fun y : SpatialNeckSphere =>
          TangentSpace (𝓡 2) y →L[ℝ] TangentSpace (𝓡 2) y →L[ℝ] ℝ)
        p.1 ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1)) :=
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).contMDiff.comp contMDiff_fst
  have htotal : ContMDiff SpatialNeckCylinderModel ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : SpatialNeckCylinder => TotalSpace.mk' ℝ
        (E := Bundle.Trivial SpatialNeckSphere ℝ) p.1
        ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1
          (Y p).1 (W p).1)) :=
    ContMDiff.clm_bundle_apply₂
      (E₁ := fun y : SpatialNeckSphere => TangentSpace (𝓡 2) y)
      (E₂ := fun y : SpatialNeckSphere => TangentSpace (𝓡 2) y)
      (E₃ := fun _ : SpatialNeckSphere => ℝ)
      (b := fun p : SpatialNeckCylinder => p.1)
      (ψ := fun p : SpatialNeckCylinder =>
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1)
      (v := fun p : SpatialNeckCylinder => (Y p).1)
      (w := fun p : SpatialNeckCylinder => (W p).1) hg hv hw
  have hround : ContMDiff SpatialNeckCylinderModel 𝓘(ℝ, ℝ) ∞
      (fun p : SpatialNeckCylinder =>
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1
          (Y p).1 (W p).1) := by
    intro p
    have hp := htotal p
    rw [contMDiffAt_totalSpace] at hp
    exact hp.2
  have heq : (fun p : SpatialNeckCylinder => unitCylinderInner p (Y p) (W p)) =
      (fun p : SpatialNeckCylinder =>
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1
          (Y p).1 (W p).1) +
        (fun p : SpatialNeckCylinder => (Y p).2) * (fun p => (W p).2) := by
    funext p
    exact unitCylinderInner_apply p (Y p) (W p)
  rw [heq]
  exact hround.add ((unitCylinder_vertical_section Y).mul (unitCylinder_vertical_section W))

def unitCylinderMetric :
    SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder where
  inner := unitCylinderInner
  symm p V W := by
    rw [unitCylinderInner_apply, unitCylinderInner_apply,
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).symm p.1 V.1 W.1,
      mul_comm V.2 W.2]
  pos := unitCylinderInner_pos
  isVonNBounded p := posDef_isVonNBounded (E := CylinderModelSpace) (unitCylinderInner p)
    (fun V hV => unitCylinderInner_pos p V hV)
  contMDiff := by
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun p : SpatialNeckCylinder =>
        TangentSpace SpatialNeckCylinderModel p →L[ℝ] ℝ)
      (φ := unitCylinderInner)
    intro Y
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun _ : SpatialNeckCylinder => ℝ)
      (φ := fun p => unitCylinderInner p (Y p))
    intro W p
    rw [contMDiffAt_section]
    refine ((unitCylinder_evaluation_smooth Y W) p).congr_of_eventuallyEq ?_
    filter_upwards with q
    rfl

theorem unitCylinderMetric_inner (y : SpatialNeckSphere) (z : ℝ)
    (v w : TangentSpace (𝓡 2) y) (a b : ℝ) :
    unitCylinderMetric.inner (y, z) (v, a) (w, b) =
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w + a * b := rfl

theorem unitCylinderMetric_unique
    (g : SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder)
    (hinner : ∀ (y : SpatialNeckSphere) (z : ℝ)
      (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
      g.inner (y, z) (v, a) (w, b) =
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w + a * b) :
    g = unitCylinderMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro p V W
  exact hinner p.1 p.2 V.1 W.1 V.2 W.2

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
