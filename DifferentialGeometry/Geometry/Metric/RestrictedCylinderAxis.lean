import DifferentialGeometry.Geometry.Metric.Cylinder
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenSubtype

noncomputable section
open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def restrictedCylinderAxis (U : TopologicalSpace.Opens (M × ℝ)) (x : U) :
    TangentSpace (I.prod 𝓘(ℝ)) x := cylinderAxis (I := I) (x : M × ℝ)

theorem contMDiff_restrictedCylinderAxis
    [FiniteDimensional ℝ E] (U : TopologicalSpace.Opens (M × ℝ)) :
    ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent ∞
      (fun x : U ↦ (⟨x, restrictedCylinderAxis U x⟩ : TangentBundle (I.prod 𝓘(ℝ)) U)) := by
  let : CompleteSpace (E × ℝ) := FiniteDimensional.complete ℝ (E × ℝ)
  let Y : ContMDiffSection (I.prod 𝓘(ℝ)) (E × ℝ) ∞ (TangentSpace (I.prod 𝓘(ℝ)) : M × ℝ → Type _) :=
    ⟨cylinderAxis, contMDiff_cylinderAxis⟩
  have h := contMDiff_restrictOpen_section (I := I.prod 𝓘(ℝ)) U Y
  convert h using 1
  first
    | rfl
    | (funext x; rw [restrictOpenTangentField_apply]; rfl)

theorem restrictedCylinderAxis_unit
    [FiniteDimensional ℝ E] [T2Space M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens (M × ℝ)) (x : U) :
    ((cylinderMetric g).restrictOpen U).inner x
      (restrictedCylinderAxis U x) (restrictedCylinderAxis U x) = 1 :=
  cylinderMetric_axis_unit g (x : M × ℝ)

theorem restrictedCylinderAxis_inner
    [FiniteDimensional ℝ E] [T2Space M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens (M × ℝ))
    (x : U) (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
    ((cylinderMetric g).restrictOpen U).inner x (restrictedCylinderAxis U x) v =
      mvfderiv (I.prod 𝓘(ℝ)) (fun y : U ↦ (y : M × ℝ).2) x v := by
  have h := mvfderiv_restrictOpen (I := I.prod 𝓘(ℝ)) U Prod.snd x v
    (contMDiff_snd.mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) (x : M × ℝ))
  exact (cylinderMetric_axis_inner g (x : M × ℝ) v).trans h.symm

end DifferentialGeometry.Geometry.Metric
