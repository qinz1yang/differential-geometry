import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceMetricEvolution

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [T2Space M] [CompactSpace M]

local instance surfaceRoundMeasurable : MeasurableSpace M := borel M
local instance surfaceRoundBorel : BorelSpace M := ⟨rfl⟩

theorem totalScalarCurvature_eq_area_mul_of_spatially_constant
    (g : SmoothRiemannianMetric I M)
    (hconstant : ∃ c : Real, ∀ y : M, metricScalarAt (I := I) g y = c) (x : M) :
    totalScalarCurvature g = surfaceArea g * metricScalarAt (I := I) g x := by
  obtain ⟨c, hc⟩ := hconstant
  have heq : (fun y : M => metricScalarAt (I := I) g y) =
      fun _ : M => metricScalarAt (I := I) g x := by
    funext y
    exact (hc y).trans (hc x).symm
  unfold totalScalarCurvature
  rw [heq, integral_const, smul_eq_mul]
  rfl

section NonemptySurface

variable [Nonempty M]

private theorem surfaceRound_totalScalar_positive
    (g : SmoothRiemannianMetric I M)
    (hpositive : ∀ x : M, 0 < metricScalarAt (I := I) g x)
    (hconstant : ∃ c : Real, ∀ x : M, metricScalarAt (I := I) g x = c) :
    0 < totalScalarCurvature g := by
  let x : M := Classical.choice (inferInstance : Nonempty M)
  rw [totalScalarCurvature_eq_area_mul_of_spatially_constant g hconstant x]
  exact mul_pos (surfaceArea_pos g) (hpositive x)

variable [I.Boundaryless]

theorem ancientSurfaceFlow_scalar_profile_of_spatially_constant
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval) (hS : IsSolutionOn S)
    (hdim : Module.finrank Real E = 2)
    (hpositive : ∀ t ≤ 0, ∀ x : M, 0 < S.scalar t x)
    (hconstant : ∀ t ≤ 0, ∃ c : Real, ∀ x : M, S.scalar t x = c) :
    let T := surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0)
    0 < T ∧ ∀ t : Real, t ≤ 0 → ∀ x : M, S.scalar t x = 1 / (T - t) := by
  let A₀ := surfaceArea (S.family.metric 0)
  let C₀ := totalScalarCurvature (S.family.metric 0)
  let T := A₀ / C₀
  have hCpos : 0 < C₀ := surfaceRound_totalScalar_positive (S.family.metric 0)
    (hpositive 0 le_rfl) (hconstant 0 le_rfl)
  have hCne : C₀ ≠ 0 := hCpos.ne'
  have hTpos : 0 < T := div_pos (surfaceArea_pos (S.family.metric 0)) hCpos
  refine ⟨hTpos, ?_⟩
  intro t ht x
  have hvalue : C₀ = surfaceArea (S.family.metric t) * S.scalar t x := by
    calc
      C₀ = totalScalarCurvature (S.family.metric t) :=
        (ancientSurfaceFlow_totalScalar_eq_terminal S hS hdim ht).symm
      _ = surfaceArea (S.family.metric t) * S.scalar t x :=
        totalScalarCurvature_eq_area_mul_of_spatially_constant
          (S.family.metric t) (hconstant t ht) x
  have hscalar : S.scalar t x = C₀ / surfaceArea (S.family.metric t) := by
    apply (eq_div_iff (surfaceArea_pos (S.family.metric t)).ne').2
    rw [mul_comm]
    exact hvalue.symm
  have harea : surfaceArea (S.family.metric t) = C₀ * (T - t) := by
    calc
      surfaceArea (S.family.metric t) = A₀ - C₀ * t :=
        ancientSurfaceFlow_area_eq_terminal_sub S hS hdim ht
      _ = C₀ * (T - t) := by
        change A₀ - C₀ * t = C₀ * (A₀ / C₀ - t)
        rw [mul_sub, mul_div_cancel₀ A₀ hCne]
  change S.scalar t x = 1 / (T - t)
  rw [hscalar, harea, div_mul_cancel_left₀ hCne, one_div]

theorem ancientSurfaceFlow_roundScaling_of_spatially_constant
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval) (hS : IsSolutionOn S)
    (hdim : Module.finrank Real E = 2)
    (hpositive : ∀ t ≤ 0, ∀ x : M, 0 < S.scalar t x)
    (hconstant : ∀ t ≤ 0, ∃ c : Real, ∀ x : M, S.scalar t x = c) :
    let T := surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0)
    ∃ hT : 0 < T,
      (∀ t : Real, t ≤ 0 → totalScalarCurvature (S.family.metric t) =
        totalScalarCurvature (S.family.metric 0)) ∧
      (∀ t : Real, t ≤ 0 → surfaceArea (S.family.metric t) =
        surfaceArea (S.family.metric 0) - totalScalarCurvature (S.family.metric 0) * t) ∧
      (∀ t : Real, t ≤ 0 → ∀ x : M, S.scalar t x = 1 / (T - t)) ∧
      (∀ (t : Real) (ht : t ≤ 0), S.family.metric t =
        scaleMetric ((T - t) / T) (div_pos (by linarith) hT) (S.family.metric 0)) := by
  obtain ⟨hT, hprofile⟩ :=
    ancientSurfaceFlow_scalar_profile_of_spatially_constant S hS hdim hpositive hconstant
  refine ⟨hT, ?_, ?_, hprofile, ?_⟩
  · exact fun _ ht => ancientSurfaceFlow_totalScalar_eq_terminal S hS hdim ht
  · exact fun _ ht => ancientSurfaceFlow_area_eq_terminal_sub S hS hdim ht
  · intro t ht
    exact surfaceMetric_eq_scale_of_scalar_profile S hS hdim rfl rfl hT hprofile ht

end NonemptySurface

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
