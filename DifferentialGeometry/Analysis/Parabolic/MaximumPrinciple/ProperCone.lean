import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.HeatPotential
import DifferentialGeometry.Analysis.InnerProductSpace.ProperConeIsometry

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff RealInnerProductSpace

universe u uE uH uF

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]

def innerScalarization (u : Real → M → F) (y : F) : Real → M → Real :=
  fun t x ↦ ⟪u t x, y⟫

abbrev innerDualScalarization (u : Real → M → F) (y : F) : Real → M → Real :=
  innerScalarization u y

def IsInnerDualHeatPotSupersolutionOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (potential : Real → M → Real)
    (C : ProperCone Real F)
    (u : Real → M → F) : Prop :=
  ∀ y : F, y ∈ ProperCone.innerDual (C : Set F) →
    IsHeatPotSupersolutionOn D G potential (innerScalarization u y)

abbrev IsInnerDualHeatSupersolutionOn
    (D : RealTimeInterval)
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (C : ProperCone Real F)
    (u : Real → M → F) : Prop :=
  IsInnerDualHeatPotSupersolutionOn D G (fun _ _ ↦ 0) C u

omit [CompleteSpace E] in
theorem properCone_heat_pot_supersolution_mem_of_potential_le
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (potential : Real → M → Real)
    (C : ProperCone Real F)
    (u : Real → M → F)
    (hsol : IsInnerDualHeatPotSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G potential C u)
    (B : Real)
    (hpotential : ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, potential t x ≤ B)
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C := by
  have hscalar : ∀ y : F, y ∈ ProperCone.innerDual (C : Set F) →
      ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M,
        0 ≤ innerScalarization u y t x := by
    intro y hy
    apply heat_pot_supersolution_nonneg (I := I) G hT potential
      (innerScalarization u y) (hsol y hy) B hpotential
    intro x
    exact hy (hinit x)
  intro t ht x
  rw [← C.innerDual_innerDual]
  rw [ProperCone.mem_innerDual]
  intro y hy
  simpa [innerScalarization, real_inner_comm] using hscalar y hy t ht x

omit [CompleteSpace E] in
theorem properCone_heat_supersolution_mem
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T)
    (C : ProperCone Real F)
    (u : Real → M → F)
    (hsol : IsInnerDualHeatSupersolutionOn
      (RealTimeInterval.closed 0 T hT) G C u)
    (hinit : ∀ x : M, u 0 x ∈ C) :
    ∀ t : Real, t ∈ Set.Icc 0 T → ∀ x : M, u t x ∈ C := by
  exact properCone_heat_pot_supersolution_mem_of_potential_le
    (I := I) G hT (fun _ _ ↦ 0) C u hsol 0 (by simp) hinit

end

end DifferentialGeometry.Analysis.Parabolic
