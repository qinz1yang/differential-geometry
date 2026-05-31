import RicciFlower.Coordinates.Normal.Data

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Normal injectivity radius

This file defines the RicciFlower-native injectivity radius attached to the
normal-coordinate exponential endpoint.  It lives below the
Hamilton--Cheeger--Gromov compactness layer: compactness files can later cite
`injRadAtLeast` instead of carrying their own primitive predicate.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace Coordinates
namespace Normal

open scoped ENNReal Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [SigmaCompactSpace M] [T2Space M]

/-- A positive radius whose tangent ball is contained in the source of a C1
exponential local diffeomorphism at `x`. -/
def injRadAdmissible [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) (ρ : Real) : Prop :=
  0 < ρ ∧
    ∃ D : RicciFlower.Coordinates.NormalC1ExpData (I := I) g x,
      Metric.ball (0 : TangentSpace I x) ρ ⊆ D.expLD.source

/-- The normal-coordinate injectivity radius at `x`, as the supremum of all
admissible exponential radii. -/
noncomputable def injRadAt [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) : ℝ≥0∞ :=
  sSup { r : ℝ≥0∞ |
    ∃ ρ : Real,
      injRadAdmissible (I := I) g x ρ ∧
      r = ENNReal.ofReal ρ }

/-- A positive lower bound for the normal-coordinate injectivity radius at
`x`.  This is the form expected by compactness hypotheses. -/
def injRadAtLeast [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) (ρ : Real) : Prop :=
  0 < ρ ∧ ENNReal.ofReal ρ ≤ injRadAt (I := I) g x

/-- Every admissible radius gives a lower bound for `injRadAt`. -/
theorem injRadAtLeast_of_admissible [I.Boundaryless] [CompleteSpace E]
    {g : SmoothRiemannianMetric I M} {x : M} {ρ : Real}
    (hρ : injRadAdmissible (I := I) g x ρ) :
    injRadAtLeast (I := I) g x ρ := by
  refine ⟨hρ.1, ?_⟩
  exact le_sSup (show ENNReal.ofReal ρ ∈
    { r : ℝ≥0∞ |
      ∃ ρ' : Real,
        injRadAdmissible (I := I) g x ρ' ∧
        r = ENNReal.ofReal ρ' } from ⟨ρ, hρ, rfl⟩)

/-- The checked C1 exponential local diffeomorphism supplies at least one
positive admissible radius. -/
theorem exists_injRadAdmissible [I.Boundaryless] [CompleteSpace E]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ ρ : Real, injRadAdmissible (I := I) g x ρ := by
  obtain ⟨D⟩ := RicciFlower.Coordinates.expAt_c1Exp (I := I) g x
  have hnhds : D.expLD.source ∈ 𝓝 (0 : TangentSpace I x) :=
    D.expLD.open_source.mem_nhds D.zero_mem_source
  rw [Metric.mem_nhds_iff] at hnhds
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ := hnhds
  exact ⟨ρ, hρ_pos, D, hρ_sub⟩

/-- The normal-coordinate injectivity radius is positive. -/
theorem injRadAt_pos [I.Boundaryless] [CompleteSpace E]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (g : SmoothRiemannianMetric I M) (x : M) :
    0 < injRadAt (I := I) g x := by
  obtain ⟨ρ, hρ⟩ := exists_injRadAdmissible (I := I) g x
  have hle : ENNReal.ofReal ρ ≤ injRadAt (I := I) g x :=
    (injRadAtLeast_of_admissible (I := I) hρ).2
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hρ.1) hle

end Normal
end Coordinates
end RicciFlower
