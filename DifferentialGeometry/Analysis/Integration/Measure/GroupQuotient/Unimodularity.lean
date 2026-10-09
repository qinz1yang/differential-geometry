/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.Lattices.Basic
import Mathlib.MeasureTheory.Group.ModularCharacter

noncomputable section

open Set Function MeasureTheory MeasureTheory.Measure
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped ENNReal

namespace DifferentialGeometry.LatticeMeasure

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {μ : Measure G} [IsHaarMeasure μ] [InnerRegular μ]

theorem quasiMeasurePreserving_right (g : G) :
    QuasiMeasurePreserving (fun x : G => x * g) μ μ where
  measurable := (continuous_mul_const g).measurable
  absolutelyContinuous := by
    rw [map_right_mul_eq_modularCharacterFun_smul μ g]
    intro A hA
    rw [Measure.smul_apply, hA, smul_zero]

variable {Γ : Subgroup G} [Countable Γ]

omit [Countable Γ] in
theorem isFundamentalDomain_preimage_right {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) (g : G) :
    IsFundamentalDomain Γ ((fun x : G => x * g) ⁻¹' F) μ :=
  hF.preimage_of_equiv (quasiMeasurePreserving_right g) bijective_id
    (fun γ x => by
      change ((γ : G) * x) * g = (γ : G) * (x * g)
      exact mul_assoc _ _ _)

theorem modularCharacterFun_eq_one {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) (hvol : μ F ≠ ⊤) (g : G) :
    modularCharacterFun g = 1 := by
  have hpos : μ F ≠ 0 := hF.measure_ne_zero (NeZero.ne μ)
  have hq := quasiMeasurePreserving_right (μ := μ) g
  have hmap : μ.map (fun x : G => x * g) F = μ F := by
    rw [Measure.map_apply₀ hq.measurable.aemeasurable
      (hF.nullMeasurableSet.mono_ac hq.absolutelyContinuous)]
    exact (isFundamentalDomain_preimage_right hF g).measure_eq hF
  rw [map_right_mul_eq_modularCharacterFun_smul μ g, Measure.smul_apply] at hmap
  change (modularCharacterFun g : ℝ≥0∞) * μ F = μ F at hmap
  apply ENNReal.coe_injective
  apply (ENNReal.mul_left_inj hpos hvol).mp
  simpa only [ENNReal.coe_one, one_mul] using hmap

theorem isMulRightInvariant_of_finite_fundamentalDomain {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) (hvol : μ F ≠ ⊤) :
    IsMulRightInvariant μ where
  map_mul_right_eq_self g := by
    rw [map_right_mul_eq_modularCharacterFun_smul μ g,
      modularCharacterFun_eq_one hF hvol g, one_smul]

end Group

section PO

variable {n : ℕ}

theorem volume_isMulRightInvariant (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) [hfd : HasFundamentalDomain Γ (PO n 1)]
    (hcov : covolume Γ (PO n 1) ≠ ⊤) :
    IsMulRightInvariant (volume : Measure (PO n 1)) := by
  let : Countable Γ := DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.countable_of_isDiscrete Γ disc
  let : InnerRegular (volume : Measure (PO n 1)) := by
    change InnerRegular (Measure.haar : Measure (PO n 1))
    infer_instance
  obtain ⟨F, hF⟩ := hfd.ExistsIsFundamentalDomain
  exact isMulRightInvariant_of_finite_fundamentalDomain hF
    (by rwa [← hF.covolume_eq_volume volume])

end PO

end DifferentialGeometry.LatticeMeasure
