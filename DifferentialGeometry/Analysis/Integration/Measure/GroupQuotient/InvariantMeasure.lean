/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Integration.Measure.GroupQuotient.Unimodularity

noncomputable section

open Set Function MeasureTheory MeasureTheory.Measure
open scoped ENNReal Pointwise
open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.HomogeneousSpaceMeasure

variable {G : Type*} [Group G]

abbrev FrameQuotient (Γ : Subgroup G) := MulAction.orbitRel.Quotient Γ G

def projection (Γ : Subgroup G) : G → FrameQuotient Γ := Quotient.mk''

theorem projection_smul (Γ : Subgroup G) (γ : Γ) (x : G) :
    projection Γ ((γ : G) * x) = projection Γ x :=
  Quotient.sound ⟨γ, rfl⟩

def right (Γ : Subgroup G) (g : G) : FrameQuotient Γ → FrameQuotient Γ :=
  Quotient.map (fun x => x * g) fun x y h => by
    obtain ⟨γ, hγ⟩ := h
    refine ⟨γ, ?_⟩
    change (γ : G) * y = x at hγ
    change (γ : G) * (y * g) = x * g
    simpa only [mul_assoc] using congrArg (fun z : G => z * g) hγ

@[simp] theorem right_projection (Γ : Subgroup G) (g x : G) :
    right Γ g (projection Γ x) = projection Γ (x * g) := rfl

@[simp] theorem right_one (Γ : Subgroup G) (q : FrameQuotient Γ) : right Γ 1 q = q := by
  induction q using Quotient.inductionOn with
  | h x => change projection Γ (x * 1) = projection Γ x; rw [mul_one]

theorem right_mul (Γ : Subgroup G) (g h : G) (q : FrameQuotient Γ) :
    right Γ (g * h) q = right Γ h (right Γ g q) := by
  induction q using Quotient.inductionOn with
  | h x => change projection Γ (x * (g * h)) = projection Γ ((x * g) * h); rw [mul_assoc]

def rightEquiv (Γ : Subgroup G) (g : G) : FrameQuotient Γ ≃ FrameQuotient Γ where
  toFun := right Γ g
  invFun := right Γ g⁻¹
  left_inv q := by rw [← right_mul, mul_inv_cancel, right_one]
  right_inv q := by rw [← right_mul, inv_mul_cancel, right_one]

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
theorem measurable_projection (Γ : Subgroup G) : Measurable (projection Γ) :=
  measurable_quotient_mk''

theorem measurable_right (Γ : Subgroup G) (g : G) : Measurable (right Γ g) := by
  apply measurable_from_quotient.mpr
  exact (measurable_projection Γ).comp (continuous_mul_const g).measurable

def rightMeasurableEquiv (Γ : Subgroup G) (g : G) : FrameQuotient Γ ≃ᵐ FrameQuotient Γ where
  toEquiv := rightEquiv Γ g
  measurable_toFun := measurable_right Γ g
  measurable_invFun := measurable_right Γ g⁻¹

variable (μ : Measure G) (Γ : Subgroup G)
variable [hfd : HasFundamentalDomain Γ G μ]

def quotientMeasure : Measure (FrameQuotient Γ) :=
  (μ.restrict hfd.ExistsIsFundamentalDomain.choose).map (projection Γ)

variable [Countable Γ] [IsMulLeftInvariant μ]

theorem quotientMeasure_eq {D : Set G} (hD : IsFundamentalDomain Γ D μ) :
    quotientMeasure μ Γ = (μ.restrict D).map (projection Γ) :=
  hfd.ExistsIsFundamentalDomain.choose_spec.quotientMeasure_eq μ hD

theorem quotientMeasure_apply {D : Set G} (hD : IsFundamentalDomain Γ D μ)
    {U : Set (FrameQuotient Γ)} (hU : MeasurableSet U) :
    quotientMeasure μ Γ U = μ (projection Γ ⁻¹' U ∩ D) := by
  rw [quotientMeasure_eq μ Γ hD, Measure.map_apply (measurable_projection Γ) hU,
    Measure.restrict_apply ((measurable_projection Γ) hU)]

theorem quotientMeasure_univ : quotientMeasure μ Γ univ = covolume Γ G μ := by
  obtain ⟨D, hD⟩ := hfd.ExistsIsFundamentalDomain
  rw [quotientMeasure_apply μ Γ hD MeasurableSet.univ]
  simpa using (hD.covolume_eq_volume μ).symm

theorem quotientMeasure_null_iff {U : Set (FrameQuotient Γ)} (hU : MeasurableSet U) :
    quotientMeasure μ Γ U = 0 ↔ μ (projection Γ ⁻¹' U) = 0 := by
  obtain ⟨D, hD⟩ := hfd.ExistsIsFundamentalDomain
  rw [quotientMeasure_apply μ Γ hD hU]
  constructor
  · apply hD.measure_zero_of_invariant
    intro γ
    ext x
    rw [mem_smul_set_iff_inv_smul_mem]
    change projection Γ ((γ⁻¹ : Γ) * x) ∈ U ↔ projection Γ x ∈ U
    rw [projection_smul]
  · exact measure_mono_null inter_subset_left

variable [IsMulRightInvariant μ]

theorem quotientMeasure_right (g : G) :
    MeasurePreserving (right Γ g) (quotientMeasure μ Γ) (quotientMeasure μ Γ) where
  measurable := measurable_right Γ g
  map_eq := by
    ext U hU
    obtain ⟨D, hD⟩ := hfd.ExistsIsFundamentalDomain
    let D' := (fun x : G => x * g⁻¹) ⁻¹' D
    have hD' : IsFundamentalDomain Γ D' μ :=
      hD.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
        bijective_id (fun γ x => by
          change ((γ : G) * x) * g⁻¹ = (γ : G) * (x * g⁻¹)
          exact mul_assoc _ _ _)
    rw [Measure.map_apply (measurable_right Γ g) hU,
      quotientMeasure_apply μ Γ hD ((measurable_right Γ g) hU),
      quotientMeasure_apply μ Γ hD' hU]
    have he : projection Γ ⁻¹' (right Γ g ⁻¹' U) ∩ D =
        (fun x : G => x * g) ⁻¹' (projection Γ ⁻¹' U ∩ D') := by
      ext x
      simp only [mem_inter_iff, mem_preimage, D', right_projection, mul_inv_cancel_right]
    rw [he, measure_preimage_mul_right]

def probabilityMeasure : Measure (FrameQuotient Γ) :=
  (covolume Γ G μ)⁻¹ • quotientMeasure μ Γ

omit [IsMulRightInvariant μ] in
theorem isProbabilityMeasure_probabilityMeasure
    (hfin : covolume Γ G μ ≠ ⊤) (hpos : covolume Γ G μ ≠ 0) :
    IsProbabilityMeasure (probabilityMeasure μ Γ) where
  measure_univ := by
    rw [probabilityMeasure, Measure.smul_apply, quotientMeasure_univ]
    exact ENNReal.inv_mul_cancel hpos hfin

theorem probabilityMeasure_right (g : G) :
    MeasurePreserving (right Γ g) (probabilityMeasure μ Γ) (probabilityMeasure μ Γ) where
  measurable := measurable_right Γ g
  map_eq := by
    rw [probabilityMeasure, Measure.map_smul _ (measurable_right Γ g).aemeasurable,
      (quotientMeasure_right μ Γ g).map_eq]

omit [IsMulRightInvariant μ] in
theorem probabilityMeasure_null_iff (hfin : covolume Γ G μ ≠ ⊤)
    {U : Set (FrameQuotient Γ)} (hU : MeasurableSet U) :
    probabilityMeasure μ Γ U = 0 ↔ μ (projection Γ ⁻¹' U) = 0 := by
  rw [probabilityMeasure, Measure.smul_apply]
  change (covolume Γ G μ)⁻¹ * quotientMeasure μ Γ U = 0 ↔ _
  rw [mul_eq_zero, ENNReal.inv_eq_zero, or_iff_right hfin, quotientMeasure_null_iff μ Γ hU]

section PO

variable {n : ℕ}

theorem exists_invariant_probability (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) [HasFundamentalDomain Γ (PO n 1)]
    (hcov : covolume Γ (PO n 1) ≠ ⊤) :
    ∃ ν : Measure (FrameQuotient Γ), IsProbabilityMeasure ν ∧
      (∀ g : PO n 1, MeasurePreserving (right Γ g) ν ν) ∧
      (∀ U : Set (FrameQuotient Γ), MeasurableSet U →
        (ν U = 0 ↔ volume (projection Γ ⁻¹' U) = 0)) := by
  let : Countable Γ := DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.countable_of_isDiscrete Γ disc
  let : IsMulRightInvariant (volume : Measure (PO n 1)) :=
    LatticeMeasure.volume_isMulRightInvariant Γ disc hcov
  exact ⟨probabilityMeasure volume Γ,
    isProbabilityMeasure_probabilityMeasure volume Γ hcov (DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices.covolume_ne_zero Γ disc),
    probabilityMeasure_right volume Γ, fun _ hU => probabilityMeasure_null_iff volume Γ hcov hU⟩

end PO

end DifferentialGeometry.HomogeneousSpaceMeasure
