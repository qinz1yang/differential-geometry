/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Ergodic.HomogeneousSpace
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.Generation

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology Pointwise symmDiff

namespace DifferentialGeometry.GeodesicErgodicity

open GeodesicFlow LorentzGenerators TransverseGeneration DifferentialGeometry.HomogeneousSpaceDynamics

variable {m : ℕ}

local instance : MulAction (IsometryGroup m) (Hyperbolic.HUpper (m + 1)) :=
  HyperbolicAction.poMulAction (by omega)
local instance : MulAction (IsometryGroup m) (HyperbolicBoundary.BoundaryH (m + 1)) :=
  HyperbolicBoundary.poBoundaryMulAction (by omega)

theorem null_or_conull_of_flow_invariant (hm : 1 ≤ m)
    (Γ : Subgroup (IsometryGroup m)) (disc : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (IsometryGroup m)]
    (hcov : covolume Γ (IsometryGroup m) ≠ ⊤)
    (ν : Measure (GeodesicQuotient Γ))
    (hν : ∀ U : Set (GeodesicQuotient Γ), MeasurableSet U →
      (ν U = 0 ↔ volume ((fun g : IsometryGroup m =>
        GeodesicFlow.projection Γ (g • (standardTangent : Tangent m))) ⁻¹' U) = 0))
    {U : Set (GeodesicQuotient Γ)} (hU : MeasurableSet U)
    (hflow : ∀ t : ℝ, quotientFlow Γ t ⁻¹' U =ᵐ[ν] U) :
    ν U = 0 ∨ ν Uᶜ = 0 := by
  obtain ⟨μ, hμ, hr, hn⟩ := DifferentialGeometry.HomogeneousSpaceMeasure.exists_invariant_probability Γ disc hcov
  let := hμ
  let := inverseRightAction Γ
  let := smulInvariant_of_right Γ μ hr
  let : IsMulRightInvariant (volume : Measure (IsometryGroup m)) :=
    LatticeMeasure.volume_isMulRightInvariant Γ disc hcov
  let V : Set (DifferentialGeometry.HomogeneousSpaceMeasure.FrameQuotient Γ) := frameProjection Γ ⁻¹' U
  have hV : MeasurableSet V := (measurable_frameProjection Γ) hU
  have htransfer {W : Set (GeodesicQuotient Γ)} (hW : MeasurableSet W) :
      μ (frameProjection Γ ⁻¹' W) = 0 ↔ ν W = 0 := by
    rw [hn _ ((measurable_frameProjection Γ) hW), hν W hW]
    rfl
  have hlift {W Z : Set (GeodesicQuotient Γ)} (hW : MeasurableSet W)
      (hZ : MeasurableSet Z) (h : W =ᵐ[ν] Z) :
      frameProjection Γ ⁻¹' W =ᵐ[μ] frameProjection Γ ⁻¹' Z := by
    apply measure_symmDiff_eq_zero_iff.mp
    rw [← preimage_symmDiff]
    exact (htransfer (hW.symmDiff hZ)).mpr (measure_symmDiff_eq_zero_iff.mpr h)
  have hD (t : ℝ) : DifferentialGeometry.HomogeneousSpaceMeasure.right Γ (GeodesicFlow.diagonal t) ⁻¹' V =ᵐ[μ] V := by
    have h := hlift ((measurable_quotientFlow Γ t) hU) hU (hflow t)
    have he : DifferentialGeometry.HomogeneousSpaceMeasure.right Γ (GeodesicFlow.diagonal t) ⁻¹' V =
        frameProjection Γ ⁻¹' (quotientFlow Γ t ⁻¹' U) := by
      ext q
      change (frameProjection Γ (DifferentialGeometry.HomogeneousSpaceMeasure.right Γ (GeodesicFlow.diagonal t) q) ∈ U) ↔
        (quotientFlow Γ t (frameProjection Γ q) ∈ U)
      rw [frameProjection_right_diagonal]
    rw [he]
    exact h
  let H := MulAction.aestabilizer (IsometryGroup m) μ V
  have hH (g : IsometryGroup m) :
      g ∈ H ↔ DifferentialGeometry.HomogeneousSpaceMeasure.right Γ g ⁻¹' V =ᵐ[μ] V := by
    rw [MulAction.mem_aestabilizer, smul_set_eq_preimage_right]
  have htop : H = ⊤ := by
    apply eq_top_of_transverse_and_horospherical hm H
    · intro b
      apply (hH _).mpr
      exact ae_right_of_tendsto_conjugate (by omega) Γ disc μ hr hV
        (Eventually.of_forall (fun k : ℕ => hD (-(k : ℝ))))
        (tendsto_conjugate_translation hm b)
    · intro b
      apply (hH _).mpr
      exact ae_right_of_tendsto_conjugate (by omega) Γ disc μ hr hV
        (Eventually.of_forall (fun k : ℕ => hD (k : ℝ)))
        (tendsto_conjugate_oppositeTranslation hm b)
    · intro t
      exact (hH _).mpr (hD t)
    · intro g hg
      apply (hH _).mpr
      apply Eventually.of_forall
      intro q
      change (frameProjection Γ (DifferentialGeometry.HomogeneousSpaceMeasure.right Γ g q) ∈ U) =
        (frameProjection Γ q ∈ U)
      rw [frameProjection_right_transverse Γ hg]
  have hfull (g : IsometryGroup m) :
      DifferentialGeometry.HomogeneousSpaceMeasure.right Γ g ⁻¹' V =ᵐ[μ] V :=
    (hH g).mp (htop ▸ Subgroup.mem_top g)
  rcases null_or_conull_of_all_right Γ volume μ hn hV hfull with hzero | hone
  · exact Or.inl ((htransfer hU).mp hzero)
  · right
    apply (htransfer hU.compl).mp
    simpa only [preimage_compl] using hone

theorem exists_ergodic_probability (hm : 1 ≤ m)
    (Γ : Subgroup (IsometryGroup m)) (disc : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (IsometryGroup m)]
    (hcov : covolume Γ (IsometryGroup m) ≠ ⊤) :
    ∃ ν : Measure (GeodesicQuotient Γ), IsProbabilityMeasure ν ∧
      (∀ t : ℝ, MeasurePreserving (quotientFlow Γ t) ν ν) ∧
      (∀ U : Set (GeodesicQuotient Γ), MeasurableSet U →
        (∀ t : ℝ, quotientFlow Γ t ⁻¹' U =ᵐ[ν] U) → ν U = 0 ∨ ν Uᶜ = 0) ∧
      (∀ U : Set (GeodesicQuotient Γ), MeasurableSet U →
        (ν U = 0 ↔ volume ((fun g : IsometryGroup m =>
          GeodesicFlow.projection Γ (g • (standardTangent : Tangent m))) ⁻¹' U) = 0)) := by
  obtain ⟨ν, hν, hf, hn⟩ := GeodesicFlow.exists_invariant_probability Γ disc hcov
  exact ⟨ν, hν, hf, fun U hU hflow =>
    null_or_conull_of_flow_invariant hm Γ disc hcov ν hn hU hflow, hn⟩

theorem exists_probability_ergodic_realAction (hm : 1 ≤ m)
    (Γ : Subgroup (IsometryGroup m)) (disc : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (IsometryGroup m)]
    (hcov : covolume Γ (IsometryGroup m) ≠ ⊤) :
    ∃ ν : Measure (GeodesicQuotient Γ), IsProbabilityMeasure ν ∧
      (letI := realAction Γ
       ErgodicSMul (Multiplicative ℝ) (GeodesicQuotient Γ) ν) := by
  obtain ⟨ν, hν, hf, he, _⟩ := exists_ergodic_probability hm Γ disc hcov
  refine ⟨ν, hν, ?_⟩
  let := realAction Γ
  refine
    { measure_preimage_smul := fun t _ hU => (hf t.toAdd).measure_preimage hU.nullMeasurableSet
      aeconst_of_forall_preimage_smul_ae_eq := fun {U} hU hInv => ?_ }
  have h := he U hU (fun t => hInv (Multiplicative.ofAdd t))
  simpa only [eventuallyEmptyOrUniv_iff', ae_eq_empty, ae_eq_univ] using h

end DifferentialGeometry.GeodesicErgodicity
