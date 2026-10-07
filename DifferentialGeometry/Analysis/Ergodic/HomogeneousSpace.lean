/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Ergodic.Mautner
import DifferentialGeometry.Analysis.Integration.Measure.GroupQuotient.InvariantMeasure
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.Center
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology Pointwise symmDiff

namespace DifferentialGeometry.HomogeneousSpaceDynamics

open DifferentialGeometry.HomogeneousSpaceMeasure

variable {G : Type*} [Group G]

@[instance_reducible]
def inverseRightAction (Γ : Subgroup G) : MulAction G (FrameQuotient Γ) where
  smul g q := right Γ g⁻¹ q
  one_smul q := by
    change right Γ (1 : G)⁻¹ q = q
    rw [inv_one, right_one]
  mul_smul g h q := by
    change right Γ (g * h)⁻¹ q = right Γ g⁻¹ (right Γ h⁻¹ q)
    rw [mul_inv_rev, right_mul]

attribute [local instance] inverseRightAction

theorem smul_set_eq_preimage_right (Γ : Subgroup G) (g : G) (U : Set (FrameQuotient Γ)) :
    g • U = right Γ g ⁻¹' U := by
  rw [← preimage_smul_inv]
  change right Γ (g⁻¹)⁻¹ ⁻¹' U = right Γ g ⁻¹' U
  rw [inv_inv]

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem continuous_projection (Γ : Subgroup G) : Continuous (projection Γ) :=
  continuous_quotient_mk'

theorem isOpenQuotientMap_projection (Γ : Subgroup G) : IsOpenQuotientMap (projection Γ) :=
  MulAction.isOpenQuotientMap_quotientMk

instance continuous_inverseRightAction (Γ : Subgroup G) :
    ContinuousSMul G (FrameQuotient Γ) := by
  constructor
  have hp := (IsOpenQuotientMap.id (X := G)).prodMap (isOpenQuotientMap_projection Γ)
  rw [← hp.continuous_comp_iff]
  change Continuous (fun p : G × G => projection Γ (p.2 * p.1⁻¹))
  exact (continuous_projection Γ).comp (continuous_snd.mul continuous_fst.inv)

theorem quotient_secondCountable (Γ : Subgroup G) [SecondCountableTopology G] :
    SecondCountableTopology (FrameQuotient Γ) :=
  ContinuousConstSMul.secondCountableTopology

theorem quotient_locallyCompact (Γ : Subgroup G) [LocallyCompactSpace G] :
    LocallyCompactSpace (FrameQuotient Γ) :=
  (isOpenQuotientMap_projection Γ).locallyCompactSpace

variable [MeasurableSpace G] [BorelSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
theorem smulInvariant_of_right (Γ : Subgroup G) (ν : Measure (FrameQuotient Γ))
    (hr : ∀ g : G, MeasurePreserving (right Γ g) ν ν) :
    SMulInvariantMeasure G (FrameQuotient Γ) ν where
  measure_preimage_smul g _ hU := (hr g⁻¹).measure_preimage hU.nullMeasurableSet

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
theorem lift_ae_eq (Γ : Subgroup G) (μ : Measure G) (ν : Measure (FrameQuotient Γ))
    (hn : ∀ U : Set (FrameQuotient Γ), MeasurableSet U →
      (ν U = 0 ↔ μ (projection Γ ⁻¹' U) = 0))
    {U V : Set (FrameQuotient Γ)} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (h : U =ᵐ[ν] V) :
    projection Γ ⁻¹' U =ᵐ[μ] projection Γ ⁻¹' V := by
  apply measure_symmDiff_eq_zero_iff.mp
  rw [← preimage_symmDiff]
  exact (hn _ (hU.symmDiff hV)).mp (measure_symmDiff_eq_zero_iff.mpr h)

theorem null_or_conull_of_all_right (Γ : Subgroup G) (μ : Measure G)
    [SecondCountableTopology G] [SFinite μ] [IsMulRightInvariant μ]
    (ν : Measure (FrameQuotient Γ))
    (hn : ∀ U : Set (FrameQuotient Γ), MeasurableSet U →
      (ν U = 0 ↔ μ (projection Γ ⁻¹' U) = 0))
    {U : Set (FrameQuotient Γ)} (hU : MeasurableSet U)
    (h : ∀ g : G, right Γ g ⁻¹' U =ᵐ[ν] U) :
    ν U = 0 ∨ ν Uᶜ = 0 := by
  have hA : MeasurableSet (projection Γ ⁻¹' U) := (measurable_projection Γ) hU
  have hconst := aeconst_of_forall_preimage_smul_ae_eq Gᵐᵒᵖ hA.nullMeasurableSet
    (fun g => lift_ae_eq Γ μ ν hn ((measurable_right Γ g.unop) hU) hU (h g.unop))
  rcases eventuallyEmptyOrUniv_iff'.mp hconst with hzero | hone
  · left
    apply (hn U hU).mpr
    exact measure_congr hzero |>.trans measure_empty
  · right
    apply (hn Uᶜ hU.compl).mpr
    rw [preimage_compl]
    exact measure_congr hone.compl |>.trans (by simp)

section PO

variable {n : ℕ} (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
variable (disc : IsDiscrete (SetLike.coe Γ))

include hn disc

theorem po_quotient_borel : BorelSpace (FrameQuotient Γ) := by
  let : T3Space (PO n 1) := DifferentialGeometry.ProjectiveOrthogonalGroup.Center.t3Space_PO hn
  let : T2Space (FrameQuotient Γ) := DifferentialGeometry.ProjectiveOrthogonalGroup.Center.t2Space_orbitQuotient hn Γ disc
  let := quotient_secondCountable Γ
  let L := unitary (MatrixSum (Fin n) (Fin 1) ℝ)
  let : PolishSpace (MatrixSum (Fin n) (Fin 1) ℝ) :=
    inferInstanceAs (PolishSpace ((Fin n ⊕ Fin 1) → (Fin n ⊕ Fin 1) → ℝ))
  let : PolishSpace L := (MatrixSum.isClosed_unitary (Fin n) (Fin 1) ℝ).polishSpace
  let : MeasurableSpace L := borel L
  let : BorelSpace L := ⟨rfl⟩
  let q : L → PO n 1 := QuotientGroup.mk' _
  have hq : Continuous q := QuotientGroup.isOpenQuotientMap_mk.continuous
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have he := hq.map_eq_borel hqs
  have hs : Function.Surjective (projection Γ) := Quotient.mk''_surjective
  have hp := ((continuous_projection Γ).comp hq).map_eq_borel (hs.comp hqs)
  constructor
  change MeasurableSpace.map (projection Γ) (borel (PO n 1)) = borel (FrameQuotient Γ)
  rw [← he, MeasurableSpace.map_comp]
  exact hp

theorem po_quotient_innerRegular (ν : Measure (FrameQuotient Γ)) [IsFiniteMeasure ν] :
    ν.InnerRegular := by
  let : T2Space (FrameQuotient Γ) := DifferentialGeometry.ProjectiveOrthogonalGroup.Center.t2Space_orbitQuotient hn Γ disc
  let := quotient_secondCountable Γ
  let := quotient_locallyCompact Γ
  let := po_quotient_borel hn Γ disc
  infer_instance

theorem ae_right_of_tendsto_conjugate (ν : Measure (FrameQuotient Γ))
    [IsFiniteMeasure ν] (hr : ∀ g : PO n 1, MeasurePreserving (right Γ g) ν ν)
    {ι : Type*} {l : Filter ι} [l.NeBot] {a : ι → PO n 1} {g : PO n 1}
    {U : Set (FrameQuotient Γ)} (hU : MeasurableSet U)
    (ha : ∀ᶠ i in l, right Γ (a i) ⁻¹' U =ᵐ[ν] U)
    (hc : Tendsto (fun i => a i * g * (a i)⁻¹) l (𝓝 1)) :
    right Γ g ⁻¹' U =ᵐ[ν] U := by
  let : T2Space (FrameQuotient Γ) := DifferentialGeometry.ProjectiveOrthogonalGroup.Center.t2Space_orbitQuotient hn Γ disc
  let := po_quotient_borel hn Γ disc
  let := po_quotient_innerRegular hn Γ disc ν
  let := smulInvariant_of_right Γ ν hr
  have he := fun b : PO n 1 => smul_set_eq_preimage_right Γ b U
  have hm : g ∈ MulAction.aestabilizer (PO n 1) ν U :=
    Mautner.mem_aestabilizer_of_tendsto_conjugate ν hU.nullMeasurableSet
      (ha.mono (fun i hi => by simpa only [MulAction.mem_aestabilizer, he] using hi)) hc
  simpa only [MulAction.mem_aestabilizer, he] using hm

end PO

end DifferentialGeometry.HomogeneousSpaceDynamics
