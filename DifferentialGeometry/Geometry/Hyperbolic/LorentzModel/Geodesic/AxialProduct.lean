import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.RadialQuotient
import DifferentialGeometry.Topology.Manifold.SubmersionFiber
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.AxisGeometry

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)

variable (m : ℕ) (Γ : Subgroup (PO (m + 1) 1))

private local instance : MulAction Γ (HUpper (m + 1)) := EquivariantMap.subAction (by omega) Γ

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
local notation "Q" => MulAction.orbitRel.Quotient Γ (HUpper (m + 1))
local notation "q" => Quotient.mk (MulAction.orbitRel Γ (HUpper (m + 1)))

variable (ξ η : BoundaryH (m + 1)) (hne : ξ ≠ η)
  (hpair : ∀ γ : Γ,
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) ξ ∈ ({ξ, η} : Set (BoundaryH (m + 1))) ∧
    (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul (γ : PO (m + 1) 1) η ∈ ({ξ, η} : Set (BoundaryH (m + 1))))

local notation "R" => quotientAxisDistance m Γ ξ η hne hpair
local notation "F" => quotientAxisRadialFlow m Γ ξ η hne hpair
local notation "S" => {z : Q // R z = Real.arsinh 1}

theorem continuous_quotientAxisDistance : Continuous R := by
  exact continuous_quot_lift _ (lipschitzWith_dist_axisFoot ξ η hne).continuous

theorem quotientAxisDistance_nonneg (z : Q) : 0 ≤ R z := by
  induction z using Quotient.inductionOn with
  | _ y => exact dist_nonneg

def axisOffCore : TopologicalSpace.Opens Q where
  carrier := (q '' axis ξ η)ᶜ
  is_open' := by
    have he : (q '' axis ξ η)ᶜ = {z : Q | R z ≠ 0} := by
      ext z
      exact not_congr (quotientAxisDistance_eq_zero_iff_mem_image_axis m Γ ξ η hne hpair z).symm
    rw [he]
    exact isOpen_ne_fun (continuous_quotientAxisDistance m Γ ξ η hne hpair) continuous_const

local notation "O" => axisOffCore m Γ ξ η hne hpair

theorem quotientAxisDistance_pos_of_mem_axisOffCore (z : O) : 0 < R z.val := by
  apply lt_of_le_of_ne (quotientAxisDistance_nonneg m Γ ξ η hne hpair z.val)
  intro hz
  exact z.property ((quotientAxisDistance_eq_zero_iff_mem_image_axis m Γ ξ η hne hpair z.val).mp hz.symm)

def axisLogSinhRadius (z : O) : ℝ := Real.log (Real.sinh (R z.val))

local notation "τ" => axisLogSinhRadius m Γ ξ η hne hpair

theorem axisLogSinhRadius_eq_zero_iff (z : O) : τ z = 0 ↔ R z.val = Real.arsinh 1 := by
  constructor
  · intro hz
    have hs := Real.eq_one_of_pos_of_log_eq_zero
      (Real.sinh_pos_iff.mpr (quotientAxisDistance_pos_of_mem_axisOffCore m Γ ξ η hne hpair z)) hz
    have h := congrArg Real.arsinh hs
    rwa [Real.arsinh_sinh] at h
  · intro hz
    simp only [axisLogSinhRadius, hz, Real.sinh_arsinh, Real.log_one]

def axisOffCoreFlow (t : ℝ) (z : O) : O :=
  ⟨F t z.val, fun hz => z.property
    ((quotientAxisRadialFlow_mem_image_axis_iff m Γ ξ η hne hpair t z.val).mp hz)⟩

local notation "Fₒ" => axisOffCoreFlow m Γ ξ η hne hpair

theorem axisOffCoreFlow_zero (z : O) : Fₒ 0 z = z :=
  Subtype.ext (quotientAxisRadialFlow_zero m Γ ξ η hne hpair z.val)

theorem axisOffCoreFlow_add (s t : ℝ) (z : O) : Fₒ s (Fₒ t z) = Fₒ (s + t) z :=
  Subtype.ext (quotientAxisRadialFlow_add m Γ ξ η hne hpair s t z.val)

theorem axisLogSinhRadius_axisOffCoreFlow (t : ℝ) (z : O) : τ (Fₒ t z) = τ z + t :=
  log_sinh_quotientAxisDistance_quotientAxisRadialFlow m Γ ξ η hne hpair t z.property

private def axisSectionToOffCore (z : S) : O :=
  ⟨z.val, by
    intro hz
    have hzero := (quotientAxisDistance_eq_zero_iff_mem_image_axis m Γ ξ η hne hpair z.val).mpr hz
    have hp : 0 < Real.arsinh (1 : ℝ) := Real.arsinh_pos_iff.mpr (by norm_num)
    rw [z.property] at hzero
    exact hp.ne' hzero⟩

def axisSectionFiberHomeomorph : S ≃ₜ {z : O // τ z = 0} where
  toFun z := ⟨axisSectionToOffCore m Γ ξ η hne hpair z,
    (axisLogSinhRadius_eq_zero_iff m Γ ξ η hne hpair _).mpr z.property⟩
  invFun z := ⟨z.val.val, (axisLogSinhRadius_eq_zero_iff m Γ ξ η hne hpair z.val).mp z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

section Smooth

variable [DiscreteTopology Γ] [IsCancelSMul Γ (HUpper (m + 1))]

private local instance : ProperlyDiscontinuousSMul Γ (HUpper (m + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (by omega) Γ
    (isDiscrete_iff_discreteTopology.mpr inferInstance)

private local instance : ContinuousConstSMul Γ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩

private local instance : ContMDiffConstSMul I ∞ Γ (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩

private theorem contMDiff_radius_offCore : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun z : O => R z.val) := by
  have hs := contMDiffOn_quotientAxisDistance m Γ ξ η hne hpair
    (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
  intro z
  have hz : R z.val ≠ 0 := (quotientAxisDistance_pos_of_mem_axisOffCore m Γ ξ η hne hpair z).ne'
  exact (hs z.val hz |>.contMDiffAt
    ((isOpen_ne_fun (continuous_quotientAxisDistance m Γ ξ η hne hpair) continuous_const).mem_nhds hz)).comp z
      contMDiff_subtype_val.contMDiffAt

theorem contMDiff_axisLogSinhRadius : ContMDiff I 𝓘(ℝ, ℝ) ∞ τ := by
  have hs := Real.contDiff_sinh.contMDiff.comp (contMDiff_radius_offCore m Γ ξ η hne hpair)
  intro z
  exact (Real.contDiffAt_log.mpr
    (Real.sinh_pos_iff.mpr (quotientAxisDistance_pos_of_mem_axisOffCore m Γ ξ η hne hpair z)).ne').contMDiffAt.comp z
      (hs z)

theorem contMDiff_axisOffCoreFlow :
    ContMDiff ((I).prod 𝓘(ℝ, ℝ)) I ∞ (fun z : O × ℝ => Fₒ z.2 z.1) := by
  apply (Manifold.contMDiff_subtypeVal_comp_iff O _).mp
  exact (contMDiff_quotientAxisRadialFlow m Γ ξ η hne hpair
    (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))).comp
      ((contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd)

private theorem contMDiff_axisOffCoreFlow_curve (z : O) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => Fₒ t z) := by
  apply (Manifold.contMDiff_subtypeVal_comp_iff O _).mp
  have hp : ContMDiff 𝓘(ℝ, ℝ) ((I).prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (z.val, t)) :=
    contMDiff_const.prodMk contMDiff_id
  exact (contMDiff_quotientAxisRadialFlow m Γ ξ η hne hpair
    (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))).comp hp

theorem surjective_mfderiv_axisLogSinhRadius (z : O) :
    Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) τ z) := by
  let c : ℝ → O := fun t => Fₒ t z
  have hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c := contMDiff_axisOffCoreFlow_curve m Γ ξ η hne hpair z
  have hc0 : c 0 = z := axisOffCoreFlow_zero m Γ ξ η hne hpair z
  have heq : τ ∘ c = fun t : ℝ => τ z + t :=
    funext fun t => axisLogSinhRadius_axisOffCoreFlow m Γ ξ η hne hpair t z
  let u : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1
  have hd := mvfderiv_comp_apply 0
    ((contMDiff_axisLogSinhRadius m Γ ξ η hne hpair).mdifferentiableAt (x := c 0) (by simp))
    (hc.mdifferentiableAt (x := 0) (by simp)) u
  have hid : mvfderiv 𝓘(ℝ, ℝ) (τ ∘ c) 0 u = 1 := by
    rw [heq, mvfderiv_eq_fderiv]
    change fderiv ℝ (fun t : ℝ => τ z + t) 0 ((NormedSpace.fromTangentSpace (0 : ℝ)) u) = 1
    rw [ContinuousLinearEquiv.apply_symm_apply, fderiv_apply_one_eq_deriv]
    exact ((hasDerivAt_id (0 : ℝ)).const_add (τ z)).deriv
  rw [hid] at hd
  have hv : ∃ v : TangentSpace I (c 0), mvfderiv I τ (c 0) v = 1 :=
    ⟨mfderiv 𝓘(ℝ, ℝ) I c 0 u, hd.symm⟩
  rw [hc0] at hv
  obtain ⟨v, hv⟩ := hv
  intro a
  refine ⟨((NormedSpace.fromTangentSpace (𝕜 := ℝ) (τ z)) a) • v, ?_⟩
  apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (τ z)).injective
  change mvfderiv I τ z
    (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (τ z)) a) • v) = _
  rw [map_smul, hv]
  simp only [smul_eq_mul, mul_one]

private theorem section_submersion (z : O) :
    _root_.Manifold.IsSubmersionAtOfComplement (Fin m → ℝ) I 𝓘(ℝ, ℝ) ∞ τ z := by
  have h := Topology.Manifold.isSubmersionAtOfComplement_of_surjective_mfderiv
    τ (contMDiff_axisLogSinhRadius m Γ ξ η hne hpair) z
    (surjective_mfderiv_axisLogSinhRadius m Γ ξ η hne hpair z)
  let L : (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) - Module.finrank ℝ ℝ) → ℝ) ≃L[ℝ]
      (Fin m → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  exact h.trans_F L

@[instance_reducible]
private def axisSectionFiberChartedSpace : ChartedSpace (Fin m → ℝ) {z : O // τ z = 0} :=
  Topology.Manifold.submersionFiberChartedSpace τ 0
    (fun z _ => section_submersion m Γ ξ η hne hpair z)

@[instance_reducible]
def axisSectionChartedSpace : ChartedSpace (Fin m → ℝ) S :=
  let _ := axisSectionFiberChartedSpace m Γ ξ η hne hpair
  Manifold.Homeomorph.pullbackChartedSpace (axisSectionFiberHomeomorph m Γ ξ η hne hpair)

local notation "J" => 𝓘(ℝ, Fin m → ℝ)
local notation "L" => {z : O // τ z = 0}

private local instance : ChartedSpace (Fin m → ℝ) L := axisSectionFiberChartedSpace m Γ ξ η hne hpair

private theorem axisSectionFiber_isManifold : IsManifold J ∞ L :=
  Topology.Manifold.submersionFiberIsManifold τ 0
    (fun z _ => section_submersion m Γ ξ η hne hpair z)

private local instance : IsManifold J ∞ L := axisSectionFiber_isManifold m Γ ξ η hne hpair

private local instance : ChartedSpace (Fin m → ℝ) S := axisSectionChartedSpace m Γ ξ η hne hpair

theorem axisSection_isManifold : IsManifold J ∞ S :=
  Manifold.Homeomorph.instIsManifoldPullback (axisSectionFiberHomeomorph m Γ ξ η hne hpair)

private local instance : IsManifold J ∞ S := axisSection_isManifold m Γ ξ η hne hpair

private def axisSectionFiberDiffeomorph : S ≃ₘ⟮J, J⟯ L :=
  Manifold.Homeomorph.pullbackDiffeomorph (axisSectionFiberHomeomorph m Γ ξ η hne hpair)

private theorem contMDiff_sectionToOffCore : ContMDiff J I ∞ (axisSectionToOffCore m Γ ξ η hne hpair) := by
  have hi := Topology.Manifold.contMDiff_submersionFiberInclusion τ 0
    (fun z _ => section_submersion m Γ ξ η hne hpair z)
  exact hi.comp (axisSectionFiberDiffeomorph m Γ ξ η hne hpair).contMDiff

theorem contMDiff_axisSection_inclusion : ContMDiff J I ∞ (Subtype.val : S → Q) :=
  contMDiff_subtype_val.comp (contMDiff_sectionToOffCore m Γ ξ η hne hpair)

omit [DiscreteTopology Γ] [IsCancelSMul Γ (HUpper (m + 1))] in
private theorem retraction_height (z : O) : τ (Fₒ (-τ z) z) = 0 := by
  rw [axisLogSinhRadius_axisOffCoreFlow, add_neg_cancel]

private def axisFiberRetraction (z : O) : L :=
  ⟨Fₒ (-τ z) z, retraction_height m Γ ξ η hne hpair z⟩

private theorem contMDiff_axisFiberRetraction : ContMDiff I J ∞ (axisFiberRetraction m Γ ξ η hne hpair) := by
  apply (Topology.Manifold.contMDiff_submersionFiber_iff τ 0
    (fun z _ => section_submersion m Γ ξ η hne hpair z) _).mpr
  apply (Manifold.contMDiff_subtypeVal_comp_iff O _).mp
  have hp : ContMDiff I ((I).prod 𝓘(ℝ, ℝ)) ∞ (fun z : O => (z.val, -τ z)) :=
    contMDiff_subtype_val.prodMk (contMDiff_axisLogSinhRadius m Γ ξ η hne hpair).neg
  exact (contMDiff_quotientAxisRadialFlow m Γ ξ η hne hpair
    (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))).comp hp

private theorem contMDiff_sectionFlow :
    ContMDiff ((J).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : S × ℝ => Fₒ z.2 (axisSectionToOffCore m Γ ξ η hne hpair z.1)) := by
  apply (Manifold.contMDiff_subtypeVal_comp_iff O _).mp
  have hp : ContMDiff ((J).prod 𝓘(ℝ, ℝ)) ((I).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : S × ℝ => (z.1.val, z.2)) :=
    ((contMDiff_axisSection_inclusion m Γ ξ η hne hpair).comp contMDiff_fst).prodMk contMDiff_snd
  exact (contMDiff_quotientAxisRadialFlow m Γ ξ η hne hpair
    (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))).comp hp

def axisProductDiffeomorph : O ≃ₘ⟮I, (J).prod 𝓘(ℝ, ℝ)⟯ S × ℝ where
  toFun z := ((axisSectionFiberDiffeomorph m Γ ξ η hne hpair).symm
    (axisFiberRetraction m Γ ξ η hne hpair z), τ z)
  invFun z := Fₒ z.2 (axisSectionToOffCore m Γ ξ η hne hpair z.1)
  left_inv z := by
    change Fₒ (τ z) (Fₒ (-τ z) z) = z
    rw [axisOffCoreFlow_add, add_neg_cancel, axisOffCoreFlow_zero]
  right_inv z := by
    obtain ⟨z, t⟩ := z
    have hz : τ (axisSectionToOffCore m Γ ξ η hne hpair z) = 0 :=
      (axisLogSinhRadius_eq_zero_iff m Γ ξ η hne hpair _).mpr z.property
    apply Prod.ext
    · apply Subtype.ext
      change (Fₒ (-τ (Fₒ t (axisSectionToOffCore m Γ ξ η hne hpair z)))
        (Fₒ t (axisSectionToOffCore m Γ ξ η hne hpair z))).val = z.val
      rw [axisLogSinhRadius_axisOffCoreFlow, hz, zero_add,
        axisOffCoreFlow_add, neg_add_cancel, axisOffCoreFlow_zero]
      rfl
    · change τ (Fₒ t (axisSectionToOffCore m Γ ξ η hne hpair z)) = t
      rw [axisLogSinhRadius_axisOffCoreFlow, hz, zero_add]
  contMDiff_toFun :=
    ((axisSectionFiberDiffeomorph m Γ ξ η hne hpair).symm.contMDiff.comp
      (contMDiff_axisFiberRetraction m Γ ξ η hne hpair)).prodMk
        (contMDiff_axisLogSinhRadius m Γ ξ η hne hpair)
  contMDiff_invFun := contMDiff_sectionFlow m Γ ξ η hne hpair

@[simp] theorem axisProductDiffeomorph_fst_val (z : O) :
    ((axisProductDiffeomorph m Γ ξ η hne hpair z).1 : Q) = F (-τ z) z.val := rfl

@[simp] theorem axisProductDiffeomorph_snd (z : O) :
    (axisProductDiffeomorph m Γ ξ η hne hpair z).2 = τ z := rfl

@[simp] theorem axisProductDiffeomorph_symm_val (z : S × ℝ) :
    ((axisProductDiffeomorph m Γ ξ η hne hpair).symm z : Q) = F z.2 z.1.val := rfl

end Smooth

end DifferentialGeometry.AxisGeometry
