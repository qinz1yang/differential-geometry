import DifferentialGeometry.Topology.ProjectiveSpace.Projectivization
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.IsLocalHomeomorph

set_option autoImplicit false
noncomputable section
open Bundle Set Topology

namespace DifferentialGeometry

section

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace Real A]

def realProjectiveTautologicalLine (p : RealProjectiveSpace A) : Submodule Real A :=
  (realProjectiveSpaceToProjectivization p).submodule

@[simp] theorem realProjectiveTautologicalLine_quotientMap
    (y : Metric.sphere (0 : A) 1) :
    realProjectiveTautologicalLine (realProjectiveSpaceQuotientMap y) = Real ∙ (y : A) := rfl

theorem realProjectiveTautologicalLine_finrank (p : RealProjectiveSpace A) :
    Module.finrank Real (realProjectiveTautologicalLine p) = 1 :=
  Projectivization.finrank_submodule _

abbrev RealProjectiveTautologicalSpace (A : Type*) [NormedAddCommGroup A] [NormedSpace Real A] :=
  {z : RealProjectiveSpace A × A // z.2 ∈ realProjectiveTautologicalLine z.1}

def realProjectiveTautologicalQuotientMap (x : Metric.sphere (0 : A) 1 × Real) :
    RealProjectiveTautologicalSpace A :=
  ⟨(realProjectiveSpaceQuotientMap x.1, x.2 • (x.1 : A)),
    Submodule.mem_span_singleton.mpr ⟨x.2, rfl⟩⟩

theorem realProjectiveTautologicalQuotientMap_continuous :
    Continuous (realProjectiveTautologicalQuotientMap (A := A)) := by
  apply Continuous.subtype_mk
  exact (realProjectiveSpaceQuotientMap_isOpenQuotientMap.continuous.comp continuous_fst).prodMk
    (continuous_snd.smul (continuous_subtype_val.comp continuous_fst))

theorem realProjectiveTautologicalQuotientMap_surjective :
    Function.Surjective (realProjectiveTautologicalQuotientMap (A := A)) := by
  rintro ⟨⟨p, v⟩, hv⟩
  induction p using Quotient.inductionOn with
  | _ y =>
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv
    exact ⟨(y, s), rfl⟩

theorem realProjectiveTautologicalQuotientMap_eq_iff
    {x y : Metric.sphere (0 : A) 1 × Real} :
    realProjectiveTautologicalQuotientMap x = realProjectiveTautologicalQuotientMap y ↔
      x = y ∨ x = (-y.1, -y.2) := by
  constructor
  · intro h
    have hp : realProjectiveSpaceQuotientMap x.1 = realProjectiveSpaceQuotientMap y.1 :=
      congrArg (fun z => z.1.1) h
    have hv : x.2 • (x.1 : A) = y.2 • (y.1 : A) := congrArg (fun z => z.1.2) h
    rcases realProjectiveSpaceQuotientMap_eq_iff.mp hp with hsphere | hneg
    · left
      apply Prod.ext hsphere
      rw [hsphere] at hv
      exact smul_left_injective Real (ne_zero_of_mem_unit_sphere y.1) hv
    · right
      apply Prod.ext (Subtype.ext hneg)
      rw [hneg, smul_neg, ← neg_smul] at hv
      have hs := smul_left_injective Real (ne_zero_of_mem_unit_sphere y.1) hv
      linarith
  · rintro (rfl | rfl)
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · exact realProjectiveSpaceQuotientMap_eq_iff.mpr (Or.inr rfl)
      · change (-y.2) • (-(y.1 : A)) = y.2 • (y.1 : A)
        simp

abbrev RealProjectiveTautologicalFiber (p : RealProjectiveSpace A) : Type _ :=
  realProjectiveTautologicalLine p

private def tautologicalTotalEmbedding :
    TotalSpace Real (RealProjectiveTautologicalFiber (A := A)) → RealProjectiveSpace A × A :=
  fun z => (z.1, z.2.1)

instance realProjectiveTautologicalTotalSpaceTopology :
    TopologicalSpace (TotalSpace Real (RealProjectiveTautologicalFiber (A := A))) :=
  TopologicalSpace.induced tautologicalTotalEmbedding inferInstance

private theorem tautologicalTotalEmbedding_isInducing :
    IsInducing (tautologicalTotalEmbedding (A := A)) := IsInducing.induced _

private theorem tautologicalTotalEmbedding_continuous :
    Continuous (tautologicalTotalEmbedding (A := A)) :=
  tautologicalTotalEmbedding_isInducing.continuous

private theorem tautologicalTotal_proj_continuous :
    Continuous (fun z : TotalSpace Real (RealProjectiveTautologicalFiber (A := A)) => z.1) :=
  continuous_fst.comp tautologicalTotalEmbedding_continuous

private theorem tautologicalTotal_vector_continuous :
    Continuous (fun z : TotalSpace Real (RealProjectiveTautologicalFiber (A := A)) => (z.2 : A)) :=
  continuous_snd.comp tautologicalTotalEmbedding_continuous

end

section

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace Real A]

theorem realProjectiveTautologicalLine_inner_smul
    (y : Metric.sphere (0 : A) 1) (v : A)
    (hv : v ∈ realProjectiveTautologicalLine (realProjectiveSpaceQuotientMap y)) :
    (inner Real (y : A) v) • (y : A) = v := by
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have hnorm : inner Real (y : A) (y : A) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere y]
    norm_num
  rw [inner_smul_right, hnorm, mul_one]

private def tautologicalSectionTrivializationInv
    (U : Set (RealProjectiveSpace A)) (s : RealProjectiveSpace A → Metric.sphere (0 : A) 1)
    (hq : ∀ p ∈ U, realProjectiveSpaceQuotientMap (s p) = p)
    (z : RealProjectiveSpace A × Real) : TotalSpace Real (RealProjectiveTautologicalFiber (A := A)) := by
  classical
  exact ⟨z.1, if h : z.1 ∈ U then ⟨z.2 • (s z.1 : A), by
    have hm : z.2 • (s z.1 : A) ∈
        realProjectiveTautologicalLine (realProjectiveSpaceQuotientMap (s z.1)) :=
      Submodule.mem_span_singleton.mpr ⟨z.2, rfl⟩
    exact (congrArg realProjectiveTautologicalLine (hq z.1 h)) ▸ hm⟩ else 0⟩

private theorem tautologicalSectionTrivializationInv_apply
    (U : Set (RealProjectiveSpace A)) (s : RealProjectiveSpace A → Metric.sphere (0 : A) 1)
    (hq : ∀ p ∈ U, realProjectiveSpaceQuotientMap (s p) = p)
    (z : RealProjectiveSpace A × Real) (hz : z.1 ∈ U) :
    tautologicalTotalEmbedding (tautologicalSectionTrivializationInv U s hq z) =
      (z.1, z.2 • (s z.1 : A)) := by
  simp only [tautologicalTotalEmbedding, tautologicalSectionTrivializationInv, dif_pos hz]

def realProjectiveTautologicalTrivialization
    (U : Set (RealProjectiveSpace A)) (hU : IsOpen U)
    (s : RealProjectiveSpace A → Metric.sphere (0 : A) 1) (hs : ContinuousOn s U)
    (hq : ∀ p ∈ U, realProjectiveSpaceQuotientMap (s p) = p) :
    Trivialization Real (π Real (RealProjectiveTautologicalFiber (A := A))) where
  toFun z := (z.1, inner Real (s z.1 : A) (z.2 : A))
  invFun := tautologicalSectionTrivializationInv U s hq
  source := (fun z => z.1) ⁻¹' U
  target := U ×ˢ univ
  map_source' _ h := ⟨h, mem_univ _⟩
  map_target' _ h := h.1
  left_inv' z hz := by
    classical
    change z.1 ∈ U at hz
    apply TotalSpace.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      change (if h : z.1 ∈ U then _ else (0 : RealProjectiveTautologicalFiber z.1)).1 = (z.2 : A)
      rw [dif_pos hz]
      exact realProjectiveTautologicalLine_inner_smul (s z.1) z.2 (by rw [hq z.1 hz]; exact z.2.property)
  right_inv' z hz := by
    classical
    apply Prod.ext
    · rfl
    · have hnorm : inner Real (s z.1 : A) (s z.1 : A) = 1 := by
        rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere (s z.1)]
        norm_num
      have hv := congrArg Prod.snd (tautologicalSectionTrivializationInv_apply U s hq z hz.1)
      change (tautologicalSectionTrivializationInv U s hq z).2.1 = z.2 • (s z.1 : A) at hv
      change inner Real (s z.1 : A) (tautologicalSectionTrivializationInv U s hq z).2.1 = z.2
      rw [hv, inner_smul_right, hnorm, mul_one]
  open_source := hU.preimage tautologicalTotal_proj_continuous
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := by
    apply tautologicalTotal_proj_continuous.continuousOn.prodMk
    exact (continuous_subtype_val.comp_continuousOn
      (hs.comp tautologicalTotal_proj_continuous.continuousOn (fun _ h => h))).inner
        tautologicalTotal_vector_continuous.continuousOn
  continuousOn_invFun := by
    apply tautologicalTotalEmbedding_isInducing.continuousOn_iff.mpr
    have hsec : ContinuousOn (fun z : RealProjectiveSpace A × Real => (s z.1 : A)) (U ×ˢ univ) :=
      continuous_subtype_val.comp_continuousOn
        (hs.comp continuous_fst.continuousOn (fun _ h => h.1))
    exact (continuous_fst.continuousOn.prodMk
      (continuous_snd.continuousOn.smul hsec)).congr
        (fun z hz => tautologicalSectionTrivializationInv_apply U s hq z hz.1)
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance realProjectiveTautologicalTrivialization_isLinear
    (U : Set (RealProjectiveSpace A)) (hU : IsOpen U)
    (s : RealProjectiveSpace A → Metric.sphere (0 : A) 1) (hs : ContinuousOn s U)
    (hq : ∀ p ∈ U, realProjectiveSpaceQuotientMap (s p) = p) :
    (realProjectiveTautologicalTrivialization U hU s hs hq).IsLinear Real where
  linear p hp :=
    { map_add x y := by
        change inner Real (s p : A) ((x : A) + (y : A)) = _
        exact inner_add_right _ _ _
      map_smul a x := by
        change inner Real (s p : A) (a • (x : A)) = a * inner Real (s p : A) (x : A)
        exact inner_smul_right _ _ _ }

private theorem tautologicalTotal_mk_isInducing (p : RealProjectiveSpace A) :
    IsInducing (TotalSpace.mk p : RealProjectiveTautologicalFiber p →
      TotalSpace Real (RealProjectiveTautologicalFiber (A := A))) := by
  apply tautologicalTotalEmbedding_isInducing.of_comp_iff.mp
  exact (Topology.isInducing_const_prod.mpr IsInducing.subtypeVal)

private theorem projectiveQuotient_isLocalHomeomorph :
    IsLocalHomeomorph (realProjectiveSpaceQuotientMap (E := A)) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro y
  let U : Set (Metric.sphere (0 : A) 1) := {x | 0 < inner Real (y : A) (x : A)}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
  have hy : y ∈ U := by
    change 0 < inner Real (y : A) (y : A)
    exact real_inner_self_pos.mpr (ne_zero_of_mem_unit_sphere y)
  refine ⟨U, hU.mem_nhds hy, ?_⟩
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨realProjectiveSpaceQuotientMap_isOpenQuotientMap.continuous.comp continuous_subtype_val,
    ?_, realProjectiveSpaceQuotientMap_isOpenQuotientMap.isOpenMap.comp hU.isOpenEmbedding_subtypeVal.isOpenMap⟩
  intro x z h
  have hq : realProjectiveSpaceQuotientMap x.1 = realProjectiveSpaceQuotientMap z.1 := h
  rcases realProjectiveSpaceQuotientMap_eq_iff.mp hq with hsame | hneg
  · exact Subtype.ext hsame
  · have hx : 0 < inner Real (y : A) (x.1 : A) := x.2
    have hz : 0 < inner Real (y : A) (z.1 : A) := z.2
    rw [hneg, inner_neg_right] at hx
    linarith

private def tautologicalLocalTrivialization (y : Metric.sphere (0 : A) 1) :
    Trivialization Real (π Real (RealProjectiveTautologicalFiber (A := A))) :=
  realProjectiveTautologicalTrivialization
    (projectiveQuotient_isLocalHomeomorph.localInverseAt y).source
    (projectiveQuotient_isLocalHomeomorph.localInverseAt y).open_source
    (projectiveQuotient_isLocalHomeomorph.localInverseAt y)
    (projectiveQuotient_isLocalHomeomorph.localInverseAt y).continuousOn
    (fun _ h => projectiveQuotient_isLocalHomeomorph.apply_localInverseAt_of_mem h)

instance realProjectiveTautologicalFiberBundle :
    FiberBundle Real (RealProjectiveTautologicalFiber (A := A)) where
  totalSpaceMk_isInducing' := tautologicalTotal_mk_isInducing
  trivializationAtlas' := Set.range tautologicalLocalTrivialization
  trivializationAt' p := tautologicalLocalTrivialization (Quotient.out p)
  mem_baseSet_trivializationAt' p := by
    change p ∈ (projectiveQuotient_isLocalHomeomorph.localInverseAt (Quotient.out p)).source
    have h := projectiveQuotient_isLocalHomeomorph.apply_self_mem_localInverseAt_source
      (x := Quotient.out p)
    change realProjectiveSpaceQuotientMap (Quotient.out p) ∈ _ at h
    simpa only [realProjectiveSpaceQuotientMap, Quotient.out_eq] using h
  trivialization_mem_atlas' p := ⟨_, rfl⟩

private instance tautologicalLocalTrivialization_isLinear (y : Metric.sphere (0 : A) 1) :
    (tautologicalLocalTrivialization y).IsLinear Real :=
  realProjectiveTautologicalTrivialization_isLinear _ _ _ _ _

private theorem tautologicalLocalTrivialization_coordChange
    (x y : Metric.sphere (0 : A) 1)
    (p : RealProjectiveSpace A)
    (hp : p ∈ (tautologicalLocalTrivialization x).baseSet ∩
      (tautologicalLocalTrivialization y).baseSet) :
    (tautologicalLocalTrivialization x).coordChangeL Real (tautologicalLocalTrivialization y) p =
      (inner Real
        (projectiveQuotient_isLocalHomeomorph.localInverseAt y p : A)
        (projectiveQuotient_isLocalHomeomorph.localInverseAt x p : A)) •
          ContinuousLinearMap.id Real Real := by
  apply ContinuousLinearMap.ext
  intro r
  change (tautologicalLocalTrivialization x).coordChangeL Real
    (tautologicalLocalTrivialization y) p r = _
  rw [Trivialization.coordChangeL_apply' _ _ hp]
  have hv := congrArg Prod.snd (tautologicalSectionTrivializationInv_apply
    (projectiveQuotient_isLocalHomeomorph.localInverseAt x).source
    (projectiveQuotient_isLocalHomeomorph.localInverseAt x)
    (fun _ h => projectiveQuotient_isLocalHomeomorph.apply_localInverseAt_of_mem h) (p, r) hp.1)
  change (tautologicalSectionTrivializationInv _ _ _ (p, r)).2.1 =
    r • (projectiveQuotient_isLocalHomeomorph.localInverseAt x p : A) at hv
  change inner Real (projectiveQuotient_isLocalHomeomorph.localInverseAt y p : A)
    (tautologicalSectionTrivializationInv
      (projectiveQuotient_isLocalHomeomorph.localInverseAt x).source
      (projectiveQuotient_isLocalHomeomorph.localInverseAt x)
      (fun _ h => projectiveQuotient_isLocalHomeomorph.apply_localInverseAt_of_mem h) (p, r)).2.1 = _
  rw [hv, inner_smul_right]
  change r * inner Real _ _ = inner Real _ _ * r
  exact mul_comm _ _

instance realProjectiveTautologicalVectorBundle :
    VectorBundle Real Real (RealProjectiveTautologicalFiber (A := A)) where
  trivialization_linear' := by
    rintro _ ⟨y, rfl⟩
    exact realProjectiveTautologicalTrivialization_isLinear _ _ _ _ _
  continuousOn_coordChange' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    have hx : ContinuousOn (fun p => (projectiveQuotient_isLocalHomeomorph.localInverseAt x p : A))
        ((tautologicalLocalTrivialization x).baseSet ∩ (tautologicalLocalTrivialization y).baseSet) :=
      continuous_subtype_val.comp_continuousOn
        ((projectiveQuotient_isLocalHomeomorph.localInverseAt x).continuousOn.mono inter_subset_left)
    have hy : ContinuousOn (fun p => (projectiveQuotient_isLocalHomeomorph.localInverseAt y p : A))
        ((tautologicalLocalTrivialization x).baseSet ∩ (tautologicalLocalTrivialization y).baseSet) :=
      continuous_subtype_val.comp_continuousOn
        ((projectiveQuotient_isLocalHomeomorph.localInverseAt y).continuousOn.mono inter_subset_right)
    have hi : ContinuousOn (fun p => inner Real
        (projectiveQuotient_isLocalHomeomorph.localInverseAt y p : A)
        (projectiveQuotient_isLocalHomeomorph.localInverseAt x p : A))
        ((tautologicalLocalTrivialization x).baseSet ∩ (tautologicalLocalTrivialization y).baseSet) :=
      hy.inner hx
    exact (hi.smul continuousOn_const).congr
      (fun p hp => tautologicalLocalTrivialization_coordChange x y p hp)

end

section

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace Real A]

noncomputable def realProjectiveTautologicalTotalSpaceHomeomorph :
    TotalSpace Real (RealProjectiveTautologicalFiber (A := A)) ≃ₜ RealProjectiveTautologicalSpace A where
  toFun z := ⟨(z.1, z.2.1), z.2.property⟩
  invFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := tautologicalTotalEmbedding_continuous.subtype_mk _
  continuous_invFun := tautologicalTotalEmbedding_isInducing.continuous_iff.mpr continuous_subtype_val

@[simp] theorem realProjectiveTautologicalTotalSpaceHomeomorph_apply
    (z : TotalSpace Real (RealProjectiveTautologicalFiber (A := A))) :
    (realProjectiveTautologicalTotalSpaceHomeomorph z).1 = (z.1, z.2.1) := rfl

@[simp] theorem realProjectiveTautologicalTotalSpaceHomeomorph_symm_apply
    (z : RealProjectiveTautologicalSpace A) :
    (realProjectiveTautologicalTotalSpaceHomeomorph.symm z).1 = z.1.1 := rfl

end

end DifferentialGeometry
