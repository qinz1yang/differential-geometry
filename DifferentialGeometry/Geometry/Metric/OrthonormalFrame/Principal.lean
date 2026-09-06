import DifferentialGeometry.Bundle.Equiv.Continuity
import DifferentialGeometry.Geometry.Metric.OrthonormalFrame.LocalTrivialization
import DifferentialGeometry.Geometry.Metric.OrthonormalFrame.Topology
import DifferentialGeometry.Bundle.Principal.Topology

noncomputable section

open Set Bundle
open scoped Topology

namespace Bundle.Pretrivialization

variable {k B F : Type*} [NontriviallyNormedField k] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace k F]
  {V : B → Type*} [∀ x, SeminormedAddCommGroup (V x)] [∀ x, Module k (V x)]

def orthonormalFrame (q : ∀ x, V x ≃ₗᵢ[k] F) (U : Set B) (hU : IsOpen U) :
    Pretrivialization (F ≃ₗᵢ[k] F) (π (F ≃ₗᵢ[k] F) (fun x => V x ≃ₗᵢ[k] F)) where
  toFun z := (z.1, (q z.1).symm.trans z.2)
  invFun z := ⟨z.1, (q z.1).trans z.2⟩
  source := TotalSpace.proj ⁻¹' U
  target := U ×ˢ univ
  map_source' := fun _ h => ⟨h, mem_univ _⟩
  map_target' := fun _ h => h.1
  left_inv' := fun ⟨x, p⟩ _ => by
    apply TotalSpace.mk_inj.mpr
    ext v
    exact congrArg p ((q x).symm_apply_apply v)
  right_inv' := fun ⟨x, g⟩ _ => by
    congr 1
    ext v
    exact congrArg g ((q x).apply_symm_apply v)
  open_target := hU.prod isOpen_univ
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem orthonormalFrame_apply (q : ∀ x, V x ≃ₗᵢ[k] F) (U : Set B) (hU : IsOpen U)
    (z : TotalSpace (F ≃ₗᵢ[k] F) (fun x => V x ≃ₗᵢ[k] F)) :
    orthonormalFrame q U hU z = (z.1, (q z.1).symm.trans z.2) := rfl

@[simp]
theorem orthonormalFrame_symm_apply (q : ∀ x, V x ≃ₗᵢ[k] F) (U : Set B) (hU : IsOpen U)
    (z : B × (F ≃ₗᵢ[k] F)) :
    (orthonormalFrame q U hU).toPartialEquiv.symm z = ⟨z.1, (q z.1).trans z.2⟩ := rfl

theorem orthonormalFrame_coordChange (q r : ∀ x, V x ≃ₗᵢ[k] F)
    (U U' : Set B) (hU : IsOpen U) (hU' : IsOpen U') (z : B × (F ≃ₗᵢ[k] F)) :
    orthonormalFrame q U hU ((orthonormalFrame r U' hU').toPartialEquiv.symm z) =
      (z.1, z.2 * ((q z.1).symm.trans (r z.1))) := rfl

end Bundle.Pretrivialization

namespace FiberBundle

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContinuousRiemannianBundle F V]

def orthonormalFramePrebundle :
    FiberPrebundle (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) := by
  classical
  have hex (x : B) := LinearIsometryEquiv.exists_continuous_coframe (F := F)
    x (linearIsometryEquivAt (F := F) V x)
  choose U hU hx q hq₀ hq using hex
  exact
    { pretrivializationAtlas := {e | ∃ (U : Set B) (hU : IsOpen U)
          (q : ∀ x, V x ≃ₗᵢ[ℝ] F),
          (∀ w : F, ContinuousOn (fun x => (⟨x, (q x).symm w⟩ : TotalSpace F V)) U) ∧
          e = Pretrivialization.orthonormalFrame q U hU}
      pretrivializationAt x := Pretrivialization.orthonormalFrame (q x) (U x) (hU x)
      mem_base_pretrivializationAt := hx
      pretrivialization_mem_atlas x := ⟨U x, hU x, q x, hq x, rfl⟩
      continuous_trivChange := by
        rintro _ ⟨U, hU, q, hq, rfl⟩ _ ⟨U', hU', r, hr, rfl⟩
        rw [Pretrivialization.target_inter_preimage_symm_source_eq]
        have htCLM := ContinuousLinearEquiv.continuousOn_bundle_trans_of_symm
          (fun x => (q x).toContinuousLinearEquiv)
          (fun x => (r x).toContinuousLinearEquiv) hq hr
        have ht : ContinuousOn (fun x => (q x).symm.trans (r x)) (U ∩ U') := by
          intro x hx
          have h := LinearIsometryEquiv.isEmbedding_toContinuousLinearMap
            (k := ℝ) (E := F) (F := F)
          exact h.isInducing.continuousWithinAt_iff.mpr (htCLM x hx)
        have ht' : ContinuousOn
            (fun z : B × (F ≃ₗᵢ[ℝ] F) => (q z.1).symm.trans (r z.1))
            ((U ∩ U') ×ˢ univ) :=
          ht.comp continuousOn_fst (fun _ hz => hz.1)
        have hcoord : ContinuousOn
            (fun z : B × (F ≃ₗᵢ[ℝ] F) => z.2 * ((q z.1).symm.trans (r z.1)))
            ((U ∩ U') ×ˢ univ) := continuousOn_snd.mul ht'
        exact (continuousOn_fst.prodMk hcoord).congr
          (fun z _ => Pretrivialization.orthonormalFrame_coordChange q r U U' hU hU' z)
      totalSpaceMk_isInducing := fun x =>
        Topology.isInducing_const_prod.mpr ((q x x).symm.precompHomeomorph.isInducing) }

theorem orthonormalFrame_isPrincipalBundle :
    letI : ∀ x, Nonempty (V x ≃ₗᵢ[ℝ] F) := fun x => ⟨linearIsometryEquivAt (F := F) V x⟩
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := (orthonormalFramePrebundle (F := F) V).toFiberBundle
    IsPrincipalBundle (fun x => V x ≃ₗᵢ[ℝ] F) := by
  let : ∀ x, Nonempty (V x ≃ₗᵢ[ℝ] F) := fun x => ⟨linearIsometryEquivAt (F := F) V x⟩
  let := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := (orthonormalFramePrebundle (F := F) V).toFiberBundle
  constructor
  intro e he x hx g p
  obtain ⟨e₀, he₀, rfl⟩ := he.out
  obtain ⟨U, hU, q, hq, rfl⟩ := he₀
  rfl


theorem continuousWithinAt_orthonormalFrame_of_symm
    {Z : Type*} [TopologicalSpace Z] {b : Z → B}
    {q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F} {s : Set Z} {z₀ : Z}
    (hq : ∀ w : F, ContinuousWithinAt
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) s z₀) :
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    ContinuousWithinAt
      (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) s z₀ := by
  let a := orthonormalFramePrebundle (F := F) V
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  have hb : ContinuousWithinAt b s z₀ := by
    have h := hq 0
    rw [FiberBundle.continuousWithinAt_totalSpace] at h
    exact h.1
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨hb, ?_⟩
  change ContinuousWithinAt
    (fun z => (a.pretrivializationAt (b z₀) ⟨b z, q z⟩).2) s z₀
  obtain ⟨U, hU, r, hr, he⟩ := a.pretrivialization_mem_atlas (b z₀)
  have hx : b z₀ ∈ U := by
    have h := a.mem_base_pretrivializationAt (b z₀)
    rw [he] at h
    exact h
  rw [he]
  change ContinuousWithinAt (fun z => (r (b z)).symm.trans (q z)) s z₀
  have hi : ContinuousWithinAt (fun z => (q z).symm.trans (r (b z))) s z₀ := by
    have hind := LinearIsometryEquiv.isEmbedding_toContinuousLinearMap
      (k := ℝ) (E := F) (F := F)
    rw [hind.isInducing.continuousWithinAt_iff]
    apply continuousWithinAt_clm_apply.mpr
    intro w
    have hf := ContinuousLinearEquiv.continuousOn_bundle_apply_of_symm
      (fun x => (r x).toContinuousLinearEquiv) hr
    have hf₀ := hf (⟨b z₀, (q z₀).symm w⟩ : TotalSpace F V) hx
    have hd : (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) ⁻¹'
        (TotalSpace.proj ⁻¹' U) ∈ 𝓝[s] z₀ := hb (hU.mem_nhds hx)
    have hg := ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin
      (f := fun z : Z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) hf₀ (hq w) hd
    exact hg.snd
  simpa only [Function.comp_def, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm] using
    (LinearIsometryEquiv.continuous_symm.continuousAt.comp_continuousWithinAt hi)

theorem continuousOn_orthonormalFrame_of_symm
    {Z : Type*} [TopologicalSpace Z] {b : Z → B}
    {q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F} {s : Set Z}
    (hq : ∀ w : F, ContinuousOn
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) s) :
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    ContinuousOn
      (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) s :=
  fun z hz => continuousWithinAt_orthonormalFrame_of_symm V (fun w => hq w z hz)


theorem continuousAt_orthonormalFrame_of_symm
    {Z : Type*} [TopologicalSpace Z] {b : Z → B}
    {q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F} {z₀ : Z}
    (hq : ∀ w : F, ContinuousAt
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) z₀) :
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    ContinuousAt
      (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) z₀ := by
  simpa only [continuousWithinAt_univ] using
    continuousWithinAt_orthonormalFrame_of_symm V (s := univ)
      (fun w => (hq w).continuousWithinAt)

theorem continuous_orthonormalFrame_of_symm
    {Z : Type*} [TopologicalSpace Z] {b : Z → B}
    {q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F}
    (hq : ∀ w : F, Continuous
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V))) :
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    Continuous
      (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) := by
  simpa only [continuousOn_univ] using
    continuousOn_orthonormalFrame_of_symm V (s := univ) (fun w => (hq w).continuousOn)

end FiberBundle
