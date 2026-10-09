import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Changing the model fibre of a smooth vector bundle (lane CMS3-CARRIER, group G2b)

The range subbundle of the tree (`ContMDiffVectorSubbundle.range`) has model fibre `Fin k → ℝ`
(sup norm), while the frozen LFR46 / LFR47 interfaces quantify over bundles whose model fibre is an
inner product space. This small file re-models a fibre bundle along a continuous linear
equivalence `L : F ≃L[ℝ] F'` of model fibres, keeping the fibres `V b`:

* `remodelEquiv : TotalSpace F' V ≃ TotalSpace F V` is the tautological bijection; for any topology
  on `TotalSpace F' V` for which it is inducing (`remodelTopology` is the induced one),
  `remodelHomeomorph` is a homeomorphism;
* `remodelTriv L hσ e = (e.compHomeomorph σ).transFiberHomeomorph L` turns trivializations into
  trivializations with model `F'` (`remodelTriv_apply`, `remodelTriv_symm`);
* `remodelFiberBundle`, `remodelVectorBundle`, `remodelContMDiffVectorBundle`: the re-modelled
  bundle is a fibre bundle, a vector bundle and a `C^n` vector bundle (coordinate changes
  `L ∘ c ∘ L⁻¹`);
* `contMDiff_remodelEquiv`: the tautological map from the new total space to the old one is `C^n`
  (in charts it is `id × L⁻¹`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FiniteSoul

section Equiv

variable {B : Type*} (F F' : Type*) (V : B → Type*)

/-- The tautological bijection between the total spaces for two model fibres. -/
def remodelEquiv : TotalSpace F' V ≃ TotalSpace F V where
  toFun z := ⟨z.proj, z.snd⟩
  invFun z := ⟨z.proj, z.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {F F' V}

@[simp] theorem remodelEquiv_apply (z : TotalSpace F' V) :
    remodelEquiv F F' V z = ⟨z.proj, z.snd⟩ := rfl

variable (F F' V) in
/-- The topology on the new total space induced from the old one. -/
@[reducible] def remodelTopology [TopologicalSpace (TotalSpace F V)] :
    TopologicalSpace (TotalSpace F' V) :=
  TopologicalSpace.induced (remodelEquiv F F' V) ‹_›

theorem isInducing_remodelEquiv [TopologicalSpace (TotalSpace F V)] :
    @IsInducing _ _ (remodelTopology F F' V) _ (remodelEquiv F F' V) :=
  @IsInducing.mk _ _ (remodelTopology F F' V) _ _ rfl

variable [TopologicalSpace (TotalSpace F V)] [TopologicalSpace (TotalSpace F' V)]

/-- The tautological homeomorphism, for a topology on the new total space making `remodelEquiv`
inducing. -/
def remodelHomeomorph (hσ : IsInducing (remodelEquiv F F' V)) :
    TotalSpace F' V ≃ₜ TotalSpace F V :=
  (remodelEquiv F F' V).toHomeomorphOfIsInducing hσ

@[simp] theorem remodelHomeomorph_apply (hσ : IsInducing (remodelEquiv F F' V))
    (z : TotalSpace F' V) : remodelHomeomorph hσ z = ⟨z.proj, z.snd⟩ := rfl

end Equiv

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [TopologicalSpace (TotalSpace F' V)]

section Triv

/-- A trivialization with model `F`, re-modelled along `L`. -/
def remodelTriv (L : F ≃L[ℝ] F') (hσ : IsInducing (remodelEquiv F F' V))
    (e : Trivialization F (π F V)) : Trivialization F' (π F' V) :=
  (e.compHomeomorph (remodelHomeomorph hσ)).transFiberHomeomorph L.toHomeomorph

@[simp] theorem remodelTriv_baseSet (L : F ≃L[ℝ] F') (hσ : IsInducing (remodelEquiv F F' V))
    (e : Trivialization F (π F V)) : (remodelTriv L hσ e).baseSet = e.baseSet := rfl

theorem remodelTriv_apply (L : F ≃L[ℝ] F') (hσ : IsInducing (remodelEquiv F F' V))
    (e : Trivialization F (π F V)) (z : TotalSpace F' V) :
    remodelTriv L hσ e z = ((e ⟨z.proj, z.snd⟩).1, L (e ⟨z.proj, z.snd⟩).2) := rfl

theorem remodelTriv_snd (L : F ≃L[ℝ] F') (hσ : IsInducing (remodelEquiv F F' V))
    (e : Trivialization F (π F V)) (b : B) (v : V b) :
    (remodelTriv L hσ e ⟨b, v⟩).2 = L (e ⟨b, v⟩).2 := rfl

end Triv

section Linear

variable [∀ b, AddCommMonoid (V b)]

theorem remodelTriv_symm (L : F ≃L[ℝ] F') (hσ : IsInducing (remodelEquiv F F' V))
    (e : Trivialization F (π F V)) {b : B} (hb : b ∈ e.baseSet) (y : F') :
    (remodelTriv L hσ e).symm b y = e.symm b (L.symm y) := by
  have hb' : b ∈ (remodelTriv L hσ e).baseSet := hb
  have h1 : (remodelTriv L hσ e ⟨b, e.symm b (L.symm y)⟩).2 = y := by
    rw [remodelTriv_snd, e.apply_mk_symm hb, ContinuousLinearEquiv.apply_symm_apply]
  conv_lhs => rw [← h1]
  exact (remodelTriv L hσ e).symm_apply_apply_mk hb' _

variable [∀ b, Module ℝ (V b)]

theorem remodelTriv_isLinear (L : F ≃L[ℝ] F') (hσ : IsInducing (remodelEquiv F F' V))
    (e : Trivialization F (π F V)) [e.IsLinear ℝ] : (remodelTriv L hσ e).IsLinear ℝ where
  linear b hb :=
    { map_add := fun v w => by
        simp only [remodelTriv_snd, (e.linear ℝ hb).map_add, map_add]
      map_smul := fun c v => by
        simp only [remodelTriv_snd, (e.linear ℝ hb).map_smul, map_smul] }

theorem remodelTriv_coordChangeL (L : F ≃L[ℝ] F') (hσ : IsInducing (remodelEquiv F F' V))
    (e e' : Trivialization F (π F V)) [e.IsLinear ℝ] [e'.IsLinear ℝ]
    [(remodelTriv L hσ e).IsLinear ℝ] [(remodelTriv L hσ e').IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    ((remodelTriv L hσ e).coordChangeL ℝ (remodelTriv L hσ e') b : F' →L[ℝ] F') =
      (L : F →L[ℝ] F').comp ((e.coordChangeL ℝ e' b : F →L[ℝ] F).comp
        (L.symm : F' →L[ℝ] F)) := by
  ext1 y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [Trivialization.coordChangeL_apply (remodelTriv L hσ e) (remodelTriv L hσ e') hb,
    remodelTriv_symm L hσ e hb.1, remodelTriv_snd, Trivialization.coordChangeL_apply e e' hb]

end Linear

variable [∀ b, TopologicalSpace (V b)]

/-- The re-modelled fibre bundle. -/
@[reducible] def remodelFiberBundle [FiberBundle F V] (L : F ≃L[ℝ] F')
    (hσ : IsInducing (remodelEquiv F F' V)) : FiberBundle F' V where
  totalSpaceMk_isInducing' b := by
    have h := FiberBundle.totalSpaceMk_isInducing F V b
    exact (hσ.of_comp_iff).mp h
  trivializationAtlas' := remodelTriv L hσ '' FiberBundle.trivializationAtlas F V
  trivializationAt' b := remodelTriv L hσ (trivializationAt F V b)
  mem_baseSet_trivializationAt' b := FiberBundle.mem_baseSet_trivializationAt F V b
  trivialization_mem_atlas' b :=
    ⟨trivializationAt F V b, FiberBundle.trivialization_mem_atlas F V b, rfl⟩

variable [∀ b, AddCommMonoid (V b)] [∀ b, Module ℝ (V b)]

theorem remodelVectorBundle [FiberBundle F V] [VectorBundle ℝ F V]
    (L : F ≃L[ℝ] F') (hσ : IsInducing (remodelEquiv F F' V)) :
    letI := remodelFiberBundle L hσ
    VectorBundle ℝ F' V := by
  let _ := remodelFiberBundle L hσ
  refine ⟨?_, ?_⟩
  · rintro _ ⟨⟨e, he, rfl⟩⟩
    have : MemTrivializationAtlas e := ⟨he⟩
    exact remodelTriv_isLinear L hσ e
  · rintro _ _ ⟨⟨e, he, rfl⟩⟩ ⟨⟨e', he', rfl⟩⟩
    have : MemTrivializationAtlas e := ⟨he⟩
    have : MemTrivializationAtlas e' := ⟨he'⟩
    have := remodelTriv_isLinear L hσ e
    have := remodelTriv_isLinear L hσ e'
    have hc := VectorBundle.continuousOn_coordChange' (R := ℝ) e e'
    refine ContinuousOn.congr (f := fun b => (L : F →L[ℝ] F').comp
      ((e.coordChangeL ℝ e' b : F →L[ℝ] F).comp (L.symm : F' →L[ℝ] F))) ?_ ?_
    · exact (continuous_const.clm_comp continuous_id).comp_continuousOn
        (hc.clm_comp continuousOn_const)
    · intro b hb
      exact remodelTriv_coordChangeL L hσ e e' hb

variable [ChartedSpace HB B]

theorem remodelContMDiffVectorBundle {n : ℕ∞ω} [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V IB]
    (L : F ≃L[ℝ] F') (hσ : IsInducing (remodelEquiv F F' V)) :
    letI := remodelFiberBundle L hσ
    letI := remodelVectorBundle L hσ
    ContMDiffVectorBundle n F' V IB := by
  let _ := remodelFiberBundle L hσ
  let _ := remodelVectorBundle L hσ
  refine ⟨?_⟩
  rintro _ _ ⟨⟨e, he, rfl⟩⟩ ⟨⟨e', he', rfl⟩⟩
  have : MemTrivializationAtlas e := ⟨he⟩
  have : MemTrivializationAtlas e' := ⟨he'⟩
  have := remodelTriv_isLinear L hσ e
  have := remodelTriv_isLinear L hσ e'
  have hc := ContMDiffVectorBundle.contMDiffOn_coordChangeL (IB := IB) (n := n) e e'
  refine ContMDiffOn.congr (f := fun b => (L : F →L[ℝ] F').comp
    ((e.coordChangeL ℝ e' b : F →L[ℝ] F).comp (L.symm : F' →L[ℝ] F))) ?_ ?_
  · have hL : ContMDiffOn IB 𝓘(ℝ, F →L[ℝ] F') n (fun _ : B => (L : F →L[ℝ] F'))
        (e.baseSet ∩ e'.baseSet) := contMDiffOn_const
    have hLs : ContMDiffOn IB 𝓘(ℝ, F' →L[ℝ] F) n (fun _ : B => (L.symm : F' →L[ℝ] F))
        (e.baseSet ∩ e'.baseSet) := contMDiffOn_const
    exact hL.clm_comp (hc.clm_comp hLs)
  · intro b hb
    exact remodelTriv_coordChangeL L hσ e e' hb

/-- **The tautological map from the re-modelled total space to the old one is `C^n`.** -/
theorem contMDiff_remodelEquiv {n : ℕ∞ω} [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V IB]
    (L : F ≃L[ℝ] F') (hσ : IsInducing (remodelEquiv F F' V)) :
    letI := remodelFiberBundle L hσ
    letI := remodelVectorBundle L hσ
    ContMDiff (IB.prod 𝓘(ℝ, F')) (IB.prod 𝓘(ℝ, F)) n (remodelEquiv F F' V) := by
  let _ := remodelFiberBundle L hσ
  let _ := remodelVectorBundle L hσ
  let _ := remodelContMDiffVectorBundle (IB := IB) (n := n) L hσ
  intro z
  rw [contMDiffAt_totalSpace]
  refine ⟨Bundle.contMDiffAt_proj (fun b => V b), ?_⟩
  have hid := (contMDiffAt_totalSpace (IB := IB) (F := F') (E := V) (n := n)
    (f := id) (x₀ := z)).mp contMDiffAt_id
  have h2 : ContMDiffAt (IB.prod 𝓘(ℝ, F')) 𝓘(ℝ, F) n
      (fun x => (L.symm : F' →L[ℝ] F) ((trivializationAt F' V z.proj x).2)) z :=
    (L.symm : F' →L[ℝ] F).contMDiff.contMDiffAt.comp z hid.2
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  change (trivializationAt F V z.proj ⟨x.proj, x.snd⟩).2 =
    L.symm (L (trivializationAt F V z.proj ⟨x.proj, x.snd⟩).2)
  rw [ContinuousLinearEquiv.symm_apply_apply]

end DifferentialGeometry.Geometry.FiniteSoul
