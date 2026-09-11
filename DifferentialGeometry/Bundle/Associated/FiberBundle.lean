import DifferentialGeometry.Bundle.Principal.Defs
import DifferentialGeometry.Bundle.Associated.Topology
import Mathlib.Topology.VectorBundle.Basic

noncomputable section

open Set Bundle
open scoped Topology

namespace Bundle.Pretrivialization

variable {k G B W : Type*} [Semiring k] [Group G]
  [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace W]
  [AddCommMonoid W] [Module k W]
  {P : B → Type*} [∀ x, Torsor G (P x)] [TopologicalSpace (TotalSpace G P)]

def associated (ρ : Representation k G W) (e : Trivialization G (π G P)) :
    Pretrivialization W (π W (fun x => P x →ₑ[ρ] W)) where
  toFun z := (z.1, z.2 (e.principalSection z.1))
  invFun z := ⟨z.1, (ρ.evalLinearEquiv (e.principalSection z.1)).symm z.2⟩
  source := TotalSpace.proj ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' := fun _ h => ⟨h, mem_univ _⟩
  map_target' := fun _ h => h.1
  left_inv' := fun ⟨x, v⟩ _ => by
    simp only [TotalSpace.mk_inj]
    exact (ρ.evalLinearEquiv (e.principalSection x)).symm_apply_apply v
  right_inv' := fun ⟨x, w⟩ _ => by
    simp only [Prod.mk_right_inj]
    exact (ρ.evalLinearEquiv (e.principalSection x)).apply_symm_apply w
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance associated.isLinear (ρ : Representation k G W) (e : Trivialization G (π G P)) :
    (associated ρ e).IsLinear k where
  linear _ _ :=
    { map_add _ _ := rfl
      map_smul _ _ := rfl }

@[simp]
theorem associated_apply (ρ : Representation k G W) (e : Trivialization G (π G P))
    (z : TotalSpace W (fun x => P x →ₑ[ρ] W)) :
    associated ρ e z = (z.1, z.2 (e.principalSection z.1)) := rfl

@[simp]
theorem associated_symm_apply (ρ : Representation k G W) (e : Trivialization G (π G P))
    (z : B × W) :
    (associated ρ e).toPartialEquiv.symm z =
      ⟨z.1, (ρ.evalLinearEquiv (e.principalSection z.1)).symm z.2⟩ := rfl

theorem associated_coordChange (ρ : Representation k G W)
    (e e' : Trivialization G (π G P)) (z : B × W) :
    associated ρ e ((associated ρ e').toPartialEquiv.symm z) =
      (z.1, ρ (e.principalSection z.1 /ₛ e'.principalSection z.1) z.2) := rfl

theorem associatedSet_iff (ρ : Representation k G W)
    (e : Trivialization G (π G P)) {C : Set W}
    (hC : ∀ g : G, MapsTo (ρ g) C C)
    (z : TotalSpace W (fun x => P x →ₑ[ρ] W)) :
    z.2 ∈ ρ.associatedSet (P z.1) C ↔ (associated ρ e z).2 ∈ C :=
  ρ.mem_associatedSet_iff hC (e.principalSection z.1) z.2

theorem image_associatedSet (ρ : Representation k G W)
    (e : Trivialization G (π G P)) {C : Set W}
    (hC : ∀ g : G, MapsTo (ρ g) C C) :
    associated ρ e ''
      {z : TotalSpace W (fun x => P x →ₑ[ρ] W) |
        z.1 ∈ e.baseSet ∧ z.2 ∈ ρ.associatedSet (P z.1) C} = e.baseSet ×ˢ C := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hv.1, (associatedSet_iff ρ e hC v).mp hv.2⟩
  · intro hz
    refine ⟨⟨z.1, (ρ.evalLinearEquiv (e.principalSection z.1)).symm z.2⟩,
      ⟨hz.1, ?_⟩, ?_⟩
    · apply (ρ.mem_associatedSet_iff hC (e.principalSection z.1) _).mpr
      simpa only [← Representation.evalLinearEquiv_apply, LinearEquiv.apply_symm_apply]
        using hz.2
    · exact (associated ρ e).right_inv ⟨hz.1, mem_univ _⟩

end Bundle.Pretrivialization

namespace Representation

variable {k G B W : Type*} [Semiring k] [Group G]
  [TopologicalSpace G] [TopologicalSpace B]
  [AddCommMonoid W] [TopologicalSpace W] [Module k W]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]

def associatedFiberPrebundle (ρ : Representation k G W)
    (hρ : Continuous (fun z : G × W => ρ z.1 z.2)) :
    FiberPrebundle W (fun x => P x →ₑ[ρ] W) where
  pretrivializationAtlas :=
    {e | ∃ (p : Trivialization G (π G P)), MemTrivializationAtlas p ∧
      e = Pretrivialization.associated ρ p}
  pretrivializationAt x :=
    Pretrivialization.associated ρ (trivializationAt G P x)
  mem_base_pretrivializationAt x := mem_baseSet_trivializationAt G P x
  pretrivialization_mem_atlas x := ⟨trivializationAt G P x, inferInstance, rfl⟩
  continuous_trivChange := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    let := he
    let := he'
    rw [Pretrivialization.target_inter_preimage_symm_source_eq]
    have h := e'.continuousOn_principalSection_sdiv e
    have hg : ContinuousOn
        (fun z : B × W => e.principalSection z.1 /ₛ e'.principalSection z.1)
        ((e.baseSet ∩ e'.baseSet) ×ˢ univ) :=
      h.comp continuousOn_fst (fun z hz => ⟨hz.1.2, hz.1.1⟩)
    have ha := hρ.comp_continuousOn (hg.prodMk continuousOn_snd)
    exact (continuousOn_fst.prodMk ha).congr
      (fun z _ => Pretrivialization.associated_coordChange ρ e e' z)
  totalSpaceMk_isInducing := by
    intro x
    let e := ρ.evalContinuousLinearEquiv (fun g => hρ.comp (continuous_const.prodMk continuous_id))
      ((trivializationAt G P x).principalSection x)
    exact Topology.isInducing_const_prod.mpr e.toHomeomorph.isInducing

def associatedTrivialization (ρ : Representation k G W)
    (hρ : Continuous (fun z : G × W => ρ z.1 z.2))
    (e : Trivialization G (π G P)) [MemTrivializationAtlas e] :
    @Trivialization B W _ _ _ (ρ.associatedFiberPrebundle (P := P) hρ).totalSpaceTopology
      (π W (fun x => P x →ₑ[ρ] W)) :=
  (ρ.associatedFiberPrebundle hρ).trivializationOfMemPretrivializationAtlas
    ⟨e, inferInstance, rfl⟩

instance associatedTrivialization.isLinear (ρ : Representation k G W)
    (hρ : Continuous (fun z : G × W => ρ z.1 z.2))
    (e : Trivialization G (π G P)) [MemTrivializationAtlas e] :
    letI := (ρ.associatedFiberPrebundle (P := P) hρ).totalSpaceTopology
    (ρ.associatedTrivialization hρ e).IsLinear k := by
  let := (ρ.associatedFiberPrebundle (P := P) hρ).totalSpaceTopology
  exact { linear := fun _ _ => { map_add := fun _ _ => rfl, map_smul := fun _ _ => rfl } }

@[simp]
theorem associatedTrivialization_apply (ρ : Representation k G W)
    (hρ : Continuous (fun z : G × W => ρ z.1 z.2))
    (e : Trivialization G (π G P)) [MemTrivializationAtlas e]
    (z : TotalSpace W (fun x => P x →ₑ[ρ] W)) :
    ρ.associatedTrivialization hρ e z = (z.1, z.2 (e.principalSection z.1)) := rfl

theorem associatedTrivialization_coordChangeL_apply (ρ : Representation k G W)
    (hρ : Continuous (fun z : G × W => ρ z.1 z.2))
    (e e' : Trivialization G (π G P)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {x : B} (hx : x ∈ e.baseSet ∩ e'.baseSet) (w : W) :
    let _ := (ρ.associatedFiberPrebundle (P := P) hρ).totalSpaceTopology
    (Trivialization.coordChangeL k (ρ.associatedTrivialization hρ e)
      (ρ.associatedTrivialization hρ e') x) w =
      ρ (e'.principalSection x /ₛ e.principalSection x) w := by
  let _ := (ρ.associatedFiberPrebundle (P := P) hρ).totalSpaceTopology
  have hx' : x ∈ (ρ.associatedTrivialization hρ e).baseSet ∩
      (ρ.associatedTrivialization hρ e').baseSet := by
    change x ∈ e.baseSet ∩ e'.baseSet
    exact hx
  rw [Bundle.Trivialization.coordChangeL_apply' _ _ hx']
  change ((ρ.associatedTrivialization hρ e')
      ((ρ.associatedTrivialization hρ e).toOpenPartialHomeomorph.symm (x, w))).2 = _
  convert congrArg Prod.snd
      (Bundle.Pretrivialization.associated_coordChange ρ e' e (x, w)) using 1
  rfl

theorem isClosed_totalSpace_associatedSet (ρ : Representation k G W)
    (hρ : Continuous (fun z : G × W => ρ z.1 z.2)) {C : Set W}
    (hC : IsClosed C) (hG : ∀ g : G, MapsTo (ρ g) C C) :
    letI := (ρ.associatedFiberPrebundle (P := P) hρ).totalSpaceTopology
    IsClosed {z : TotalSpace W (fun x => P x →ₑ[ρ] W) |
      z.2 ∈ ρ.associatedSet (P z.1) C} := by
  simp only [isClosed_iSup_iff, isClosed_coinduced]
  rintro e ⟨p, hp, rfl⟩
  have h : IsClosed {z : (Pretrivialization.associated ρ p).target |
      z.val.2 ∈ C} :=
    hC.preimage (continuous_snd.comp continuous_subtype_val)
  convert h using 1
  ext z
  change ((ρ.evalLinearEquiv (p.principalSection z.val.1)).symm z.val.2 ∈
    ρ.associatedSet (P z.val.1) C) ↔ z.val.2 ∈ C
  rw [ρ.mem_associatedSet_iff hG (p.principalSection z.val.1)]
  simp only [← Representation.evalLinearEquiv_apply, LinearEquiv.apply_symm_apply]

variable {W' : Type*} [AddCommMonoid W'] [TopologicalSpace W'] [Module k W']

theorem continuous_totalSpace_associatedMap (ρ : Representation k G W)
    (σ : Representation k G W')
    (hρ : Continuous (fun z : G × W => ρ z.1 z.2))
    (hσ : Continuous (fun z : G × W' => σ z.1 z.2))
    (f : W → W') (hf : ∀ g w, f (ρ g w) = σ g (f w)) (hfc : Continuous f) :
    letI := (ρ.associatedFiberPrebundle (P := P) hρ).totalSpaceTopology
    letI := (σ.associatedFiberPrebundle (P := P) hσ).totalSpaceTopology
    Continuous (fun z : TotalSpace W (fun x => P x →ₑ[ρ] W) =>
      (⟨z.1, ρ.associatedMap σ f hf z.2⟩ : TotalSpace W' (fun x => P x →ₑ[σ] W'))) := by
  let := (σ.associatedFiberPrebundle (P := P) hσ).totalSpaceTopology
  simp only [continuous_iSup_dom, continuous_coinduced_dom]
  rintro e ⟨p, hp, rfl⟩
  let := hp
  have hi : Continuous (fun z : (Pretrivialization.associated ρ p).target =>
      (z.val.1, f z.val.2)) :=
    continuous_subtype_val.fst.prodMk (hfc.comp continuous_subtype_val.snd)
  let q := σ.associatedTrivialization hσ p
  have h := q.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
    hi (fun z => ⟨z.property.1, mem_univ _⟩)
  apply h.congr
  intro z
  symm
  change (⟨z.val.1,
    ρ.associatedMap σ f hf ((ρ.evalLinearEquiv (p.principalSection z.val.1)).symm z.val.2)⟩ :
      TotalSpace W' (fun x => P x →ₑ[σ] W')) =
    ⟨z.val.1, (σ.evalLinearEquiv (p.principalSection z.val.1)).symm (f z.val.2)⟩
  congr 1
  rw [ρ.evalLinearEquiv_associatedMap σ f hf (p.principalSection z.val.1)]
  simp only [LinearEquiv.apply_symm_apply]

end Representation
