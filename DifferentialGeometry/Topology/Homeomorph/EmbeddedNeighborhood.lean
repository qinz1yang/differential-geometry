import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

noncomputable section
open Set
open scoped Topology

namespace Topology.IsEmbedding

theorem exists_openPartialHomeomorph_of_range_mem_nhds
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {D : Set X} (hD : IsOpen D) {F : D → Y} (hF : IsEmbedding F)
    {o : D} (honto : range F ∈ 𝓝 (F o)) :
    ∃ e : OpenPartialHomeomorph Y X,
      F o ∈ e.source ∧ e (F o) = (o : X) ∧ e.target ⊆ D ∧
      ∀ y ∈ e.source, ∃ x : D, F x = y ∧ e y = (x : X) := by
  classical
  obtain ⟨V, hVrange, hV, hoV⟩ := mem_nhds_iff.mp honto
  let S : Set D := F ⁻¹' V
  have hS : IsOpen S := hV.preimage hF.continuous
  let e0 : S ≃ₜ V := hF.homeomorphOfSubsetRange hVrange
  let iS : S → X := fun x => ((x : D) : X)
  have hiS : IsOpenEmbedding iS :=
    hD.isOpenEmbedding_subtypeVal.comp hS.isOpenEmbedding_subtypeVal
  let : Nonempty S := ⟨⟨o, hoV⟩⟩
  let : Nonempty V := ⟨⟨F o, hoV⟩⟩
  let eV := (hV.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : V → Y))
  let eS := hiS.toOpenPartialHomeomorph iS
  let e := eV.symm.trans (e0.symm.toOpenPartialHomeomorph.trans eS)
  have heV (y : Y) (hy : y ∈ V) : eV.symm y = ⟨y, hy⟩ := by
    exact hV.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv
      (x := (⟨y, hy⟩ : V))
  have heSource : e.source = V := by
    ext y
    simp only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      eV, IsOpenEmbedding.toOpenPartialHomeomorph_target, e0,
      Homeomorph.toOpenPartialHomeomorph_source, eS,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]
    simp only [Subtype.range_coe]
  have heEval (y : Y) (hy : y ∈ V) : e y = ((e0.symm ⟨y, hy⟩ : S) : X) := by
    change iS (e0.symm (eV.symm y)) = _
    rw [heV y hy]
  have heForward (y : Y) (hy : y ∈ V) : F (e0.symm ⟨y, hy⟩ : D) = y := by
    exact congrArg Subtype.val (e0.apply_symm_apply ⟨y, hy⟩)
  refine ⟨e, heSource.symm ▸ hoV, ?_, ?_, ?_⟩
  · rw [heEval (F o) hoV]
    have hxo : (e0.symm ⟨F o, hoV⟩ : D) = o := hF.injective (heForward _ _)
    exact congrArg Subtype.val hxo
  · intro x hx
    have hy : e.symm x ∈ V := heSource ▸ e.map_target hx
    rw [← e.right_inv hx, heEval _ hy]
    exact (e0.symm ⟨e.symm x, hy⟩ : D).property
  · intro y hy
    have hyV : y ∈ V := heSource ▸ hy
    exact ⟨(e0.symm ⟨y, hyV⟩ : D), heForward y hyV, heEval y hyV⟩

end Topology.IsEmbedding
