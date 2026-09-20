import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Homeomorph.Lemmas

section

noncomputable section
open Set Filter Topology
open scoped Topology


theorem IsLocalHomeomorphOn.snd_fiber
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {Ω : Set X} (hΩ : IsOpen Ω) {f : X → Y} {g : X → Z}
    (h : IsLocalHomeomorphOn (fun x => (f x, g x)) Ω) (c : Y) :
    IsLocalHomeomorph (fun x : {x : X // x ∈ Ω ∧ f x = c} => g x) := by
  classical
  let L := {x : X // x ∈ Ω ∧ f x = c}
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro p
  obtain ⟨e₀, hp₀, he₀⟩ := h p.val p.property.1
  let e := e₀.restrOpen Ω hΩ
  have he (x : X) : e x = (f x, g x) := congrFun he₀.symm x
  have heΩ : e.source ⊆ Ω := fun x hx => hx.2
  have hp : p.val ∈ e.source := ⟨hp₀, p.property.1⟩
  let S : Set L := Subtype.val ⁻¹' e.source
  let T : Set Z := (fun z => (c, z)) ⁻¹' e.target
  have hS : IsOpen S := e.open_source.preimage continuous_subtype_val
  have hT : IsOpen T := e.open_target.preimage (continuous_const.prodMk continuous_id)
  have hinv (z : T) : f (e.symm (c, z.val)) = c := by
    have hh := e.right_inv z.property
    rw [he] at hh
    exact congrArg Prod.fst hh
  let H : S ≃ₜ T :=
    { toFun := fun x => ⟨g x.val.val, by
        have hh := e.map_source x.property
        rw [he, x.val.property.2] at hh
        exact hh⟩
      invFun := fun z => ⟨⟨e.symm (c, z.val), heΩ (e.map_target z.property), hinv z⟩,
        e.map_target z.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        change e.symm (c, g x.val.val) = x.val.val
        have hx : (c, g x.val.val) = e x.val.val := by rw [he, x.val.property.2]
        rw [hx, e.left_inv x.property]
      right_inv := by
        intro z
        apply Subtype.ext
        change g (e.symm (c, z.val)) = z.val
        have hh := e.right_inv z.property
        rw [he] at hh
        exact congrArg Prod.snd hh
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hco : Continuous (fun x : S => e x.val.val) :=
          e.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
            (fun x => x.property)
        have hg : (fun x : S => (e x.val.val).2) = fun x => g x.val.val := by
          funext x
          rw [he]
        exact hg ▸ hco.snd
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact e.symm.continuousOn.comp_continuous
          (continuous_const.prodMk continuous_subtype_val) (fun z => z.property) }
  have hEmbedding : IsOpenEmbedding (fun x : S => g x.val.val) :=
    hT.isOpenEmbedding_subtypeVal.comp H.isOpenEmbedding
  exact ⟨S, hS.mem_nhds hp, hEmbedding⟩

end

end
