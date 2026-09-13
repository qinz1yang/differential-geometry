import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion

set_option autoImplicit false

noncomputable section

open Set

universe u

namespace DifferentialGeometry.Topology.VanKampen

private noncomputable def subtypePreimageHomeomorph {X : Type u} [TopologicalSpace X]
    {A B : Set X} : {x : ↥A // x.1 ∈ B} ≃ₜ ↥(A ∩ B) where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk (fun x : ↥(A ∩ B) => x.2.1)).subtype_mk _

private theorem pathConnectedSpace_of_homeomorph {A B : Type u} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) : PathConnectedSpace A ↔ PathConnectedSpace B := by
  constructor
  · intro h
    have h3 := (pathConnectedSpace_iff_univ.mp h).image e.continuous
    rw [Set.image_univ, e.surjective.range_eq] at h3
    exact pathConnectedSpace_iff_univ.mpr h3
  · intro h
    have h3 := (pathConnectedSpace_iff_univ.mp h).image e.symm.continuous
    rw [Set.image_univ, e.symm.surjective.range_eq] at h3
    exact pathConnectedSpace_iff_univ.mpr h3

private theorem simplyConnectedSpace_subtype_preimage_iff {X : Type u} [TopologicalSpace X]
    {A B : Set X} :
    SimplyConnectedSpace {x : ↥A // x.1 ∈ B} ↔ SimplyConnectedSpace ↥(A ∩ B) :=
  (subtypePreimageHomeomorph (A := A) (B := B)).toHomotopyEquiv.simplyConnectedSpace_iff

private theorem pathConnectedSpace_subtype_preimage_iff {X : Type u} [TopologicalSpace X]
    {A B : Set X} :
    PathConnectedSpace {x : ↥A // x.1 ∈ B} ↔ PathConnectedSpace ↥(A ∩ B) :=
  pathConnectedSpace_of_homeomorph (subtypePreimageHomeomorph (A := A) (B := B))

theorem simplyConnectedSpace_inter_coverMembers_of_open_twoCover
    {X : Type u} [TopologicalSpace X] (W L R : Set X)
    (hL : IsOpen L) (hR : IsOpen R) (hcov : W ⊆ L ∪ R)
    [SimplyConnectedSpace ↥W] [SimplyConnectedSpace ↥(W ∩ (L ∩ R))]
    [PathConnectedSpace ↥(W ∩ L)] [PathConnectedSpace ↥(W ∩ R)] :
    SimplyConnectedSpace ↥(W ∩ L) ∧ SimplyConnectedSpace ↥(W ∩ R) := by
  let U : Set ↥W := {x | (x : X) ∈ L}
  let V : Set ↥W := {x | (x : X) ∈ R}
  have hU : IsOpen U := hL.preimage continuous_subtype_val
  have hV : IsOpen V := hR.preimage continuous_subtype_val
  have hcover : U ∪ V = univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    rcases hcov x.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hnonempty : Nonempty ↥(W ∩ (L ∩ R)) := inferInstance
  let y : ↥(W ∩ (L ∩ R)) := Classical.choice hnonempty
  let x₀ : ↥W := ⟨y.1, y.2.1⟩
  have hx₀U : x₀ ∈ U := y.2.2.1
  have hx₀V : x₀ ∈ V := y.2.2.2
  have hpcU : PathConnectedSpace ↥U :=
    (pathConnectedSpace_subtype_preimage_iff (A := W) (B := L)).mpr inferInstance
  have hpcV : PathConnectedSpace ↥V :=
    (pathConnectedSpace_subtype_preimage_iff (A := W) (B := R)).mpr inferInstance
  have hUV : U ∩ V = {x : ↥W | (x : X) ∈ L ∩ R} := by
    ext x
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  have hscUV : SimplyConnectedSpace ↥(U ∩ V) := by
    rw [hUV]
    exact (simplyConnectedSpace_subtype_preimage_iff (A := W) (B := L ∩ R)).mpr inferInstance
  obtain ⟨hUsc, hVsc⟩ :=
    @simplyConnected_coverMembers_of_union ↥W _ U V hU hV hcover x₀ ⟨hx₀U, hx₀V⟩
      hpcU hpcV inferInstance hscUV
  exact ⟨(simplyConnectedSpace_subtype_preimage_iff (A := W) (B := L)).mp hUsc,
    (simplyConnectedSpace_subtype_preimage_iff (A := W) (B := R)).mp hVsc⟩

theorem simplyConnectedSpace_of_twoCover_chain
    {X : Type u} [TopologicalSpace X] (W L R : ℕ → Set X)
    (hL : ∀ k, IsOpen (L k)) (hR : ∀ k, IsOpen (R k))
    (hcov : ∀ k, W k ⊆ L k ∪ R k)
    (hnext : ∀ k, W (k + 1) = W k ∩ L k ∨ W (k + 1) = W k ∩ R k)
    (hstart : SimplyConnectedSpace ↥(W 0))
    (hoverlap : ∀ k, SimplyConnectedSpace ↥(W k ∩ (L k ∩ R k)))
    (hpathL : ∀ k, PathConnectedSpace ↥(W k ∩ L k))
    (hpathR : ∀ k, PathConnectedSpace ↥(W k ∩ R k)) :
    ∀ n, SimplyConnectedSpace ↥(W n) := by
  intro n
  induction n with
  | zero => exact hstart
  | succ k ih =>
      have hstep :=
        @simplyConnectedSpace_inter_coverMembers_of_open_twoCover X _ (W k) (L k) (R k)
          (hL k) (hR k) (hcov k) ih (hoverlap k) (hpathL k) (hpathR k)
      rcases hnext k with h | h
      · rw [h]
        exact hstep.1
      · rw [h]
        exact hstep.2

end DifferentialGeometry.Topology.VanKampen
