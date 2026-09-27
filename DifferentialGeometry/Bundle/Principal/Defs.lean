import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Algebra.Torsor.Basic

noncomputable section

open Set

namespace Bundle

section Principal

variable {G B : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace B]
  (P : B → Type*) [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P]

class IsPrincipalBundle : Prop where
  trivialization_smul' : ∀ (e : Trivialization G (π G P)), MemTrivializationAtlas e →
    ∀ (x : B), x ∈ e.baseSet → ∀ (g : G) (p : P x),
      (e ⟨x, g • p⟩).2 = g * (e ⟨x, p⟩).2

end Principal

namespace Trivialization

section LocalSection

variable {G B : Type*} [One G] [TopologicalSpace G] [TopologicalSpace B]
  {P : B → Type*} [∀ x, Nonempty (P x)] [TopologicalSpace (TotalSpace G P)]

def principalSection (e : Trivialization G (π G P)) (x : B) : P x := e.symm x 1

@[simp]
theorem principalSection_apply (e : Trivialization G (π G P)) {x : B} (hx : x ∈ e.baseSet) :
    e ⟨x, e.principalSection x⟩ = (x, 1) :=
  e.apply_mk_symm hx 1

theorem continuousOn_principalSection (e : Trivialization G (π G P)) :
    ContinuousOn (fun x => (⟨x, e.principalSection x⟩ : TotalSpace G P)) e.baseSet := by
  have h := e.continuousOn_symm.comp
    (continuousOn_id.prodMk (continuousOn_const (c := (1 : G))))
    (fun x hx => ⟨hx, Set.mem_univ _⟩)
  exact h

end LocalSection

variable {G B : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace B]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]

theorem apply_smul (e : Trivialization G (π G P)) [MemTrivializationAtlas e]
    {x : B} (hx : x ∈ e.baseSet) (g : G) (p : P x) :
    (e ⟨x, g • p⟩).2 = g * (e ⟨x, p⟩).2 :=
  IsPrincipalBundle.trivialization_smul' e inferInstance x hx g p

theorem apply_sdiv (e : Trivialization G (π G P)) [MemTrivializationAtlas e]
    {x : B} (hx : x ∈ e.baseSet) (p q : P x) :
    p /ₛ q = (e ⟨x, p⟩).2 / (e ⟨x, q⟩).2 := by
  have h := e.apply_smul hx (p /ₛ q) q
  rw [sdiv_smul] at h
  rw [h, mul_div_cancel_right]

theorem sdiv_principalSection (e : Trivialization G (π G P))
    [MemTrivializationAtlas e] {x : B} (hx : x ∈ e.baseSet) (p : P x) :
    p /ₛ e.principalSection x = (e ⟨x, p⟩).2 := by
  rw [e.apply_sdiv hx, e.principalSection_apply hx, div_one]

theorem smul_principalSection (e : Trivialization G (π G P))
    [MemTrivializationAtlas e] {x : B} (hx : x ∈ e.baseSet) (g : G) :
    g • e.principalSection x = e.symm x g := by
  calc
    g • e.principalSection x = e.symm x (e ⟨x, g • e.principalSection x⟩).2 :=
      (e.symm_apply_apply_mk hx _).symm
    _ = e.symm x g := by rw [e.apply_smul hx, e.principalSection_apply hx, mul_one]

theorem continuousOn_principalSection_sdiv
    (e e' : Trivialization G (π G P)) [MemTrivializationAtlas e] :
    ContinuousOn (fun x => e'.principalSection x /ₛ e.principalSection x)
      (e.baseSet ∩ e'.baseSet) := by
  have h := e.continuousOn.comp
    (e'.continuousOn_principalSection.mono inter_subset_right)
    (fun x hx => e.mem_source.mpr hx.1)
  apply h.snd.congr
  intro x hx
  exact e.sdiv_principalSection hx.1 _

end Trivialization

namespace Trivial

variable {G B : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace B]

instance isPrincipalBundle : IsPrincipalBundle (Trivial B G) where
  trivialization_smul' e he _ _ _ _ := by
    let := he
    rw [eq_trivialization B G e]
    rfl

end Trivial

end Bundle
