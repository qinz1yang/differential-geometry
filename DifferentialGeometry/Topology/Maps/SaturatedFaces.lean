import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! ZSP03 (master207B, B:6481): zero faces are saturated and descend to the bases.
Point-set kernels: a face that is a full preimage is saturated; with connected fibres, the
complement of an interior is saturated; a proper map sends a closed saturated set to a closed set
whose full preimage is that set; and a connected face meeting the bundle region over an isolated
base level is one whole fibre (no invariance of domain is used). -/

set_option autoImplicit false
open Set Filter Topology

namespace DifferentialGeometry.Topology

theorem frontier_saturated_of_eq_preimage {M B : Type*} [TopologicalSpace M] {f : M → B}
    {Z : Set M} {T : Set B} (h : frontier Z = f ⁻¹' T) {p q : M} (hpq : f p = f q)
    (hp : p ∈ frontier Z) : q ∈ frontier Z := by
  rw [h] at hp ⊢
  change f q ∈ T
  rw [← hpq]
  exact hp

theorem isPreconnected_subset_interior_or_subset_compl_closure {X : Type*} [TopologicalSpace X]
    {s A : Set X} (hs : IsPreconnected s) (h : Disjoint s (frontier A)) :
    s ⊆ interior A ∨ s ⊆ (closure A)ᶜ := by
  apply hs.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
  · exact Set.disjoint_left.mpr fun x hx hx' => hx' (interior_subset_closure hx)
  · intro x hx
    by_cases hint : x ∈ interior A
    · exact Or.inl hint
    · right
      intro hcl
      exact Set.disjoint_left.mp h hx ⟨hcl, hint⟩

/-- Saturation of `M₁ ∩ X = X \ int Z` when fibres in `X` are connected and the face `∂Z` is
saturated. -/
theorem not_mem_interior_of_same_fiber {M B : Type*} [TopologicalSpace M] (f : M → B)
    (X Z : Set M) (hconn : ∀ p ∈ X, IsPreconnected {q | q ∈ X ∧ f q = f p})
    (hsat : ∀ p ∈ X, ∀ q ∈ X, f p = f q → p ∈ frontier Z → q ∈ frontier Z)
    {p q : M} (hp : p ∈ X) (hq : q ∈ X) (hpq : f p = f q) (hpZ : p ∉ interior Z) :
    q ∉ interior Z := by
  by_cases hmeet : ∃ r, (r ∈ X ∧ f r = f p) ∧ r ∈ frontier Z
  · obtain ⟨r, ⟨hrX, hr⟩, hrZ⟩ := hmeet
    have hqZ := hsat r hrX q hq (hr.trans hpq) hrZ
    exact fun hint => hqZ.2 hint
  · have hdisj : Disjoint {r | r ∈ X ∧ f r = f p} (frontier Z) :=
      Set.disjoint_left.mpr fun r hr hrZ => hmeet ⟨r, hr, hrZ⟩
    rcases isPreconnected_subset_interior_or_subset_compl_closure (hconn p hp) hdisj with h | h
    · exact absurd (h ⟨hp, rfl⟩) hpZ
    · exact fun hint => h ⟨hq, hpq.symm⟩ (interior_subset_closure hint)

/-- A proper map sends a closed saturated set to a closed set whose full preimage is the set. -/
theorem isClosed_image_and_preimage_image_eq {X B : Type*} [TopologicalSpace X]
    [TopologicalSpace B] (f : X → B) (hf : IsProperMap f) (A : Set X) (hA : IsClosed A)
    (hsat : ∀ p q, f p = f q → p ∈ A → q ∈ A) :
    IsClosed (f '' A) ∧ f ⁻¹' (f '' A) = A := by
  refine ⟨hf.isClosedMap A hA, ?_⟩
  ext q
  constructor
  · rintro ⟨p, hp, hpq⟩
    exact hsat p q hpq hp
  · intro hq
    exact ⟨q, hq, rfl⟩

/-- `j = 3`: a preconnected face `S` whose part over the open bundle region `X` is the full
preimage of a base set `D`, meets the compact fibre over an isolated point `w` of `D`; then `S`
is that entire fibre. -/
theorem eq_fiber_of_isPreconnected_of_isolated {M B : Type*} [TopologicalSpace M] [T2Space M]
    [TopologicalSpace B] (f : M → B) (X S : Set M) (D : Set B) (hX : IsOpen X)
    (hf : ContinuousOn f X) (hS : IsPreconnected S) (hSX : S ∩ X = X ∩ f ⁻¹' D) {w : B}
    (hiso : ∃ O : Set B, IsOpen O ∧ O ∩ D = {w}) (hcpt : IsCompact (X ∩ f ⁻¹' {w}))
    (hne : (X ∩ f ⁻¹' {w}).Nonempty) : S = X ∩ f ⁻¹' {w} := by
  obtain ⟨O, hO, hOD⟩ := hiso
  have hwD : w ∈ D := by
    have : w ∈ O ∩ D := by rw [hOD]; exact rfl
    exact this.2
  have hfibS : X ∩ f ⁻¹' {w} ⊆ S := by
    intro x hx
    have : x ∈ X ∩ f ⁻¹' D := ⟨hx.1, by
      have h := hx.2
      change f x ∈ D
      rw [show f x = w from h]
      exact hwD⟩
    rw [← hSX] at this
    exact this.1
  apply Subset.antisymm _ hfibS
  set u : Set M := X ∩ f ⁻¹' O
  set v : Set M := (X ∩ f ⁻¹' {w})ᶜ
  have hu : IsOpen u := hf.isOpen_inter_preimage hX hO
  have hv : IsOpen v := hcpt.isClosed.isOpen_compl
  by_contra hnot
  obtain ⟨y, hyS, hyfib⟩ := Set.not_subset.mp hnot
  obtain ⟨x₀, hx₀⟩ := hne
  have hsuv : S ⊆ u ∪ v := by
    intro x hx
    by_cases hxf : x ∈ X ∩ f ⁻¹' {w}
    · left
      refine ⟨hxf.1, ?_⟩
      change f x ∈ O
      rw [show f x = w from hxf.2]
      have : w ∈ O ∩ D := by rw [hOD]; exact rfl
      exact this.1
    · exact Or.inr hxf
  obtain ⟨z, hzS, hzu, hzv⟩ := hS u v hu hv hsuv ⟨x₀, hfibS hx₀, (hsuv (hfibS hx₀)).resolve_right
    (fun h => h hx₀)⟩ ⟨y, hyS, hyfib⟩
  apply hzv
  have hzD : z ∈ X ∩ f ⁻¹' D := by rw [← hSX]; exact ⟨hzS, hzu.1⟩
  have hzOD : f z ∈ O ∩ D := ⟨hzu.2, hzD.2⟩
  rw [hOD] at hzOD
  exact ⟨hzu.1, hzOD⟩

/-- A level point of a real function with nonzero derivative is isolated in that level. -/
theorem exists_isOpen_inter_preimage_eq_singleton_of_hasDerivAt {g : ℝ → ℝ} {a g' : ℝ}
    (hg : HasDerivAt g g' a) (hg' : g' ≠ 0) :
    ∃ O : Set ℝ, IsOpen O ∧ O ∩ g ⁻¹' {g a} = {a} := by
  have h := hg.eventually_ne (c := g a) hg'
  rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at h
  obtain ⟨O, hO, hOopen, haO⟩ := h
  refine ⟨O, hOopen, ?_⟩
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨hzO, hz⟩
    by_contra hne
    exact hO z hzO hne hz
  · rintro rfl
    exact ⟨haO, rfl⟩

end DifferentialGeometry.Topology
