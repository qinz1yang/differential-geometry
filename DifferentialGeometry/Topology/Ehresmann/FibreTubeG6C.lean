import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Basic

/-!
# The tube lemma for circle charts (lane O-G6C, G2 step L1)

For a map `f : Wt → H` with a local product chart `φ : E × Q → Wt` over an embedded piece
`σ : E → H` of the base (`range φ = X ∩ f⁻¹(range σ)`, `f ∘ φ = σ ∘ fst`) and a COMPACT fibre
model `Q`: every open set `U` containing the whole fibre `X ∩ f⁻¹{y}` contains the whole fibres
over all base points near `y` (`exists_open_fibre_subset_of_chart_G6C`).
-/

set_option autoImplicit false

open Set Function Topology

namespace DifferentialGeometry.Topology

variable {E Q Wt H : Type*} [TopologicalSpace E] [TopologicalSpace Q] [CompactSpace Q]
  [TopologicalSpace Wt] [TopologicalSpace H]

/-- **Tube lemma for a fibre chart.** -/
theorem exists_open_fibre_subset_of_chart_G6C {X : Set Wt} {f : Wt → H} {Bs : Set H} {y : H}
    {σ : E → H} {φ : E × Q → Wt} {O : Set H} {x₀ : E} (hx₀ : σ x₀ = y) (hσ : IsEmbedding σ)
    (hO : IsOpen O) (hσr : range σ = Bs ∩ O) (hφc : Continuous φ)
    (hφr : range φ = X ∩ f ⁻¹' range σ) (hφf : ∀ x z, f (φ (x, z)) = σ x) {U : Set Wt}
    (hU : IsOpen U) (hfib : X ∩ f ⁻¹' {y} ⊆ U) :
    ∃ O' : Set H, IsOpen O' ∧ y ∈ O' ∧ ∀ y' ∈ O' ∩ Bs, X ∩ f ⁻¹' {y'} ⊆ U := by
  have hsub : ({x₀} : Set E) ×ˢ (univ : Set Q) ⊆ φ ⁻¹' U := by
    rintro ⟨x, z⟩ ⟨hx, -⟩
    rw [mem_singleton_iff] at hx
    subst hx
    have hmem : φ (x, z) ∈ range φ := ⟨(x, z), rfl⟩
    rw [hφr] at hmem
    exact hfib ⟨hmem.1, by rw [mem_preimage, hφf, hx₀]; rfl⟩
  obtain ⟨V, V', hV, -, hx₀V, hV'univ, hVsub⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ (hU.preimage hφc) hsub
  obtain ⟨U', hU', hU'V⟩ := hσ.isOpen_iff.mp hV
  refine ⟨U' ∩ O, hU'.inter hO, ⟨?_, ?_⟩, ?_⟩
  · have : x₀ ∈ σ ⁻¹' U' := hU'V ▸ hx₀V rfl
    rw [← hx₀]
    exact this
  · have : y ∈ range σ := ⟨x₀, hx₀⟩
    rw [hσr] at this
    exact this.2
  · rintro y' ⟨⟨hy'U', hy'O⟩, hy'B⟩ q ⟨hqX, hqy'⟩
    have hy'r : y' ∈ range σ := by
      rw [hσr]
      exact ⟨hy'B, hy'O⟩
    obtain ⟨x', rfl⟩ := hy'r
    have hqy : f q = σ x' := hqy'
    have hqr : q ∈ range φ := by
      rw [hφr]
      exact ⟨hqX, ⟨x', hqy.symm⟩⟩
    obtain ⟨⟨x'', z⟩, rfl⟩ := hqr
    have hx'' : x'' = x' := hσ.injective ((hφf x'' z).symm.trans hqy)
    subst hx''
    have hx'V : x'' ∈ V := by
      rw [← hU'V]
      exact hy'U'
    exact hVsub (mk_mem_prod hx'V (hV'univ (mem_univ z)))

end DifferentialGeometry.Topology
