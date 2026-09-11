import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BicollarAxialOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BicollarOrder

set_option autoImplicit false

noncomputable section

open Set Metric Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
  [TopologicalSpace M] [T2Space M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
  (r : ℝ) (hr : 0 < r)
  (φ : {p : A × ℝ // -r < p.2 ∧ p.2 < r} → M) (hφ : IsOpenEmbedding φ) (a : A)

include hφ

local notation "Φ" => φ ∘ bicollarLineHomeomorph r hr
local notation "σ" => OpenPartialHomeomorph.symm (OpenPartialHomeomorph.univBall (0 : ℝ) r)

theorem finite_bicollar_ordered_band
    (hzero : IsCompact (closure (bicollarLowerSide Φ a 0)))
    (s t : ℝ) (hs : -r < s ∧ s < r) (ht : -r < t ∧ t < r) (hst : s < t) :
    closure (bicollarLowerSide Φ a (σ s)) ⊆ bicollarLowerSide Φ a (σ t) ∧
      closure (bicollarLowerSide Φ a (σ t)) =
        closure (bicollarLowerSide Φ a (σ s)) ∪ φ '' {q | s ≤ q.val.2 ∧ q.val.2 ≤ t} ∧
      (φ '' {q | s ≤ q.val.2 ∧ q.val.2 ≤ t})ᶜ =
        bicollarLowerSide Φ a (σ s) ∪ bicollarUpperSide Φ a (σ t) := by
  have hΦ : IsOpenEmbedding Φ := hφ.comp (bicollarLineHomeomorph r hr).isOpenEmbedding
  have hστ := (bicollar_axial_inverse_lt_iff r hr s t hs ht).mpr hst
  have hband : Φ '' ((univ : Set A) ×ˢ Icc (σ s) (σ t)) =
      φ '' {q | s ≤ q.val.2 ∧ q.val.2 ≤ t} := by
    rw [image_comp, bicollarLineHomeomorph_image_band r hr s t hs ht]
  obtain ⟨hnested, hclosure, hcompl⟩ := bicollar_ordered_band Φ hΦ a hzero hστ
  rw [hband] at hclosure hcompl
  exact ⟨hnested, hclosure, hcompl⟩

theorem finite_bicollar_slice_frontiers (s : ℝ) (hs : -r < s ∧ s < r) :
    frontier (bicollarLowerSide Φ a (σ s)) = range (fun y => φ ⟨(y, s), hs⟩) ∧
      frontier (bicollarUpperSide Φ a (σ s)) = range (fun y => φ ⟨(y, s), hs⟩) ∧
      interior (closure (bicollarLowerSide Φ a (σ s))) = bicollarLowerSide Φ a (σ s) := by
  have hΦ : IsOpenEmbedding Φ := hφ.comp (bicollarLineHomeomorph r hr).isOpenEmbedding
  have hslice : range (fun y => Φ (y, σ s)) = range (fun y => φ ⟨(y, s), hs⟩) := by
    congr 1
    funext y
    change φ (bicollarLineHomeomorph r hr (y, σ s)) = φ ⟨(y, s), hs⟩
    rw [bicollarLineHomeomorph_slice r hr s hs y]
  obtain ⟨_hB, _hE, _hBop, _hEop, _hBE, _hcover, hBfr, hEfr, _hBcl, _hEcl,
    _hn, _hp⟩ := bicollar_slice_components Φ hΦ a (σ s)
  rw [hslice] at hBfr hEfr
  exact ⟨hBfr, hEfr, bicollar_lower_regular_open Φ hΦ a (σ s)⟩

theorem finite_bicollar_path_crosses_slice (s : ℝ) (hs : -r < s ∧ s < r)
    {x y : M} (hx : x ∈ bicollarLowerSide Φ a (σ s))
    (hy : y ∈ bicollarUpperSide Φ a (σ s)) (γ : Path x y) :
    ∃ u, γ u ∈ range (fun z => φ ⟨(z, s), hs⟩) := by
  have hΦ : IsOpenEmbedding Φ := hφ.comp (bicollarLineHomeomorph r hr).isOpenEmbedding
  obtain ⟨u, z, hz⟩ := bicollar_path_crosses_slice Φ hΦ a (σ s) hx hy γ
  refine ⟨u, z, ?_⟩
  change φ (bicollarLineHomeomorph r hr (z, σ s)) = γ u at hz
  rwa [bicollarLineHomeomorph_slice r hr s hs z] at hz

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
