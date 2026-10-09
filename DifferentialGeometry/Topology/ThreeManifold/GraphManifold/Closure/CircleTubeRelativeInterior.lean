import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CornerRelativeInterior
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base

/-!
# Consumer: FDC03's relative interior on the whole corner tube of the rows' circle bundle

`fdc03_relInterior_circleTube_EFC`: for the row circle bundle `R` (`FC39P0Base.lean`) with an open,
closed projection, R1's inputs at a rim base point `c₀`, and the local model `M₂ = {h_F ≥ 0}`,
`M^edge = {h_F ≥ 0, T ≤ 0}` on an open neighbourhood of the whole rim fibre, there is an open
`U ∋ c₀` such that at EVERY point `x` of the whole tube over `U` — the horizontal face included —
the relative interior of `M^edge` in `M₂` (computed in the carrier) is `{h_F ≥ 0, T < 0}` and the
remainder `M₃ = M₂ \ int_{M₂} M^edge` is `{T ≥ 0, h_F ≥ 0}` (FDC03, B:7341–7344; D74-14).
`relInterior_val_iff_EFC` transfers relative interiors between an open subset and the ambient space.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint

namespace GC.GraphManifold.Assembly.FC39P0

universe u

/-- Relative interiors at points of an open subset `O` agree with those computed inside `O`. -/
theorem relInterior_val_iff_EFC {Y : Type*} [TopologicalSpace Y] {O : Set Y} (hO : IsOpen O)
    {S A : Set Y} {p : O} :
    (p : Y) ∈ Subtype.val '' interior (Subtype.val ⁻¹' A : Set S) ↔
      p ∈ Subtype.val '' interior
        (Subtype.val ⁻¹' (Subtype.val ⁻¹' A : Set O) : Set (Subtype.val ⁻¹' S : Set O)) := by
  rw [mem_image_interior_preimage_val_iff, mem_image_interior_preimage_val_iff]
  constructor
  · rintro ⟨hpS, O', hO', hpO', hO'A⟩
    exact ⟨hpS, Subtype.val ⁻¹' O', hO'.preimage continuous_subtype_val, hpO',
      fun q hq => hO'A ⟨hq.1, hq.2⟩⟩
  · rintro ⟨hpS, O'', hO'', hpO'', hO''A⟩
    refine ⟨hpS, Subtype.val '' O'', hO.isOpenMap_subtype_val _ hO'', ⟨p, hpO'', rfl⟩, ?_⟩
    rintro _ ⟨⟨q, hq, rfl⟩, hqS⟩
    exact hO''A ⟨hq, hqS⟩

/-- **FDC03 on the whole corner tube of the row circle bundle** (relative interior in the carrier,
horizontal face included). -/
theorem fdc03_relInterior_circleTube_EFC (W : CompactCarrier.{u}) (R : CircleBundle W)
    (hcl : IsClosedMap R.proj) (hop : IsOpenMap R.proj) (c₀ : R.Base) {T res : R.domain → ℝ}
    {V : TopologicalSpace.Opens R.Base} (hc₀ : c₀ ∈ V) {Tb hb : R.Base → ℝ}
    (hTb : ContMDiffOn (𝓡 2) 𝓘(ℝ) ∞ Tb V) (hhb : ContMDiffOn (𝓡 2) 𝓘(ℝ) ∞ hb V)
    (hdesc : ∀ x : R.domain, R.proj x ∈ V → T x = Tb (R.proj x) ∧ res x = hb (R.proj x))
    (hcen : Tb c₀ = 0 ∧ hb c₀ = 0) {x₀ : R.domain} (hx₀ : R.proj x₀ = c₀)
    (hrank : Surjective (mfderiv W.model 𝓘(ℝ, ℝ × ℝ) (fun z => (T z, res z)) x₀))
    {N : Set R.domain} (hN : IsOpen N) (hfib : R.proj ⁻¹' {c₀} ⊆ N)
    {M₂ Medge : Set W.Carrier}
    (hsign : ∀ x ∈ N, ((x : W.Carrier) ∈ M₂ ↔ 0 ≤ res x) ∧
      ((x : W.Carrier) ∈ Medge ↔ 0 ≤ res x ∧ T x ≤ 0)) :
    ∃ U : Set R.Base, IsOpen U ∧ c₀ ∈ U ∧ ∀ x : R.domain, R.proj x ∈ U →
      ((x : W.Carrier) ∈ Subtype.val '' interior (Subtype.val ⁻¹' Medge : Set M₂) ↔
        0 ≤ res x ∧ T x < 0) ∧
      ((x : W.Carrier) ∈ M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' Medge : Set M₂) ↔
        0 ≤ T x ∧ 0 ≤ res x) := by
  have hEB : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  have hf : MDifferentiableAt W.model (𝓡 2) R.proj x₀ :=
    (R.proj_smooth x₀).mdifferentiableAt (by simp)
  obtain ⟨U, hU, hc₀U, hrel⟩ :=
    DifferentialGeometry.Geometry.Collapse.EdgeDisk.fdc03_relInterior_of_wholeCornerTube_EFC hEB
      R.proj.continuous hcl hop hc₀ hTb hhb hdesc hcen hx₀ hf hrank hN hfib
      (M₂ := Subtype.val ⁻¹' M₂) (Medge := Subtype.val ⁻¹' Medge) hsign
  refine ⟨U, hU, hc₀U, fun x hx => ⟨?_, ?_⟩⟩
  · rw [relInterior_val_iff_EFC R.domain.isOpen (p := x)]
    exact (hrel x hx).1
  · have h := (hrel x hx).2
    rw [Set.mem_sdiff] at h
    rw [Set.mem_sdiff, relInterior_val_iff_EFC R.domain.isOpen (p := x)]
    exact h

end GC.GraphManifold.Assembly.FC39P0
