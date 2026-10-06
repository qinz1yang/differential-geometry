import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesDatumJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceSign
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSeamFacesParams

/-!
# Draft 74, `local_faces`, step 3: structural facts on the faces of `∂M₂`

Lane S-JUNCTIONS (by S-JUNCTIONS4), G24 part 1 (suffix `_JN74`). Rows-free facts:

* `exists_open_inter_pieceBoundary_eq_JN74`: a model boundary face of a piece is, in the ambient
  space, the trace of an open set on the boundary of the piece (components of the boundary
  manifold are open, the piece map is a closed embedding);
* `exists_mem_lt_of_regular_JN74`: at an interior point a smooth function with `f x = 0`,
  `df x ≠ 0` takes negative and positive values in every neighbourhood;
* `lt_of_mem_interior_sublevel_JN74`: such an `x` in the interior of `{f ≤ 0}` has `f x < 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

/-- **A model boundary face of a piece is open in the boundary of the piece, in the ambient
space.** -/
theorem exists_open_inter_pieceBoundary_eq_JN74 (P : PieceEmbedding W)
    (Fm : ModelBoundaryFace P) :
    ∃ O : Set W.Carrier, IsOpen O ∧ O ∩ pieceBoundary P = P.map '' Fm.1 := by
  obtain ⟨U, hU, hUF⟩ := isOpen_induced_iff.1 (isOpen_boundaryFaceSet_GSF P Fm)
  obtain ⟨O, hO, hOU⟩ := P.isClosedEmbedding_map.isEmbedding.isInducing.isOpen_iff.1 hU
  have hFb : ∀ p ∈ Fm.1, p ∈ (𝓡∂ 3).boundary P.Piece := by
    obtain ⟨x, -, hm⟩ := Fm.2
    intro p hp
    rw [hm] at hp
    exact connectedComponentIn_subset _ _ hp
  refine ⟨O, hO, ?_⟩
  ext z
  constructor
  · rintro ⟨hzO, p, hp, rfl⟩
    refine ⟨p, ?_, rfl⟩
    have h : (⟨p, hp⟩ : BoundaryManifold (𝓡∂ 3) P.Piece) ∈ boundaryFaceSet_GSF P Fm := by
      rw [← hUF]
      change p ∈ U
      rw [← hOU]
      exact hzO
    exact h
  · rintro ⟨p, hp, rfl⟩
    have hpU : p ∈ U := by
      have h : (⟨p, hFb p hp⟩ : BoundaryManifold (𝓡∂ 3) P.Piece) ∈ boundaryFaceSet_GSF P Fm := hp
      rw [← hUF] at h
      exact h
    refine ⟨?_, p, hFb p hp, rfl⟩
    rw [← hOU] at hpU
    exact hpU

/-- **A regular zero of a smooth function at an interior point takes both signs nearby.** -/
theorem exists_mem_lt_of_regular_JN74 {f : W.Carrier → ℝ} {x : W.Carrier}
    (hx : x ∈ W.interior) (hf : MDifferentiableAt W.model 𝓘(ℝ, ℝ) f x) (hf0 : f x = 0)
    (hdf : mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0) {s : Set W.Carrier} (hs : s ∈ 𝓝 x) :
    (∃ y ∈ s, f y < 0) ∧ ∃ y ∈ s, 0 < f y := by
  have hxi : W.model.IsInteriorPoint x := hx
  have key : ∀ g : W.Carrier → ℝ, MDifferentiableAt W.model 𝓘(ℝ, ℝ) g x → g x = 0 →
      mfderiv W.model 𝓘(ℝ, ℝ) g x ≠ 0 → ∃ y ∈ s, g y < 0 := by
    intro g hg hg0 hdg
    obtain ⟨v, hv⟩ := exists_dirDeriv_neg_GTR (I := W.model) hdg
    have h1 := eventually_lt_chartLine_GTR hxi v hg hv
    rw [hg0] at h1
    have h2 := ((tendsto_chartLine_GTR (I := W.model) x v).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).eventually (eventually_mem_nhds_iff.2 hs)
    obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
    exact ⟨_, mem_of_mem_nhds ht2, ht1⟩
  refine ⟨key f hf hf0 hdf, ?_⟩
  obtain ⟨y, hy, hlt⟩ := key (fun z => -f z) hf.neg (by simp [hf0]) (by
    change mfderiv W.model 𝓘(ℝ, ℝ) (-f) x ≠ 0
    rw [mfderiv_neg]
    exact neg_ne_zero.2 hdf)
  exact ⟨y, hy, by linarith⟩

/-- **A regular zero at an interior point is not in the interior of the sublevel set.** -/
theorem lt_of_mem_interior_sublevel_JN74 {f : W.Carrier → ℝ} {x : W.Carrier}
    (hx : x ∈ W.interior) (hf : MDifferentiableAt W.model 𝓘(ℝ, ℝ) f x)
    (hreg : f x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0) (hxi : x ∈ interior {y | f y ≤ 0}) :
    f x < 0 := by
  have hxle : f x ≤ 0 := (interior_subset hxi : x ∈ {y | f y ≤ 0})
  rcases hxle.lt_or_eq with h | h
  · exact h
  · obtain ⟨-, y, hy, hpos⟩ := exists_mem_lt_of_regular_JN74 hx hf h (hreg h)
      (mem_interior_iff_mem_nhds.1 hxi)
    exact absurd (show f y ≤ 0 from hy) (not_le.2 hpos)

end GC.GraphManifold.Assembly.FC39P0
