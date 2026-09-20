/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingSource

/-!
# Locality of PL double crossings at the double point

The PL double crossing predicates only see the behaviour of the map near the fibre over
the double point. Two forms of this are recorded here, for each of the plain, boundary
and normal predicates.

* `HasPLNormalDoubleCrossingAt.inter_preimage_of_isOpen` shrinks the source `P` of a
  crossing at `y` to `P ∩ f ⁻¹' V`, for any open set `V` containing `y`.
* `HasPLNormalDoubleCrossingAt.of_eqOn_of_isOpen` transfers a crossing to any map `g`
  agreeing with `f` on that shrunk source, provided the two shrunk sources agree.

The intended application is the last lemma of the file: a regluing which changes a map
only over a closed set `C` avoiding `y`, and which sends the changed part of the source
into `C`, preserves every normal double crossing at `y`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

/-- Intersecting a neighbourhood of `c` within `P` with `f ⁻¹' V` produces a
neighbourhood of `c` within the shrunk source `P ∩ f ⁻¹' V`. -/
theorem inter_preimage_mem_nhdsWithin {E F : Type*} [TopologicalSpace E] {f : E → F}
    {P C : Set E} {V : Set F} {c : E} (hC : C ∈ 𝓝[P] c) : C ∩ f ⁻¹' V ∈ 𝓝[P ∩ f ⁻¹' V] c :=
  Filter.inter_mem (nhdsWithin_mono c inter_subset_left hC)
    (Filter.mem_of_superset self_mem_nhdsWithin inter_subset_right)

/-- For a map continuous on `P` and an open target set `V`, the shrunk source
`P ∩ g ⁻¹' V` is a relative neighbourhood in `P` of each of its points. -/
theorem exists_mem_nhds_inter_subset_inter_preimage {E F : Type*} [TopologicalSpace E]
    [TopologicalSpace F] {g : E → F} {P : Set E} (hg : ContinuousOn g P) {V : Set F}
    (hV : IsOpen V) {a : E} (ha : a ∈ P ∩ g ⁻¹' V) : ∃ W ∈ 𝓝 a, P ∩ W ⊆ P ∩ g ⁻¹' V := by
  obtain ⟨u, hu, hueq⟩ := continuousOn_iff'.mp hg V hV
  exact ⟨u, hu.mem_nhds (hueq.subset ⟨ha.2, ha.1⟩).1,
    fun x hx => ⟨hx.1, (hueq.superset ⟨hx.2, hx.1⟩).1⟩⟩

/-- Fibres of `g` over points close to `y` lie in the shrunk source `P ∩ g ⁻¹' V`,
whenever `V` is an open set containing `y`. -/
theorem eventually_inter_preimage_singleton_subset {E F : Type*} [TopologicalSpace F]
    {g : E → F} (P : Set E) {V : Set F} (hV : IsOpen V) {y : F} (hy : y ∈ V) :
    ∀ᶠ z in 𝓝 y, P ∩ g ⁻¹' {z} ⊆ P ∩ g ⁻¹' V := by
  filter_upwards [hV.mem_nhds hy] with z hz x hx
  exact ⟨hx.1, show g x ∈ V from (mem_singleton_iff.mp hx.2).symm ▸ hz⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The restriction of a PL homeomorphism on `A` to the part of `A` lying over an open
set `V` is again a PL homeomorphism onto its image. -/
theorem isPLHomeomorphOn_inter_preimage_of_isOpen {f : E → F} {A : Set E}
    (hf : IsPLHomeomorphOn f A (f '' A)) {V : Set F} (hV : IsOpen V) :
    IsPLHomeomorphOn f (A ∩ f ⁻¹' V) (f '' (A ∩ f ⁻¹' V)) := by
  have hinj : InjOn f (A ∩ f ⁻¹' V) := hf.bijOn.injOn.mono inter_subset_left
  refine ⟨hinj.bijOn_image, ?_, ?_⟩
  · simpa only [Function.id_comp] using
      (isPiecewiseAffineOn_id (u := V) hV).comp hf.isPiecewiseAffineOn
  · rw [image_inter_preimage]
    refine (hf.isPiecewiseAffineOn_invFunOn.inter_of_isOpen hV).congr ?_
    rintro z ⟨⟨x, hx, rfl⟩, hfx⟩
    rw [hinj.leftInvOn_invFunOn ⟨hx, hfx⟩, hf.bijOn.injOn.leftInvOn_invFunOn hx]

/-- A PL double crossing at `y` may be shrunk to the part of its source lying over any
open set `V` containing `y`. -/
theorem HasPLDoubleCrossingAt.inter_preimage_of_isOpen {f : E → F} {P : Set E} {y : F}
    {V : Set F} (hV : IsOpen V) (hy : y ∈ V) (h : HasPLDoubleCrossingAt f P y) :
    HasPLDoubleCrossingAt f (P ∩ f ⁻¹' V) y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hcross, hcov⟩ := h
  have haV : f a ∈ V := hfa.symm ▸ hy
  have hbV : f b ∈ V := hfb.symm ▸ hy
  refine ⟨a, b, A ∩ f ⁻¹' V, B ∩ f ⁻¹' V, ⟨ha, haV⟩, ⟨hb, hbV⟩, hfa, hfb,
    inter_subset_inter hAP Subset.rfl, inter_subset_inter hBP Subset.rfl,
    hdis.mono inter_subset_left inter_subset_left, inter_preimage_mem_nhdsWithin hA,
    inter_preimage_mem_nhdsWithin hB, isPLHomeomorphOn_inter_preimage_of_isOpen hfA hV,
    isPLHomeomorphOn_inter_preimage_of_isOpen hfB hV, ?_, ?_⟩
  · rw [image_inter_preimage, image_inter_preimage]
    apply hcross.congr <;>
      filter_upwards [hV.mem_nhds hy] with z hz <;>
        simp only [mem_inter_iff, hz, and_true]
  · filter_upwards [hcov] with z hz x hx
    exact (hz ⟨hx.1.1, hx.2⟩).elim (fun hm => Or.inl ⟨hm, hx.1.2⟩)
      (fun hm => Or.inr ⟨hm, hx.1.2⟩)

/-- A PL boundary double crossing at `y` may be shrunk to the part of its source lying
over any open set `V` containing `y`. -/
theorem HasPLBoundaryDoubleCrossingAt.inter_preimage_of_isOpen {f : E → F} {P : Set E}
    {Mb : Set F} {y : F} {V : Set F} (hV : IsOpen V) (hy : y ∈ V)
    (h : HasPLBoundaryDoubleCrossingAt f P Mb y) :
    HasPLBoundaryDoubleCrossingAt f (P ∩ f ⁻¹' V) Mb y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hcross, hcov⟩ := h
  have haV : f a ∈ V := hfa.symm ▸ hy
  have hbV : f b ∈ V := hfb.symm ▸ hy
  refine ⟨a, b, A ∩ f ⁻¹' V, B ∩ f ⁻¹' V, ⟨ha, haV⟩, ⟨hb, hbV⟩, hfa, hfb,
    inter_subset_inter hAP Subset.rfl, inter_subset_inter hBP Subset.rfl,
    hdis.mono inter_subset_left inter_subset_left, inter_preimage_mem_nhdsWithin hA,
    inter_preimage_mem_nhdsWithin hB, isPLHomeomorphOn_inter_preimage_of_isOpen hfA hV,
    isPLHomeomorphOn_inter_preimage_of_isOpen hfB hV, ?_, ?_⟩
  · rw [image_inter_preimage, image_inter_preimage]
    apply hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) <;>
      filter_upwards [hV.mem_nhds hy] with z hz <;>
        simp only [mem_inter_iff, hz, and_true]
  · filter_upwards [hcov] with z hz x hx
    exact (hz ⟨hx.1.1, hx.2⟩).elim (fun hm => Or.inl ⟨hm, hx.1.2⟩)
      (fun hm => Or.inr ⟨hm, hx.1.2⟩)

/-- A PL normal double crossing at `y` may be shrunk to the part of its source lying
over any open set `V` containing `y`. -/
theorem HasPLNormalDoubleCrossingAt.inter_preimage_of_isOpen {f : E → F} {P : Set E}
    {Bd : Set F} {y : F} {V : Set F} (hV : IsOpen V) (hy : y ∈ V)
    (h : HasPLNormalDoubleCrossingAt f P Bd y) :
    HasPLNormalDoubleCrossingAt f (P ∩ f ⁻¹' V) Bd y := by
  rcases h with ⟨hyB, Mb, hcross⟩ | ⟨hyB, hcross⟩
  · exact Or.inl ⟨hyB, Mb, hcross.inter_preimage_of_isOpen hV hy⟩
  · exact Or.inr ⟨hyB, hcross.inter_preimage_of_isOpen hV hy⟩

/-- A PL double crossing at `y` transfers to any map `g` which agrees with `f` over an
open set `V` containing `y`, as soon as the two shrunk sources agree. -/
theorem HasPLDoubleCrossingAt.of_eqOn_of_isOpen {f g : E → F} {P P' : Set E} {y : F}
    (hg : ContinuousOn g P') {V : Set F} (hV : IsOpen V) (hy : y ∈ V)
    (hPP' : P ∩ f ⁻¹' V = P' ∩ g ⁻¹' V) (hfg : EqOn f g (P ∩ f ⁻¹' V))
    (h : HasPLDoubleCrossingAt f P y) : HasPLDoubleCrossingAt g P' y := by
  have h₁ : HasPLDoubleCrossingAt g (P ∩ f ⁻¹' V) y :=
    (h.inter_preimage_of_isOpen hV hy).congr_source hfg
  rw [hPP'] at h₁
  refine h₁.mono_of_subset inter_subset_left (Subset.refl P') ?_ ?_
  · exact fun a ha _ => exists_mem_nhds_inter_subset_inter_preimage hg hV ha
  · exact eventually_inter_preimage_singleton_subset P' hV hy

/-- A PL boundary double crossing at `y` transfers to any map `g` which agrees with `f`
over an open set `V` containing `y`, as soon as the two shrunk sources agree. -/
theorem HasPLBoundaryDoubleCrossingAt.of_eqOn_of_isOpen {f g : E → F} {P P' : Set E}
    {Mb : Set F} {y : F} (hg : ContinuousOn g P') {V : Set F} (hV : IsOpen V) (hy : y ∈ V)
    (hPP' : P ∩ f ⁻¹' V = P' ∩ g ⁻¹' V) (hfg : EqOn f g (P ∩ f ⁻¹' V))
    (h : HasPLBoundaryDoubleCrossingAt f P Mb y) :
    HasPLBoundaryDoubleCrossingAt g P' Mb y := by
  have h₁ : HasPLBoundaryDoubleCrossingAt g (P ∩ f ⁻¹' V) Mb y :=
    (h.inter_preimage_of_isOpen hV hy).congr_source hfg
  rw [hPP'] at h₁
  refine h₁.mono_of_subset inter_subset_left (Subset.refl P') ?_ ?_
  · exact fun a ha _ => exists_mem_nhds_inter_subset_inter_preimage hg hV ha
  · exact eventually_inter_preimage_singleton_subset P' hV hy

/-- A PL normal double crossing at `y` transfers to any map `g` which agrees with `f`
over an open set `V` containing `y`, as soon as the two shrunk sources agree. -/
theorem HasPLNormalDoubleCrossingAt.of_eqOn_of_isOpen {f g : E → F} {P P' : Set E}
    {Bd : Set F} {y : F} (hg : ContinuousOn g P') {V : Set F} (hV : IsOpen V) (hy : y ∈ V)
    (hPP' : P ∩ f ⁻¹' V = P' ∩ g ⁻¹' V) (hfg : EqOn f g (P ∩ f ⁻¹' V))
    (h : HasPLNormalDoubleCrossingAt f P Bd y) : HasPLNormalDoubleCrossingAt g P' Bd y := by
  have h₁ : HasPLNormalDoubleCrossingAt g (P ∩ f ⁻¹' V) Bd y :=
    (h.inter_preimage_of_isOpen hV hy).congr_source hfg
  rw [hPP'] at h₁
  refine h₁.mono_of_subset inter_subset_left (Subset.refl P') ?_ ?_
  · exact fun a ha _ => exists_mem_nhds_inter_subset_inter_preimage hg hV ha
  · exact eventually_inter_preimage_singleton_subset P' hV hy

/-- Consistency check for the transfer lemma: taking `g = f` and `P' = P` satisfies both
agreement hypotheses and returns the original normal double crossing. -/
theorem HasPLNormalDoubleCrossingAt.of_eqOn_of_isOpen_self {f : E → F} {P : Set E}
    {Bd : Set F} {y : F} (hf : ContinuousOn f P) {V : Set F} (hV : IsOpen V) (hy : y ∈ V)
    (h : HasPLNormalDoubleCrossingAt f P Bd y) : HasPLNormalDoubleCrossingAt f P Bd y :=
  h.of_eqOn_of_isOpen hf hV hy rfl fun _ _ => rfl

/-- Changing a map only over a closed set `C` which avoids the double point `y`, in such
a way that the changed part of the source is sent into `C`, preserves normal double
crossings at `y`. This is the regluing situation: `g` and `f` agree off `f ⁻¹' C`, and
`g` maps `f ⁻¹' C` into `C`. -/
theorem HasPLNormalDoubleCrossingAt.of_eqOn_sdiff_preimage_of_isClosed {f g : E → F}
    {P : Set E} {Bd C : Set F} {y : F} (hg : ContinuousOn g P) (hC : IsClosed C)
    (hy : y ∉ C) (hfg : EqOn f g (P \ f ⁻¹' C)) (hmaps : MapsTo g (P ∩ f ⁻¹' C) C)
    (h : HasPLNormalDoubleCrossingAt f P Bd y) : HasPLNormalDoubleCrossingAt g P Bd y := by
  have hdiff : P ∩ f ⁻¹' Cᶜ = P \ f ⁻¹' C := by rw [preimage_compl, Set.sdiff_eq]
  have hfg' : EqOn f g (P ∩ f ⁻¹' Cᶜ) := by rw [hdiff]; exact hfg
  have hPP' : P ∩ f ⁻¹' Cᶜ = P ∩ g ⁻¹' Cᶜ := by
    refine Subset.antisymm (fun x hx => ⟨hx.1, ?_⟩) (fun x hx => ⟨hx.1, ?_⟩)
    · rw [mem_preimage, ← hfg' hx]
      exact hx.2
    · have hgx : g x ∉ C := hx.2
      exact show f x ∉ C from fun hxC => hgx (hmaps ⟨hx.1, hxC⟩)
  exact h.of_eqOn_of_isOpen hg hC.isOpen_compl (show y ∈ Cᶜ from hy) hPP' hfg'

end DifferentialGeometry.Topology.PiecewiseLinear
