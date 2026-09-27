/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.SurfacePointSmoothingMapsTo
import DifferentialGeometry.Topology.Manifold.SurfaceSegmentFamilySmoothing
import DifferentialGeometry.Topology.PlanarJordan.SegmentCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialFaceSeparation
import DifferentialGeometry.Analysis.Convex.SegmentInterior

open Set Filter Topology
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PiecewiseLinear
open DifferentialGeometry.Topology.PlanarJordan

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N] [ChartedSpace Plane M] [ChartedSpace Plane N]
  [IsManifold 𝓘(ℝ, Plane) ∞ M] [IsManifold 𝓘(ℝ, Plane) ∞ N]

theorem exists_smooth_simplicial_skeleton
    (h : M ≃ₜ N) (a : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) M Plane ∞)
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces]
    (hconv : Convex ℝ K.space) (hKa : K.space ⊆ a.target)
    (b : K.faces → PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) N Plane ∞)
    (hb : ∀ s : K.faces, h '' (a.symm '' convexHull ℝ (s.val : Set Plane)) ⊆ (b s).source)
    (hout : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h
      (a.symm '' interior K.space)ᶜ) :
    ∃ L : Set M, IsCompact L ∧ L ⊆ a.symm '' interior K.space ∧ ∃ g : M ≃ₜ N,
      EqOn g h Lᶜ ∧
      (∀ s : K.faces, g '' (a.symm '' convexHull ℝ (s.val : Set Plane)) ⊆ (b s).source) ∧
      (∀ s ∈ K.faces, s.card ≤ 2 → IsLocalDiffeomorphOn
        𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g (a.symm '' convexHull ℝ (s : Set Plane))) := by
  classical
  let Ω := a.symm '' interior K.space
  have hΩ : IsOpen Ω := a.symm.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    isOpen_interior (interior_subset.trans hKa)
  let C (s : K.faces) := a.symm '' convexHull ℝ (s.val : Set Plane)
  have hC (s : K.faces) : IsCompact (C s) :=
    (s.val.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (a.symm.toOpenPartialHomeomorph.continuousOn.mono
        ((K.convexHull_subset_space s.property).trans hKa))
  let P := a.symm '' K.vertices
  have hPfin : P.Finite := by
    apply Set.Finite.image
    rw [K.vertices_eq]
    exact (Set.toFinite K.faces).biUnion fun s _ => s.finite_toSet
  let T := (hPfin.inter_of_left Ω).toFinset
  obtain ⟨L₀, hL₀, hL₀Ω, g₀, hg₀out, -, hg₀T, hg₀map⟩ :=
    h.exists_smooth_on_finset_preserving_mapsTo C (fun s => (b s).source)
      (fun s => (hC s).isClosed) (fun s => (b s).open_source)
      (fun s => mapsTo_iff_image_subset.mpr (hb s)) T hΩ (by
        simp only [T, Set.Finite.coe_toFinset]
        exact inter_subset_right)
  have hg₀ext {x : M} (hx : x ∉ L₀)
      (hh : IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h x) :
      IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g₀ x := by
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := h) _ hh
    filter_upwards [hL₀.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hg₀out hy
  have hg₀P : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g₀ P := by
    intro x
    by_cases hxΩ : (x : M) ∈ Ω
    · exact hg₀T ⟨x, (hPfin.inter_of_left Ω).mem_toFinset.mpr ⟨x.property, hxΩ⟩⟩
    · exact hg₀ext (fun hxL => hxΩ (hL₀Ω hxL)) (hout ⟨x, hxΩ⟩)
  let E := {s : K.faces // s.val.card = 2 ∧ openSimplex s.val ⊆ interior K.space}
  have hpairs (i : E) : ∃ p q : Plane, p ≠ q ∧ i.val.val = {p, q} :=
    Finset.card_eq_two.mp i.property.1
  choose p q hpq hpqs using hpairs
  choose D hD using fun i => exists_diffeomorph_lineMap (hpq i)
  let A (i : E) := (D i).toPartialDiffeomorph.trans a.symm
  let σ : ℝ → Plane := fun t => Plane.mk t 0
  have hA (i : E) (t : ℝ) : A i (σ t) = a.symm (AffineMap.lineMap (p i) (q i) t) := by
    change a.symm (D i (Plane.mk t 0)) = _
    rw [hD]
  have hseg (i : E) : convexHull ℝ (i.val.val : Set Plane) =
      AffineMap.lineMap (p i) (q i) '' Icc (0 : ℝ) 1 := by
    rw [hpqs i]
    simp only [Finset.coe_pair, convexHull_pair, segment_eq_image_lineMap]
  have hopen (i : E) : openSimplex i.val.val =
      AffineMap.lineMap (p i) (q i) '' Ioo (0 : ℝ) 1 := by
    rw [hpqs i]
    exact (openSimplex_pair_eq_openSegment (hpq i)).trans
      (openSegment_eq_image_lineMap ℝ (p i) (q i))
  have hAS (i : E) : A i '' (σ '' Icc (0 : ℝ) 1) = C i.val := by
    rw [image_image, show C i.val = a.symm '' convexHull ℝ (i.val.val : Set Plane) from rfl,
      hseg, image_image]
    exact image_congr fun t _ => hA i t
  have hAO (i : E) : A i '' (σ '' Ioo (0 : ℝ) 1) = a.symm '' openSimplex i.val.val := by
    rw [image_image, hopen, image_image]
    exact image_congr fun t _ => hA i t
  have hhas (i : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : σ t ∈ (A i).source := by
    refine ⟨trivial, ?_⟩
    change D i (σ t) ∈ a.target
    rw [hD]
    apply hKa (K.convexHull_subset_space i.val.property _)
    rw [hseg]
    exact mem_image_of_mem _ ht
  have hmem (i : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : A i (σ t) ∈ C i.val :=
    hAS i ▸ mem_image_of_mem (A i) (mem_image_of_mem σ ht)
  have hdisimage {s t : Set Plane} (hs : s ⊆ a.target) (ht : t ⊆ a.target)
      (hd : Disjoint s t) : Disjoint (a.symm '' s) (a.symm '' t) := by
    apply disjoint_left.mpr
    rintro x ⟨v, hv, hvx⟩ ⟨w, hw, hwx⟩
    have hvw := a.symm.toOpenPartialHomeomorph.injOn (hs hv) (ht hw) (hvx.trans hwx.symm)
    exact disjoint_left.mp hd hv (hvw.symm ▸ hw)
  have hinc (i : E) (s : K.faces) : A i '' (σ '' Icc (0 : ℝ) 1) ⊆ C s ∨
      Disjoint (A i '' (σ '' Ioo (0 : ℝ) 1)) (C s) := by
    rw [hAS, hAO]
    rcases convexHull_subset_or_disjoint_openSimplex K i.val.property s.property with hc | hd
    · exact Or.inl (image_mono hc)
    · exact Or.inr (hdisimage
        ((openSimplex_subset_convexHull _).trans
        ((K.convexHull_subset_space i.val.property).trans hKa))
        ((K.convexHull_subset_space s.property).trans hKa) hd)
  have hdis : Pairwise fun i j : E =>
      Disjoint (A i '' (σ '' Ioo (0 : ℝ) 1)) (A j '' (σ '' Icc (0 : ℝ) 1)) := by
    intro i j hij
    rw [hAO, hAS]
    exact hdisimage
      ((openSimplex_subset_convexHull _).trans
        ((K.convexHull_subset_space i.val.property).trans hKa))
      ((K.convexHull_subset_space j.val.property).trans hKa)
      (disjoint_openSimplex_convexHull_of_card_eq K i.val.property j.val.property
        (i.property.1.trans j.property.1.symm)
        (fun heq => hij (Subtype.ext (Subtype.ext heq))))
  have hends (i : E) : A i (σ 0) ∈ P ∧ A i (σ 1) ∈ P := by
    have hp : p i ∈ K.vertices := K.down_closed i.val.property
      (Finset.singleton_subset_iff.mpr (by rw [hpqs]; simp)) (by simp)
    have hq : q i ∈ K.vertices := K.down_closed i.val.property
      (Finset.singleton_subset_iff.mpr (by rw [hpqs]; simp)) (by simp)
    simpa only [hA, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
      And.intro (mem_image_of_mem a.symm hp) (mem_image_of_mem a.symm hq)
  have hAΩ (i : E) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : A i (σ t) ∈ Ω \ P := by
    have hx : A i (σ t) ∈ a.symm '' openSimplex i.val.val :=
      hAO i ▸ mem_image_of_mem (A i) (mem_image_of_mem σ ht)
    refine ⟨image_mono i.property.2 hx, ?_⟩
    exact fun hxp => disjoint_left.mp (hdisimage
      ((openSimplex_subset_convexHull _).trans
        ((K.convexHull_subset_space i.val.property).trans hKa))
      (K.vertices_subset_space.trans hKa)
      (disjoint_openSimplex_vertices_of_one_lt_card K i.val.property
        (by rw [i.property.1]; norm_num)))
      hx hxp
  obtain ⟨L₁, hL₁, hL₁Ω, g, hgout, hgmap, hgseg⟩ :=
    g₀.exists_smooth_finite_segments_preserving_mapsTo A (fun i => b i.val) hhas
      (fun i t ht => hg₀map i.val (hmem i t ht)) C (fun s => (b s).source)
      (fun s => (hC s).isClosed) (fun s => (b s).open_source) hg₀map hinc hdis
      hPfin.isClosed hΩ hg₀P (fun i => (hends i).1) (fun i => (hends i).2) hAΩ
  have hgext {x : M} (hx : x ∉ L₁)
      (hh : IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g₀ x) :
      IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g x := by
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := g₀) _ hh
    filter_upwards [hL₁.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hgout hy
  have hgP : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g P :=
    fun x => hgext (fun hxL => (hL₁Ω hxL).2 x.property) (hg₀P x)
  have hgΩ : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g Ωᶜ := fun x =>
    hgext (fun hxL => x.property (hL₁Ω hxL).1)
      (hg₀ext (fun hxL => x.property (hL₀Ω hxL)) (hout x))
  refine ⟨L₀ ∪ L₁, hL₀.union hL₁,
    union_subset hL₀Ω (hL₁Ω.trans sdiff_subset), g, ?_,
    fun s => mapsTo_iff_image_subset.mp (hgmap s), ?_⟩
  · intro x hx
    exact (hgout (fun hxL => hx (Or.inr hxL))).trans
      (hg₀out (fun hxL => hx (Or.inl hxL)))
  · intro s hs hcard x
    obtain ⟨v, hv, hvx⟩ := x.property
    have hpos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
    by_cases hs1 : s.card = 1
    · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hs1
      have hvp : v = p := by simpa using hv
      subst v
      exact hgP ⟨x, hvx ▸ mem_image_of_mem a.symm hs⟩
    · have hs2 : s.card = 2 := by omega
      obtain ⟨p, q, hpq, hspq⟩ := Finset.card_eq_two.mp hs2
      have hopen' : openSimplex s = openSegment ℝ p q := by
        rw [hspq]
        exact openSimplex_pair_eq_openSegment hpq
      have hpK : p ∈ K.space := K.subset_space hs (by rw [hspq]; simp)
      have hqK : q ∈ K.space := K.subset_space hs (by rw [hspq]; simp)
      rcases hconv.openSegment_subset_interior_or_disjoint hpK hqK with hinside | houtside
      · let i : E := ⟨⟨s, hs⟩, hs2, hopen' ▸ hinside⟩
        have hxS : (x : M) ∈ A i '' (σ '' Icc (0 : ℝ) 1) := (hAS i).symm ▸ x.property
        obtain ⟨_, ⟨t, ht, rfl⟩, htx⟩ := hxS
        exact htx ▸ hgseg i t ht
      · by_cases hvopen : v ∈ openSimplex s
        · have hxout : (x : M) ∉ Ω := by
            rintro ⟨w, hw, hwx⟩
            have hvw := a.symm.toOpenPartialHomeomorph.injOn
              (hKa (K.convexHull_subset_space hs hv)) (hKa (interior_subset hw))
              (hvx.trans hwx.symm)
            exact disjoint_left.mp houtside (hopen' ▸ hvopen) (hvw.symm ▸ hw)
          exact hgΩ ⟨x, hxout⟩
        · have hvseg : v ∈ segment ℝ p q := by
            simpa only [hspq, Finset.coe_pair, convexHull_pair] using hv
          have hvnot : v ∉ openSegment ℝ p q := hopen' ▸ hvopen
          have hvpq : v = p ∨ v = q := by
            rw [← insert_endpoints_openSegment] at hvseg
            simpa only [mem_insert_iff, hvnot, or_false] using hvseg
          have hvvertex : v ∈ K.vertices := by
            apply K.down_closed hs
            · apply Finset.singleton_subset_iff.mpr
              rcases hvpq with rfl | rfl <;> rw [hspq] <;> simp
            · simp
          exact hgP ⟨x, hvx ▸ mem_image_of_mem a.symm hvvertex⟩

end Homeomorph
