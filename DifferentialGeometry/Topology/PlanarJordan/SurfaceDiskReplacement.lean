/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.PartialBoundaryGermExtension
import DifferentialGeometry.Topology.Manifold.RelativeDiffeomorphPasting

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies (Plane)

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
  [ChartedSpace H M] [ChartedSpace G N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}

theorem exists_homeomorph_smoothing_disk_in_charts
    (h : M ≃ₜ N)
    (a : PartialDiffeomorph I 𝓘(ℝ, Plane) M Plane ∞)
    (b : PartialDiffeomorph J 𝓘(ℝ, Plane) N Plane ∞)
    {K : Set M} (hK : IsCompact K) (hKa : K ⊆ a.source) (hKb : h '' K ⊆ b.source)
    {γ : AddCircle (1 : ℝ) → Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ γ)
    (hcoord : a '' K = closure (Schoenflies.inside (range γ)))
    {U : Set M} (hU : IsOpen U) (hfrontier : frontier K ⊆ U)
    (hlocal : IsLocalDiffeomorphOn I J ∞ h U) :
    ∃ g : M ≃ₜ N,
      EqOn g h (interior K)ᶜ ∧ g '' K = h '' K ∧
      (∀ x, IsLocalDiffeomorphAt I J ∞ h x → IsLocalDiffeomorphAt I J ∞ g x) ∧
      ∃ V : Set M, IsOpen V ∧ frontier K ⊆ V ∧ V ⊆ U ∧ EqOn g h V ∧
        ∃ W : Set M, IsOpen W ∧ K ⊆ W ∧ W ⊆ a.source ∧
          g '' W ⊆ b.source ∧ IsLocalDiffeomorphOn I J ∞ g W := by
  have ha {x : M} (hx : x ∈ a.source) : a.symm (a x) = x := a.left_inv hx
  have hb {y : N} (hy : y ∈ b.source) : b.symm (b y) = y := b.left_inv hy
  let e := (a.symm.toOpenPartialHomeomorph.trans h.toOpenPartialHomeomorph).trans
    b.toOpenPartialHomeomorph
  have he (z : Plane) : e z = b (h (a.symm z)) := rfl
  have hCsource : closure (Schoenflies.inside (range γ)) ⊆ e.source := by
    rw [← hcoord]
    rintro z ⟨x, hx, rfl⟩
    change ((a x ∈ a.target ∧ True) ∧ h (a.symm (a x)) ∈ b.source)
    refine ⟨⟨a.map_source (hKa hx), trivial⟩, ?_⟩
    rw [ha (hKa hx)]
    exact hKb (mem_image_of_mem h hx)
  have hfr : a '' frontier K = range γ := by
    calc
      a '' frontier K = frontier (a '' K) :=
        a.toOpenPartialHomeomorph.image_frontier_of_isCompact hK hKa
      _ = range γ := by
        rw [hcoord]
        exact frontier_closure_inside
          (isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero hγ.isEmbedding)
  let O := e.source ∩ (a.target ∩ a.symm ⁻¹' U)
  have hO : IsOpen O := e.open_source.inter
    (a.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hU)
  have hγO : range γ ⊆ O := by
    rw [← hfr]
    rintro z ⟨x, hx, rfl⟩
    have hxa := hKa (hK.isClosed.frontier_subset hx)
    refine ⟨hCsource (hcoord ▸ mem_image_of_mem a (hK.isClosed.frontier_subset hx)),
      a.map_source hxa, ?_⟩
    change a.symm (a x) ∈ U
    rw [ha hxa]
    exact hfrontier hx
  have hlocalO : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ e O := by
    rintro ⟨z, hz⟩
    obtain ⟨d, hzd, hd⟩ := hlocal ⟨a.symm z, hz.2.2⟩
    let c := (a.symm.trans d).trans b
    have hzbs : h (a.symm z) ∈ b.source := hz.1.2
    refine ⟨c, ⟨⟨hz.2.1, hzd⟩, ?_⟩, ?_⟩
    · change d (a.symm z) ∈ b.source
      rw [← hd hzd]
      exact hzbs
    · intro y hy
      change b (h (a.symm y)) = b (d (a.symm y))
      exact congrArg b (hd hy.1.2)
  obtain ⟨Q, hQimage, A, hA, hγA, hAO, hQA⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_localDiffeomorphOn e hγ hCsource
      hO hγO inter_subset_left hlocalO
  have heimage : e '' (a '' K) = b '' (h '' K) := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      rw [he, ha (hKa hx)]
      exact mem_image_of_mem b (mem_image_of_mem h hx)
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨a x, mem_image_of_mem a hx, ?_⟩
      rw [he, ha (hKa hx)]
  have hQK : Q '' (a '' K) = b '' (h '' K) := by
    rw [hcoord, hQimage, ← hcoord, heimage]
  let φ := (a.trans Q.toPartialDiffeomorph).trans b.symm
  have hφsource : K ⊆ φ.source := by
    intro x hx
    refine ⟨⟨hKa hx, mem_univ _⟩, ?_⟩
    have hq : Q (a x) ∈ b '' (h '' K) := hQK.subset
      (mem_image_of_mem Q (mem_image_of_mem a hx))
    obtain ⟨y, hy, hyq⟩ := hq
    change Q (a x) ∈ b.target
    rw [← hyq]
    exact b.map_source (hKb hy)
  have hφimage : φ '' K = h '' K := by
    have hcomp : φ '' K = b.symm '' (Q '' (a '' K)) := by
      rw [image_image, image_image]
      rfl
    rw [hcomp, hQK]
    apply Subset.antisymm
    · rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hb (hKb hx)]
    · intro x hx
      exact ⟨b x, mem_image_of_mem b hx, hb (hKb hx)⟩
  let V := a.source ∩ a ⁻¹' A
  have hV : IsOpen V := a.toOpenPartialHomeomorph.isOpen_inter_preimage hA
  have hKV : frontier K ⊆ V := by
    intro x hx
    exact ⟨hKa (hK.isClosed.frontier_subset hx), hγA (hfr.subset (mem_image_of_mem a hx))⟩
  have hVU : V ⊆ U := by
    intro x hx
    have h := (hAO hx.2).2.2
    change a.symm (a x) ∈ U at h
    rwa [ha hx.1] at h
  have hφh : EqOn φ h V := by
    intro x hx
    change b.symm (Q (a x)) = h x
    rw [hQA hx.2, he, ha hx.1]
    apply hb
    have hbs := (hAO hx.2).1.2
    change h (a.symm (a x)) ∈ b.source at hbs
    simpa only [ha hx.1] using hbs
  obtain ⟨g, -, hgout, hgV, hgK, hgpreserve, W, hW, hKW, hWs, hgW, hlocalW⟩ :=
    h.exists_pasting_of_partialDiffeomorph φ hK.isClosed hφsource hφimage hV hKV hφh
  refine ⟨g, hgout, hgK, hgpreserve, V, hV, hKV, hVU, hgV,
    W, hW, hKW, fun x hx => (hWs hx).1.1, ?_, hlocalW⟩
  rintro y ⟨x, hx, rfl⟩
  rw [hgW hx]
  exact (φ.map_source (hWs hx)).1

end DifferentialGeometry.Topology.PlanarJordan
