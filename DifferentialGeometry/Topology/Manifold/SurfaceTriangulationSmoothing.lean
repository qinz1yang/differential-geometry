/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.SurfaceSimplicialSkeleton
import DifferentialGeometry.Topology.Manifold.SurfaceTriangleReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial

open Set Filter Topology
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PiecewiseLinear

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N] [ChartedSpace Plane M] [ChartedSpace Plane N]
  [IsManifold 𝓘(ℝ, Plane) ∞ M] [IsManifold 𝓘(ℝ, Plane) ∞ N]

theorem exists_diffeomorph_of_planar_triangulation
    (h : M ≃ₜ N) (a : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) M Plane ∞)
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces]
    (hconv : Convex ℝ K.space) (hKa : K.space ⊆ a.target)
    (b : K.faces → PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) N Plane ∞)
    (hb : ∀ s : K.faces, h '' (a.symm '' convexHull ℝ (s.val : Set Plane)) ⊆ (b s).source)
    (hout : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h
      (a.symm '' interior K.space)ᶜ) :
    ∃ D : M ≃ₘ⟮𝓘(ℝ, Plane), 𝓘(ℝ, Plane)⟯ N, EqOn D h (a.symm '' interior K.space)ᶜ := by
  classical
  obtain ⟨L, hL, hLΩ, g, hgout, hgb, hgskel⟩ :=
    h.exists_smooth_simplicial_skeleton a K hconv hKa b hb hout
  have hgΩ : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g
      (a.symm '' interior K.space)ᶜ := by
    intro x
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := h) _ (hout x)
    filter_upwards [hL.isClosed.isOpen_compl.mem_nhds (fun hxL => x.property (hLΩ hxL))] with y hy
    exact hgout hy
  let F := {s : K.faces // s.val.card = 3}
  have hcard (i : F) : i.val.val.card = Module.finrank ℝ Plane + 1 := by
    rw [i.property, finrank_euclideanSpace_fin]
  have hbases (i : F) : ∃ t : AffineBasis (Fin 3) ℝ Plane, range t = (i.val.val : Set Plane) := by
    have htop : affineSpan ℝ (range ((↑) : i.val.val → Plane)) = ⊤ :=
      (K.indep i.val.property).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
        (by simpa only [Fintype.card_coe] using hcard i)
    let t : AffineBasis i.val.val ℝ Plane := ⟨Subtype.val, K.indep i.val.property, htop⟩
    let e : i.val.val ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using i.property)
    refine ⟨t.reindex e, ?_⟩
    change range (fun j => ((e.symm j : i.val.val) : Plane)) = (i.val.val : Set Plane)
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact (e.symm j).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩
  choose t ht using hbases
  have hta (i : F) : convexHull ℝ (range (t i)) ⊆ a.target := by
    rw [ht]
    exact (K.convexHull_subset_space i.val.property).trans hKa
  have htb (i : F) : g '' (a.symm '' convexHull ℝ (range (t i))) ⊆ (b i.val).source := by
    rw [ht]
    exact hgb i.val
  have hdis : Pairwise fun i j : F => Disjoint
      (interior (convexHull ℝ (range (t i)))) (interior (convexHull ℝ (range (t j)))) := by
    intro i j hij
    rw [ht, ht, interior_convexHull_eq_openSimplex (K.indep i.val.property) (hcard i),
      interior_convexHull_eq_openSimplex (K.indep j.val.property) (hcard j)]
    exact disjoint_left.mpr fun x hxi hxj => hij (Subtype.ext (Subtype.ext
      (face_eq_of_mem_openSimplex K i.val.property j.val.property hxi hxj)))
  let U := {x | IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g x}
  have hU : IsOpen U := isOpen_setOf_isLocalDiffeomorphAt _ _ _ _
  have hbd (i : F) : a.symm '' frontier (convexHull ℝ (range (t i))) ⊆ U := by
    rw [ht, frontier_convexHull_eq_simplexBoundary (K.indep i.val.property) (hcard i)]
    rintro x ⟨v, hv, rfl⟩
    obtain ⟨s, hs, hvs⟩ := (simplexBoundary i.val.val (K.indep i.val.property)).mem_space_iff.mp hv
    have hsK : s ∈ K.faces := K.down_closed i.val.property hs.1 hs.2.1
    have hlt : s.card < i.val.val.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs.1, hs.2.2⟩)
    have hs2 : s.card ≤ 2 := by rw [i.property] at hlt; omega
    exact hgskel s hsK hs2 ⟨_, v, hvs, rfl⟩
  have houtfaces : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g
      (⋃ i : F, a.symm '' convexHull ℝ (range (t i)))ᶜ := by
    intro x
    by_cases hxΩ : (x : M) ∈ a.symm '' interior K.space
    · obtain ⟨v, hv, hvx⟩ := hxΩ
      obtain ⟨s, hs, hvs⟩ := K.mem_space_iff.mp (interior_subset hv)
      have hle : s.card ≤ 3 := by
        simpa only [finrank_euclideanSpace_fin] using card_le_finrank_succ_of_mem_faces K hs
      by_cases hs3 : s.card = 3
      · let i : F := ⟨⟨s, hs⟩, hs3⟩
        apply False.elim (x.property (mem_iUnion.mpr ⟨i, v, ?_, hvx⟩))
        rw [ht]
        exact hvs
      · exact hgskel s hs (by omega) ⟨x, v, hvs, hvx⟩
    · exact hgΩ ⟨x, hxΩ⟩
  obtain ⟨D, hD⟩ := g.exists_diffeomorph_of_smooth_triangle_boundaries a
    (fun i : F => b i.val) t hta htb hdis hU (fun x => x.property) hbd houtfaces
  refine ⟨D, fun x hx => (hD ?_).trans (hgout (fun hxL => hx (hLΩ hxL)))⟩
  intro hxfaces
  obtain ⟨i, v, hv, hvx⟩ := mem_iUnion.mp hxfaces
  rw [ht] at hv
  exact hx ⟨v, interior_mono (K.convexHull_subset_space i.val.property) hv, hvx⟩

end Homeomorph
