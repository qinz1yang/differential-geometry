/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Planar.TriangleSmoothCore
import DifferentialGeometry.Topology.PlanarJordan.FiniteDiskReplacement

open Set
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PlanarJordan

variable {E F H G M N ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [ChartedSpace H M] [ChartedSpace G N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}

theorem exists_diffeomorph_of_smooth_triangle_boundaries [Finite ι]
    (h : M ≃ₜ N) (a : PartialDiffeomorph I 𝓘(ℝ, Plane) M Plane ∞)
    (b : ι → PartialDiffeomorph J 𝓘(ℝ, Plane) N Plane ∞)
    (t : ι → AffineBasis (Fin 3) ℝ Plane)
    (hta : ∀ i, convexHull ℝ (range (t i)) ⊆ a.target)
    (htb : ∀ i, h '' (a.symm '' convexHull ℝ (range (t i))) ⊆ (b i).source)
    (hdisjoint : Pairwise fun i j => Disjoint
      (interior (convexHull ℝ (range (t i)))) (interior (convexHull ℝ (range (t j)))))
    {U : Set M} (hU : IsOpen U) (hlocal : IsLocalDiffeomorphOn I J ∞ h U)
    (hboundary : ∀ i, a.symm '' frontier (convexHull ℝ (range (t i))) ⊆ U)
    (houtside : IsLocalDiffeomorphOn I J ∞ h
      (⋃ i, a.symm '' convexHull ℝ (range (t i)))ᶜ) :
    ∃ D : Diffeomorph I J M N ∞,
      EqOn D h (⋃ i, a.symm '' interior (convexHull ℝ (range (t i))))ᶜ := by
  classical
  let C (i : ι) := convexHull ℝ (range (t i))
  have hC (i : ι) : IsCompact (C i) := (finite_range (t i)).isCompact_convexHull ℝ
  let W := a.target ∩ a.symm ⁻¹' U
  have hW : IsOpen W := a.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hU
  have hCW (i : ι) : frontier (C i) ⊆ W := fun x hx =>
    ⟨hta i ((hC i).isClosed.frontier_subset hx), hboundary i ⟨x, hx, rfl⟩⟩
  have hcores (i : ι) :=
    DifferentialGeometry.Topology.Planar.exists_smooth_jordan_core_triangle (t i) hW (hCW i)
  choose γ hγ hQsub hrest using hcores
  let Q (i : ι) := closure (Schoenflies.inside (range (γ i)))
  let K (i : ι) := a.symm '' Q i
  have hQt (i : ι) : Q i ⊆ a.target := (hQsub i).trans (interior_subset.trans (hta i))
  have hQ (i : ι) : IsCompact (Q i) :=
    (hC i).of_isClosed_subset isClosed_closure ((hQsub i).trans interior_subset)
  have hK (i : ι) : IsCompact (K i) := (hQ i).image_of_continuousOn
    (a.symm.toOpenPartialHomeomorph.continuousOn.mono (hQt i))
  have hKa (i : ι) : K i ⊆ a.source := by
    rintro _ ⟨x, hx, rfl⟩
    exact a.map_target (hQt i hx)
  have hKCi (i : ι) : K i ⊆ a.symm '' interior (C i) := image_mono (hQsub i)
  have hKC (i : ι) : K i ⊆ a.symm '' C i := (hKCi i).trans (image_mono interior_subset)
  have hKb (i : ι) : h '' K i ⊆ (b i).source := (image_mono (hKC i)).trans (htb i)
  have haright (v : Plane) (hv : v ∈ a.target) : a (a.symm v) = v := a.right_inv hv
  have hcoord (i : ι) : a '' K i = Q i := by
    ext z
    constructor
    · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
      rw [haright v (hQt i hv)]
      exact hv
    · intro hz
      exact ⟨a.symm z, ⟨z, hz, rfl⟩, haright z (hQt i hz)⟩
  have hdis : Pairwise fun i j => Disjoint (K i) (K j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨v, hv, hvx⟩ ⟨w, hw, hwx⟩
    have hvw : v = w := a.symm.toOpenPartialHomeomorph.injOn
      (hQt i hv) (hQt j hw) (hvx.trans hwx.symm)
    exact disjoint_left.mp (hdisjoint hij) (hQsub i hv) (hvw.symm ▸ hQsub j hw)
  have hJ (i : ι) : Schoenflies.IsJordanCurve (range (γ i)) :=
    isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero (hγ i).isEmbedding
  have hfront (i : ι) : frontier (K i) = a.symm '' range (γ i) := by
    change frontier (a.symm.toOpenPartialHomeomorph '' Q i) =
      a.symm.toOpenPartialHomeomorph '' range (γ i)
    rw [← a.symm.toOpenPartialHomeomorph.image_frontier_of_isCompact (hQ i) (hQt i)]
    rw [show frontier (Q i) = range (γ i) from frontier_closure_inside (hJ i)]
  have hγQ (i : ι) : range (γ i) ⊆ Q i := by
    rw [← frontier_closure_inside (hJ i)]
    exact isClosed_closure.frontier_subset
  have hKU (i : ι) : frontier (K i) ⊆ U := by
    rw [hfront i]
    rintro _ ⟨v, hv, rfl⟩
    have hvC : v ∈ C i := interior_subset (hQsub i (hγQ i hv))
    exact (hrest i ⟨hvC, fun hvIn => Schoenflies.inside_subset_compl hvIn hv⟩).2
  have houtK : IsLocalDiffeomorphOn I J ∞ h (⋃ i, K i)ᶜ := by
    intro x
    by_cases hx : (x : M) ∈ ⋃ i, a.symm '' C i
    · obtain ⟨i, v, hvC, hvx⟩ := mem_iUnion.mp hx
      have hvIn : v ∉ Schoenflies.inside (range (γ i)) := by
        intro hvIn
        exact x.property (mem_iUnion.mpr ⟨i, v, subset_closure hvIn, hvx⟩)
      exact hlocal ⟨x, hvx ▸ (hrest i ⟨hvC, hvIn⟩).2⟩
    · exact houtside ⟨x, hx⟩
  obtain ⟨D, hD, -⟩ := exists_diffeomorph_eqOn_compl_finite_disjoint_disks h
    (fun _ => a) b K hK hdis hKa hKb γ hγ hcoord (fun _ => U)
    (fun _ => hU) hKU (fun _ => hlocal) houtK
  refine ⟨D, fun x hx => hD ?_⟩
  intro hxK
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxK
  exact hx (mem_iUnion.mpr ⟨i, hKCi i (interior_subset hi)⟩)

end Homeomorph
