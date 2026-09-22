/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Groupoid
import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineSimplicial
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph

/-!
Simplicial subdivision on chart overlap where the transition map is face-affine.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_transitionSubdivisionOnOverlap
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (ec ec' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) (hec' : ec' ∈ (plGroupoid 3).maximalAtlas M)
    (N : Set M) (hN : IsCompact N) (hNec : N ⊆ ec.source) (hNec' : N ⊆ ec'.source) :
    ∃ Q : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      Q.faces.Finite ∧ ⇑ec '' N ⊆ interior Q.space ∧
        Q.space ⊆ ⇑ec '' (ec.source ∩ ec'.source) ∧
        ∀ s ∈ Q.faces, ∃ A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
          EqOn (fun z => ec' (ec.symm z)) A
            (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))) := by
  let W := ec.source ∩ ec'.source
  have hWopen : IsOpen W := ec.open_source.inter ec'.open_source
  have hNW : N ⊆ W := subset_inter hNec hNec'
  have hUopen : IsOpen (ec '' W) := ec.isOpen_image_of_subset_source hWopen inter_subset_left
  have hCcomp : IsCompact (ec '' N) := hN.image_of_continuousOn (ec.continuousOn.mono hNec)
  have hCU : ec '' N ⊆ ec '' W := fun _ ⟨x, hx, heq⟩ => ⟨x, hNW hx, heq⟩
  obtain ⟨P, hPpoly, hCP, hPU⟩ := exists_isPolyhedron_neighborhood hCcomp hUopen hCU
  obtain ⟨K, hKfin, hKspace⟩ := hPpoly.exists_simplicialComplex
  have _ : Finite K.faces := hKfin.to_subtype
  have htrans : ec.symm.trans ec' ∈ plGroupoid 3 :=
    StructureGroupoid.compatible_of_mem_maximalAtlas hec hec'
  have htrans_pa : IsPiecewiseAffineOn (ec.symm.trans ec') (ec.symm.trans ec').source :=
    (mem_plGroupoid_iff.mp htrans).1
  have htrans_src : (ec.symm.trans ec').source = ec '' W := by
    ext z
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hz_target, hz_source⟩
      exact ⟨ec.symm z, ⟨ec.map_target hz_target, hz_source⟩, ec.right_inv hz_target⟩
    · rintro ⟨x, ⟨hx_ec, hx_ec'⟩, rfl⟩
      exact ⟨ec.map_source hx_ec, by simpa only [ec.left_inv hx_ec] using hx_ec'⟩
  have htrans_pa' : IsPiecewiseAffineOn (ec.symm.trans ec') (ec '' W) :=
    htrans_src ▸ htrans_pa
  have hf_pa : IsPiecewiseAffineOn (fun z => ec' (ec.symm z)) (ec '' W) :=
    htrans_pa'.congr (fun z _ => (OpenPartialHomeomorph.trans_apply ec.symm ec').symm)
  have hKU : K.space ⊆ ec '' W := hKspace.symm ▸ hPU
  have hfK : IsPiecewiseAffineOn (fun z => ec' (ec.symm z)) K.space :=
    hf_pa.mono_of_isPolyhedron (isPolyhedron_space K) hKU
  obtain ⟨Q, hQsub, hQfin, haff⟩ := hfK.exists_isSubdivision_affineOn_faces K
  refine ⟨Q, hQfin, ?_, ?_, haff⟩
  · rw [hQsub.space_eq, hKspace]
    exact hCP
  · rw [hQsub.space_eq, hKspace]
    exact hPU

end DifferentialGeometry.Topology.PiecewiseLinear
