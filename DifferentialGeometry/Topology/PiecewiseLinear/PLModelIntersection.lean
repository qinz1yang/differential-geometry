/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelCellRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.ChartPolyhedron

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
private theorem compact_polyhedron_of_local_polyhedra {Q : Set E3} (hQ : IsCompact Q)
    (hlocal : ∀ x ∈ Q, ∃ P : Set E3, IsPolyhedron P ∧ Q =ᶠ[𝓝 x] P) :
    IsPolyhedron Q := by
  choose P hP hQP using fun x : Q => hlocal x x.property
  choose C hC hCsub hCnhds using fun x : Q =>
    exists_isHPolytope_subset_mem_nhds (hQP x)
  have hcover : Q ⊆ ⋃ x : Q, interior (C x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hCnhds ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover (fun x : Q => interior (C x))
    (fun _ => isOpen_interior) hcover
  have heq : Q = ⋃ x : t, P x ∩ C x := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x, hxt, hyC⟩ := mem_iUnion₂.mp (ht hy)
      exact mem_iUnion.mpr ⟨⟨x, hxt⟩,
        (hCsub x (interior_subset hyC)).mp hy, interior_subset hyC⟩
    · refine iUnion_subset fun x => ?_
      rintro y ⟨hyP, hyC⟩
      exact (hCsub x hyC).mpr hyP
  rw [heq]
  exact IsPolyhedron.iUnion fun x : t => (hP x).inter (hC x).isPolyhedron

open Classical in
theorem IsPLHomeomorphInto.isPolyhedron_inter_preimage_image
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    {v f : E3 → M} {Q S : Set E3} (hv : IsPLHomeomorphInto 3 v Q)
    (hf : IsPLOn 3 3 f S) (hcompact : IsCompact (S ∩ f ⁻¹' (v '' Q))) :
    IsPolyhedron (S ∩ f ⁻¹' (v '' Q)) := by
  apply compact_polyhedron_of_local_polyhedra hcompact
  intro x hx
  let e := chartAt E3 (f x)
  have hfx : f x ∈ e.source := mem_chart_source _ _
  have hInv := hv.isPLOn_inverse hv.injOn.leftInvOn_invFunOn (f x) hx.2
  change ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty 3 3)
    (Function.invFunOn v Q) (v '' Q) (f x) at hInv
  rw [StructureGroupoid.liftPropWithinAt_self_target] at hInv
  obtain ⟨-, ι, hι, C, A, hC, hCnhds⟩ := hInv
  let _ := hι
  let R : Set E3 := ⋃ i, C i
  have hR : IsPolyhedron R := ⟨ι, hι, C, fun i => (hC i).1, rfl⟩
  have hRsub : R ⊆ e.symm ⁻¹' (v '' Q) := iUnion_subset fun i => (hC i).2.1
  obtain ⟨V, hV, hxV, hVR⟩ := mem_nhdsWithin.mp hCnhds
  have hcoord := (hf x hx.1).prop
  change IsPiecewiseAffineWithinAt (e ∘ f) S x at hcoord
  obtain ⟨κ, hκ, D, B, hD, hDnhds⟩ := hcoord
  let _ := hκ
  let P : Set E3 := ⋃ i, D i ∩ B i ⁻¹' R
  have hP : IsPolyhedron P := IsPolyhedron.iUnion fun i =>
    (hD i).1.isPolyhedron.inter_preimage hR (B i)
  refine ⟨P, hP, ?_⟩
  have hsource : f ⁻¹' e.source ∈ 𝓝[S] x :=
    (hf x hx.1).continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_source.mem_nhds hfx)
  have htarget : (e ∘ f) ⁻¹' V ∈ 𝓝[S] x :=
    (hf x hx.1).prop.continuousWithinAt.preimage_mem_nhdsWithin (hV.mem_nhds hxV)
  have hgood : (⋃ i, D i) ∩ f ⁻¹' e.source ∩ (e ∘ f) ⁻¹' V ∈ 𝓝[S] x :=
    Filter.inter_mem (Filter.inter_mem hDnhds hsource) htarget
  obtain ⟨O, hO, hOsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hgood
  filter_upwards [hO] with z hzO
  apply propext
  constructor
  · rintro ⟨hzS, hzQ⟩
    have hzgood := hOsub ⟨hzO, hzS⟩
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hzgood.1.1
    have heq : B i z = e (f z) := ((hD i).2.2 hzi).symm
    refine mem_iUnion.mpr ⟨i, hzi, ?_⟩
    change B i z ∈ R
    rw [heq]
    apply hVR ⟨hzgood.2, ?_⟩
    change e.symm (e (f z)) ∈ v '' Q
    simpa only [mem_preimage, e.left_inv hzgood.1.2] using hzQ
  · intro hzP
    obtain ⟨i, hzi, hzBi⟩ := mem_iUnion.mp hzP
    have hzS : z ∈ S := (hD i).2.1 hzi
    have hzgood := hOsub ⟨hzO, hzS⟩
    have heq : B i z = e (f z) := ((hD i).2.2 hzi).symm
    have hzR : e (f z) ∈ R := heq ▸ hzBi
    refine ⟨hzS, ?_⟩
    simpa only [mem_preimage, e.left_inv hzgood.1.2] using hRsub hzR

theorem IsPLHomeomorphInto.mono_of_polyhedron
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {u : E3 → M} {P Q : Set E3} (hu : IsPLHomeomorphInto 3 u P)
    (hQ : IsPolyhedron Q) (hQP : Q ⊆ P) : IsPLHomeomorphInto 3 u Q :=
  (hu.isPLOn.mono_of_isPolyhedron hQ hQP).isPLHomeomorphInto_of_isCompact
    hQ.isCompact (hu.injOn.mono hQP)

theorem IsPLCellOn.isPolyhedron_inter_preimage_boundary
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {A B : Set M} {u : E3 → M} {P S : Set E3} (hcell : IsPLCellOn 3 A B)
    (hu : IsPLHomeomorphInto 3 u P) (hS : IsPolyhedron S) (hSP : S ⊆ P) :
    IsPolyhedron (S ∩ u ⁻¹' B) := by
  obtain ⟨Q, r, v, hr, hv, -, rfl⟩ := hcell
  have hJ : IsPolyhedron (r '' stdSimplexBoundary 3) :=
    hr.isPLSphere_image_stdSimplexBoundary.isPolyhedron
  have hJQ : r '' stdSimplexBoundary 3 ⊆ Q := by
    rw [← hr.image_eq]
    exact image_mono fun x hx => hx.1
  have hvJ := hv.mono_of_polyhedron hJ hJQ
  have hclosed : IsClosed (v '' (r '' stdSimplexBoundary 3)) :=
    (hJ.isCompact.image_of_continuousOn hvJ.continuousOn).isClosed
  have huS := hu.isPLOn.mono_of_isPolyhedron hS hSP
  obtain ⟨C, hC, heq⟩ := continuousOn_iff_isClosed.mp
    (hu.continuousOn.mono hSP) _ hclosed
  apply hvJ.isPolyhedron_inter_preimage_image huS
  rw [inter_comm, heq]
  exact hS.isCompact.inter_left hC

end DifferentialGeometry.Topology.PiecewiseLinear
