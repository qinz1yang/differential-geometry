/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartGlue
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.PLMap

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem PLPieceIn.isPolyhedron_inter_preimage_chart_of_isPolyhedron
    {Y : Set X} (T : PLPieceIn E n X Y)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsPolyhedron C) (hCe : C ⊆ e.target) :
    IsPolyhedron (T.complex.space ∩ T.map ⁻¹' (e.symm '' C)) := by
  obtain ⟨ι, hι, D, hD, rfl⟩ := hC
  let _ := hι
  rw [image_iUnion, preimage_iUnion, inter_iUnion]
  exact IsPolyhedron.iUnion fun i => T.isPolyhedron_inter_preimage_chart e he (hD i)
    ((subset_iUnion D i).trans hCe)

theorem PLPieceIn.isPolyhedron_inter_preimage_chart_symm
    {Y : Set X} (T : PLPieceIn E n X Y)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsPolyhedron C) (hCe : C ⊆ e.target) :
    IsPolyhedron (C ∩ e.symm ⁻¹' Y) := by
  have hpre := T.isPolyhedron_inter_preimage_chart_of_isPolyhedron e he hC hCe
  have hsub : T.complex.space ∩ T.map ⁻¹' (e.symm '' C) ⊆
      T.complex.space ∩ T.map ⁻¹' e.source := by
    rintro x ⟨hx, y, hy, hxy⟩
    refine ⟨hx, ?_⟩
    change T.map x ∈ e.source
    rw [← hxy]
    exact e.map_target (hCe hy)
  have hpl := (T.isPiecewiseAffineOn_chart e he).mono_of_isPolyhedron hpre hsub
  have hinj := e.injOn.comp (T.bijOn.injOn.mono inter_subset_left)
    (fun x hx => (hsub hx).2)
  have himage : (e ∘ T.map) '' (T.complex.space ∩ T.map ⁻¹' (e.symm '' C)) =
      C ∩ e.symm ⁻¹' Y := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, z, hz, hzx⟩, rfl⟩
      have heq : e (T.map x) = z := by rw [← hzx, e.right_inv (hCe hz)]
      constructor
      · change e (T.map x) ∈ C
        rwa [heq]
      · change e.symm (e (T.map x)) ∈ Y
        rw [heq, hzx]
        exact T.bijOn.mapsTo hx
    · rintro ⟨hy, hyY⟩
      obtain ⟨x, hx, hxy⟩ := T.bijOn.surjOn hyY
      refine ⟨x, ⟨hx, y, hy, hxy.symm⟩, ?_⟩
      change e (T.map x) = y
      rw [hxy, e.right_inv (hCe hy)]
  rw [← himage]
  exact hpre.image_of_isPiecewiseAffineOn hpl hinj

theorem PLPieceIn.exists_isPolyhedron_chart_neighborhood
    {N C J : Set X} (T : PLPieceIn E n X N)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) (hC : IsCompact C) (hCe : C ⊆ e.source)
    (hCN : C \ J ⊆ interior N) :
    ∃ P : Set (EuclideanSpace ℝ (Fin n)), IsPolyhedron P ∧
      (e '' C) \ (e '' J) ⊆ interior P ∧ P ⊆ e.target ∧ e.symm '' P ⊆ N := by
  have hCt : e '' C ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hCe hx)
  obtain ⟨Q, hQ, hCQ, hQt⟩ := exists_isPolyhedron_neighborhood
    (hC.image_of_continuousOn (e.continuousOn.mono hCe)) e.open_target hCt
  refine ⟨Q ∩ e.symm ⁻¹' N, T.isPolyhedron_inter_preimage_chart_symm e he hQ hQt,
    ?_, inter_subset_left.trans hQt, ?_⟩
  · intro y hy
    rw [interior_inter]
    refine ⟨hCQ hy.1, ?_⟩
    obtain ⟨x, hx, rfl⟩ := hy.1
    have hxJ : x ∉ J := fun hxJ => hy.2 ⟨x, hxJ, rfl⟩
    apply mem_interior_iff_mem_nhds.mpr
    apply (e.continuousAt_symm (e.map_source (hCe hx))).preimage_mem_nhds
    rw [e.left_inv (hCe hx)]
    exact mem_interior_iff_mem_nhds.mp (hCN ⟨hx, hxJ⟩)
  · rintro _ ⟨y, hy, rfl⟩
    exact hy.2

open Classical in
private theorem isPolyhedron_of_isCompact_of_eventuallyEq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {Q : Set F} (hQ : IsCompact Q)
    (hlocal : ∀ x ∈ Q, ∃ P : Set F, IsPolyhedron P ∧ Q =ᶠ[𝓝 x] P) :
    IsPolyhedron Q := by
  choose P hP hQP using fun x : Q => hlocal x x.property
  choose C hC hCsub hCnhds using fun x : Q =>
    exists_isHPolytope_subset_mem_nhds (hQP x)
  have hcover : Q ⊆ ⋃ x : Q, interior (C x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hCnhds ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover (fun x : Q => interior (C x))
    (fun _ => isOpen_interior) hcover
  let R : t → Set F := fun x => P x ∩ C x
  have hR : ∀ x : t, IsPolyhedron (R x) := fun x =>
    (hP x).inter (hC x).isPolyhedron
  rw [show Q = ⋃ x : t, R x by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x, hxt, hyC⟩ := mem_iUnion₂.mp (ht hy)
      have hyP : y ∈ P x := (hCsub x (interior_subset hyC)).mp hy
      exact mem_iUnion.mpr ⟨⟨x, hxt⟩, hyP, interior_subset hyC⟩
    · refine iUnion_subset fun x => ?_
      rintro y ⟨hyP, hyC⟩
      exact (hCsub x hyC).mpr hyP]
  exact IsPolyhedron.iUnion hR

open Classical in
theorem PLPieceIn.isPolyhedron_inter_preimage_of_isCompact
    {Y : Set X} (T : PLPieceIn E n X Y) {m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → X} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hf : IsPLOn m n f S) (hcompact : IsCompact (S ∩ f ⁻¹' Y)) :
    IsPolyhedron (S ∩ f ⁻¹' Y) := by
  apply isPolyhedron_of_isCompact_of_eventuallyEq hcompact
  intro x hx
  let e := chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  have hfx : f x ∈ e.source := mem_chart_source _ _
  have hex : e (f x) ∈ e.target := e.map_source hfx
  obtain ⟨C, hC, hCsub, hCnhds⟩ :=
    exists_isHPolytope_subset_mem_nhds (e.open_target.mem_nhds hex)
  let P : Set (EuclideanSpace ℝ (Fin n)) := C ∩ e.symm ⁻¹' Y
  have hP : IsPolyhedron P :=
    T.isPolyhedron_inter_preimage_chart_symm e (chart_mem_atlas _ _) hC.isPolyhedron hCsub
  have hcoord := (hf x hx.1).prop
  change IsPiecewiseAffineWithinAt (e ∘ f) S x at hcoord
  have hcoordcont := hcoord.continuousWithinAt
  obtain ⟨ι, hι, D, A, hDA, hDnhds⟩ := hcoord
  let _ := hι
  let R : Set (EuclideanSpace ℝ (Fin m)) := ⋃ i, D i ∩ A i ⁻¹' P
  have hR : IsPolyhedron R := IsPolyhedron.iUnion fun i =>
    (hDA i).1.isPolyhedron.inter_preimage hP (A i)
  refine ⟨R, hR, ?_⟩
  have hsource : f ⁻¹' e.source ∈ 𝓝[S] x :=
    (hf x hx.1).continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_source.mem_nhds hfx)
  have htarget : (e ∘ f) ⁻¹' C ∈ 𝓝[S] x :=
    hcoordcont.preimage_mem_nhdsWithin hCnhds
  have hgood : (⋃ i, D i) ∩ f ⁻¹' e.source ∩ (e ∘ f) ⁻¹' C ∈ 𝓝[S] x :=
    Filter.inter_mem (Filter.inter_mem hDnhds hsource) htarget
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hgood
  filter_upwards [hU] with z hzU
  by_cases hzS : z ∈ S
  · have hzgood := hUsub ⟨hzU, hzS⟩
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hzgood.1.1
    have hzfsource : f z ∈ e.source := hzgood.1.2
    have hzC : e (f z) ∈ C := hzgood.2
    have hAeq : A i z = e (f z) := ((hDA i).2.2 hzi).symm
    apply propext
    constructor
    · intro hzQ
      apply mem_iUnion.mpr
      refine ⟨i, hzi, ?_⟩
      change A i z ∈ C ∩ e.symm ⁻¹' Y
      rw [hAeq]
      exact ⟨hzC, by simpa only [mem_preimage, e.left_inv hzfsource] using hzQ.2⟩
    · intro hzR
      obtain ⟨j, hzj, hzAj⟩ := mem_iUnion.mp hzR
      have hzSj : z ∈ S := (hDA j).2.1 hzj
      have hAjeq : A j z = e (f z) := ((hDA j).2.2 hzj).symm
      refine ⟨hzSj, ?_⟩
      change f z ∈ Y
      have h := hzAj
      change A j z ∈ C ∩ e.symm ⁻¹' Y at h
      rw [hAjeq] at h
      simpa only [mem_preimage, e.left_inv hzfsource] using h.2
  · apply propext
    constructor
    · intro h
      exact (hzS h.1).elim
    · intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact (hzS ((hDA i).2.1 hi.1)).elim

end DifferentialGeometry.Topology.PiecewiseLinear
