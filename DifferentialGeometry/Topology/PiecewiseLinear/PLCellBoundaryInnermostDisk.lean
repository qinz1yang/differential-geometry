/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocalInnermostDisk
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryDiskSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSphereInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CapDeletion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem IsPLCellOn.exists_innermost_disk_subset_of_eventually_eq
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {V S T D₀ : Set M} (hV : IsPLCellOn 3 V S)
    {ι : Type*} [Finite ι] {F : ι → Set M}
    (hF : ∀ i, IsPolyhedralSphere (n := 3) 1 (F i))
    (hFT : ∀ i, F i ⊆ T) (hdis : Pairwise fun i j => Disjoint (F i) (F j))
    (i₀ : ι) (hD₀ : IsPLCellOn 2 D₀ (F i₀)) (hD₀S : D₀ ⊆ S)
    (hlocal : ∀ x ∈ D₀, ∀ᶠ y in 𝓝 x, y ∈ T ↔ y ∈ S) :
    ∃ (i : ι) (D : Set M), IsPLCellOn 2 D (F i) ∧ D ⊆ D₀ ∧
      ∀ j, j ≠ i → Disjoint D (F j) := by
  obtain ⟨P, p, u, hp, hu, hVP, hSP⟩ := hV
  have hP : IsPLBall 3 P := ⟨p, hp⟩
  have hfrP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hp] at hSP
  let g := Function.invFunOn u P
  have hleft : LeftInvOn g u P := hu.injOn.leftInvOn_invFunOn
  have hD₀P : D₀ ⊆ u '' P := by
    rw [← hVP]
    exact hD₀S.trans (by rw [hSP, hVP]; exact image_mono hfrP)
  have hright : ∀ y ∈ u '' P, u (g y) = y :=
    fun y hy => hu.injOn.bijOn_image.invOn_invFunOn.2 hy
  have hD₀fr : g '' D₀ ⊆ frontier P := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hSP.subset (hD₀S hy)
    rw [← hzy, hleft (hfrP hz)]
    exact hz
  let I := {i : ι // F i ⊆ D₀}
  let G : I → Set E3 := fun i => g '' F i
  have hG : ∀ i, IsPLSphere 1 (G i) :=
    fun i => hu.isPLSphere_invFunOn_image (hF i) (i.2.trans hD₀P)
  have hGfr : ∀ i, G i ⊆ frontier P := fun i => (image_mono i.2).trans hD₀fr
  have hGdis : Pairwise fun i j => Disjoint (G i) (G j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    have hyz : y = z := by
      rw [← hright y (hD₀P (i.2 hy)), ← hright z (hD₀P (j.2 hz)), hyx, hzx]
    exact disjoint_left.mp (hdis (fun heq => hij (Subtype.ext heq))) hy (hyz.symm ▸ hz)
  obtain ⟨q₀, hq₀, hq₀J⟩ := hD₀.exists_isPLHomeomorphOn_invFunOn hu hD₀P
  let k₀ : I := ⟨i₀, hD₀.boundary_subset⟩
  obtain ⟨k, D, q, hq, hDD₀, hqG, hclean⟩ :=
    hP.isPLSphere_frontier.exists_innermost_disk_subset_of_eventually_eq
      hq₀ hD₀fr (fun _ _ => Filter.Eventually.of_forall fun _ => Iff.rfl)
      hG hGfr hGdis k₀ hq₀J.symm
  have hDP : D ⊆ P := hDD₀.trans (hD₀fr.trans hfrP)
  have hDpoly : IsPolyhedron D := (IsPLBall.isPolyhedron ⟨q, hq⟩)
  have himageG : u '' G k = F k := by
    rw [image_image]
    calc
      (u ∘ g) '' F k = id '' F k := image_congr fun y hy => hright y (hD₀P (k.2 hy))
      _ = F k := image_id _
  have hcell : IsPLCellOn 2 (u '' D) (F k) :=
    ⟨D, q, u, hq, hu.mono_of_polyhedron hDpoly hDP, rfl, by rw [hqG, himageG]⟩
  have himageD : u '' D ⊆ D₀ := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hyz⟩ := hDD₀ hz
    rw [← hyz, hright y (hD₀P hy)]
    exact hy
  refine ⟨k, u '' D, hcell, himageD, fun j hjk => ?_⟩
  by_cases hj : F j ⊆ D₀
  · apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxj
    apply disjoint_left.mp (hclean ⟨j, hj⟩ (fun heq => hjk (congrArg Subtype.val heq))) hx
    exact ⟨u x, hxj, hleft (hDP hx)⟩
  · have hji : j ≠ i₀ := fun heq => hj (heq.symm ▸ hD₀.boundary_subset)
    have hV' : IsPLCellOn 3 V S := ⟨P, p, u, hp, hu, hVP, by
      rw [IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hp]
      exact hSP⟩
    rcases hV'.subset_or_disjoint_disk_of_eventually_eq hD₀ hD₀S hlocal
        (hF j).isConnected.isPreconnected (hFT j) (hdis hji) with h | h
    · exact (hj h).elim
    · exact h.mono_left himageD

end DifferentialGeometry.Topology.PiecewiseLinear
