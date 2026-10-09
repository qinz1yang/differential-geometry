/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusDiskComplementConnected
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerSeams
import DifferentialGeometry.Topology.PiecewiseLinear.DisjointRimDiskFamily
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskSeparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLTorus.exists_connected_annulus_subset_avoiding_null_circles
    {T B : Set E3} (hT : IsPLTorus T) {ι κ : Type*} [Finite κ]
    (E : ι → Set E3) (hE : ∀ i, IsPLSphere 1 (E i)) (hET : ∀ i, E i ⊆ T)
    (hess : ∀ i, ¬ boundsDiskIn (E i) T) {i₀ i₁ : ι}
    (hB : IsPLAnnulusWithEnds B (E i₀) (E i₁))
    (hcomp : ∀ x ∈ B \ (E i₀ ∪ E i₁),
      connectedComponentIn (T \ ⋃ i, E i) x = B \ (E i₀ ∪ E i₁))
    (Q : κ → Set E3) (hQdis : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hQE : ∀ j i, Disjoint (Q j) (E i)) (hnull : ∀ j, boundsDiskIn (Q j) T) :
    ∃ U : Set E3, IsConnected U ∧ U ⊆ B \ (E i₀ ∪ E i₁) ∧
      Disjoint U (⋃ j, Q j) ∧ E i₀ ∪ E i₁ ⊆ closure U := by
  classical
  let τ := {j : κ // (Q j ∩ (B \ (E i₀ ∪ E i₁))).Nonempty}
  choose D r hr hDT hQr using fun j : τ => hnull j
  have hDball : ∀ j, IsPLBall 2 (D j) := fun j => ⟨r j, hr j⟩
  have hQD : ∀ j : τ, Q j ⊆ D j := by
    intro j
    rw [hQr j, ← (hr j).image_eq]
    exact image_mono fun x hx => hx.1
  have hDE : ∀ j i, Disjoint (D j) (E i) := by
    intro j i
    apply hT.disjoint_disk_of_essential_circle (hr j) (hDT j) (hE i) (hET i)
    · rw [← hQr j]
      exact (hQE j i).symm
    · exact hess i
  have hDcut : ∀ j, D j ⊆ T \ ⋃ i, E i := by
    intro j x hx
    refine ⟨hDT j hx, ?_⟩
    intro hxE
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxE
    exact disjoint_left.mp (hDE j i) hx hi
  have hDB : ∀ j, D j ⊆ B \ (E i₀ ∪ E i₁) := by
    intro j
    obtain ⟨x, hxQ, hxB⟩ := j.property
    exact ((hDball j).isConnected.isPreconnected.subset_connectedComponentIn
      (hQD j hxQ) (hDcut j)).trans (hcomp x hxB).subset
  obtain ⟨K, hKfin, hK, hKc, hKT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite K.faces := hKfin.to_subtype
  have hDK : ∀ j, D j ⊆ K.space := fun j => (hDT j).trans hKT.symm.subset
  have hrdis : Pairwise fun i j => Disjoint (r i '' stdSimplexBoundary 2)
      (r j '' stdSimplexBoundary 2) := by
    intro i j hij
    rw [← hQr i, ← hQr j]
    exact hQdis (Subtype.coe_injective.ne hij)
  have hpair : ∀ i j, (K.space \ (D i ∪ D j)).Nonempty := by
    intro i j
    obtain ⟨x, hx⟩ := (hE i₀).nonempty
    refine ⟨x, hKT.symm.subset (hET i₀ hx), ?_⟩
    rintro (hxi | hxj)
    · exact disjoint_left.mp (hDE i i₀) hxi hx
    · exact disjoint_left.mp (hDE j i₀) hxj hx
  obtain ⟨μ, hμ, F, hFD, hFdis, hFcover⟩ :=
    hK.exists_disjoint_disk_subfamily_of_disjoint_boundaries hKc hr hDK hrdis hpair
  let _ : Finite μ := hμ
  have hFball : ∀ j, IsPLBall 2 (F j) := by
    intro j
    obtain ⟨i, hi⟩ := hFD j
    rw [← hi]
    exact hDball i
  have hFB : ∀ j, F j ⊆ B \ (E i₀ ∪ E i₁) := by
    intro j
    obtain ⟨i, hi⟩ := hFD j
    rw [← hi]
    exact hDB i
  let U := (B \ (E i₀ ∪ E i₁)) \ ⋃ j, F j
  have hU : IsConnected U :=
    hB.isConnected_sdiff_ends_iUnion_of_isPLBall_two hFball hFB hFdis
  have hUQ : Disjoint U (⋃ j, Q j) := by
    apply disjoint_left.mpr
    intro x hxU hxQ
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxQ
    let j' : τ := ⟨j, ⟨x, hj, hxU.1⟩⟩
    apply hxU.2
    rw [hFcover]
    exact mem_iUnion.mpr ⟨j', hQD j' hj⟩
  have hFclosed : IsClosed (⋃ j, F j) :=
    isClosed_iUnion_of_finite fun j => (hFball j).isPolyhedron.isClosed
  have hends : Disjoint (E i₀ ∪ E i₁) (⋃ j, F j) := by
    apply disjoint_left.mpr
    intro x hxEnds hxF
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxF
    exact (hFB j hj).2 hxEnds
  exact ⟨U, hU, sdiff_subset, hUQ,
    hB.ends_subset_closure_sdiff_ends_sdiff hFclosed hends⟩

end DifferentialGeometry.Topology.PiecewiseLinear
