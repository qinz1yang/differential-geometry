/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.DisjointRimDiskFamily
import DifferentialGeometry.Topology.PiecewiseLinear.GlobalSolidTorusLongitude
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskDisplacement
import DifferentialGeometry.Topology.PiecewiseLinear.TorusSubsurfaceHomologyRange

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem disk_firstHomology_subsingleton {D : Set E3} (hD : IsPLBall 2 D) :
    Subsingleton (integralSingularHomology 1 D) := by
  let _ := hD.contractibleSpace
  exact integralSingularHomology_subsingleton_of_contractible 1 one_ne_zero D

private theorem separating_subsurface_dichotomy {S W J : Set E3}
    {ι : Type*} [Finite ι] {C : ι → Set E3} (hS : IsCombinatorialSolidTorus S)
    (hJ : IsPLSphere 1 J) (hJT : J ⊆ frontier S) (hJS : CarriesFirstHomologyOnto J S)
    (hW : W ⊆ frontier S) (hWc : IsClosed W) (hC : ∀ i, IsPLSphere 1 (C i))
    (hCW : ∀ i, C i ⊆ W) (hCd : Pairwise fun i j => Disjoint (C i) (C j))
    (hfr : W ∩ closure (frontier S \ W) ⊆ ⋃ i, C i)
    (hsep : ∀ i, ¬ IsPreconnected (frontier S \ C i)) :
    (∃ G, IsPLSphere 1 G ∧ G ⊆ W ∧ CarriesFirstHomologyOnto G S) ∨
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion (hW.trans hS.isPolyhedron.isClosed.frontier_subset),
          continuous_inclusion _⟩ : C(W, S))) = ⊥ := by
  classical
  by_cases hsing : Subsingleton (integralSingularHomology 1 S)
  · right
    apply le_antisymm _ bot_le
    intro a _
    rw [Submodule.mem_bot]
    exact hsing.elim _ _
  have hT := hS.isPLTorus_frontier
  have hTS := hS.isPolyhedron.isClosed.frontier_subset
  obtain ⟨K, hKfin, hK, hKc, hKT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite K.faces := hKfin.to_subtype
  have hKS : K.space ⊆ S := hKT.subset.trans hTS
  have hJK : J ⊆ K.space := hJT.trans hKT.symm.subset
  choose D r hr hDT hCr using fun i =>
    hT.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff (hC i)
      ((hCW i).trans hW) (hsep i)
  have hD : ∀ i, IsPLBall 2 (D i) := fun i => ⟨r i, hr i⟩
  have hDK : ∀ i, D i ⊆ K.space := fun i => (hDT i).trans hKT.symm.subset
  have hpair : ∀ i j, (K.space \ (D i ∪ D j)).Nonempty := by
    intro i j
    by_contra hne
    have hcover : K.space ⊆ D i ∪ D j := sdiff_eq_empty.mp (not_nonempty_iff_eq_empty.mp hne)
    obtain ⟨J', -, hJ'K, hJ'D, -, hJ'S⟩ :=
      hK.exists_isPLSphere_one_avoiding_disk (hD i) (hDK i) hJ hJK hKS hJS
        isOpen_univ (subset_univ _)
    have hJ'Dj : J' ⊆ D j := fun x hx =>
      (hcover (hJ'K hx)).resolve_left (disjoint_left.mp hJ'D hx)
    exact hsing ((hJ'S.mono hJ'Dj ((hDT j).trans hTS)).subsingleton
      (disk_firstHomology_subsingleton (hD j)))
  have hdisr : Pairwise fun i j => Disjoint (r i '' stdSimplexBoundary 2)
      (r j '' stdSimplexBoundary 2) := by
    intro i j hij
    rw [← hCr i, ← hCr j]
    exact hCd hij
  obtain ⟨κ, hκ, B, hBD, hBd, hBunion⟩ :=
    hK.exists_disjoint_disk_subfamily_of_disjoint_boundaries hKc hr hDK hdisr hpair
  let _ : Finite κ := hκ
  have hB : ∀ b, IsPLBall 2 (B b) := fun b => by
    obtain ⟨i, hi⟩ := hBD b
    exact hi ▸ hD i
  have hBK : ∀ b, B b ⊆ K.space := fun b => by
    obtain ⟨i, hi⟩ := hBD b
    exact hi ▸ hDK i
  have hBU : (⋃ b, B b) ⊆ S := (iUnion_subset hBK).trans hKS
  have hCB : (⋃ i, C i) ⊆ ⋃ b, B b := by
    rw [hBunion]
    refine iUnion_mono fun i => ?_
    rw [hCr i, ← (hr i).image_eq]
    exact image_mono fun x hx => hx.1
  have hQ := hK.isConnected_sdiff_iUnion_of_isPLBall_two hKc hB hBK hBd
  have hcov : K.space \ ⋃ b, B b ⊆ (closure (frontier S \ W))ᶜ ∪ Wᶜ := by
    intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inl fun hcl => hx.2 (hCB (hfr ⟨hxW, hcl⟩))
    · exact Or.inr hxW
  have hemp : (K.space \ ⋃ b, B b) ∩ ((closure (frontier S \ W))ᶜ ∩ Wᶜ) = ∅ :=
    eq_empty_iff_forall_notMem.mpr fun x hx =>
      hx.2.1 (subset_closure ⟨hKT.subset hx.1.1, hx.2.2⟩)
  rcases isPreconnected_iff_subset_of_disjoint.mp hQ.isPreconnected _ _
    isClosed_closure.isOpen_compl hWc.isOpen_compl hcov hemp with hinside | houtside
  · left
    obtain ⟨G, hG, hGK, hGdis, hGS⟩ :=
      hK.exists_isPLSphere_one_avoiding_disjoint_disks B hB hBK hBd hJ hJK hKS hJS
    refine ⟨G, hG, ?_, hGS⟩
    intro x hx
    by_contra hxW
    exact hinside ⟨hGK hx, disjoint_left.mp hGdis hx⟩
      (subset_closure ⟨hKT.subset (hGK hx), hxW⟩)
  · right
    have hWB : W ⊆ ⋃ b, B b := by
      intro x hx
      by_contra hxB
      exact houtside ⟨hKT.symm.subset (hW hx), hxB⟩ hx
    have hzero : Subsingleton (integralSingularHomology 1 (⋃ b, B b)) :=
      (carriesFirstHomologyOnto_self _).subsingleton_of_iUnion
        (fun b => (hB b).isPolyhedron.isClosed) hBd
        (fun b => disk_firstHomology_subsingleton (hB b))
    have hle := range_integralSingularHomologyMap_inclusion_mono (hW.trans hTS) hBU hWB
    refine le_antisymm (hle.trans ?_) bot_le
    rintro _ ⟨a, rfl⟩
    rw [hzero.elim a 0, map_zero]
    exact Submodule.zero_mem _

theorem IsCombinatorialSolidTorus.exists_polygon_carrier_or_range_eq_bot_of_separating_boundary
    {S W : Set E3} {ι : Type*} [Finite ι] {C : ι → Set E3}
    (hS : IsCombinatorialSolidTorus S) (hW : W ⊆ frontier S) (hWc : IsClosed W)
    (hC : ∀ i, IsPLSphere 1 (C i)) (hCW : ∀ i, C i ⊆ W)
    (hCd : Pairwise fun i j => Disjoint (C i) (C j))
    (hfr : W ∩ closure (frontier S \ W) ⊆ ⋃ i, C i)
    (hsep : ∀ i, ¬ IsPreconnected (frontier S \ C i)) :
    (∃ G, IsPLSphere 1 G ∧ G ⊆ W ∧ CarriesFirstHomologyOnto G S) ∨
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion (hW.trans hS.isPolyhedron.isClosed.frontier_subset),
          continuous_inclusion _⟩ : C(W, S))) = ⊥ := by
  obtain ⟨J, hJ, hJT, hJS⟩ := hS.exists_isPLSphere_one_carriesFirstHomologyOnto_frontier
  exact separating_subsurface_dichotomy hS hJ hJT hJS hW hWc hC hCW hCd hfr hsep

end DifferentialGeometry.Topology.PiecewiseLinear
