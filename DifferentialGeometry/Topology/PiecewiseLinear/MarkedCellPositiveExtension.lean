/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedSpherePositiveExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CellPairBoundaryOrientation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLBall.exists_extension_of_positive_disk_family
    {P : Set E3} (hP : IsPLBall 3 P) {ι : Type*} [Finite ι]
    {D : ι → Set E3} {q : ι → (Fin 3 → ℝ) → E3}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDP : ∀ i, D i ⊆ frontier P) (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    {δ : ι → E3 → E3} (hδ : ∀ i, IsPLHomeomorphOn (δ i) (D i) (D i))
    (hpos : ∀ i, IsPLCirclePositive (q i '' stdSimplexBoundary 2) (δ i)) :
    ∃ N : E3 → E3, IsPLHomeomorphOn N P P ∧ ∀ i, EqOn N (δ i) (D i) := by
  obtain ⟨F, hF, hFD⟩ := hP.isPLSphere_frontier.exists_extension_of_positive_disk_family
    hq hDP hdis hδ hpos
  obtain ⟨r, hr⟩ := hP
  have hFb : IsPLHomeomorphOn F (r '' stdSimplexBoundary 3)
      (r '' stdSimplexBoundary 3) := by rw [hr.image_stdSimplexBoundary]; exact hF
  obtain ⟨N, hN, hNF⟩ := exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary hr hr hFb
  rw [hr.image_stdSimplexBoundary] at hNF
  exact ⟨N, hN, fun i => (hNF.mono (hDP i)).trans (hFD i)⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

theorem IsPLCellOn.exists_extension_of_positive_disk_family
    {P PB : Set M} (hP : IsPLCellOn 3 P PB) {ι : Type*} [Finite ι]
    {D J : ι → Set M} (hD : ∀ i, IsPLCellOn 2 (D i) (J i))
    (hDP : ∀ i, D i ⊆ PB) (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    {b : OpenPartialHomeomorph M E3} (hb : b ∈ (plGroupoid 3).maximalAtlas M)
    (hPb : P ⊆ b.source) {δ : ι → M → M}
    (hδ : ∀ i, IsPLHomeomorphInto 3 (δ i) (D i)) (hδD : ∀ i, δ i '' D i = D i)
    (hpos : ∀ i, IsPLCirclePositive (b '' J i) (b ∘ δ i ∘ b.symm)) :
    ∃ N : M → M, IsPLHomeomorphInto 3 N P ∧ N '' P = P ∧
      ∀ i, EqOn N (δ i) (D i) := by
  have hDP' (i : ι) : D i ⊆ P := (hDP i).trans hP.boundary_subset
  have hDb (i : ι) : D i ⊆ b.source := (hDP' i).trans hPb
  obtain ⟨hB, hPB⟩ := hP.isPLBall_image_chart hb hPb
  choose q hq hqJ using fun i => (hD i).exists_isPLHomeomorphOn_image_chart hb (hDb i)
  have hDfr (i : ι) : b '' D i ⊆ frontier (b '' P) := by
    rw [← hPB]
    exact image_mono (hDP i)
  have hdisb : Pairwise fun i j => Disjoint (b '' D i) (b '' D j) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hxy : y = x := b.injOn (hDb j hy) (hDb i hx) hyx
    exact disjoint_left.mp (hdis hij) hx (hxy ▸ hy)
  have hδb (i : ι) : IsPLHomeomorphOn (b ∘ δ i ∘ b.symm) (b '' D i) (b '' D i) :=
    (hδ i).isPLHomeomorphOn_chart_conjugate (hδD i) hb (hDb i)
      (IsPLBall.isPolyhedron ⟨q i, hq i⟩)
  have hposb (i : ι) : IsPLCirclePositive (q i '' stdSimplexBoundary 2)
      (b ∘ δ i ∘ b.symm) := by rw [← hqJ i]; exact hpos i
  obtain ⟨n, hn, hnD⟩ := hB.exists_extension_of_positive_disk_family hq hDfr hdisb hδb hposb
  have hBt : b '' P ⊆ b.target := image_subset_iff.mpr fun _ hx => b.map_source (hPb hx)
  have hbback : b.symm '' (b '' P) = P := b.symm_image_image_of_subset_source hPb
  have hi := isPLHomeomorphInto_symm_of_mem_maximalAtlas hb hB.isPolyhedron hBt
  let N := b.symm ∘ n ∘ Function.invFunOn b.symm (b '' P)
  obtain ⟨hN, hNim⟩ := exists_isPLHomeomorphInto_of_isPLHomeomorphOn hi hi hn
  rw [hbback] at hN hNim
  have hNb (x : E3) (hx : x ∈ b '' P) : N (b.symm x) = b.symm (n x) := by
    change b.symm (n (Function.invFunOn b.symm (b '' P) (b.symm x))) = _
    rw [hi.injOn.leftInvOn_invFunOn hx]
  refine ⟨N, hN, hNim, ?_⟩
  intro i x hx
  have hδx : δ i x ∈ D i := hδD i ▸ mem_image_of_mem (δ i) hx
  have ht := hNb (b x) ⟨x, hDP' i hx, rfl⟩
  rw [b.left_inv (hDb i hx), hnD i (mem_image_of_mem b hx)] at ht
  change N x = b.symm (b (δ i (b.symm (b x)))) at ht
  rwa [b.left_inv (hDb i hx), b.left_inv (hDb i hδx)] at ht

end DifferentialGeometry.Topology.PiecewiseLinear
