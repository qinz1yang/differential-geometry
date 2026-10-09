/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedSphereOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.ChartCircleOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.CellPairBoundaryOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLBall.exists_disk_family_map_with_circle_parity
    {P : Set E3} (hP : IsPLBall 3 P) {ι : Type*} [Finite ι]
    {D : ι → Set E3} {q : ι → (Fin 3 → ℝ) → E3}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDP : ∀ i, D i ⊆ frontier P) (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (σ : ZMod 2) :
    ∃ N : E3 → E3, IsPLHomeomorphOn N P P ∧ (∀ i, N '' D i = D i) ∧
      ∀ i, circleOrientationParity (q i '' stdSimplexBoundary 2) N = σ := by
  classical
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) σ with hσ | hσ
  · subst σ
    exact ⟨id, hP.isPolyhedron.isPLHomeomorphOn_id, fun _ => image_id _,
      fun i => circleOrientationParity_id ((hq i).isPLSphere_image_stdSimplexBoundary (n := 1))⟩
  · subst σ
    obtain ⟨G, hG, hGD, hneg⟩ :=
      hP.isPLSphere_frontier.exists_disk_family_map_reversing_circles hq hDP hdis
    obtain ⟨r, hr⟩ := hP
    have hGb : IsPLHomeomorphOn G (r '' stdSimplexBoundary 3)
        (r '' stdSimplexBoundary 3) := by rw [hr.image_stdSimplexBoundary]; exact hG
    obtain ⟨N, hN, hNG⟩ := exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary hr hr hGb
    rw [hr.image_stdSimplexBoundary] at hNG
    refine ⟨N, hN, fun i => ((hNG.mono (hDP i)).image_eq).trans (hGD i), ?_⟩
    intro i
    have hJ : q i '' stdSimplexBoundary 2 ⊆ frontier P :=
      (image_subset_iff.mpr fun _ hx => (hq i).bijOn.mapsTo hx.1).trans (hDP i)
    rw [circleOrientationParity_congr (hNG.mono hJ)]
    simp [circleOrientationParity, hneg i]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

theorem IsPLCellOn.exists_disk_family_map_with_circle_parity
    {P PB : Set M} (hP : IsPLCellOn 3 P PB) {ι : Type*} [Finite ι]
    {D J : ι → Set M} (hD : ∀ i, IsPLCellOn 2 (D i) (J i))
    (hDP : ∀ i, D i ⊆ PB) (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    {b : OpenPartialHomeomorph M E3} (hb : b ∈ (plGroupoid 3).maximalAtlas M)
    (hPb : P ⊆ b.source) (σ : ZMod 2) :
    ∃ N : M → M, IsPLHomeomorphInto 3 N P ∧ N '' P = P ∧
      (∀ i, N '' D i = D i) ∧ (∀ i, N '' J i = J i) ∧
      ∀ i (c : OpenPartialHomeomorph M E3), J i ⊆ c.source →
        circleOrientationParity (c '' J i) (c ∘ N ∘ c.symm) = σ := by
  have hDP' (i : ι) : D i ⊆ P := (hDP i).trans hP.boundary_subset
  have hDb (i : ι) : D i ⊆ b.source := (hDP' i).trans hPb
  have hJb (i : ι) : J i ⊆ b.source := (hD i).boundary_subset.trans (hDb i)
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
  obtain ⟨n, hn, hnD, hnσ⟩ := hB.exists_disk_family_map_with_circle_parity hq hDfr hdisb σ
  have hBt : b '' P ⊆ b.target := image_subset_iff.mpr fun _ hx => b.map_source (hPb hx)
  have hbback : b.symm '' (b '' P) = P := b.symm_image_image_of_subset_source hPb
  have hi := isPLHomeomorphInto_symm_of_mem_maximalAtlas hb hB.isPolyhedron hBt
  let N := b.symm ∘ n ∘ Function.invFunOn b.symm (b '' P)
  obtain ⟨hN, hNim⟩ := exists_isPLHomeomorphInto_of_isPLHomeomorphOn hi hi hn
  rw [hbback] at hN hNim
  have hNb (x : E3) (hx : x ∈ b '' P) : N (b.symm x) = b.symm (n x) := by
    change b.symm (n (Function.invFunOn b.symm (b '' P) (b.symm x))) = _
    rw [hi.injOn.leftInvOn_invFunOn hx]
  have hND (i : ι) : N '' D i = D i := by
    have hback : b.symm '' (b '' D i) = D i := b.symm_image_image_of_subset_source (hDb i)
    have heq : EqOn (N ∘ b.symm) (b.symm ∘ n) (b '' D i) :=
      fun x hx => hNb x (image_mono (hDP' i) hx)
    calc
      N '' D i = N '' (b.symm '' (b '' D i)) := by rw [hback]
      _ = (N ∘ b.symm) '' (b '' D i) := (image_comp _ _ _).symm
      _ = (b.symm ∘ n) '' (b '' D i) := heq.image_eq
      _ = b.symm '' (n '' (b '' D i)) := image_comp _ _ _
      _ = D i := by rw [hnD i, hback]
  have hNJ (i : ι) : N '' J i = J i := by
    have hnDi : IsPLHomeomorphOn n (b '' D i) (b '' D i) := by
      have ht := hn.restrict (IsPLBall.isPolyhedron ⟨q i, hq i⟩) (image_mono (hDP' i))
      rwa [hnD i] at ht
    have hnJi : n '' (b '' J i) = b '' J i := by
      rw [hqJ i]
      simpa only [image_comp] using ((hq i).trans hnDi).image_stdSimplexBoundary_congr (hq i)
    have hback : b.symm '' (b '' J i) = J i := b.symm_image_image_of_subset_source (hJb i)
    have heq : EqOn (N ∘ b.symm) (b.symm ∘ n) (b '' J i) := fun x hx =>
      hNb x (image_mono ((hD i).boundary_subset.trans (hDP' i)) hx)
    calc
      N '' J i = N '' (b.symm '' (b '' J i)) := by rw [hback]
      _ = (N ∘ b.symm) '' (b '' J i) := (image_comp _ _ _).symm
      _ = (b.symm ∘ n) '' (b '' J i) := heq.image_eq
      _ = b.symm '' (n '' (b '' J i)) := image_comp _ _ _
      _ = J i := by rw [hnJi, hback]
  refine ⟨N, hN, hNim, hND, hNJ, ?_⟩
  intro i c hJc
  have heq : EqOn (b ∘ N ∘ b.symm) n (b '' J i) := by
    intro x hx
    have hxB : x ∈ b '' P := image_mono ((hD i).boundary_subset.trans (hDP' i)) hx
    change b (N (b.symm x)) = n x
    rw [hNb x hxB, b.right_inv (hBt (hn.bijOn.mapsTo hxB))]
  have hbase : circleOrientationParity (b '' J i) (b ∘ N ∘ b.symm) = σ := by
    rw [circleOrientationParity_congr heq, hqJ i]
    exact hnσ i
  have hchange := circleOrientationParity_chart_eq b c (hJb i) hJc
    (fun x hx => hNJ i ▸ mem_image_of_mem N hx)
  exact hchange.symm.trans hbase

end DifferentialGeometry.Topology.PiecewiseLinear
