/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CapComplex
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq (E × ℝ)]

theorem capComplex_space (A L : Geometry.SimplicialComplex ℝ (E × ℝ)) {x₀ : E}
    (h : IsConeBase ((x₀, 1) : E × ℝ) L) (hA : ∀ q ∈ A.space, (q : E × ℝ).2 = 0)
    (hLA : L.faces ⊆ A.faces) :
    (capComplex A L h hA hLA).space = A.space ∪ (coneComplex h).space := by
  ext z
  constructor
  · intro hz
    obtain ⟨s, hs, hzs⟩ := (capComplex A L h hA hLA).mem_space_iff.mp hz
    rcases (show s ∈ A.faces ∪ (coneComplex h).faces from hs) with hs | hs
    · exact Or.inl (A.convexHull_subset_space hs hzs)
    · exact Or.inr ((coneComplex h).convexHull_subset_space hs hzs)
  · rintro (hz | hz)
    · obtain ⟨s, hs, hzs⟩ := A.mem_space_iff.mp hz
      exact (capComplex A L h hA hLA).convexHull_subset_space (Or.inl hs) hzs
    · obtain ⟨s, hs, hzs⟩ := (coneComplex h).mem_space_iff.mp hz
      exact (capComplex A L h hA hLA).convexHull_subset_space (Or.inr hs) hzs

theorem space_inter_coneComplex_space (A L : Geometry.SimplicialComplex ℝ (E × ℝ)) {x₀ : E}
    (h : IsConeBase ((x₀, 1) : E × ℝ) L) (hA : ∀ q ∈ A.space, (q : E × ℝ).2 = 0)
    (hLA : L.faces ⊆ A.faces) :
    A.space ∩ (coneComplex h).space = L.space := by
  ext z
  constructor
  · rintro ⟨hzA, hzc⟩
    have hz0 : z.2 = 0 := hA _ hzA
    obtain ⟨t, ht, hzt⟩ := (coneComplex h).mem_space_iff.mp hzc
    rcases (mem_coneComplex_faces_iff h).mp ht with htL | rfl | ⟨σ, hσ, rfl⟩
    · exact L.convexHull_subset_space htL hzt
    · rw [Finset.coe_singleton, convexHull_singleton] at hzt
      have hz1 : z.2 = 1 := by rw [hzt]
      rw [hz0] at hz1
      norm_num at hz1
    · have hpσ : ((x₀, 1) : E × ℝ) ∉ σ := h.notMem_face hσ
      rcases exists_combo_of_mem_convexHull_insert hpσ hzt with hzp | ⟨w, hw, u, hu0, hu1, hzeq⟩
      · rw [hzp] at hz0
        norm_num at hz0
      · have hw0 : w.2 = 0 := hA _ (A.convexHull_subset_space (hLA hσ) hw)
        have hsnd : z.2 = 1 + u * (w.2 - 1) := by
          rw [hzeq]
          simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
        rw [hz0, hw0] at hsnd
        have hu : u = 1 := by linarith
        rw [hu, one_smul, add_sub_cancel] at hzeq
        exact hzeq ▸ L.convexHull_subset_space hσ hw
  · intro hz
    obtain ⟨σ, hσ, hzσ⟩ := L.mem_space_iff.mp hz
    exact ⟨A.convexHull_subset_space (hLA hσ) hzσ,
      (coneComplex h).convexHull_subset_space ((mem_coneComplex_faces_iff h).mpr (Or.inl hσ)) hzσ⟩

theorem capComplex_space_sdiff_coneComplex_space (A L : Geometry.SimplicialComplex ℝ (E × ℝ))
    {x₀ : E} (h : IsConeBase ((x₀, 1) : E × ℝ) L) (hA : ∀ q ∈ A.space, (q : E × ℝ).2 = 0)
    (hLA : L.faces ⊆ A.faces) :
    (capComplex A L h hA hLA).space \ (coneComplex h).space = A.space \ L.space := by
  have hinter := space_inter_coneComplex_space A L h hA hLA
  rw [capComplex_space]
  ext z
  constructor
  · rintro ⟨hz, hzc⟩
    rcases hz with hz | hz
    · refine ⟨hz, fun hzL => hzc ?_⟩
      exact ((hinter.symm.subset hzL) : z ∈ A.space ∩ (coneComplex h).space).2
    · exact absurd hz hzc
  · rintro ⟨hz, hzL⟩
    exact ⟨Or.inl hz, fun hzc => hzL (hinter.subset ⟨hz, hzc⟩)⟩

theorem isPLBall_coneComplex_space_of_isPLSphere_one [FiniteDimensional ℝ E]
    {L : Geometry.SimplicialComplex ℝ (E × ℝ)} {x₀ : E} (h : IsConeBase ((x₀, 1) : E × ℝ) L)
    [Finite L.faces] (hL : IsPLSphere 1 L.space) : IsPLBall 2 (coneComplex h).space :=
  h.isPLBall_of_isPLSphere hL

theorem isPLBall_space_of_isPLSphere_capComplex [FiniteDimensional ℝ E]
    (A L : Geometry.SimplicialComplex ℝ (E × ℝ)) {x₀ : E}
    (h : IsConeBase ((x₀, 1) : E × ℝ) L) (hA : ∀ q ∈ A.space, (q : E × ℝ).2 = 0)
    (hLA : L.faces ⊆ A.faces) [Finite A.faces] [Finite L.faces] (hL : IsPLSphere 1 L.space)
    (hS : IsPLSphere 2 (capComplex A L h hA hLA).space)
    (hdense : A.space ⊆ closure (A.space \ L.space)) :
    IsPLBall 2 A.space := by
  have hD : IsPLBall 2 (coneComplex h).space := isPLBall_coneComplex_space_of_isPLSphere_one h hL
  have hDS : (coneComplex h).space ⊆ (capComplex A L h hA hLA).space := by
    rw [capComplex_space]
    exact subset_union_right
  have hball := hS.isPLBall_closure_sdiff hD hDS
  rw [capComplex_space_sdiff_coneComplex_space A L h hA hLA] at hball
  have hclosed : IsClosed A.space := (isPolyhedron_space A).isClosed
  have heq : closure (A.space \ L.space) = A.space :=
    Subset.antisymm (closure_minimal sdiff_subset hclosed) hdense
  rwa [heq] at hball

end DifferentialGeometry.Topology.PiecewiseLinear
