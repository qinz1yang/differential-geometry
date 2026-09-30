/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeExtension
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Simplex

variable (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))

def simplexComplex : Geometry.SimplicialComplex ℝ E where
  faces := {s | s.Nonempty ∧ s ⊆ T}
  isRelLowerSet_faces := by
    rintro s ⟨hne, hsT⟩
    exact ⟨hne, fun t hts ht => ⟨ht, hts.trans hsT⟩⟩
  indep hs := affineIndependent_of_subset hT hs.2
  inter_subset_convexHull hs ht := convexHull_inter_subset_of_affineIndependent hT hs.2 ht.2

theorem mem_simplexComplex_faces_iff {s : Finset E} :
    s ∈ (simplexComplex T hT).faces ↔ s.Nonempty ∧ s ⊆ T := Iff.rfl

theorem simplexComplex_faces_finite : (simplexComplex T hT).faces.Finite :=
  (Set.toFinite (T.powerset : Set (Finset E))).subset fun _ hs =>
    Finset.mem_coe.mpr (Finset.mem_powerset.mpr hs.2)

theorem simplexComplex_space (hne : T.Nonempty) :
    (simplexComplex T hT).space = convexHull ℝ (T : Set E) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := (simplexComplex T hT).mem_space_iff.mp hx
    exact convexHull_mono (Finset.coe_subset.mpr hs.2) hxs
  · exact (simplexComplex T hT).convexHull_subset_space ⟨hne, subset_rfl⟩

theorem simplexComplex_space_subset : (simplexComplex T hT).space ⊆ convexHull ℝ (T : Set E) := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (simplexComplex T hT).mem_space_iff.mp hx
  exact convexHull_mono (Finset.coe_subset.mpr hs.2) hxs

theorem simplexBoundary_faces_subset_simplexComplex :
    (simplexBoundary T hT).faces ⊆ (simplexComplex T hT).faces := fun _ hs => ⟨hs.2.1, hs.1⟩

theorem isConeBase_simplexComplex [DecidableEq E] {p : E} (hpT : p ∉ T)
    (hpind : AffineIndependent ℝ ((↑) : {x // x ∈ (insert p T : Finset E)} → E)) :
    IsConeBase p (simplexComplex T hT) where
  notMem_space := fun hp =>
    notMem_convexHull_of_affineIndependent_insert hpT hpind (simplexComplex_space_subset T hT hp)
  indep := by
    rintro σ ⟨-, hσT⟩
    refine hpind.mono (t := ((insert p T : Finset E) : Set E)) ?_
    rw [Finset.coe_insert]
    exact Set.insert_subset_insert (Finset.coe_subset.mpr hσT)
  radial := by
    intro x hx y hy t ht hyx
    have hxT : x ∈ convexHull ℝ (T : Set E) := simplexComplex_space_subset T hT hx
    have hyT : y ∈ convexHull ℝ (T : Set E) := simplexComplex_space_subset T hT hy
    by_contra hne
    have ht1 : t ≠ 1 := fun h => hne (by rw [hyx, h, one_smul, add_sub_cancel])
    have h1t : (1 : ℝ) - t ≠ 0 := sub_ne_zero.mpr ht1.symm
    obtain ⟨a, -, ha1, hax⟩ := mem_convexHull_iff_exists_weights.mp hxT
    obtain ⟨b, -, hb1, hby⟩ := mem_convexHull_iff_exists_weights.mp hyT
    refine (affineIndependent_insert_iff hpT hT).mp hpind ⟨fun v => (b v - t * a v) / (1 - t), ?_,
        ?_⟩
    · rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ha1, hb1, mul_one,
        div_self h1t]
    · calc ∑ v ∈ T, ((b v - t * a v) / (1 - t)) • v
          = (1 - t)⁻¹ • (∑ v ∈ T, b v • v - t • ∑ v ∈ T, a v • v) := by
            rw [Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [div_eq_inv_mul, mul_smul, sub_smul, mul_smul]
        _ = p := by
            rw [hby, hax, hyx]
            have hcombo : p + t • (x - p) - t • x = (1 - t) • p := by
              rw [smul_sub, sub_smul, one_smul]
              abel
            rw [hcombo, smul_smul, inv_mul_cancel₀ h1t, one_smul]

end Simplex

theorem IsConeBase.isPLBall_of_isPLBall [FiniteDimensional ℝ E] [DecidableEq E] {p : E}
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L) {n : ℕ}
    (hB : IsPLBall n L.space) : IsPLBall (n + 1) (coneComplex hL).space := by
  classical
  let q : Fin (n + 2) → ℝ := Pi.single 0 1
  have hq : q ∈ stdVertices n := by
    rw [stdVertices]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ 0)
  have hT₀ : AffineIndependent ℝ ((↑) : (stdVertices n).erase q → Fin (n + 2) → ℝ) :=
    affineIndependent_of_subset (stdVertices_affineIndependent n) (Finset.erase_subset q _)
  have hqT₀ : q ∉ (stdVertices n).erase q := Finset.notMem_erase q _
  have hins : insert q ((stdVertices n).erase q) = stdVertices n := Finset.insert_erase hq
  have hind : AffineIndependent ℝ
      ((↑) : {x // x ∈ (insert q ((stdVertices n).erase q) : Finset (Fin (n + 2) → ℝ))} →
        Fin (n + 2) → ℝ) := by
    rw [hins]
    exact stdVertices_affineIndependent n
  have hcard : ((stdVertices n).erase q).card = n + 1 := by
    have h1 := Finset.card_erase_of_mem hq
    have h2 := card_stdVertices n
    omega
  have hne : ((stdVertices n).erase q).Nonempty := Finset.card_pos.mp (by omega)
  have hcone := isConeBase_simplexComplex _ hT₀ hqT₀ hind
  have hfin := (simplexComplex_faces_finite _ hT₀).to_subtype
  have hball : IsPLBall n (simplexComplex _ hT₀).space := by
    rw [simplexComplex_space _ hT₀ hne]
    exact isPLBall_convexHull_of_affineIndependent _ hT₀ hcard
  obtain ⟨f, hf⟩ := hB
  obtain ⟨f₀, hf₀⟩ := hball
  obtain ⟨g, hg, -, -, -⟩ := exists_isPLHomeomorphOn_coneComplex hL hcone (hf.symm.trans hf₀)
  have hspace' : (coneComplex hcone).space =
      convexHull ℝ ((insert q ((stdVertices n).erase q) : Finset (Fin (n + 2) → ℝ)) :
        Set (Fin (n + 2) → ℝ)) := by
    ext x
    rw [mem_coneComplex_space_iff, simplexComplex_space _ hT₀ hne]
    constructor
    · rintro (rfl | ⟨z, hz, s, hs0, hs1, rfl⟩)
      · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self q _))
      · exact mem_convexHull_insert_of_combo hz hs0.le hs1
    · intro hx
      rcases exists_combo_of_mem_convexHull_insert hqT₀ hx with h | ⟨z, hz, s, hs0, hs1, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨z, hz, s, hs0, hs1, h⟩
  have hspace : (coneComplex hcone).space = Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)) := by
    rw [hspace', hins, convexHull_stdVertices]
  rw [hspace] at hg
  exact ⟨_, hg.symm⟩

end DifferentialGeometry.Topology.PiecewiseLinear
