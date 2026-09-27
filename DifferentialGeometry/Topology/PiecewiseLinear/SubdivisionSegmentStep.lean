/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBallNeighborhoodImage
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionEndPoints

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {Ea : Type*} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

open Classical in
theorem LocallyFinitePLPieceIn.exists_pair_mem_faces_lt_of_mem_segment
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U) (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    {a x : Ea} (hax : ({a, x} : Finset Ea) ∈ 𝒦.complex.faces) (g : Ea →L[ℝ] ℝ)
    (hg : g (x - a) = 1) {q : Ea} (hq : ({q} : Finset Ea) ∈ 𝒦'.complex.faces)
    (hqs : q ∈ segment ℝ a x) (hqx : q ≠ x) :
    ∃ q', ({q, q'} : Finset Ea) ∈ 𝒦'.complex.faces ∧ q' ≠ q ∧ q' ∈ segment ℝ a x ∧
      g (q - a) < g (q' - a) := by
  have hind : AffineIndependent ℝ ((↑) : ({a, x} : Finset Ea) → Ea) := 𝒦.complex.indep hax
  have hne : ({a, x} : Finset Ea).Nonempty := ⟨a, Finset.mem_insert_self a {x}⟩
  have hLK : (simplexComplex ({a, x} : Finset Ea) hind).faces ⊆ 𝒦.complex.faces :=
    fun ρ hρ => 𝒦.complex.down_closed hax hρ.2 hρ.1
  have hLspace : (simplexComplex ({a, x} : Finset Ea) hind).space = segment ℝ a x := by
    rw [simplexComplex_space _ hind hne, Finset.coe_insert, Finset.coe_singleton,
      convexHull_pair]
  have hJ := hsub.restrict (simplexComplex ({a, x} : Finset Ea) hind) hLK
  have hJspace : (restrict 𝒦'.complex (simplexComplex ({a, x} : Finset Ea) hind).space).space =
      segment ℝ a x := hJ.space_eq.trans hLspace
  have hsegK : segment ℝ a x ⊆ 𝒦'.complex.space := by
    rw [hsub.space_eq, ← hLspace]
    exact space_mono_of_faces_subset hLK
  have hsegC : IsCompact (segment ℝ a x) := by
    rw [← hLspace, simplexComplex_space _ hind hne]
    exact ({a, x} : Finset Ea).finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hJfin : (restrict 𝒦'.complex
      (simplexComplex ({a, x} : Finset Ea) hind).space).faces.Finite := by
    refine (𝒦'.finite_faces_inter_of_isCompact hsegC hsegK).subset ?_
    intro ρ hρ
    obtain ⟨z, hz⟩ := 𝒦'.complex.nonempty_of_mem_faces hρ.1
    exact ⟨hρ.1, z, subset_convexHull ℝ _ (Finset.mem_coe.mpr hz),
      hLspace ▸ hρ.2 (subset_convexHull ℝ _ (Finset.mem_coe.mpr hz))⟩
  have : Finite (restrict 𝒦'.complex
      (simplexComplex ({a, x} : Finset Ea) hind).space).faces := hJfin.to_subtype
  have hdim : ∀ s ∈ (restrict 𝒦'.complex
      (simplexComplex ({a, x} : Finset Ea) hind).space).faces, s.card ≤ 2 :=
    fun s hs => hJ.card_le (fun ρ hρ => (Finset.card_le_card hρ.2).trans Finset.card_le_two) hs
  have hqJ : ({q} : Finset Ea) ∈ (restrict 𝒦'.complex
      (simplexComplex ({a, x} : Finset Ea) hind).space).faces := by
    refine ⟨hq, ?_⟩
    rw [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff, hLspace]
    exact hqs
  have hray : ∀ s ∈ Ioc (0 : ℝ) 1, q + s • (x - q) ∈ (restrict 𝒦'.complex
      (simplexComplex ({a, x} : Finset Ea) hind).space).space := by
    intro s hs
    rw [hJspace]
    exact (convex_segment a x).add_smul_sub_mem hqs (right_mem_segment ℝ a x) ⟨hs.1.le, hs.2⟩
  obtain ⟨q', s, hq'q, hpair, hs0, -, hm⟩ :=
    exists_pair_mem_faces_of_forall_add_smul_mem_space hdim hqJ (sub_ne_zero.mpr hqx.symm)
      one_pos hray
  have hq'seg : q' ∈ segment ℝ a x := by
    rw [← hLspace]
    exact hpair.2 (subset_convexHull ℝ _ (by simp))
  refine ⟨q', hpair.1, hq'q, hq'seg, ?_⟩
  rw [segment_eq_image'] at hqs
  obtain ⟨l, ⟨hl0, hl1⟩, hql⟩ := hqs
  beta_reduce at hql
  have hgq : g (q - a) = l := by
    rw [← hql, add_sub_cancel_left, map_smul, hg, smul_eq_mul, mul_one]
  have hl1' : l < 1 := by
    rcases hl1.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hqx
      rw [← hql, h, one_smul, add_sub_cancel]
  rw [Finset.coe_insert, Finset.coe_singleton, convexHull_pair, segment_eq_image'] at hm
  obtain ⟨μ, ⟨hμ0, -⟩, hμ⟩ := hm
  beta_reduce at hμ
  have hμ' : μ • (q' - q) = s • (x - q) := add_left_cancel hμ
  have hgμ := congrArg g hμ'
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hgμ
  have e1 : g (q' - q) = g (q' - a) - g (q - a) := by
    rw [← map_sub]
    congr 1
    abel
  have e2 : g (x - q) = 1 - g (q - a) := by
    rw [← hg, ← map_sub]
    congr 1
    abel
  rw [e1, e2, hgq] at hgμ
  rw [hgq]
  by_contra hle
  rw [not_lt] at hle
  have h1 : μ * (g (q' - a) - l) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμ0 (by linarith)
  have h2 : 0 < s * (1 - l) := mul_pos hs0 (by linarith)
  linarith

end DifferentialGeometry.Topology.PiecewiseLinear
