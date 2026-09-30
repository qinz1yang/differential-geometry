/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.SurfacePointSmoothing

open Set
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)

variable {M N ι : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N] [ChartedSpace Plane M] [ChartedSpace Plane N]
  [IsManifold 𝓘(ℝ, Plane) ∞ M] [IsManifold 𝓘(ℝ, Plane) ∞ N]

theorem exists_smooth_at_preserving_mapsTo [Finite ι] (h : M ≃ₜ N)
    (C : ι → Set M) (V : ι → Set N) (hC : ∀ i, IsClosed (C i))
    (hV : ∀ i, IsOpen (V i)) (hmap : ∀ i, MapsTo h (C i) (V i))
    {x : M} {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧ ∃ g : M ≃ₜ N,
      EqOn g h Kᶜ ∧ g x = h x ∧ IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g x ∧
      (∀ i, MapsTo g (C i) (V i)) ∧
      ∀ y ∉ K, IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h y →
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g y := by
  classical
  let W := U ∩ ⋂ i, if x ∈ C i then h ⁻¹' V i else (C i)ᶜ
  have hW : IsOpen W := hU.inter (isOpen_iInter_of_finite fun i => by
    split_ifs
    · exact (hV i).preimage h.continuous
    · exact (hC i).isOpen_compl)
  have hxW : x ∈ W := ⟨hxU, mem_iInter.mpr fun i => by
    split_ifs with hx
    · exact hmap i hx
    · exact hx⟩
  obtain ⟨K, hK, hKW, g, hgout, hgx, hglocal, hgpreserve⟩ := h.exists_smooth_at hW hxW
  have himage : g '' K = h '' K := by
    apply compl_injective
    rw [← g.image_compl, ← h.image_compl]
    exact image_congr fun y hy => hgout hy
  refine ⟨K, hK, hKW.trans inter_subset_left, g, hgout, hgx, hglocal, ?_, hgpreserve⟩
  intro i y hy
  by_cases hyK : y ∈ K
  · have hyV := mem_iInter.mp (hKW hyK).2 i
    by_cases hx : x ∈ C i
    · have hgy : g y ∈ h '' K := himage ▸ mem_image_of_mem g hyK
      obtain ⟨z, hz, hzg⟩ := hgy
      have hzV := mem_iInter.mp (hKW hz).2 i
      rw [ite_eq_left hx] at hzV
      exact hzg ▸ hzV
    · rw [ite_eq_right hx] at hyV
      exact (hyV hy).elim
  · rw [hgout hyK]
    exact hmap i hy

theorem exists_smooth_on_finset_preserving_mapsTo [Finite ι] (h : M ≃ₜ N)
    (C : ι → Set M) (V : ι → Set N) (hC : ∀ i, IsClosed (C i))
    (hV : ∀ i, IsOpen (V i)) (hmap : ∀ i, MapsTo h (C i) (V i))
    (T : Finset M) {U : Set M} (hU : IsOpen U) (hTU : (T : Set M) ⊆ U) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧ ∃ g : M ≃ₜ N,
      EqOn g h Kᶜ ∧ EqOn g h (T : Set M) ∧
      IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g (T : Set M) ∧
      ∀ i, MapsTo g (C i) (V i) := by
  classical
  have step : ∀ s : Finset M, s ⊆ T →
      ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧ ∃ g : M ≃ₜ N,
        EqOn g h Kᶜ ∧ EqOn g h (T : Set M) ∧
        IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g (s : Set M) ∧
        ∀ i, MapsTo g (C i) (V i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨∅, isCompact_empty, empty_subset _, h, fun _ _ => rfl, fun _ _ => rfl, ?_,
          hmap⟩
        intro y
        exact False.elim (by simpa using y.property)
    | @insert x s hxs ih =>
        intro hsub
        have hxT : x ∈ T := hsub (Finset.mem_insert_self _ _)
        have hsT : s ⊆ T := fun y hy => hsub (Finset.mem_insert_of_mem hy)
        obtain ⟨K, hK, hKU, g, hgout, hgfix, hgdiff, hgmap⟩ := ih hsT
        let W := U ∩ (T.erase x : Set M)ᶜ
        have hW : IsOpen W := hU.inter (T.erase x).finite_toSet.isClosed.isOpen_compl
        have hxW : x ∈ W := ⟨hTU hxT, by simp⟩
        obtain ⟨L, hL, hLW, g', hg'out, hg'x, hg'diff, hg'map, hg'preserve⟩ :=
          g.exists_smooth_at_preserving_mapsTo C V hC hV hgmap hW hxW
        have hout {y : M} (hyT : y ∈ T) (hyx : y ≠ x) : y ∉ L := by
          intro hyL
          exact (hLW hyL).2 (Finset.mem_erase.mpr ⟨hyx, hyT⟩)
        refine ⟨K ∪ L, hK.union hL, union_subset hKU (hLW.trans inter_subset_left),
          g', ?_, ?_, ?_, hg'map⟩
        · intro y hy
          exact (hg'out (fun hyL => hy (Or.inr hyL))).trans
            (hgout (fun hyK => hy (Or.inl hyK)))
        · intro y hyT
          by_cases hyx : y = x
          · subst y
            exact hg'x.trans (hgfix hxT)
          · exact (hg'out (hout hyT hyx)).trans (hgfix hyT)
        · intro y
          rcases Finset.mem_insert.mp y.property with hyx | hys
          · simpa only [hyx] using hg'diff
          · have hyx : (y : M) ≠ x := by
              intro heq
              apply hxs
              simpa only [heq] using hys
            exact hg'preserve y (hout (hsT hys) hyx) (hgdiff ⟨y, hys⟩)
  exact step T (Finset.Subset.refl T)

end Homeomorph
