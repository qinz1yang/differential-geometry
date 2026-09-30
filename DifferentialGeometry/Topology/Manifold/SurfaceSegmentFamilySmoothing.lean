/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.SurfaceSegmentSupport

open Set Filter Topology Metric
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)

variable {M N ι κ : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N] [ChartedSpace Plane M] [ChartedSpace Plane N]

theorem exists_smooth_finite_segments_preserving_mapsTo [Finite ι] [Finite κ]
    (h : M ≃ₜ N)
    (a : ι → PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) Plane M ∞)
    (b : ι → PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) N Plane ∞)
    (has : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, Plane.mk t 0 ∈ (a i).source)
    (hbs : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, h (a i (Plane.mk t 0)) ∈ (b i).source)
    (C : κ → Set M) (V : κ → Set N) (hC : ∀ j, IsClosed (C j))
    (hV : ∀ j, IsOpen (V j)) (hmap : ∀ j, MapsTo h (C j) (V j))
    (hinc : ∀ i j,
      (a i '' ((fun t : ℝ => Plane.mk t 0) '' Icc 0 1)) ⊆ C j ∨
      Disjoint (a i '' ((fun t : ℝ => Plane.mk t 0) '' Ioo 0 1)) (C j))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (a i '' ((fun t : ℝ => Plane.mk t 0) '' Ioo 0 1))
        (a j '' ((fun t : ℝ => Plane.mk t 0) '' Icc 0 1)))
    {P Ω : Set M} (hP : IsClosed P) (hΩ : IsOpen Ω)
    (hlocalP : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h P)
    (h0P : ∀ i, a i (Plane.mk 0 0) ∈ P) (h1P : ∀ i, a i (Plane.mk 1 0) ∈ P)
    (hAΩ : ∀ i, ∀ t ∈ Ioo (0 : ℝ) 1, a i (Plane.mk t 0) ∈ Ω \ P) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ Ω \ P ∧ ∃ g : M ≃ₜ N,
      EqOn g h Kᶜ ∧ (∀ j, MapsTo g (C j) (V j)) ∧
      ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g (a i (Plane.mk t 0)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let σ : ℝ → Plane := fun t => Plane.mk t 0
  let S (i : ι) := a i '' (σ '' Icc (0 : ℝ) 1)
  let A (i : ι) := a i '' (σ '' Ioo (0 : ℝ) 1)
  have hAS (i : ι) : A i ⊆ S i := image_mono (image_mono Ioo_subset_Icc_self)
  let e : Plane ≃L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hσ : Continuous σ := e.symm.continuous.comp (continuous_id.prodMk continuous_const)
  have hS (i : ι) : IsCompact (S i) :=
    (isCompact_Icc.image hσ).image_of_continuousOn
      ((a i).toOpenPartialHomeomorph.continuousOn.mono (by
        rintro _ ⟨t, ht, rfl⟩
        exact has i t ht))
  have hmem (i : ι) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : a i (σ t) ∈ S i :=
    ⟨σ t, ⟨t, ht, rfl⟩, rfl⟩
  have step (s : Finset ι) : ∃ K : Set M, IsCompact K ∧ K ⊆ Ω \ P ∧ ∃ g : M ≃ₜ N,
      EqOn g h Kᶜ ∧ (∀ j, MapsTo g (C j) (V j)) ∧
      (∀ i ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g (a i (σ t))) ∧
      ∀ i ∉ s, EqOn g h (S i) := by
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨∅, isCompact_empty, empty_subset _, h, fun _ _ => rfl, hmap,
          by simp, fun _ _ _ _ => rfl⟩
    | @insert i s hi ih =>
        obtain ⟨K, hK, hKΩ, g, hgout, hgmap, hgsmooth, hgeq⟩ := ih
        have hgP : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g P := by
          intro x
          have hxK : (x : M) ∉ K := fun hx => (hKΩ hx).2 x.property
          apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := h) _ (hlocalP x)
          filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
          exact hgout hy
        let U := ((Ω \ P) ∩ ⋂ j, if i = j then univ else (S j)ᶜ) ∩
          ⋂ j, if S i ⊆ C j then g ⁻¹' V j else (C j)ᶜ
        have hU : IsOpen U := ((hΩ.sdiff hP).inter (isOpen_iInter_of_finite fun j => by
          split_ifs
          · exact isOpen_univ
          · exact (hS j).isClosed.isOpen_compl)).inter (isOpen_iInter_of_finite fun j => by
            split_ifs
            · exact (hV j).preimage g.continuous
            · exact (hC j).isOpen_compl)
        have hAU : A i ⊆ U := by
          intro x hx
          have hxA := hx
          obtain ⟨v, ⟨t, ht, rfl⟩, rfl⟩ := hx
          refine ⟨⟨hAΩ i t ht, mem_iInter.mpr fun j => ?_⟩,
            mem_iInter.mpr fun j => ?_⟩
          · split_ifs with hij
            · trivial
            · exact fun hxj => disjoint_left.mp (hdisjoint hij) hxA hxj
          · split_ifs with hij
            · exact hgmap j (hij (hAS i hxA))
            · exact fun hxj => disjoint_left.mp ((hinc i j).resolve_left hij) hxA hxj
        have hgbs : ∀ t ∈ Icc (0 : ℝ) 1, g (a i (Plane.mk t 0)) ∈ (b i).source := by
          intro t ht
          rw [hgeq i hi (hmem i t ht)]
          exact hbs i t ht
        obtain ⟨L, hL, hLU, g', hg'out, hg'image, hg'smooth, hg'preserve⟩ :=
          g.exists_smooth_segment_within (a i) (b i) (has i) hgbs
            (hgP ⟨_, h0P i⟩) (hgP ⟨_, h1P i⟩) hU
            (fun t ht => hAU ⟨σ t, ⟨t, ht, rfl⟩, rfl⟩)
        have hLS {j : ι} (hij : i ≠ j) {x : M} (hx : x ∈ S j) : x ∉ L := by
          intro hxL
          have hxU := mem_iInter.mp (hLU hxL).1.2 j
          rw [ite_eq_right hij] at hxU
          exact hxU hx
        refine ⟨K ∪ L, hK.union hL, union_subset hKΩ
          (fun x hx => (hLU hx).1.1), g', ?_, ?_, ?_, ?_⟩
        · intro x hx
          exact (hg'out (fun hxL => hx (Or.inr hxL))).trans
            (hgout (fun hxK => hx (Or.inl hxK)))
        · intro j x hxC
          by_cases hxL : x ∈ L
          · by_cases hij : S i ⊆ C j
            · have hxy : g' x ∈ g '' L := hg'image ▸ mem_image_of_mem g' hxL
              obtain ⟨y, hy, hyx⟩ := hxy
              have hyV := mem_iInter.mp (hLU hy).2 j
              rw [ite_eq_left hij] at hyV
              exact hyx ▸ hyV
            · have hxU := mem_iInter.mp (hLU hxL).2 j
              rw [ite_eq_right hij] at hxU
              exact (hxU hxC).elim
          · rw [hg'out hxL]
            exact hgmap j hxC
        · intro j hj t ht
          rcases Finset.mem_insert.mp hj with hji | hjs
          · subst j
            exact hg'smooth t ht
          · have hij : i ≠ j := fun heq => hi (heq.symm ▸ hjs)
            exact hg'preserve _ (hLS hij (hmem j t ht)) (hgsmooth j hjs t ht)
        · intro j hj x hx
          have hij : i ≠ j := fun heq => hj (heq ▸ Finset.mem_insert_self i s)
          exact (hg'out (hLS hij hx)).trans (hgeq j
            (fun hjs => hj (Finset.mem_insert_of_mem hjs)) hx)
  obtain ⟨K, hK, hKΩ, g, hgout, hgmap, hgsmooth, -⟩ := step Finset.univ
  exact ⟨K, hK, hKΩ, g, hgout, hgmap, fun i => hgsmooth i (Finset.mem_univ i)⟩

end Homeomorph
