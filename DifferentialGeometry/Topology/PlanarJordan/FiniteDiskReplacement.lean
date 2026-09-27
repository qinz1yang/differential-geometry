/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.SurfaceDiskReplacement

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies (Plane)

variable {E F H G M N ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
  [ChartedSpace H M] [ChartedSpace G N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}

theorem exists_homeomorph_smoothing_finite_disjoint_disks [Finite ι]
    (h : M ≃ₜ N)
    (a : ι → PartialDiffeomorph I 𝓘(ℝ, Plane) M Plane ∞)
    (b : ι → PartialDiffeomorph J 𝓘(ℝ, Plane) N Plane ∞)
    (K : ι → Set M) (hK : ∀ i, IsCompact (K i))
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (hKa : ∀ i, K i ⊆ (a i).source) (hKb : ∀ i, h '' K i ⊆ (b i).source)
    (γ : ι → AddCircle (1 : ℝ) → Plane)
    (hγ : ∀ i, _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ (γ i))
    (hcoord : ∀ i, a i '' K i = closure (Schoenflies.inside (range (γ i))))
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hfrontier : ∀ i, frontier (K i) ⊆ U i)
    (hlocal : ∀ i, IsLocalDiffeomorphOn I J ∞ h (U i)) :
    ∃ g : M ≃ₜ N,
      EqOn g h (⋃ i, interior (K i))ᶜ ∧
      (∀ i, g '' K i = h '' K i) ∧
      (∀ x, IsLocalDiffeomorphAt I J ∞ h x → IsLocalDiffeomorphAt I J ∞ g x) ∧
      ∀ i, IsLocalDiffeomorphOn I J ∞ g (K i) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have step (s : Finset ι) : ∃ g : M ≃ₜ N,
      EqOn g h (⋃ i ∈ s, interior (K i))ᶜ ∧
      (∀ i, g '' K i = h '' K i) ∧
      (∀ x, IsLocalDiffeomorphAt I J ∞ h x → IsLocalDiffeomorphAt I J ∞ g x) ∧
      ∀ i ∈ s, IsLocalDiffeomorphOn I J ∞ g (K i) := by
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨h, fun _ _ => rfl, fun _ => rfl, fun _ hx => hx, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨g, hgeq, hgimage, hgpreserve, hgsmooth⟩ := ih
        have hgchart : g '' K i ⊆ (b i).source := by rw [hgimage]; exact hKb i
        have hgU : IsLocalDiffeomorphOn I J ∞ g (U i) :=
          fun x => hgpreserve x (hlocal i x)
        obtain ⟨g', hgeq', hgimage', hgpreserve', V, hV, hKV, hVU, hgV,
          W, hW, hKW, hWa, hWb, hgW⟩ :=
          exists_homeomorph_smoothing_disk_in_charts g (a i) (b i) (hK i) (hKa i)
            hgchart (hγ i) (hcoord i) (hU i) (hfrontier i) hgU
        refine ⟨g', ?_, ?_, fun x hx => hgpreserve' x (hgpreserve x hx), ?_⟩
        · intro x hx
          have hxi : x ∉ interior (K i) := fun hxi =>
            hx (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_insert_self _ _, hxi⟩⟩)
          have hxs : x ∉ ⋃ j ∈ s, interior (K j) := by
            intro hxs
            obtain ⟨j, hjx⟩ := mem_iUnion.mp hxs
            obtain ⟨hj, hxj⟩ := mem_iUnion.mp hjx
            exact hx (mem_iUnion.mpr ⟨j, mem_iUnion.mpr
              ⟨Finset.mem_insert_of_mem hj, hxj⟩⟩)
          exact (hgeq' hxi).trans (hgeq hxs)
        · intro j
          by_cases hij : i = j
          · subst j
            exact hgimage'.trans (hgimage i)
          · have heq : EqOn g' g (K j) := by
              intro x hxj
              apply hgeq'
              intro hxi
              exact Set.disjoint_left.mp (hdisjoint hij) (interior_subset hxi) hxj
            exact (image_congr heq).trans (hgimage j)
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hjs
          · exact fun x => hgW ⟨x, hKW x.property⟩
          · exact fun x => hgpreserve' x (hgsmooth j hjs x)
  obtain ⟨g, hgeq, hgimage, hgpreserve, hgsmooth⟩ := step Finset.univ
  exact ⟨g, by simpa using hgeq, hgimage, hgpreserve,
    fun i => hgsmooth i (Finset.mem_univ i)⟩

theorem exists_diffeomorph_eqOn_compl_finite_disjoint_disks [Finite ι]
    (h : M ≃ₜ N)
    (a : ι → PartialDiffeomorph I 𝓘(ℝ, Plane) M Plane ∞)
    (b : ι → PartialDiffeomorph J 𝓘(ℝ, Plane) N Plane ∞)
    (K : ι → Set M) (hK : ∀ i, IsCompact (K i))
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (hKa : ∀ i, K i ⊆ (a i).source) (hKb : ∀ i, h '' K i ⊆ (b i).source)
    (γ : ι → AddCircle (1 : ℝ) → Plane)
    (hγ : ∀ i, _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ (γ i))
    (hcoord : ∀ i, a i '' K i = closure (Schoenflies.inside (range (γ i))))
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hfrontier : ∀ i, frontier (K i) ⊆ U i)
    (hlocal : ∀ i, IsLocalDiffeomorphOn I J ∞ h (U i))
    (houtside : IsLocalDiffeomorphOn I J ∞ h (⋃ i, K i)ᶜ) :
    ∃ D : Diffeomorph I J M N ∞,
      EqOn D h (⋃ i, interior (K i))ᶜ ∧ ∀ i, D '' K i = h '' K i := by
  obtain ⟨g, hgeq, hgimage, hgpreserve, hgsmooth⟩ :=
    exists_homeomorph_smoothing_finite_disjoint_disks h a b K hK hdisjoint hKa hKb
      γ hγ hcoord U hU hfrontier hlocal
  have hg : IsLocalDiffeomorph I J ∞ g := by
    intro x
    by_cases hx : x ∈ ⋃ i, K i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hgsmooth i ⟨x, hi⟩
    · exact hgpreserve x (houtside ⟨x, hx⟩)
  exact ⟨hg.diffeomorphOfBijective g.bijective, hgeq, hgimage⟩

end DifferentialGeometry.Topology.PlanarJordan
