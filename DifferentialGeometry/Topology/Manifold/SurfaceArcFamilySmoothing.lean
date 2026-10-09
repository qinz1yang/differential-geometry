/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.SurfaceArcSmoothing

open Set Metric
open scoped ContDiff Manifold

namespace Homeomorph

open Schoenflies (Plane)
open DifferentialGeometry.Topology.PlanarJordan

variable {M N ι : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N] [ChartedSpace Plane M] [ChartedSpace Plane N]

theorem exists_smooth_finite_disjoint_arcs_in_charts [Finite ι] (h : M ≃ₜ N)
    (a : ι → PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) Plane M ∞)
    (b : ι → PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) N Plane ∞)
    (τa τb ρ W : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (hρW : ∀ i, ρ i ≤ W i)
    (hab : ∀ i, τa i + 2 * ρ i < τb i - 2 * ρ i)
    (hR : ∀ i, planeRect (τa i - 3 * ρ i) (τb i + 3 * ρ i) (-W i) (W i) ⊆ (a i).source)
    (hRb : ∀ i, ∀ v ∈ planeRect (τa i - 3 * ρ i) (τb i + 3 * ρ i) (-W i) (W i),
      h (a i v) ∈ (b i).source)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (a i '' planeRect (τa i - 3 * ρ i) (τb i + 3 * ρ i) (-W i) (W i))
        (a j '' planeRect (τa j - 3 * ρ j) (τb j + 3 * ρ j) (-W j) (W j)))
    (hends : ∀ i, IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h
      (a i '' (ball (Plane.mk (τa i) 0) (ρ i) ∪ ball (Plane.mk (τb i) 0) (ρ i)))) :
    ∃ g : M ≃ₜ N,
      EqOn g h (⋃ i, a i '' planeRect (τa i - 3 * ρ i) (τb i + 3 * ρ i) (-W i) (W i))ᶜ ∧
      (∀ i, g '' (a i '' planeRect (τa i - 3 * ρ i) (τb i + 3 * ρ i) (-W i) (W i)) =
        h '' (a i '' planeRect (τa i - 3 * ρ i) (τb i + 3 * ρ i) (-W i) (W i))) ∧
      (∀ i, ∀ t ∈ Icc (τa i) (τb i),
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g (a i (Plane.mk t 0))) ∧
      ∀ x ∉ ⋃ i, a i '' planeRect (τa i - 3 * ρ i) (τb i + 3 * ρ i) (-W i) (W i),
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h x →
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g x := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let R (i : ι) := planeRect (τa i - 3 * ρ i) (τb i + 3 * ρ i) (-W i) (W i)
  let K (i : ι) := a i '' R i
  have hballs (i : ι) : ball (Plane.mk (τa i) 0) (ρ i) ∪
      ball (Plane.mk (τb i) 0) (ρ i) ⊆ R i := by
    apply union_subset
    · apply ball_subset_planeRect <;>
        norm_num [Schoenflies.Plane.mk] <;>
        linarith [hρ i, hρW i, hab i]
    · apply ball_subset_planeRect <;>
        norm_num [Schoenflies.Plane.mk] <;>
        linarith [hρ i, hρW i, hab i]
  have hcore (i : ι) {t : ℝ} (ht : t ∈ Icc (τa i) (τb i)) : Plane.mk t 0 ∈ R i := by
    change τa i - 3 * ρ i ≤ t ∧ t ≤ τb i + 3 * ρ i ∧ -W i ≤ 0 ∧ 0 ≤ W i
    exact ⟨by linarith [ht.1, hρ i], by linarith [ht.2, hρ i],
      by linarith [hρW i, hρ i], by linarith [hρW i, hρ i]⟩
  have step (s : Finset ι) : ∃ g : M ≃ₜ N,
      EqOn g h (⋃ i ∈ s, K i)ᶜ ∧ (∀ i, g '' K i = h '' K i) ∧
      (∀ i ∈ s, ∀ t ∈ Icc (τa i) (τb i),
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g (a i (Plane.mk t 0))) ∧
      ∀ x ∉ ⋃ i ∈ s, K i,
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ h x →
        IsLocalDiffeomorphAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨h, fun _ _ => rfl, fun _ => rfl, by simp, fun _ _ hx => hx⟩
    | @insert i s hi ih =>
        obtain ⟨g, hgeq, hgimage, hgsmooth, hgpreserve⟩ := ih
        have hout {x : M} (hx : x ∈ K i) : x ∉ ⋃ j ∈ s, K j := by
          intro hsx
          obtain ⟨j, hjx⟩ := mem_iUnion.mp hsx
          obtain ⟨hj, hxj⟩ := mem_iUnion.mp hjx
          have hij : i ≠ j := fun heq => hi (heq.symm ▸ hj)
          exact disjoint_left.mp (hdisjoint hij) hx hxj
        have hgRb : ∀ v ∈ R i, g (a i v) ∈ (b i).source := by
          intro v hv
          rw [hgeq (hout ⟨v, hv, rfl⟩)]
          exact hRb i v hv
        have hgends : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ g
            (a i '' (ball (Plane.mk (τa i) 0) (ρ i) ∪ ball (Plane.mk (τb i) 0) (ρ i))) := by
          intro x
          obtain ⟨v, hv, hvx⟩ := x.property
          exact hgpreserve x (hout ⟨v, hballs i hv, hvx⟩) (hends i x)
        obtain ⟨ρ', hρ', -, δ, hδ, -, g', hgeq', hgimage', -, hglocal, -, hgpreserve'⟩ :=
          g.exists_smooth_arc_in_charts (a i) (b i) (hρ i) (hρW i) (hab i)
            (hR i) hgRb hgends
        have hsub : (⋃ j ∈ s, K j) ⊆ ⋃ j ∈ insert i s, K j := by
          intro x hx
          obtain ⟨j, hjx⟩ := mem_iUnion.mp hx
          obtain ⟨hj, hxj⟩ := mem_iUnion.mp hjx
          exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hj, hxj⟩⟩
        have hnew : K i ⊆ ⋃ j ∈ insert i s, K j := fun x hx =>
          mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_insert_self _ _, hx⟩⟩
        refine ⟨g', ?_, ?_, ?_, ?_⟩
        · intro x hx
          exact (hgeq' (fun hxi => hx (hnew hxi))).trans
            (hgeq (fun hxs => hx (hsub hxs)))
        · intro j
          by_cases hij : i = j
          · subst j
            exact hgimage'.trans (hgimage i)
          · have heq : EqOn g' g (K j) := fun x hxj =>
              hgeq' (fun hxi => disjoint_left.mp (hdisjoint hij) hxi hxj)
            exact (image_congr heq).trans (hgimage j)
        · intro j hj t ht
          rcases Finset.mem_insert.mp hj with hji | hjs
          · subst j
            apply hglocal ⟨a i (Plane.mk t 0), Plane.mk t 0, ?_, rfl⟩
            change τa i - 3 * ρ' < t ∧ t < τb i + 3 * ρ' ∧ -δ < 0 ∧ 0 < δ
            exact ⟨by linarith [ht.1], by linarith [ht.2], by linarith, hδ⟩
          · have hij : i ≠ j := fun heq => hi (heq.symm ▸ hjs)
            exact hgpreserve' _
              (fun hxi => disjoint_left.mp (hdisjoint hij) hxi ⟨_, hcore j ht, rfl⟩)
              (hgsmooth j hjs t ht)
        · intro x hx hlocalx
          exact hgpreserve' x (fun hxi => hx (hnew hxi))
            (hgpreserve x (fun hxs => hx (hsub hxs)) hlocalx)
  obtain ⟨g, hgeq, hgimage, hgsmooth, hgpreserve⟩ := step Finset.univ
  exact ⟨g, by simpa using hgeq, hgimage,
    fun i => hgsmooth i (Finset.mem_univ i), by simpa [K, R] using hgpreserve⟩

end Homeomorph
