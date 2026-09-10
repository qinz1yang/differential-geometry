/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

open Bundle Filter Function Set Topology
open scoped Manifold ContDiff

noncomputable section

namespace Poincare.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M]

theorem exists_finite_smoothBumpCovering_of_isCompact
    {K : Set M} (hK : IsCompact K) (U : M → Set M) (hU : ∀ x ∈ K, U x ∈ nhds x) :
    ∃ (t : Finset K) (ρ : SmoothBumpCovering t I M K),
      ∀ i, ρ.c i = (i.val : M) ∧ tsupport (ρ i) ⊆ U (i.val : M) := by
  classical
  have hb (x : K) : ∃ b : SmoothBumpFunction I (x : M), tsupport b ⊆ U x := by
    obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) (x : M)).mem_iff.mp
      (hU x x.property)
    exact ⟨b, hb⟩
  choose b hb using hb
  let W (x : K) := interior {y : M | b x y = 1}
  have hcover : K ⊆ ⋃ x : K, W x := by
    intro x hx
    refine mem_iUnion_of_mem ⟨x, hx⟩ ?_
    exact mem_interior_iff_mem_nhds.mpr (b ⟨x, hx⟩).eventuallyEq_one
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover W (fun _ ↦ isOpen_interior) hcover
  refine ⟨t, {
    c := fun i ↦ i.val.val
    toFun := fun i ↦ b i.val
    c_mem' := fun i ↦ i.val.property
    locallyFinite' := locallyFinite_of_finite _
    eventuallyEq_one' := ?_ }, fun i ↦ ⟨rfl, hb i.val⟩⟩
  intro x hx
  obtain ⟨i, hi, hxW⟩ := mem_iUnion₂.mp (ht hx)
  exact ⟨⟨i, hi⟩, mem_interior_iff_mem_nhds.mp hxW⟩

variable [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, TopologicalSpace (V x)]
    [∀ x, Module ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V] {m : ℕ∞}

theorem exists_contMDiffSection_eqOn_of_isCompact_of_local
    {K : Set M} (hK : IsCompact K) (s : ∀ x, V x)
    (hloc : ∀ x ∈ K, ∃ U ∈ nhds x, ∃ l : ∀ y, V y,
      ContMDiffOn I (I.prod (modelWithCornersSelf ℝ F)) (m : ℕ∞ω)
        (fun y ↦ (⟨y, l y⟩ : TotalSpace F V)) U ∧
      ∀ y ∈ U, y ∈ K → l y = s y) :
    ∃ S : Cₛ^(m : ℕ∞ω)⟮I; F, V⟯,
      IsCompact (closure {x | S x ≠ 0}) ∧ ∀ x ∈ K, S x = s x := by
  classical
  have hloc' (x : M) : ∃ U ∈ nhds x, ∃ l : ∀ y, V y,
      (x ∈ K → ContMDiffOn I (I.prod (modelWithCornersSelf ℝ F)) (m : ℕ∞ω)
        (fun y ↦ (⟨y, l y⟩ : TotalSpace F V)) U) ∧
      (x ∈ K → ∀ y ∈ U, y ∈ K → l y = s y) := by
    by_cases hx : x ∈ K
    · obtain ⟨U, hU, l, hl, hs⟩ := hloc x hx
      exact ⟨U, hU, l, fun _ ↦ hl, fun _ ↦ hs⟩
    · exact ⟨univ, univ_mem, s, by simp [hx]⟩
  choose U hU l hl hs using hloc'
  obtain ⟨t, b, hb⟩ := exists_finite_smoothBumpCovering_of_isCompact (I := I) hK
    (fun x ↦ interior (U x)) (fun x _ ↦ interior_mem_nhds.mpr (hU x))
  let ρ := b.toSmoothPartitionOfUnity
  have hρ (i : t) : tsupport (ρ i) ⊆ interior (U (i.val : M)) := by
    apply Subset.trans (closure_mono (b.support_toSmoothPartitionOfUnity_subset i))
    exact (hb i).2
  let S (x : M) : V x := ∑ i : t, (ρ i x) • l (i.val : M) x
  have hsmooth (i : t) : ContMDiff I (I.prod (modelWithCornersSelf ℝ F)) (m : ℕ∞ω)
      (fun x ↦ (⟨x, (ρ i x) • l (i.val : M) x⟩ : TotalSpace F V)) := by
    exact ContMDiffOn.smul_section_of_tsupport
      ((ρ i).contMDiff.of_le (by simp)).contMDiffOn isOpen_interior (hρ i)
      ((hl (i.val : M) i.val.property).mono interior_subset)
  have hS : ContMDiff I (I.prod (modelWithCornersSelf ℝ F)) (m : ℕ∞ω)
      (fun x ↦ (⟨x, S x⟩ : TotalSpace F V)) := by
    exact ContMDiff.sum_section (fun i _ ↦ hsmooth i)
  have hc : IsCompact (⋃ i : t, tsupport (b i)) :=
    isCompact_iUnion fun i ↦ (b i).hasCompactSupport
  have hsupport : closure {x | S x ≠ 0} ⊆ ⋃ i : t, tsupport (b i) := by
    apply closure_minimal ?_ hc.isClosed
    intro x hx
    by_contra hn
    apply hx
    change ∑ i : t, (ρ i x) • l (i.val : M) x = 0
    apply Finset.sum_eq_zero
    intro i _
    have hi : ρ i x = 0 := by
      by_contra hi
      exact hn (mem_iUnion.mpr ⟨i,
        subset_closure (b.support_toSmoothPartitionOfUnity_subset i hi)⟩)
    rw [hi, zero_smul]
  refine ⟨⟨S, hS⟩, hc.of_isClosed_subset isClosed_closure hsupport, fun x hx ↦ ?_⟩
  change ∑ i : t, (ρ i x) • l (i.val : M) x = s x
  calc
    _ = ∑ i : t, (ρ i x) • s x := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : ρ i x = 0
      · simp [hi]
      · rw [hs (i.val : M) i.val.property x
          (interior_subset (hρ i (subset_closure hi))) hx]
    _ = (∑ i : t, ρ i x) • s x := (Finset.sum_smul ..).symm
    _ = s x := by
      have hsum : ∑ i : t, ρ i x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hsum, one_smul]

end Poincare.Topology
