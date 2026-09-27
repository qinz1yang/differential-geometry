/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.InwardPushStages
import DifferentialGeometry.Topology.PiecewiseLinear.StageInwardPush

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [T2Space M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [MetricSpace M₂]

theorem IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isPLOn_injOn_leftInvOn_dist_lt
    {K : Set M₁} (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 3 K)
    {h : M₁ → M₂} (hh : ContinuousOn h K) {ψ : M₁ → ℝ} (hψ : ContinuousOn ψ K)
    (hψpos : ∀ x ∈ K, 0 < ψ x) :
    ∃ p q : M₁ → M₁, ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ MapsTo p K W ∧
      IsPLOn 3 3 p K ∧ InjOn p K ∧ IsPLOn 3 3 q W ∧ MapsTo q W K ∧ LeftInvOn q p K ∧
      ∀ x ∈ K, dist (h (p x)) (h x) < ψ x := by
  classical
  have : LocallyCompactSpace M₁ :=
    ChartedSpace.locallyCompactSpace (H := EuclideanSpace ℝ (Fin 3)) (M := M₁)
  have : Nonempty ((M₁ → M₁) × (M₁ → M₁) × Set M₁ × Set M₁) := ⟨(id, id, ∅, ∅)⟩
  obtain ⟨T, -⟩ := id hK
  obtain ⟨N, hN0, hNsucc⟩ :
      ∃ N : ℕ → Set M₁, N 0 = ∅ ∧ ∀ j, N (j + 1) = T.N j :=
    ⟨fun i => Nat.rec ∅ (fun j _ => T.N j) i, rfl, fun _ => rfl⟩
  have hNc : ∀ i, IsCompact (N i) := by
    intro i
    cases i with
    | zero => rw [hN0]; exact isCompact_empty
    | succ j => rw [hNsucc]; exact T.isCompact j
  have hNK : ∀ i, N i ⊆ K := by
    intro i
    cases i with
    | zero => rw [hN0]; exact empty_subset _
    | succ j => rw [hNsucc]; exact T.subset j
  have hNmono : Monotone N := by
    refine monotone_nat_of_le_succ fun i => ?_
    cases i with
    | zero => rw [hN0]; exact empty_subset _
    | succ j => rw [hNsucc, hNsucc]; exact T.monotone (Nat.le_succ j)
  have hNcover : ∀ x ∈ K, ∃ i, x ∈ N i := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (T.iUnion_eq.symm ▸ hx)
    exact ⟨j + 1, by rw [hNsucc]; exact hj⟩
  have hNnhds : ∀ i, ∀ x ∈ N i, N (i + 1) ∈ 𝓝[K] x := by
    intro i x hx
    cases i with
    | zero => rw [hN0] at hx; exact absurd hx (notMem_empty x)
    | succ j =>
      rw [hNsucc] at hx
      rw [hNsucc]
      exact T.subset_nhdsWithin j x hx
  obtain ⟨Inv, hInv⟩ :
      ∃ Inv : ℕ → ((M₁ → M₁) × (M₁ → M₁) × Set M₁ × Set M₁) → Prop, ∀ i d, Inv i d ↔
        IsPLOn 3 3 d.1 K ∧ InjOn d.1 K ∧ MapsTo d.1 K K ∧ IsPLOn 3 3 d.2.1 K ∧
          MapsTo d.2.1 K K ∧ LeftInvOn d.2.1 d.1 K ∧ IsCompact d.2.2.1 ∧
          d.2.2.1 ⊆ interior K ∧ MapsTo d.1 (N i) (interior d.2.2.1) ∧ IsCompact d.2.2.2 ∧
          d.2.2.2 ⊆ interior K ∧ d.2.2.1 ⊆ d.2.2.2 ∧
          (∀ x ∈ K, dist (h (d.1 x)) (h x) ≤ (1 - (1 / 2 : ℝ) ^ i) * ψ x) ∧
          ∀ x ∈ K, ψ (d.1 x) ≤ (2 - (1 / 2 : ℝ) ^ i) * ψ x :=
    ⟨_, fun _ _ => Iff.rfl⟩
  have hbase : Inv 0 ((id, id, ∅, ∅) : (M₁ → M₁) × (M₁ → M₁) × Set M₁ × Set M₁) := by
    refine (hInv 0 _).mpr ⟨hK.isPLOn_id, injOn_id K, mapsTo_id K, hK.isPLOn_id, mapsTo_id K,
      fun _ _ => rfl, isCompact_empty, empty_subset _, ?_, isCompact_empty, empty_subset _,
      Subset.rfl, fun x _ => ?_, fun x _ => ?_⟩
    · rw [hN0]
      intro x hx
      exact absurd hx (notMem_empty x)
    · change dist (h x) (h x) ≤ (1 - (1 / 2 : ℝ) ^ 0) * ψ x
      rw [dist_self, pow_zero]
      norm_num
    · change ψ x ≤ (2 - (1 / 2 : ℝ) ^ 0) * ψ x
      rw [pow_zero]
      norm_num
  have hstep : ∀ (i : ℕ) (d : (M₁ → M₁) × (M₁ → M₁) × Set M₁ × Set M₁), Inv i d →
      ∃ d', Inv (i + 1) d' ∧ (∀ x ∈ K, d.1 x ∈ d.2.2.2 → d'.1 x = d.1 x) ∧
        (∀ y ∈ d.2.2.2, d'.2.1 y = d.2.1 y) ∧ d.2.2.2 ⊆ d'.2.2.2 := by
    intro i d hd
    obtain ⟨hPpl, hPinj, hPmap, hQpl, hQmap, hQP, -, -, -, hCc, hCint, -, hdist, hpsi⟩ :=
      (hInv i d).mp hd
    have hr0 : (0 : ℝ) < (1 / 2 : ℝ) ^ i := by positivity
    have hrsucc : (1 / 2 : ℝ) ^ (i + 1) = (1 / 2 : ℝ) ^ i / 2 := by rw [pow_succ]; ring
    have hPcont : ContinuousOn d.1 (N (i + 1)) := hPpl.continuousOn.mono (hNK (i + 1))
    have hAc : IsCompact (d.1 '' N (i + 1) \ interior K) :=
      ((hNc (i + 1)).image_of_continuousOn hPcont).diff isOpen_interior
    have hAK : d.1 '' N (i + 1) \ interior K ⊆ K \ interior K := by
      rintro x ⟨⟨y, hy, rfl⟩, hxint⟩
      exact ⟨hPmap (hNK (i + 1) hy), hxint⟩
    obtain ⟨p, q, hppl, hpinj, hpmap, hpdich, hpA, hpC, hqpl, hqmap, hqC, hqp, hpdist⟩ :=
      hK.exists_isPLOn_stage_inward_dist_lt hAc hCc hAK hCint
        (h := fun x => (h x, ψ x)) (hh.prodMk hψ)
        (δ := fun w => (1 / 2 : ℝ) ^ i / 4 * ψ w) (continuousOn_const.mul hψ)
        (fun x hx => mul_pos (by positivity) (hψpos x hx))
    have hP'int : (p ∘ d.1) '' N (i + 1) ⊆ interior K := by
      rintro _ ⟨x, hx, rfl⟩
      by_cases hmem : d.1 x ∈ interior K
      · rcases hpdich (d.1 x) (hPmap (hNK (i + 1) hx)) with hc | hc
        · exact hc
        · rw [Function.comp_apply, hc]
          exact hmem
      · exact hpA (d.1 x) ⟨⟨x, hx, rfl⟩, hmem⟩
    have hP'cont : ContinuousOn (p ∘ d.1) (N (i + 1)) :=
      hppl.continuousOn.comp hPcont (hPmap.mono (hNK (i + 1)) Subset.rfl)
    obtain ⟨L, hLc, hLnb, hLK⟩ :=
      exists_compact_between ((hNc (i + 1)).image_of_continuousOn hP'cont) isOpen_interior hP'int
    refine ⟨(p ∘ d.1, d.2.1 ∘ q, L, d.2.2.2 ∪ L), (hInv (i + 1) _).mpr
      ⟨hppl.comp_of_mapsTo hPpl hPmap, hpinj.comp hPinj hPmap, hpmap.comp hPmap,
        hQpl.comp_of_mapsTo hqpl hqmap, hQmap.comp hqmap, ?_, hLc, hLK,
        fun x hx => hLnb ⟨x, hx, rfl⟩, hCc.union hLc, union_subset hCint hLK,
        subset_union_right, ?_, ?_⟩,
      fun x _ hmem => hpC hmem, fun y hmem => congrArg d.2.1 (hqC hmem), subset_union_left⟩
    · intro x hx
      change d.2.1 (q (p (d.1 x))) = x
      rw [hqp (hPmap hx), hQP hx]
    · intro x hx
      change dist (h (p (d.1 x))) (h x) ≤ (1 - (1 / 2 : ℝ) ^ (i + 1)) * ψ x
      have hxK : d.1 x ∈ K := hPmap hx
      have hψx : 0 < ψ x := hψpos x hx
      have hpr : dist ((h (p (d.1 x)), ψ (p (d.1 x))) : M₂ × ℝ) (h (d.1 x), ψ (d.1 x)) <
          (1 / 2 : ℝ) ^ i / 4 * ψ (d.1 x) := hpdist (d.1 x) hxK
      have hprod : dist (h (p (d.1 x))) (h (d.1 x)) ≤
          dist ((h (p (d.1 x)), ψ (p (d.1 x))) : M₂ × ℝ) (h (d.1 x), ψ (d.1 x)) := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      have h1 : dist (h (p (d.1 x))) (h (d.1 x)) < (1 / 2 : ℝ) ^ i / 4 * ψ (d.1 x) :=
        lt_of_le_of_lt hprod hpr
      have h2 : dist (h (d.1 x)) (h x) ≤ (1 - (1 / 2 : ℝ) ^ i) * ψ x := hdist x hx
      have h3 : ψ (d.1 x) ≤ (2 - (1 / 2 : ℝ) ^ i) * ψ x := hpsi x hx
      have h4 : (1 / 2 : ℝ) ^ i / 4 * ψ (d.1 x) ≤
          (1 / 2 : ℝ) ^ i / 4 * ((2 - (1 / 2 : ℝ) ^ i) * ψ x) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : dist (h (p (d.1 x))) (h x) ≤
          dist (h (p (d.1 x))) (h (d.1 x)) + dist (h (d.1 x)) (h x) := dist_triangle _ _ _
      rw [hrsucc]
      nlinarith [mul_nonneg (mul_nonneg hr0.le hr0.le) hψx.le]
    · intro x hx
      change ψ (p (d.1 x)) ≤ (2 - (1 / 2 : ℝ) ^ (i + 1)) * ψ x
      have hxK : d.1 x ∈ K := hPmap hx
      have hψx : 0 < ψ x := hψpos x hx
      have hpr : dist ((h (p (d.1 x)), ψ (p (d.1 x))) : M₂ × ℝ) (h (d.1 x), ψ (d.1 x)) <
          (1 / 2 : ℝ) ^ i / 4 * ψ (d.1 x) := hpdist (d.1 x) hxK
      have hprod : dist (ψ (p (d.1 x))) (ψ (d.1 x)) ≤
          dist ((h (p (d.1 x)), ψ (p (d.1 x))) : M₂ × ℝ) (h (d.1 x), ψ (d.1 x)) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      have h1 : ψ (p (d.1 x)) - ψ (d.1 x) < (1 / 2 : ℝ) ^ i / 4 * ψ (d.1 x) := by
        have habs := le_abs_self (ψ (p (d.1 x)) - ψ (d.1 x))
        rw [← Real.dist_eq] at habs
        linarith [lt_of_le_of_lt hprod hpr]
      have h3 : ψ (d.1 x) ≤ (2 - (1 / 2 : ℝ) ^ i) * ψ x := hpsi x hx
      have h4 : (1 + (1 / 2 : ℝ) ^ i / 4) * ψ (d.1 x) ≤
          (1 + (1 / 2 : ℝ) ^ i / 4) * ((2 - (1 / 2 : ℝ) ^ i) * ψ x) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      rw [hrsucc]
      nlinarith [mul_nonneg (mul_nonneg hr0.le hr0.le) hψx.le]
  choose! next hnextInv hnextP hnextQ hnextC using hstep
  obtain ⟨F, hF0, hFsucc⟩ :
      ∃ F : ℕ → (M₁ → M₁) × (M₁ → M₁) × Set M₁ × Set M₁,
        F 0 = (id, id, ∅, ∅) ∧ ∀ j, F (j + 1) = next j (F j) :=
    ⟨fun i => Nat.rec (id, id, ∅, ∅) (fun j dj => next j dj) i, rfl, fun _ => rfl⟩
  have hFinv : ∀ i, Inv i (F i) := by
    intro i
    induction i with
    | zero => rw [hF0]; exact hbase
    | succ j ih =>
      rw [hFsucc j]
      exact hnextInv j (F j) ih
  have hall := fun i => (hInv i (F i)).mp (hFinv i)
  have hLC : ∀ i, (F i).2.2.1 ⊆ (F i).2.2.2 := by
    intro i
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hx, -⟩ := hall i
    exact hx
  have hPN : ∀ i, MapsTo (F i).1 (N i) (interior (F i).2.2.1) := by
    intro i
    obtain ⟨-, -, -, -, -, -, -, -, hx, -⟩ := hall i
    exact hx
  have hCmono : ∀ i j, i ≤ j → (F i).2.2.2 ⊆ (F j).2.2.2 := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact Subset.rfl
    | succ k hk ih =>
      refine ih.trans ?_
      have hgrow := hnextC k (F k) (hFinv k)
      rwa [← hFsucc k] at hgrow
  have hPstab : ∀ i j, i ≤ j → EqOn (F j).1 (F i).1 (N i) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ k hk ih =>
      intro x hx
      have hfix : (F (k + 1)).1 x = (F k).1 x := by
        have hmem : (F k).1 x ∈ (F k).2.2.2 := by
          rw [ih hx]
          exact hCmono i k hk (hLC i (interior_subset (hPN i hx)))
        have hlink := hnextP k (F k) (hFinv k) x (hNK i hx) hmem
        rwa [← hFsucc k] at hlink
      rw [hfix]
      exact ih hx
  have hQstab : ∀ i j, i ≤ j →
      EqOn (F j).2.1 (F i).2.1 (interior (F i).2.2.1) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ k hk ih =>
      intro y hy
      have hmem : y ∈ (F k).2.2.2 := hCmono i k hk (hLC i (interior_subset hy))
      have hlink := hnextQ k (F k) (hFinv k) y hmem
      rw [hFsucc k, hlink]
      exact ih hy
  have hGK : ∀ i, interior (F i).2.2.1 ⊆ K := by
    intro i
    obtain ⟨-, -, -, -, -, -, -, hx, -⟩ := hall i
    exact interior_subset.trans (hx.trans interior_subset)
  refine exists_isPLOn_injOn_leftInvOn_dist_lt_of_stage_family (N := N)
    (G := fun i => interior (F i).2.2.1) (P := fun i => (F i).1) (Q := fun i => (F i).2.1)
    hNmono hNK hNcover hNnhds (fun _ => isOpen_interior) ?_ hPN ?_ ?_ ?_ ?_ ?_ ?_ hPstab hQstab
  · intro i
    obtain ⟨-, -, -, -, -, -, -, hx, -⟩ := hall i
    exact interior_subset.trans hx
  · exact fun i => (hall i).1
  · exact fun i => (hall i).2.1
  · intro i
    obtain ⟨-, -, -, hx, -⟩ := hall i
    exact hx.mono_of_isOpen isOpen_interior (hGK i)
  · intro i
    obtain ⟨-, -, -, -, hx, -⟩ := hall i
    exact hx.mono_left (hGK i)
  · intro i
    obtain ⟨-, -, -, -, -, hx, -⟩ := hall i
    exact hx
  · intro i x hx
    have hxK : x ∈ K := hNK i hx
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hd, -⟩ := hall i
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ i := by positivity
    nlinarith [hd x hxK, mul_pos hpos (hψpos x hxK)]

end DifferentialGeometry.Topology.PiecewiseLinear
