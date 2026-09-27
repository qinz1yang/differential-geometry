/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteHomeomorphTower
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTowerExistence
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldPointMove

open Set Topology Filter Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

structure CompactCoreExhaustion (X : Type u) [TopologicalSpace X] where
  core : ℕ → Set X
  monotone_core : Monotone core
  isCompact_core : ∀ i, IsCompact (core i)
  core_succ_mem_nhds : ∀ i ⦃x⦄, x ∈ core i → core (i + 1) ∈ 𝓝 x
  iUnion_core : ⋃ i, core i = Set.univ

namespace CompactCoreExhaustion

variable {X : Type u} [TopologicalSpace X] (D : CompactCoreExhaustion X)

theorem core_subset_succ (i : ℕ) : D.core i ⊆ D.core (i + 1) :=
  D.monotone_core (Nat.le_succ i)

theorem core_subset_interior_succ (i : ℕ) : D.core i ⊆ interior (D.core (i + 1)) :=
  fun _ hx => mem_interior_iff_mem_nhds.mpr (D.core_succ_mem_nhds i hx)

theorem exists_mem_core (x : X) : ∃ i, x ∈ D.core i :=
  mem_iUnion.mp (D.iUnion_core.symm ▸ Set.mem_univ x)

theorem exists_core_of_isCompact {C : Set X} (hC : IsCompact C) :
    ∃ i, C ⊆ D.core i := by
  let O : ℕ → Set X := fun i => interior (D.core (i + 1))
  have hcover : C ⊆ ⋃ i, O i := by
    intro x hx
    obtain ⟨i, hxi⟩ := D.exists_mem_core x
    exact mem_iUnion.mpr ⟨i, D.core_subset_interior_succ i hxi⟩
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover O (fun _ => isOpen_interior) hcover
  refine ⟨s.sup id + 1, fun x hx => ?_⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
  exact D.monotone_core (Nat.add_le_add_right (Finset.le_sup hi) 1) (interior_subset hxi)

theorem core_eventually {C : Set X} (hC : IsCompact C) :
    ∀ᶠ i in atTop, C ⊆ D.core i := by
  obtain ⟨i, hi⟩ := D.exists_core_of_isCompact hC
  exact eventually_atTop.mpr ⟨i, fun j hij => hi.trans (D.monotone_core hij)⟩

open Classical in
noncomputable def coreIndex (D : CompactCoreExhaustion X) (x : X) : ℕ :=
  Nat.find (D.exists_mem_core x)

open Classical in
theorem mem_core_coreIndex (x : X) : x ∈ D.core (D.coreIndex x) :=
  Nat.find_spec (D.exists_mem_core x)

open Classical in
theorem coreIndex_le {i : ℕ} {x : X} (hx : x ∈ D.core i) : D.coreIndex x ≤ i :=
  Nat.find_min' (D.exists_mem_core x) hx

theorem shell_nonempty [T2Space X] [PreconnectedSpace X] [NoncompactSpace X]
    (h0 : (D.core 0).Nonempty) (i : ℕ) :
    (interior (D.core (i + 1)) \ D.core i).Nonempty := by
  have hi : (D.core i).Nonempty :=
    h0.mono (D.monotone_core (Nat.zero_le i))
  by_contra h
  have hreverse : interior (D.core (i + 1)) ⊆ D.core i := by
    intro x hx
    by_contra hxi
    exact h ⟨x, hx, hxi⟩
  have heq : D.core i = interior (D.core (i + 1)) :=
    Subset.antisymm (D.core_subset_interior_succ i) hreverse
  have hopen : IsOpen (D.core i) := heq.symm ▸ isOpen_interior
  have hclosed : IsClosed (D.core i) := (D.isCompact_core i).isClosed
  exact (D.isCompact_core i).ne_univ (IsClopen.eq_univ ⟨hclosed, hopen⟩ hi)

end CompactCoreExhaustion

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [HasGroupoid X (plGroupoid n)]

namespace LocallyFinitePieceTower

def compactCoreExhaustion
    (T : LocallyFinitePieceTower n X (Set.univ : Set X)) (offset : ℕ) :
    CompactCoreExhaustion X where
  core i := T.coreSpace (offset + 2 * i)
  monotone_core := by
    intro i j hij
    exact T.core_space_monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hij) offset)
  isCompact_core i := T.isCompact_core_space (offset + 2 * i)
  core_succ_mem_nhds i x hx := by
    have hxN : x ∈ T.N (offset + 2 * i) :=
      T.core_space_subset (offset + 2 * i) hx
    simpa only [nhdsWithin_univ, Nat.mul_succ, Nat.add_assoc] using
      T.core_space_mem_nhdsWithin hxN
  iUnion_core := by
    apply Subset.antisymm
    · exact subset_univ _
    · intro x _
      obtain ⟨i, hxi⟩ := T.exists_mem_core_space (Set.mem_univ x)
      exact mem_iUnion.mpr ⟨i,
        T.core_space_monotone (by omega : i ≤ offset + 2 * i) hxi⟩

omit [HasGroupoid X (plGroupoid n)] in
theorem compact_subset_compactCoreExhaustion_core
    (T : LocallyFinitePieceTower n X (Set.univ : Set X)) {C : Set X} (hC : IsCompact C) :
    ∃ offset, C ⊆ (T.compactCoreExhaustion offset).core 0 := by
  obtain ⟨offset, hCoffset⟩ := T.exists_core_of_isCompact hC (subset_univ C)
  change C ⊆ T.coreSpace offset at hCoffset
  exact ⟨offset, by simpa only [compactCoreExhaustion, mul_zero, add_zero] using hCoffset⟩

end LocallyFinitePieceTower

theorem image_eq_of_homeomorph_eqOn_compl_of_subset
    (h : X ≃ₜ X) {C A : Set X} (hfix : EqOn h id Cᶜ) (hCA : C ⊆ A) :
    h '' A = A := by
  apply Subset.antisymm
  · rintro y ⟨x, hxA, rfl⟩
    by_cases hxC : x ∈ C
    · apply hCA
      by_contra hnot
      have hfixed : h (h x) = h x := hfix hnot
      have heq : h x = x := h.injective hfixed
      exact hnot (heq.symm ▸ hxC)
    · rw [hfix hxC]
      exact hxA
  · intro y hyA
    refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
    by_cases hyC : y ∈ C
    · apply hCA
      by_contra hnot
      have hfixed : h (h.symm y) = h.symm y := hfix hnot
      have heq : y = h.symm y := (h.apply_symm_apply y).symm.trans hfixed
      exact hnot (heq ▸ hyC)
    · have hfixed : h y = y := hfix hyC
      have heq : h.symm y = y := by
        apply h.injective
        rw [h.apply_symm_apply, hfixed]
      simpa only [heq] using hyA

structure CompatiblePLHomeomorphExhaustion (D : CompactCoreExhaustion X) where
  stage : ℕ → X ≃ₜ X
  isPL_stage : ∀ i, IsPL n n (stage i)
  image_core : ∀ i, stage i '' D.core i = D.core i
  eqOn_core : ∀ i, EqOn (stage (i + 1)) (stage i) (D.core i)

structure SupportedPLHomeomorphSystem (D : CompactCoreExhaustion X) where
  support : ℕ → Set X
  point : ℕ → X
  step : ℕ → X ≃ₜ X
  isCompact_support : ∀ i, IsCompact (support i)
  support_subset_shell : ∀ i, support i ⊆ interior (D.core (i + 1)) \ D.core i
  isPL_step : ∀ i, IsPL n n (step i)
  moves_point : ∀ i, step i (point i) ≠ point i
  eqOn_compl : ∀ i, EqOn (step i) id (support i)ᶜ

namespace SupportedPLHomeomorphSystem

variable {D : CompactCoreExhaustion X}

omit [HasGroupoid X (plGroupoid n)] in
theorem point_mem_support (S : SupportedPLHomeomorphSystem (n := n) D) (i : ℕ) :
    S.point i ∈ S.support i := by
  by_contra hi
  exact S.moves_point i (S.eqOn_compl i hi)

omit [HasGroupoid X (plGroupoid n)] in
theorem point_mem_interior_succ (S : SupportedPLHomeomorphSystem (n := n) D) (i : ℕ) :
    S.point i ∈ interior (D.core (i + 1)) :=
  (S.support_subset_shell i (S.point_mem_support i)).1

omit [HasGroupoid X (plGroupoid n)] in
theorem point_not_mem_core (S : SupportedPLHomeomorphSystem (n := n) D) (i : ℕ) :
    S.point i ∉ D.core i :=
  (S.support_subset_shell i (S.point_mem_support i)).2

omit [HasGroupoid X (plGroupoid n)] in
theorem fixes_core (S : SupportedPLHomeomorphSystem (n := n) D) (i : ℕ) :
    EqOn (S.step i) id (D.core i) := by
  intro x hx
  apply S.eqOn_compl i
  exact fun hxS => (S.support_subset_shell i hxS).2 hx

omit [HasGroupoid X (plGroupoid n)] in
theorem image_core (S : SupportedPLHomeomorphSystem (n := n) D) (i j : ℕ) :
    S.step i '' D.core j = D.core j := by
  by_cases hji : j ≤ i
  · exact (S.fixes_core i).mono (D.monotone_core hji) |>.image_eq_self
  · exact image_eq_of_homeomorph_eqOn_compl_of_subset (S.step i) (S.eqOn_compl i)
      ((S.support_subset_shell i).trans
        (sdiff_subset.trans (interior_subset.trans
          (D.monotone_core (Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hji))))))

def partialHomeomorph (S : SupportedPLHomeomorphSystem (n := n) D) : ℕ → X ≃ₜ X
  | 0 => Homeomorph.refl X
  | i + 1 => (S.partialHomeomorph i).trans (S.step i)

omit [HasGroupoid X (plGroupoid n)] in
@[simp]
theorem partialHomeomorph_zero (S : SupportedPLHomeomorphSystem (n := n) D) :
    S.partialHomeomorph 0 = Homeomorph.refl X := rfl

omit [HasGroupoid X (plGroupoid n)] in
@[simp]
theorem partialHomeomorph_succ_apply (S : SupportedPLHomeomorphSystem (n := n) D)
    (i : ℕ) (x : X) :
    S.partialHomeomorph (i + 1) x = S.step i (S.partialHomeomorph i x) := rfl

omit [HasGroupoid X (plGroupoid n)] in
theorem isPL_partialHomeomorph (S : SupportedPLHomeomorphSystem (n := n) D) :
    ∀ i, IsPL n n (S.partialHomeomorph i)
  | 0 => isPL_id
  | i + 1 => (S.isPL_step i).comp (S.isPL_partialHomeomorph i)

omit [HasGroupoid X (plGroupoid n)] in
theorem image_partialHomeomorph_core (S : SupportedPLHomeomorphSystem (n := n) D)
    (i j : ℕ) : S.partialHomeomorph i '' D.core j = D.core j := by
  induction i with
  | zero =>
      change (id : X → X) '' D.core j = D.core j
      exact image_id (D.core j)
  | succ i ih =>
      calc
        S.partialHomeomorph (i + 1) '' D.core j =
            S.step i '' (S.partialHomeomorph i '' D.core j) := by
          apply Subset.antisymm
          · rintro y ⟨x, hx, rfl⟩
            exact ⟨S.partialHomeomorph i x, ⟨x, hx, rfl⟩, rfl⟩
          · rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨x, hx, rfl⟩
        _ = D.core j := by rw [ih, S.image_core]

omit [HasGroupoid X (plGroupoid n)] in
theorem eqOn_partialHomeomorph_succ (S : SupportedPLHomeomorphSystem (n := n) D)
    (i : ℕ) : EqOn (S.partialHomeomorph (i + 1)) (S.partialHomeomorph i) (D.core i) := by
  intro x hx
  rw [S.partialHomeomorph_succ_apply]
  apply S.fixes_core i
  rw [← S.image_partialHomeomorph_core i i]
  exact ⟨x, hx, rfl⟩

def toCompatibleExhaustion (S : SupportedPLHomeomorphSystem (n := n) D) :
    CompatiblePLHomeomorphExhaustion (n := n) D where
  stage := S.partialHomeomorph
  isPL_stage := S.isPL_partialHomeomorph
  image_core i := S.image_partialHomeomorph_core i i
  eqOn_core := S.eqOn_partialHomeomorph_succ

omit [HasGroupoid X (plGroupoid n)] in
theorem pairwise_disjoint_support (S : SupportedPLHomeomorphSystem (n := n) D) :
    Pairwise (fun i j => Disjoint (S.support i) (S.support j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact (S.support_subset_shell j hxj).2
      (D.monotone_core (Nat.succ_le_iff.mpr hij')
        (interior_subset (S.support_subset_shell i hxi).1))
  · exact (S.support_subset_shell i hxi).2
      (D.monotone_core (Nat.succ_le_iff.mpr hji')
        (interior_subset (S.support_subset_shell j hxj).1))

omit [HasGroupoid X (plGroupoid n)] in
theorem locallyFinite_support (S : SupportedPLHomeomorphSystem (n := n) D) :
    LocallyFinite S.support := by
  intro x
  obtain ⟨k, hxk⟩ := D.exists_mem_core x
  refine ⟨D.core (k + 1), D.core_succ_mem_nhds k hxk, (Set.finite_Iic k).subset ?_⟩
  intro i hi
  by_contra hik
  have hki : k + 1 ≤ i := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hik)
  obtain ⟨y, hyS, hycore⟩ := hi
  exact (S.support_subset_shell i hyS).2 (D.monotone_core hki hycore)

omit [HasGroupoid X (plGroupoid n)] in
theorem injective_point (S : SupportedPLHomeomorphSystem (n := n) D) :
    Function.Injective S.point := by
  intro i j hij
  by_contra hne
  have hdis := Set.disjoint_left.mp (S.pairwise_disjoint_support hne)
  apply hdis (S.point_mem_support i)
  rw [hij]
  exact S.point_mem_support j

omit [HasGroupoid X (plGroupoid n)] in
theorem step_ne_refl (S : SupportedPLHomeomorphSystem (n := n) D) (i : ℕ) :
    S.step i ≠ Homeomorph.refl X := by
  intro hi
  exact S.moves_point i (by rw [hi]; rfl)

omit [HasGroupoid X (plGroupoid n)] in
theorem stage_succ_ne_stage (S : SupportedPLHomeomorphSystem (n := n) D) (i : ℕ) :
    S.toCompatibleExhaustion.stage (i + 1) ≠ S.toCompatibleExhaustion.stage i := by
  intro hi
  let x := (S.partialHomeomorph i).symm (S.point i)
  have hix := congrArg (fun f : X ≃ₜ X => f x) hi
  change S.step i (S.partialHomeomorph i x) = S.partialHomeomorph i x at hix
  have hx : S.partialHomeomorph i x = S.point i :=
    (S.partialHomeomorph i).apply_symm_apply (S.point i)
  exact S.moves_point i (by simpa only [hx] using hix)

omit [HasGroupoid X (plGroupoid n)] in
theorem partialHomeomorph_point (S : SupportedPLHomeomorphSystem (n := n) D) (i : ℕ) :
    S.partialHomeomorph i (S.point i) = S.point i := by
  have haux : ∀ k, k ≤ i → S.partialHomeomorph k (S.point i) = S.point i := by
    intro k hki
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [S.partialHomeomorph_succ_apply, ih (Nat.le_trans (Nat.le_succ k) hki)]
        apply S.eqOn_compl k
        intro hpoint
        exact S.point_not_mem_core i
          (D.monotone_core hki (interior_subset (S.support_subset_shell k hpoint).1))
  exact haux i le_rfl

end SupportedPLHomeomorphSystem

namespace CompatiblePLHomeomorphExhaustion

variable {D : CompactCoreExhaustion X}

omit [HasGroupoid X (plGroupoid n)] in
theorem eqOn_core_of_le (H : CompatiblePLHomeomorphExhaustion (n := n) D)
    {i j : ℕ} (hij : i ≤ j) : EqOn (H.stage j) (H.stage i) (D.core i) := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ j hij ih =>
      intro x hx
      exact (H.eqOn_core j (D.monotone_core hij hx)).trans (ih hx)

omit [HasGroupoid X (plGroupoid n)] in
theorem image_stage_core_of_le (H : CompatiblePLHomeomorphExhaustion (n := n) D)
    {i j : ℕ} (hij : i ≤ j) : H.stage j '' D.core i = D.core i := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [H.eqOn_core_of_le hij hx]
    rw [← H.image_core i]
    exact ⟨x, hx, rfl⟩
  · intro y hy
    have hy' : y ∈ H.stage i '' D.core i := by
      rw [H.image_core i]
      exact hy
    obtain ⟨x, hx, rfl⟩ := hy'
    exact ⟨x, hx, H.eqOn_core_of_le hij hx⟩

noncomputable def limitMap (H : CompatiblePLHomeomorphExhaustion (n := n) D) : X → X :=
  fun x => H.stage (D.coreIndex x) x

omit [HasGroupoid X (plGroupoid n)] in
theorem limitMap_eq_stage (H : CompatiblePLHomeomorphExhaustion (n := n) D)
    {i : ℕ} {x : X} (hx : x ∈ D.core i) : H.limitMap x = H.stage i x :=
  (H.eqOn_core_of_le (D.coreIndex_le hx) (D.mem_core_coreIndex x)).symm

omit [HasGroupoid X (plGroupoid n)] in
theorem image_limitMap_core (H : CompatiblePLHomeomorphExhaustion (n := n) D) (i : ℕ) :
    H.limitMap '' D.core i = D.core i := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [H.limitMap_eq_stage hx]
    rw [← H.image_core i]
    exact ⟨x, hx, rfl⟩
  · intro y hy
    have hy' : y ∈ H.stage i '' D.core i := by
      rw [H.image_core i]
      exact hy
    obtain ⟨x, hx, rfl⟩ := hy'
    exact ⟨x, hx, H.limitMap_eq_stage hx⟩

omit [HasGroupoid X (plGroupoid n)] in
theorem isPL_limitMap (H : CompatiblePLHomeomorphExhaustion (n := n) D) :
    IsPL n n H.limitMap := by
  intro x
  obtain ⟨i, hxi⟩ := D.exists_mem_core x
  apply piecewiseAffineProperty_localInvariantProp.liftPropAt_congr_of_eventuallyEq
    (H.isPL_stage (i + 1) x)
  filter_upwards [D.core_succ_mem_nhds i hxi] with y hy
  exact H.limitMap_eq_stage hy

noncomputable def symm (H : CompatiblePLHomeomorphExhaustion (n := n) D) :
    CompatiblePLHomeomorphExhaustion (n := n) D where
  stage i := (H.stage i).symm
  isPL_stage i := isPL_symm_of_homeomorph (H.isPL_stage i)
  image_core i := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hx' : x ∈ H.stage i '' D.core i := by
        rw [H.image_core i]
        exact hx
      obtain ⟨z, hz, hzx⟩ := hx'
      have hzy : z = (H.stage i).symm x := by
        apply (H.stage i).injective
        rw [hzx, (H.stage i).apply_symm_apply]
      exact hzy ▸ hz
    · intro y hy
      refine ⟨H.stage i y, ?_, (H.stage i).symm_apply_apply y⟩
      rw [← H.image_core i]
      exact ⟨y, hy, rfl⟩
  eqOn_core i := by
    intro y hy
    let x := (H.stage i).symm y
    have hx : x ∈ D.core i := by
      rw [← H.image_core i] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      simpa only [x, ← hzy, (H.stage i).symm_apply_apply] using hz
    have heq := H.eqOn_core i hx
    apply (H.stage (i + 1)).injective
    rw [(H.stage (i + 1)).apply_symm_apply]
    simpa only [x, (H.stage i).apply_symm_apply] using heq.symm

theorem symm_limitMap_leftInverse (H : CompatiblePLHomeomorphExhaustion (n := n) D) :
    Function.LeftInverse H.symm.limitMap H.limitMap := by
  intro x
  obtain ⟨i, hxi⟩ := D.exists_mem_core x
  rw [H.limitMap_eq_stage hxi]
  have himage : H.stage i x ∈ D.core i := by
    rw [← H.image_core i]
    exact ⟨x, hxi, rfl⟩
  rw [H.symm.limitMap_eq_stage himage]
  exact (H.stage i).symm_apply_apply x

theorem symm_limitMap_rightInverse (H : CompatiblePLHomeomorphExhaustion (n := n) D) :
    Function.RightInverse H.symm.limitMap H.limitMap := by
  intro y
  obtain ⟨i, hyi⟩ := D.exists_mem_core y
  rw [H.symm.limitMap_eq_stage hyi]
  have himage : (H.stage i).symm y ∈ D.core i := by
    rw [← H.symm.image_core i]
    exact ⟨y, hyi, rfl⟩
  change H.limitMap ((H.stage i).symm y) = y
  rw [H.limitMap_eq_stage himage]
  exact (H.stage i).apply_symm_apply y

noncomputable def limitHomeomorph (H : CompatiblePLHomeomorphExhaustion (n := n) D) :
    X ≃ₜ X :=
  Homeomorph.mk
    ⟨H.limitMap, H.symm.limitMap, H.symm_limitMap_leftInverse,
      H.symm_limitMap_rightInverse⟩
    (continuous_iff_continuousAt.mpr fun x => by
      simpa only [continuousWithinAt_univ] using (H.isPL_limitMap x).continuousWithinAt)
    (continuous_iff_continuousAt.mpr fun x => by
      simpa only [continuousWithinAt_univ] using (H.symm.isPL_limitMap x).continuousWithinAt)

theorem isPL_limitHomeomorph (H : CompatiblePLHomeomorphExhaustion (n := n) D) :
    IsPL n n H.limitHomeomorph := H.isPL_limitMap

theorem limitHomeomorph_eq_stage (H : CompatiblePLHomeomorphExhaustion (n := n) D)
    {i : ℕ} {x : X} (hx : x ∈ D.core i) : H.limitHomeomorph x = H.stage i x :=
  H.limitMap_eq_stage hx

theorem image_limitHomeomorph_core (H : CompatiblePLHomeomorphExhaustion (n := n) D)
    (i : ℕ) : H.limitHomeomorph '' D.core i = D.core i :=
  H.image_limitMap_core i

theorem eventually_eqOn_limitHomeomorph_of_isCompact
    (H : CompatiblePLHomeomorphExhaustion (n := n) D) {C : Set X} (hC : IsCompact C) :
    ∀ᶠ i in atTop, EqOn H.limitHomeomorph (H.stage i) C := by
  filter_upwards [D.core_eventually hC] with i hi
  exact fun x hx => H.limitHomeomorph_eq_stage (hi hx)

end CompatiblePLHomeomorphExhaustion

namespace SupportedPLHomeomorphSystem

variable {D : CompactCoreExhaustion X}

theorem limitHomeomorph_moves_point (S : SupportedPLHomeomorphSystem (n := n) D) (i : ℕ) :
    S.toCompatibleExhaustion.limitHomeomorph (S.point i) ≠ S.point i := by
  rw [S.toCompatibleExhaustion.limitHomeomorph_eq_stage
    (interior_subset (S.point_mem_interior_succ i))]
  change S.step i (S.partialHomeomorph i (S.point i)) ≠ S.point i
  rw [S.partialHomeomorph_point]
  exact S.moves_point i

end SupportedPLHomeomorphSystem

open Classical in
theorem CompactCoreExhaustion.exists_supportedPLHomeomorphSystem
    {m : ℕ} {Y : Type u} [MetricSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) Y] [HasGroupoid Y (plGroupoid m)]
    (D : CompactCoreExhaustion Y) (hn : 0 < m)
    (hstrict : ∀ i, (interior (D.core (i + 1)) \ D.core i).Nonempty) :
    ∃ S : SupportedPLHomeomorphSystem (n := m) D,
      LocallyFinite S.support ∧
      Pairwise (fun i j => Disjoint (S.support i) (S.support j)) ∧
      (∀ i, S.step i ≠ Homeomorph.refl Y) ∧
      (∀ i, S.toCompatibleExhaustion.stage (i + 1) ≠
        S.toCompatibleExhaustion.stage i) := by
  choose p hp using hstrict
  have hclosed (i : ℕ) : IsClosed (D.core i) := (D.isCompact_core i).isClosed
  have hmove (i : ℕ) :
      ∃ (C : Set Y) (h : Y ≃ₜ Y),
        IsCompact C ∧ C ⊆ interior (D.core (i + 1)) \ D.core i ∧
        IsPL m m h ∧ IsPL m m h.symm ∧ h (p i) ≠ p i ∧
        EqOn h id Cᶜ := by
    obtain ⟨C, h, hC, hCshell, hh, hh', hne, hfix, -, -, -⟩ :=
      exists_isPL_homeomorph_moves_point_dist_lt_eqOn hn (hclosed i) isOpen_interior
        (hp i).1 (hp i).2 (by norm_num : (0 : ℝ) < 1)
    exact ⟨C, h, hC, hCshell, hh, hh', hne, hfix⟩
  choose C h hC hCshell hh hh' hne hfix using hmove
  let S : SupportedPLHomeomorphSystem (n := m) D :=
    { support := C
      point := p
      step := h
      isCompact_support := hC
      support_subset_shell := hCshell
      isPL_step := hh
      moves_point := hne
      eqOn_compl := hfix }
  exact ⟨S, S.locallyFinite_support, S.pairwise_disjoint_support,
    S.step_ne_refl, S.stage_succ_ne_stage⟩

open Classical in
theorem exists_noncompact_infinite_supported_PL_modification_three :
    ∃ (G : Set (EuclideanSpace ℝ (Fin 3)))
        (T : LocallyFinitePieceTower 3 (EuclideanSpace ℝ (Fin 3)) Set.univ)
        (D : CompactCoreExhaustion (EuclideanSpace ℝ (Fin 3)))
        (S : SupportedPLHomeomorphSystem (n := 3) D),
      G.Nonempty ∧ IsCompact G ∧
      (∀ i, IsCombinatorialManifoldWithBoundary 3 (T.piece i).piece.complex) ∧
      G ⊆ D.core 0 ∧ LocallyFinite S.support ∧
      Pairwise (fun i j => Disjoint (S.support i) (S.support j)) ∧
      Function.Injective S.point ∧
      (∀ i, S.step i ≠ Homeomorph.refl (EuclideanSpace ℝ (Fin 3))) ∧
      (∀ i, S.toCompatibleExhaustion.stage (i + 1) ≠
        S.toCompatibleExhaustion.stage i) ∧
      IsPL 3 3 S.toCompatibleExhaustion.limitHomeomorph ∧
      (∀ i, S.toCompatibleExhaustion.limitHomeomorph (S.point i) ≠ S.point i) ∧
      (∀ i, EqOn (S.step i) id G) ∧
      EqOn S.toCompatibleExhaustion.limitHomeomorph id G ∧
      (∀ C : Set (EuclideanSpace ℝ (Fin 3)), IsCompact C →
        ∀ᶠ i in atTop,
          EqOn S.toCompatibleExhaustion.limitHomeomorph
            (S.toCompatibleExhaustion.stage i) C) := by
  let E := EuclideanSpace ℝ (Fin 3)
  let e : E := EuclideanSpace.single (0 : Fin 3) 1
  let G : Set E := segment ℝ 0 e
  have hG : IsCompact G := by
    change IsCompact (segment ℝ (0 : E) e)
    rw [← convexHull_pair]
    exact (Set.toFinite {0, e}).isCompact_convexHull ℝ
  have hGne : G.Nonempty := ⟨0, left_mem_segment ℝ 0 e⟩
  obtain ⟨T, hT⟩ :=
    exists_locallyFinitePieceTower_of_isOpen (m := 2) (X := E) isOpen_univ
  obtain ⟨offset, hGcore⟩ := T.compact_subset_compactCoreExhaustion_core hG
  let D := T.compactCoreExhaustion offset
  have hD0 : (D.core 0).Nonempty := hGne.mono hGcore
  have hstrict (i : ℕ) : (interior (D.core (i + 1)) \ D.core i).Nonempty :=
    D.shell_nonempty hD0 i
  obtain ⟨S, hSloc, hSdis, hSne, hstage⟩ :=
    D.exists_supportedPLHomeomorphSystem (m := 3) (by omega) hstrict
  refine ⟨G, T, D, S, hGne, hG, hT, hGcore, hSloc, hSdis, S.injective_point,
    hSne, hstage, S.toCompatibleExhaustion.isPL_limitHomeomorph,
    S.limitHomeomorph_moves_point, ?_, ?_, ?_⟩
  · intro i x hx
    exact S.fixes_core i (D.monotone_core (Nat.zero_le i) (hGcore hx))
  · intro x hx
    rw [S.toCompatibleExhaustion.limitHomeomorph_eq_stage (hGcore hx)]
    rfl
  · intro C hC
    exact S.toCompatibleExhaustion.eventually_eqOn_limitHomeomorph_of_isCompact hC

end DifferentialGeometry.Topology.PiecewiseLinear
