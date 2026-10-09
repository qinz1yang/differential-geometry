import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

noncomputable section

open Set Filter Metric Asymptotics
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

theorem indicator_eventuallyEq_of_mem {E G : Type*} [TopologicalSpace E] [Zero G] {U : Set E}
    (hU : IsOpen U) (g : E → G) {x : E} (hx : x ∈ U) : U.indicator g =ᶠ[𝓝 x] g := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact Set.indicator_of_mem hy g

private theorem hasFDerivAt_indicator_zero_of_sq_decay {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] {U : Set E} {g : E → G}
    {C : ℝ} (hC : 0 ≤ C) (hg : ∀ y ∈ U, ‖g y‖ ≤ C * infDist y Uᶜ ^ 2) {x : E} (hx : x ∉ U) :
    HasFDerivAt (U.indicator g) (0 : E →L[ℝ] G) x := by
  have hO : U.indicator g =O[𝓝 x] fun y => ‖y - x‖ ^ 2 := by
    refine IsBigO.of_bound C (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg ‖y - x‖)]
    by_cases hy : y ∈ U
    · rw [Set.indicator_of_mem hy]
      have hd : infDist y Uᶜ ≤ ‖y - x‖ := by
        rw [← dist_eq_norm_sub]
        exact infDist_le_dist_of_mem (Set.mem_compl hx)
      exact (hg y hy).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ infDist_nonneg hd 2) hC)
    · rw [Set.indicator_of_notMem hy, norm_zero]
      exact mul_nonneg hC (sq_nonneg _)
  exact hO.hasFDerivAt (by decide)

private theorem continuousMultilinearMap_curryLeft_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) :
    (0 : E [×(j + 1)]→L[ℝ] F).curryLeft = 0 := by
  ext v m
  rfl

theorem hasFTaylorSeriesUpTo_indicator_of_quadratic_jet_decay {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (k : ℕ) (hf : ContDiffOn ℝ (k : ℕ∞ω) f U)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j, j ≤ k → ∀ x ∈ U, ‖iteratedFDeriv ℝ j f x‖ ≤ C * infDist x Uᶜ ^ 2) :
    HasFTaylorSeriesUpTo ((k : ℕ∞) : ℕ∞ω) (U.indicator f)
      (fun x j => U.indicator (fun y => iteratedFDeriv ℝ j f y) x :
        E → FormalMultilinearSeries ℝ E F) := by
  have hs : HasFTaylorSeriesUpToOn ((k : ℕ∞) : ℕ∞ω) f (ftaylorSeries ℝ f) U :=
    (hf.ftaylorSeriesWithin hU.uniqueDiffOn).congr_series fun j _ x hx =>
      iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) j hU hx
  refine ⟨fun x => ?_, fun j hj x => ?_, fun j hj => ?_⟩
  · change (U.indicator (fun y => iteratedFDeriv ℝ 0 f y) x).curry0 = U.indicator f x
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      rfl
  · change HasFDerivAt (U.indicator fun y => iteratedFDeriv ℝ j f y)
      (U.indicator (fun y => iteratedFDeriv ℝ (j + 1) f y) x).curryLeft x
    have hjk : j < k := Nat.cast_lt.mp (hj : (j : ℕ∞ω) < (k : ℕ∞ω))
    by_cases hx : x ∈ U
    · have h1 : HasFDerivAt (fun y => iteratedFDeriv ℝ j f y)
          (iteratedFDeriv ℝ (j + 1) f x).curryLeft x :=
        (hs.fderivWithin j hj x hx).hasFDerivAt (hU.mem_nhds hx)
      rw [Set.indicator_of_mem hx]
      exact h1.congr_of_eventuallyEq (indicator_eventuallyEq_of_mem hU _ hx)
    · rw [Set.indicator_of_notMem hx, continuousMultilinearMap_curryLeft_zero]
      exact hasFDerivAt_indicator_zero_of_sq_decay
        (g := fun y => iteratedFDeriv ℝ j f y) hC (hbound j hjk.le) hx
  · change Continuous (U.indicator fun y => iteratedFDeriv ℝ j f y)
    have hjk : j ≤ k := Nat.cast_le.mp (hj : (j : ℕ∞ω) ≤ (k : ℕ∞ω))
    refine continuous_iff_continuousAt.mpr fun x => ?_
    by_cases hx : x ∈ U
    · have h1 : ContinuousAt (fun y => iteratedFDeriv ℝ j f y) x :=
        (hs.cont j hj).continuousAt (hU.mem_nhds hx)
      exact h1.congr_of_eventuallyEq (indicator_eventuallyEq_of_mem hU _ hx)
    · exact (hasFDerivAt_indicator_zero_of_sq_decay
        (g := fun y => iteratedFDeriv ℝ j f y) hC (hbound j hjk) hx).continuousAt

theorem contDiff_indicator_of_quadratic_jet_decay {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (k : ℕ) (hf : ContDiffOn ℝ (k : ℕ∞ω) f U)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j, j ≤ k → ∀ x ∈ U, ‖iteratedFDeriv ℝ j f x‖ ≤ C * infDist x Uᶜ ^ 2) :
    ContDiff ℝ (k : ℕ∞ω) (U.indicator f) ∧
      ∀ j, j ≤ k → ∀ x, iteratedFDeriv ℝ j (U.indicator f) x =
        U.indicator (fun y => iteratedFDeriv ℝ j f y) x := by
  have hp := hasFTaylorSeriesUpTo_indicator_of_quadratic_jet_decay hU k hf hC hbound
  have hcd : ContDiff ℝ ((k : ℕ∞) : ℕ∞ω) (U.indicator f) := hp.contDiff
  refine ⟨hcd, fun j hj x => ?_⟩
  have hjk : (j : ℕ∞ω) ≤ ((k : ℕ∞) : ℕ∞ω) := (Nat.cast_le.mpr hj : (j : ℕ∞ω) ≤ (k : ℕ∞ω))
  exact (hp.eq_iteratedFDeriv hjk x).symm

private theorem norm_fderiv_indicator_le_of_iteratedFDeriv_one_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {f : E → F} {c : ℝ} (hc : 0 ≤ c) {x : E}
    (heq : iteratedFDeriv ℝ 1 (U.indicator f) x =
      U.indicator (fun y => iteratedFDeriv ℝ 1 f y) x)
    (hb : x ∈ U → ‖iteratedFDeriv ℝ 1 f x‖ ≤ c) :
    ‖fderiv ℝ (U.indicator f) x‖ ≤ c := by
  rw [← norm_iteratedFDeriv_one, heq]
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx]
    exact hb hx
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact hc

theorem contDiff_indicator_of_weight_decay {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (k : ℕ) (hf : ContDiffOn ℝ (k : ℕ∞ω) f U)
    {c : ℝ} (hc : 0 ≤ c) {δ : E → ℝ} (hδ0 : ∀ x, 0 ≤ δ x) (hδ1 : ∀ x, δ x ≤ 1)
    (hδU : U ≠ univ → ∀ x, δ x ≤ infDist x Uᶜ)
    (hbound : ∀ j, j ≤ k → ∀ x ∈ U, ‖iteratedFDeriv ℝ j f x‖ ≤ c * δ x ^ 2) :
    ContDiff ℝ (k : ℕ∞ω) (U.indicator f) ∧
      (∀ j, j ≤ k → ∀ x, iteratedFDeriv ℝ j (U.indicator f) x =
        U.indicator (fun y => iteratedFDeriv ℝ j f y) x) ∧
      (1 ≤ k → ∀ x, ‖fderiv ℝ (U.indicator f) x‖ ≤ c) := by
  have hmain : ContDiff ℝ (k : ℕ∞ω) (U.indicator f) ∧
      ∀ j, j ≤ k → ∀ x, iteratedFDeriv ℝ j (U.indicator f) x =
        U.indicator (fun y => iteratedFDeriv ℝ j f y) x := by
    by_cases hUu : U = univ
    · subst hUu
      refine ⟨?_, fun j _ x => ?_⟩
      · rw [Set.indicator_univ]
        exact contDiffOn_univ.mp hf
      · simp only [Set.indicator_univ]
    · refine contDiff_indicator_of_quadratic_jet_decay hU k hf hc fun j hj x hx => ?_
      exact (hbound j hj x hx).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hδ0 x) (hδU hUu x) 2) hc)
  refine ⟨hmain.1, hmain.2, fun hk x => ?_⟩
  refine norm_fderiv_indicator_le_of_iteratedFDeriv_one_eq hc (hmain.2 1 hk x) fun hx => ?_
  calc ‖iteratedFDeriv ℝ 1 f x‖ ≤ c * δ x ^ 2 := hbound 1 hk x hx
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (hδ0 x) (hδ1 x)) hc
    _ = c := mul_one c

theorem contDiff_indicator_of_min_one_sq_decay {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (k : ℕ) (hf : ContDiffOn ℝ (k : ℕ∞ω) f U)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ j, j ≤ k → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j f x‖ ≤ c * min 1 (infDist x Uᶜ) ^ 2) :
    ContDiff ℝ (k : ℕ∞ω) (U.indicator f) ∧
      (∀ j, j ≤ k → ∀ x, iteratedFDeriv ℝ j (U.indicator f) x =
        U.indicator (fun y => iteratedFDeriv ℝ j f y) x) ∧
      (1 ≤ k → ∀ x, ‖fderiv ℝ (U.indicator f) x‖ ≤ c) :=
  contDiff_indicator_of_weight_decay hU k hf hc (δ := fun x => min 1 (infDist x Uᶜ))
    (fun _ => le_min zero_le_one infDist_nonneg) (fun _ => min_le_left _ _)
    (fun _ _ => min_le_right _ _) hbound

theorem exists_jet_decay_weight {E : Type*} [PseudoMetricSpace E] {U : Set E}
    (hU : IsOpen U) :
    ∃ δ : E → ℝ, Continuous δ ∧ (∀ x, 0 ≤ δ x) ∧ (∀ x, δ x ≤ 1) ∧ (∀ x ∈ U, 0 < δ x) ∧
      (U ≠ univ → ∀ x, δ x ≤ infDist x Uᶜ) := by
  by_cases hUu : U = univ
  · exact ⟨fun _ => 1, continuous_const, fun _ => zero_le_one, fun _ => le_rfl,
      fun _ _ => zero_lt_one, fun h => absurd hUu h⟩
  · refine ⟨fun x => min 1 (infDist x Uᶜ), continuous_const.min (continuous_infDist_pt Uᶜ),
      fun _ => le_min zero_le_one infDist_nonneg, fun _ => min_le_left _ _, fun x hx => ?_,
      fun _ _ => min_le_right _ _⟩
    have hpos : 0 < infDist x Uᶜ :=
      (hU.isClosed_compl.notMem_iff_infDist_pos (Set.nonempty_compl.mpr hUu)).mp
        (Set.notMem_compl_iff.mpr hx)
    exact lt_min zero_lt_one hpos

end DifferentialGeometry.Analysis
