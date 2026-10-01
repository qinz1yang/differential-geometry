import DifferentialGeometry.Analysis.Calculus.Inverse.SmallNormalGraphDerivative
import DifferentialGeometry.Analysis.FunctionalAnalysis.Contraction.ClosedBall
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.MeanValue
import DifferentialGeometry.Analysis.Calculus.Inverse.ContinuousLinearMapNeumann

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology NNReal

namespace DifferentialGeometry.Analysis

theorem exists_contDiffOn_contraction_graph
    {E N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    {n : ℕ∞ω} (hn : n ≠ 0)
    {U : Set E} (hU : IsOpen U) {W : Set (E × N)} (hW : IsOpen W)
    {r : ℝ} (hr : 0 < r)
    (hcylinder : U ×ˢ Metric.closedBall (0 : N) r ⊆ W)
    {e : E × N → N} (he : ContDiffOn ℝ n e W)
    (hsmall : ∀ t ∈ U, ∀ z ∈ Metric.closedBall (0 : N) r, ‖e (t, z)‖ ≤ r / 4)
    (hnormal : ∀ t ∈ U, ∀ z ∈ Metric.closedBall (0 : N) r,
      ‖fderiv ℝ (fun w : N => e (t, w)) z‖ ≤ 1 / 2) :
    ∃ g : E → N, ContDiffOn ℝ n g U ∧
      (∀ t ∈ U, ‖g t‖ ≤ r / 4 ∧ g t + e (t, g t) = 0) ∧
      ∀ t ∈ U, ∀ z ∈ Metric.closedBall (0 : N) r,
        z + e (t, z) = 0 ↔ z = g t := by
  classical
  have hzero : (0 : N) ∈ Metric.closedBall 0 r := by
    simpa only [Metric.mem_closedBall, dist_self] using hr.le
  have hdiff (t : E) (ht : t ∈ U) (z : N)
      (hz : z ∈ Metric.closedBall (0 : N) r) :
      DifferentiableAt ℝ (fun w : N => e (t, w)) z := by
    exact ((he.contDiffAt (hW.mem_nhds (hcylinder ⟨ht, hz⟩))).differentiableAt hn).comp z
      ((differentiableAt_const t).prodMk differentiableAt_id)
  have hroot (t : E) (ht : t ∈ U) :
      ∃! z : N, z ∈ Metric.closedBall (0 : N) r ∧ z + e (t, z) = 0 := by
    have hlip : LipschitzOnWith (1 / 2 : ℝ≥0) (fun z : N => e (t, z))
        (Metric.closedBall (0 : N) r) := by
      apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (hdiff t ht) _ (convex_closedBall 0 r)
      intro z hz
      exact_mod_cast hnormal t ht z hz
    have hneg : LipschitzOnWith (1 / 2 : ℝ≥0) (fun z : N => -e (t, z))
        (Metric.closedBall (0 : N) r) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro z hz w hw
      simpa only [dist_neg_neg] using hlip.dist_le_mul z hz w hw
    have hcenter : ‖-e (t, (0 : N))‖ ≤ (1 - ((1 / 2 : ℝ≥0) : ℝ)) * r := by
      rw [norm_neg]
      have h := hsmall t ht 0 hzero
      norm_num at ⊢
      linarith
    obtain ⟨z, ⟨hz, hfix⟩, huniq⟩ :=
      exists_unique_fixedPoint_mem_closedBall hr.le (by norm_num : (1 / 2 : ℝ≥0) < 1)
        hcenter hneg
    have heq (w : N) : Function.IsFixedPt (fun v : N => -e (t, v)) w ↔
        w + e (t, w) = 0 := by
      change -e (t, w) = w ↔ w + e (t, w) = 0
      constructor
      · intro h
        exact (congrArg (fun v : N => v + e (t, w)) h.symm).trans (neg_add_cancel _)
      · intro h
        exact (eq_neg_of_add_eq_zero_left h).symm
    exact ⟨z, ⟨hz, (heq z).mp hfix⟩,
      fun w hw => huniq w ⟨hw.1, (heq w).mpr hw.2⟩⟩
  let g : E → N := fun t => if ht : t ∈ U then Classical.choose (hroot t ht) else 0
  have hspec (t : E) (ht : t ∈ U) :
      g t ∈ Metric.closedBall (0 : N) r ∧ g t + e (t, g t) = 0 := by
    dsimp only [g]
    rw [dite_eq_left ht]
    exact (Classical.choose_spec (hroot t ht)).1
  have huniq (t : E) (ht : t ∈ U) (z : N)
      (hz : z ∈ Metric.closedBall (0 : N) r) : z + e (t, z) = 0 ↔ z = g t := by
    constructor
    · intro h
      have hu := (Classical.choose_spec (hroot t ht)).2 z ⟨hz, h⟩
      simpa only [g, dite_eq_left ht] using hu
    · rintro rfl
      exact (hspec t ht).2
  have hbound (t : E) (ht : t ∈ U) : ‖g t‖ ≤ r / 4 := by
    have hg : g t = -e (t, g t) := eq_neg_of_add_eq_zero_left (hspec t ht).2
    rw [hg, norm_neg]
    exact hsmall t ht (g t) (hspec t ht).1
  have hinterior (t : E) (ht : t ∈ U) : g t ∈ Metric.ball (0 : N) r := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (hbound t ht) (by linarith)
  refine ⟨g, ?_, (fun t ht => ⟨hbound t ht, (hspec t ht).2⟩), huniq⟩
  intro t ht
  let F : E × N → N := fun p => p.2 + e p
  have hFt : ContDiffAt ℝ n F (t, g t) :=
    contDiffAt_snd.add (he.contDiffAt (hW.mem_nhds (hcylinder ⟨ht, (hspec t ht).1⟩)))
  let B : N →L[ℝ] N := fderiv ℝ (fun z : N => e (t, z)) (g t)
  have hB : ‖B‖ < 1 := lt_of_le_of_lt (hnormal t ht (g t) (hspec t ht).1) (by norm_num)
  have hslice : HasFDerivAt (fun z : N => F (t, z))
      (ContinuousLinearMap.id ℝ N + B) (g t) :=
    (hasFDerivAt_id (g t)).add (hdiff t ht (g t) (hspec t ht).1).hasFDerivAt
  have hpartial : (fderiv ℝ F (t, g t)).comp (ContinuousLinearMap.inr ℝ E N) =
      ContinuousLinearMap.id ℝ N + B := by
    exact ((hFt.differentiableAt hn).hasFDerivAt.comp (g t)
      ((hasFDerivAt_const t (g t)).prodMk (hasFDerivAt_id (g t)))).unique hslice
  have hinv : ((fderiv ℝ F (t, g t)).comp (ContinuousLinearMap.inr ℝ E N)).IsInvertible := by
    rw [hpartial]
    apply ContinuousLinearMap.invertible_of_id_sub
    simpa only [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg] using hB
  let ψ := hFt.implicitFunction hn hinv
  have hψ : ContDiffAt ℝ n ψ t := hFt.contDiffAt_implicitFunction hn hinv
  have hψt : ψ t = g t := hFt.implicitFunction_apply_self hn hinv
  have hψmem : ∀ᶠ s in 𝓝 t, ψ s ∈ Metric.ball (0 : N) r := by
    apply hψ.continuousAt (Metric.isOpen_ball.mem_nhds _)
    rw [hψt]
    exact hinterior t ht
  have heq : g =ᶠ[𝓝 t] ψ := by
    filter_upwards [hU.mem_nhds ht, hψmem, hFt.eventually_apply_implicitFunction hn hinv]
      with s hs hmem hF
    apply ((huniq s hs (ψ s) (Metric.ball_subset_closedBall hmem)).mp _).symm
    exact hF.trans (hspec t ht).2
  exact (hψ.congr_of_eventuallyEq heq).contDiffWithinAt

theorem exists_contDiffOn_small_normal_graph
    {E N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    {n : ℕ∞ω} (hn : n ≠ 0)
    {U : Set E} (hU : IsOpen U) {W : Set (E × N)} (hW : IsOpen W)
    {r ε₀ ε₁ : ℝ} (hr : 0 < r) (hε₀ : ε₀ ≤ r / 4)
    (hcylinder : U ×ˢ Metric.closedBall (0 : N) r ⊆ W)
    {e : E × N → N} (he : ContDiffOn ℝ n e W)
    (hsmall : ∀ t ∈ U, ∀ z ∈ Metric.closedBall (0 : N) r, ‖e (t, z)‖ ≤ ε₀)
    (hnormal : ∀ t ∈ U, ∀ z ∈ Metric.closedBall (0 : N) r,
      ‖fderiv ℝ (fun w : N => e (t, w)) z‖ ≤ 1 / 2)
    (htangent : ∀ t ∈ U, ∀ z ∈ Metric.closedBall (0 : N) r,
      ‖fderiv ℝ (fun s : E => e (s, z)) t‖ ≤ ε₁) :
    ∃ g : E → N, ContDiffOn ℝ n g U ∧
      (∀ t ∈ U, ‖g t‖ ≤ ε₀ ∧ ‖fderiv ℝ g t‖ ≤ 2 * ε₁ ∧
        g t + e (t, g t) = 0) ∧
      ∀ t ∈ U, ∀ z ∈ Metric.closedBall (0 : N) r,
        z + e (t, z) = 0 ↔ z = g t := by
  obtain ⟨g, hg, hvalue, huniq⟩ := exists_contDiffOn_contraction_graph hn hU hW hr
    hcylinder he (fun t ht z hz => (hsmall t ht z hz).trans hε₀) hnormal
  refine ⟨g, hg, ?_, huniq⟩
  intro t ht
  have hmem : g t ∈ Metric.closedBall (0 : N) r := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hvalue t ht).1.trans (by linarith)
  have hnorm : ‖g t‖ ≤ ε₀ := by
    rw [eq_neg_of_add_eq_zero_left (hvalue t ht).2, norm_neg]
    exact hsmall t ht (g t) hmem
  refine ⟨hnorm, ?_, (hvalue t ht).2⟩
  have hgd := (hg.contDiffAt (hU.mem_nhds ht)).differentiableAt hn
  have hed : DifferentiableAt ℝ e (t, g t) := (he.contDiffAt (hW.mem_nhds (hcylinder ⟨ht, hmem⟩))).differentiableAt hn
  have hrel : ∀ᶠ s in 𝓝 t, g s + e (s, g s) = 0 := by
    filter_upwards [hU.mem_nhds ht] with s hs
    exact (hvalue s hs).2
  have hN := hnormal t ht (g t) hmem
  have hT := htangent t ht (g t) hmem
  have hε₁ : 0 ≤ ε₁ := (norm_nonneg _).trans hT
  have hpos : 0 < 1 - ‖fderiv ℝ (fun z : N => e (t, z)) (g t)‖ := by linarith
  have h := norm_fderiv_normal_graph_le hgd hed hrel (by linarith)
  apply h.trans
  apply (div_le_iff₀ hpos).mpr
  nlinarith

end DifferentialGeometry.Analysis
