import DifferentialGeometry.Topology.LoopSpace.SpanningDisk
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Sequences
import DifferentialGeometry.Analysis.Calculus.Cutoff.Ball
import DifferentialGeometry.Topology.LoopSpace.RadialLoopExtension
import DifferentialGeometry.Analysis.Calculus.LipschitzConvolution
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.MetricSpace.Lipschitz
import DifferentialGeometry.Analysis.Integration.BallBoundary
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Topology

def IsDiskCollarCutoff (χ : ℂ → ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ (∀ z : ℂ, 0 ≤ χ z) ∧ (∀ z : ℂ, χ z ≤ 1) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 - 2 * δ → χ z = 0) ∧
    (∀ z : ℂ, 1 - δ ≤ ‖z‖ → χ z = 1)

def diskCollarClamp (δ : ℝ) (z : ℂ) : ℝ :=
  (Set.projIcc 0 1 zero_le_one ((‖z‖ - (1 - 2 * δ)) / δ) : Set.Icc (0 : ℝ) 1)

theorem diskCollarClamp_nonneg (δ : ℝ) (z : ℂ) : 0 ≤ diskCollarClamp δ z :=
  (Set.projIcc 0 1 zero_le_one ((‖z‖ - (1 - 2 * δ)) / δ)).2.1

theorem diskCollarClamp_le_one (δ : ℝ) (z : ℂ) : diskCollarClamp δ z ≤ 1 :=
  (Set.projIcc 0 1 zero_le_one ((‖z‖ - (1 - 2 * δ)) / δ)).2.2

theorem diskCollarClamp_eq_zero {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : ‖z‖ ≤ 1 - 2 * δ) :
    diskCollarClamp δ z = 0 := by
  have h : (‖z‖ - (1 - 2 * δ)) / δ ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  rw [diskCollarClamp, Set.projIcc_of_le_left zero_le_one h]

theorem diskCollarClamp_eq_one {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : 1 - δ ≤ ‖z‖) :
    diskCollarClamp δ z = 1 := by
  have h : 1 ≤ (‖z‖ - (1 - 2 * δ)) / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  rw [diskCollarClamp, Set.projIcc_of_right_le zero_le_one h]

theorem continuous_diskCollarClamp (δ : ℝ) : Continuous (diskCollarClamp δ) := by
  have h : Continuous fun z : ℂ => (‖z‖ - (1 - 2 * δ)) / δ :=
    (continuous_norm.sub continuous_const).div_const δ
  exact continuous_subtype_val.comp (continuous_projIcc.comp h)

theorem isDiskCollarCutoff_diskCollarClamp {δ : ℝ} (hδ : 0 < δ) :
    IsDiskCollarCutoff (diskCollarClamp δ) δ :=
  ⟨hδ, diskCollarClamp_nonneg δ, diskCollarClamp_le_one δ,
    fun _ hz => diskCollarClamp_eq_zero hδ hz, fun _ hz => diskCollarClamp_eq_one hδ hz⟩

theorem diskBoundary_norm_coe (θ : loopCircle) :
    ‖((diskBoundary θ : closedDisk) : ℂ)‖ = 1 := by
  change ‖(AddCircle.toCircle θ : ℂ)‖ = 1
  exact Circle.norm_coe _

theorem exists_diskBoundary_eq_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ θ : loopCircle, ((diskBoundary θ : closedDisk) : ℂ) = z := by
  have hzmem : z ∈ Submonoid.unitSphere ℂ := by
    change z ∈ Metric.sphere (0 : ℂ) 1
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  obtain ⟨θ, hθ⟩ :=
    (AddCircle.homeomorphCircle (T := 1) (by norm_num)).surjective ⟨z, hzmem⟩
  refine ⟨θ, ?_⟩
  have hcoe : ((AddCircle.toCircle θ : Circle) : ℂ) = z := by
    have h := congrArg (fun x : Circle => (x : ℂ)) hθ
    rwa [AddCircle.homeomorphCircle_apply] at h
  simpa [diskBoundary] using hcoe

theorem exists_forall_norm_le_of_continuous_eq_zero_on_sphere
    {F : Type*} [NormedAddCommGroup F] {φ : ℂ → F} (hφ : Continuous φ)
    (h0 : ∀ z : ℂ, ‖z‖ = 1 → φ z = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → 1 - 2 * δ < ‖z‖ → ‖φ z‖ ≤ ε := by
  intro ε hε
  by_contra hcon
  push Not at hcon
  have hex : ∀ n : ℕ, ∃ z : ℂ,
      ‖z‖ ≤ 1 ∧ 1 - 2 * (1 / ((n : ℝ) + 1)) < ‖z‖ ∧ ε < ‖φ z‖ :=
    fun n => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose z hz1 hz2 hz3 using hex
  obtain ⟨a, ha, ψ, hψ, hlim⟩ :=
    IsCompact.tendsto_subseq (isCompact_closedBall (0 : ℂ) 1) (fun n => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz1 n)
  have hψtend : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hdiv : Tendsto (fun n : ℕ => 1 / ((ψ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hψtend
  have hlower : Tendsto (fun n : ℕ => 1 - 2 * (1 / ((ψ n : ℝ) + 1))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hdiv.const_mul 2)
  have hnorm : Tendsto (fun n : ℕ => ‖z (ψ n)‖) atTop (𝓝 ‖a‖) := hlim.norm
  have hle_one : (1 : ℝ) ≤ ‖a‖ :=
    le_of_tendsto_of_tendsto hlower hnorm
      (Eventually.of_forall fun n => (hz2 (ψ n)).le)
  have hnorm_le : ‖a‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using ha
  have hnorma : ‖a‖ = 1 := le_antisymm hnorm_le hle_one
  have hzero : ‖φ a‖ = 0 := by rw [h0 a hnorma, norm_zero]
  have hphilim : Tendsto (fun n : ℕ => ‖φ (z (ψ n))‖) atTop (𝓝 ‖φ a‖) :=
    ((hφ.tendsto a).comp hlim).norm
  have hge : ε ≤ ‖φ a‖ :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hphilim
      (Eventually.of_forall fun n => (hz3 (ψ n)).le)
  linarith

def diskCollarInterpolation {F : Type*} [AddCommGroup F] [Module ℝ F]
    (χ : ℂ → ℝ) (w q : ℂ → F) : ℂ → F :=
  fun z => (1 - χ z) • w z + χ z • q z

theorem diskCollarInterpolation_sub {F : Type*} [AddCommGroup F] [Module ℝ F]
    (χ : ℂ → ℝ) (w q : ℂ → F) (z : ℂ) :
    diskCollarInterpolation χ w q z - w z = χ z • (q z - w z) := by
  rw [diskCollarInterpolation, sub_smul, one_smul, smul_sub]
  abel

theorem diskCollarInterpolation_eq_of_eq_zero {F : Type*} [AddCommGroup F] [Module ℝ F]
    {χ : ℂ → ℝ} {w q : ℂ → F} {z : ℂ} (h : χ z = 0) :
    diskCollarInterpolation χ w q z = w z := by
  rw [diskCollarInterpolation, h, sub_zero, one_smul, zero_smul, add_zero]

theorem diskCollarInterpolation_eq_of_eq_one {F : Type*} [AddCommGroup F] [Module ℝ F]
    {χ : ℂ → ℝ} {w q : ℂ → F} {z : ℂ} (h : χ z = 1) :
    diskCollarInterpolation χ w q z = q z := by
  rw [diskCollarInterpolation, h, sub_self, zero_smul, one_smul, zero_add]

theorem norm_diskCollarInterpolation_sub_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : ℂ → ℝ} {w q : ℂ → F} {z : ℂ} (h0 : 0 ≤ χ z) (h1 : χ z ≤ 1) :
    ‖diskCollarInterpolation χ w q z - w z‖ ≤ ‖q z - w z‖ := by
  rw [diskCollarInterpolation_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
  exact mul_le_of_le_one_left (norm_nonneg _) h1

theorem continuous_diskCollarInterpolation {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {χ : ℂ → ℝ} (hχ : Continuous χ) {w q : ℂ → F}
    (hw : Continuous w) (hq : Continuous q) :
    Continuous (diskCollarInterpolation χ w q) := by
  unfold diskCollarInterpolation
  exact ((continuous_const.sub hχ).smul hw).add (hχ.smul hq)

theorem diskCollarInterpolation_diskBoundary {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {χ : ℂ → ℝ} {δ : ℝ} (hχ : IsDiskCollarCutoff χ δ)
    (w q : ℂ → F) (θ : loopCircle) :
    diskCollarInterpolation χ w q ((diskBoundary θ : closedDisk) : ℂ) =
      q ((diskBoundary θ : closedDisk) : ℂ) := by
  refine diskCollarInterpolation_eq_of_eq_one (hχ.2.2.2.2 _ ?_)
  rw [diskBoundary_norm_coe]
  linarith [hχ.1]

def diskCollarFamily {F : Type*} [AddCommGroup F] [Module ℝ F]
    (χ : ℕ → ℂ → ℝ) (w : ℕ → ℂ → F) (q : ℂ → F) : ℕ → ℂ → F :=
  fun j => diskCollarInterpolation (χ j) (w j) q

theorem continuous_diskCollarFamily {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : ℕ → ℂ → ℝ} (hχ : ∀ j : ℕ, Continuous (χ j)) {w : ℕ → ℂ → F}
    (hw : ∀ j : ℕ, Continuous (w j)) {q : ℂ → F} (hq : Continuous q) :
    ∀ j : ℕ, Continuous (diskCollarFamily χ w q j) :=
  fun j => continuous_diskCollarInterpolation (hχ j) (hw j) hq

theorem diskCollarFamily_diskBoundary {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : ℕ → ℂ → ℝ} {δ : ℕ → ℝ}
    (hχ : ∀ j : ℕ, IsDiskCollarCutoff (χ j) (δ j))
    {w : ℕ → ℂ → F} {q : ℂ → F} {γ : C(loopCircle, F)}
    (hqb : ∀ θ : loopCircle, q ((diskBoundary θ : closedDisk) : ℂ) = γ θ) :
    ∀ (j : ℕ) (θ : loopCircle),
      diskCollarFamily χ w q j ((diskBoundary θ : closedDisk) : ℂ) = γ θ :=
  fun j θ => (diskCollarInterpolation_diskBoundary (hχ j) (w j) q θ).trans (hqb θ)

theorem tendstoUniformly_diskCollarFamily {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v q : ℂ → F} (hv : Continuous v) (hq : Continuous q) {γ : C(loopCircle, F)}
    (hvb : ∀ θ : loopCircle, v ((diskBoundary θ : closedDisk) : ℂ) = γ θ)
    (hqb : ∀ θ : loopCircle, q ((diskBoundary θ : closedDisk) : ℂ) = γ θ)
    {w : ℕ → ℂ → F}
    (hw : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ z : ℂ,
      ‖z‖ ≤ 1 → ‖w j z - v z‖ ≤ ε)
    {δ : ℕ → ℝ} (hδlim : Tendsto δ atTop (𝓝 0))
    {χ : ℕ → ℂ → ℝ} (hχ : ∀ j : ℕ, IsDiskCollarCutoff (χ j) (δ j)) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖diskCollarFamily χ w q j z - v z‖ ≤ ε := by
  have hgap0 : ∀ z : ℂ, ‖z‖ = 1 → (fun w : ℂ => q w - v w) z = 0 := by
    intro z hz
    obtain ⟨θ, hθ⟩ := exists_diskBoundary_eq_of_norm_eq_one hz
    change q z - v z = 0
    rw [← hθ, hqb θ, hvb θ, sub_self]
  intro ε hε
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ :=
    exists_forall_norm_le_of_continuous_eq_zero_on_sphere (hq.sub hv) hgap0 (ε / 2)
      (by linarith)
  have hsmall : ∀ᶠ j in atTop, δ j < δ₀ := hδlim.eventually (eventually_lt_nhds hδ₀pos)
  obtain ⟨J₁, hJ₁⟩ := eventually_atTop.1 hsmall
  obtain ⟨J₂, hJ₂⟩ := hw (ε / 4) (by linarith)
  refine ⟨max J₁ J₂, ?_⟩
  intro j hj z hz
  unfold diskCollarFamily
  have hδj : δ j < δ₀ := hJ₁ j (le_trans (le_max_left _ _) hj)
  have hwj : ‖w j z - v z‖ ≤ ε / 4 := hJ₂ j (le_trans (le_max_right _ _) hj) z hz
  by_cases hcase : ‖z‖ ≤ 1 - 2 * δ j
  · rw [diskCollarInterpolation_eq_of_eq_zero ((hχ j).2.2.2.1 z hcase)]
    linarith
  · have hcollar : 1 - 2 * δ₀ < ‖z‖ := by
      have : 1 - 2 * δ j < ‖z‖ := not_le.mp hcase
      linarith
    have hqv : ‖q z - v z‖ ≤ ε / 2 := hδ₀ z hz hcollar
    have hbound : ‖diskCollarInterpolation (χ j) (w j) q z - w j z‖ ≤ ‖q z - w j z‖ :=
      norm_diskCollarInterpolation_sub_le ((hχ j).2.1 z) ((hχ j).2.2.1 z)
    have hsplit : ‖q z - w j z‖ ≤ ‖q z - v z‖ + ‖v z - w j z‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (q z - v z) (v z - w j z)
    have hstep : ‖diskCollarInterpolation (χ j) (w j) q z - v z‖ ≤
        ‖diskCollarInterpolation (χ j) (w j) q z - w j z‖ + ‖w j z - v z‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le (diskCollarInterpolation (χ j) (w j) q z - w j z) (w j z - v z)
    have hrev : ‖v z - w j z‖ = ‖w j z - v z‖ := norm_sub_rev _ _
    calc ‖diskCollarInterpolation (χ j) (w j) q z - v z‖
        ≤ ‖diskCollarInterpolation (χ j) (w j) q z - w j z‖ + ‖w j z - v z‖ := hstep
      _ ≤ ‖q z - w j z‖ + ε / 4 := by linarith
      _ ≤ (‖q z - v z‖ + ‖v z - w j z‖) + ε / 4 := by linarith
      _ ≤ ε := by linarith [hrev.le]

theorem exists_diskCollarFamily_trace_and_tendstoUniformly
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v q : ℂ → F} (hv : Continuous v) (hq : Continuous q) {γ : C(loopCircle, F)}
    (hvb : ∀ θ : loopCircle, v ((diskBoundary θ : closedDisk) : ℂ) = γ θ)
    (hqb : ∀ θ : loopCircle, q ((diskBoundary θ : closedDisk) : ℂ) = γ θ)
    {w : ℕ → ℂ → F}
    (hw : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ z : ℂ,
      ‖z‖ ≤ 1 → ‖w j z - v z‖ ≤ ε)
    {δ : ℕ → ℝ} (hδlim : Tendsto δ atTop (𝓝 0))
    {χ : ℕ → ℂ → ℝ} (hχ : ∀ j : ℕ, IsDiskCollarCutoff (χ j) (δ j)) :
    ∃ Φ : ℕ → ℂ → F,
      (∀ (j : ℕ) (θ : loopCircle), Φ j ((diskBoundary θ : closedDisk) : ℂ) = γ θ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ z : ℂ,
        ‖z‖ ≤ 1 → ‖Φ j z - v z‖ ≤ ε :=
  ⟨diskCollarFamily χ w q, diskCollarFamily_diskBoundary hχ hqb,
    tendstoUniformly_diskCollarFamily hv hq hvb hqb hw hδlim hχ⟩

theorem exists_diskCollarClamp_trace_and_tendstoUniformly
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v q : ℂ → F} (hv : Continuous v) (hq : Continuous q) {γ : C(loopCircle, F)}
    (hvb : ∀ θ : loopCircle, v ((diskBoundary θ : closedDisk) : ℂ) = γ θ)
    (hqb : ∀ θ : loopCircle, q ((diskBoundary θ : closedDisk) : ℂ) = γ θ)
    {w : ℕ → ℂ → F}
    (hw : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ z : ℂ,
      ‖z‖ ≤ 1 → ‖w j z - v z‖ ≤ ε) :
    ∃ Φ : ℕ → ℂ → F,
      (∀ (j : ℕ) (θ : loopCircle), Φ j ((diskBoundary θ : closedDisk) : ℂ) = γ θ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ z : ℂ,
        ‖z‖ ≤ 1 → ‖Φ j z - v z‖ ≤ ε :=
  exists_diskCollarFamily_trace_and_tendstoUniformly hv hq hvb hqb hw
    (δ := fun j : ℕ => 1 / ((j : ℝ) + 1))
    (χ := fun j : ℕ => diskCollarClamp (1 / ((j : ℝ) + 1)))
    tendsto_one_div_add_atTop_nhds_zero_nat
    (fun _ => isDiskCollarCutoff_diskCollarClamp (by positivity))

theorem exists_continuousMap_diskTrace_and_tendstoUniformly
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v q : ℂ → F} (hv : Continuous v) (hq : Continuous q) {γ : C(loopCircle, F)}
    (hvb : ∀ θ : loopCircle, v ((diskBoundary θ : closedDisk) : ℂ) = γ θ)
    (hqb : ∀ θ : loopCircle, q ((diskBoundary θ : closedDisk) : ℂ) = γ θ)
    {w : ℕ → ℂ → F} (hwc : ∀ j : ℕ, Continuous (w j))
    (hw : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ z : ℂ,
      ‖z‖ ≤ 1 → ‖w j z - v z‖ ≤ ε) :
    ∃ vj : ℕ → C(closedDisk, F),
      (∀ j : ℕ, diskTrace (vj j) = γ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J,
        ∀ z : closedDisk, ‖vj j z - v z‖ ≤ ε := by
  have hcont : ∀ j : ℕ, Continuous (fun z : closedDisk =>
      diskCollarFamily (fun j : ℕ => diskCollarClamp (1 / ((j : ℝ) + 1))) w q j (z : ℂ)) :=
    fun j => (continuous_diskCollarFamily (fun _ => continuous_diskCollarClamp _) hwc hq j).comp
      continuous_subtype_val
  have htr : ∀ j : ℕ, diskTrace ⟨fun z : closedDisk =>
      diskCollarFamily (fun j : ℕ => diskCollarClamp (1 / ((j : ℝ) + 1))) w q j (z : ℂ),
        hcont j⟩ = γ := by
    intro j
    ext θ
    exact diskCollarFamily_diskBoundary
      (fun _ => isDiskCollarCutoff_diskCollarClamp (by positivity)) hqb j θ
  refine ⟨fun j => ⟨fun z : closedDisk =>
    diskCollarFamily (fun j : ℕ => diskCollarClamp (1 / ((j : ℝ) + 1))) w q j (z : ℂ),
      hcont j⟩, htr, ?_⟩
  intro ε hε
  obtain ⟨J, hJ⟩ := tendstoUniformly_diskCollarFamily hv hq hvb hqb hw
    (δ := fun j : ℕ => 1 / ((j : ℝ) + 1))
    (χ := fun j : ℕ => diskCollarClamp (1 / ((j : ℝ) + 1)))
    tendsto_one_div_add_atTop_nhds_zero_nat
    (fun _ => isDiskCollarCutoff_diskCollarClamp (by positivity)) ε hε
  exact ⟨J, fun j hj z =>
    hJ j hj (z : ℂ) (by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2)⟩

theorem exists_diskCollarClamp_trace_and_eq_of_trace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : ℂ → F} {γ : C(loopCircle, F)}
    (hvb : ∀ θ : loopCircle, v ((diskBoundary θ : closedDisk) : ℂ) = γ θ) :
    ∃ Φ : ℕ → ℂ → F,
      (∀ (j : ℕ) (θ : loopCircle), Φ j ((diskBoundary θ : closedDisk) : ℂ) = γ θ) ∧
      ∀ (j : ℕ) (z : ℂ), ‖z‖ ≤ 1 → Φ j z = v z := by
  refine ⟨diskCollarFamily (fun j : ℕ => diskCollarClamp (1 / ((j : ℝ) + 1))) (fun _ => v) v,
    ?_, ?_⟩
  · intro j θ
    have hδ : 0 < 1 / ((j : ℝ) + 1) := by positivity
    rw [diskCollarFamily, diskCollarInterpolation_diskBoundary
      (isDiskCollarCutoff_diskCollarClamp hδ) v v θ]
    exact hvb θ
  · intro j z _
    rw [diskCollarFamily, diskCollarInterpolation, ← add_smul, sub_add_cancel, one_smul]

end DifferentialGeometry.Geometry

end

noncomputable section

open NormedSpace
open scoped NNReal

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F]

private theorem dist_normalize_eq {x : V} (hx : x ≠ 0) :
    dist x (normalize x) = |‖x‖ - 1| := by
  have he : x - normalize x = (‖x‖ - 1) • normalize x := by
    rw [sub_smul, one_smul, norm_smul_normalize]
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, norm_normalize hx, mul_one]

theorem LipschitzOnWith.norm_le_mul_one_sub_norm_of_eq_zero_on_sphere
    {L : ℝ≥0} {f : V → F} (hf : LipschitzOnWith L f (Metric.closedBall 0 1))
    (hboundary : ∀ x : V, ‖x‖ = 1 → f x = 0) {x : V}
    (hx : x ≠ 0) (hx1 : ‖x‖ ≤ 1) : ‖f x‖ ≤ (L : ℝ) * (1 - ‖x‖) := by
  have hnormal : ‖normalize x‖ = 1 := norm_normalize hx
  have h := hf.dist_le_mul x
    (show x ∈ Metric.closedBall 0 1 by simpa only [Metric.mem_closedBall, dist_zero_right])
    (normalize x) (show normalize x ∈ Metric.closedBall 0 1 by
      simp only [Metric.mem_closedBall, dist_zero_right, hnormal, le_refl])
  rw [hboundary _ hnormal, dist_zero_right, dist_normalize_eq hx,
    abs_of_nonpos (sub_nonpos.mpr hx1), neg_sub] at h
  exact h

end

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis

def diskCollarCutoff (δ : ℝ) (z : ℂ) : ℝ :=
  1 - ballCutoff 0 (1 - 2 * δ) (1 - δ) z

theorem diskCollarCutoff_contDiff (δ : ℝ) : ContDiff ℝ ∞ (diskCollarCutoff δ) :=
  contDiff_const.sub (ballCutoff_contDiff 0 (1 - 2 * δ) (1 - δ))

theorem isDiskCollarCutoff_diskCollarCutoff {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    IsDiskCollarCutoff (diskCollarCutoff δ) δ := by
  have hr : 0 ≤ 1 - 2 * δ := by linarith
  have hrR : 1 - 2 * δ < 1 - δ := by linarith
  refine ⟨hδ, fun z => ?_, fun z => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · exact sub_nonneg.mpr (ballCutoff_mem_Icc 0 (1 - 2 * δ) (1 - δ) z).2
  · exact sub_le_self 1 (ballCutoff_mem_Icc 0 (1 - 2 * δ) (1 - δ) z).1
  · rw [diskCollarCutoff, ballCutoff_eq_one_of_mem_closedBall hr hrR
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz), sub_self]
  · rw [diskCollarCutoff, ballCutoff_eq_zero_of_le_dist hr hrR
      (by simpa only [dist_zero_right] using hz), sub_zero]

theorem norm_fderiv_diskCollarCutoff_le {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (z : ℂ) : ‖fderiv ℝ (diskCollarCutoff δ) z‖ ≤ 2 * CutoffProfile.derivBound / δ := by
  have hr : 0 ≤ 1 - 2 * δ := by linarith
  have hrR : 1 - 2 * δ < 1 - δ := by linarith
  have hden : 0 < (1 - δ) ^ 2 - (1 - 2 * δ) ^ 2 := by nlinarith
  have hfactor : 2 * (1 - δ) / ((1 - δ) ^ 2 - (1 - 2 * δ) ^ 2) ≤ 2 / δ := by
    rw [div_le_div_iff₀ hden hδ]
    nlinarith
  have hd : fderiv ℝ (diskCollarCutoff δ) z =
      -ballCutoffFDeriv 0 (1 - 2 * δ) (1 - δ) z := by
    exact ((hasFDerivAt_ballCutoff 0 (1 - 2 * δ) (1 - δ) z).const_sub 1).fderiv
  rw [hd, norm_neg]
  calc
    _ ≤ ballCutoffFDerivBound (1 - 2 * δ) (1 - δ) := norm_ballCutoffFDeriv_le hr hrR z
    _ ≤ CutoffProfile.derivBound * (2 / δ) :=
      mul_le_mul_of_nonneg_left hfactor CutoffProfile.derivBound_nonneg
    _ = _ := by ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_diskCollarInterpolation {χ : ℂ → ℝ} {w q : ℂ → F} {z : ℂ}
    (hχ : DifferentiableAt ℝ χ z) (hw : DifferentiableAt ℝ w z)
    (hq : DifferentiableAt ℝ q z) :
    fderiv ℝ (diskCollarInterpolation χ w q) z =
      (1 - χ z) • fderiv ℝ w z + χ z • fderiv ℝ q z +
        (fderiv ℝ χ z).smulRight (q z - w z) := by
  have h := (((hasDerivAt_id (χ z)).const_sub 1).comp_hasFDerivAt z hχ.hasFDerivAt).smul
    hw.hasFDerivAt
  have hh := h.add (hχ.hasFDerivAt.smul hq.hasFDerivAt)
  calc
    _ = _ := hh.fderiv
    _ = _ := by
      ext v
      change (1 - χ z) • fderiv ℝ w z v + (-1 * fderiv ℝ χ z v) • w z +
          (χ z • fderiv ℝ q z v + fderiv ℝ χ z v • q z) =
        (1 - χ z) • fderiv ℝ w z v + χ z • fderiv ℝ q z v +
          fderiv ℝ χ z v • (q z - w z)
      module

theorem norm_fderiv_diskCollarInterpolation_le {χ : ℂ → ℝ} {w q : ℂ → F} {z : ℂ}
    (hχ : DifferentiableAt ℝ χ z) (hw : DifferentiableAt ℝ w z)
    (hq : DifferentiableAt ℝ q z) (hχ0 : 0 ≤ χ z) (hχ1 : χ z ≤ 1) :
    ‖fderiv ℝ (diskCollarInterpolation χ w q) z‖ ≤
      (1 - χ z) * ‖fderiv ℝ w z‖ + χ z * ‖fderiv ℝ q z‖ +
        ‖fderiv ℝ χ z‖ * ‖q z - w z‖ := by
  rw [fderiv_diskCollarInterpolation hχ hw hq]
  refine (norm_add_le _ _).trans ?_
  apply add_le_add
  · refine (norm_add_le _ _).trans ?_
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hχ0,
      abs_of_nonneg (sub_nonneg.mpr hχ1), le_refl]
  · exact (ContinuousLinearMap.norm_smulRight_apply _ _).le

theorem diskCollarInterpolation_eventuallyEq {χ : ℂ → ℝ} {δ : ℝ}
    (hχ : IsDiskCollarCutoff χ δ) (w q : ℂ → F) {z : ℂ} (hz : ‖z‖ < 1 - 2 * δ) :
    diskCollarInterpolation χ w q =ᶠ[𝓝 z] w := by
  filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hz)] with y hy
  exact diskCollarInterpolation_eq_of_eq_zero (hχ.2.2.2.1 y hy.le)

theorem diskCollarInterpolation_contDiff {χ : ℂ → ℝ} {δ : ℝ}
    (hχ : IsDiskCollarCutoff χ δ) (hδ : δ < 1 / 2) (hχs : ContDiff ℝ ∞ χ)
    {w q : ℂ → F} (hw : ContDiff ℝ ∞ w)
    (hq : ContDiffOn ℝ ∞ q {z : ℂ | z ≠ 0}) :
    ContDiff ℝ ∞ (diskCollarInterpolation χ w q) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    exact hw.contDiffAt.congr_of_eventuallyEq
      (diskCollarInterpolation_eventuallyEq hχ w q (by simp only [norm_zero]; linarith))
  · have hqz : ContDiffAt ℝ ∞ q z := hq.contDiffAt (isOpen_compl_singleton.mem_nhds hz)
    exact ((contDiffAt_const.sub hχs.contDiffAt).smul hw.contDiffAt).add
      (hχs.contDiffAt.smul hqz)

theorem diskCollarInterpolation_fderiv_eventuallyEq {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) {χ : ℕ → ℂ → ℝ}
    (hχ : ∀ j, IsDiskCollarCutoff (χ j) (δ j)) (w : ℕ → ℂ → F) (q : ℂ → F)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ∀ᶠ j in atTop, fderiv ℝ (diskCollarInterpolation (χ j) (w j) q) z = fderiv ℝ (w j) z := by
  have ht : Tendsto (fun j => 1 - 2 * δ j) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hδ.const_mul 2)
  filter_upwards [ht.eventually (lt_mem_nhds hz)] with j hj
  exact (diskCollarInterpolation_eventuallyEq (hχ j) (w j) q hj).fderiv_eq

theorem exists_contDiff_diskTrace_extension (γ : DifferentialGeometry.Topology.freeLoop F)
    (hγ : ContDiff ℝ ∞ (fun t : ℝ => γ (t : DifferentialGeometry.Topology.loopCircle))) :
    ∃ q : ℂ → F, ContDiff ℝ ∞ q ∧
      ∀ θ, q (DifferentialGeometry.Topology.diskBoundary θ : ℂ) = γ θ := by
  let q := DifferentialGeometry.Topology.radialLoopExtension γ
  have hq : ContDiffOn ℝ ∞ q {z : ℂ | z ≠ 0} :=
    (DifferentialGeometry.Topology.contMDiffOn_radialLoopExtension γ hγ.contMDiff).contDiffOn
  have hχ := isDiskCollarCutoff_diskCollarCutoff (δ := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨diskCollarInterpolation (diskCollarCutoff (1 / 4)) (fun _ => 0) q,
    diskCollarInterpolation_contDiff hχ (by norm_num)
      (diskCollarCutoff_contDiff _) contDiff_const hq, ?_⟩
  intro θ
  exact (diskCollarInterpolation_diskBoundary hχ (fun _ => 0) q θ).trans
    (DifferentialGeometry.Topology.radialLoopExtension_diskBoundary γ θ)

end DifferentialGeometry.Geometry

end

noncomputable section

open Set Filter
open scoped ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_contDiff_lipschitz_diskTrace_extension (γ : freeLoop F)
    (hγ : ContDiff ℝ ∞ (fun t : ℝ => γ (t : loopCircle))) :
    ∃ (q : ℂ → F) (L : ℝ≥0), ContDiff ℝ ∞ q ∧ HasCompactSupport q ∧
      LipschitzWith L q ∧ ∀ θ, q (diskBoundary θ : ℂ) = γ θ := by
  obtain ⟨q, hq, hqtr⟩ := exists_contDiff_diskTrace_extension γ hγ
  let Q : ℂ → F := fun z => ballCutoff 0 1 2 z • q z
  have hQs : ContDiff ℝ ∞ Q := (ballCutoff_contDiff 0 1 2).smul hq
  have hQc : HasCompactSupport Q :=
    (ballCutoff_hasCompactSupport (center := (0 : ℂ)) (r := 1) (R := 2)
      (by norm_num) (by norm_num)).smul_right
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hQc hQs (by simp)
  refine ⟨Q, L, hQs, hQc, hL, fun θ => ?_⟩
  change ballCutoff 0 1 2 (diskBoundary θ : ℂ) • q (diskBoundary θ : ℂ) = γ θ
  rw [ballCutoff_eq_one_of_mem_closedBall (by norm_num) (by norm_num)
    (diskBoundary θ).property, one_smul, hqtr]

omit [NormedSpace ℝ F] in
theorem norm_sub_le_mul_one_sub_norm_of_diskTrace {q v : ℂ → F} {Lq Lv : ℝ≥0}
    (hq : LipschitzWith Lq q) (hv : LipschitzWith Lv v)
    (htr : ∀ θ, q (diskBoundary θ : ℂ) = v (diskBoundary θ : ℂ))
    {z : ℂ} (hz : z ≠ 0) (hz1 : ‖z‖ ≤ 1) :
    ‖q z - v z‖ ≤ ((Lq : ℝ) + Lv) * (1 - ‖z‖) := by
  apply (hq.sub hv).lipschitzOnWith.norm_le_mul_one_sub_norm_of_eq_zero_on_sphere
    (fun x hx => ?_) hz hz1
  obtain ⟨θ, hθ⟩ := exists_diskBoundary_eq_of_norm_eq_one hx
  rw [← hθ, htr θ, sub_self]

private theorem norm_fderiv_diskCollarInterpolation_le_of_collar_bound {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) {w q : ℂ → F}
    (hw : ContDiff ℝ ∞ w) (hq : ContDiff ℝ ∞ q)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hwD : ∀ z, ‖fderiv ℝ w z‖ ≤ A) (hqD : ∀ z, ‖fderiv ℝ q z‖ ≤ B)
    (hgap : ∀ z, 1 - 2 * δ ≤ ‖z‖ → ‖z‖ ≤ 1 → ‖q z - w z‖ ≤ C * δ)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖fderiv ℝ (diskCollarInterpolation (diskCollarCutoff δ) w q) z‖ ≤
      A + B + 2 * CutoffProfile.derivBound * C := by
  have hχ := isDiskCollarCutoff_diskCollarCutoff hδ hδ'.le
  by_cases hzin : ‖z‖ < 1 - 2 * δ
  · rw [(diskCollarInterpolation_eventuallyEq hχ w q hzin).fderiv_eq]
    exact (hwD z).trans (by nlinarith [mul_nonneg CutoffProfile.derivBound_nonneg hC])
  · have hg := hgap z (le_of_not_gt hzin) hz
    have hprod : ‖fderiv ℝ (diskCollarCutoff δ) z‖ * ‖q z - w z‖ ≤
        2 * CutoffProfile.derivBound * C := by
      calc
        _ ≤ (2 * CutoffProfile.derivBound / δ) * (C * δ) :=
          mul_le_mul (norm_fderiv_diskCollarCutoff_le hδ hδ'.le z) hg
            (norm_nonneg _) (div_nonneg
              (mul_nonneg (by norm_num) CutoffProfile.derivBound_nonneg) hδ.le)
        _ = _ := by field_simp
    have hfirst : (1 - diskCollarCutoff δ z) * ‖fderiv ℝ w z‖ ≤ A :=
      (mul_le_mul_of_nonneg_left (hwD z) (sub_nonneg.mpr (hχ.2.2.1 z))).trans
        (mul_le_of_le_one_left hA (by linarith [hχ.2.1 z]))
    have hsecond : diskCollarCutoff δ z * ‖fderiv ℝ q z‖ ≤ B :=
      (mul_le_mul_of_nonneg_left (hqD z) (hχ.2.1 z)).trans
        (mul_le_of_le_one_left hB (hχ.2.2.1 z))
    exact (norm_fderiv_diskCollarInterpolation_le
      ((diskCollarCutoff_contDiff δ).differentiable (by simp) z)
      (hw.differentiable (by simp) z) (hq.differentiable (by simp) z)
      (hχ.2.1 z) (hχ.2.2.1 z)).trans (by linarith)

end DifferentialGeometry.Geometry

end

noncomputable section

open Set Filter
open scoped ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
private theorem norm_sub_le_mul_collar_width {q v w : ℂ → F} {Lq Lv : ℝ≥0}
    (hq : LipschitzWith Lq q) (hv : LipschitzWith Lv v)
    (htr : ∀ θ, q (diskBoundary θ : ℂ) = v (diskBoundary θ : ℂ))
    {δ : ℝ} (hδ' : δ < 1 / 2)
    (hw : ∀ z, ‖z‖ ≤ 1 → ‖w z - v z‖ ≤ (Lv : ℝ) * δ)
    {z : ℂ} (hzin : 1 - 2 * δ ≤ ‖z‖) (hz : ‖z‖ ≤ 1) :
    ‖q z - w z‖ ≤ (2 * ((Lq : ℝ) + Lv) + Lv) * δ := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hqv := norm_sub_le_mul_one_sub_norm_of_diskTrace hq hv htr hz0 hz
  have hqv' : ‖q z - v z‖ ≤ 2 * ((Lq : ℝ) + Lv) * δ := by
    calc
      _ ≤ ((Lq : ℝ) + Lv) * (1 - ‖z‖) := hqv
      _ ≤ ((Lq : ℝ) + Lv) * (2 * δ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  calc
    ‖q z - w z‖ ≤ ‖q z - v z‖ + ‖v z - w z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ((Lq : ℝ) + Lv) * δ + Lv * δ := by
      rw [norm_sub_rev (v z) (w z)]
      exact add_le_add hqv' (hw z hz)
    _ = _ := by ring

private theorem norm_diskCollarInterpolation_sub_le_mul_width {q v w : ℂ → F} {Lq Lv : ℝ≥0}
    (hq : LipschitzWith Lq q) (hv : LipschitzWith Lv v)
    (htr : ∀ θ, q (diskBoundary θ : ℂ) = v (diskBoundary θ : ℂ))
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hw : ∀ z, ‖z‖ ≤ 1 → ‖w z - v z‖ ≤ (Lv : ℝ) * δ)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖diskCollarInterpolation (diskCollarCutoff δ) w q z - v z‖ ≤
      (2 * ((Lq : ℝ) + Lv) + 2 * Lv) * δ := by
  have hχ := isDiskCollarCutoff_diskCollarCutoff hδ hδ'.le
  by_cases hzin : ‖z‖ ≤ 1 - 2 * δ
  · rw [diskCollarInterpolation_eq_of_eq_zero (hχ.2.2.2.1 z hzin)]
    refine (hw z hz).trans ?_
    apply mul_le_mul_of_nonneg_right _ hδ.le
    nlinarith [Lq.coe_nonneg, Lv.coe_nonneg]
  · have hgap := norm_sub_le_mul_collar_width hq hv htr hδ' hw (le_of_not_ge hzin) hz
    calc
      _ ≤ ‖diskCollarInterpolation (diskCollarCutoff δ) w q z - w z‖ + ‖w z - v z‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖q z - w z‖ + ‖w z - v z‖ :=
        add_le_add (norm_diskCollarInterpolation_sub_le (hχ.2.1 z) (hχ.2.2.1 z)) le_rfl
      _ ≤ (2 * ((Lq : ℝ) + Lv) + Lv) * δ + Lv * δ := add_le_add hgap (hw z hz)
      _ = _ := by ring

private theorem norm_fderiv_diskCollarInterpolation_le_of_lipschitz
    {q v w : ℂ → F} {Lq Lv : ℝ≥0}
    (hqs : ContDiff ℝ ∞ q) (hws : ContDiff ℝ ∞ w)
    (hq : LipschitzWith Lq q) (hv : LipschitzWith Lv v) (hw : LipschitzWith Lv w)
    (htr : ∀ θ, q (diskBoundary θ : ℂ) = v (diskBoundary θ : ℂ))
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hwv : ∀ z, ‖z‖ ≤ 1 → ‖w z - v z‖ ≤ (Lv : ℝ) * δ)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖fderiv ℝ (diskCollarInterpolation (diskCollarCutoff δ) w q) z‖ ≤
      Lv + Lq + 2 * CutoffProfile.derivBound * (2 * ((Lq : ℝ) + Lv) + Lv) := by
  apply norm_fderiv_diskCollarInterpolation_le_of_collar_bound hδ hδ' hws hqs
    Lv.coe_nonneg Lq.coe_nonneg (by positivity)
    (fun _ => norm_fderiv_le_of_lipschitz ℝ hw)
    (fun _ => norm_fderiv_le_of_lipschitz ℝ hq) _ hz
  exact fun z hzin hz => norm_sub_le_mul_collar_width hq hv htr hδ' hwv hzin hz

end DifferentialGeometry.Geometry

end

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_contDiff_diskTrace_tendstoUniformlyOn_fderiv {v : ℂ → F} {L : ℝ≥0}
    (hv : LipschitzWith L v) (γ : freeLoop F)
    (hγ : ContDiff ℝ ∞ (fun t : ℝ => γ (t : loopCircle)))
    (htr : ∀ θ, v (diskBoundary θ : ℂ) = γ θ) :
    ∃ (u : ℕ → ℂ → F) (B : ℝ), 0 ≤ B ∧
      (∀ j, ContDiff ℝ ∞ (u j)) ∧
      (∀ j θ, u j (diskBoundary θ : ℂ) = γ θ) ∧
      (∀ j z, ‖z‖ ≤ 1 → ‖fderiv ℝ (u j) z‖ ≤ B) ∧
      TendstoUniformlyOn u v atTop (Metric.closedBall (0 : ℂ) 1) ∧
      ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1),
        Tendsto (fun j => fderiv ℝ (u j) z) atTop (𝓝 (fderiv ℝ v z)) := by
  obtain ⟨q, Lq, hqs, _, hq, hqtr⟩ := exists_contDiff_lipschitz_diskTrace_extension γ hγ
  obtain ⟨w, hws, hwl, _, hwv, hwd, _⟩ :=
    hv.exists_contDiff_lipschitz_tendstoUniformly_fderiv (μ := volume)
  let δ (j : ℕ) : ℝ := 1 / ((j : ℝ) + 4)
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδ' (j : ℕ) : δ j < 1 / 2 := by
    dsimp [δ]
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 4) (by norm_num)]
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 3)
    simpa only [δ, Function.comp_def, Nat.cast_add, Nat.cast_ofNat, add_assoc,
      show (3 : ℝ) + 1 = 4 by norm_num] using ht
  have hχ (j : ℕ) := isDiskCollarCutoff_diskCollarCutoff (hδ j) (hδ' j).le
  have htrace : ∀ θ, q (diskBoundary θ : ℂ) = v (diskBoundary θ : ℂ) :=
    fun θ => (hqtr θ).trans (htr θ).symm
  have happrox (j : ℕ) : ∀ z, ‖z‖ ≤ 1 → ‖w (j + 3) z - v z‖ ≤ (L : ℝ) * δ j := by
    intro z _
    change ‖w (j + 3) z - v z‖ ≤ (L : ℝ) * (1 / ((j : ℝ) + 4))
    rw [mul_one_div]
    simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc,
      show (3 : ℝ) + 1 = 4 by norm_num] using hwv (j + 3) z
  let u (j : ℕ) := diskCollarInterpolation (diskCollarCutoff (δ j)) (w (j + 3)) q
  let B : ℝ := L + Lq + 2 * CutoffProfile.derivBound * (2 * ((Lq : ℝ) + L) + L)
  refine ⟨u, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [B]
    exact add_nonneg (add_nonneg L.coe_nonneg Lq.coe_nonneg)
      (mul_nonneg (mul_nonneg (by norm_num) CutoffProfile.derivBound_nonneg) (by positivity))
  · intro j
    exact diskCollarInterpolation_contDiff (hχ j) (hδ' j) (diskCollarCutoff_contDiff _)
      (hws (j + 3)) hqs.contDiffOn
  · intro j θ
    exact (diskCollarInterpolation_diskBoundary (hχ j) (w (j + 3)) q θ).trans (hqtr θ)
  · intro j z hz
    exact norm_fderiv_diskCollarInterpolation_le_of_lipschitz hqs (hws (j + 3))
      hq hv (hwl (j + 3)) htrace (hδ j) (hδ' j) (happrox j) hz
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have ht : Tendsto (fun j => (2 * ((Lq : ℝ) + L) + 2 * L) * δ j) atTop (𝓝 0) := by
      simpa using hδlim.const_mul (2 * ((Lq : ℝ) + L) + 2 * L)
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with j hj z hz
    rw [dist_comm, dist_eq_norm]
    exact (norm_diskCollarInterpolation_sub_le_mul_width hq hv htrace
      (hδ j) (hδ' j) (happrox j)
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)).trans_lt hj
  · filter_upwards [ae_restrict_of_ae hwd, (MeasureTheory.ae_mem_ball_of_measure_sphere_eq_zero (MeasureTheory.Measure.addHaar_sphere volume (0 : ℂ) 1))] with z hz hzin
    have hlim := hz.comp (tendsto_add_atTop_nat 3)
    apply hlim.congr'
    filter_upwards [diskCollarInterpolation_fderiv_eventuallyEq hδlim hχ
      (fun j => w (j + 3)) q (z := z)
      (by simpa only [Metric.mem_ball, dist_zero_right] using hzin)] with j hj
    exact hj.symm

end DifferentialGeometry.Geometry

end
