import DifferentialGeometry.Topology.LoopSpace.SpanningDisk
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Sequences

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
