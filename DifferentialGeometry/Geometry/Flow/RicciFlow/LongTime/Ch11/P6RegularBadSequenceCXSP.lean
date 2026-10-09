import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedForwardRegularCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScalarRegimeCXSP

set_option autoImplicit false

/-!
# 原 P6(c) 坏序列的实际正则化 / Regularization of the actual P6(c) bad sequence

输入逐项 bad inequality 正是 P6ScalarBadSequenceCXSP 的原产物；scalar 正性在体内证明。
每项调用 same-F forward producer，取 eta=1/(i+1)，半径 rho=r/2。
原点、原 stage、history index 与新 observation 的识别均保留。
统一 Anew=32768*exp(3)*A 只用于新 seed 的体积和空间球，不冒领原 hw(A)。

The three limits are proved for these actual new queries. The optional ratio
subsequence is selected using q.neckRadius at their new times, with no continuity
assumption. Neither kappa nor the old alpha accuracy condition is transported.
This is an intermediate producer, not a proof of the full hspine contract.
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

/-- The original counterexamples produce regular counterexamples on the same F.
All geometric data come from the actual forward seed theorem. The final ratio
dichotomy is evaluated at tau, and does not inherit the original nr regime. -/
theorem exists_regularized_scalar_bad_sequence_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {A : ℝ} (hA : 0 < A)
    (idx : ℕ → ℕ)
    (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).horizon)
    (p x : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
    (r : ℕ → ℝ) (htime : ∀ i, 2 * r i ^ 2 < (t i : ℝ))
    (hsmall : ∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory
      (t i) (p i) (r i))
    (hvol : ∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤ ballVolume
      ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i))
    (hx : ∀ i, x i ∈ riemannianBallOf
      ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (A * r i))
    (hbad : ∀ i : ℕ, (i : ℝ) + 1 < metricScalarAt
      ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (x i) * r i ^ 2)
    (hratio : Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0))
    (hescape : Tendsto (fun i => metricScalarAt
      ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (x i) * r i ^ 2)
      atTop atTop)
    (hlate : Tendsto (fun i => (t i : ℝ)) atTop atTop) :
    let Anew := 32768 * Real.exp 3 * A
    let Rold := fun i => metricScalarAt
      ((F.tower.history (idx i)).toHistory.stageMetric
        ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (x i)
    ∃ (N : ℕ → ℕ)
      (τ : ∀ i, Icc (0 : ℝ) (F.tower.history (N i)).horizon)
      (s : ℕ → RegularSlice F.observation)
      (p' x' : ∀ i, ((F.tower.history (N i)).toHistory.stageAt (τ i)).Carrier)
      (ρ : ℕ → ℝ),
      let Rnew := fun i => metricScalarAt
        ((F.tower.history (N i)).toHistory.stageMetric
          ((F.tower.history (N i)).toHistory.activeStage (τ i)) (τ i)) (x' i)
      (∀ i, idx i < N i) ∧ (∀ i, (t i : ℝ) < τ i) ∧
      (∀ i, (τ i : ℝ) - (t i : ℝ) < 1 / ((i : ℝ) + 1)) ∧
      (∀ i, (τ i : ℝ) ≤ 2 * (t i : ℝ)) ∧ (∀ i, (s i).time = (τ i : ℝ)) ∧
      (∀ i, (F.tower.history (idx i)).toHistory.stageAt (t i) =
        (F.tower.history (N i)).toHistory.stageAt (τ i)) ∧
      (∀ i, HEq (p' i) (p i)) ∧ (∀ i, HEq (x' i) (x i)) ∧
      (∀ i, ρ i = r i / 2) ∧ (∀ i, 0 < ρ i) ∧ (∀ i, 0 < (τ i : ℝ)) ∧
      (∀ i, 2 * ρ i ^ 2 < (τ i : ℝ)) ∧
      (∀ i, hasSmallParabolicCurvature (F.tower.history (N i)).toHistory
        (τ i) (p' i) (ρ i)) ∧
      (∀ i, ENNReal.ofReal (Anew⁻¹ * ρ i ^ 3) ≤ ballVolume
        ((F.tower.history (N i)).toHistory.stageMetric
          ((F.tower.history (N i)).toHistory.activeStage (τ i)) (τ i)) (p' i) (ρ i)) ∧
      (∀ i, x' i ∈ riemannianBallOf
        ((F.tower.history (N i)).toHistory.stageMetric
          ((F.tower.history (N i)).toHistory.activeStage (τ i)) (τ i))
        (p' i) (Anew * ρ i)) ∧
      (∀ i, Rold i / 2 ≤ Rnew i) ∧ (∀ i, 0 < Rnew i) ∧
      (∀ i, Rold i * r i ^ 2 / 8 ≤ Rnew i * ρ i ^ 2) ∧
      Tendsto (fun i => Rnew i * ρ i ^ 2) atTop atTop ∧
      Tendsto (fun i => ρ i / Real.sqrt (τ i : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun i => (τ i : ℝ)) atTop atTop ∧
      Tendsto (fun i => (τ i : ℝ) - (t i : ℝ)) atTop (𝓝 0) ∧
      ∀ q : CutoffParameters, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ((∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ i, ρ (φ i) ≤ Λ * q.neckRadius (τ (φ i))) ∨
          ((∀ i, q.neckRadius (τ (φ i)) ≤ ρ (φ i)) ∧
            Tendsto (fun i => ρ (φ i) / q.neckRadius (τ (φ i))) atTop atTop)) := by
  classical
  let Rold := fun i => metricScalarAt
    ((F.tower.history (idx i)).toHistory.stageMetric
      ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (x i)
  have hr (i : ℕ) : 0 < r i := (hsmall i).1
  have ht (i : ℕ) : 0 < (t i : ℝ) :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (r i))).trans_lt (htime i)
  have hRold (i : ℕ) : 0 < Rold i := by
    by_contra hnot
    have hnonpos : Rold i * r i ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) (sq_nonneg (r i))
    have hhigh : (i : ℝ) + 1 < Rold i * r i ^ 2 := hbad i
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  have hsingle (i : ℕ) := exists_forward_regular_seed_same_flow_CXSP F (idx i)
    (t i) (p i) (x i) (η := 1 / ((i : ℝ) + 1)) hA (ht i) (htime i)
    (hsmall i) (hvol i) (hx i) (hRold i) (by positivity)
  choose N hN τ htτ hshift hupper s hs hstage p' x' hp' hx' htime' hsmall' hvol' hball' hR'
    using hsingle
  let ρ : ℕ → ℝ := fun i => r i / 2
  let Rnew := fun i => metricScalarAt
    ((F.tower.history (N i)).toHistory.stageMetric
      ((F.tower.history (N i)).toHistory.activeStage (τ i)) (τ i)) (x' i)
  have hρ (i : ℕ) : 0 < ρ i := half_pos (hr i)
  have hτpos (i : ℕ) : 0 < (τ i : ℝ) := (ht i).trans (htτ i)
  have hRnew (i : ℕ) : 0 < Rnew i := (half_pos (hRold i)).trans_le (hR' i)
  have hproduct (i : ℕ) : Rold i * r i ^ 2 / 8 ≤ Rnew i * ρ i ^ 2 := by
    calc
      _ = (Rold i / 2) * ρ i ^ 2 := by dsimp only [ρ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hR' i) (sq_nonneg (ρ i))
  have hescape' : Tendsto (fun i => Rnew i * ρ i ^ 2) atTop atTop :=
    tendsto_atTop_mono hproduct (hescape.atTop_div_const (by norm_num : (0 : ℝ) < 8))
  have hratio' : Tendsto (fun i => ρ i / Real.sqrt (τ i : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => div_nonneg (hρ i).le (Real.sqrt_nonneg _)) ?_ hratio
    intro i
    calc
      _ ≤ r i / Real.sqrt (τ i : ℝ) :=
        div_le_div_of_nonneg_right (by dsimp only [ρ]; linarith [hr i])
          (Real.sqrt_nonneg _)
      _ ≤ r i / Real.sqrt (t i : ℝ) :=
        div_le_div_of_nonneg_left (hr i).le (Real.sqrt_pos.mpr (ht i))
          (Real.sqrt_le_sqrt (htτ i).le)
  have hlate' : Tendsto (fun i => (τ i : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun i => (htτ i).le) hlate
  have hnat : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hshift' : Tendsto (fun i => (τ i : ℝ) - (t i : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun i => sub_nonneg.mpr (htτ i).le) (fun i => (hshift i).le) hinv
  refine ⟨N, τ, s, p', x', ρ, hN, htτ, hshift, hupper, hs, hstage, hp', hx',
    (fun _ => rfl), hρ, hτpos, htime', hsmall', hvol', hball', hR', hRnew, hproduct,
    hescape', hratio', hlate', hshift', ?_⟩
  intro q
  exact seed_ratio_regime_subsequence_CXSP ρ (fun i => q.neckRadius (τ i))
    (fun i => q.neckRadius_pos _ (τ i).2.1)

end GC.LongTime.Ch11
