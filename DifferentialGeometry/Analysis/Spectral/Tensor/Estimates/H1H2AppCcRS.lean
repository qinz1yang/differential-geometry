import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1L6
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Mixed H1-H2 product estimate for mixed tensor passengers

On a closed three-manifold, an operator field with one intrinsic `L2` jet
acts on a mixed tensor with two intrinsic `L2` jets to produce an `H1` mixed
tensor.  The proof uses the mixed `H1 → L6` embedding, finite-volume
`L6 → L3`, and the covariant Leibniz rule for `appCcRS`.
-/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

set_option linter.unusedSectionVars false

open scoped ContDiff Manifold Topology BigOperators ENNReal
open MeasureTheory
open Tensor0SBundle
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem grad_inner_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold tensorL2Inner
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  change tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
      (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s S).toSection x))
      (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s S).toSection x)) =
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S x
  exact (tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s S S x).symm

private theorem h1_norm_sq_jet
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    ‖(⟨S⟩ : SmoothCcTensorH1 g r s)‖ ^ 2 =
      ‖S‖ ^ 2 + ‖covGrad (I := I) (M := M) g r s S‖ ^ 2 := by
  rw [SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M),
    tensorH1Inner_def,
    ← SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M) S,
    ← grad_inner_eq (I := I) (M := M) g r s S,
    ← SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M)
      (covGrad (I := I) (M := M) g r s S)]

/-- The mixed-tensor `H1` norm squared is the sum of the intrinsic zeroth and
first covariant `L2` jets. -/
theorem h1_jet_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    ‖(⟨S⟩ : SmoothCcTensorH1 g r s)‖ ^ 2 =
      ‖S‖ ^ 2 + ‖covGrad (I := I) (M := M) g r s S‖ ^ 2 :=
  h1_norm_sq_jet (I := I) (M := M) g r s S

private noncomputable def rsFiberFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) : M → ℝ := fun x =>
  Real.sqrt
    (riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))

private theorem fiber_rs_cont
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) : Continuous (rsFiberFun g r s S) := by
  apply Real.continuous_sqrt.comp
  have h := SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine h.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
    (I := I) (M := M) g r s x (S.toSection x),
    ← SmoothCcTensor.toFun_apply (I := I) (M := M) S x]

private theorem fiber_rs_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) : 0 ≤ rsFiberFun g r s S x :=
  Real.sqrt_nonneg _

private theorem tensor_l2_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hfun : S.toFun = fun x =>
      TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) (S.toSection x) := rfl
  rw [hfun]
  exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq
    (I := I) (M := M) g r s _

private theorem normSq_le_int
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C : SmoothCcTensor g r s) (F : M → ℝ)
    (hF : Integrable F (riemannianVolumeMeasure (I := I) (M := M) g))
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x
        (C.toSection x) ≤ F x) :
    ‖C‖ ^ 2 ≤ ∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  rw [SmoothCcTensor.norm_def (I := I) (M := M) C,
    tensor_l2_sq (I := I) (M := M) g r s C]
  have hint : Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x
        (C.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r s C
  exact integral_mono hint hF (fun x => hpt x)

private theorem fiber_rs_lp2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    lpNorm (rsFiberFun g r s S) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) = ‖S‖ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hcont := fiber_rs_cont (I := I) (M := M) g r s S
  have hmeas : AEStronglyMeasurable (rsFiberFun g r s S) μ :=
    hcont.aestronglyMeasurable
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hmeas]
  have hpoint : ∀ x : M,
      ‖rsFiberFun g r s S x‖ ^ ((2 : ENNReal).toReal) =
        riemannianFiberNormSq (I := I) (M := M) g r s x
          (S.toSection x) := by
    intro x
    rw [show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num,
      Real.norm_eq_abs, abs_of_nonneg (fiber_rs_nonneg g r s S x)]
    change (Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x
      (S.toSection x))) ^ (2 : ℝ) = _
    rw [Real.rpow_two, Real.sq_sqrt
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _)]
  simp_rw [hpoint]
  rw [show ((2 : ENNReal).toReal)⁻¹ = (1 / 2 : ℝ) by norm_num,
    ← Real.sqrt_eq_rpow]
  rw [← tensor_l2_sq (I := I) (M := M) g r s S,
    Real.sqrt_sq (tensorL2Norm_nonneg (I := I) (M := M) g r s S.toFun),
    ← SmoothCcTensor.norm_def (I := I) (M := M) S]

private theorem rsFiber_slotExtend
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (q : ℝ≥0∞) :
    lpNorm (rsFiberFun g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s S)) q
        (riemannianVolumeMeasure (I := I) (M := M) g) =
      Real.sqrt (Module.finrank ℝ E) *
        lpNorm (rsFiberFun g r s S) q
          (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let k : ℝ := Real.sqrt (Module.finrank ℝ E)
  have hfun :
      rsFiberFun g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s S) =
        k • rsFiberFun g r s S := by
    funext x
    change Real.sqrt
        (riemannianFiberNormSq (I := I) (M := M) g (r + 1) (s + 1) x
          ((slotExtend (I := I) (M := M) g r s S).toSection x)) =
      k * Real.sqrt
        (riemannianFiberNormSq (I := I) (M := M) g r s x
          (S.toSection x))
    rw [rfns_slotExtend_eq (I := I) (M := M) g r s S x,
      Real.sqrt_mul (Nat.cast_nonneg (Module.finrank ℝ E))]
  rw [hfun, lpNorm_const_smul]
  simp [k]

private theorem rsFiber3_le_6
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g r s,
      lpNorm (rsFiberFun g r s S) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        C * lpNorm (rsFiberFun g r s S) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let V : ℝ := (μ Set.univ ^ (1 / 6 : ℝ)).toReal
  refine ⟨V, ENNReal.toReal_nonneg, ?_⟩
  intro S
  have hcont := fiber_rs_cont (I := I) (M := M) g r s S
  have hmem : MemLp (rsFiberFun g r s S) 6 μ :=
    hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (f := rsFiberFun g r s S) (p := (3 : ℝ≥0∞)) (q := 6)
    (by norm_num) hcont.aestronglyMeasurable
  have hpow : μ Set.univ ^
      (1 / (3 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)
  have htop : eLpNorm (rsFiberFun g r s S) 6 μ * μ Set.univ ^
      (1 / (3 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.mul_ne_top hmem.eLpNorm_ne_top hpow
  have hreal := ENNReal.toReal_mono htop hcmp
  rw [toReal_eLpNorm hcont.aestronglyMeasurable, ENNReal.toReal_mul,
    toReal_eLpNorm hcont.aestronglyMeasurable,
    show 1 / (3 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal =
      (1 / 6 : ℝ) by norm_num] at hreal
  simpa only [V, mul_comm] using hreal

private theorem rs_l2_right
    (g : SmoothRiemannianMetric I M) (p r c : ℕ)
    (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r)
    (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g p r x
        (W.toSection x) ≤ B ^ 2) :
    ‖appCcRS (I := I) (M := M) g p r c Φ W‖ ≤ ‖Φ‖ * B := by
  classical
  set F : M → ℝ := fun x => B ^ 2 *
    riemannianFiberNormSq (I := I) (M := M) g r c x
      (Φ.toSection x) with hF_def
  have hF_int : Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [hF_def]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r c Φ).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g p c x
          ((appCcRS (I := I) (M := M) g p r c Φ W).toSection x) ≤ F x := by
    intro x
    rw [appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul
      (I := I) (M := M) g p r c x (Φ.toSection x) (W.toSection x)) ?_
    rw [hF_def]
    calc
      riemannianFiberNormSq (I := I) (M := M) g r c x (Φ.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g p r x (W.toSection x)
          ≤ riemannianFiberNormSq (I := I) (M := M) g r c x
              (Φ.toSection x) * B ^ 2 :=
        mul_le_mul_of_nonneg_left (hW x)
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g r c x _)
      _ = B ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r c x
          (Φ.toSection x) := by ring
  have hsq : ‖appCcRS (I := I) (M := M) g p r c Φ W‖ ^ 2 ≤
      ‖Φ‖ ^ 2 * B ^ 2 := by
    have h1 := normSq_le_int
      (I := I) (M := M) g p c
      (appCcRS (I := I) (M := M) g p r c Φ W) F hF_int hpt
    rw [hF_def, integral_const_mul] at h1
    have hbridge :=
      tensor_l2_sq
        (I := I) (M := M) g r c Φ
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    nlinarith [h1]
  have hrhs : 0 ≤ ‖Φ‖ * B := mul_nonneg (norm_nonneg _) hB
  refine le_of_sq_le_sq ?_ hrhs
  rw [mul_pow]
  exact hsq

/-- The complementary `L²` composition estimate: a pointwise-bounded
operator acts on an `L²` passenger. -/
private theorem rs_l2_left
    (g : SmoothRiemannianMetric I M) (p r c : ℕ)
    (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r)
    (A : ℝ) (hA : 0 ≤ A)
    (hΦ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r c x
        (Φ.toSection x) ≤ A ^ 2) :
    ‖appCcRS (I := I) (M := M) g p r c Φ W‖ ≤ A * ‖W‖ := by
  classical
  set F : M → ℝ := fun x => A ^ 2 *
    riemannianFiberNormSq (I := I) (M := M) g p r x
      (W.toSection x) with hF_def
  have hF_int : Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [hF_def]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g p r W).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g p c x
          ((appCcRS (I := I) (M := M) g p r c Φ W).toSection x) ≤ F x := by
    intro x
    rw [appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul
      (I := I) (M := M) g p r c x (Φ.toSection x) (W.toSection x)) ?_
    rw [hF_def]
    exact mul_le_mul_of_nonneg_right (hΦ x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g p r x _)
  have hsq : ‖appCcRS (I := I) (M := M) g p r c Φ W‖ ^ 2 ≤
      A ^ 2 * ‖W‖ ^ 2 := by
    have h1 := normSq_le_int
      (I := I) (M := M) g p c
      (appCcRS (I := I) (M := M) g p r c Φ W) F hF_int hpt
    rw [hF_def, integral_const_mul] at h1
    have hbridge := tensor_l2_sq (I := I) (M := M) g p r W
    rw [← hbridge, ← SmoothCcTensor.norm_def (I := I) (M := M)] at h1
    exact h1
  have hrhs : 0 ≤ A * ‖W‖ := mul_nonneg hA (norm_nonneg _)
  refine le_of_sq_le_sq ?_ hrhs
  rw [mul_pow]
  exact hsq

private theorem rs_l6_l3_l2
    (g : SmoothRiemannianMetric I M) (p r c : ℕ)
    (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) :
    ‖appCcRS (I := I) (M := M) g p r c Φ W‖ ≤
      lpNorm (rsFiberFun g r c Φ) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) *
        lpNorm (rsFiberFun g p r W) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let Y : SmoothCcTensor g p c := appCcRS (I := I) (M := M) g p r c Φ W
  have hΦc := fiber_rs_cont (I := I) (M := M) g r c Φ
  have hWc := fiber_rs_cont (I := I) (M := M) g p r W
  have hYc := fiber_rs_cont (I := I) (M := M) g p c Y
  have hΦmem : MemLp (rsFiberFun g r c Φ) 6 μ :=
    hΦc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hWmem : MemLp (rsFiberFun g p r W) 3 μ :=
    hWc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hYmem : MemLp (rsFiberFun g p c Y) 2 μ :=
    hYc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  haveI : ENNReal.HolderTriple (6 : ENNReal) 3 2 := by
    exact ENNReal.HolderTriple.of_toReal (by
      rw [Real.holderTriple_iff]
      norm_num)
  have hpt : ∀ x : M,
      rsFiberFun g p c Y x ≤
        rsFiberFun g r c Φ x * rsFiberFun g p r W x := by
    intro x
    dsimp [rsFiberFun, Y]
    have h := riemannianFiberNormSq_compRS_le_mul
      (I := I) (M := M) g p r c x (Φ.toSection x) (W.toSection x)
    refine (Real.sqrt_le_sqrt h).trans_eq ?_
    rw [Real.sqrt_mul
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g r c x _)]
  have hmono :
      eLpNorm (rsFiberFun g p c Y) 2 μ ≤
        eLpNorm (fun x => rsFiberFun g r c Φ x * rsFiberFun g p r W x) 2 μ := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (fiber_rs_nonneg g p c Y x),
      Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (fiber_rs_nonneg g r c Φ x)
          (fiber_rs_nonneg g p r W x))]
    exact hpt x
  have hholder :
      eLpNorm (fun x => rsFiberFun g r c Φ x * rsFiberFun g p r W x) 2 μ ≤
        eLpNorm (rsFiberFun g r c Φ) 6 μ *
          eLpNorm (rsFiberFun g p r W) 3 μ := by
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
        (p := 6) (q := 3) (r := 2) (μ := μ)
        (hΦc.aestronglyMeasurable) (hWc.aestronglyMeasurable)
        (fun a b : ℝ => a * b) 1
        (Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs, abs_mul]
          norm_num)))
  have hENN := hmono.trans hholder
  have hfinite :
      eLpNorm (rsFiberFun g r c Φ) 6 μ *
          eLpNorm (rsFiberFun g p r W) 3 μ ≠ ⊤ :=
    ENNReal.mul_ne_top hΦmem.eLpNorm_ne_top hWmem.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hfinite hENN
  rw [toReal_eLpNorm hYmem.aestronglyMeasurable,
    ENNReal.toReal_mul, toReal_eLpNorm hΦmem.aestronglyMeasurable,
    toReal_eLpNorm hWmem.aestronglyMeasurable] at hreal
  rw [← fiber_rs_lp2 (I := I) (M := M) g p c Y]
  exact hreal

/-- In dimension three, an operator field with one `L2` jet acting on a
mixed tensor with two `L2` jets is controlled in mixed-tensor `H1`. -/
theorem appRS_h1_h2_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
        0 ≤ A → 0 ≤ B →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
        ‖(⟨appCcRS (I := I) (M := M) g p r c Φ W⟩ :
            SmoothCcTensorH1 g p c)‖ ≤ C * A * B := by
  classical
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g p r
  obtain ⟨CΦ, hCΦ, hΦ6⟩ := h1_lp6_fiber_rs (I := I) (M := M) hDim g r c
  obtain ⟨CG, hCG, hG6⟩ := h1_lp6_fiber_rs (I := I) (M := M) hDim g p (r + 1)
  obtain ⟨CV, hCV, h63⟩ := rsFiber3_le_6 (I := I) (M := M) g p (r + 1)
  let sd : ℝ := Real.sqrt (Module.finrank ℝ E)
  let Ks : ℝ := sd * CΦ * CV * CG
  let K : ℝ := Cpt + (Cpt + Ks)
  refine ⟨K, by
    dsimp [K, Ks, sd]
    positivity, ?_⟩
  intro Φ W A B hA hB hΦjet hWjet
  let G : SmoothCcTensor g p (r + 1) :=
    covGrad (I := I) (M := M) g p r W
  let Y : SmoothCcTensor g p c :=
    appCcRS (I := I) (M := M) g p r c Φ W
  have hΦsq :
      ‖Φ‖ ^ 2 + ‖covGrad (I := I) (M := M) g r c Φ‖ ^ 2 ≤ A ^ 2 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hΦjet
  have hΦ0 : ‖Φ‖ ≤ A := by
    nlinarith [sq_nonneg ‖covGrad (I := I) (M := M) g r c Φ‖,
      norm_nonneg Φ]
  have hΦ1 : ‖covGrad (I := I) (M := M) g r c Φ‖ ≤ A := by
    nlinarith [sq_nonneg ‖Φ‖,
      norm_nonneg (covGrad (I := I) (M := M) g r c Φ)]
  have hΦH1 : ‖(⟨Φ⟩ : SmoothCcTensorH1 g r c)‖ ≤ A := by
    have hsq : ‖(⟨Φ⟩ : SmoothCcTensorH1 g r c)‖ ^ 2 ≤ A ^ 2 := by
      rw [h1_norm_sq_jet (I := I) (M := M) g r c Φ]
      exact hΦsq
    nlinarith [norm_nonneg (⟨Φ⟩ : SmoothCcTensorH1 g r c)]
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range 3 := by
    rw [hDim]
  have hWsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g p r x
          (W.toSection x) ≤ (Cpt * B) ^ 2 := by
    intro x
    have hx := hpt W x
    rw [hrange] at hx
    calc
      _ ≤ Cpt ^ 2 * (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) := hx
      _ ≤ Cpt ^ 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_left hWjet (sq_nonneg Cpt)
      _ = (Cpt * B) ^ 2 := by ring
  have hGsq :
      ‖G‖ ^ 2 + ‖covGrad (I := I) (M := M) g p (r + 1) G‖ ^ 2 ≤ B ^ 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2 := by
        dsimp [G]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero]
        nlinarith [sq_nonneg ‖W‖]
      _ ≤ B ^ 2 := hWjet
  have hGH1 : ‖(⟨G⟩ : SmoothCcTensorH1 g p (r + 1))‖ ≤ B := by
    have hsq : ‖(⟨G⟩ : SmoothCcTensorH1 g p (r + 1))‖ ^ 2 ≤ B ^ 2 := by
      rw [h1_norm_sq_jet (I := I) (M := M) g p (r + 1) G]
      exact hGsq
    nlinarith [norm_nonneg (⟨G⟩ : SmoothCcTensorH1 g p (r + 1))]
  have hΦ6' :
      lpNorm (rsFiberFun g r c Φ) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CΦ * A := by
    calc
      _ ≤ CΦ * ‖(⟨Φ⟩ : SmoothCcTensorH1 g r c)‖ := by
        simpa only [rsFiberFun] using hΦ6 (⟨Φ⟩ : SmoothCcTensorH1 g r c)
      _ ≤ CΦ * A := mul_le_mul_of_nonneg_left hΦH1 hCΦ
  have hG6' :
      lpNorm (rsFiberFun g p (r + 1) G) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CG * B := by
    calc
      _ ≤ CG * ‖(⟨G⟩ : SmoothCcTensorH1 g p (r + 1))‖ := by
        simpa only [rsFiberFun] using hG6 (⟨G⟩ : SmoothCcTensorH1 g p (r + 1))
      _ ≤ CG * B := mul_le_mul_of_nonneg_left hGH1 hCG
  have hG3' :
      lpNorm (rsFiberFun g p (r + 1) G) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CV * (CG * B) := by
    exact (h63 G).trans (mul_le_mul_of_nonneg_left hG6' hCV)
  have hslot6 :
      lpNorm (rsFiberFun g (r + 1) (c + 1)
          (slotExtend (I := I) (M := M) g r c Φ)) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        sd * (CΦ * A) := by
    rw [rsFiber_slotExtend (I := I) (M := M) g r c Φ 6]
    exact mul_le_mul_of_nonneg_left hΦ6' (Real.sqrt_nonneg _)
  have hY0 : ‖Y‖ ≤ Cpt * A * B := by
    have h0 := rs_l2_right
      (I := I) (M := M) g p r c Φ W
      (Cpt * B) (mul_nonneg hCpt hB) hWsup
    dsimp [Y]
    calc
      _ ≤ ‖Φ‖ * (Cpt * B) := h0
      _ ≤ A * (Cpt * B) :=
        mul_le_mul_of_nonneg_right hΦ0 (mul_nonneg hCpt hB)
      _ = Cpt * A * B := by ring
  have hcross :
      ‖appCcRS (I := I) (M := M) g p r (c + 1)
          (covGrad (I := I) (M := M) g r c Φ) W‖ ≤ Cpt * A * B := by
    have hc := rs_l2_right
      (I := I) (M := M) g p r (c + 1)
      (covGrad (I := I) (M := M) g r c Φ) W
      (Cpt * B) (mul_nonneg hCpt hB) hWsup
    calc
      _ ≤ ‖covGrad (I := I) (M := M) g r c Φ‖ * (Cpt * B) := hc
      _ ≤ A * (Cpt * B) :=
        mul_le_mul_of_nonneg_right hΦ1 (mul_nonneg hCpt hB)
      _ = Cpt * A * B := by ring
  have hslot :
      ‖appCcRS (I := I) (M := M) g p (r + 1) (c + 1)
          (slotExtend (I := I) (M := M) g r c Φ) G‖ ≤ Ks * A * B := by
    have hp := rs_l6_l3_l2 (I := I) (M := M) g p (r + 1) (c + 1)
      (slotExtend (I := I) (M := M) g r c Φ) G
    calc
      _ ≤
          lpNorm (rsFiberFun g (r + 1) (c + 1)
              (slotExtend (I := I) (M := M) g r c Φ)) 6
              (riemannianVolumeMeasure (I := I) (M := M) g) *
            lpNorm (rsFiberFun g p (r + 1) G) 3
              (riemannianVolumeMeasure (I := I) (M := M) g) := hp
      _ ≤ (sd * (CΦ * A)) * (CV * (CG * B)) :=
        mul_le_mul hslot6 hG3' lpNorm_nonneg
          (mul_nonneg (Real.sqrt_nonneg _)
            (mul_nonneg hCΦ hA))
      _ = Ks * A * B := by dsimp [Ks, sd]; ring
  have hY1 :
      ‖covGrad (I := I) (M := M) g p c Y‖ ≤
        (Cpt + Ks) * A * B := by
    rw [show covGrad (I := I) (M := M) g p c Y =
        appCcRS (I := I) (M := M) g p r (c + 1)
            (covGrad (I := I) (M := M) g r c Φ) W +
          appCcRS (I := I) (M := M) g p (r + 1) (c + 1)
            (slotExtend (I := I) (M := M) g r c Φ) G by
      dsimp [Y, G]
      exact covGrad_appCcRS_eq (I := I) (M := M) g p r c Φ W]
    calc
      _ ≤
          ‖appCcRS (I := I) (M := M) g p r (c + 1)
              (covGrad (I := I) (M := M) g r c Φ) W‖ +
            ‖appCcRS (I := I) (M := M) g p (r + 1) (c + 1)
              (slotExtend (I := I) (M := M) g r c Φ) G‖ := norm_add_le _ _
      _ ≤ Cpt * A * B + Ks * A * B := add_le_add hcross hslot
      _ = (Cpt + Ks) * A * B := by ring
  have hYH1 : ‖(⟨Y⟩ : SmoothCcTensorH1 g p c)‖ ≤ ‖Y‖ +
      ‖covGrad (I := I) (M := M) g p c Y‖ := by
    have hsq : ‖(⟨Y⟩ : SmoothCcTensorH1 g p c)‖ ^ 2 =
        ‖Y‖ ^ 2 + ‖covGrad (I := I) (M := M) g p c Y‖ ^ 2 :=
      h1_norm_sq_jet (I := I) (M := M) g p c Y
    have hprod : 0 ≤ ‖Y‖ * ‖covGrad (I := I) (M := M) g p c Y‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    refine le_of_sq_le_sq ?_ (add_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [hsq]
    nlinarith
  change ‖(⟨Y⟩ : SmoothCcTensorH1 g p c)‖ ≤ _
  calc
    _ ≤ ‖Y‖ + ‖covGrad (I := I) (M := M) g p c Y‖ := hYH1
    _ ≤ Cpt * A * B + (Cpt + Ks) * A * B := add_le_add hY0 hY1
    _ = K * A * B := by dsimp [K]; ring

/-- In dimension three, the complementary mixed product allocation also
holds: an operator field with two intrinsic `L2` jets acting on a passenger
with one intrinsic `L2` jet is controlled in mixed-tensor `H1`.

This orientation is needed by nested Ricci--DeTurck coefficients: an inner
composition is first estimated in `H1`, while the outer moving trace remains
in the low `H2` class. -/
theorem appRS_h2_h1_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
        0 ≤ A → 0 ≤ B →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
        ‖(⟨appCcRS (I := I) (M := M) g p r c Φ W⟩ :
            SmoothCcTensorH1 g p c)‖ ≤ C * A * B := by
  classical
  obtain ⟨Cpt, hCpt, hpt⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g r c
  obtain ⟨CG, hCG, hG6⟩ := h1_lp6_fiber_rs (I := I) (M := M) hDim g r (c + 1)
  obtain ⟨CW, hCW, hW6⟩ := h1_lp6_fiber_rs (I := I) (M := M) hDim g p r
  obtain ⟨CV, hCV, h63⟩ := rsFiber3_le_6 (I := I) (M := M) g p r
  let sd : ℝ := Real.sqrt (Module.finrank ℝ E)
  let Kcross : ℝ := CG * CV * CW
  let Kslot : ℝ := sd * Cpt
  let K : ℝ := Cpt + (Kcross + Kslot)
  refine ⟨K, by
    dsimp [K, Kcross, Kslot, sd]
    positivity, ?_⟩
  intro Φ W A B hA hB hΦjet hWjet
  let GΦ : SmoothCcTensor g r (c + 1) :=
    covGrad (I := I) (M := M) g r c Φ
  let GW : SmoothCcTensor g p (r + 1) :=
    covGrad (I := I) (M := M) g p r W
  let Y : SmoothCcTensor g p c :=
    appCcRS (I := I) (M := M) g p r c Φ W
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range 3 := by
    rw [hDim]
  have hΦsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r c x
          (Φ.toSection x) ≤ (Cpt * A) ^ 2 := by
    intro x
    calc
      _ ≤ Cpt ^ 2 * (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) := by
        simpa only [hrange] using hpt Φ x
      _ ≤ Cpt ^ 2 * A ^ 2 :=
        mul_le_mul_of_nonneg_left hΦjet (sq_nonneg Cpt)
      _ = (Cpt * A) ^ 2 := by ring
  have hW0 : ‖W‖ ≤ B := by
    have h0 : ‖W‖ ^ 2 ≤ B ^ 2 := by
      calc
        _ ≤ ∑ j ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2 := by
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
            iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add]
          exact le_add_of_nonneg_right (sq_nonneg _)
        _ ≤ B ^ 2 := hWjet
    nlinarith [norm_nonneg W]
  have hGW0 : ‖GW‖ ≤ B := by
    have h0 : ‖GW‖ ^ 2 ≤ B ^ 2 := by
      calc
        _ ≤ ∑ j ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2 := by
          dsimp only [GW]
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
            iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add]
          exact le_add_of_nonneg_left (sq_nonneg _)
        _ ≤ B ^ 2 := hWjet
    nlinarith [norm_nonneg GW]
  have hGΦsq :
      ‖GΦ‖ ^ 2 + ‖covGrad (I := I) (M := M) g r (c + 1) GΦ‖ ^ 2 ≤
        A ^ 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2 := by
        dsimp only [GΦ]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero]
        exact le_add_of_nonneg_left (sq_nonneg _)
      _ ≤ A ^ 2 := hΦjet
  have hGΦH1 : ‖(⟨GΦ⟩ : SmoothCcTensorH1 g r (c + 1))‖ ≤ A := by
    have hsq : ‖(⟨GΦ⟩ : SmoothCcTensorH1 g r (c + 1))‖ ^ 2 ≤ A ^ 2 := by
      rw [h1_norm_sq_jet (I := I) (M := M) g r (c + 1) GΦ]
      exact hGΦsq
    nlinarith [norm_nonneg (⟨GΦ⟩ : SmoothCcTensorH1 g r (c + 1))]
  have hWsq :
      ‖W‖ ^ 2 + ‖covGrad (I := I) (M := M) g p r W‖ ^ 2 ≤ B ^ 2 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hWjet
  have hWH1 : ‖(⟨W⟩ : SmoothCcTensorH1 g p r)‖ ≤ B := by
    have hsq : ‖(⟨W⟩ : SmoothCcTensorH1 g p r)‖ ^ 2 ≤ B ^ 2 := by
      rw [h1_norm_sq_jet (I := I) (M := M) g p r W]
      exact hWsq
    nlinarith [norm_nonneg (⟨W⟩ : SmoothCcTensorH1 g p r)]
  have hGΦ6 :
      lpNorm (rsFiberFun g r (c + 1) GΦ) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CG * A := by
    calc
      _ ≤ CG * ‖(⟨GΦ⟩ : SmoothCcTensorH1 g r (c + 1))‖ := by
        simpa only [rsFiberFun] using
          hG6 (⟨GΦ⟩ : SmoothCcTensorH1 g r (c + 1))
      _ ≤ CG * A := mul_le_mul_of_nonneg_left hGΦH1 hCG
  have hW6' :
      lpNorm (rsFiberFun g p r W) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CW * B := by
    calc
      _ ≤ CW * ‖(⟨W⟩ : SmoothCcTensorH1 g p r)‖ := by
        simpa only [rsFiberFun] using hW6 (⟨W⟩ : SmoothCcTensorH1 g p r)
      _ ≤ CW * B := mul_le_mul_of_nonneg_left hWH1 hCW
  have hW3 :
      lpNorm (rsFiberFun g p r W) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CV * (CW * B) :=
    (h63 W).trans (mul_le_mul_of_nonneg_left hW6' hCV)
  have hslotSup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g (r + 1) (c + 1) x
          ((slotExtend (I := I) (M := M) g r c Φ).toSection x) ≤
        (sd * (Cpt * A)) ^ 2 := by
    intro x
    rw [rfns_slotExtend_eq (I := I) (M := M) g r c Φ x]
    have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
    calc
      (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g r c x
            (Φ.toSection x)
          ≤ (Module.finrank ℝ E : ℝ) * (Cpt * A) ^ 2 :=
        mul_le_mul_of_nonneg_left (hΦsup x) hfr
      _ = (sd * (Cpt * A)) ^ 2 := by
        rw [show sd ^ 2 = (Module.finrank ℝ E : ℝ) by
          simp only [sd, Real.sq_sqrt hfr]]
        ring
  have hY0 : ‖Y‖ ≤ Cpt * A * B := by
    have h0 := rs_l2_left
      (I := I) (M := M) g p r c Φ W
      (Cpt * A) (mul_nonneg hCpt hA) hΦsup
    dsimp only [Y]
    calc
      _ ≤ (Cpt * A) * ‖W‖ := h0
      _ ≤ (Cpt * A) * B :=
        mul_le_mul_of_nonneg_left hW0 (mul_nonneg hCpt hA)
      _ = Cpt * A * B := by ring
  have hcross :
      ‖appCcRS (I := I) (M := M) g p r (c + 1) GΦ W‖ ≤
        Kcross * A * B := by
    have hp := rs_l6_l3_l2 (I := I) (M := M) g p r (c + 1) GΦ W
    calc
      _ ≤ lpNorm (rsFiberFun g r (c + 1) GΦ) 6
            (riemannianVolumeMeasure (I := I) (M := M) g) *
          lpNorm (rsFiberFun g p r W) 3
            (riemannianVolumeMeasure (I := I) (M := M) g) := hp
      _ ≤ (CG * A) * (CV * (CW * B)) :=
        mul_le_mul hGΦ6 hW3 lpNorm_nonneg
          (mul_nonneg hCG hA)
      _ = Kcross * A * B := by dsimp only [Kcross]; ring
  have hslot :
      ‖appCcRS (I := I) (M := M) g p (r + 1) (c + 1)
          (slotExtend (I := I) (M := M) g r c Φ) GW‖ ≤
        Kslot * A * B := by
    have hs := rs_l2_left
      (I := I) (M := M) g p (r + 1) (c + 1)
      (slotExtend (I := I) (M := M) g r c Φ) GW
      (sd * (Cpt * A))
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCpt hA)) hslotSup
    calc
      _ ≤ (sd * (Cpt * A)) * ‖GW‖ := hs
      _ ≤ (sd * (Cpt * A)) * B :=
        mul_le_mul_of_nonneg_left hGW0
          (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCpt hA))
      _ = Kslot * A * B := by dsimp only [Kslot, sd]; ring
  have hY1 :
      ‖covGrad (I := I) (M := M) g p c Y‖ ≤
        (Kcross + Kslot) * A * B := by
    rw [show covGrad (I := I) (M := M) g p c Y =
        appCcRS (I := I) (M := M) g p r (c + 1) GΦ W +
          appCcRS (I := I) (M := M) g p (r + 1) (c + 1)
            (slotExtend (I := I) (M := M) g r c Φ) GW by
      dsimp only [Y, GΦ, GW]
      exact covGrad_appCcRS_eq (I := I) (M := M) g p r c Φ W]
    calc
      _ ≤ ‖appCcRS (I := I) (M := M) g p r (c + 1) GΦ W‖ +
          ‖appCcRS (I := I) (M := M) g p (r + 1) (c + 1)
            (slotExtend (I := I) (M := M) g r c Φ) GW‖ := norm_add_le _ _
      _ ≤ Kcross * A * B + Kslot * A * B := add_le_add hcross hslot
      _ = (Kcross + Kslot) * A * B := by ring
  have hYH1 : ‖(⟨Y⟩ : SmoothCcTensorH1 g p c)‖ ≤
      ‖Y‖ + ‖covGrad (I := I) (M := M) g p c Y‖ := by
    have hsq : ‖(⟨Y⟩ : SmoothCcTensorH1 g p c)‖ ^ 2 =
        ‖Y‖ ^ 2 + ‖covGrad (I := I) (M := M) g p c Y‖ ^ 2 :=
      h1_norm_sq_jet (I := I) (M := M) g p c Y
    refine le_of_sq_le_sq ?_ (add_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [hsq]
    nlinarith [mul_nonneg (norm_nonneg Y)
      (norm_nonneg (covGrad (I := I) (M := M) g p c Y))]
  change ‖(⟨Y⟩ : SmoothCcTensorH1 g p c)‖ ≤ _
  calc
    _ ≤ ‖Y‖ + ‖covGrad (I := I) (M := M) g p c Y‖ := hYH1
    _ ≤ Cpt * A * B + (Kcross + Kslot) * A * B := add_le_add hY0 hY1
    _ = K * A * B := by dsimp only [K]; ring

/-- On a closed three-manifold, the intrinsic mixed-tensor `H2` jet is an
algebra for `appCcRS`.  The middle second-derivative cell is discharged by the
canonical two-arm Gagliardo--Nirenberg product-grid estimate. -/
theorem appRS_h2_h2_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
        0 ≤ A → 0 ≤ B →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g p c j
            (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
          (C * A * B) ^ 2 := by
  classical
  obtain ⟨CΦ, hCΦ, hΦpt⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g r c
  obtain ⟨CW, hCW, hWpt⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g p r
  let G : ℕ → ℝ := fun i =>
    (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g r p c r i).choose
  have hG : ∀ i, 0 ≤ G i := fun i =>
    (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g r p c r i).choose_spec.1
  let K : ℝ := ∑ i ∈ Finset.range 3,
    appCcGdiag (E := E) i * G i * (CW ^ 2 + CΦ ^ 2)
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg
        (mul_nonneg (appCcGdiag_nonneg (E := E) i) (hG i))
        (add_nonneg (sq_nonneg CW) (sq_nonneg CΦ))
  let C : ℝ := Real.sqrt K
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro Φ W A B hA hB hΦ hW
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) =
      Finset.range 3 := by
    rw [hDim]
  have hΦsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r c x
          (Φ.toSection x) ≤ (CΦ * A) ^ 2 := by
    intro x
    calc
      _ ≤ CΦ ^ 2 * (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) := by
        simpa only [hrange] using hΦpt Φ x
      _ ≤ CΦ ^ 2 * A ^ 2 :=
        mul_le_mul_of_nonneg_left hΦ (sq_nonneg CΦ)
      _ = (CΦ * A) ^ 2 := by ring
  have hWsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g p r x
          (W.toSection x) ≤ (CW * B) ^ 2 := by
    intro x
    calc
      _ ≤ CW ^ 2 * (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) := by
        simpa only [hrange] using hWpt W x
      _ ≤ CW ^ 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_left hW (sq_nonneg CW)
      _ = (CW * B) ^ 2 := by ring
  have hterm : ∀ i : ℕ, i < 3 →
      ‖iteratedCovGrad (I := I) g p c i
          (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2 ≤
        appCcGdiag (E := E) i * G i * (CW ^ 2 + CΦ ^ 2) *
          A ^ 2 * B ^ 2 := by
    intro i hi
    let grid : M → ℝ := fun x =>
      ∑ n ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g r (c + n) x
            ((iteratedCovGrad (I := I) g r c n Φ).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - n),
            riemannianFiberNormSq (I := I) (M := M) g p (r + l) x
              ((iteratedCovGrad (I := I) g p r l W).toSection x)
    obtain ⟨hgridInt, hgridBound⟩ :=
      (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g r p c r i).choose_spec.2
        Φ W (CΦ * A) (CW * B) (mul_nonneg hCΦ hA)
          (mul_nonneg hCW hB) hΦsup hWsup
    have hgridInt' : Integrable grid
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [grid] using hgridInt
    have hgridBound' :
        (∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          G i * ((CW * B) ^ 2 *
              (∑ n ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g r c n Φ‖ ^ 2) +
            (CΦ * A) ^ 2 *
              (∑ l ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g p r l W‖ ^ 2)) := by
      simpa only [grid, G] using hgridBound
    have hΦwin : (∑ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g r c n Φ‖ ^ 2) ≤ A ^ 2 := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) ?_).trans hΦ
      intro n _ _
      exact sq_nonneg _
    have hWwin : (∑ l ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g p r l W‖ ^ 2) ≤ B ^ 2 := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) ?_).trans hW
      intro l _ _
      exact sq_nonneg _
    have hgridFinal :
        (∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          G i * (CW ^ 2 + CΦ ^ 2) * A ^ 2 * B ^ 2 := by
      calc
        _ ≤ G i * ((CW * B) ^ 2 *
              (∑ n ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g r c n Φ‖ ^ 2) +
            (CΦ * A) ^ 2 *
              (∑ l ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g p r l W‖ ^ 2)) := hgridBound'
        _ ≤ G i * ((CW * B) ^ 2 * A ^ 2 +
            (CΦ * A) ^ 2 * B ^ 2) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (hG i)
          · exact mul_le_mul_of_nonneg_left hΦwin (sq_nonneg (CW * B))
          · exact mul_le_mul_of_nonneg_left hWwin (sq_nonneg (CΦ * A))
        _ = G i * (CW ^ 2 + CΦ ^ 2) * A ^ 2 * B ^ 2 := by ring
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g p (c + i)
      (iteratedCovGrad (I := I) g p c i
        (appCcRS (I := I) (M := M) g p r c Φ W))
      (fun x => appCcGdiag (E := E) i * grid x)
      (hgridInt'.const_mul (appCcGdiag (E := E) i))
      (fun x => by
        simpa only [grid] using
          (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
            (I := I) (M := M) g i p r c Φ W x))
    calc
      _ ≤ ∫ x, appCcGdiag (E := E) i * grid x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := key
      _ = appCcGdiag (E := E) i *
          ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ appCcGdiag (E := E) i *
          (G i * (CW ^ 2 + CΦ ^ 2) * A ^ 2 * B ^ 2) :=
        mul_le_mul_of_nonneg_left hgridFinal
          (appCcGdiag_nonneg (E := E) i)
      _ = appCcGdiag (E := E) i * G i * (CW ^ 2 + CΦ ^ 2) *
          A ^ 2 * B ^ 2 := by ring
  calc
    (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g p c i
          (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2)
        ≤ ∑ i ∈ Finset.range 3,
          (appCcGdiag (E := E) i * G i * (CW ^ 2 + CΦ ^ 2) *
            A ^ 2 * B ^ 2) :=
      Finset.sum_le_sum fun i hi => hterm i (Finset.mem_range.mp hi)
    _ = K * A ^ 2 * B ^ 2 := by
      dsimp only [K]
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = (C * A * B) ^ 2 := by
      rw [mul_pow, mul_pow, show C ^ 2 = K by
        simp only [C, Real.sq_sqrt hK]]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
