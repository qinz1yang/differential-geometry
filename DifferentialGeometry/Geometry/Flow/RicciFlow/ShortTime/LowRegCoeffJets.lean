import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H3GridIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2AppCcRS
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldTameEnvelope
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefold
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0LowJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSThreeArmCancel

/-!
# Low-regularity jets of concrete Ricci--DeTurck coefficients

This file converts the intrinsic antidiagonal product-grid bounds for the
realized metric path into the first two `L2` jets of the concrete order-zero
Ricci and DeTurck `DLa` coefficient fields.  Only the metric jet through order
three is used.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem iteratedCovGrad_smul_real
    (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (W : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • W) =
      c • iteratedCovGrad (I := I) g r s j W := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

private theorem jet_two
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j ((2 : ℝ) • W)‖ ^ 2) =
      4 * ∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs]
  norm_num

private theorem jet_sum2
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W Z : SmoothCcTensor g r s) (A B : ℝ)
    (hW : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2) ≤ A ^ 2)
    (hZ : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) ≤ B ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (W + Z)‖ ^ 2) ≤
      2 * (A ^ 2 + B ^ 2) := by
  have hterm : ∀ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (W + Z)‖ ^ 2 ≤
        2 * (‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) := by
    intro j hj
    rw [iteratedCovGrad_add]
    have htri := norm_add_le
      (iteratedCovGrad (I := I) g r s j W)
      (iteratedCovGrad (I := I) g r s j Z)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg
      (‖iteratedCovGrad (I := I) g r s j W‖ -
        ‖iteratedCovGrad (I := I) g r s j Z‖)]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        2 * (‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) :=
      Finset.sum_le_sum hterm
    _ = 2 * ((∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2)) := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * (A ^ 2 + B ^ 2) := by gcongr

private theorem jet_add4
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (A B C D : SmoothCcTensor g r s) (a b c d : ℝ)
    (hA : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) ≤ a ^ 2)
    (hB : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) ≤ b ^ 2)
    (hC : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j C‖ ^ 2) ≤ c ^ 2)
    (hD : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j D‖ ^ 2) ≤ d ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j
        ((-2 : ℝ) • A + ((B + C) + D))‖ ^ 2) ≤
      4 * (4 * a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  classical
  have hper : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g r s j
        ((-2 : ℝ) • A + ((B + C) + D))‖ ^ 2 ≤
      4 * (4 * ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g r s j C‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g r s j D‖ ^ 2) := by
    intro j
    have hgrad : iteratedCovGrad (I := I) g r s j
        ((-2 : ℝ) • A + ((B + C) + D)) =
        (-2 : ℝ) • iteratedCovGrad (I := I) g r s j A +
          ((iteratedCovGrad (I := I) g r s j B +
            iteratedCovGrad (I := I) g r s j C) +
            iteratedCovGrad (I := I) g r s j D) := by
      rw [iteratedCovGrad_add, iteratedCovGrad_smul_real,
        iteratedCovGrad_add, iteratedCovGrad_add]
    rw [hgrad]
    let x : ℝ := 2 * ‖iteratedCovGrad (I := I) g r s j A‖
    let y : ℝ := ‖iteratedCovGrad (I := I) g r s j B‖
    let z : ℝ := ‖iteratedCovGrad (I := I) g r s j C‖
    let w : ℝ := ‖iteratedCovGrad (I := I) g r s j D‖
    have hx : 0 ≤ x := mul_nonneg (by norm_num) (norm_nonneg _)
    have hy : 0 ≤ y := norm_nonneg _
    have hz : 0 ≤ z := norm_nonneg _
    have hw : 0 ≤ w := norm_nonneg _
    have htri : ‖(-2 : ℝ) • iteratedCovGrad (I := I) g r s j A +
          ((iteratedCovGrad (I := I) g r s j B +
            iteratedCovGrad (I := I) g r s j C) +
            iteratedCovGrad (I := I) g r s j D)‖ ≤ x + y + z + w := by
      calc
        _ ≤ ‖(-2 : ℝ) • iteratedCovGrad (I := I) g r s j A‖ +
            ‖(iteratedCovGrad (I := I) g r s j B +
              iteratedCovGrad (I := I) g r s j C) +
              iteratedCovGrad (I := I) g r s j D‖ := norm_add_le _ _
        _ ≤ ‖(-2 : ℝ) • iteratedCovGrad (I := I) g r s j A‖ +
            (‖iteratedCovGrad (I := I) g r s j B +
              iteratedCovGrad (I := I) g r s j C‖ +
              ‖iteratedCovGrad (I := I) g r s j D‖) :=
            add_le_add_left (norm_add_le _ _) _
        _ ≤ ‖(-2 : ℝ) • iteratedCovGrad (I := I) g r s j A‖ +
            ((‖iteratedCovGrad (I := I) g r s j B‖ +
              ‖iteratedCovGrad (I := I) g r s j C‖) +
              ‖iteratedCovGrad (I := I) g r s j D‖) :=
            add_le_add_left (add_le_add_right (norm_add_le _ _) _) _
        _ = x + y + z + w := by
          simp only [x, y, z, w, norm_smul, Real.norm_eq_abs, abs_of_nonneg
            (by norm_num : (0 : ℝ) ≤ 2)]
          ring
    have hsq : ‖(-2 : ℝ) • iteratedCovGrad (I := I) g r s j A +
          ((iteratedCovGrad (I := I) g r s j B +
            iteratedCovGrad (I := I) g r s j C) +
            iteratedCovGrad (I := I) g r s j D)‖ ^ 2 ≤
        (x + y + z + w) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hcauchy : (x + y + z + w) ^ 2 ≤
        4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - w),
        sq_nonneg (y - z), sq_nonneg (y - w), sq_nonneg (z - w)]
    exact hsq.trans (hcauchy.trans_eq (by simp only [x, y, z, w]; ring))
  calc
    (∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g r s j
          ((-2 : ℝ) • A + ((B + C) + D))‖ ^ 2)
        ≤ ∑ j ∈ Finset.range n,
          4 * (4 * ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s j C‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s j D‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => hper j
    _ = 4 * (4 * (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j C‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j D‖ ^ 2)) := by
      simp only [Finset.mul_sum]
      ring
    _ ≤ 4 * (4 * a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
      gcongr

private theorem jet_add5
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (A B C D F : SmoothCcTensor g r s) (a b c d f : ℝ)
    (hA : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) ≤ a ^ 2)
    (hB : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) ≤ b ^ 2)
    (hC : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j C‖ ^ 2) ≤ c ^ 2)
    (hD : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j D‖ ^ 2) ≤ d ^ 2)
    (hF : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j F‖ ^ 2) ≤ f ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j
        (A + ((((B + C) + D) + F)))‖ ^ 2) ≤
      5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + f ^ 2) := by
  classical
  have hper : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g r s j
        (A + ((((B + C) + D) + F)))‖ ^ 2 ≤
      5 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g r s j C‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g r s j D‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g r s j F‖ ^ 2) := by
    intro j
    rw [iteratedCovGrad_add, iteratedCovGrad_add, iteratedCovGrad_add,
      iteratedCovGrad_add]
    let x : ℝ := ‖iteratedCovGrad (I := I) g r s j A‖
    let y : ℝ := ‖iteratedCovGrad (I := I) g r s j B‖
    let z : ℝ := ‖iteratedCovGrad (I := I) g r s j C‖
    let w : ℝ := ‖iteratedCovGrad (I := I) g r s j D‖
    let u : ℝ := ‖iteratedCovGrad (I := I) g r s j F‖
    have htri :
        ‖iteratedCovGrad (I := I) g r s j A +
          (((iteratedCovGrad (I := I) g r s j B +
            iteratedCovGrad (I := I) g r s j C) +
            iteratedCovGrad (I := I) g r s j D) +
            iteratedCovGrad (I := I) g r s j F)‖ ≤ x + y + z + w + u := by
      calc
        _ ≤ ‖iteratedCovGrad (I := I) g r s j A‖ +
            ‖((iteratedCovGrad (I := I) g r s j B +
              iteratedCovGrad (I := I) g r s j C) +
              iteratedCovGrad (I := I) g r s j D) +
              iteratedCovGrad (I := I) g r s j F‖ := norm_add_le _ _
        _ ≤ ‖iteratedCovGrad (I := I) g r s j A‖ +
            (‖(iteratedCovGrad (I := I) g r s j B +
              iteratedCovGrad (I := I) g r s j C) +
              iteratedCovGrad (I := I) g r s j D‖ +
              ‖iteratedCovGrad (I := I) g r s j F‖) :=
            add_le_add_left (norm_add_le _ _) _
        _ ≤ ‖iteratedCovGrad (I := I) g r s j A‖ +
            ((‖iteratedCovGrad (I := I) g r s j B +
              iteratedCovGrad (I := I) g r s j C‖ +
              ‖iteratedCovGrad (I := I) g r s j D‖) +
              ‖iteratedCovGrad (I := I) g r s j F‖) :=
            add_le_add_left (add_le_add_right (norm_add_le _ _) _) _
        _ ≤ ‖iteratedCovGrad (I := I) g r s j A‖ +
            (((‖iteratedCovGrad (I := I) g r s j B‖ +
              ‖iteratedCovGrad (I := I) g r s j C‖) +
              ‖iteratedCovGrad (I := I) g r s j D‖) +
              ‖iteratedCovGrad (I := I) g r s j F‖) :=
            add_le_add_left
              (add_le_add_right (add_le_add_right (norm_add_le _ _) _) _) _
        _ = x + y + z + w + u := by simp only [x, y, z, w, u]; ring
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hcauchy : (x + y + z + w + u) ^ 2 ≤
        5 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 + u ^ 2) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - w),
        sq_nonneg (x - u), sq_nonneg (y - z), sq_nonneg (y - w),
        sq_nonneg (y - u), sq_nonneg (z - w), sq_nonneg (z - u),
        sq_nonneg (w - u)]
    exact hsq.trans (hcauchy.trans_eq (by simp only [x, y, z, w, u]))
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        5 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j C‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j D‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j F‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => hper j
    _ = 5 * ((∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j C‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j D‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j F‖ ^ 2)) := by
      simp only [Finset.mul_sum]
      ring
    _ ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + f ^ 2) := by
      gcongr

private theorem jet_add2
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (A B : SmoothCcTensor g r s) (a b : ℝ)
    (hA : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) ≤ a ^ 2)
    (hB : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) ≤ b ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j ((-2 : ℝ) • A + B)‖ ^ 2) ≤
      2 * (4 * a ^ 2 + b ^ 2) := by
  classical
  have hper : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g r s j ((-2 : ℝ) • A + B)‖ ^ 2 ≤
        2 * (4 * ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
    intro j
    rw [iteratedCovGrad_add, iteratedCovGrad_smul_real]
    have htri := norm_add_le ((-2 : ℝ) • iteratedCovGrad (I := I) g r s j A)
      (iteratedCovGrad (I := I) g r s j B)
    have htri' : ‖(-2 : ℝ) • iteratedCovGrad (I := I) g r s j A +
        iteratedCovGrad (I := I) g r s j B‖ ≤
        2 * ‖iteratedCovGrad (I := I) g r s j A‖ +
          ‖iteratedCovGrad (I := I) g r s j B‖ := by
      simpa [norm_smul, Real.norm_eq_abs] using htri
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri' 2
    nlinarith [hsquare,
      sq_nonneg (2 * ‖iteratedCovGrad (I := I) g r s j A‖ -
        ‖iteratedCovGrad (I := I) g r s j B‖)]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        2 * (4 * ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => hper j
    _ = 2 * (4 * (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2)) := by
      simp only [Finset.mul_sum]
      ring
    _ ≤ 2 * (4 * a ^ 2 + b ^ 2) := by gcongr

/-- Jet-squared wrapper around the mixed `H1 × H2 → H1` operator estimate. -/
private theorem app_h1h2_j1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
        0 ≤ A → 0 ≤ B →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g p c j
            (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
          (C * A * B) ^ 2 := by
  obtain ⟨C, hC, happ⟩ := appRS_h1_h2_h1 (I := I) (M := M) hDim g p r c
  refine ⟨C, hC, ?_⟩
  intro Φ W A B hA hB hΦ hW
  have hnorm := happ Φ W A B hA hB hΦ hW
  have hsquare := pow_le_pow_left₀
    (norm_nonneg (⟨appCcRS (I := I) (M := M) g p r c Φ W⟩ :
      SmoothCcTensorH1 g p c)) hnorm 2
  rw [h1_jet_sq (I := I) (M := M) g p c
    (appCcRS (I := I) (M := M) g p r c Φ W)] at hsquare
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare

/-- Jet-squared wrapper around the complementary `H2 × H1 → H1` estimate. -/
private theorem app_h2h1_j1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
        0 ≤ A → 0 ≤ B →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g p c j
            (appCcRS (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
          (C * A * B) ^ 2 := by
  obtain ⟨C, hC, happ⟩ := appRS_h2_h1_h1 (I := I) (M := M) hDim g p r c
  refine ⟨C, hC, ?_⟩
  intro Φ W A B hA hB hΦ hW
  have hnorm := happ Φ W A B hA hB hΦ hW
  have hsquare := pow_le_pow_left₀
    (norm_nonneg (⟨appCcRS (I := I) (M := M) g p r c Φ W⟩ :
      SmoothCcTensorH1 g p c)) hnorm 2
  rw [h1_jet_sq (I := I) (M := M) g p c
    (appCcRS (I := I) (M := M) g p r c Φ W)] at hsquare
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare

/-- The spectral `H3` norm controls the four-term squared intrinsic jet of
every point of a convex metric segment, with the same endpoint bound. -/
theorem convex_h3_jet (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2) (R : ℝ), 0 ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ ≤ R →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤
            (C * R) ^ 2 := by
  classical
  obtain ⟨C, hC, hjet⟩ := hsJet_le (I := I) (M := M) g₀ 2 3
  refine ⟨C, hC, ?_⟩
  intro T T' R hR hT hT' s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hpath :
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ)
          (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    rw [show convexPerturbation (I := I) g₀ T T' s =
        (1 - s) • T' + s • T from rfl,
      ccTensorToHs_add, ccTensorToHs_smul, ccTensorToHs_smul]
    calc
      ‖(1 - s) • ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T' +
          s • ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖
          ≤ ‖(1 - s) • ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ +
            ‖s • ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ :=
            norm_add_le _ _
      _ = (1 - s) * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ +
            s * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
        add_le_add (mul_le_mul_of_nonneg_left hT' h1ms)
          (mul_le_mul_of_nonneg_left hT hs0)
      _ = R := by ring
  have hsum : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j
        (convexPerturbation (I := I) g₀ T T' s)‖) ≤ C * R := by
    exact (hjet (convexPerturbation (I := I) g₀ T T' s)).trans
      (mul_le_mul_of_nonneg_left hpath hC)
  exact (Finset.sum_sq_le_sq_sum_of_nonneg
    (fun j _ => norm_nonneg
      (iteratedCovGrad (I := I) g₀ 0 2 j
        (convexPerturbation (I := I) g₀ T T' s)))).trans
    (pow_le_pow_left₀
      (Finset.sum_nonneg fun j _ => norm_nonneg
        (iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)))
      hsum 2)

/-- Intrinsic antidiagonal product grid of the metric-perturbation jet. -/
def lowJetGrid (g : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g 0 2) (k : ℕ) (x : M) : ℝ :=
  ∑ n ∈ Finset.range (k + 1),
    ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
      ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)

theorem grid_h1_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (P : SmoothCcTensor g 0 2)
    (K C : ℕ → ℝ)
    (hK : ∀ k, 0 ≤ K k)
    (hgrid : ∀ k : ℕ, k ≤ 3 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K k)
    (hC : ∀ i, 0 ≤ C i)
    (Φ : SmoothCcTensor g r s)
    (hΦ : ∀ (i : ℕ), i < 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
          ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
        C i * ∑ k ∈ Finset.range (i + 3),
          lowJetGrid (I := I) (M := M) g P k x) :
    (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤
      ∑ i ∈ Finset.range 2,
        C i * ∑ k ∈ Finset.range (i + 3), K k := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  have hi2 : i < 2 := Finset.mem_range.mp hi
  have hsumInt : MeasureTheory.Integrable
      (fun x => ∑ k ∈ Finset.range (i + 3),
        lowJetGrid (I := I) (M := M) g P k x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply MeasureTheory.integrable_finset_sum
    intro k hk
    exact (hgrid k (by have := Finset.mem_range.mp hk; omega)).1
  have hscaled : MeasureTheory.Integrable
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        lowJetGrid (I := I) (M := M) g P k x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hsumInt.const_mul (C i)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g r (s + i)
    (iteratedCovGrad (I := I) g r s i Φ)
    (fun x => C i * ∑ k ∈ Finset.range (i + 3),
      lowJetGrid (I := I) (M := M) g P k x)
    hscaled (hΦ i hi2)
  refine hnorm.trans ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (hC i)
  rw [MeasureTheory.integral_finset_sum _
    (fun k hk => (hgrid k (by have := Finset.mem_range.mp hk; omega)).1)]
  exact Finset.sum_le_sum fun k hk =>
    (hgrid k (by have := Finset.mem_range.mp hk; omega)).2

/-- In dimension three, a pointwise coefficient-jet bound by the metric
product grid through total order three integrates to a uniform `H1` bound.
This is the common final step for all concrete order-zero coefficient pieces. -/
theorem h1_of_grid
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (C : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (P : SmoothCcTensor g 0 2) (Φ : SmoothCcTensor g r s)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∀ (i : ℕ), i < 2 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
              ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
            C i * ∑ k ∈ Finset.range (i + 3),
              lowJetGrid (I := I) (M := M) g P k x) →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤ (B A) ^ 2 := by
  classical
  obtain ⟨K, hK, hgrid⟩ := h3_grid_int (I := I) (M := M) hDim g
  let Q : ℝ → ℝ := fun A => ∑ i ∈ Finset.range 2,
    C i * ∑ k ∈ Finset.range (i + 3), K A k
  let B : ℝ → ℝ := fun A => Real.sqrt (Q A)
  have hQ : ∀ A : ℝ, 0 ≤ A → 0 ≤ Q A := by
    intro A hA
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hC i)
      (Finset.sum_nonneg fun k _ => hK A hA k)
  refine ⟨B, fun A _ => Real.sqrt_nonneg _, ?_⟩
  intro P Φ A hA hP hΦ
  have hgr : ∀ k : ℕ, k ≤ 3 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K A k := by
    intro k hk
    simpa only [lowJetGrid] using hgrid P A hA hP k hk
  have hle := grid_h1_le (I := I) (M := M) g P (K A) C
    (hK A hA) hgr hC Φ hΦ
  change _ ≤ (B A) ^ 2
  rw [show (B A) ^ 2 = Q A by
    simp only [B, Real.sq_sqrt (hQ A hA)]]
  exact hle

/-- Integrate an `H2` coefficient jet whose order-`i` pointwise bound uses
only the sharp metric grid window through total order `i`.  This is the tame
variant for moving traces: when `i < 3`, only metric grids through order two
occur, hence the metric `H2` jet suffices. -/
theorem grid_h2_low
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (P : SmoothCcTensor g 0 2)
    (K C : ℕ → ℝ)
    (hK : ∀ k, 0 ≤ K k)
    (hgrid : ∀ k : ℕ, k ≤ 2 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K k)
    (hC : ∀ i, 0 ≤ C i)
    (Φ : SmoothCcTensor g r s)
    (hΦ : ∀ (i : ℕ), i < 3 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
          ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
        C i * ∑ k ∈ Finset.range (i + 1),
          lowJetGrid (I := I) (M := M) g P k x) :
    (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤
      ∑ i ∈ Finset.range 3,
        C i * ∑ k ∈ Finset.range (i + 1), K k := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  have hi3 : i < 3 := Finset.mem_range.mp hi
  have hsumInt : MeasureTheory.Integrable
      (fun x => ∑ k ∈ Finset.range (i + 1),
        lowJetGrid (I := I) (M := M) g P k x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply MeasureTheory.integrable_finset_sum
    intro k hk
    exact (hgrid k (by have := Finset.mem_range.mp hk; omega)).1
  have hscaled : MeasureTheory.Integrable
      (fun x => C i * ∑ k ∈ Finset.range (i + 1),
        lowJetGrid (I := I) (M := M) g P k x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hsumInt.const_mul (C i)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g r (s + i)
    (iteratedCovGrad (I := I) g r s i Φ)
    (fun x => C i * ∑ k ∈ Finset.range (i + 1),
      lowJetGrid (I := I) (M := M) g P k x)
    hscaled (hΦ i hi3)
  refine hnorm.trans ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (hC i)
  rw [MeasureTheory.integral_finset_sum _
    (fun k hk => (hgrid k (by have := Finset.mem_range.mp hk; omega)).1)]
  exact Finset.sum_le_sum fun k hk =>
    (hgrid k (by have := Finset.mem_range.mp hk; omega)).2

/-- In dimension three, the sharp trace grid window integrates to an `H2`
bound depending only on the metric `H2` jet. -/
theorem h2_of_grid_low
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (C : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (P : SmoothCcTensor g 0 2) (Φ : SmoothCcTensor g r s)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∀ (i : ℕ), i < 3 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
              ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
            C i * ∑ k ∈ Finset.range (i + 1),
              lowJetGrid (I := I) (M := M) g P k x) →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤ (B A) ^ 2 := by
  classical
  obtain ⟨K, hK, hgrid⟩ := h2_grid_int (I := I) (M := M) hDim g
  let Q : ℝ → ℝ := fun A => ∑ i ∈ Finset.range 3,
    C i * ∑ k ∈ Finset.range (i + 1), K A k
  let B : ℝ → ℝ := fun A => Real.sqrt (Q A)
  have hQ : ∀ A : ℝ, 0 ≤ A → 0 ≤ Q A := by
    intro A hA
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hC i)
      (Finset.sum_nonneg fun k _ => hK A hA k)
  refine ⟨B, fun A _ => Real.sqrt_nonneg _, ?_⟩
  intro P Φ A hA hP hΦ
  have hgr : ∀ k : ℕ, k ≤ 2 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K A k := by
    intro k hk
    simpa only [lowJetGrid] using hgrid P A hA hP k hk
  have hle := grid_h2_low (I := I) (M := M) g P (K A) C
    (hK A hA) hgr hC Φ hΦ
  change _ ≤ (B A) ^ 2
  rw [show (B A) ^ 2 = Q A by
    simp only [B, Real.sq_sqrt (hQ A hA)]]
  exact hle

/-- Integrate a pointwise coefficient grid through two covariant derivatives.

The `i + 2` window is the sharp one needed for a connection-difference
coefficient: its zeroth-order term already contains one derivative of the
metric.  When `i < 3`, every requested product grid has total order at most
three, exactly the range supplied by `h3_grid_int`. -/
theorem grid_h2_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (P : SmoothCcTensor g 0 2)
    (K C : ℕ → ℝ)
    (hK : ∀ k, 0 ≤ K k)
    (hgrid : ∀ k : ℕ, k ≤ 3 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K k)
    (hC : ∀ i, 0 ≤ C i)
    (Φ : SmoothCcTensor g r s)
    (hΦ : ∀ (i : ℕ), i < 3 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
          ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
        C i * ∑ k ∈ Finset.range (i + 2),
          lowJetGrid (I := I) (M := M) g P k x) :
    (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤
      ∑ i ∈ Finset.range 3,
        C i * ∑ k ∈ Finset.range (i + 2), K k := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  have hi3 : i < 3 := Finset.mem_range.mp hi
  have hsumInt : MeasureTheory.Integrable
      (fun x => ∑ k ∈ Finset.range (i + 2),
        lowJetGrid (I := I) (M := M) g P k x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply MeasureTheory.integrable_finset_sum
    intro k hk
    exact (hgrid k (by have := Finset.mem_range.mp hk; omega)).1
  have hscaled : MeasureTheory.Integrable
      (fun x => C i * ∑ k ∈ Finset.range (i + 2),
        lowJetGrid (I := I) (M := M) g P k x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hsumInt.const_mul (C i)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g r (s + i)
    (iteratedCovGrad (I := I) g r s i Φ)
    (fun x => C i * ∑ k ∈ Finset.range (i + 2),
      lowJetGrid (I := I) (M := M) g P k x)
    hscaled (hΦ i hi3)
  refine hnorm.trans ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (hC i)
  rw [MeasureTheory.integral_finset_sum _
    (fun k hk => (hgrid k (by have := Finset.mem_range.mp hk; omega)).1)]
  exact Finset.sum_le_sum fun k hk =>
    (hgrid k (by have := Finset.mem_range.mp hk; omega)).2

/-- In dimension three, a pointwise grid bound with the connection-difference
window `i + 2` gives a uniform intrinsic `H2` bound. -/
theorem h2_of_grid
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (C : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (P : SmoothCcTensor g 0 2) (Φ : SmoothCcTensor g r s)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∀ (i : ℕ), i < 3 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
              ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
            C i * ∑ k ∈ Finset.range (i + 2),
              lowJetGrid (I := I) (M := M) g P k x) →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤ (B A) ^ 2 := by
  classical
  obtain ⟨K, hK, hgrid⟩ := h3_grid_int (I := I) (M := M) hDim g
  let Q : ℝ → ℝ := fun A => ∑ i ∈ Finset.range 3,
    C i * ∑ k ∈ Finset.range (i + 2), K A k
  let B : ℝ → ℝ := fun A => Real.sqrt (Q A)
  have hQ : ∀ A : ℝ, 0 ≤ A → 0 ≤ Q A := by
    intro A hA
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hC i)
      (Finset.sum_nonneg fun k _ => hK A hA k)
  refine ⟨B, fun A _ => Real.sqrt_nonneg _, ?_⟩
  intro P Φ A hA hP hΦ
  have hgr : ∀ k : ℕ, k ≤ 3 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K A k := by
    intro k hk
    simpa only [lowJetGrid] using hgrid P A hA hP k hk
  have hle := grid_h2_le (I := I) (M := M) g P (K A) C
    (hK A hA) hgr hC Φ hΦ
  change _ ≤ (B A) ^ 2
  rw [show (B A) ^ 2 = Q A by
    simp only [B, Real.sq_sqrt (hQ A hA)]]
  exact hle

/-- Tame form of `h2_of_grid`: the grids through total order two depend only
on the lower `H2` radius `R`, while the total-order-three grid is linear in
the top derivative bound `A`.  The square-root subadditivity is packaged in
the conclusion, so downstream product estimates see the affine bound
`B0 R + B1 R * A` directly. -/
theorem h2_grid_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (C : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (P : SmoothCcTensor g 0 2) (Φ : SmoothCcTensor g r s)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g 0 2 3 P‖ ≤ A →
        (∀ (i : ℕ), i < 3 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
              ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
            C i * ∑ k ∈ Finset.range (i + 2),
              lowJetGrid (I := I) (M := M) g P k x) →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨K0, hK0, hgrid0⟩ := h2_grid_int (I := I) (M := M) hDim g
  obtain ⟨K3, hK3, hgrid3⟩ := h3_top_grid_int (I := I) (M := M) hDim g
  let L : ℝ → ℕ → ℝ := fun R i =>
    ∑ k ∈ Finset.range (i + 2), if k = 3 then 0 else K0 R k
  let T : ℝ → ℕ → ℝ := fun R i =>
    ∑ k ∈ Finset.range (i + 2), if k = 3 then K3 R else 0
  let Q0 : ℝ → ℝ := fun R =>
    ∑ i ∈ Finset.range 3, C i * L R i
  let Q1 : ℝ → ℝ := fun R =>
    ∑ i ∈ Finset.range 3, C i * T R i
  let B0 : ℝ → ℝ := fun R => Real.sqrt (Q0 R)
  let B1 : ℝ → ℝ := fun R => Real.sqrt (Q1 R)
  have hL : ∀ R : ℝ, 0 ≤ R → ∀ i, 0 ≤ L R i := by
    intro R hR i
    exact Finset.sum_nonneg fun k _ => by
      by_cases hk : k = 3
      · simp only [hk, if_pos]
      · simp only [if_neg hk]
        exact hK0 R hR k
  have hT : ∀ R : ℝ, 0 ≤ R → ∀ i, 0 ≤ T R i := by
    intro R hR i
    exact Finset.sum_nonneg fun k _ => by
      by_cases hk : k = 3
      · simp only [hk, if_pos]
        exact hK3 R hR
      · simp only [if_neg hk]
  have hQ0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q0 R := by
    intro R hR
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hC i) (hL R hR i)
  have hQ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q1 R := by
    intro R hR
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hC i) (hT R hR i)
  refine ⟨B0, B1, fun R _ => Real.sqrt_nonneg _,
    fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro P Φ R A hR hA hP2 htop hΦ
  let Km : ℕ → ℝ := fun k => if k = 3 then K3 R * A ^ 2 else K0 R k
  have hKm : ∀ k, 0 ≤ Km k := by
    intro k
    by_cases hk : k = 3
    · simp only [Km, hk, if_pos]
      exact mul_nonneg (hK3 R hR) (sq_nonneg A)
    · simp only [Km, if_neg hk]
      exact hK0 R hR k
  have hgr : ∀ k : ℕ, k ≤ 3 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ Km k := by
    intro k hk
    by_cases hk3 : k = 3
    · subst k
      simpa only [lowJetGrid, Km, if_pos, Nat.reduceAdd] using
        hgrid3 P R A hR hA hP2 htop
    · have hk2 : k ≤ 2 := by omega
      simpa only [lowJetGrid, Km, if_neg hk3] using
        hgrid0 P R hR hP2 k hk2
  have hle := grid_h2_le (I := I) (M := M) g P Km C
    hKm hgr hC Φ hΦ
  have hsplit : ∀ i : ℕ,
      (∑ k ∈ Finset.range (i + 2), Km k) = L R i + T R i * A ^ 2 := by
    intro i
    simp only [L, T]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = 3
    · simp only [Km, hk, if_pos]
      ring
    · simp only [Km, if_neg hk]
      ring
  have hQeq :
      (∑ i ∈ Finset.range 3,
        C i * ∑ k ∈ Finset.range (i + 2), Km k) =
        Q0 R + Q1 R * A ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range 3,
          (C i * L R i + (C i * T R i) * A ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hsplit i]
            ring
      _ = (∑ i ∈ Finset.range 3, C i * L R i) +
          ∑ i ∈ Finset.range 3, (C i * T R i) * A ^ 2 := by
            rw [Finset.sum_add_distrib]
      _ = Q0 R + Q1 R * A ^ 2 := by
            simp only [Q0, Q1, Finset.sum_mul]
  rw [hQeq] at hle
  calc
    _ ≤ Q0 R + Q1 R * A ^ 2 := hle
    _ = (B0 R) ^ 2 + (B1 R * A) ^ 2 := by
      simp only [B0, B1, mul_pow, Real.sq_sqrt (hQ0 R hR),
        Real.sq_sqrt (hQ1 R hR)]
    _ ≤ (B0 R + B1 R * A) ^ 2 := by
      nlinarith [mul_nonneg (Real.sqrt_nonneg (Q0 R))
        (mul_nonneg (Real.sqrt_nonneg (Q1 R)) hA)]

/-- Covariant derivatives of an iterated slot extension cost only the expected
finite-dimensional factor.  The added identity slots are parallel, so no
derivative is lost. -/
theorem slotIter_rfns
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ (w : ℕ) (Φ : SmoothCcTensor g r s) (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g (r + w) ((s + w) + i) x
          ((iteratedCovGrad (I := I) g (r + w) (s + w) i
            (slotExtendIter (I := I) (M := M) g r s w Φ)).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ w *
          riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
            ((iteratedCovGrad (I := I) g r s i Φ).toSection x) := by
  intro w
  induction w with
  | zero =>
      intro Φ i x
      simp only [slotExtendIter, Nat.add_zero, pow_zero, one_mul]
  | succ w ih =>
      intro Φ i x
      change riemannianFiberNormSq (I := I) (M := M) g
          ((r + w) + 1) (((s + w) + 1) + i) x
          ((iteratedCovGrad (I := I) g ((r + w) + 1) ((s + w) + 1) i
            (slotExtend (I := I) (M := M) g (r + w) (s + w)
              (slotExtendIter (I := I) (M := M) g r s w Φ))).toSection x) ≤ _
      calc
        _ ≤ (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g (r + w) ((s + w) + i) x
              ((iteratedCovGrad (I := I) g (r + w) (s + w) i
                (slotExtendIter (I := I) (M := M) g r s w Φ)).toSection x) :=
          rfns_iteratedCovGrad_slotExtend_le
            (I := I) (M := M) g (r + w) (s + w)
              (slotExtendIter (I := I) (M := M) g r s w Φ) i x
        _ ≤ (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) ^ w *
              riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
                ((iteratedCovGrad (I := I) g r s i Φ).toSection x)) :=
          mul_le_mul_of_nonneg_left (ih Φ i x) (Nat.cast_nonneg _)
        _ = (Module.finrank ℝ E : ℝ) ^ (w + 1) *
              riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
                ((iteratedCovGrad (I := I) g r s i Φ).toSection x) := by
          rw [pow_succ]
          ring

/-- Integrated version of `slotIter_rfns`. -/
theorem slotIter_l2
    (g : SmoothRiemannianMetric I M) (r s w i : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g (r + w) (s + w) i
        (slotExtendIter (I := I) (M := M) g r s w Φ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ w *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) ^ w *
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
      ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i Φ)).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + w) ((s + w) + i)
    (iteratedCovGrad (I := I) g (r + w) (s + w) i
      (slotExtendIter (I := I) (M := M) g r s w Φ))
    F hF (fun x => slotIter_rfns (I := I) (M := M) g r s w Φ i x)
  have hint : (∫ x,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

/-- The complete `H2` jet of an iterated slot extension has the same
finite-dimensional loss and no Sobolev-order loss. -/
theorem slotIter_h2
    (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (Φ : SmoothCcTensor g r s) :
    (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g (r + w) (s + w) i
        (slotExtendIter (I := I) (M := M) g r s w Φ)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ w *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
  calc
    _ ≤ ∑ i ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) ^ w *
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => slotIter_l2 (I := I) (M := M) g r s w i Φ
    _ = _ := by rw [Finset.mul_sum]

/-- The analogous range-two (`H1`) slot-extension estimate. -/
theorem slotIter_h1
    (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (Φ : SmoothCcTensor g r s) :
    (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g (r + w) (s + w) i
        (slotExtendIter (I := I) (M := M) g r s w Φ)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ w *
        ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
  calc
    _ ≤ ∑ i ∈ Finset.range 2, (Module.finrank ℝ E : ℝ) ^ w *
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => slotIter_l2 (I := I) (M := M) g r s w i Φ
    _ = _ := by rw [Finset.mul_sum]

/-- Scalar-bound form of `slotIter_h2`. -/
theorem slotIter_h2b
    (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (Φ : SmoothCcTensor g r s) (A : ℝ)
    (hΦ : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤ A ^ 2) :
    (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g (r + w) (s + w) i
        (slotExtendIter (I := I) (M := M) g r s w Φ)‖ ^ 2) ≤
      (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ w) * A) ^ 2 := by
  have hf : 0 ≤ (Module.finrank ℝ E : ℝ) ^ w :=
    pow_nonneg (Nat.cast_nonneg _) _
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) ^ w *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 :=
      slotIter_h2 (I := I) (M := M) g r s w Φ
    _ ≤ (Module.finrank ℝ E : ℝ) ^ w * A ^ 2 :=
      mul_le_mul_of_nonneg_left hΦ hf
    _ = (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ w) * A) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hf]

/-- Scalar-bound form of `slotIter_h1`. -/
theorem slotIter_h1b
    (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (Φ : SmoothCcTensor g r s) (A : ℝ)
    (hΦ : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤ A ^ 2) :
    (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g (r + w) (s + w) i
        (slotExtendIter (I := I) (M := M) g r s w Φ)‖ ^ 2) ≤
      (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ w) * A) ^ 2 := by
  have hf : 0 ≤ (Module.finrank ℝ E : ℝ) ^ w :=
    pow_nonneg (Nat.cast_nonneg _) _
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) ^ w *
        ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 :=
      slotIter_h1 (I := I) (M := M) g r s w Φ
    _ ≤ (Module.finrank ℝ E : ℝ) ^ w * A ^ 2 :=
      mul_le_mul_of_nonneg_left hΦ hf
    _ = (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ w) * A) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hf]

/-- A moving double trace of arbitrary passenger rank has an intrinsic `H2`
bound from only the metric `H2` jet.  This is the reusable low factor for all
three nested traces in the `VB` and `AMix` normal forms. -/
theorem trace_h2
    (p : ℕ) (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin (p + 2))) (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ (p + 2) p i
            (lc0Trace (I := I) (M := M) g₀ g₁ p σ)‖ ^ 2) ≤ (B A) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ := trace_grid (I := I) (M := M) p g₀ hδ₀
  obtain ⟨B, hB_nn, hB⟩ := h2_of_grid_low (I := I) (M := M)
    (r := p + 2) (s := p) hDim g₀ C hC
  refine ⟨B, hB_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound σ A hA hP
  refine hB P (lc0Trace (I := I) (M := M) g₀ g₁ p σ) A hA hP ?_
  intro i hi x
  simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGrid] using
    hpt g₁ P htie hδ_le hδ_nonneg hbound σ i x

/-- Rank-two specialization of `trace_h2`. -/
theorem trace2_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin 4)) (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (lc0Trace (I := I) (M := M) g₀ g₁ 2 σ)‖ ^ 2) ≤ (B A) ^ 2 := by
  simpa only [Nat.reduceAdd] using trace_h2 (I := I) (M := M) 2 hDim g₀ hδ₀

/-- The metric-lowered connection difference has an intrinsic `H2` bound
from the perturbation `H3` jet. -/
theorem connLow_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2) ≤ (B A) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨B, hB_nn, hB⟩ := h2_of_grid (I := I) (M := M)
    (r := 0) (s := 3) hDim g₀ C hC
  refine ⟨B, hB_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound A hA hP
  refine hB P (connDiffLoweredCc (I := I) g₀ g₁) A hA hP ?_
  intro i hi x
  rw [connLow_rfns (I := I) (M := M) g₀ g₁ i x]
  simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGrid] using
    hpt g₁ P htie hδ_le hδ_nonneg hbound i x

/-- Tame `H2` bound for the lowered connection difference.  The lower
coefficient depends only on the perturbation `H2` radius, while the third
metric derivative enters through one affine top-order arm. -/
theorem connLow_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨B0, B1, hB0, hB1, hB⟩ := h2_grid_tame (I := I) (M := M)
    (r := 0) (s := 3) hDim g₀ C hC
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 hP3
  have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ^ 2 ≤ A ^ 2 := by
    have hmem : 3 ∈ Finset.range 4 := by norm_num
    exact (Finset.single_le_sum
      (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
      (fun j _ => sq_nonneg _) hmem).trans hP3
  have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ A := by
    nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 3 P)]
  refine hB P (connDiffLoweredCc (I := I) g₀ g₁) R A hR hA hP2 htop ?_
  intro i hi x
  rw [connLow_rfns (I := I) (M := M) g₀ g₁ i x]
  simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGrid] using
    hpt g₁ P htie hδ_le hδ_nonneg hbound i x

/-- On the self-background arm, the lowered connection difference has an
`H1` jet controlled only by the metric `H2` jet.  This is the low factor in
the tame `VB` and `AMix` product allocations. -/
theorem kappaSelf_h1
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w)
    (R : ℝ) (hR : 0 ≤ R)
    (hP : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2) :
    (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤ (4 * R) ^ 2 := by
  classical
  rw [kappa_self (I := I) (M := M) g₀ g₁ P htie]
  have hterm : ∀ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (domDomCongrSection (I := I) g₀ (finRotate 3).symm
          (koszulCovecCc (I := I) g₀ P))‖ ^ 2 ≤
        10 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P‖ ^ 2 := by
    intro i hi
    have hperm :
        ‖iteratedCovGrad (I := I) g₀ 0 3 i
          (domDomCongrSection (I := I) g₀ (finRotate 3).symm
            (koszulCovecCc (I := I) g₀ P))‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (koszulCovecCc (I := I) g₀ P)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x =>
        riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
          (I := I) (M := M) g₀ (finRotate 3).symm
          (koszulCovecCc (I := I) g₀ P) i x)
    rw [hperm]
    exact koszul_l2_succ (I := I) (M := M) g₀ P i
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum hP ⊢
  nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 0 P‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 1 P‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 2 P‖]

/-- On the self-background arm, the lowered connection difference is bounded
in `H2` directly by the perturbation `H3` jet.  No inverse-metric estimate is
used: `kappa_self` first performs the exact Koszul cancellation. -/
theorem kappaSelf_h2
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w)
    (A : ℝ) (hA : 0 ≤ A)
    (hP : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2) :
    (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤ (4 * A) ^ 2 := by
  classical
  rw [kappa_self (I := I) (M := M) g₀ g₁ P htie]
  have hterm : ∀ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (domDomCongrSection (I := I) g₀ (finRotate 3).symm
          (koszulCovecCc (I := I) g₀ P))‖ ^ 2 ≤
        10 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P‖ ^ 2 := by
    intro i hi
    have hperm :
        ‖iteratedCovGrad (I := I) g₀ 0 3 i
          (domDomCongrSection (I := I) g₀ (finRotate 3).symm
            (koszulCovecCc (I := I) g₀ P))‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (koszulCovecCc (I := I) g₀ P)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x =>
        riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
          (I := I) (M := M) g₀ (finRotate 3).symm
          (koszulCovecCc (I := I) g₀ P) i x)
    rw [hperm]
    exact koszul_l2_succ (I := I) (M := M) g₀ P i
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum hP ⊢
  nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 0 P‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 1 P‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 2 P‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖]

/-- The perturbation pairing with a fixed background connection difference is
`H2`-controlled by the perturbation `H2` jet. -/
theorem pbLow_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2) (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2) ≤ (B A) ^ 2 := by
  classical
  obtain ⟨C, hC, hprod⟩ := appRS_h2_h2_h2
    (I := I) (M := M) hDim g₀ 1 1 2
  let SF : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 1 2 j
      (connDiffSection (I := I) g₀ gB)‖ ^ 2
  have hSF : 0 ≤ SF := Finset.sum_nonneg fun j _ => sq_nonneg _
  let AF : ℝ := Real.sqrt SF
  have hAF : 0 ≤ AF := Real.sqrt_nonneg _
  have hAFsq : SF = AF ^ 2 := by
    simp only [AF, Real.sq_sqrt hSF]
  let B : ℝ → ℝ := fun A => C * AF * A
  refine ⟨B, fun A hA => mul_nonneg (mul_nonneg hC hAF) hA, ?_⟩
  intro P A hA hP
  let W : SmoothCcTensor g₀ 1 1 :=
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
      (symmS (I := I) (M := M) g₀ P)
  have hWterm : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 1 1 j W‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
    intro j hj
    have hraise :
        ‖iteratedCovGrad (I := I) g₀ 1 1 j W‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
            (symmS (I := I) (M := M) g₀ P)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simpa only [W] using
          (rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P) j x))
    rw [hraise]
    have hs := norm_iteratedCovGrad_symmS_le
      (I := I) (M := M) g₀ P j
    nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j
      (symmS (I := I) (M := M) g₀ P)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P)]
  have hW : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 1 1 j W‖ ^ 2) ≤ A ^ 2 := by
    exact (Finset.sum_le_sum hWterm).trans hP
  have hout := hprod (connDiffSection (I := I) g₀ gB) W AF A
    hAF hA (by simpa only [SF, hAFsq]) hW
  have heq : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2) =
      ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 1 2 i
          (appCcRS (I := I) (M := M) g₀ 1 1 2
            (connDiffSection (I := I) g₀ gB) W)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simpa only [W] using pbLow_rfns (I := I) (M := M) g₀ gB P i x)
  rw [heq]
  simpa only [B] using hout

/-- The full moving-metric lowered connection difference relative to a fixed
background has an `H1` jet controlled solely by the low metric `H2` size. -/
theorem kappaBg_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        (R : ℝ), 0 ≤ R →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2) ≤ (B R) ^ 2 := by
  classical
  obtain ⟨BP, hBP_nn, hBP⟩ := pbLow_h2 (I := I) (M := M) hDim g₀ gB
  let SF : ℝ := ∑ i ∈ Finset.range 2,
    ‖iteratedCovGrad (I := I) g₀ 0 3 i
      (connDiffLoweredCc (I := I) g₀ gB)‖ ^ 2
  have hSF : 0 ≤ SF := Finset.sum_nonneg fun i _ => sq_nonneg _
  let Q : ℝ → ℝ := fun R => 3 * (16 * R ^ 2 + SF + (BP R) ^ 2)
  have hQ : ∀ R : ℝ, 0 ≤ Q R := by
    intro R
    exact mul_nonneg (by norm_num) (add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg R)) hSF)
      (sq_nonneg (BP R)))
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  refine ⟨B, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P htie R hR hP
  have hself := kappaSelf_h1 (I := I) (M := M) g₀ g₁ P htie R hR hP
  have hpb3 := hBP P R hR hP
  have hpb : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2) ≤ (BP R) ^ 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      (fun i _ _ => sq_nonneg _)).trans hpb3
  have hterm : ∀ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤
        3 * (‖iteratedCovGrad (I := I) g₀ 0 3 i
              (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
              (connDiffLoweredCc (I := I) g₀ gB)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
              (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2) := by
    intro i hi
    rw [kappa_bg (I := I) (M := M) g₀ g₁ gB P htie,
      iteratedCovGrad_add, iteratedCovGrad_sub]
    let X := iteratedCovGrad (I := I) g₀ 0 3 i
      (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)
    let Y := iteratedCovGrad (I := I) g₀ 0 3 i
      (connDiffLoweredCc (I := I) g₀ gB)
    let Z := iteratedCovGrad (I := I) g₀ 0 3 i
      (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)
    have htri : ‖X - Y + Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ :=
      (norm_add_le (X - Y) Z).trans (add_le_add_right (norm_sub_le X Y) ‖Z‖)
    nlinarith [norm_nonneg X, norm_nonneg Y, norm_nonneg Z,
      norm_nonneg (X - Y + Z), sq_nonneg (‖X‖ - ‖Y‖),
      sq_nonneg (‖X‖ - ‖Z‖), sq_nonneg (‖Y‖ - ‖Z‖)]
  have hsum := Finset.sum_le_sum hterm
  have hfactor :
      (∑ i ∈ Finset.range 2,
        3 * (‖iteratedCovGrad (I := I) g₀ 0 3 i
              (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
              (connDiffLoweredCc (I := I) g₀ gB)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
              (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2)) =
        3 * ((∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) + SF +
          (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2)) := by
    simp only [mul_add, Finset.sum_add_distrib, SF]
    ring
  rw [hfactor] at hsum
  have hagg : 3 * ((∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) + SF +
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2)) ≤ Q R := by
    dsimp only [Q]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    nlinarith
  refine hsum.trans (hagg.trans ?_)
  change Q R ≤ (B R) ^ 2
  rw [show (B R) ^ 2 = Q R by simp only [B, Real.sq_sqrt (hQ R)]]

/-- Tame `H2` control of the full moving-metric lowered connection difference.
The self-background Koszul arm uses the top metric `H3` size `A`, while the
fixed-background pairing uses only the low metric `H2` size `R`. -/
theorem kappaBg_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ B R A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2) ≤ (B R A) ^ 2 := by
  classical
  obtain ⟨BP, hBP_nn, hBP⟩ := pbLow_h2 (I := I) (M := M) hDim g₀ gB
  let SF : ℝ := ∑ i ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 3 i
      (connDiffLoweredCc (I := I) g₀ gB)‖ ^ 2
  have hSF : 0 ≤ SF := Finset.sum_nonneg fun i _ => sq_nonneg _
  let Q : ℝ → ℝ → ℝ := fun R A => 3 * (16 * A ^ 2 + SF + (BP R) ^ 2)
  have hQ : ∀ R A : ℝ, 0 ≤ Q R A := by
    intro R A
    exact mul_nonneg (by norm_num) (add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg A)) hSF)
      (sq_nonneg (BP R)))
  let B : ℝ → ℝ → ℝ := fun R A => Real.sqrt (Q R A)
  refine ⟨B, fun R hR A hA => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P htie R A hR hA hP2 hP3
  have hself := kappaSelf_h2 (I := I) (M := M) g₀ g₁ P htie A hA hP3
  have hpb := hBP P R hR hP2
  have hterm : ∀ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤
        3 * (‖iteratedCovGrad (I := I) g₀ 0 3 i
              (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
              (connDiffLoweredCc (I := I) g₀ gB)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
              (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2) := by
    intro i hi
    rw [kappa_bg (I := I) (M := M) g₀ g₁ gB P htie,
      iteratedCovGrad_add, iteratedCovGrad_sub]
    let X := iteratedCovGrad (I := I) g₀ 0 3 i
      (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)
    let Y := iteratedCovGrad (I := I) g₀ 0 3 i
      (connDiffLoweredCc (I := I) g₀ gB)
    let Z := iteratedCovGrad (I := I) g₀ 0 3 i
      (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)
    have htri : ‖X - Y + Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ :=
      (norm_add_le (X - Y) Z).trans (add_le_add_right (norm_sub_le X Y) ‖Z‖)
    nlinarith [norm_nonneg X, norm_nonneg Y, norm_nonneg Z,
      norm_nonneg (X - Y + Z), sq_nonneg (‖X‖ - ‖Y‖),
      sq_nonneg (‖X‖ - ‖Z‖), sq_nonneg (‖Y‖ - ‖Z‖)]
  have hsum := Finset.sum_le_sum hterm
  have hfactor :
      (∑ i ∈ Finset.range 3,
        3 * (‖iteratedCovGrad (I := I) g₀ 0 3 i
              (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
              (connDiffLoweredCc (I := I) g₀ gB)‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
              (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2)) =
        3 * ((∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) + SF +
          (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2)) := by
    simp only [mul_add, Finset.sum_add_distrib, SF]
    ring
  rw [hfactor] at hsum
  have hagg : 3 * ((∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) + SF +
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2)) ≤ Q R A := by
    dsimp only [Q]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    nlinarith
  refine hsum.trans (hagg.trans ?_)
  change Q R A ≤ (B R A) ^ 2
  rw [show (B R A) ^ 2 = Q R A by simp only [B, Real.sq_sqrt (hQ R A)]]

/-- One-parameter wrapper around `kappaBg_tame` for callers that already use
a single `H3` jet size. -/
theorem kappaBg_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2) ≤ (B A) ^ 2 := by
  obtain ⟨Bt, hBt_nn, hBt⟩ := kappaBg_tame (I := I) (M := M) hDim g₀ gB
  let B : ℝ → ℝ := fun A => Bt A A
  refine ⟨B, fun A hA => hBt_nn A hA A hA, ?_⟩
  intro g₁ P htie A hA hP
  have hP2 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      (fun j _ _ => sq_nonneg _)).trans hP
  simpa only [B] using hBt g₁ P htie A A hA hA hP2 hP

/-- In dimension three, the concrete order-zero Ricci connection-difference
coefficient has an intrinsic `H1` bound depending only on the metric `H3` jet
size and a fixed common fibre ellipticity bound. -/
theorem ricci0_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (linearizedRicciConnDiffOrder0CoeffField
              (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ (B A) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ :=
    rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0CoeffField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K, hK, hgrid⟩ := h3_grid_int (I := I) (M := M) hDim g₀
  let Q : ℝ → ℝ := fun A => ∑ i ∈ Finset.range 2,
    C i * ∑ k ∈ Finset.range (i + 3), K A k
  let B : ℝ → ℝ := fun A => Real.sqrt (Q A)
  have hQ : ∀ A : ℝ, 0 ≤ A → 0 ≤ Q A := by
    intro A hA
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hC i)
      (Finset.sum_nonneg fun k _ => hK A hA k)
  refine ⟨B, fun A hA => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound A hA hP
  have hgr : ∀ k : ℕ, k ≤ 3 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g₀ P k)
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g₀ P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ K A k := by
    intro k hk
    simpa only [lowJetGrid] using hgrid P A hA hP k hk
  have hle := grid_h1_le (I := I) (M := M) g₀ P (K A) C
    (hK A hA) hgr hC
    (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
    (fun i _ x => hpt g₁ P htie hδ_le hδ_nonneg hbound i x)
  change _ ≤ (B A) ^ 2
  rw [show (B A) ^ 2 = Q A by
    simp only [B, Real.sq_sqrt (hQ A hA)]]
  exact hle

/-- In dimension three, the `DLa` part of the concrete order-zero DeTurck
coefficient has an intrinsic `H1` bound from the same metric `H3` data.  The
fixed DeTurck gauge background is independent of the frozen spectral metric. -/
theorem dla_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
          (B A) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ :=
    rfns_iteratedCovGrad_deTurckLieDLaCoeffField_diagonalProductGrid_le
      (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨K, hK, hgrid⟩ := h3_grid_int (I := I) (M := M) hDim g₀
  let Q : ℝ → ℝ := fun A => ∑ i ∈ Finset.range 2,
    C i * ∑ k ∈ Finset.range (i + 3), K A k
  let B : ℝ → ℝ := fun A => Real.sqrt (Q A)
  have hQ : ∀ A : ℝ, 0 ≤ A → 0 ≤ Q A := by
    intro A hA
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hC i)
      (Finset.sum_nonneg fun k _ => hK A hA k)
  refine ⟨B, fun A hA => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound A hA hP
  have hgr : ∀ k : ℕ, k ≤ 3 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g₀ P k)
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g₀ P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ K A k := by
    intro k hk
    simpa only [lowJetGrid] using hgrid P A hA hP k hk
  have hle := grid_h1_le (I := I) (M := M) g₀ P (K A) C
    (hK A hA) hgr hC
    (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg)
    (fun i _ x => hpt g₁ P htie hδ_le hδ_nonneg hbound i x)
  change _ ≤ (B A) ^ 2
  rw [show (B A) ^ 2 = Q A by
    simp only [B, Real.sq_sqrt (hQ A hA)]]
  exact hle

/-- In dimension three, changing the fixed DeTurck background in the `DLb`
coefficient costs only an intrinsic `H1` jet of the metric perturbation.  In
particular, no derivative beyond the endpoint `H3` ball is used. -/
theorem dlbDiff_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
              deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
          (B A) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ := dlbDiff_grid (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨K, hK, hgrid⟩ := h3_grid_int (I := I) (M := M) hDim g₀
  let Q : ℝ → ℝ := fun A => ∑ i ∈ Finset.range 2,
    C i * ∑ k ∈ Finset.range (i + 3), K A k
  let B : ℝ → ℝ := fun A => Real.sqrt (Q A)
  have hQ : ∀ A : ℝ, 0 ≤ A → 0 ≤ Q A := by
    intro A hA
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hC i)
      (Finset.sum_nonneg fun k _ => hK A hA k)
  refine ⟨B, fun A _ => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound A hA hP
  have hgr : ∀ k : ℕ, k ≤ 3 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g₀ P k)
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g₀ P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ K A k := by
    intro k hk
    simpa only [lowJetGrid] using hgrid P A hA hP k hk
  have hpt' : ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
              deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
        C i * ∑ k ∈ Finset.range (i + 3),
          lowJetGrid (I := I) (M := M) g₀ P k x := by
    intro i x
    let b : ℕ → ℝ := fun l' =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
        ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)
    have hb : ∀ l', 0 ≤ b l' := fun l' =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
    have hwin := Combinatorics.antidiagonalTupleGridWindow_mono b hb
      (show i + 2 ≤ i + 3 by omega)
    have hwin' :
        Combinatorics.antidiagonalTupleGridWindow b (i + 2) ≤
          ∑ k ∈ Finset.range (i + 3),
            lowJetGrid (I := I) (M := M) g₀ P k x := by
      simpa only [b, Combinatorics.antidiagonalTupleGridWindow,
        Combinatorics.antidiagonalTupleGrid, lowJetGrid] using hwin
    exact (hpt g₁ P htie hδ_le hδ_nonneg hbound i x).trans
      (mul_le_mul_of_nonneg_left hwin' (hC i))
  have hle := grid_h1_le (I := I) (M := M) g₀ P (K A) C
    (hK A hA) hgr hC
    (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)
    (fun i _ x => hpt' i x)
  change _ ≤ (B A) ^ 2
  rw [show (B A) ^ 2 = Q A by
    simp only [B, Real.sq_sqrt (hQ A hA)]]
  exact hle

/-- In dimension three, the fixed-curvature piece of `lieCorr0` has an
intrinsic `H1` bound from only the metric `H3` jet.  Algebraically it is one
moving cometric trace acting on a fixed smooth curvature passenger. -/
theorem riem_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0Riem (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ (B A) ^ 2 := by
  classical
  obtain ⟨Ct, hCt, htpt⟩ := trace2_grid (I := I) (M := M) g₀ hδ₀
  obtain ⟨Bt, hBt, htH1⟩ :=
    h1_of_grid (I := I) (M := M) (r := 4) (s := 2) hDim g₀ Ct hCt
  obtain ⟨Cp, hCp, happ⟩ :=
    appRS_h1_h2_h1 (I := I) (M := M) hDim g₀ 2 4 2
  let Rf : SmoothCcTensor g₀ 2 4 := lc0RiemRest (I := I) (M := M) g₀
  let Fr : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 2 4 j Rf‖ ^ 2
  let Br : ℝ := Real.sqrt Fr
  let B : ℝ → ℝ := fun A => Cp * Bt A * Br
  have hFr : 0 ≤ Fr := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hBr : 0 ≤ Br := Real.sqrt_nonneg _
  have hRf : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 4 j Rf‖ ^ 2) ≤ Br ^ 2 := by
    rw [show Br ^ 2 = Fr by simp only [Br, Real.sq_sqrt hFr]]
  refine ⟨B, fun A hA => by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg hCp (hBt A hA)) hBr, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound A hA hP
  let Tr : SmoothCcTensor g₀ 4 2 :=
    lc0Trace (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2
  have hTrpt : ∀ (i : ℕ), i < 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 4 2 i Tr).toSection x) ≤
        Ct i * ∑ k ∈ Finset.range (i + 3),
          lowJetGrid (I := I) (M := M) g₀ P k x := by
    intro i _ x
    let b : ℕ → ℝ := fun j =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)
    have hb : ∀ j, 0 ≤ b j := fun j =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
    have hwin := Combinatorics.antidiagonalTupleGridWindow_mono b hb
      (show i + 1 ≤ i + 3 by omega)
    have hwin' :
        (∑ k ∈ Finset.range (i + 1),
          Combinatorics.antidiagonalTupleGrid b k) ≤
        ∑ k ∈ Finset.range (i + 3),
          lowJetGrid (I := I) (M := M) g₀ P k x := by
      simpa only [b, Combinatorics.antidiagonalTupleGridWindow,
        Combinatorics.antidiagonalTupleGrid, lowJetGrid] using hwin
    have hraw := htpt g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0RiemPerm2 i x
    change riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i Tr).toSection x) ≤ _
    exact hraw.trans (mul_le_mul_of_nonneg_left hwin' (hCt i))
  have hTr : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i Tr‖ ^ 2) ≤ (Bt A) ^ 2 :=
    htH1 P Tr A hA hP hTrpt
  have hApp := happ Tr Rf (Bt A) Br (hBt A hA) hBr hTr hRf
  have hAppSq :
      ‖(⟨appCcRS (I := I) (M := M) g₀ 2 4 2 Tr Rf⟩ :
          SmoothCcTensorH1 g₀ 2 2)‖ ^ 2 ≤ (B A) ^ 2 := by
    have hs := pow_le_pow_left₀ (norm_nonneg
      (⟨appCcRS (I := I) (M := M) g₀ 2 4 2 Tr Rf⟩ :
        SmoothCcTensorH1 g₀ 2 2)) hApp 2
    simpa only [B, mul_pow] using hs
  have hAppJet : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 4 2 Tr Rf)‖ ^ 2) ≤
      (B A) ^ 2 := by
    rw [h1_jet_sq (I := I) (M := M) g₀ 2 2
      (appCcRS (I := I) (M := M) g₀ 2 4 2 Tr Rf)] at hAppSq
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hAppSq
  rw [riem_refold (I := I) (M := M) g₀ g₁]
  simpa only [Tr, Rf, iteratedCovGrad_smul_real, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_one, one_mul] using hAppJet

/-- Tame `H1` jet bound for the cancellation-compatible operator normal form
of the vector--bilinear correction.  Every moving trace is a low `H2` factor;
the unique top `H3` derivative is carried linearly by the self-background
Koszul tensor. -/
theorem vbForm_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ B R A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0VBForm (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ (B R A) ^ 2 := by
  classical
  obtain ⟨Bt1, hBt1, htr1⟩ := trace_h2 (I := I) (M := M) 1 hDim g₀ hδ₀
  obtain ⟨Bt2, hBt2, htr2⟩ := trace_h2 (I := I) (M := M) 2 hDim g₀ hδ₀
  obtain ⟨Cv, hCv, hvprod⟩ := appRS_h2_h2_h2
    (I := I) (M := M) hDim g₀ 0 3 1
  obtain ⟨Ci, hCi, hiprod⟩ := appRS_h2_h2_h2
    (I := I) (M := M) hDim g₀ 2 3 1
  obtain ⟨Cn, hCn, hnprod⟩ := app_h1h2_j1
    (I := I) (M := M) hDim g₀ 2 1 4
  obtain ⟨Co, hCo, hoprod⟩ := app_h2h1_j1
    (I := I) (M := M) hDim g₀ 2 4 2
  let sf : ℕ → ℝ := fun w => Real.sqrt ((Module.finrank ℝ E : ℝ) ^ w)
  let Vb : ℝ → ℝ → ℝ := fun R A => Cv * Bt1 R * (4 * A)
  let Ib : ℝ → ℝ → ℝ := fun R A => Ci * Bt1 R * (sf 2 * Vb R A)
  let Nb : ℝ → ℝ → ℝ := fun R A => Cn * (sf 1 * (4 * R)) * Ib R A
  let Ob : ℝ → ℝ → ℝ := fun R A => Co * Bt2 R * Nb R A
  let B : ℝ → ℝ → ℝ := fun R A => 2 * Ob R A
  have hsf : ∀ w : ℕ, 0 ≤ sf w := fun w => Real.sqrt_nonneg _
  have hVb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Vb R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCv (hBt1 R hR))
      (mul_nonneg (by norm_num) hA)
  have hIb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Ib R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCi (hBt1 R hR))
      (mul_nonneg (hsf 2) (hVb R hR A hA))
  have hNb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Nb R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCn
      (mul_nonneg (hsf 1) (mul_nonneg (by norm_num) hR)))
      (hIb R hR A hA)
  have hOb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Ob R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCo (hBt2 R hR)) (hNb R hR A hA)
  refine ⟨B, fun R hR A hA => mul_nonneg (by norm_num) (hOb R hR A hA), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 hP3
  let T1 : SmoothCcTensor g₀ 3 1 :=
    lc0Trace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)
  let T1i : SmoothCcTensor g₀ 3 1 :=
    lc0Trace (I := I) (M := M) g₀ g₁ 1 lieCorr0IVPerm
  let T2 : SmoothCcTensor g₀ 4 2 :=
    lc0Trace (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm
  let K : SmoothCcTensor g₀ 0 3 :=
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀
  let Vf : SmoothCcTensor g₀ 0 1 :=
    appCcRS (I := I) (M := M) g₀ 0 3 1 T1 K
  let Vs : SmoothCcTensor g₀ 2 3 :=
    slotExtendIter (I := I) (M := M) g₀ 0 1 2 Vf
  let Iv : SmoothCcTensor g₀ 2 1 :=
    appCcRS (I := I) (M := M) g₀ 2 3 1 T1i Vs
  let Ks : SmoothCcTensor g₀ 1 4 :=
    slotExtendIter (I := I) (M := M) g₀ 0 3 1 K
  let Inn : SmoothCcTensor g₀ 2 4 :=
    appCcRS (I := I) (M := M) g₀ 2 1 4 Ks Iv
  let Out : SmoothCcTensor g₀ 2 2 :=
    appCcRS (I := I) (M := M) g₀ 2 4 2 T2 Inn
  have hT1 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i T1‖ ^ 2) ≤ (Bt1 R) ^ 2 := by
    simpa only [T1] using htr1 g₁ P htie hδ_le hδ_nonneg hbound
      (Equiv.refl _) R hR hP2
  have hT1i : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i T1i‖ ^ 2) ≤ (Bt1 R) ^ 2 := by
    simpa only [T1i] using htr1 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0IVPerm R hR hP2
  have hT2 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i T2‖ ^ 2) ≤ (Bt2 R) ^ 2 := by
    simpa only [T2] using htr2 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0VBPerm R hR hP2
  have hK2 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i K‖ ^ 2) ≤ (4 * A) ^ 2 := by
    simpa only [K] using kappaSelf_h2
      (I := I) (M := M) g₀ g₁ P htie A hA hP3
  have hK1 : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i K‖ ^ 2) ≤ (4 * R) ^ 2 := by
    simpa only [K] using kappaSelf_h1
      (I := I) (M := M) g₀ g₁ P htie R hR hP2
  have hVf : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 1 i Vf‖ ^ 2) ≤ (Vb R A) ^ 2 := by
    simpa only [Vf, Vb] using hvprod T1 K (Bt1 R) (4 * A)
      (hBt1 R hR) (mul_nonneg (by norm_num) hA) hT1 hK2
  have hVs : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 3 i Vs‖ ^ 2) ≤
        (sf 2 * Vb R A) ^ 2 := by
    simpa only [Vs, sf] using slotIter_h2b
      (I := I) (M := M) g₀ 0 1 2 Vf (Vb R A) hVf
  have hIv : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 1 i Iv‖ ^ 2) ≤ (Ib R A) ^ 2 := by
    simpa only [Iv, Ib] using hiprod T1i Vs (Bt1 R) (sf 2 * Vb R A)
      (hBt1 R hR) (mul_nonneg (hsf 2) (hVb R hR A hA)) hT1i hVs
  have hKs : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 4 i Ks‖ ^ 2) ≤
        (sf 1 * (4 * R)) ^ 2 := by
    simpa only [Ks, sf] using slotIter_h1b
      (I := I) (M := M) g₀ 0 3 1 K (4 * R) hK1
  have hInn : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 4 i Inn‖ ^ 2) ≤ (Nb R A) ^ 2 := by
    simpa only [Inn, Nb] using hnprod Ks Iv (sf 1 * (4 * R)) (Ib R A)
      (mul_nonneg (hsf 1) (mul_nonneg (by norm_num) hR))
      (hIb R hR A hA) hKs hIv
  have hOut : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Out‖ ^ 2) ≤ (Ob R A) ^ 2 := by
    simpa only [Out, Ob] using hoprod T2 Inn (Bt2 R) (Nb R A)
      (hBt2 R hR) (hNb R hR A hA) hT2 hInn
  have htwo := jet_two (I := I) (M := M) g₀ 2 2 2 Out
  rw [show lc0VBForm (I := I) (M := M) g₀ g₁ = (2 : ℝ) • Out by rfl,
    htwo]
  change 4 * (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Out‖ ^ 2) ≤ (B R A) ^ 2
  calc
    _ ≤ 4 * (Ob R A) ^ 2 := mul_le_mul_of_nonneg_left hOut (by norm_num)
    _ = (B R A) ^ 2 := by dsimp only [B]; ring

/-- Tame `H1` jet bound for the mixed connection-correction normal form.  The
background connection factor is kept in low `H1`, the self-background Koszul
factor carries the unique top derivative in `H2`, and every subsequent moving
trace is allocated as `H2 × H1 → H1`. -/
theorem amixForm_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ B R A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0AMixForm (I := I) (M := M) g₀ g₁ gB)‖ ^ 2) ≤
          (B R A) ^ 2 := by
  classical
  obtain ⟨Bt2, hBt2, htr2⟩ := trace_h2 (I := I) (M := M) 2 hDim g₀ hδ₀
  obtain ⟨Bt3, hBt3, htr3⟩ := trace_h2 (I := I) (M := M) 3 hDim g₀ hδ₀
  obtain ⟨Bt4, hBt4, htr4⟩ := trace_h2 (I := I) (M := M) 4 hDim g₀ hδ₀
  obtain ⟨BK, hBK, hkbg⟩ := kappaBg_h1 (I := I) (M := M) hDim g₀ gB
  obtain ⟨Cq, hCq, hqprod⟩ := appRS_h2_h2_h2
    (I := I) (M := M) hDim g₀ 2 5 3
  obtain ⟨Cn, hCn, hnprod⟩ := app_h1h2_j1
    (I := I) (M := M) hDim g₀ 2 3 6
  obtain ⟨Cm, hCm, hmprod⟩ := app_h2h1_j1
    (I := I) (M := M) hDim g₀ 2 6 4
  obtain ⟨Co, hCo, hoprod⟩ := app_h2h1_j1
    (I := I) (M := M) hDim g₀ 2 4 2
  let sf : ℕ → ℝ := fun w => Real.sqrt ((Module.finrank ℝ E : ℝ) ^ w)
  let Qb : ℝ → ℝ → ℝ := fun R A => Cq * Bt3 R * (sf 2 * (4 * A))
  let Nb : ℝ → ℝ → ℝ := fun R A => Cn * (sf 3 * BK R) * Qb R A
  let Mb : ℝ → ℝ → ℝ := fun R A => Cm * Bt4 R * Nb R A
  let Ob : ℝ → ℝ → ℝ := fun R A => Co * Bt2 R * Mb R A
  let B : ℝ → ℝ → ℝ := fun R A => 4 * Ob R A
  have hsf : ∀ w : ℕ, 0 ≤ sf w := fun w => Real.sqrt_nonneg _
  have hQb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Qb R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCq (hBt3 R hR))
      (mul_nonneg (hsf 2) (mul_nonneg (by norm_num) hA))
  have hNb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Nb R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCn (mul_nonneg (hsf 3) (hBK R hR)))
      (hQb R hR A hA)
  have hMb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Mb R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCm (hBt4 R hR)) (hNb R hR A hA)
  have hOb : ∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ Ob R A := by
    intro R hR A hA
    exact mul_nonneg (mul_nonneg hCo (hBt2 R hR)) (hMb R hR A hA)
  refine ⟨B, fun R hR A hA => mul_nonneg (by norm_num) (hOb R hR A hA), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 hP3
  let T2a : SmoothCcTensor g₀ 4 2 :=
    lc0Trace (I := I) (M := M) g₀ g₁ 2 lieCorr0AMixPerm2
  let T2b : SmoothCcTensor g₀ 4 2 :=
    lc0Trace (I := I) (M := M) g₀ g₁ 2
      (lc0SwapPerm * lieCorr0AMixPerm2)
  let T3 : SmoothCcTensor g₀ 5 3 :=
    lc0Trace (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ
  let T4 : SmoothCcTensor g₀ 6 4 :=
    lc0Trace (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1
  let K0 : SmoothCcTensor g₀ 0 3 :=
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀
  let KB : SmoothCcTensor g₀ 0 3 :=
    lc0Kappa (I := I) (M := M) g₀ g₁ gB
  let K0s : SmoothCcTensor g₀ 2 5 :=
    slotExtendIter (I := I) (M := M) g₀ 0 3 2 K0
  let Q : SmoothCcTensor g₀ 2 3 :=
    appCcRS (I := I) (M := M) g₀ 2 5 3 T3 K0s
  let KBs : SmoothCcTensor g₀ 3 6 :=
    slotExtendIter (I := I) (M := M) g₀ 0 3 3 KB
  let N : SmoothCcTensor g₀ 2 6 :=
    appCcRS (I := I) (M := M) g₀ 2 3 6 KBs Q
  let Mid : SmoothCcTensor g₀ 2 4 :=
    appCcRS (I := I) (M := M) g₀ 2 6 4 T4 N
  let Oa : SmoothCcTensor g₀ 2 2 :=
    appCcRS (I := I) (M := M) g₀ 2 4 2 T2a Mid
  let Ob' : SmoothCcTensor g₀ 2 2 :=
    appCcRS (I := I) (M := M) g₀ 2 4 2 T2b Mid
  have hT2a : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i T2a‖ ^ 2) ≤ (Bt2 R) ^ 2 := by
    simpa only [T2a] using htr2 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0AMixPerm2 R hR hP2
  have hT2b : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i T2b‖ ^ 2) ≤ (Bt2 R) ^ 2 := by
    simpa only [T2b] using htr2 g₁ P htie hδ_le hδ_nonneg hbound
      (lc0SwapPerm * lieCorr0AMixPerm2) R hR hP2
  have hT3 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 5 3 i T3‖ ^ 2) ≤ (Bt3 R) ^ 2 := by
    simpa only [T3] using htr3 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0AMixPermQ R hR hP2
  have hT4 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 6 4 i T4‖ ^ 2) ≤ (Bt4 R) ^ 2 := by
    simpa only [T4] using htr4 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0AMixPerm1 R hR hP2
  have hK0 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i K0‖ ^ 2) ≤ (4 * A) ^ 2 := by
    simpa only [K0] using kappaSelf_h2
      (I := I) (M := M) g₀ g₁ P htie A hA hP3
  have hKB : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i KB‖ ^ 2) ≤ (BK R) ^ 2 := by
    simpa only [KB] using hkbg g₁ P htie R hR hP2
  have hK0s : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 5 i K0s‖ ^ 2) ≤
        (sf 2 * (4 * A)) ^ 2 := by
    simpa only [K0s, sf] using slotIter_h2b
      (I := I) (M := M) g₀ 0 3 2 K0 (4 * A) hK0
  have hQ : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 3 i Q‖ ^ 2) ≤ (Qb R A) ^ 2 := by
    simpa only [Q, Qb] using hqprod T3 K0s (Bt3 R) (sf 2 * (4 * A))
      (hBt3 R hR) (mul_nonneg (hsf 2) (mul_nonneg (by norm_num) hA)) hT3 hK0s
  have hKBs : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 3 6 i KBs‖ ^ 2) ≤
        (sf 3 * BK R) ^ 2 := by
    simpa only [KBs, sf] using slotIter_h1b
      (I := I) (M := M) g₀ 0 3 3 KB (BK R) hKB
  have hN : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 6 i N‖ ^ 2) ≤ (Nb R A) ^ 2 := by
    simpa only [N, Nb] using hnprod KBs Q (sf 3 * BK R) (Qb R A)
      (mul_nonneg (hsf 3) (hBK R hR)) (hQb R hR A hA) hKBs hQ
  have hMid : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 4 i Mid‖ ^ 2) ≤ (Mb R A) ^ 2 := by
    simpa only [Mid, Mb] using hmprod T4 N (Bt4 R) (Nb R A)
      (hBt4 R hR) (hNb R hR A hA) hT4 hN
  have hOa : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Oa‖ ^ 2) ≤ (Ob R A) ^ 2 := by
    simpa only [Oa, Ob] using hoprod T2a Mid (Bt2 R) (Mb R A)
      (hBt2 R hR) (hMb R hR A hA) hT2a hMid
  have hOb' : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Ob'‖ ^ 2) ≤ (Ob R A) ^ 2 := by
    simpa only [Ob', Ob] using hoprod T2b Mid (Bt2 R) (Mb R A)
      (hBt2 R hR) (hMb R hR A hA) hT2b hMid
  have hsum := jet_sum2 (I := I) (M := M) g₀ 2 2 2 Oa Ob'
    (Ob R A) (Ob R A) hOa hOb'
  have htwo := jet_two (I := I) (M := M) g₀ 2 2 2 (Oa + Ob')
  rw [show lc0AMixForm (I := I) (M := M) g₀ g₁ gB =
      (2 : ℝ) • (Oa + Ob') by rfl, htwo]
  change 4 * (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i (Oa + Ob')‖ ^ 2) ≤ (B R A) ^ 2
  calc
    _ ≤ 4 * (2 * ((Ob R A) ^ 2 + (Ob R A) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (B R A) ^ 2 := by dsimp only [B]; ring

/-- Tame `H1` jet bound for the genuine vector--bilinear correction. -/
theorem vb_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ B R A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0VB (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ (B R A) ^ 2 := by
  obtain ⟨B, hB, hform⟩ := vbForm_h1 (I := I) (M := M) hDim g₀ hδ₀
  refine ⟨B, hB, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 hP3
  rw [vb_refold (I := I) (M := M) g₀ g₁]
  exact hform g₁ P htie hδ_le hδ_nonneg hbound R A hR hA hP2 hP3

/-- Tame `H1` jet bound for the genuine mixed connection correction. -/
theorem amix_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → ∀ A : ℝ, 0 ≤ A → 0 ≤ B R A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0AMix (I := I) (M := M) g₀ g₁ gB)‖ ^ 2) ≤
          (B R A) ^ 2 := by
  obtain ⟨B, hB, hform⟩ := amixForm_h1 (I := I) (M := M) hDim g₀ gB hδ₀
  refine ⟨B, hB, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 hP3
  rw [amix_refold (I := I) (M := M) g₀ g₁ gB]
  exact hform g₁ P htie hδ_le hδ_nonneg hbound R A hR hA hP2 hP3

/-- The combined order-zero tail splits into a background-change term and the
base-background pair in which the leading endomorphism contribution cancels
against `lieCorr0`. -/
theorem tail0_split
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg +
        lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg =
      (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
          deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀) +
        (lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg +
          deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀) := by
  rw [endo_eq_dlb (I := I) (M := M) g₀ g₁ g₀]
  abel

/-- Cancellation-preserving five-piece normal form of the complete order-zero
tail.  The first summand records the change of DeTurck background; the second
is the insertion difference left after cancelling the base-background
endomorphism arm. -/
theorem tail0_decomp
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg +
        lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg =
      (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
          deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀) +
        ((((lc0Insert (I := I) (M := M) g₀ g₁ g_bg -
              lc0Insert (I := I) (M := M) g₀ g₁ g₀) +
            lc0VB (I := I) (M := M) g₀ g₁) +
          lc0AMix (I := I) (M := M) g₀ g₁ g_bg) +
        lc0Riem (I := I) (M := M) g₀ g₁) := by
  rw [tail0_split (I := I) (M := M) g₀ g₁ g_bg,
    tail_base_split (I := I) (M := M) g₀ g₁ g_bg]

/-- Assemble the five cancellation-preserving order-zero pieces into the
`H1` jet of the complete `DLb + lieCorr0` tail. -/
theorem tail_h1_parts
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (Bd Bi Bv Ba Br : ℝ)
    (hD : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
          deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤ Bd ^ 2)
    (hI : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lc0Insert (I := I) (M := M) g₀ g₁ g_bg -
          lc0Insert (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤ Bi ^ 2)
    (hV : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lc0VB (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ Bv ^ 2)
    (hA : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lc0AMix (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤ Ba ^ 2)
    (hR : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lc0Riem (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ Br ^ 2) :
    (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg +
          lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
      (Real.sqrt (5 *
        (Bd ^ 2 + Bi ^ 2 + Bv ^ 2 + Ba ^ 2 + Br ^ 2))) ^ 2 := by
  let Df : SmoothCcTensor g₀ 2 2 :=
    deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀
  let Ins : SmoothCcTensor g₀ 2 2 :=
    lc0Insert (I := I) (M := M) g₀ g₁ g_bg -
      lc0Insert (I := I) (M := M) g₀ g₁ g₀
  let VB : SmoothCcTensor g₀ 2 2 := lc0VB (I := I) (M := M) g₀ g₁
  let AM : SmoothCcTensor g₀ 2 2 := lc0AMix (I := I) (M := M) g₀ g₁ g_bg
  let RF : SmoothCcTensor g₀ 2 2 := lc0Riem (I := I) (M := M) g₀ g₁
  have hsum := jet_add5 (I := I) (M := M) g₀ 2 2 2 Df Ins VB AM RF
    Bd Bi Bv Ba Br (by simpa only [Df] using hD) (by simpa only [Ins] using hI)
    (by simpa only [VB] using hV) (by simpa only [AM] using hA)
    (by simpa only [RF] using hR)
  have htail :
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg +
          lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg =
        Df + ((((Ins + VB) + AM) + RF)) := by
    simpa only [Df, Ins, VB, AM, RF] using
      tail0_decomp (I := I) (M := M) g₀ g₁ g_bg
  have hinside : 0 ≤ 5 *
      (Bd ^ 2 + Bi ^ 2 + Bv ^ 2 + Ba ^ 2 + Br ^ 2) := by positivity
  rw [htail, Real.sq_sqrt hinside]
  exact hsum

/-- Direct synthesis of the complete order-zero path coefficient.  The sole
remaining input is the low jet of the combined `DLb + lieCorr0` tail, so the
essential cancellation inside that pair is retained.  The Ricci and `DLa`
bounds are supplied above from the endpoint spectral `H3` ball. -/
theorem rhs0_h1_of_aux
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ C : ℝ, ∃ BR BD : ℝ → ℝ,
      0 ≤ C ∧ (∀ A : ℝ, 0 ≤ A → 0 ≤ BR A) ∧
        (∀ A : ℝ, 0 ≤ A → 0 ≤ BD A) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ₀)
        (R : ℝ), 0 ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ ≤ R →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (Lt : ℝ),
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLbCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg +
              lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2) ≤ Lt ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (rhsLow0Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)‖ ^ 2) ≤
          (Real.sqrt (4 *
            (4 * (BR (C * R)) ^ 2 + (BD (C * R)) ^ 2 + Lt ^ 2))) ^ 2 := by
  classical
  obtain ⟨C, hC, hpath⟩ := convex_h3_jet (I := I) (M := M) g₀
  obtain ⟨BR, hBR, hric⟩ := ricci0_h1 (I := I) (M := M) hDim g₀ hδ₀_lt
  obtain ⟨BD, hBD, hdla⟩ := dla_h1 (I := I) (M := M) hDim g₀ g_bg hδ₀_lt
  refine ⟨C, BR, BD, hC, hBR, hBD, ?_⟩
  intro T T' hδ hδ' R hR hT hT' s hs Lt hLt
  let P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s
  let g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s
  have hPjet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ (C * R) ^ 2 := by
    simpa only [P] using hpath T T' R hR hT hT' s hs
  have hPbound : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) δ₀ := by
    have h := convexPerturbation_gFibreOpBound
      (I := I) (M := M) g₀ T T' hδ hδ' hs.1 hs.2
    have hscalar : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    rw [hscalar] at h
    simpa only [P] using h
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    simpa only [g₁, P] using realizedFam_inner_of_mem
      (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ₀_lt hδ₀_lt hs) y v w
  have hCR : 0 ≤ C * R := mul_nonneg hC hR
  let Ric : SmoothCcTensor g₀ 2 2 :=
    linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
  let DLa : SmoothCcTensor g₀ 2 2 :=
    deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg
  let Tail : SmoothCcTensor g₀ 2 2 :=
    deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg +
      lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg
  have hRic : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Ric‖ ^ 2) ≤ (BR (C * R)) ^ 2 := by
    simpa only [Ric] using hric g₁ P htie (δ := δ₀) le_rfl hδ₀_nonneg hPbound
      (C * R) hCR hPjet
  have hDLa : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i DLa‖ ^ 2) ≤ (BD (C * R)) ^ 2 := by
    simpa only [DLa] using hdla g₁ P htie (δ := δ₀) le_rfl hδ₀_nonneg hPbound
      (C * R) hCR hPjet
  have hTail : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Tail‖ ^ 2) ≤ Lt ^ 2 := by
    simpa only [Tail, g₁] using hLt
  have hzero : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (0 : SmoothCcTensor g₀ 2 2)‖ ^ 2) ≤ (0 : ℝ) ^ 2 := by simp
  have hsum := jet_add4 (I := I) (M := M) g₀ 2 2 2 Ric DLa Tail
    (0 : SmoothCcTensor g₀ 2 2) (BR (C * R)) (BD (C * R)) Lt 0
    hRic hDLa hTail hzero
  have hinside : 0 ≤ 4 *
      (4 * (BR (C * R)) ^ 2 + (BD (C * R)) ^ 2 + Lt ^ 2) := by
    positivity
  have hrhs : rhsLow0Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s =
      (-2 : ℝ) • Ric + ((DLa + Tail) + (0 : SmoothCcTensor g₀ 2 2)) := by
    simp only [rhsLow0Coeff, linearizedRicciConnDiffOrder0Coeff,
      Ric, DLa, Tail, g₁, add_zero]
    rw [deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField]
    abel
  rw [hrhs, Real.sq_sqrt hinside]
  exact hsum

/-- Direct two-piece synthesis of the complete order-one path coefficient.
Its precise remaining producers are an `H2` jet bound for the Ricci order-one
`appCcRS` field and an `H2` jet bound for `deTurckLieArm1Coeff`. -/
theorem rhs1_h2_of_aux
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (Ar Al : ℝ)
    (hRic : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2) ≤ Ar ^ 2)
    (hLie : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2) ≤ Al ^ 2) :
    (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (rhsLow1Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)‖ ^ 2) ≤
      (Real.sqrt (2 * (4 * Ar ^ 2 + Al ^ 2))) ^ 2 := by
  have hsum := jet_add2 (I := I) (M := M) g₀ 3 2 3
    (linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s))
    (deTurckLieArm1Coeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
    Ar Al hRic hLie
  have hinside : 0 ≤ 2 * (4 * Ar ^ 2 + Al ^ 2) := by positivity
  simpa only [rhsLow1Coeff, linearizedRicciConnDiffOrder1Coeff,
    Real.sq_sqrt hinside] using hsum

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
