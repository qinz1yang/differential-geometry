import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Coefficients.LowOrderJetBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PointwiseUnif
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.ThirdOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Morrey
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.MixedTensorThirdOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Grid.ConvexJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Pairing.TopOrderH5Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Path.RemainderConvexBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply ccTensorToHs ccTensorToHs_smul
    covsum_hs_three h3CovsumC h3CovsumC_nonneg norm_ccHs_eq_smoothHs
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
    iteratedCovGrad_comp_norm oneMinusConnLapSmooth)
open DifferentialGeometry.Analysis.Sobolev (iteratedCovGrad)
open DifferentialGeometry.Analysis.Elliptic (riemannianFiberNormSq)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma two_mul_le_eps {eta x y : ℝ} (heta : 0 < eta) :
    2 * x * y ≤ eta * x ^ 2 + eta⁻¹ * y ^ 2 := by
  have hinv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  have hs := mul_nonneg hinv (sq_nonneg (eta * x - y))
  have hexpand : eta⁻¹ * (eta * x - y) ^ 2 =
      eta * x ^ 2 - 2 * x * y + eta⁻¹ * y ^ 2 := by
    field_simp [ne_of_gt heta]
    ring
  rw [hexpand] at hs
  linarith

private lemma shifted_three_sq_le (a : ℕ → ℝ) :
    ∑ j ∈ Finset.range 3, a (1 + j) ^ 2 ≤
      ∑ j ∈ Finset.range 4, a j ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd]
  nlinarith [sq_nonneg (a 0)]

private lemma shifted_four_sq_le (a : ℕ → ℝ) :
    ∑ j ∈ Finset.range 4, a (1 + j) ^ 2 ≤
      ∑ j ∈ Finset.range 5, a j ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd]
  nlinarith [sq_nonneg (a 0)]

private lemma low1_first_poly
    {Ca Ct Ksum Cw y q : ℝ}
    (hCa : 0 ≤ Ca) (hKsum : 0 ≤ Ksum)
    (hCw : 0 ≤ Cw) (hy : 0 ≤ y) (hq : 0 ≤ q) :
    Ca * ((Ct * y) ^ 2 * (Ksum * (1 + q ^ 2 + Cw * y ^ 2))) ≤
      (Ca * Ct ^ 2 * Ksum * (1 + Cw)) *
        (y + y * q + y ^ 2) ^ 2 := by
  let P : ℝ := y + y * q + y ^ 2
  let L : ℝ := Ca * Ct ^ 2 * Ksum
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hbase : y ^ 2 + (y * q) ^ 2 ≤ P ^ 2 := by
    dsimp only [P]
    nlinarith only [sq_nonneg y, sq_nonneg (y * q), sq_nonneg (y ^ 2),
      mul_nonneg hy (mul_nonneg hy hq),
      mul_nonneg hy (sq_nonneg y),
      mul_nonneg (mul_nonneg hy hq) (sq_nonneg y)]
  have htop : Cw * (y ^ 2) ^ 2 ≤ Cw * P ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hCw
    exact pow_le_pow_left₀ (sq_nonneg y) (by
      dsimp only [P]
      nlinarith only [hy, mul_nonneg hy hq, sq_nonneg y]) 2
  calc
    Ca * ((Ct * y) ^ 2 * (Ksum * (1 + q ^ 2 + Cw * y ^ 2))) =
        L * (y ^ 2 + (y * q) ^ 2 + Cw * (y ^ 2) ^ 2) := by
      dsimp only [L]
      ring
    _ ≤ L * (P ^ 2 + Cw * P ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hbase htop) hL
    _ = (Ca * Ct ^ 2 * Ksum * (1 + Cw)) * P ^ 2 := by
      dsimp only [L]
      ring

private lemma low1_second_poly
    {Ca A0 A1 Cw y q : ℝ}
    (hCa : 0 ≤ Ca) (hCw : 0 ≤ Cw) (hy : 0 ≤ y) (hq : 0 ≤ q) :
    Ca * ((A0 + A1 * y) ^ 2 * (q ^ 2 + Cw * y ^ 2)) ≤
      (2 * Ca * A0 ^ 2) * q ^ 2 +
        (2 * Ca * A1 ^ 2 + 2 * Ca * Cw * (A0 ^ 2 + A1 ^ 2)) *
          (y + y * q + y ^ 2) ^ 2 := by
  let P : ℝ := y + y * q + y ^ 2
  have hyP : y ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hy (by
    dsimp only [P]
    nlinarith only [mul_nonneg hy hq, sq_nonneg y]) 2
  have hyqP : (y * q) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (mul_nonneg hy hq) (by
    dsimp only [P]
    nlinarith only [hy, mul_nonneg hy hq, sq_nonneg y]) 2
  have hy2P : (y ^ 2) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (sq_nonneg y) (by
    dsimp only [P]
    nlinarith only [hy, mul_nonneg hy hq, sq_nonneg y]) 2
  have hsum : (A0 + A1 * y) ^ 2 ≤ 2 * (A0 ^ 2 + (A1 * y) ^ 2) := by
    nlinarith only [sq_nonneg (A0 - A1 * y)]
  have hfac : 0 ≤ q ^ 2 + Cw * y ^ 2 :=
    add_nonneg (sq_nonneg q) (mul_nonneg hCw (sq_nonneg y))
  have hraw := mul_le_mul_of_nonneg_right hsum hfac
  have hraw' := mul_le_mul_of_nonneg_left hraw hCa
  have h1 : 2 * Ca * A1 ^ 2 * (y * q) ^ 2 ≤
      2 * Ca * A1 ^ 2 * P ^ 2 :=
    mul_le_mul_of_nonneg_left hyqP
      (mul_nonneg (mul_nonneg (by norm_num) hCa) (sq_nonneg A1))
  have h2 : 2 * Ca * Cw * A0 ^ 2 * y ^ 2 ≤
      2 * Ca * Cw * A0 ^ 2 * P ^ 2 :=
    mul_le_mul_of_nonneg_left hyP
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCa) hCw) (sq_nonneg A0))
  have h3 : 2 * Ca * Cw * A1 ^ 2 * (y ^ 2) ^ 2 ≤
      2 * Ca * Cw * A1 ^ 2 * P ^ 2 :=
    mul_le_mul_of_nonneg_left hy2P
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCa) hCw) (sq_nonneg A1))
  calc
    Ca * ((A0 + A1 * y) ^ 2 * (q ^ 2 + Cw * y ^ 2)) ≤
        Ca * (2 * (A0 ^ 2 + (A1 * y) ^ 2) * (q ^ 2 + Cw * y ^ 2)) := hraw'
    _ = (2 * Ca * A0 ^ 2) * q ^ 2 +
        2 * Ca * A1 ^ 2 * (y * q) ^ 2 +
        2 * Ca * Cw * A0 ^ 2 * y ^ 2 +
        2 * Ca * Cw * A1 ^ 2 * (y ^ 2) ^ 2 := by ring
    _ ≤ (2 * Ca * A0 ^ 2) * q ^ 2 +
        2 * Ca * A1 ^ 2 * P ^ 2 +
        2 * Ca * Cw * A0 ^ 2 * P ^ 2 +
        2 * Ca * Cw * A1 ^ 2 * P ^ 2 := by linarith only [h1, h2, h3]
    _ = (2 * Ca * A0 ^ 2) * q ^ 2 +
        (2 * Ca * A1 ^ 2 + 2 * Ca * Cw * (A0 ^ 2 + A1 ^ 2)) * P ^ 2 := by ring

theorem low1_path_h3
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Lambda : ℝ}
    (hLambda : 1 ≤ Lambda) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta_le : delta ≤ 1 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Lambda →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Lambda) →
        ∃ D : ℝ, 0 ≤ D ∧
          ∀ (T : SmoothCcTensor g 0 2)
            (hTsymm : ∀ (x : M) (u v : TangentSpace I x),
              ccTensorBilin (I := I) g T x u v =
                ccTensorBilin (I := I) g T x v u)
            (hdelta : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) delta)
              (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g
                  (0 : SmoothCcTensor g 0 2)) delta),
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ 1 →
            let D1 := ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M)
              g gBase T 0 (lt_of_le_of_lt hdelta_le (by norm_num))
                hdelta (lt_of_le_of_lt hdelta_le (by norm_num)) hdeltaZ
            let Y := operatorFieldApply (I := I) (M := M) g 3 2 D1
              (iteratedCovGrad (I := I) g 0 2 1 T)
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖ ≤
              C * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ +
                D *
                  (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ +
                    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ *
                      ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ +
                    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2) := by
  classical
  obtain ⟨Ca, hCa, happ⟩ :=
    operatorFieldComposition_h3_sup_uniform_bound (I := I) (M := M) gBase Lambda 0 3 2
  obtain ⟨Cm0, hCm0, hmor0⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hLambda 0 3
  obtain ⟨Cm3, hCm3, hmor3⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hLambda 3 2
  obtain ⟨B0, B1, hB0, hB1, hcoeff⟩ :=
    ricciDeTurckRemainderFirstOrderPathIntegral_h2_uniform_bound (I := I) (M := M) hDim gBase hLambda
      hdelta0 (lt_of_le_of_lt hdelta_le (by norm_num))
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hLambda
  let Cj : ℝ := h3CovsumC Kcurv.rankTwo Kcurv.rankThree
  let Ct : ℝ := Cm0 * Cj
  let Ch : ℝ := 2 + 2 * 3 + max 0 Kcurv.rankTwo
  let A0 : ℝ := Cm3 * B0 1
  let A1 : ℝ := Cm3 * B1 1
  let K0 : ℝ := 2 * Ca * A0 ^ 2
  let C : ℝ := 2 * Ch * Real.sqrt K0
  have hCj : 0 ≤ Cj := h3CovsumC_nonneg _ _
  have hCt : 0 ≤ Ct := mul_nonneg hCm0 hCj
  have hCh : 0 ≤ Ch := by
    dsimp only [Ch]
    positivity
  have hA0 : 0 ≤ A0 := mul_nonneg hCm3 (hB0 1 zero_le_one)
  have hA1 : 0 ≤ A1 := mul_nonneg hCm3 (hB1 1 zero_le_one)
  have hK0 : 0 ≤ K0 := by dsimp only [K0]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro g hEq hjet
  obtain ⟨hact2, hact3⟩ := hKcurv.bounds g hEq hjet
  obtain ⟨Kc, hKc, htow⟩ :=
    firstOrderCoefficient_jet_tower_quadratic_background (I := I) (M := M) g gBase
  obtain ⟨Cgap, hCgap, hgap⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
      (I := I) (M := M) g 3
  let Cw : ℝ := Cj ^ 2 + Cgap
  let Ksum : ℝ := ∑ i ∈ Finset.range 4, Kc i
  let Kfirst : ℝ := Ca * Ct ^ 2 * Ksum * (1 + Cw)
  let Ksecond : ℝ := 2 * Ca * A1 ^ 2 +
    2 * Ca * Cw * (A0 ^ 2 + A1 ^ 2)
  let K1 : ℝ := Kfirst + Ksecond
  let D : ℝ := 2 * Ch * Real.sqrt K1
  have hCw : 0 ≤ Cw := add_nonneg (sq_nonneg _) hCgap
  have hKsum : 0 ≤ Ksum := Finset.sum_nonneg fun i _ => hKc i
  have hKfirst : 0 ≤ Kfirst := by dsimp only [Kfirst]; positivity
  have hKsecond : 0 ≤ Ksecond := by dsimp only [Ksecond]; positivity
  have hK1 : 0 ≤ K1 := add_nonneg hKfirst hKsecond
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro T hTsymm hdelta hdeltaZ hT2
  let delta_lt : delta < 1 := lt_of_le_of_lt hdelta_le (by norm_num)
  let D1 : SmoothCcTensor g 3 2 := ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M)
    g gBase T 0 delta_lt hdelta delta_lt hdeltaZ
  let W : SmoothCcTensor g 0 3 := iteratedCovGrad (I := I) g 0 2 1 T
  let Y : SmoothCcTensor g 0 2 := operatorFieldApply (I := I) (M := M) g 3 2 D1 W
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let P : ℝ := y + y * q + y ^ 2
  have hy : 0 ≤ y := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hzeroHs (sigma : ℝ) :
      ccTensorToHs (I := I) (M := M) g 2 sigma
          (0 : SmoothCcTensor g 0 2) = 0 := by
    have h := ccTensorToHs_smul (I := I) (M := M) g 2 sigma 0 T
    simpa using h
  have hTsum : ∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤ Cj * y := by
    simpa only [Cj, y] using
      covsum_hs_three (I := I) (M := M) g 2 hact2 hact3 T
  have hTlowSq : ∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤ (Cj * y) ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _
      _ ≤ (Cj * y) ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg _) hTsum 2
  have hTtop : ‖iteratedCovGrad (I := I) g 0 2 4 T‖ ^ 2 ≤
      q ^ 2 + Cgap * y ^ 2 := by
    have h := hgap T
    rw [SmoothCcTensor.norm_toL2] at h
    rw [show 3 + 1 = 4 by norm_num,
      show ((3 : ℕ) : ℝ) + 1 = 4 by norm_num,
      show ((3 : ℕ) : ℝ) = 3 by norm_num] at h
    simpa only [Nat.cast_ofNat, norm_ccHs_eq_smoothHs, y, q] using h
  have hTjet5 : ∑ j ∈ Finset.range 5,
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤
        q ^ 2 + Cw * y ^ 2 := by
    rw [Finset.sum_range_succ]
    dsimp only [Cw]
    nlinarith [hTlowSq, hTtop]
  have hWjet : ∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 3 j W‖ ^ 2 ≤
        q ^ 2 + Cw * y ^ 2 := by
    calc
      _ = ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [W, Nat.reduceAdd, Nat.add_comm] using congrArg (fun z : ℝ => z ^ 2)
          (iteratedCovGrad_comp_norm (I := I) (M := M) g 2 1 j T)
      _ ≤ ∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
        exact shifted_four_sq_le
          (fun j => ‖iteratedCovGrad (I := I) g 0 2 j T‖)
      _ ≤ q ^ 2 + Cw * y ^ 2 := hTjet5
  have hWlow : ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 3 j W‖ ^ 2 ≤ (Cj * y) ^ 2 := by
    calc
      _ = ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [W, Nat.reduceAdd, Nat.add_comm] using congrArg (fun z : ℝ => z ^ 2)
          (iteratedCovGrad_comp_norm (I := I) (M := M) g 2 1 j T)
      _ ≤ ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
        exact shifted_three_sq_le
          (fun j => ‖iteratedCovGrad (I := I) g 0 2 j T‖)
      _ ≤ (Cj * y) ^ 2 := hTlowSq
  have hWpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x (W.toSection x) ≤
        (Ct * y) ^ 2 := by
    intro x
    calc
      _ ≤ Cm0 ^ 2 * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 3 j W‖ ^ 2 :=
        hmor0 g hEq (hjet 1 (by norm_num)) (hjet 2 (by norm_num)) W x
      _ ≤ Cm0 ^ 2 * (Cj * y) ^ 2 :=
        mul_le_mul_of_nonneg_left hWlow (sq_nonneg Cm0)
      _ = (Ct * y) ^ 2 := by dsimp only [Ct]; ring
  have hD1low : ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 3 2 j D1‖ ^ 2 ≤
        (B0 1 + B1 1 * y) ^ 2 := by
    have hraw := hcoeff g hEq hjet T 0 hdelta hdeltaZ 1 y
      zero_le_one hy hT2 (by rw [hzeroHs, norm_zero]; exact zero_le_one)
      (le_refl y) (by rw [hzeroHs, norm_zero]; exact hy)
    simpa only [D1, y] using hraw
  have hD1pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 3 2 x (D1.toSection x) ≤
        (A0 + A1 * y) ^ 2 := by
    intro x
    calc
      _ ≤ Cm3 ^ 2 * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 3 2 j D1‖ ^ 2 :=
        hmor3 g hEq (hjet 1 (by norm_num)) (hjet 2 (by norm_num)) D1 x
      _ ≤ Cm3 ^ 2 * (B0 1 + B1 1 * y) ^ 2 :=
        mul_le_mul_of_nonneg_left hD1low (sq_nonneg Cm3)
      _ = (A0 + A1 * y) ^ 2 := by dsimp only [A0, A1]; ring
  have hD1jet : ∑ i ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 3 2 i D1‖ ^ 2 ≤
        Ksum * (1 + q ^ 2 + Cw * y ^ 2) := by
    have hterm : ∀ i ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 3 2 i D1‖ ^ 2 ≤
          Kc i * (1 + q ^ 2 + Cw * y ^ 2) := by
      intro i hiMem
      have hi0 := htow T hTsymm hdelta0 hdelta_le hdelta hdeltaZ i
      have hi : ‖iteratedCovGrad (I := I) g 3 2 i D1‖ ^ 2 ≤
          Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
        simpa only [D1, delta_lt, RicciDeTurckLowOrder.firstOrderCoefficient_eq] using hi0
      refine hi.trans (mul_le_mul_of_nonneg_left ?_ (hKc i))
      have hisub : ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤
            ∑ j ∈ Finset.range 5,
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
        have hi4 := Finset.mem_range.mp hiMem
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega))
        intro j _ _
        exact sq_nonneg _
      linarith [hisub.trans hTjet5]
    calc
      _ ≤ ∑ i ∈ Finset.range 4,
          Kc i * (1 + q ^ 2 + Cw * y ^ 2) := Finset.sum_le_sum hterm
      _ = Ksum * (1 + q ^ 2 + Cw * y ^ 2) := by
        dsimp only [Ksum]
        rw [Finset.sum_mul]
  have hYjetRaw := happ g hEq D1 W (A0 + A1 * y) (Ct * y)
    (add_nonneg hA0 (mul_nonneg hA1 hy)) (mul_nonneg hCt hy)
    hD1pt hWpt
  have hYjet : ∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2 ≤
        K0 * q ^ 2 + K1 * P ^ 2 := by
    have hfirst : Ca * ((Ct * y) ^ 2 *
        (Ksum * (1 + q ^ 2 + Cw * y ^ 2))) ≤ Kfirst * P ^ 2 := by
      simpa only [Kfirst, P] using
        low1_first_poly hCa hKsum hCw hy hq
    have hsecond : Ca * ((A0 + A1 * y) ^ 2 *
        (q ^ 2 + Cw * y ^ 2)) ≤ K0 * q ^ 2 + Ksecond * P ^ 2 := by
      simpa only [K0, Ksecond, P] using
        low1_second_poly hCa hCw hy hq
    change (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2) ≤ _ at hYjetRaw
    refine hYjetRaw.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hD1jet (sq_nonneg (Ct * y))
    have h2 := mul_le_mul_of_nonneg_left hWjet (sq_nonneg (A0 + A1 * y))
    have h12 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCa
    have hbound := add_le_add hfirst hsecond
    calc
      Ca * ((Ct * y) ^ 2 * ∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 3 2 j D1‖ ^ 2 +
          (A0 + A1 * y) ^ 2 * ∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 0 3 j W‖ ^ 2) ≤
          Ca * ((Ct * y) ^ 2 *
              (Ksum * (1 + q ^ 2 + Cw * y ^ 2)) +
            (A0 + A1 * y) ^ 2 * (q ^ 2 + Cw * y ^ 2)) := h12
      _ = Ca * ((Ct * y) ^ 2 *
            (Ksum * (1 + q ^ 2 + Cw * y ^ 2)) +
          (A0 + A1 * y) ^ 2 * (q ^ 2 + Cw * y ^ 2)) := rfl
      _ = Ca * ((Ct * y) ^ 2 *
            (Ksum * (1 + q ^ 2 + Cw * y ^ 2))) +
          Ca * ((A0 + A1 * y) ^ 2 * (q ^ 2 + Cw * y ^ 2)) := by ring
      _ ≤ Kfirst * P ^ 2 + (K0 * q ^ 2 + Ksecond * P ^ 2) := hbound
      _ = K0 * q ^ 2 + K1 * P ^ 2 := by dsimp only [K1]; ring
  have hYroot : ∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤
        2 * (Real.sqrt K0 * q + Real.sqrt K1 * P) := by
    let JY : ℝ := ∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖
    have hJY : 0 ≤ JY := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsq := sq_sum_le_card_mul_sum_sq
      (s := Finset.range 4)
      (f := fun j => ‖iteratedCovGrad (I := I) g 0 2 j Y‖)
    have htarget : JY ^ 2 ≤
        (2 * (Real.sqrt K0 * q + Real.sqrt K1 * P)) ^ 2 := by
      rw [show (2 * (Real.sqrt K0 * q + Real.sqrt K1 * P)) ^ 2 =
        4 * (K0 * q ^ 2 + K1 * P ^ 2 +
          2 * Real.sqrt K0 * Real.sqrt K1 * q * P) by
        nlinarith only [Real.sq_sqrt hK0, Real.sq_sqrt hK1]]
      have hcross : 0 ≤ 2 * Real.sqrt K0 * Real.sqrt K1 * q * P :=
        mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
              (Real.sqrt_nonneg _)) hq) hP
      simpa only [JY, Finset.card_range, Nat.cast_ofNat] using
        hsq.trans (mul_le_mul_of_nonneg_left
          (hYjet.trans (le_add_of_nonneg_right hcross)) (by norm_num))
    have hrhs : 0 ≤ 2 * (Real.sqrt K0 * q + Real.sqrt K1 * P) :=
      mul_nonneg (by norm_num) (add_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) hq)
        (mul_nonneg (Real.sqrt_nonneg _) hP))
    have := (sq_le_sq₀ hJY hrhs).mp htarget
    simpa only [JY] using this
  have hHs := hs_three_le_jet (I := I) (M := M) g hact2 Y
  change ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖ ≤ C * q + D * P
  calc
    _ ≤ Ch * ∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ := by
      refine hHs.trans ?_
      apply mul_le_mul_of_nonneg_right _
        (Finset.sum_nonneg fun j _ => norm_nonneg _)
      dsimp only [Ch]
      rw [hDim]
      norm_num
    _ ≤ Ch * (2 * (Real.sqrt K0 * q + Real.sqrt K1 * P)) :=
      mul_le_mul_of_nonneg_left hYroot hCh
    _ = C * q + D * P := by dsimp only [C, D]; ring

theorem low1_pair_h5_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Lambda : ℝ}
    (hLambda : 1 ≤ Lambda) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta_le : delta ≤ 1 / 3) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ G : ℝ, 0 ≤ G ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Lambda →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Lambda) →
          ∃ F : ℝ, 0 ≤ F ∧
            ∀ (T : SmoothCcTensor g 0 2)
              (hTsymm : ∀ (x : M) (u v : TangentSpace I x),
                ccTensorBilin (I := I) g T x u v =
                  ccTensorBilin (I := I) g T x v u)
              (hdelta : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) delta)
              (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g
                  (0 : SmoothCcTensor g 0 2)) delta),
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ 1 →
              let D1 := ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M)
                g gBase T 0 (lt_of_le_of_lt hdelta_le (by norm_num))
                  hdelta (lt_of_le_of_lt hdelta_le (by norm_num)) hdeltaZ
              let Y := operatorFieldApply (I := I) (M := M) g 3 2 D1
                (iteratedCovGrad (I := I) g 0 2 1 T)
              2 * |tensorL2Inner (I := I) (M := M) g 0 2
                  (oneMinusConnLapSmooth (I := I) g 0 2
                    (oneMinusConnLapSmooth (I := I) g 0 2
                      (oneMinusConnLapSmooth (I := I) g 0 2 T))).toFun
                  (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
                eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
                  G * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                  F *
                    (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
                      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
                        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  intro eta heta
  obtain ⟨C, hC, hpath⟩ := low1_path_h3 (I := I) (M := M)
    hDim gBase hLambda hdelta0 hdelta_le
  let e : ℝ := eta / 2
  let G : ℝ := 2 * eta⁻¹ * C ^ 2
  have he : 0 < e := by dsimp only [e]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  refine ⟨G, hG, ?_⟩
  intro g hEq hjet
  obtain ⟨D, hD, hY⟩ := hpath g hEq hjet
  let F : ℝ := 6 * eta⁻¹ * D ^ 2
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  refine ⟨F, hF, ?_⟩
  intro T hTsymm hdelta hdeltaZ hT2
  let delta_lt : delta < 1 := lt_of_le_of_lt hdelta_le (by norm_num)
  let D1 : SmoothCcTensor g 3 2 := ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M)
    g gBase T 0 delta_lt hdelta delta_lt hdeltaZ
  let Y : SmoothCcTensor g 0 2 := operatorFieldApply (I := I) (M := M) g 3 2 D1
    (iteratedCovGrad (I := I) g 0 2 1 T)
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖
  let P : ℝ := y + y * q + y ^ 2
  have hy : 0 ≤ y := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hYP : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖ ≤
      C * q + D * P := by
    simpa only [D1, Y, y, q, P, delta_lt] using
      hY T hTsymm hdelta hdeltaZ hT2
  have hpair := oneMinusConnLapSmooth_pair_h5_h3
    (I := I) (M := M) g T Y
  have hraw : 2 * |tensorL2Inner (I := I) (M := M) g 0 2
      (oneMinusConnLapSmooth (I := I) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T))).toFun
      (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
        2 * z * (C * q + D * P) := by
    calc
      _ ≤ 2 * (z * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖) :=
        mul_le_mul_of_nonneg_left (by simpa only [z] using hpair) (by norm_num)
      _ ≤ 2 * (z * (C * q + D * P)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hYP hz) (by norm_num)
      _ = 2 * z * (C * q + D * P) := by ring
  have hsplit : 2 * z * (C * q + D * P) =
      2 * z * (C * q) + 2 * z * (D * P) := by ring
  have hY1 := two_mul_le_eps (eta := e) (x := z) (y := C * q) he
  have hY2 := two_mul_le_eps (eta := e) (x := z) (y := D * P) he
  have heinv : e⁻¹ = 2 * eta⁻¹ := by
    dsimp only [e]
    field_simp [ne_of_gt heta]
  have hP2 : P ^ 2 ≤ 3 * (y ^ 2 + y ^ 2 * q ^ 2 + y ^ 4) := by
    dsimp only [P]
    nlinarith [sq_nonneg (y - y * q), sq_nonneg (y - y ^ 2),
      sq_nonneg (y * q - y ^ 2)]
  change 2 * |tensorL2Inner (I := I) (M := M) g 0 2
      (oneMinusConnLapSmooth (I := I) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T))).toFun
      (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
        eta * z ^ 2 + G * q ^ 2 + F * (y ^ 2 + y ^ 2 * q ^ 2 + y ^ 4)
  calc
    _ ≤ 2 * z * (C * q + D * P) := hraw
    _ = 2 * z * (C * q) + 2 * z * (D * P) := hsplit
    _ ≤ (e * z ^ 2 + e⁻¹ * (C * q) ^ 2) +
        (e * z ^ 2 + e⁻¹ * (D * P) ^ 2) := add_le_add hY1 hY2
    _ ≤ eta * z ^ 2 + G * q ^ 2 +
        F * (y ^ 2 + y ^ 2 * q ^ 2 + y ^ 4) := by
      rw [heinv]
      dsimp only [e, G, F]
      have hDP := mul_le_mul_of_nonneg_left hP2 (sq_nonneg D)
      nlinarith [inv_nonneg.mpr heta.le, hDP]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
