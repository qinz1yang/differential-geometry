import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.AppCcLpProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1L6
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound

/-!
# Mixed H1-H2 product estimate for operator fields

On a closed three-manifold, an operator coefficient controlled by its first
intrinsic `L2` jet acts from spectral `H2` to spectral `H1`.  The only genuinely
mixed product is the Leibniz arm `slotExtend Φ · ∇U`; it is estimated by
`H1 → L6`, finite-volume `L6 → L3`, and `L6 × L3 → L2`.
-/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology BigOperators ENNReal
open MeasureTheory
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
      [T2Space M] [SigmaCompactSpace M]

private theorem h1_norm_sq_jet
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    ‖(⟨S⟩ : SmoothCcTensorH1 g r s)‖ ^ 2 =
      ‖S‖ ^ 2 + ‖covGrad (I := I) (M := M) g r s S‖ ^ 2 := by
  rw [SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M),
    tensorH1Inner_def,
    ← SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M) S,
    ← tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g r s S S,
    ← SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M)
      (covGrad (I := I) (M := M) g r s S)]

/-- In dimension three, a mixed coefficient with an intrinsic `L2` jet
through order one acts from spectral `H2` to spectral `H1`. -/
theorem appCc_h1_h2_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (U : SmoothCcTensor g 0 r) (A : ℝ),
        0 ≤ A →
        (∑ j ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ)
            (appCc (I := I) (M := M) g r c Φ U)‖ ≤
          C * A *
            ‖ccTensorToHs (I := I) (M := M) g r (2 : ℝ) U‖ := by
  classical
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) g c 1
  obtain ⟨Cin, hCin, hin⟩ := hsJet_le (I := I) (M := M) g r 2
  obtain ⟨Cpt, hCpt, hpt⟩ := hs2_fiber_sq (I := I) (M := M) hDim g r
  obtain ⟨CΦ, hCΦ, hΦ6⟩ := h1_lp6_fiber_rs (I := I) (M := M) hDim g r c
  obtain ⟨CG, hCG, hG6⟩ := h1_lp6_fiber_rs (I := I) (M := M) hDim g 0 (r + 1)
  obtain ⟨CV, hCV, h63⟩ := fiberLp3_le_lp6 (I := I) (M := M) g 0 (r + 1)
  let sd : ℝ := Real.sqrt (Module.finrank ℝ E)
  let Ks : ℝ := sd * CΦ * CV * CG * Cin
  let K : ℝ := Cpt + (Cpt + Ks)
  refine ⟨Csp * K, by
    dsimp [K, Ks, sd]
    positivity, ?_⟩
  intro Φ U A hA hΦjet
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g r (2 : ℝ) U‖
  let G : SmoothCcTensor g 0 (r + 1) :=
    covGrad (I := I) (M := M) g 0 r U
  let Y : SmoothCcTensor g 0 c :=
    appCc (I := I) (M := M) g r c Φ U
  have hN : 0 ≤ N := norm_nonneg _
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
  have hJ :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 r j U‖ ≤ Cin * N := by
    simpa only [N] using hin U
  have hUsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 r x
          (U.toSection x) ≤ (Cpt * N) ^ 2 := by
    intro x
    simpa only [N, mul_pow] using hpt U x
  have hGH1sum :
      ‖(G : SmoothCcTensor g 0 (r + 1))‖ +
          ‖covGrad (I := I) (M := M) g 0 (r + 1) G‖ ≤
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 r j U‖ := by
    dsimp [G]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero]
    linarith [norm_nonneg U]
  have hGH1raw :
      ‖(⟨G⟩ : SmoothCcTensorH1 g 0 (r + 1))‖ ≤
        ‖G‖ + ‖covGrad (I := I) (M := M) g 0 (r + 1) G‖ := by
    have hsq : ‖(⟨G⟩ : SmoothCcTensorH1 g 0 (r + 1))‖ ^ 2 =
        ‖G‖ ^ 2 +
          ‖covGrad (I := I) (M := M) g 0 (r + 1) G‖ ^ 2 :=
      h1_norm_sq_jet (I := I) (M := M) g 0 (r + 1) G
    have hprod : 0 ≤ ‖G‖ *
        ‖covGrad (I := I) (M := M) g 0 (r + 1) G‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [norm_nonneg (⟨G⟩ : SmoothCcTensorH1 g 0 (r + 1)),
      norm_nonneg G,
      norm_nonneg (covGrad (I := I) (M := M) g 0 (r + 1) G)]
  have hGH1 :
      ‖(⟨G⟩ : SmoothCcTensorH1 g 0 (r + 1))‖ ≤ Cin * N :=
    hGH1raw.trans (hGH1sum.trans hJ)
  have hΦ6' :
      lpNorm (fiberLpFun g r c Φ) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ CΦ * A := by
    calc
      _ ≤ CΦ * ‖(⟨Φ⟩ : SmoothCcTensorH1 g r c)‖ := by
        simpa only [fiberLpFun] using hΦ6 (⟨Φ⟩ : SmoothCcTensorH1 g r c)
      _ ≤ CΦ * A := mul_le_mul_of_nonneg_left hΦH1 hCΦ
  have hG6' :
      lpNorm (fiberLpFun g 0 (r + 1) G) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        CG * (Cin * N) := by
    calc
      _ ≤ CG * ‖(⟨G⟩ : SmoothCcTensorH1 g 0 (r + 1))‖ := by
        simpa only [fiberLpFun] using
          hG6 (⟨G⟩ : SmoothCcTensorH1 g 0 (r + 1))
      _ ≤ CG * (Cin * N) := mul_le_mul_of_nonneg_left hGH1 hCG
  have hG3' :
      lpNorm (fiberLpFun g 0 (r + 1) G) 3
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        CV * (CG * (Cin * N)) := by
    exact (h63 G).trans (mul_le_mul_of_nonneg_left hG6' hCV)
  have hslot6 :
      lpNorm (fiberLpFun g (r + 1) (c + 1)
          (slotExtend (I := I) (M := M) g r c Φ)) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        sd * (CΦ * A) := by
    rw [fiberLp_slotExtend (I := I) (M := M) g r c Φ 6]
    exact mul_le_mul_of_nonneg_left hΦ6' (Real.sqrt_nonneg _)
  have hY0 : ‖Y‖ ≤ Cpt * A * N := by
    have h0 := appCc_l2_right
      (I := I) (M := M) g r c Φ U
      (Cpt * N) (mul_nonneg hCpt hN) hUsup
    dsimp [Y]
    calc
      _ ≤ ‖Φ‖ * (Cpt * N) := h0
      _ ≤ A * (Cpt * N) :=
        mul_le_mul_of_nonneg_right hΦ0 (mul_nonneg hCpt hN)
      _ = Cpt * A * N := by ring
  have hcross :
      ‖appCc (I := I) (M := M) g r (c + 1)
          (covGrad (I := I) (M := M) g r c Φ) U‖ ≤ Cpt * A * N := by
    have hc := appCc_l2_right
      (I := I) (M := M) g r (c + 1)
      (covGrad (I := I) (M := M) g r c Φ) U
      (Cpt * N) (mul_nonneg hCpt hN) hUsup
    calc
      _ ≤ ‖covGrad (I := I) (M := M) g r c Φ‖ * (Cpt * N) := hc
      _ ≤ A * (Cpt * N) :=
        mul_le_mul_of_nonneg_right hΦ1 (mul_nonneg hCpt hN)
      _ = Cpt * A * N := by ring
  have hslot :
      ‖appCc (I := I) (M := M) g (r + 1) (c + 1)
          (slotExtend (I := I) (M := M) g r c Φ) G‖ ≤ Ks * A * N := by
    have hp := appCc_l6_l3_l2 (I := I) (M := M) g (r + 1) (c + 1)
      (slotExtend (I := I) (M := M) g r c Φ) G
    calc
      _ ≤
          lpNorm (fiberLpFun g (r + 1) (c + 1)
              (slotExtend (I := I) (M := M) g r c Φ)) 6
              (riemannianVolumeMeasure (I := I) (M := M) g) *
            lpNorm (fiberLpFun g 0 (r + 1) G) 3
              (riemannianVolumeMeasure (I := I) (M := M) g) := hp
      _ ≤ (sd * (CΦ * A)) * (CV * (CG * (Cin * N))) :=
        mul_le_mul hslot6 hG3'
          (show 0 ≤ lpNorm (fiberLpFun g 0 (r + 1) G) 3
            (riemannianVolumeMeasure (I := I) (M := M) g) from lpNorm_nonneg)
          (mul_nonneg (Real.sqrt_nonneg _)
            (mul_nonneg hCΦ hA))
      _ = Ks * A * N := by dsimp [Ks, sd]; ring
  have hY1 :
      ‖covGrad (I := I) (M := M) g 0 c Y‖ ≤
        (Cpt + Ks) * A * N := by
    rw [show covGrad (I := I) (M := M) g 0 c Y =
        appCc (I := I) (M := M) g r (c + 1)
            (covGrad (I := I) (M := M) g r c Φ) U +
          appCc (I := I) (M := M) g (r + 1) (c + 1)
            (slotExtend (I := I) (M := M) g r c Φ) G by
      dsimp [Y, G]
      exact covGrad_appCc_eq (I := I) (M := M) g r c Φ U]
    calc
      _ ≤
          ‖appCc (I := I) (M := M) g r (c + 1)
              (covGrad (I := I) (M := M) g r c Φ) U‖ +
            ‖appCc (I := I) (M := M) g (r + 1) (c + 1)
              (slotExtend (I := I) (M := M) g r c Φ) G‖ := norm_add_le _ _
      _ ≤ Cpt * A * N + Ks * A * N := add_le_add hcross hslot
      _ = (Cpt + Ks) * A * N := by ring
  have hspec :
      ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) Y‖ ≤
        Csp * (‖Y‖ + ‖covGrad (I := I) (M := M) g 0 c Y‖) := by
    rw [← show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num]
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ] using hsp Y
  change ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) Y‖ ≤ _
  calc
    _ ≤ Csp * (‖Y‖ + ‖covGrad (I := I) (M := M) g 0 c Y‖) := hspec
    _ ≤ Csp * (K * A * N) :=
      mul_le_mul_of_nonneg_left (by
        calc
          ‖Y‖ + ‖covGrad (I := I) (M := M) g 0 c Y‖
              ≤ Cpt * A * N + (Cpt + Ks) * A * N := add_le_add hY0 hY1
          _ = K * A * N := by dsimp [K]; ring) hCsp
    _ = (Csp * K) * A * N := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
