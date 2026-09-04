import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.CoefficientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.MetricDifference

section

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_add_le covariantJetNormSq_sum_six_le reindexCoefficientInputSlots_sub)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (ccOperatorFieldComp operatorFieldComposition_sub_left operatorFieldComposition_sub_right ccTensorToHs permCoeff)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

private lemma second_le_three_term_sum
    (D3 D2 A : ℝ) (hD3 : 0 ≤ D3) (hD2 : 0 ≤ D2) (hA : 0 ≤ A) :
    D2 ≤ D3 + D2 + A * D2 := by
  nlinarith only [hD3, mul_nonneg hA hD2]

private lemma two_mul_sq_add_sq_le_four_sum_sq
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (x ^ 2 + y ^ 2) ≤ (2 * (x + y)) ^ 2 := by
  nlinarith only [sq_nonneg x, sq_nonneg y, mul_nonneg hx hy]

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem ricciQuadraticKernelDerivativeCoefficient_sub_eq_six_terms
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) :
    ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gT T -
        ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gU U =
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationCycleZeroThreeOneTwo -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationCycleZeroThreeOneTwo) +
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationSwapBlocks -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationSwapBlocks) +
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationCycleZeroThreeTwo -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationCycleZeroThreeTwo) +
      (ricciQuadraticKernelDerivativeDirectTerm (I := I) (M := M) g gT T ricciQuadraticPermutationCycleZeroOneThreeTwo -
        ricciQuadraticKernelDerivativeDirectTerm (I := I) (M := M) g gU U ricciQuadraticPermutationCycleZeroOneThreeTwo) +
      (ricciQuadraticKernelDerivativeDirectTerm (I := I) (M := M) g gT T ricciQuadraticPermutationCycleZeroOneTwo -
        ricciQuadraticKernelDerivativeDirectTerm (I := I) (M := M) g gU U ricciQuadraticPermutationCycleZeroOneTwo) +
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationSwapZeroTwo -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationSwapZeroTwo) := by
  simp only [ricciQuadraticKernelDerivativeCoefficient]
  module

theorem exists_ricciQuadraticKernelDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gT T -
            ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, houtPair⟩ :=
    connIns_sub_tame (I := I) (M := M) hDim g
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨Bo, hBo, houtBdd⟩ := exists_connectionDifferenceContravariantInsertionField_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρi, Bi, hρi, hBi, hinBdd⟩ :=
    exists_connectionDifferenceInsertionInnerActionCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρp, Bp, hρp, hBp, hinPair⟩ :=
    exists_connectionDifferenceInsertionInnerActionCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cb, hCb, hblk⟩ :=
    exists_ricciQuadraticKernelDerivativeBlock_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cm, hCm, hmid⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 3
  let J : ℝ := ricciQuadraticPermutationJetCap (I := I) (M := M) g
  let P : ℝ := Real.sqrt J
  let Zf : ℝ := 1 + Cm * P
  let Co : ℝ → ℝ := fun R => B0 R + B1 R
  let L : ℝ → ℝ := fun R =>
    Cb * P *
      (Co R * (Zf * Bi * R) + Bo R * Zf * Bp * (1 + R))
  let B : ℝ → ℝ := fun R => 10 * L R
  let ρ : ℝ := min ρi ρp
  have hJ : 0 ≤ J := ricciQuadraticPermutationJetCap_nonneg (I := I) (M := M) g
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hPsq : P ^ 2 = J := by
    simpa only [P] using Real.sq_sqrt hJ
  have hZf : 0 ≤ Zf :=
    add_nonneg (by norm_num) (mul_nonneg hCm hP)
  have hZf1 : 1 ≤ Zf := by
    dsimp only [Zf]
    exact le_add_of_nonneg_right (mul_nonneg hCm hP)
  have hCo : ∀ R : ℝ, 0 ≤ R → 0 ≤ Co R := by
    intro R hR
    exact add_nonneg (hB0 R hR) (hB1 R hR)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    dsimp only [L]
    exact mul_nonneg (mul_nonneg hCb hP)
      (add_nonneg
        (mul_nonneg (hCo R hR)
          (mul_nonneg (mul_nonneg hZf hBi) hR))
        (mul_nonneg
          (mul_nonneg (mul_nonneg (hBo R hR) hZf) hBp)
          (add_nonneg (by norm_num) hR)))
  have hρ : 0 < ρ := lt_min hρi hρp
  refine ⟨ρ, B, hρ,
    fun R hR => mul_nonneg (by norm_num) (hL R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let IT : SmoothCcTensor g 3 3 :=
    connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gT T
  let IU : SmoothCcTensor g 3 3 :=
    connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gU U
  let OD : ℝ := B0 R * D3 + B1 R * D2 + B1 R * A * D2
  let OU : ℝ := Bo R * (1 + A)
  let ZB : ℝ := Zf * (Bi * R)
  let ZD : ℝ := Zf * (Bp * (D2 + R * N))
  let D : ℝ := D3 + D2 + A * D2
  let S : ℝ := (1 + A) * (D + N)
  let Q : ℝ := (L R * S) ^ 2
  have hOD : 0 ≤ OD := by
    dsimp only [OD]
    exact add_nonneg
      (add_nonneg (mul_nonneg (hB0 R hR) hD3)
        (mul_nonneg (hB1 R hR) hD2))
      (mul_nonneg (mul_nonneg (hB1 R hR) hA) hD2)
  have hOU : 0 ≤ OU := by
    dsimp only [OU]
    exact mul_nonneg (hBo R hR) (add_nonneg (by norm_num) hA)
  have hZB : 0 ≤ ZB := by
    dsimp only [ZB]
    exact mul_nonneg hZf (mul_nonneg hBi hR)
  have hZD : 0 ≤ ZD := by
    dsimp only [ZD]
    exact mul_nonneg hZf
      (mul_nonneg hBp (add_nonneg hD2 (mul_nonneg hR hN)))
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact mul_nonneg (add_nonneg (by norm_num) hA)
      (add_nonneg hD hN)
  have hQ : 0 ≤ Q := sq_nonneg _
  have hTni : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρi := hTn.trans (min_le_left _ _)
  have hTnp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρp := hTn.trans (min_le_right _ _)
  have hUnp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρp := hUn.trans (min_le_right _ _)
  have hIT : covariantJetNormSq (I := I) (M := M) g 2 IT ≤ (Bi * R) ^ 2 := by
    simpa only [IT] using
      hinBdd gT T T hT hT hTtie R hR hT2 hTni
  have hIdiff : covariantJetNormSq (I := I) (M := M) g 2 (IT - IU) ≤
      (Bp * (D2 + R * N)) ^ 2 := by
    simpa only [IT, IU] using
      hinPair gT gU T U hT hU hTtie hUtie hTnp hUnp
        R D2 N hR hD2 hN hU2 hTU2 hTUn
  have hoDiff : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceContravariantInsertionField (I := I) g gT -
        connectionDifferenceContravariantInsertionField (I := I) g gU) ≤ OD ^ 2 := by
    simpa only [OD] using
      houtPair gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hoU : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceContravariantInsertionField (I := I) g gU) ≤ OU ^ 2 := by
    simpa only [OU] using
      houtBdd gU U hU hUtie hδ_le hδ0 hδU hδZ
        R A hR hA hU2 hU3
  have hcap4 : ∀ pm : Equiv.Perm (Fin 4),
      (pm = ricciQuadraticPermutationCycleZeroThreeOneTwo ∨ pm = ricciQuadraticPermutationSwapBlocks ∨ pm = ricciQuadraticPermutationCycleZeroThreeTwo ∨
        pm = ricciQuadraticPermutationCycleZeroOneThreeTwo ∨ pm = ricciQuadraticPermutationCycleZeroOneTwo ∨ pm = ricciQuadraticPermutationSwapZeroTwo) →
      covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) ≤ P ^ 2 := by
    intro pm hpm
    simpa only [hPsq, J] using covariantJetNormSq_ricciQuadraticPermutation_four_le (I := I) (M := M) g pm hpm
  have hcap3 : ∀ pm : Equiv.Perm (Fin 3),
      (pm = ricciQuadraticPermutationSwapZeroOne ∨ pm = ricciQuadraticPermutationRotateInputs) →
      covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) ≤ P ^ 2 := by
    intro pm hpm
    simpa only [hPsq, J] using covariantJetNormSq_ricciQuadraticPermutation_three_le (I := I) (M := M) g pm hpm
  have hmidB : ∀ pm : Equiv.Perm (Fin 3),
      (pm = ricciQuadraticPermutationSwapZeroOne ∨ pm = ricciQuadraticPermutationRotateInputs) →
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
            (permCoeff (I := I) (M := M) g pm) IT) ≤ ZB ^ 2 := by
    intro pm hpm
    have hraw := hmid
      (permCoeff (I := I) (M := M) g pm) IT
      P (Bi * R) hP (mul_nonneg hBi hR) (hcap3 pm hpm) hIT
    refine hraw.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg hCm hP) (mul_nonneg hBi hR)) ?_ 2)
    dsimp only [ZB, Zf]
    rw [show (1 + Cm * P) * (Bi * R) =
        Cm * P * (Bi * R) + 1 * (Bi * R) by ring]
    exact le_add_of_nonneg_right
      (mul_nonneg (by norm_num) (mul_nonneg hBi hR))
  have hmidD : ∀ pm : Equiv.Perm (Fin 3),
      (pm = ricciQuadraticPermutationSwapZeroOne ∨ pm = ricciQuadraticPermutationRotateInputs) →
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
              (permCoeff (I := I) (M := M) g pm) IT -
            ccOperatorFieldComp (I := I) (M := M) g 3 3 3
              (permCoeff (I := I) (M := M) g pm) IU) ≤ ZD ^ 2 := by
    intro pm hpm
    rw [← operatorFieldComposition_sub_right]
    have hraw := hmid
      (permCoeff (I := I) (M := M) g pm) (IT - IU)
      P (Bp * (D2 + R * N)) hP
      (mul_nonneg hBp (add_nonneg hD2 (mul_nonneg hR hN)))
      (hcap3 pm hpm) hIdiff
    refine hraw.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg hCm hP)
        (mul_nonneg hBp (add_nonneg hD2 (mul_nonneg hR hN)))) ?_ 2)
    dsimp only [ZD, Zf]
    rw [show (1 + Cm * P) * (Bp * (D2 + R * N)) =
        Cm * P * (Bp * (D2 + R * N)) +
          1 * (Bp * (D2 + R * N)) by ring]
    exact le_add_of_nonneg_right
      (mul_nonneg (by norm_num)
        (mul_nonneg hBp (add_nonneg hD2 (mul_nonneg hR hN))))
  have hbareB : covariantJetNormSq (I := I) (M := M) g 2 IT ≤ ZB ^ 2 := by
    refine hIT.trans (pow_le_pow_left₀ (mul_nonneg hBi hR) ?_ 2)
    dsimp only [ZB]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hZf1 (mul_nonneg hBi hR)
  have hbareD : covariantJetNormSq (I := I) (M := M) g 2 (IT - IU) ≤ ZD ^ 2 := by
    refine hIdiff.trans (pow_le_pow_left₀
      (mul_nonneg hBp (add_nonneg hD2 (mul_nonneg hR hN))) ?_ 2)
    dsimp only [ZD]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hZf1
        (mul_nonneg hBp (add_nonneg hD2 (mul_nonneg hR hN)))
  have hD2D : D2 ≤ D := by
    dsimp only [D]
    exact second_le_three_term_sum D3 D2 A hD3 hD2 hA
  have hDS : D ≤ S := by
    have hDN : D ≤ D + N := le_add_of_nonneg_right hN
    have hmul : D + N ≤ (1 + A) * (D + N) := by
      have h1A : 1 ≤ 1 + A := le_add_of_nonneg_right hA
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right h1A (add_nonneg hD hN)
    exact hDN.trans hmul
  have hDR : D2 + R * N ≤ (1 + R) * (D + N) := by
    have hNsum : N ≤ D + N := le_add_of_nonneg_left hD
    calc
      D2 + R * N ≤ D + R * (D + N) :=
        add_le_add hD2D (mul_le_mul_of_nonneg_left hNsum hR)
      _ ≤ (D + N) + R * (D + N) :=
        add_le_add (le_add_of_nonneg_right hN) le_rfl
      _ = (1 + R) * (D + N) := by ring
  have hODle : OD ≤ Co R * D := by
    have hgap : Co R * D = OD +
        (B0 R * D2 + B0 R * A * D2 + B1 R * D3) := by
      simp only [Co, D, OD]
      ring
    rw [hgap]
    exact le_add_of_nonneg_right
      (add_nonneg
        (add_nonneg (mul_nonneg (hB0 R hR) hD2)
          (mul_nonneg (mul_nonneg (hB0 R hR) hA) hD2))
        (mul_nonneg (hB1 R hR) hD3))
  have hlead : Cb * P * (OD * ZB + OU * ZD) ≤ L R * S := by
    let c1 : ℝ := Co R * (Zf * Bi * R)
    let c2 : ℝ := Bo R * Zf * Bp * (1 + R)
    have hc1 : 0 ≤ c1 := by
      dsimp only [c1]
      exact mul_nonneg (hCo R hR)
        (mul_nonneg (mul_nonneg hZf hBi) hR)
    have hc2 : 0 ≤ c2 := by
      dsimp only [c2]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (hBo R hR) hZf) hBp)
        (add_nonneg (by norm_num) hR)
    have hfirst : OD * ZB ≤ c1 * S := by
      calc
        OD * ZB ≤ (Co R * D) * ZB :=
          mul_le_mul_of_nonneg_right hODle hZB
        _ = c1 * D := by simp only [c1, ZB]; ring
        _ ≤ c1 * S := mul_le_mul_of_nonneg_left hDS hc1
    have hsecond : OU * ZD ≤ c2 * S := by
      have hbase : 0 ≤ Bo R * Zf * Bp * (1 + A) :=
        mul_nonneg
          (mul_nonneg (mul_nonneg (hBo R hR) hZf) hBp)
          (add_nonneg (by norm_num) hA)
      calc
        OU * ZD =
            (Bo R * Zf * Bp * (1 + A)) * (D2 + R * N) := by
          simp only [OU, ZD]
          ring
        _ ≤ (Bo R * Zf * Bp * (1 + A)) *
            ((1 + R) * (D + N)) :=
          mul_le_mul_of_nonneg_left hDR hbase
        _ = c2 * S := by simp only [c2, S]; ring
    calc
      Cb * P * (OD * ZB + OU * ZD) ≤
          Cb * P * (c1 * S + c2 * S) :=
        mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
          (mul_nonneg hCb hP)
      _ = L R * S := by simp only [L, c1, c2]; ring
  have hblkFin : ∀ (pm : Equiv.Perm (Fin 4))
      (hpm : pm = ricciQuadraticPermutationCycleZeroThreeOneTwo ∨ pm = ricciQuadraticPermutationSwapBlocks ∨
        pm = ricciQuadraticPermutationCycleZeroThreeTwo ∨ pm = ricciQuadraticPermutationCycleZeroOneThreeTwo ∨
        pm = ricciQuadraticPermutationCycleZeroOneTwo ∨ pm = ricciQuadraticPermutationSwapZeroTwo)
      (ZT ZU : SmoothCcTensor g 3 3),
      covariantJetNormSq (I := I) (M := M) g 2 ZT ≤ ZB ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2 (ZT - ZU) ≤ ZD ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticKernelDerivativeBlock (I := I) (M := M) g gT pm ZT -
            ricciQuadraticKernelDerivativeBlock (I := I) (M := M) g gU pm ZU) ≤ Q := by
    intro pm hpm ZT ZU hZT hZD'
    have hraw := hblk gT gU pm ZT ZU P OD OU ZB ZD
      hP hOD hOU hZB hZD (hcap4 pm hpm) hoDiff hoU hZT hZD'
    exact hraw.trans
      (pow_le_pow_left₀
        (mul_nonneg (mul_nonneg hCb hP)
          (add_nonneg (mul_nonneg hOD hZB) (mul_nonneg hOU hZD)))
        hlead 2)
  have hx0 : covariantJetNormSq (I := I) (M := M) g 2
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationCycleZeroThreeOneTwo -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationCycleZeroThreeOneTwo) ≤ Q := by
    simpa only [ricciQuadraticKernelDerivativeNestedTerm, ricciQuadraticKernelDerivativeBlock, IT, IU] using
      hblkFin ricciQuadraticPermutationCycleZeroThreeOneTwo (Or.inl rfl) _ _
        (hmidB ricciQuadraticPermutationSwapZeroOne (Or.inl rfl))
        (hmidD ricciQuadraticPermutationSwapZeroOne (Or.inl rfl))
  have hx1 : covariantJetNormSq (I := I) (M := M) g 2
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationSwapBlocks -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationSwapBlocks) ≤ Q := by
    simpa only [ricciQuadraticKernelDerivativeNestedTerm, ricciQuadraticKernelDerivativeBlock, IT, IU] using
      hblkFin ricciQuadraticPermutationSwapBlocks (Or.inr (Or.inl rfl)) _ _
        (hmidB ricciQuadraticPermutationSwapZeroOne (Or.inl rfl))
        (hmidD ricciQuadraticPermutationSwapZeroOne (Or.inl rfl))
  have hx2 : covariantJetNormSq (I := I) (M := M) g 2
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationCycleZeroThreeTwo -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationCycleZeroThreeTwo) ≤ Q := by
    simpa only [ricciQuadraticKernelDerivativeNestedTerm, ricciQuadraticKernelDerivativeBlock, IT, IU] using
      hblkFin ricciQuadraticPermutationCycleZeroThreeTwo (Or.inr (Or.inr (Or.inl rfl))) _ _
        (hmidB ricciQuadraticPermutationRotateInputs (Or.inr rfl))
        (hmidD ricciQuadraticPermutationRotateInputs (Or.inr rfl))
  have hx3 : covariantJetNormSq (I := I) (M := M) g 2
      (ricciQuadraticKernelDerivativeDirectTerm (I := I) (M := M) g gT T ricciQuadraticPermutationCycleZeroOneThreeTwo -
        ricciQuadraticKernelDerivativeDirectTerm (I := I) (M := M) g gU U ricciQuadraticPermutationCycleZeroOneThreeTwo) ≤ Q := by
    simpa only [ricciQuadraticKernelDerivativeDirectTerm, ricciQuadraticKernelDerivativeBlock, IT, IU] using
      hblkFin ricciQuadraticPermutationCycleZeroOneThreeTwo
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) IT IU hbareB hbareD
  have hx4 : covariantJetNormSq (I := I) (M := M) g 2
      (ricciQuadraticKernelDerivativeDirectTerm (I := I) (M := M) g gT T ricciQuadraticPermutationCycleZeroOneTwo -
        ricciQuadraticKernelDerivativeDirectTerm (I := I) (M := M) g gU U ricciQuadraticPermutationCycleZeroOneTwo) ≤ Q := by
    simpa only [ricciQuadraticKernelDerivativeDirectTerm, ricciQuadraticKernelDerivativeBlock, IT, IU] using
      hblkFin ricciQuadraticPermutationCycleZeroOneTwo
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        IT IU hbareB hbareD
  have hx5 : covariantJetNormSq (I := I) (M := M) g 2
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationSwapZeroTwo -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationSwapZeroTwo) ≤ Q := by
    simpa only [ricciQuadraticKernelDerivativeNestedTerm, ricciQuadraticKernelDerivativeBlock, IT, IU] using
      hblkFin ricciQuadraticPermutationSwapZeroTwo
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _ _
        (hmidB ricciQuadraticPermutationRotateInputs (Or.inr rfl))
        (hmidD ricciQuadraticPermutationRotateInputs (Or.inr rfl))
  rw [ricciQuadraticKernelDerivativeCoefficient_sub_eq_six_terms (I := I) (M := M) g gT gU T U]
  refine (covariantJetNormSq_sum_six_le (I := I) (M := M) g 2 _ _ _ _ _ _
    hx0 hx1 hx2 hx3 hx4 hx5).trans ?_
  calc
    94 * Q ≤ 100 * Q := mul_le_mul_of_nonneg_right (by norm_num) hQ
    _ = (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num]
      change 10 ^ 2 * (L R * S) ^ 2 = _
      rw [← mul_pow]
      apply congrArg (fun x : ℝ => x ^ 2)
      simp only [B, S, D]
      ring

theorem exists_ricciCometricFourTraceCastG0_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gT -
              ricciCometricFourTraceCastG0 (I := I) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C0, hρ, hC0, hlip⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  let L : ℝ := 22 * C0 ^ 2
  let C : ℝ := Real.sqrt L
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (sq_nonneg C0)
  refine ⟨ρ, C, hρ, Real.sqrt_nonneg _, ?_⟩
  intro T U gT gU hTtie hUtie hTn hUn
  have hF : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
        cometricDoubleTraceCoefficient (I := I) (M := M) g gU) ≤
      (C0 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (T - U)‖) ^ 2 := by
    rw [cometricDoubleTraceCoefficient_eq_pureTrace, cometricDoubleTraceCoefficient_eq_pureTrace]
    exact hlip T U gT gU hTtie hUtie hTn hUn
  have heq :
      ricciCometricFourTraceCastG0 (I := I) g gT -
          ricciCometricFourTraceCastG0 (I := I) g gU =
        ((1 : ℝ) / 2) •
          (reindexCoefficientInputSlots (I := I) (M := M) g 4 2
                (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                  cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
                fourTraceArgPerm0231 +
            reindexCoefficientInputSlots (I := I) (M := M) g 4 2
                (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                  cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
                fourTraceArgPerm0321 -
            (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
              cometricDoubleTraceCoefficient (I := I) (M := M) g gU) -
            reindexCoefficientInputSlots (I := I) (M := M) g 4 2
                (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                  cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
                fourTraceArgPerm2301) := by
    rw [ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g gT,
      ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g gU,
      reindexCoefficientInputSlots_sub, reindexCoefficientInputSlots_sub, reindexCoefficientInputSlots_sub]
    module
  rw [heq]
  refine (covariantJetNormSq_ricciFourTraceCombination_le (I := I) (M := M) g _).trans ?_
  calc
    22 * covariantJetNormSq (I := I) (M := M) g 2
        (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
          cometricDoubleTraceCoefficient (I := I) (M := M) g gU) ≤
      22 * (C0 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (T - U)‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hF (by norm_num)
    _ = (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (T - U)‖) ^ 2 := by
      simp only [C, mul_pow]
      rw [Real.sq_sqrt hL]
      simp only [L]
      ring

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
private theorem ricciConnectionDifferenceQuadraticDerivativeCoefficient_sub_eq_two_terms
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) :
    ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gT T -
        ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gU U =
      ccOperatorFieldComp (I := I) (M := M) g 3 4 2
          (ricciCometricFourTraceCastG0 (I := I) g gT -
            ricciCometricFourTraceCastG0 (I := I) g gU)
          (ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gT T) +
        ccOperatorFieldComp (I := I) (M := M) g 3 4 2
          (ricciCometricFourTraceCastG0 (I := I) g gU)
          (ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gT T -
            ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gU U) := by
  simp only [ricciConnectionDifferenceQuadraticDerivativeCoefficient, operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
  module

theorem exists_ricciConnectionDifferenceQuadraticDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gT T -
            ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρkp, Bp, hρkp, hBp, hkerPair⟩ :=
    exists_ricciQuadraticKernelDerivativeCoefficient_pairing_secondOrder_bound
      (I := I) (M := M) hDim g
  obtain ⟨ρkb, Bk, hρkb, hBk, hkerBdd⟩ :=
    exists_ricciQuadraticKernelDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρtp, Ct, hρtp, hCt, htracePair⟩ :=
    exists_ricciCometricFourTraceCastG0_pairing_secondOrder_bound
      (I := I) (M := M) hDim g
  obtain ⟨ρtb, Bt, hρtb, hBt, htraceBdd⟩ :=
    exists_ricciCometricFourTraceCastG0_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 2
  let ρ : ℝ := min ρkp (min ρkb (min ρtp ρtb))
  let B : ℝ → ℝ := fun R =>
    2 * Ca * (Ct * Bk R + Bt * Bp R)
  have hρ : 0 < ρ := lt_min hρkp (lt_min hρkb (lt_min hρtp hρtb))
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hCa)
      (add_nonneg (mul_nonneg hCt (hBk R hR))
        (mul_nonneg hBt (hBp R hR)))
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let FT : SmoothCcTensor g 4 2 :=
    ricciCometricFourTraceCastG0 (I := I) g gT
  let FU : SmoothCcTensor g 4 2 :=
    ricciCometricFourTraceCastG0 (I := I) g gU
  let KT : SmoothCcTensor g 3 4 := ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gT T
  let KU : SmoothCcTensor g 3 4 := ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gU U
  let D : ℝ := D3 + D2 + A * D2 + N
  let x : ℝ := Ca * (Ct * N) * (Bk R * (1 + A))
  let y : ℝ := Ca * Bt * (Bp R * (1 + A) * D)
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact add_nonneg
      (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg (mul_nonneg hCa (mul_nonneg hCt hN))
      (mul_nonneg (hBk R hR) (add_nonneg (by norm_num) hA))
  have hy0 : 0 ≤ y := by
    dsimp only [y]
    exact mul_nonneg (mul_nonneg hCa hBt)
      (mul_nonneg
        (mul_nonneg (hBp R hR) (add_nonneg (by norm_num) hA)) hD)
  have hTkp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρkp := hTn.trans (min_le_left _ _)
  have hUkp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρkp := hUn.trans (min_le_left _ _)
  have hTkb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρkb :=
    hTn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hTtp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρtp :=
    hTn.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hUtp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρtp :=
    hUn.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hUtb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρtb :=
    hUn.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hFdiff : covariantJetNormSq (I := I) (M := M) g 2 (FT - FU) ≤
      (Ct * N) ^ 2 := by
    have hraw := htracePair T U gT gU hTtie hUtie hTtp hUtp
    exact hraw.trans
      (pow_le_pow_left₀ (mul_nonneg hCt (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hTUn hCt) 2)
  have hFU : covariantJetNormSq (I := I) (M := M) g 2 FU ≤ Bt ^ 2 := by
    simpa only [FU] using htraceBdd U gU hUtie hUtb
  have hKT : covariantJetNormSq (I := I) (M := M) g 2 KT ≤
      (Bk R * (1 + A)) ^ 2 := by
    simpa only [KT] using
      hkerBdd gT T T hT hT hTtie hδ_le hδ0 hδT hδZ
        R A hR hA hT2 hT3 hT2 hTkb
  have hKdiff : covariantJetNormSq (I := I) (M := M) g 2 (KT - KU) ≤
      (Bp R * (1 + A) * D) ^ 2 := by
    simpa only [KT, KU, D] using
      hkerPair gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδU hδZ hTkp hUkp
        R A D2 D3 N hR hA hD2 hD3 hN
        hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let X : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 (FT - FU) KT
  let Y : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 FU (KT - KU)
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ x ^ 2 := by
    simpa only [X, x] using
      happ (FT - FU) KT (Ct * N) (Bk R * (1 + A))
        (mul_nonneg hCt hN)
        (mul_nonneg (hBk R hR) (add_nonneg (by norm_num) hA))
        hFdiff hKT
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ y ^ 2 := by
    simpa only [Y, y] using
      happ FU (KT - KU) Bt (Bp R * (1 + A) * D)
        hBt
        (mul_nonneg
          (mul_nonneg (hBp R hR) (add_nonneg (by norm_num) hA)) hD)
        hFU hKdiff
  have hNle : N ≤ D := by
    dsimp only [D]
    exact le_add_of_nonneg_left
      (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2))
  have hlead : 2 * (x + y) ≤ B R * (1 + A) * D := by
    let c : ℝ := Ca * Ct * Bk R * (1 + A)
    have hc : 0 ≤ c := by
      dsimp only [c]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hCa hCt) (hBk R hR))
        (add_nonneg (by norm_num) hA)
    have hx : x ≤ c * D := by
      calc
        x = c * N := by simp only [x, c]; ring
        _ ≤ c * D := mul_le_mul_of_nonneg_left hNle hc
    calc
      2 * (x + y) ≤ 2 * (c * D + y) :=
        mul_le_mul_of_nonneg_left (add_le_add hx le_rfl) (by norm_num)
      _ = B R * (1 + A) * D := by simp only [B, c, y]; ring
  rw [ricciConnectionDifferenceQuadraticDerivativeCoefficient_sub_eq_two_terms (I := I) (M := M) g gT gU T U]
  change covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
    (B R * (1 + A) * D) ^ 2
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
        covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
      2 * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ (2 * (x + y)) ^ 2 :=
      two_mul_sq_add_sq_le_four_sum_sq x y hx0 hy0
    _ ≤ (B R * (1 + A) * D) ^ 2 :=
      pow_le_pow_left₀
        (mul_nonneg (by norm_num) (add_nonneg hx0 hy0)) hlead 2

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end
end

section

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_add_le covariantJetNormSq_nonneg covariantJetNormSq_smul
  covariantJetNormSq_sub_le)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply operatorFieldApplication_sub_left ccOperatorFieldComp operatorFieldComposition_sub_left operatorFieldComposition_sub_right
    operatorFieldComposition_zero_eq_operatorFieldApply ccOperatorFieldComp metricComparisonEndomorphismField operatorFieldApply)
open DifferentialGeometry.Geometry.Connection (slotInsertEndoCc)

private lemma two_mul_sum_sq_le_square_two_mul_sum
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (x ^ 2 + y ^ 2) ≤ (2 * (x + y)) ^ 2 := by
  nlinarith only [sq_nonneg x, sq_nonneg y, mul_nonneg hx hy]

private lemma one_add_square_le_square_one_add (x : ℝ) (hx : 0 ≤ x) :
    1 + x ^ 2 ≤ (1 + x) ^ 2 := by
  nlinarith only [hx]

private lemma two_mul_sum_le_four_sq
    (x y z : ℝ) (hx : x ≤ z ^ 2) (hy : y ≤ z ^ 2) :
    2 * (x + y) ≤ 4 * z ^ 2 := by
  linarith only [hx, hy]

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

theorem exists_ricciConnectionDifferenceDerivativeMetricWeight_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (R D2 : ℝ), 0 ≤ R → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gT T -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gU U) ≤
        (B R * D2) ^ 2 := by
  obtain ⟨Be, hBe, hslotB⟩ :=
    RicciDeTurckLowOrder.exists_metricComparisonEndomorphism_slot_one_covariantJetNormSq_two_bound (I := I) (M := M) g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bed, hBed, hslotD⟩ :=
    exists_slotInsertEndoCc_metricComparisonEndomorphismField_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨C, hC, happ⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 0 2 2
  let B : ℝ → ℝ := fun R => 2 * C * (Bed R * R + Be R)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hC)
      (add_nonneg (mul_nonneg (hBed R hR) hR) (hBe R hR))
  refine ⟨B, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
    R D2 hR hD2 hT2 hU2 hTU2
  let ET : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gT)
  let EU : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gU)
  let X : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 (ET - EU) T
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 EU (T - U)
  let x : ℝ := C * (Bed R * D2) * R
  let y : ℝ := C * Be R * D2
  have hx0 : 0 ≤ x :=
    mul_nonneg (mul_nonneg hC (mul_nonneg (hBed R hR) hD2)) hR
  have hy0 : 0 ≤ y :=
    mul_nonneg (mul_nonneg hC (hBe R hR)) hD2
  have hEU :
      covariantJetNormSq (I := I) (M := M) g 2 EU ≤ (Be R) ^ 2 := by
    simpa only [EU] using
      hslotB gU U hU hUtie hδ_le hδ0 hδU R hR hU2
  have hEdiff :
      covariantJetNormSq (I := I) (M := M) g 2 (ET - EU) ≤
        (Bed R * D2) ^ 2 := by
    simpa only [ET, EU] using
      hslotD gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R D2 hR hD2 hT2 hU2 hTU2
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ x ^ 2 := by
    simpa only [X, x, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ (ET - EU) T (Bed R * D2) R
        (mul_nonneg (hBed R hR) hD2) hR hEdiff hT2
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ y ^ 2 := by
    simpa only [Y, y, operatorFieldComposition_zero_eq_operatorFieldApply] using
      happ EU (T - U) (Be R) D2
        (hBe R hR) hD2 hEU hTU2
  have happSub (Φ : SmoothCcTensor g 2 2)
      (V W : SmoothCcTensor g 0 2) :
      operatorFieldApply (I := I) (M := M) g 2 2 Φ (V - W) =
        operatorFieldApply (I := I) (M := M) g 2 2 Φ V -
          operatorFieldApply (I := I) (M := M) g 2 2 Φ W := by
    calc
      operatorFieldApply (I := I) (M := M) g 2 2 Φ (V - W) =
          ccOperatorFieldComp (I := I) (M := M) g 0 2 2 Φ (V - W) :=
        (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g 2 2 Φ (V - W)).symm
      _ = ccOperatorFieldComp (I := I) (M := M) g 0 2 2 Φ V -
          ccOperatorFieldComp (I := I) (M := M) g 0 2 2 Φ W :=
        operatorFieldComposition_sub_right (I := I) (M := M) g 0 2 2 Φ V W
      _ = operatorFieldApply (I := I) (M := M) g 2 2 Φ V -
          operatorFieldApply (I := I) (M := M) g 2 2 Φ W :=
        congrArg₂ (fun A B : SmoothCcTensor g 0 2 => A - B)
          (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g 2 2 Φ V)
          (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g 2 2 Φ W)
  have hsplit :
      RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gT T -
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gU U =
        X + Y := by
    simp only [RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight, X, Y, ET, EU]
    rw [operatorFieldApplication_sub_left, happSub]
    module
  rw [hsplit]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
        covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
      2 * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ (2 * (x + y)) ^ 2 :=
      two_mul_sum_sq_le_square_two_mul_sum x y hx0 hy0
    _ = (B R * D2) ^ 2 := by
      simp only [B, x, y]
      ring

theorem exists_ricciConnectionDifferenceDerivativeTransposedCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (R D2 : ℝ), 0 ≤ R → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gT T -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gU U) ≤
        (B R * D2) ^ 2 := by
  obtain ⟨Bw, hBw, hweight⟩ :=
    exists_ricciConnectionDifferenceDerivativeMetricWeight_pairing_secondOrder_bound
      (I := I) (M := M) hDim g
  obtain ⟨Cm, hCm, hmono⟩ :=
    curv_pair_h2 (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 2 * Cm * Bw R
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hCm) (hBw R hR)
  refine ⟨B, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
    R D2 hR hD2 hT2 hU2 hTU2
  let WT : SmoothCcTensor g 0 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gT T
  let WU : SmoothCcTensor g 0 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gU U
  let z : ℝ := Cm * (Bw R * D2)
  have hz0 : 0 ≤ z :=
    mul_nonneg hCm (mul_nonneg (hBw R hR) hD2)
  have hWdiff :
      covariantJetNormSq (I := I) (M := M) g 2 (WT - WU) ≤
        (Bw R * D2) ^ 2 := by
    simpa only [WT, WU] using
      hweight gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU
        R D2 hR hD2 hT2 hU2 hTU2
  have hMono (σ : Equiv.Perm (Fin 4)) :
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gT T σ -
            RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gU U σ) ≤
        z ^ 2 := by
    simpa only [RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial, WT, WU, z] using
      hmono WT WU σ (Bw R * D2)
        (mul_nonneg (hBw R hR) hD2) hWdiff
  let XA : SmoothCcTensor g 4 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M)
        g gT T RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation -
      RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M)
        g gU U RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation
  let XB : SmoothCcTensor g 4 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M)
        g gT T RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap -
      RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M)
        g gU U RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap
  have hXA : covariantJetNormSq (I := I) (M := M) g 2 XA ≤ z ^ 2 := by
    simpa only [XA] using hMono RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation
  have hXB : covariantJetNormSq (I := I) (M := M) g 2 XB ≤ z ^ 2 := by
    simpa only [XB] using hMono RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap
  have hsplit :
      RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gT T -
          RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gU U =
        XA - XB := by
    simp only [RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient, XA, XB]
    module
  rw [hsplit]
  refine (covariantJetNormSq_sub_le (I := I) (M := M) g 2 XA XB).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2 XA +
        covariantJetNormSq (I := I) (M := M) g 2 XB) ≤
      4 * z ^ 2 := two_mul_sum_le_four_sq _ _ _ hXA hXB
    _ = (B R * D2) ^ 2 := by
      simp only [B, z]
      ring

theorem exists_ricciConnectionDerivativeTransposedCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gT T -
            RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨Bt, hBt, htransD⟩ :=
    exists_ricciConnectionDifferenceDerivativeTransposedCoefficient_pairing_secondOrder_bound
      (I := I) (M := M) hDim g
  obtain ⟨Kd, hKd, hdagB⟩ :=
    exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_two_radiusFree_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bd, hBd, hdagD⟩ :=
    exists_ricciConnectionDerivativeCoefficient_covariantJetNormSq_tame_difference_bound
      (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 2
  let C0 : SmoothCcTensor g 4 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g g
      (0 : SmoothCcTensor g 0 2)
  let J0 : ℝ := covariantJetNormSq (I := I) (M := M) g 2 C0
  let S0 : ℝ := Real.sqrt J0
  let Sd : ℝ := Real.sqrt Kd
  let Tu : ℝ → ℝ := fun R => 2 * (Bt R * R + S0)
  let B : ℝ → ℝ := fun R =>
    2 * Ca * (Bt R * Sd + Tu R * Bd R)
  have hJ0 : 0 ≤ J0 :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g C0
  have hS0 : 0 ≤ S0 := Real.sqrt_nonneg _
  have hS0sq : S0 ^ 2 = J0 := by
    simpa only [S0] using Real.sq_sqrt hJ0
  have hSd : 0 ≤ Sd := Real.sqrt_nonneg _
  have hSdsq : Sd ^ 2 = Kd := by
    simpa only [Sd] using Real.sq_sqrt hKd
  have hTu : ∀ R : ℝ, 0 ≤ R → 0 ≤ Tu R := by
    intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (hBt R hR) hR) hS0)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hCa)
      (add_nonneg (mul_nonneg (hBt R hR) hSd)
        (mul_nonneg (hTu R hR) (hBd R hR)))
  refine ⟨B, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  let CT : SmoothCcTensor g 4 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gT T
  let CU : SmoothCcTensor g 4 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gU U
  let DT : SmoothCcTensor g 3 4 :=
    RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gT
  let DU : SmoothCcTensor g 3 4 :=
    RicciDeTurckLowOrder.ricciConnectionDerivativeCoefficient (I := I) (M := M) g gU
  let Q : ℝ := D3 + D2 + A * D2
  have hQ : 0 ≤ Q :=
    add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)
  have h1A : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hCTU :
      covariantJetNormSq (I := I) (M := M) g 2 (CT - CU) ≤
        (Bt R * D2) ^ 2 := by
    simpa only [CT, CU] using
      htransD gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU
        R D2 hR hD2 hT2 hU2 hTU2
  have hzeroSymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero, ccTensorBilin_zero]
  have hzeroTie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero,
      ccTensorBilin_zero]
    ring
  have h02 :
      covariantJetNormSq (I := I) (M := M) g 2
          (0 : SmoothCcTensor g 0 2) ≤ (0 : ℝ) ^ 2 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • T by simp, covariantJetNormSq_smul]
    norm_num
  have hU0 :
      covariantJetNormSq (I := I) (M := M) g 2
          (U - (0 : SmoothCcTensor g 0 2)) ≤ R ^ 2 := by
    simpa only [sub_zero] using hU2
  have h02R :
      covariantJetNormSq (I := I) (M := M) g 2
          (0 : SmoothCcTensor g 0 2) ≤ R ^ 2 := by
    exact h02.trans (by norm_num; exact sq_nonneg R)
  have hCU0 :
      covariantJetNormSq (I := I) (M := M) g 2 (CU - C0) ≤
        (Bt R * R) ^ 2 := by
    simpa only [CU, C0] using
      htransD gU g U (0 : SmoothCcTensor g 0 2)
        hU hzeroSymm hUtie hzeroTie hδ_le hδ0 hδU hδZ
        R R hR hR hU2 h02R hU0
  have hCU :
      covariantJetNormSq (I := I) (M := M) g 2 CU ≤ (Tu R) ^ 2 := by
    rw [show CU = (CU - C0) + C0 by module]
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 (CU - C0) C0).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2 (CU - C0) +
          covariantJetNormSq (I := I) (M := M) g 2 C0) ≤
        2 * ((Bt R * R) ^ 2 + S0 ^ 2) := by
          rw [hS0sq]
          exact mul_le_mul_of_nonneg_left (add_le_add hCU0 le_rfl)
            (by norm_num)
      _ ≤ (2 * (Bt R * R + S0)) ^ 2 := by
        nlinarith [mul_nonneg (hBt R hR) hR,
          sq_nonneg (Bt R * R), sq_nonneg S0]
      _ = (Tu R) ^ 2 := by rfl
  have hDT0 :
      covariantJetNormSq (I := I) (M := M) g 2 DT ≤
        Kd * (1 + A ^ 2) := by
    refine (hdagB gT T hT hTtie hδ_le hδ0 hδT).trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hT3) hKd
  have hDT :
      covariantJetNormSq (I := I) (M := M) g 2 DT ≤
        (Sd * (1 + A)) ^ 2 := by
    refine hDT0.trans ?_
    rw [mul_pow, hSdsq]
    exact mul_le_mul_of_nonneg_left
      (one_add_square_le_square_one_add A hA) hKd
  have hDD :
      covariantJetNormSq (I := I) (M := M) g 2 (DT - DU) ≤
        (Bd R * Q) ^ 2 := by
    simpa only [DT, DU, Q] using
      hdagD gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 D3 hR hA hD2 hD3
        hT2 hU2 hT3 hU3 hTU2 hTU3
  let X : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 (CT - CU) DT
  let Y : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 CU (DT - DU)
  let x : ℝ := Ca * (Bt R * D2) * (Sd * (1 + A))
  let y : ℝ := Ca * Tu R * (Bd R * Q)
  have hx0 : 0 ≤ x :=
    mul_nonneg (mul_nonneg hCa (mul_nonneg (hBt R hR) hD2))
      (mul_nonneg hSd h1A)
  have hy0 : 0 ≤ y :=
    mul_nonneg (mul_nonneg hCa (hTu R hR))
      (mul_nonneg (hBd R hR) hQ)
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ x ^ 2 := by
    simpa only [X, x] using
      happ (CT - CU) DT (Bt R * D2) (Sd * (1 + A))
        (mul_nonneg (hBt R hR) hD2) (mul_nonneg hSd h1A) hCTU hDT
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ y ^ 2 := by
    simpa only [Y, y] using
      happ CU (DT - DU) (Tu R) (Bd R * Q)
        (hTu R hR) (mul_nonneg (hBd R hR) hQ) hCU hDD
  have hsplit :
      RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gT T -
          RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gU U =
        X + Y := by
    simp only [RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient, CT, CU, DT, DU, X, Y]
    rw [operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  have hD2Q : D2 ≤ Q := by
    dsimp only [Q]
    exact (le_add_of_nonneg_left hD3).trans
      (le_add_of_nonneg_right (mul_nonneg hA hD2))
  have hxle :
      x ≤ Ca * (Bt R * Sd) * (1 + A) * Q := by
    calc
      x = Ca * (Bt R * Sd) * (1 + A) * D2 := by
        simp only [x]
        ring
      _ ≤ Ca * (Bt R * Sd) * (1 + A) * Q :=
        mul_le_mul_of_nonneg_left hD2Q
          (mul_nonneg
            (mul_nonneg hCa (mul_nonneg (hBt R hR) hSd)) h1A)
  have hyle :
      y ≤ Ca * (Tu R * Bd R) * (1 + A) * Q := by
    let c : ℝ := Ca * (Tu R * Bd R)
    have hc : 0 ≤ c :=
      mul_nonneg hCa (mul_nonneg (hTu R hR) (hBd R hR))
    calc
      y = (c * 1) * Q := by simp only [y, c]; ring
      _ ≤ (c * (1 + A)) * Q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hA) hc) hQ
      _ = Ca * (Tu R * Bd R) * (1 + A) * Q := by
        simp only [c]
  have hlin :
      2 * (x + y) ≤ B R * (1 + A) * Q := by
    calc
      2 * (x + y) ≤
          2 * (Ca * (Bt R * Sd) * (1 + A) * Q +
            Ca * (Tu R * Bd R) * (1 + A) * Q) :=
        mul_le_mul_of_nonneg_left (add_le_add hxle hyle) (by norm_num)
      _ = B R * (1 + A) * Q := by
        simp only [B]
        ring
  rw [hsplit]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
        covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
      2 * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ (2 * (x + y)) ^ 2 :=
      two_mul_sum_sq_le_square_two_mul_sum x y hx0 hy0
    _ ≤ (B R * (1 + A) * Q) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by norm_num) (add_nonneg hx0 hy0)) hlin 2

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end
end

section

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq covariantJetNormSq_add_le)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (ccTensorToHs ccTensor02Symm_eq_self)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

theorem exists_ricciConnectionDifferenceDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gT T -
            ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρ, Ba, hρ, hBa, haa⟩ :=
    exists_ricciConnectionDifferenceQuadraticDerivativeCoefficient_pairing_secondOrder_bound
      (I := I) (M := M) hDim g
  obtain ⟨Bd, hBd, hda⟩ :=
    exists_ricciConnectionDerivativeTransposedCoefficient_pairing_secondOrder_bound
      (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 2 * (Ba R + Bd R)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (by norm_num) (add_nonneg (hBa R hR) (hBd R hR))
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let Q : ℝ := D3 + D2 + A * D2
  let D : ℝ := Q + N
  let x : ℝ := Ba R * (1 + A) * D
  let y : ℝ := Bd R * (1 + A) * D
  have hQ : 0 ≤ Q :=
    add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)
  have hD : 0 ≤ D := add_nonneg hQ hN
  have hQD : Q ≤ D := le_add_of_nonneg_right hN
  have h1A : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hx0 : 0 ≤ x := mul_nonneg (mul_nonneg (hBa R hR) h1A) hD
  have hy0 : 0 ≤ y := mul_nonneg (mul_nonneg (hBd R hR) h1A) hD
  have hsymmT : ccTensor02Symm (I := I) (M := M) g T = T :=
    ccTensor02Symm_eq_self (I := I) (M := M) g T hT
  have hsymmU : ccTensor02Symm (I := I) (M := M) g U = U :=
    ccTensor02Symm_eq_self (I := I) (M := M) g U hU
  have haa' : covariantJetNormSq (I := I) (M := M) g 2
      (ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gT T -
        ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gU U) ≤ x ^ 2 := by
    simpa only [x, D, Q, add_assoc] using
      haa gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
        hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
        hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hda0 := hda gT gU T U hT hU hTtie hUtie
    hδ_le hδ0 hδT hδU hδZ R A D2 D3
    hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  have hscale : 0 ≤ Bd R * (1 + A) := mul_nonneg (hBd R hR) h1A
  have hda' : covariantJetNormSq (I := I) (M := M) g 2
      (RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gT T -
        RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gU U) ≤ y ^ 2 := by
    refine hda0.trans ?_
    exact pow_le_pow_left₀ (mul_nonneg hscale hQ)
      (mul_le_mul_of_nonneg_left hQD hscale) 2
  have hsplit :
      ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gT T -
          ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gU U =
        (ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gT T -
          ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gU U) +
        (RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gT T -
          RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gU U) := by
    simp only [ricciConnectionDifferenceDerivativeCoefficient, hsymmT, hsymmU]
    module
  rw [hsplit]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gT T -
            ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gU U) +
        covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gT T -
            RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gU U)) ≤
      2 * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add haa' hda') (by norm_num)
    _ ≤ (2 * (x + y)) ^ 2 := by
      nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg hx0 hy0]
    _ = (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
      simp only [B, x, y, D, Q]
      ring

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end
end

section

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_nonneg covariantJetNormSq_smul covariantJetNormSq_sum_four_le)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral (ccTensorToHs ccTensorToHs_smul)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

theorem exists_lowOrderFirstDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s -
            affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g U hδU hδZ s) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρr, Br, hρr, hBr, hric⟩ :=
    exists_ricciConnectionDifferenceDerivativeCoefficient_pairing_secondOrder_bound
      (I := I) (M := M) hDim g
  obtain ⟨ρv, Bv, hρv, hBv, hvb⟩ :=
    exists_lieCorrectionZeroVectorBundleDerivativeCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρa, Ba, hρa, hBa, hamix⟩ :=
    exists_lieCorrectionZeroMixedConnectionDerivativeCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρq, Bq, hρq, hBq, hquad⟩ :=
    exists_lieCorrectionQuadraticFirstDerivativeCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  let ρ : ℝ := min (min ρr ρv) (min ρa ρq)
  let C : ℝ → ℝ := fun R => 2 * Br R + Bv R + Ba R + Bq R
  let B : ℝ → ℝ := fun R => 8 * C R
  have hρ : 0 < ρ := lt_min (lt_min hρr hρv) (lt_min hρa hρq)
  have hC : ∀ R : ℝ, 0 ≤ R → 0 ≤ C R := by
    intro R hR
    exact add_nonneg
      (add_nonneg (add_nonneg (mul_nonneg (by norm_num) (hBr R hR))
        (hBv R hR)) (hBa R hR)) (hBq R hR)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (by norm_num) (hC R hR)
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ hTn hUn
    R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s
  let gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s
  let P : SmoothCcTensor g 0 2 := s • T
  let Q : SmoothCcTensor g 0 2 := s • U
  let D : ℝ := D3 + D2 + A * D2 + N
  let X : ℝ := C R * (1 + A) * D
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [Q, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [gmT, P, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [gmU, Q, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [P, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [Q, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    simp only [P, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    simp only [Q, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    simp only [P, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    simp only [Q, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 := by
    rw [show P - Q = s • (T - U) by simp only [P, Q, smul_sub], covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g (T - U)) hs2).trans hTU2
  have hPQ3 : covariantJetNormSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    rw [show P - Q = s • (T - U) by simp only [P, Q, smul_sub], covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
    simp only [P, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTn)
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ := by
    simp only [Q, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hUn)
  have hPQn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    rw [show P - Q = s • (T - U) by simp only [P, Q, smul_sub],
      ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTUn)
  have hr : covariantJetNormSq (I := I) (M := M) g 2
      (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gmT P -
        ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gmU Q) ≤
      (Br R * (1 + A) * D) ^ 2 := by
    simpa only [D] using
      hric gmT gmU P Q hPsymm hQsymm hPtie hQtie
        hδ_le hδ0 hδP hδQ hδZ
        (hPn.trans ((min_le_left _ _).trans (min_le_left _ _)))
        (hQn.trans ((min_le_left _ _).trans (min_le_left _ _)))
        R A D2 D3 N hR hA hD2 hD3 hN
        hP2 hQ2 hP3 hQ3 hPQ2 hPQ3 hPQn
  have hv : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gmT P -
        lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gmU Q) ≤
      (Bv R * (1 + A) * D) ^ 2 := by
    simpa only [D] using
      hvb gmT gmU P Q hPsymm hQsymm hPtie hQtie
        hδ_le hδ0 hδP hδQ hδZ
        (hPn.trans ((min_le_left _ _).trans (min_le_right _ _)))
        (hQn.trans ((min_le_left _ _).trans (min_le_right _ _)))
        R A D2 D3 N hR hA hD2 hD3 hN
        hP2 hQ2 hP3 hQ3 hPQ2 hPQ3 hPQn
  have ha : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gmT g P -
        lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gmU g Q) ≤
      (Ba R * (1 + A) * D) ^ 2 := by
    simpa only [D] using
      hamix gmT gmU P Q hPsymm hQsymm hPtie hQtie
        hδ_le hδ0 hδP hδQ hδZ
        (hPn.trans ((min_le_right _ _).trans (min_le_left _ _)))
        (hQn.trans ((min_le_right _ _).trans (min_le_left _ _)))
        R A D2 D3 N hR hA hD2 hD3 hN
        hP2 hQ2 hP3 hQ3 hPQ2 hPQ3 hPQn
  have hq : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gmT P -
        lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gmU Q) ≤
      (Bq R * (1 + A) * D) ^ 2 := by
    simpa only [D] using
      hquad gmT gmU P Q hPsymm hQsymm hPtie hQtie
        hδ_le hδ0 hδP hδQ hδZ
        (hPn.trans ((min_le_right _ _).trans (min_le_right _ _)))
        (hQn.trans ((min_le_right _ _).trans (min_le_right _ _)))
        R A D2 D3 N hR hA hD2 hD3 hN
        hP2 hQ2 hP3 hQ3 hPQ2 hPQ3 hPQn
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hfac : 0 ≤ (1 + A) * D := mul_nonneg honeA hD
  have hcr : 2 * Br R ≤ C R := by
    simp only [C]
    linarith [hBv R hR, hBa R hR, hBq R hR]
  have hcv : Bv R ≤ C R := by
    simp only [C]
    linarith [hBr R hR, hBa R hR, hBq R hR]
  have hca : Ba R ≤ C R := by
    simp only [C]
    linarith [hBr R hR, hBv R hR, hBq R hR]
  have hcq : Bq R ≤ C R := by
    simp only [C]
    linarith [hBr R hR, hBv R hR, hBa R hR]
  have hcrX : 2 * Br R * (1 + A) * D ≤ X := by
    have h := mul_le_mul_of_nonneg_right hcr hfac
    simpa only [X, mul_assoc] using h
  have hcvX : Bv R * (1 + A) * D ≤ X := by
    have h := mul_le_mul_of_nonneg_right hcv hfac
    simpa only [X, mul_assoc] using h
  have hcaX : Ba R * (1 + A) * D ≤ X := by
    have h := mul_le_mul_of_nonneg_right hca hfac
    simpa only [X, mul_assoc] using h
  have hcqX : Bq R * (1 + A) * D ≤ X := by
    have h := mul_le_mul_of_nonneg_right hcq hfac
    simpa only [X, mul_assoc] using h
  let XR : SmoothCcTensor g 3 2 := (-2 : ℝ) •
    (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gmT P -
      ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gmU Q)
  let XV : SmoothCcTensor g 3 2 :=
    lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gmT P -
      lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gmU Q
  let XA : SmoothCcTensor g 3 2 :=
    lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gmT g P -
      lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gmU g Q
  let XQ : SmoothCcTensor g 3 2 :=
    lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gmT P -
      lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gmU Q
  have hXR : covariantJetNormSq (I := I) (M := M) g 2 XR ≤ X ^ 2 := by
    simp only [XR, covariantJetNormSq_smul]
    norm_num
    calc
      4 * covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gmT P -
            ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gmU Q) ≤
        4 * (Br R * (1 + A) * D) ^ 2 :=
          mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = (2 * Br R * (1 + A) * D) ^ 2 := by ring
      _ ≤ X ^ 2 := pow_le_pow_left₀
        (mul_nonneg (mul_nonneg
          (mul_nonneg (by norm_num) (hBr R hR)) honeA) hD) hcrX 2
  have hXV : covariantJetNormSq (I := I) (M := M) g 2 XV ≤ X ^ 2 := by
    exact hv.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (hBv R hR) honeA) hD) hcvX 2)
  have hXA : covariantJetNormSq (I := I) (M := M) g 2 XA ≤ X ^ 2 := by
    exact ha.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (hBa R hR) honeA) hD) hcaX 2)
  have hXQ : covariantJetNormSq (I := I) (M := M) g 2 XQ ≤ X ^ 2 := by
    exact hq.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (hBq R hR) honeA) hD) hcqX 2)
  have hsplit :
      affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s -
          affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g U hδU hδZ s =
        XR + XV + XA + XQ := by
    simp only [affineLowOrderFirstDerivativeCoefficientPath, lowOrderFirstDerivativeCoefficientPath, gmT, gmU, P, Q, XR, XV, XA, XQ,
      ricciConnectionDifferenceDerivativeCoefficient_smul, lieCorrectionZeroVectorBundleDerivativeCoefficient_smul, lieCorrectionZeroMixedConnectionDerivativeCoefficient_smul, lieCorrectionQuadraticFirstDerivativeCoefficient_smul]
    module
  rw [hsplit]
  have hsum := covariantJetNormSq_sum_four_le (I := I) (M := M) g XR XV XA XQ X
    hXR hXV hXA hXQ
  simpa only [B, X, mul_assoc] using hsum

theorem exists_lowOrderFirstDerivativePathIntegral_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (lowOrderFirstDerivativePathIntegral (I := I) (M := M) g T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ -
            lowOrderFirstDerivativePathIntegral (I := I) (M := M) g U
              (lt_of_le_of_lt hδ_le (by norm_num)) hδU hδZ) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hpoint⟩ :=
    exists_lowOrderFirstDerivativeCoefficient_pairing_secondOrder_bound
      (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ hTn hUn
    R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  let Φ : ℝ → SmoothCcTensor g 3 2 := fun s =>
    affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s -
      affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g U hδU hδZ s
  let D : ℝ := D3 + D2 + A * D2 + N
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjoint : JointlySmoothCcTensorFamily (I := I) g 3 2 S Φ := by
    dsimp only [S, Φ]
    exact jointlySmoothCcTensorFamily_sub (I := I) (M := M) g
      (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδT hδZ)
      (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g U hδU hδZ)
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have hBtot : 0 ≤ B R * (1 + A) * D :=
    mul_nonneg (mul_nonneg (hB R hR) (add_nonneg (by norm_num) hA)) hD
  have hpath := path_jetL2_le (I := I) (M := M) g 3 2 2
    Φ S metricPerturbationPathDomain_isOpen hSI hjoint
    (fun s hs => by
      simpa only [Φ, D, covariantJetNormSq, Nat.reduceAdd] using
        hpoint T U hT hU hδ_le hδ0 hδT hδU hδZ hTn hUn
          R A D2 D3 N hR hA hD2 hD3 hN
          hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn hs)
  rw [lowOrderFirstDerivativePathIntegral_sub (I := I) (M := M)
    g T U hδ_lt hδT hδU hδZ]
  simpa only [lowOrderFirstDerivativePathIntegralDifference, Φ, S, D, covariantJetNormSq, Nat.reduceAdd] using hpath

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end
end

section

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Sobolev
  (covariantJetNormSq iteratedCovGrad iteratedCovGrad_succ iteratedCovGrad_zero)
open DifferentialGeometry.Analysis.Spectral (operatorFieldApply ccTensorToHs)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

theorem exists_lowOrderFirstDerivativePathIntegral_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (lowOrderFirstDerivativePathIntegral (I := I) (M := M) g T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hpoint⟩ :=
    exists_affineLowOrderFirstDerivativeCoefficientPath_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g 3 2 2
    (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI
    (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδT hδZ)
    (B := B R * (1 + A))
    (fun s hs => by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using
        hpoint T hT hδ_le hδ0 hδT hδZ
          R A hR hA hT2 hT3 hTn hs)
  simpa only [lowOrderFirstDerivativePathIntegral, covariantJetNormSq, Nat.reduceAdd] using hpath

omit [SigmaCompactSpace M] in
theorem lowerScalePathIntegral_apply_decomposition
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδ hδZ) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (lowOrderZeroCoefficientPathIntegral (I := I) (M := M) g T hδ_lt hδ hδZ) T +
        operatorFieldApply (I := I) (M := M) g 3 2
          (lowOrderFirstDerivativeCoefficientPathIntegral (I := I) (M := M) g T hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T) := by
  classical
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  let Ψ : ℝ → SmoothCcTensor g 2 2 :=
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M) g g T hδ hδZ
  let L : ℝ → SmoothCcTensor g 2 2 :=
    lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ
  let Q : ℝ → SmoothCcTensor g 3 2 :=
    lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjΨ : JointlySmoothCcTensorFamily (I := I) g 2 2 S Ψ := by
    change linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 2 Ψ
      (δ := δ) (δ' := δ)
    simpa only [S, Ψ] using
      RicciDeTurckLowOrder.selfLow_joint (I := I) (M := M)
        g g T hδ hδZ
  have hjL : JointlySmoothCcTensorFamily (I := I) g 2 2 S L := by
    simpa only [S, L] using
      lowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hjQ : JointlySmoothCcTensorFamily (I := I) g 3 2 S Q := by
    simpa only [S, Q] using
      lowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hcΨ : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((Ψ s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 Ψ S hjΨ x
  have hcL : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((L s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 L S hjL x
  have hcQ : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((Q s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2 Q S hjQ x
  have hPiΨ :
      RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 Ψ
          S metricPerturbationPathDomain_isOpen hSI hjΨ := rfl
  have hPiL :
      lowOrderZeroCoefficientPathIntegral (I := I) (M := M) g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 L
          S metricPerturbationPathDomain_isOpen hSI hjL := rfl
  have hPiQ :
      lowOrderFirstDerivativeCoefficientPathIntegral (I := I) (M := M) g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 3 2 Q
          S metricPerturbationPathDomain_isOpen hSI hjQ := rfl
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [hPiΨ, hPiL, hPiQ]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 Ψ T S
      metricPerturbationPathDomain_isOpen hSI hjΨ hcΨ x v]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add
    (I := I) (M := M) g, add_apply]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 L T S
      metricPerturbationPathDomain_isOpen hSI hjL hcL x v]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 3 2 Q
      (iteratedCovGrad (I := I) g 0 2 1 T) S
      metricPerturbationPathDomain_isOpen hSI hjQ hcQ x v]
  have hIL := coeffApp_integrable (I := I) (M := M)
    g 2 2 L T S hSI hcL x v
  have hIQ := coeffApp_integrable (I := I) (M := M)
    g 3 2 Q (iteratedCovGrad (I := I) g 0 2 1 T)
    S hSI hcQ x v
  rw [← intervalIntegral.integral_add hIL hIQ]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hone := lowerScalePathIntegrand_apply_decomposition (I := I) (M := M)
    g T hT hδ_lt hδ hδZ hs
  change
    unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
            g g T hδ hδZ s) T) x v =
      unitModel (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ s) T) x v +
        unitModel (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 3 2
            (lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 1 T)) x v
  rw [hone, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add
    (I := I) (M := M) g, add_apply, iteratedCovGrad_succ, iteratedCovGrad_zero]

omit [SigmaCompactSpace M] in
theorem lowerScalePathIntegral_apply_affine_decomposition
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδ hδZ) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M)
            g T hT hδ_lt hδ hδZ) T +
        operatorFieldApply (I := I) (M := M) g 3 2
          (lowOrderFirstDerivativePathIntegral (I := I) (M := M)
            g T hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T) := by
  classical
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  let Ψ : ℝ → SmoothCcTensor g 2 2 :=
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M) g g T hδ hδZ
  let L : ℝ → SmoothCcTensor g 2 2 :=
    affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ
  let Q : ℝ → SmoothCcTensor g 3 2 :=
    affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjΨ : JointlySmoothCcTensorFamily (I := I) g 2 2 S Ψ := by
    change linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 2 Ψ
      (δ := δ) (δ' := δ)
    simpa only [S, Ψ] using
      RicciDeTurckLowOrder.selfLow_joint (I := I) (M := M)
        g g T hδ hδZ
  have hjL : JointlySmoothCcTensorFamily (I := I) g 2 2 S L := by
    simpa only [S, L] using
      affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hT hδ hδZ
  have hjQ : JointlySmoothCcTensorFamily (I := I) g 3 2 S Q := by
    simpa only [S, Q] using
      affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hcΨ : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((Ψ s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 Ψ S hjΨ x
  have hcL : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((L s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 L S hjL x
  have hcQ : ∀ x : M, ContinuousOn (fun s : ℝ =>
      TensorRSSpace.toModel ((Q s).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2 Q S hjQ x
  have hPiΨ :
      RicciDeTurckLowOrder.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 Ψ
          S metricPerturbationPathDomain_isOpen hSI hjΨ := rfl
  have hPiL :
      affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M)
          g T hT hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 L
          S metricPerturbationPathDomain_isOpen hSI hjL := rfl
  have hPiQ :
      lowOrderFirstDerivativePathIntegral (I := I) (M := M) g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 3 2 Q
          S metricPerturbationPathDomain_isOpen hSI hjQ := rfl
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [hPiΨ, hPiL, hPiQ]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 Ψ T S
      metricPerturbationPathDomain_isOpen hSI hjΨ hcΨ x v]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add
    (I := I) (M := M) g, add_apply]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 L T S
      metricPerturbationPathDomain_isOpen hSI hjL hcL x v]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 3 2 Q
      (iteratedCovGrad (I := I) g 0 2 1 T) S
      metricPerturbationPathDomain_isOpen hSI hjQ hcQ x v]
  have hIL := coeffApp_integrable (I := I) (M := M)
    g 2 2 L T S hSI hcL x v
  have hIQ := coeffApp_integrable (I := I) (M := M)
    g 3 2 Q (iteratedCovGrad (I := I) g 0 2 1 T)
    S hSI hcQ x v
  rw [← intervalIntegral.integral_add hIL hIQ]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hone := lowerScalePathIntegrand_apply_affine_decomposition (I := I) (M := M)
    g T hT hδ_lt hδ hδZ hs
  change
    unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
            g g T hδ hδZ s) T) x v =
      unitModel (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 2 2
            (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ s) T) x v +
        unitModel (I := I) (M := M) g 2
          (operatorFieldApply (I := I) (M := M) g 3 2
            (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 1 T)) x v
  rw [hone, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add
    (I := I) (M := M) g, add_apply, iteratedCovGrad_succ, iteratedCovGrad_zero]

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end
end
