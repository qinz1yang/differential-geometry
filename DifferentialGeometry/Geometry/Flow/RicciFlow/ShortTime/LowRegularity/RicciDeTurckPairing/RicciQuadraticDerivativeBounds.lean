import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.ConnectionDifferenceDerivativeBounds

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_add_le covariantJetNormSq_sum_six_le reindexCoeffGen_sub)
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
private theorem ricciQuadraticKernelDerivativeCoefficient_sub_eq_six_terms
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) :
    ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gT T -
        ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gU U =
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_cycleZeroThreeOneTwo -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_cycleZeroThreeOneTwo) +
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_swapBlocks -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_swapBlocks) +
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_cycleZeroThreeTwo -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_cycleZeroThreeTwo) +
      (ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gT T ricciQuadraticPermutation_cycleZeroOneThreeTwo -
        ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gU U ricciQuadraticPermutation_cycleZeroOneThreeTwo) +
      (ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gT T ricciQuadraticPermutation_cycleZeroOneTwo -
        ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gU U ricciQuadraticPermutation_cycleZeroOneTwo) +
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_swapZeroTwo -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_swapZeroTwo) := by
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
      (pm = ricciQuadraticPermutation_cycleZeroThreeOneTwo ∨ pm = ricciQuadraticPermutation_swapBlocks ∨ pm = ricciQuadraticPermutation_cycleZeroThreeTwo ∨
        pm = ricciQuadraticPermutation_cycleZeroOneThreeTwo ∨ pm = ricciQuadraticPermutation_cycleZeroOneTwo ∨ pm = ricciQuadraticPermutation_swapZeroTwo) →
      covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) ≤ P ^ 2 := by
    intro pm hpm
    simpa only [hPsq, J] using covariantJetNormSq_ricciQuadraticPermutation_four_le (I := I) (M := M) g pm hpm
  have hcap3 : ∀ pm : Equiv.Perm (Fin 3),
      (pm = ricciQuadraticPermutation_swapZeroOne ∨ pm = ricciQuadraticPermutation_rotateInputs) →
      covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) ≤ P ^ 2 := by
    intro pm hpm
    simpa only [hPsq, J] using covariantJetNormSq_ricciQuadraticPermutation_three_le (I := I) (M := M) g pm hpm
  have hmidB : ∀ pm : Equiv.Perm (Fin 3),
      (pm = ricciQuadraticPermutation_swapZeroOne ∨ pm = ricciQuadraticPermutation_rotateInputs) →
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
      (pm = ricciQuadraticPermutation_swapZeroOne ∨ pm = ricciQuadraticPermutation_rotateInputs) →
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
      (hpm : pm = ricciQuadraticPermutation_cycleZeroThreeOneTwo ∨ pm = ricciQuadraticPermutation_swapBlocks ∨
        pm = ricciQuadraticPermutation_cycleZeroThreeTwo ∨ pm = ricciQuadraticPermutation_cycleZeroOneThreeTwo ∨
        pm = ricciQuadraticPermutation_cycleZeroOneTwo ∨ pm = ricciQuadraticPermutation_swapZeroTwo)
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
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_cycleZeroThreeOneTwo -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_cycleZeroThreeOneTwo) ≤ Q := by
    simpa only [ricciQuadraticKernelDerivativeNestedTerm, ricciQuadraticKernelDerivativeBlock, IT, IU] using
      hblkFin ricciQuadraticPermutation_cycleZeroThreeOneTwo (Or.inl rfl) _ _
        (hmidB ricciQuadraticPermutation_swapZeroOne (Or.inl rfl))
        (hmidD ricciQuadraticPermutation_swapZeroOne (Or.inl rfl))
  have hx1 : covariantJetNormSq (I := I) (M := M) g 2
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_swapBlocks -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_swapBlocks) ≤ Q := by
    simpa only [ricciQuadraticKernelDerivativeNestedTerm, ricciQuadraticKernelDerivativeBlock, IT, IU] using
      hblkFin ricciQuadraticPermutation_swapBlocks (Or.inr (Or.inl rfl)) _ _
        (hmidB ricciQuadraticPermutation_swapZeroOne (Or.inl rfl))
        (hmidD ricciQuadraticPermutation_swapZeroOne (Or.inl rfl))
  have hx2 : covariantJetNormSq (I := I) (M := M) g 2
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_cycleZeroThreeTwo -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_cycleZeroThreeTwo) ≤ Q := by
    simpa only [ricciQuadraticKernelDerivativeNestedTerm, ricciQuadraticKernelDerivativeBlock, IT, IU] using
      hblkFin ricciQuadraticPermutation_cycleZeroThreeTwo (Or.inr (Or.inr (Or.inl rfl))) _ _
        (hmidB ricciQuadraticPermutation_rotateInputs (Or.inr rfl))
        (hmidD ricciQuadraticPermutation_rotateInputs (Or.inr rfl))
  have hx3 : covariantJetNormSq (I := I) (M := M) g 2
      (ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gT T ricciQuadraticPermutation_cycleZeroOneThreeTwo -
        ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gU U ricciQuadraticPermutation_cycleZeroOneThreeTwo) ≤ Q := by
    simpa only [ricciQuadraticKernelDerivativeBareTerm, ricciQuadraticKernelDerivativeBlock, IT, IU] using
      hblkFin ricciQuadraticPermutation_cycleZeroOneThreeTwo
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) IT IU hbareB hbareD
  have hx4 : covariantJetNormSq (I := I) (M := M) g 2
      (ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gT T ricciQuadraticPermutation_cycleZeroOneTwo -
        ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gU U ricciQuadraticPermutation_cycleZeroOneTwo) ≤ Q := by
    simpa only [ricciQuadraticKernelDerivativeBareTerm, ricciQuadraticKernelDerivativeBlock, IT, IU] using
      hblkFin ricciQuadraticPermutation_cycleZeroOneTwo
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        IT IU hbareB hbareD
  have hx5 : covariantJetNormSq (I := I) (M := M) g 2
      (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gT T ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_swapZeroTwo -
        ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gU U ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_swapZeroTwo) ≤ Q := by
    simpa only [ricciQuadraticKernelDerivativeNestedTerm, ricciQuadraticKernelDerivativeBlock, IT, IU] using
      hblkFin ricciQuadraticPermutation_swapZeroTwo
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _ _
        (hmidB ricciQuadraticPermutation_rotateInputs (Or.inr rfl))
        (hmidD ricciQuadraticPermutation_rotateInputs (Or.inr rfl))
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
          (reindexCoeffGen (I := I) (M := M) g 4 2
                (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                  cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
                fourTraceArgPerm0231 +
            reindexCoeffGen (I := I) (M := M) g 4 2
                (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                  cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
                fourTraceArgPerm0321 -
            (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
              cometricDoubleTraceCoefficient (I := I) (M := M) g gU) -
            reindexCoeffGen (I := I) (M := M) g 4 2
                (cometricDoubleTraceCoefficient (I := I) (M := M) g gT -
                  cometricDoubleTraceCoefficient (I := I) (M := M) g gU)
                fourTraceArgPerm2301) := by
    rw [ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g gT,
      ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g gU,
      reindexCoeffGen_sub, reindexCoeffGen_sub, reindexCoeffGen_sub]
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

omit [NeZero (Module.finrank ℝ E)] in
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
