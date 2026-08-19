import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.RicciDerivativePairingBounds

noncomputable section

set_option backward.isDefEq.respectTransparency false

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
  (ccTensorToHs symmS_eq_self_of_ccTensorBilin_symm)

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
  have hsymmT : symmS (I := I) (M := M) g T = T :=
    symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g T hT
  have hsymmU : symmS (I := I) (M := M) g U = U :=
    symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g U hU
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
