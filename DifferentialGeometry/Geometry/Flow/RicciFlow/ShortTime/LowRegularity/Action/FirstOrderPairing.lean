import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.RemainderDifferenceBounds

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral (ccTensorToHs)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization

private theorem firstOrderPairing_arithmetic_bound
    (c0 c1 e0 e1 a a4 d2 d3 d4 n nrm : ℝ)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (he0 : 0 ≤ e0) (he1 : 0 ≤ e1)
    (ha : 0 ≤ a) (ha4 : 0 ≤ a4) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3)
    (hd4 : 0 ≤ d4) (hn : 0 ≤ n) (hnrm : 0 ≤ nrm) (hle : nrm ≤ n) :
    c0 * (1 + a) * (d4 + d3 + d2 + n) + c1 * a4 * (d3 + n) +
        (e0 * d3 + e1 * nrm + e1 * a * nrm) ≤
      (c0 + c1 + e0 + 2 * e1) * (1 + a + a4) * (d4 + d3 + d2 + n) := by
  have hS : (0 : ℝ) ≤ d4 + d3 + d2 + n := by linarith
  have hP0 : (0 : ℝ) ≤ 1 + a + a4 := by linarith
  have haS : (0 : ℝ) ≤ a * (d4 + d3 + d2 + n) := mul_nonneg ha hS
  have ha4S : (0 : ℝ) ≤ a4 * (d4 + d3 + d2 + n) := mul_nonneg ha4 hS
  have t1 : c0 * (1 + a) * (d4 + d3 + d2 + n) ≤
      c0 * (1 + a + a4) * (d4 + d3 + d2 + n) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hc0) hS
  have t2 : c1 * a4 * (d3 + n) ≤
      c1 * (1 + a + a4) * (d4 + d3 + d2 + n) :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left (by linarith) hc1)
      (by linarith) (by linarith) (mul_nonneg hc1 hP0)
  have t3 : e0 * d3 ≤ e0 * (1 + a + a4) * (d4 + d3 + d2 + n) := by
    have h : d3 ≤ (1 + a + a4) * (d4 + d3 + d2 + n) := by nlinarith
    calc
      e0 * d3 ≤ e0 * ((1 + a + a4) * (d4 + d3 + d2 + n)) :=
        mul_le_mul_of_nonneg_left h he0
      _ = e0 * (1 + a + a4) * (d4 + d3 + d2 + n) := by ring
  have t4 : e1 * nrm ≤ e1 * (1 + a + a4) * (d4 + d3 + d2 + n) := by
    have h : nrm ≤ (1 + a + a4) * (d4 + d3 + d2 + n) := by nlinarith
    calc
      e1 * nrm ≤ e1 * ((1 + a + a4) * (d4 + d3 + d2 + n)) :=
        mul_le_mul_of_nonneg_left h he1
      _ = e1 * (1 + a + a4) * (d4 + d3 + d2 + n) := by ring
  have t5 : e1 * a * nrm ≤ e1 * (1 + a + a4) * (d4 + d3 + d2 + n) := by
    have h : a * nrm ≤ (1 + a + a4) * (d4 + d3 + d2 + n) :=
      mul_le_mul (by linarith) (by linarith) hnrm hP0
    calc
      e1 * a * nrm = e1 * (a * nrm) := by ring
      _ ≤ e1 * ((1 + a + a4) * (d4 + d3 + d2 + n)) :=
        mul_le_mul_of_nonneg_left h he1
      _ = e1 * (1 + a + a4) * (d4 + d3 + d2 + n) := by ring
  nlinarith [t1, t2, t3, t4, t5]

private theorem sqSumLe (x y z j0 j1 : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxyz : x + y ≤ z)
    (h0 : j0 ≤ x ^ 2) (h1 : j1 ≤ y ^ 2) :
    j0 + j1 ≤ z ^ 2 := by
  have hxy : (0 : ℝ) ≤ x + y := by linarith
  have hsq : (x + y) ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ hxy hxyz 2
  nlinarith [mul_nonneg hx hy]

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem lowOrderCoefficient_pairing_lipschitz_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ K : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ K R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      let AT := lowerScaleActionCoefficients (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδZ
      let AU := lowerScaleActionCoefficients (I := I) (M := M) g g U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδU hδZ
      covariantJetNormSq (I := I) (M := M) g 2 (AT.zeroOrderCoefficient - AU.zeroOrderCoefficient) +
          covariantJetNormSq (I := I) (M := M) g 2 (AT.firstOrderCoefficient - AU.firstOrderCoefficient) ≤
        (K R * (1 + A + A4) * (D4 + D3 + D2 + N)) ^ 2 := by
  obtain ⟨ρ0, C0f, C1f, hρ0, hC0f, hC1f, hc0⟩ :=
    exists_ricciDeTurckLowOrderDifference_covariantJetNormSq_tame_bound (I := I) (M := M) hDim g
  obtain ⟨ρ1, E0, E1, hρ1, hE0, hE1, hc1⟩ :=
    firstOrderCoefficientDifference_tame (I := I) (M := M) hDim g
  refine ⟨min ρ0 ρ1, fun R => C0f R + C1f R + E0 + 2 * E1,
    lt_min hρ0 hρ1, ?_, ?_⟩
  · intro R hR
    have h0 := hC0f R hR
    have h1 := hC1f R hR
    linarith
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ R A A4 D2 D3 D4 N
    hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4
    hTU2 hTU3 hTU4 hTn hUn hTUn
  dsimp only
  have hM0 := hc0 T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4
    (hTn.trans (min_le_left _ _)) (hUn.trans (min_le_left _ _)) hTUn
  have hM1 := hc1 T U hT hU hδ_le hδ0 hδT hδU hδZ
    (hTn.trans (min_le_right _ _)) (hUn.trans (min_le_right _ _))
    A D3 hA hD3 hT3 hTU3
  have hC0eq := lowerScaleActionCoefficients_zeroOrderCoefficient_sub (I := I) (M := M) g T U
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδU hδZ
  have hC1eq := lowerScaleActionCoefficients_firstOrderCoefficient_sub (I := I) (M := M) g T U
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδU hδZ
  have hNrm : (0 : ℝ) ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ :=
    norm_nonneg _
  have hX0 : (0 : ℝ) ≤
      C0f R * (1 + A) * (D4 + D3 + D2 + N) + C1f R * A4 * (D3 + N) :=
    add_nonneg
      (mul_nonneg (mul_nonneg (hC0f R hR) (by linarith)) (by linarith))
      (mul_nonneg (mul_nonneg (hC1f R hR) hA4) (by linarith))
  have hY0 : (0 : ℝ) ≤ E0 * D3 + E1 * N + E1 * A * N :=
    add_nonneg
      (add_nonneg (mul_nonneg hE0 hD3) (mul_nonneg hE1 hN))
      (mul_nonneg (mul_nonneg hE1 hA) hN)
  have hYraw : (0 : ℝ) ≤
      E0 * D3 + E1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ +
        E1 * A * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ :=
    add_nonneg
      (add_nonneg (mul_nonneg hE0 hD3) (mul_nonneg hE1 hNrm))
      (mul_nonneg (mul_nonneg hE1 hA) hNrm)
  have hYle :
      E0 * D3 + E1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ +
          E1 * A * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤
        E0 * D3 + E1 * N + E1 * A * N := by
    have h1 := mul_le_mul_of_nonneg_left hTUn hE1
    have h2 := mul_le_mul_of_nonneg_left hTUn (mul_nonneg hE1 hA)
    linarith
  have hM1' : covariantJetNormSq (I := I) (M := M) g 2
      (firstOrderCoefficientDifference (I := I) (M := M) g T U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        hδT hδU hδZ) ≤ (E0 * D3 + E1 * N + E1 * A * N) ^ 2 :=
    hM1.trans (pow_le_pow_left₀ hYraw hYle 2)
  have hXY :
      (C0f R * (1 + A) * (D4 + D3 + D2 + N) + C1f R * A4 * (D3 + N)) +
          (E0 * D3 + E1 * N + E1 * A * N) ≤
        (C0f R + C1f R + E0 + 2 * E1) * (1 + A + A4) *
          (D4 + D3 + D2 + N) :=
    firstOrderPairing_arithmetic_bound (C0f R) (C1f R) E0 E1 A A4 D2 D3 D4 N N
      (hC0f R hR) (hC1f R hR) hE0 hE1 hA hA4 hD2 hD3 hD4 hN hN le_rfl
  refine sqSumLe
    (C0f R * (1 + A) * (D4 + D3 + D2 + N) + C1f R * A4 * (D3 + N))
    (E0 * D3 + E1 * N + E1 * A * N)
    ((C0f R + C1f R + E0 + 2 * E1) * (1 + A + A4) * (D4 + D3 + D2 + N))
    _ _ hX0 hY0 hXY ?_ ?_
  · rw [hC0eq]
    exact hM0
  · rw [hC1eq]
    exact hM1'

theorem firstOrderAction_pairing_lipschitz_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ K : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ K R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      let AT := lowerScaleActionCoefficients (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδZ
      let AU := lowerScaleActionCoefficients (I := I) (M := M) g g U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδU hδZ
      ‖AT.firstOrderActionThirdToSecondOrder (I := I) (M := M) - AU.firstOrderActionThirdToSecondOrder (I := I) (M := M)‖ ≤
          K R * (1 + A + A4) * (D4 + D3 + D2 + N) ∧
        ‖AT.firstOrderActionSecondToFirstOrder (I := I) (M := M) - AU.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
          K R * (1 + A + A4) * (D4 + D3 + D2 + N) := by
  obtain ⟨ρ, K1, hρ, hK1, hjet⟩ := lowOrderCoefficient_pairing_lipschitz_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, hdiff⟩ := exists_firstOrderAction_spectralSobolev_difference_bounds (I := I) (M := M) hDim g
  refine ⟨ρ, fun R => Ca * K1 R, hρ, fun R hR => mul_nonneg hCa (hK1 R hR), ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ R A A4 D2 D3 D4 N
    hR hA hA4 hD2 hD3 hD4 hN hT2 hU2 hT3 hU3 hT4 hU4
    hTU2 hTU3 hTU4 hTn hUn hTUn
  dsimp only
  have hK : (0 : ℝ) ≤ K1 R * (1 + A + A4) * (D4 + D3 + D2 + N) :=
    mul_nonneg (mul_nonneg (hK1 R hR) (by linarith)) (by linarith)
  have hin := hjet T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn
  obtain ⟨hHi, hLo⟩ :=
    hdiff
      (lowerScaleActionCoefficients (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδZ)
      (lowerScaleActionCoefficients (I := I) (M := M) g g U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδU hδZ)
      (K1 R * (1 + A + A4) * (D4 + D3 + D2 + N)) hK hin
  exact ⟨hHi.trans_eq (by ring), hLo.trans_eq (by ring)⟩

private theorem zeroOrderCoefficient_sqrt_bound
    (b p d n : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d) (hn : 0 ≤ n) :
    b * (p ^ 4 * (d ^ 2 + n ^ 2)) ≤
      (Real.sqrt b * p ^ 2 * (d + n)) ^ 2 := by
  have hdn : d ^ 2 + n ^ 2 ≤ (d + n) ^ 2 := by
    nlinarith [mul_nonneg hd hn]
  calc
    b * (p ^ 4 * (d ^ 2 + n ^ 2)) ≤
        b * (p ^ 4 * (d + n) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdn (by positivity)) hb
    _ = (Real.sqrt b * p ^ 2 * (d + n)) ^ 2 := by
      calc
        b * (p ^ 4 * (d + n) ^ 2) =
            Real.sqrt b ^ 2 * (p ^ 4 * (d + n) ^ 2) := by
          rw [Real.sq_sqrt hb]
        _ = (Real.sqrt b * p ^ 2 * (d + n)) ^ 2 := by ring

private theorem loPairArith
    (b b0 b1 a d2 d3 n : ℝ)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (ha : 0 ≤ a) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3) (hn : 0 ≤ n) :
    Real.sqrt b * (1 + a + a ^ 2) ^ 2 * (d2 + n) +
        (b0 * d3 + b1 * n + b1 * a * n) ≤
      (Real.sqrt b + b0 + 2 * b1) *
        (1 + a + a ^ 2) ^ 2 * (d3 + d2 + n) := by
  let p : ℝ := 1 + a + a ^ 2
  let s : ℝ := d3 + d2 + n
  let f : ℝ := p ^ 2 * s
  have hp1 : 1 ≤ p := by
    simp only [p]
    nlinarith [sq_nonneg a]
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp1
  have hp2 : 1 ≤ p ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num) hp1 2
  have hs : 0 ≤ s := by
    simp only [s]
    linarith
  have hf : 0 ≤ f := by
    exact mul_nonneg (sq_nonneg p) hs
  have hs_le : s ≤ f := by
    simp only [f]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hp2 hs
  have hd2n : d2 + n ≤ s := by
    simp only [s]
    linarith
  have hd3f : d3 ≤ f := by
    apply le_trans _ hs_le
    simp only [s]
    linarith
  have hnf : n ≤ f := by
    apply le_trans _ hs_le
    simp only [s]
    linarith
  have hap : a ≤ p := by
    simp only [p]
    nlinarith [sq_nonneg a]
  have hpp : p ≤ p ^ 2 := by
    nlinarith [mul_nonneg hp0 (by linarith : 0 ≤ p - 1)]
  have haf : a * n ≤ f := by
    have han : a * n ≤ p ^ 2 * s :=
      mul_le_mul (hap.trans hpp)
        (by
          simp only [s]
          linarith)
        hn (sq_nonneg p)
    simpa only [f] using han
  have h0 :
      Real.sqrt b * p ^ 2 * (d2 + n) ≤ Real.sqrt b * f := by
    have hp :
        p ^ 2 * (d2 + n) ≤ p ^ 2 * s :=
      mul_le_mul_of_nonneg_left hd2n (sq_nonneg p)
    have := mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg b)
    simpa only [f, mul_assoc] using this
  have h1 : b0 * d3 ≤ b0 * f :=
    mul_le_mul_of_nonneg_left hd3f hb0
  have h2 : b1 * n ≤ b1 * f :=
    mul_le_mul_of_nonneg_left hnf hb1
  have h3 : b1 * a * n ≤ b1 * f := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left haf hb1
  calc
    Real.sqrt b * (1 + a + a ^ 2) ^ 2 * (d2 + n) +
          (b0 * d3 + b1 * n + b1 * a * n) ≤
        Real.sqrt b * f + (b0 * f + b1 * f + b1 * f) := by
      simp only [p] at h0
      linarith
    _ = (Real.sqrt b + b0 + 2 * b1) *
          (1 + a + a ^ 2) ^ 2 * (d3 + d2 + n) := by
      simp only [f, p, s]
      ring

theorem firstOrderActionSecondToFirstOrder_pairing_lipschitz_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ K : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ K R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      let AT := lowerScaleActionCoefficients (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδZ
      let AU := lowerScaleActionCoefficients (I := I) (M := M) g g U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδU hδZ
      ‖AT.firstOrderActionSecondToFirstOrder (I := I) (M := M) - AU.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
        K R * (1 + A + A ^ 2) ^ 2 * (D3 + D2 + N) := by
  obtain ⟨ρ0, Bq, hρ0, hBq, hc0⟩ :=
    zeroOrderCoefficientDifference_tame (I := I) (M := M) hDim g
  obtain ⟨ρ1, B0, B1, hρ1, hB0, hB1, hc1⟩ :=
    firstOrderCoefficientDifference_tame (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, hop⟩ := exists_firstOrderActionSecondToFirstOrder_difference_bound (I := I) (M := M) hDim g
  let K : ℝ → ℝ := fun R =>
    Ca * (Real.sqrt (Bq R) + B0 + 2 * B1)
  refine ⟨min ρ0 ρ1, K, lt_min hρ0 hρ1, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg hCa
      (add_nonneg
        (add_nonneg (Real.sqrt_nonneg _) hB0)
        (mul_nonneg (by norm_num) hB1))
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 N hR hA hD2 hD3 hN hT2 hU2 hT3 hU3
    hTU2 hTU3 hTn hUn hTUn
  dsimp only
  let AT := lowerScaleActionCoefficients (I := I) (M := M) g g T
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδZ
  let AU := lowerScaleActionCoefficients (I := I) (M := M) g g U
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδU hδZ
  let P : ℝ := 1 + A + A ^ 2
  let R0 : ℝ := Real.sqrt (Bq R) * P ^ 2 * (D2 + N)
  let R1 : ℝ := B0 * D3 + B1 * N + B1 * A * N
  have hM0 := hc0 T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans (min_le_left _ _)) (hUn.trans (min_le_left _ _)) hTUn
  have hM1 := hc1 T U hT hU hδ_le hδ0 hδT hδU hδZ
    (hTn.trans (min_le_right _ _)) (hUn.trans (min_le_right _ _))
    A D3 hA hD3 hT3 hTU3
  have hC0eq : AT.zeroOrderCoefficient - AU.zeroOrderCoefficient =
      ricciDeTurckLowOrderDifference (I := I) (M := M) g T U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        hδT hδU hδZ := by
    simp only [AT, AU]
    exact lowerScaleActionCoefficients_zeroOrderCoefficient_sub (I := I) (M := M) g T U _ hδT hδU hδZ
  have hC1eq : AT.firstOrderCoefficient - AU.firstOrderCoefficient =
      firstOrderCoefficientDifference (I := I) (M := M) g T U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        hδT hδU hδZ := by
    simp only [AT, AU]
    exact lowerScaleActionCoefficients_firstOrderCoefficient_sub (I := I) (M := M) g T U _ hδT hδU hδZ
  have hR0 : 0 ≤ R0 := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg P))
      (add_nonneg hD2 hN)
  have hR1 : 0 ≤ R1 := by
    exact add_nonneg
      (add_nonneg (mul_nonneg hB0 hD3) (mul_nonneg hB1 hN))
      (mul_nonneg (mul_nonneg hB1 hA) hN)
  have hj0 :
      covariantJetNormSq (I := I) (M := M) g 1 (AT.zeroOrderCoefficient - AU.zeroOrderCoefficient) ≤ R0 ^ 2 := by
    rw [hC0eq]
    refine hM0.trans ?_
    simpa only [R0, P] using
      zeroOrderCoefficient_sqrt_bound (Bq R) (1 + A + A ^ 2) D2 N (hBq R hR) hD2 hN
  have hj1 :
      covariantJetNormSq (I := I) (M := M) g 2 (AT.firstOrderCoefficient - AU.firstOrderCoefficient) ≤ R1 ^ 2 := by
    rw [hC1eq]
    refine hM1.trans ?_
    have hraw0 : 0 ≤
        B0 * D3 +
          B1 * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ +
          B1 * A * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ := by
      positivity
    have hrawle :
        B0 * D3 +
            B1 * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (T - U)‖ +
            B1 * A * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (T - U)‖ ≤ R1 := by
      simp only [R1]
      have h1 := mul_le_mul_of_nonneg_left hTUn hB1
      have h2 := mul_le_mul_of_nonneg_left hTUn (mul_nonneg hB1 hA)
      linarith
    exact pow_le_pow_left₀ hraw0 hrawle 2
  have hpair := hop AT AU R0 R1 hR0 hR1 hj0 hj1
  have hlin :
      R0 + R1 ≤
        (Real.sqrt (Bq R) + B0 + 2 * B1) *
          P ^ 2 * (D3 + D2 + N) := by
    simpa only [R0, R1, P] using
      loPairArith (Bq R) B0 B1 A D2 D3 N
        hB0 hB1 hA hD2 hD3 hN
  calc
    ‖AT.firstOrderActionSecondToFirstOrder (I := I) (M := M) - AU.firstOrderActionSecondToFirstOrder (I := I) (M := M)‖ ≤
        Ca * (R0 + R1) := hpair
    _ ≤ Ca *
        ((Real.sqrt (Bq R) + B0 + 2 * B1) *
          P ^ 2 * (D3 + D2 + N)) :=
      mul_le_mul_of_nonneg_left hlin hCa
    _ = K R * (1 + A + A ^ 2) ^ 2 * (D3 + D2 + N) := by
      simp only [K, P]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
