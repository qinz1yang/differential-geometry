import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzArmConnLapJetBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RemainderFirstOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.TopPathFirstOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.PathLowerBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.RemainderConvexPathBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]


theorem rem_h1_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ ρ Ctop : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
            ccTensorBilin (I := I) g T x v w = ccTensorBilin (I := I) g T x w v)
          (_hT'symm : ∀ (x : M) (v w : TangentSpace I x),
            ccTensorBilin (I := I) g T' x v w = ccTensorBilin (I := I) g T' x w v)
          (hδ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ₀)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T') δ₀)
          (R : ℝ), 0 ≤ R → R ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 ((1 : ℕ) : ℝ)
            ((deTurckRHSArmG0 (I := I) g gBase T hδ₀_lt hδ -
                deTurckRHSArmG0 (I := I) g gBase T' hδ₀_lt hδ') -
              DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth
                (I := I) g 0 2 (T - T'))‖ ≤
            Ctop * R *
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - T')‖ +
              B0 R *
                ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - T')‖ +
              B1 R *
                  (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ +
                    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖) *
                ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - T')‖ := by
  obtain ⟨ρ, Ctop, Clow, hρ, hCtop, hClow, htop⟩ :=
    top_path_h1_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Ccoef, hCcoef, hlower⟩ :=
    lower_jet_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Z0, Z1, hZ0, hZ1, hzero⟩ :=
    ricciDeTurckRemainderZeroOrderPathIntegral_h1_uniform_bound (I := I) (M := M) hDim gBase hΛ hδ₀_nonneg hδ₀_lt
  obtain ⟨O0, O1, hO0, hO1, hone⟩ :=
    ricciDeTurckRemainderFirstOrderPathIntegral_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ hδ₀_nonneg hδ₀_lt
  let B0 : ℝ → ℝ := fun R => Clow + Ccoef * (Z0 R + O0 R)
  let B1 : ℝ → ℝ := fun R => Ccoef * (Z1 R + O1 R)
  have hB0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R := by
    intro R hR
    exact add_nonneg hClow
      (mul_nonneg hCcoef (add_nonneg (hZ0 R hR) (hO0 R hR)))
  have hB1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R := by
    intro R hR
    exact mul_nonneg hCcoef (add_nonneg (hZ1 R hR) (hO1 R hR))
  refine ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, ?_⟩
  intro g hEq hjet T T' hTsymm hT'symm hδ hδ' R hR hRρ hT2 hT2'
  let A : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ +
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖
  have hA : 0 ≤ A := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hT3 : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ A := by
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hT3' : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ ≤ A := by
    exact le_add_of_nonneg_left (norm_nonneg _)
  let A0 : ℝ := Z0 R + Z1 R * A
  let A1 : ℝ := O0 R + O1 R * A
  have hA0 : 0 ≤ A0 :=
    add_nonneg (hZ0 R hR) (mul_nonneg (hZ1 R hR) hA)
  have hA1 : 0 ≤ A1 :=
    add_nonneg (hO0 R hR) (mul_nonneg (hO1 R hR) hA)
  have hΦ0 : (∑ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g gBase T T'
          hδ₀_lt hδ hδ₀_lt hδ')‖ ^ 2) ≤ A0 ^ 2 := by
    simpa only [A0] using
      hzero g hEq hjet T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3'
  have hΦ1 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 3 2 j
        (ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g gBase T T'
          hδ₀_lt hδ hδ₀_lt hδ')‖ ^ 2) ≤ A1 ^ 2 := by
    simpa only [A1] using
      hone g hEq hjet T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3'
  let U : SmoothCcTensor g 0 2 := T - T'
  set Φ0 : SmoothCcTensor g 2 2 :=
    ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g gBase T T'
      hδ₀_lt hδ hδ₀_lt hδ' with hΦ0def
  set Φ1 : SmoothCcTensor g 3 2 :=
    ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g gBase T T'
      hδ₀_lt hδ hδ₀_lt hδ' with hΦ1def
  clear_value Φ0 Φ1
  have hΦ0eq :
      ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g gBase T T'
        hδ₀_lt hδ hδ₀_lt hδ' = Φ0 := hΦ0def.symm
  have hΦ1eq :
      ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g gBase T T'
        hδ₀_lt hδ hδ₀_lt hδ' = Φ1 := hΦ1def.symm
  clear hΦ0def hΦ1def
  have hΦ0bound : (∑ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g 2 2 j Φ0‖ ^ 2) ≤ A0 ^ 2 := by
    simpa only [hΦ0eq] using hΦ0
  have hΦ1bound : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 3 2 j Φ1‖ ^ 2) ≤ A1 ^ 2 := by
    simpa only [hΦ1eq] using hΦ1
  let Φ2 : SmoothCcTensor g 4 2 :=
    rhsTopPathIntegral (I := I) (M := M) g T T'
      hδ₀_lt hδ hδ₀_lt hδ'
  have hpath :
      deTurckRHSAtMetricPerturbation (I := I) g gBase T hδ₀_lt hδ -
          deTurckRHSAtMetricPerturbation (I := I) g gBase T' hδ₀_lt hδ' =
        operatorFieldApply (I := I) (M := M) g 2 2 Φ0
            (iteratedCovGrad (I := I) g 0 2 0 U) +
          operatorFieldApply (I := I) (M := M) g 3 2 Φ1
            (iteratedCovGrad (I := I) g 0 2 1 U) +
          operatorFieldApply (I := I) (M := M) g 4 2 Φ2
            (iteratedCovGrad (I := I) g 0 2 2 U) := by
    simpa only [U, Φ2, hΦ0eq, hΦ1eq] using
      de_turck_rhs_at_metric_perturbation_sub_eq_path_integrals (I := I) (M := M) g gBase T T'
        hTsymm hT'symm hδ₀_lt hδ hδ₀_lt hδ'
  have hiter0 : iteratedCovGrad (I := I) g 0 2 0 U = U := by
    rw [iteratedCovGrad_zero]
  have hiter1 : iteratedCovGrad (I := I) g 0 2 1 U =
      covGrad (I := I) (M := M) g 0 2 U := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [hiter0, hiter1] at hpath
  have hlower' :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (operatorFieldApply (I := I) (M := M) g 2 2 Φ0 U +
          operatorFieldApply (I := I) (M := M) g 3 2 Φ1
            (covGrad (I := I) (M := M) g 0 2 U))‖ ≤
        Ccoef * (A0 + A1) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
    exact hlower g hEq hjet Φ0 Φ1 U A0 A1 hA0 hA1 hΦ0bound hΦ1bound
  have htop' :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (operatorFieldApply (I := I) (M := M) g 4 2 Φ2
            (iteratedCovGrad (I := I) g 0 2 2 U) -
          DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth
            (I := I) g 0 2 U)‖ ≤
        Ctop * R * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
          Clow * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
    simpa only [U, Φ2] using
      htop g hEq hjet T T' hδ₀_lt hδ hδ₀_lt hδ'
        hR hRρ hT2 hT2' U
  change
    ‖ccTensorToHs (I := I) (M := M) g 2 ((1 : ℕ) : ℝ)
      ((deTurckRHSAtMetricPerturbation (I := I) g gBase T hδ₀_lt hδ -
          deTurckRHSAtMetricPerturbation (I := I) g gBase T' hδ₀_lt hδ') -
        DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth
          (I := I) g 0 2 (T - T'))‖ ≤ _
  rw [Nat.cast_one]
  rw [hpath]
  let Slow : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 2 2 Φ0 U +
      operatorFieldApply (I := I) (M := M) g 3 2 Φ1
        (covGrad (I := I) (M := M) g 0 2 U)
  let Stop : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 Φ2
        (iteratedCovGrad (I := I) g 0 2 2 U) -
      DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth
        (I := I) g 0 2 U
  have hsplit :
      (operatorFieldApply (I := I) (M := M) g 2 2 Φ0 U +
          operatorFieldApply (I := I) (M := M) g 3 2 Φ1
            (covGrad (I := I) (M := M) g 0 2 U) +
        operatorFieldApply (I := I) (M := M) g 4 2 Φ2
            (iteratedCovGrad (I := I) g 0 2 2 U)) -
          DifferentialGeometry.Analysis.Elliptic.rawTensorConnLapSmooth
            (I := I) g 0 2 U = Slow + Stop := by
    simp only [Slow, Stop]
    abel
  rw [hsplit, ccTensorToHs_add]
  calc
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Slow‖ +
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Stop‖ := norm_add_le _ _
    _ ≤ Ccoef * (A0 + A1) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        (Ctop * R * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
          Clow * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖) := by
      apply add_le_add
      · simpa only [Slow] using hlower'
      · simpa only [Stop] using htop'
    _ = Ctop * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
        B0 R * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        B1 R * A *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
      simp only [A0, A1, B0, B1]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
