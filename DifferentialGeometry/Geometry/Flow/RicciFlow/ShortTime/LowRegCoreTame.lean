import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRemainderH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRhsOne
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegDenseN

/-!
# Tame low-regularity Ricci--DeTurck core estimate

This module integrates the affine order-zero coefficient estimate and combines
it with the affine order-one path estimate.  Substitution into the conditional
remainder theorem gives the unconditional mixed `H3 -> H1` three-arm bound:
the top-difference coefficient is small with the lower `H2` radius, while the
only dependence on the endpoint `H3` sizes multiplies the lower `H2`
difference.
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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem smoothHs_eq_ccHs
    (g₀ : SmoothRiemannianMetric I M) (sigma : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ sigma T =
      ccTensorToHs (I := I) (M := M) g₀ 2 sigma T := by
  apply tensorHs.ext
  funext i
  rw [smoothCcToTensorHs_coeff, ccTensorToHs_coeff]

/-- The affine order-zero coefficient bound passes unchanged to the `H1` jet
of its interval-integrated coefficient field. -/
theorem rhs0_path_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ₀)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ A →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ ≤ A →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (rhsLow0PathIntegral (I := I) (M := M) g₀ g_bg T T'
              hδ₀_lt hδ hδ₀_lt hδ')‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hcoeff⟩ :=
    rhs0_h1_tame (I := I) (M := M) hDim g₀ g_bg hδ₀_nonneg hδ₀_lt
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3'
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ₀) (δ' := δ₀) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ₀_lt hδ₀_lt
  have hBA : 0 ≤ B0 R + B1 R * A :=
    add_nonneg (hB0 R hR) (mul_nonneg (hB1 R hR) hA)
  have hpath := path_jetL2_le (I := I) (M := M) g₀ 2 2 1
    (fun s => rhsLow0Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)
    (realizedSmallSet (δ := δ₀) (δ' := δ₀)) realizedSmallSet_isOpen hSI
    (rhsLow0_path_joint (I := I) (M := M) g₀ g_bg T T' hδ hδ') hBA
    (hcoeff T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3')
  simpa only [rhsLow0PathIntegral] using hpath

/-- On a closed three-manifold, the smooth Ricci--DeTurck remainder satisfies
the critical mixed three-arm estimate.  The functions `B0` and `B1` depend
only on the lower `H2` radius.  In particular, no endpoint `H3` size occurs in
the coefficient of the `H3` difference. -/
theorem rem_h1_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ ρ Ctop : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ₀)
        (R : ℝ), 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          ((realizedRHSArm (I := I) g₀ g_bg T hδ₀_lt hδ -
              realizedRHSArm (I := I) g₀ g_bg T' hδ₀_lt hδ') -
            rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ ≤
          Ctop * R *
              ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) (T - T')‖ +
            B0 R *
              ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) (T - T')‖ +
            B1 R *
                (‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ +
                  ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖) *
              ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) (T - T')‖ := by
  obtain ⟨ρ, Ctop, Clow, Ccoef, hρ, hCtop, hClow, hCcoef, hrem⟩ :=
    DifferentialGeometry.PDE.RicciFlow.rem_h1_of_jets
      (I := I) (M := M) hDim g₀ g_bg
  obtain ⟨Z0, Z1, hZ0, hZ1, hzero⟩ :=
    rhs0_path_tame (I := I) (M := M) hDim g₀ g_bg hδ₀_nonneg hδ₀_lt
  obtain ⟨O0, O1, hO0, hO1, hone⟩ :=
    rhs1_path_tame (I := I) (M := M) hDim g₀ g_bg hδ₀_nonneg hδ₀_lt
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
  intro T T' hTsymm hT'symm hδ hδ' R hR hRρ hT2 hT2'
  let A : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ +
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖
  have hA : 0 ≤ A := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hT3 : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ A := by
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hT3' : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ ≤ A := by
    exact le_add_of_nonneg_left (norm_nonneg _)
  let A0 : ℝ := Z0 R + Z1 R * A
  let A1 : ℝ := O0 R + O1 R * A
  have hA0 : 0 ≤ A0 :=
    add_nonneg (hZ0 R hR) (mul_nonneg (hZ1 R hR) hA)
  have hA1 : 0 ≤ A1 :=
    add_nonneg (hO0 R hR) (mul_nonneg (hO1 R hR) hA)
  have hΦ0 : (∑ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 j
        (rhsLow0PathIntegral (I := I) (M := M) g₀ g_bg T T'
          hδ₀_lt hδ hδ₀_lt hδ')‖ ^ 2) ≤ A0 ^ 2 := by
    simpa only [A0] using
      hzero T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3'
  have hΦ1 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 2 j
        (rhsLow1PathIntegral (I := I) (M := M) g₀ g_bg T T'
          hδ₀_lt hδ hδ₀_lt hδ')‖ ^ 2) ≤ A1 ^ 2 := by
    simpa only [A1] using
      hone T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3'
  have hout := hrem T T' hTsymm hT'symm hδ₀_lt hδ
    hδ₀_lt hδ' hR hRρ hT2 hT2' A0 A1 hA0 hA1 hΦ0 hΦ1
  calc
    _ ≤ Ctop * R *
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) (T - T')‖ +
        (Clow + Ccoef * (A0 + A1)) *
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) (T - T')‖ := hout
    _ = Ctop * R *
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) (T - T')‖ +
        B0 R *
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) (T - T')‖ +
        B1 R * A *
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) (T - T')‖ := by
      simp only [A0, A1, B0, B1]
      ring

/-- Spectral form of `rem_h1_tame` for the smooth nonlinearity.  This is the
exact three-arm estimate before restriction to the dense lower-state core. -/
theorem smoothN_h1_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ ρ Ctop : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ₀)
        (R : ℝ), 0 ≤ R → R ≤ ρ →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T‖ ≤ R →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T'‖ ≤ R →
        ‖deTurckSmoothN (I := I) (M := M) g₀ g_bg 1 T hδ₀_lt hδ -
            deTurckSmoothN (I := I) (M := M) g₀ g_bg 1 T' hδ₀_lt hδ'‖ ≤
          Ctop * R *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) (T - T')‖ +
            B0 R *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) (T - T')‖ +
            B1 R *
                (‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) T‖ +
                  ‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) T'‖) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) (T - T')‖ := by
  obtain ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, hrem⟩ :=
    rem_h1_tame (I := I) (M := M) hDim g₀ g_bg hδ₀_nonneg hδ₀_lt
  refine ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, ?_⟩
  intro T T' hTsymm hT'symm hδ hδ' R hR hRρ hT2 hT2'
  have hT2c :
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R := by
    simpa only [← smoothHs_eq_ccHs] using hT2
  have hT2c' :
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R := by
    simpa only [← smoothHs_eq_ccHs] using hT2'
  have hraw := hrem T T' hTsymm hT'symm hδ hδ' R hR hRρ hT2c hT2c'
  rw [deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
    (I := I) (M := M) g₀ g_bg 1 T T' hδ₀_lt hδ hδ₀_lt hδ']
  rw [deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff
    (I := I) g₀ g_bg T T' hδ₀_lt hδ hδ₀_lt hδ']
  simp only [smoothHs_eq_ccHs]
  change
    ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
      ((realizedRHSArm (I := I) g₀ g_bg T hδ₀_lt hδ -
          realizedRHSArm (I := I) g₀ g_bg T' hδ₀_lt hδ') -
        rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ ≤ _
  exact hraw

/-- The genuine smooth Ricci--DeTurck nonlinearity on the dense lower-state
core satisfies the consumer-shaped three-arm estimate.  Both symmetrization
and passage from smooth representatives to state coordinates are norm
nonexpanding. -/
theorem coreN_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ ρ Ctop : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ {R : ℝ} (hR : 0 ≤ R) (hRρ : R ≤ ρ)
        (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T‖ ≤ R →
            gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ T) δ₀)
        (x y : smoothCore (I := I) (M := M) g₀ R),
        ‖coreN (I := I) (M := M) g₀ g_bg hδ₀_lt hreal x -
            coreN (I := I) (M := M) g₀ g_bg hδ₀_lt hreal y‖ ≤
          Ctop * R *
              ‖(x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - y.1.1‖ +
            B0 R *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (2 : ℝ) ≤ 3 by norm_num)
                ((x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - y.1.1)‖ +
            B1 R *
                (‖(x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖ +
                  ‖(y.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖) *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (2 : ℝ) ≤ 3 by norm_num)
                ((x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - y.1.1)‖ := by
  obtain ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, hsmooth⟩ :=
    smoothN_h1_tame (I := I) (M := M) hDim g₀ g_bg hδ₀_nonneg hδ₀_lt
  refine ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, ?_⟩
  intro R hR hRρ hreal x y
  let X : SmoothCcTensor g₀ 0 2 := coreRep g₀ x
  let Y : SmoothCcTensor g₀ 0 2 := coreRep g₀ y
  let S : SmoothCcTensor g₀ 0 2 := symmS (I := I) (M := M) g₀ X
  let S' : SmoothCcTensor g₀ 0 2 := symmS (I := I) (M := M) g₀ Y
  have hS2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) S‖ ≤ R := by
    simpa only [S, X] using coreSymm_h2 (I := I) (M := M) g₀ x
  have hS2' : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) S'‖ ≤ R := by
    simpa only [S', Y] using coreSymm_h2 (I := I) (M := M) g₀ y
  have hδS := hreal S hS2
  have hδS' := hreal S' hS2'
  have hbase := hsmooth S S'
    (fun z v w => ccTensorBilin_symmS_symm' (I := I) (M := M) g₀ X z v w)
    (fun z v w => ccTensorBilin_symmS_symm' (I := I) (M := M) g₀ Y z v w)
    hδS hδS' R hR hRρ hS2 hS2'
  have hS3 :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) S‖ ≤
        ‖(x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖ := by
    calc
      _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) X‖ := by
        simpa only [S] using
          norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (3 : ℝ) X
      _ = _ := by rw [X, coreRep_spec]
  have hS3' :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) S'‖ ≤
        ‖(y.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖ := by
    calc
      _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) Y‖ := by
        simpa only [S'] using
          norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (3 : ℝ) Y
      _ = _ := by rw [Y, coreRep_spec]
  have hdiff3 :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) (S - S')‖ ≤
        ‖(x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - y.1.1‖ := by
    calc
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ)
          (symmS (I := I) (M := M) g₀ (X - Y))‖ := by
        rw [S, S', ← symmS_sub]
      _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) (X - Y)‖ :=
        norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (3 : ℝ) (X - Y)
      _ = _ := by rw [smoothCcToTensorHs_sub, X, Y, coreRep_spec, coreRep_spec]
  have hdiff2 :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) (S - S')‖ ≤
        ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ 3 by norm_num)
          ((x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - y.1.1)‖ := by
    calc
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ)
          (symmS (I := I) (M := M) g₀ (X - Y))‖ := by
        rw [S, S', ← symmS_sub]
      _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) (X - Y)‖ :=
        norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (2 : ℝ) (X - Y)
      _ = ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ 3 by norm_num)
          (smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) (X - Y))‖ := by
        rw [tensorHsInclusion_smoothCcToTensorHs]
      _ = _ := by rw [smoothCcToTensorHs_sub, X, Y, coreRep_spec, coreRep_spec]
  have hcoreX :
      coreN (I := I) (M := M) g₀ g_bg hδ₀_lt hreal x =
        deTurckSmoothN (I := I) (M := M) g₀ g_bg 1 S hδ₀_lt hδS := by
    rfl
  have hcoreY :
      coreN (I := I) (M := M) g₀ g_bg hδ₀_lt hreal y =
        deTurckSmoothN (I := I) (M := M) g₀ g_bg 1 S' hδ₀_lt hδS' := by
    rfl
  rw [hcoreX, hcoreY]
  refine hbase.trans ?_
  have htop := mul_le_mul_of_nonneg_left hdiff3 (mul_nonneg hCtop hR)
  have hlow := mul_le_mul_of_nonneg_left hdiff2 (hB0 R hR)
  have hhigh := add_le_add hS3 hS3'
  have hprod := mul_le_mul hhigh hdiff2 (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hmixed :
      B1 R *
          (‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) S‖ +
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) S'‖) *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) (S - S')‖ ≤
      B1 R *
          (‖(x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖ +
            ‖(y.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖) *
        ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ 3 by norm_num)
          ((x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - y.1.1)‖ := by
    calc
      _ = B1 R *
          ((‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) S‖ +
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (3 : ℝ) S'‖) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) (S - S')‖) := by ring
      _ ≤ B1 R *
          ((‖(x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖ +
              ‖(y.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ 3 by norm_num)
              ((x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - y.1.1)‖) :=
        mul_le_mul_of_nonneg_left hprod (hB1 R hR)
      _ = _ := by ring
  exact add_le_add (add_le_add htop hlow) hmixed

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
