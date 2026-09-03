import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.FixedFirstOrderPairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.LowerScaleFifthOrderPairingBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (ccTensorToHs finiteEigenComboHs finiteEigenComboHs_coeff oneMinusConnLapSmoothIter
    norm_ccHs_eq_smoothHs oneMinusConnLapSmoothIter_succ
    oneMinusConnLapSmoothIter_zero smoothCcToTensorHs)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem galerkin_background_action_sobolev_four_pairing_bound_for_smaller_metric_perturbations
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta0 : ℝ,
        0 < delta0 ∧ delta0 ≤ 1 / 3 ∧
        ∀ {delta : ℝ}, 0 < delta → delta ≤ delta0 →
        ∃ R0 : ℝ, 0 < R0 ∧ R0 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ {R : ℝ} (hR : 0 ≤ R) (_hRR0 : R ≤ R0)
              (hdelta_lt : delta < 1)
              (hreal : ∀ T : SmoothCcTensor g 0 2,
                ‖smoothCcToTensorHs (I := I) (M := M) g
                    (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
                  gFibreOpBound (I := I) (M := M) g
                    (ccTensorBilinSymm (I := I) g T) delta),
              ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
                (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
                let theta : ℝ := min 1
                  (R / ‖galLowView (I := I) (M := M) g 1
                    (finiteEigenComboHs (I := I) (M := M) g F c
                      (((1 : ℕ) : ℝ) + 2))‖)
                let E3 : ℝ := ∑ i ∈ F,
                  tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2
                let E4 : ℝ := ∑ i ∈ F,
                  tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2
                let E5 : ℝ := ∑ i ∈ F,
                  tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2
                2 * |theta * (∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                      (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
                        hR hdelta_lt hreal F c).coeff i))| ≤
                  eta * E5 + G * (E4 + E3 * E4 + E3 ^ 2) := by
  intro eta heta
  obtain ⟨delta0, hdelta0, hdelta0third, hpair⟩ :=
    exists_uniform_lower_scale_h5_pairing_bound_with_caps (I := I) (M := M) hDim gBase hΛ heta
  refine ⟨delta0, hdelta0, hdelta0third, ?_⟩
  intro delta hdelta hdelta_le
  obtain ⟨R0, hR0, hR0one, hpair0⟩ := hpair hdelta hdelta_le
  have hdeltathird : delta ≤ 1 / 3 := hdelta_le.trans hdelta0third
  refine ⟨R0, hR0, hR0one, ?_⟩
  intro g hEq hjet
  obtain ⟨G, hG, hpairG⟩ := hpair0 g hEq hjet
  refine ⟨G, hG, ?_⟩
  intro R hR hRR0 hdelta_lt hreal F c
  let theta : ℝ := min 1
    (R / ‖galLowView (I := I) (M := M) g 1
      (finiteEigenComboHs (I := I) (M := M) g F c
        (((1 : ℕ) : ℝ) + 2))‖)
  let T : SmoothCcTensor g 0 2 :=
    symmS (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c)
  let hT := galRepFib (I := I) (M := M) g hR hreal F c
  let hZ := zeroMetricPerturbation_fibre_bound (I := I) (M := M) g hR hreal
  let E3 : ℝ := ∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2
  let E4 : ℝ := ∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2
  let E5 : ℝ := ∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2
  have hE3 : 0 ≤ E3 := by
    dsimp only [E3]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i 3)
        (sq_nonneg (c i))
  have hE4 : 0 ≤ E4 := by
    dsimp only [E4]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i 4)
        (sq_nonneg (c i))
  have hE5 : 0 ≤ E5 := by
    dsimp only [E5]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i 5)
        (sq_nonneg (c i))
  have hT2smooth :
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖ ≤ R := by
    have hraw := symm_h2_of_state (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c)
      (galCoreRep_ball (I := I) (M := M) g hR F c)
    rw [show (2 : ℝ) = (((1 : ℕ) : ℝ) + 1) by norm_num]
    simpa only [T] using hraw
  have hT2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R := by
    rw [norm_ccHs_eq_smoothHs]
    exact hT2smooth
  have hTsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u := by
    apply bilin_symm_of_symmS (I := I) (M := M) g
    dsimp only [T]
    exact symmS_idem (I := I) (M := M) g _
  have hmain := hpairG T hTsymm hdelta_lt hT hZ hR hRR0 hT2
  have hdiag := galTermPair4_diag (I := I) (M := M) g gBase hR
    hdelta_lt hdelta.le hdeltathird hreal F c
  have hT3 : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤
      Real.sqrt E3 := by
    rw [norm_ccHs_eq_smoothHs]
    simpa only [T, E3] using galRepHs_le (I := I) (M := M) g 3 hR F c
  have hT4 : ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ≤
      Real.sqrt E4 := by
    rw [norm_ccHs_eq_smoothHs]
    simpa only [T, E4] using galRepHs_le (I := I) (M := M) g 4 hR F c
  have hT5 : ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ≤
      Real.sqrt E5 := by
    rw [norm_ccHs_eq_smoothHs]
    simpa only [T, E5] using galRepHs_le (I := I) (M := M) g 5 hR F c
  have hT3sq : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 ≤ E3 := by
    calc
      _ ≤ (Real.sqrt E3) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hT3 2
      _ = E3 := Real.sq_sqrt hE3
  have hT4sq : ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 ≤ E4 := by
    calc
      _ ≤ (Real.sqrt E4) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hT4 2
      _ = E4 := Real.sq_sqrt hE4
  have hT5sq : ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 ≤ E5 := by
    calc
      _ ≤ (Real.sqrt E5) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hT5 2
      _ = E5 := Real.sq_sqrt hE5
  have hT34 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 ≤ E3 * E4 :=
    mul_le_mul hT3sq hT4sq (sq_nonneg _) hE3
  have hT3four : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4 ≤
      E3 ^ 2 := by
    nlinarith [sq_nonneg
      (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 - E3)]
  have hrhs :
      eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
          G * (‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) ≤
        eta * E5 + G * (E4 + E3 * E4 + E3 ^ 2) := by
    exact add_le_add (mul_le_mul_of_nonneg_left hT5sq heta.le)
      (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hT4sq hT34) hT3four) hG)
  change 2 * |theta * (∑ i ∈ F,
      tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
        (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase hR
          hdelta_lt hreal F c).coeff i))| ≤
    eta * E5 + G * (E4 + E3 * E4 + E3 ^ 2)
  calc
    _ = 2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmoothIter (I := I) g 0 2 3 T).toFun
        (oneMinusConnLapSmoothIter (I := I) g 0 2 1
          ((lowerScaleActionCoefficients (I := I) (M := M) g gBase T
            hdelta_lt hT hZ).secondOrderAction (I := I) (M := M) T +
            (lowerScaleActionCoefficients (I := I) (M := M) g gBase T
              hdelta_lt hT hZ).firstOrderAction (I := I) (M := M) T)).toFun| := by
      rw [hdiag]
    _ ≤ eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
          G * (‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
      simpa only [oneMinusConnLapSmoothIter_succ,
        oneMinusConnLapSmoothIter_zero] using hmain
    _ ≤ eta * E5 + G * (E4 + E3 * E4 + E3 ^ 2) := hrhs

theorem galerkin_background_action_sobolev_four_pairing_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta R0 : ℝ,
        0 < delta ∧ delta ≤ 1 / 3 ∧ 0 < R0 ∧ R0 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ {R : ℝ} (hR : 0 ≤ R) (_hRR0 : R ≤ R0)
              (hdelta_lt : delta < 1)
              (hreal : ∀ T : SmoothCcTensor g 0 2,
                ‖smoothCcToTensorHs (I := I) (M := M) g
                    (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
                  gFibreOpBound (I := I) (M := M) g
                    (ccTensorBilinSymm (I := I) g T) delta),
              ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
                (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
                let theta : ℝ := min 1
                  (R / ‖galLowView (I := I) (M := M) g 1
                    (finiteEigenComboHs (I := I) (M := M) g F c
                      (((1 : ℕ) : ℝ) + 2))‖)
                let E3 : ℝ := ∑ i ∈ F,
                  tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2
                let E4 : ℝ := ∑ i ∈ F,
                  tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2
                let E5 : ℝ := ∑ i ∈ F,
                  tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2
                2 * |theta * (∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                      (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
                        hR hdelta_lt hreal F c).coeff i))| ≤
                  eta * E5 + G * (E4 + E3 * E4 + E3 ^ 2) := by
  intro eta heta
  obtain ⟨delta, hdelta, hdeltathird, hpair⟩ :=
    galerkin_background_action_sobolev_four_pairing_bound_for_smaller_metric_perturbations (I := I) (M := M) hDim gBase hΛ heta
  obtain ⟨R0, hR0, hR0one, hpair0⟩ := hpair hdelta le_rfl
  exact ⟨delta, R0, hdelta, hdeltathird, hR0, hR0one, hpair0⟩

theorem galerkin_background_action_sobolev_four_pairing_bound_of_low_view_norm_le_for_smaller_metric_perturbations
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta0 : ℝ,
        0 < delta0 ∧ delta0 ≤ 1 / 3 ∧
        ∀ {delta : ℝ}, 0 < delta → delta ≤ delta0 →
        ∃ R0 : ℝ, 0 < R0 ∧ R0 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ {R : ℝ} (hR : 0 ≤ R) (_hRR0 : R ≤ R0)
              (hdelta_lt : delta < 1)
              (hreal : ∀ T : SmoothCcTensor g 0 2,
                ‖smoothCcToTensorHs (I := I) (M := M) g
                    (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
                  gFibreOpBound (I := I) (M := M) g
                    (ccTensorBilinSymm (I := I) g T) delta),
              ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
                (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
                ‖galLowView (I := I) (M := M) g 1
                    (finiteEigenComboHs (I := I) (M := M) g F c
                      (((1 : ℕ) : ℝ) + 2))‖ ≤ R →
                2 * |∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                      (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
                        hR hdelta_lt hreal F c).coeff i)| ≤
                  eta * (∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2) +
                  G * ((∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
                    (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                        (c i) ^ 2) *
                      (∑ i ∈ F,
                        tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                          (c i) ^ 2) +
                    (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                        (c i) ^ 2) ^ 2) := by
  intro eta heta
  obtain ⟨delta0, hdelta0, hdelta0third, hpair⟩ :=
    galerkin_background_action_sobolev_four_pairing_bound_for_smaller_metric_perturbations (I := I) (M := M) hDim gBase hΛ heta
  refine ⟨delta0, hdelta0, hdelta0third, ?_⟩
  intro delta hdelta hdelta_le
  obtain ⟨R0, hR0, hR0one, hpair0⟩ := hpair hdelta hdelta_le
  refine ⟨R0, hR0, hR0one, ?_⟩
  intro g hEq hjet
  obtain ⟨G, hG, hpairG⟩ := hpair0 g hEq hjet
  refine ⟨G, hG, ?_⟩
  intro R hR hRR0 hdelta_lt hreal F c hmem
  have hraw := hpairG hR hRR0 hdelta_lt hreal F c
  set q : ℝ := ‖galLowView (I := I) (M := M) g 1
    (finiteEigenComboHs (I := I) (M := M) g F c
      (((1 : ℕ) : ℝ) + 2))‖ with hq
  by_cases hq0 : q = 0
  · have hview : galLowView (I := I) (M := M) g 1
        (finiteEigenComboHs (I := I) (M := M) g F c
          (((1 : ℕ) : ℝ) + 2)) = 0 := by
      exact norm_eq_zero.mp (by simpa only [q] using hq0)
    have hcombo : finiteEigenComboHs (I := I) (M := M) g F c
          (((1 : ℕ) : ℝ) + 2) = 0 := by
      refine tensorHsInclusion_injective (I := I) (M := M) (g := g) (r := 0)
        (s := 2) (show (((1 : ℕ) : ℝ) + 1) ≤ ((1 : ℕ) : ℝ) + 2 by
          norm_num) ?_
      simpa only [galLowView, map_zero] using hview
    have hc : ∀ i ∈ F, c i = 0 := by
      intro i hi
      have hcoeff := congrArg (fun u => u.coeff i) hcombo
      simpa only [finiteEigenComboHs_coeff, if_pos hi, TensorHs.zero_coeff] using hcoeff
    have hE3 : 0 ≤ ∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) i 3) (sq_nonneg _)
    have hE4 : 0 ≤ ∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) i 4) (sq_nonneg _)
    have hE5 : 0 ≤ ∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) i 5) (sq_nonneg _)
    rw [Finset.sum_eq_zero fun i hi => by rw [hc i hi]; ring]
    simpa only [abs_zero, mul_zero] using
      add_nonneg (mul_nonneg heta.le hE5)
        (mul_nonneg hG
          (add_nonneg (add_nonneg hE4 (mul_nonneg hE3 hE4)) (sq_nonneg _)))
  · have hqpos : 0 < q := lt_of_le_of_ne (by positivity) (Ne.symm hq0)
    have hone : (1 : ℝ) ≤ R / q :=
      (one_le_div hqpos).2 (by simpa only [q] using hmem)
    simpa only [q, min_eq_left hone, one_mul] using hraw

theorem galerkin_background_action_sobolev_four_pairing_bound_of_low_view_norm_le
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta R0 : ℝ,
        0 < delta ∧ delta ≤ 1 / 3 ∧ 0 < R0 ∧ R0 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ {R : ℝ} (hR : 0 ≤ R) (_hRR0 : R ≤ R0)
              (hdelta_lt : delta < 1)
              (hreal : ∀ T : SmoothCcTensor g 0 2,
                ‖smoothCcToTensorHs (I := I) (M := M) g
                    (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
                  gFibreOpBound (I := I) (M := M) g
                    (ccTensorBilinSymm (I := I) g T) delta),
              ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
                (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
                ‖galLowView (I := I) (M := M) g 1
                    (finiteEigenComboHs (I := I) (M := M) g F c
                      (((1 : ℕ) : ℝ) + 2))‖ ≤ R →
                2 * |∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                      (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
                        hR hdelta_lt hreal F c).coeff i)| ≤
                  eta * (∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (5 : ℝ) * (c i) ^ 2) +
                  G * ((∑ i ∈ F,
                    tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
                    (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                        (c i) ^ 2) *
                      (∑ i ∈ F,
                        tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                          (c i) ^ 2) +
                    (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                        (c i) ^ 2) ^ 2) := by
  intro eta heta
  obtain ⟨delta, hdelta, hdeltathird, hpair⟩ :=
    galerkin_background_action_sobolev_four_pairing_bound_of_low_view_norm_le_for_smaller_metric_perturbations (I := I) (M := M) hDim gBase hΛ heta
  obtain ⟨R0, hR0, hR0one, hpair0⟩ := hpair hdelta le_rfl
  exact ⟨delta, R0, hdelta, hdeltathird, hR0, hR0one, hpair0⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
