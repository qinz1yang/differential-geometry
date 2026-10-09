import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopCentres
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimChartValueTolerance
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamily
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison

/-!
# The LC87 slim centre at a centre of the sphere loop (S-FIXTURE-C2b, F2, G3 file 2)

At the constant scale `ρ ≡ R` the normalized metric `R⁻² g` of the sphere loop has uniform
constants: the volume of the unit ball is `≥ v = w / R³` (`exists_loopMetric3_volume_FXC2`), the
curvature derivatives of order `≤ K` are `≤ R^(K+2) A`, and `sec ≥ 0`. Hence the threshold form
`exists_slimCentre_with_formula_threshold_vs` applies at EVERY centre
`j = loopDiffeo (π_a (z₀, 0))` with the single threshold `slimBeta0_FXC2` (depending on
`Δ, σs, vs, K, R, z₀` only):

* `exists_slimCentre_loop_FXC2`: for `β 1 < slimBeta0_FXC2 …` there is an LC87 `SlimCentre` at `j`
  whose packet cutoff is the formula cutoff and whose coordinate is within `vs` of the first
  component of the actual splitting on `B(j, 10⁶ Δ R)`.
-/

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open GC.MetricGeometry
open scoped Manifold ContDiff ENNReal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2
attribute [local instance] nezero_finrank_euclideanThree_LC87

namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Data

variable {R : ℝ} (hR : 0 < R) (z₀ : S2)

/-- The volume constant of the normalized unit ball. -/
def slimVol_FXC2 : ℝ := Classical.choose (exists_loopMetric3_volume_FXC2 hR z₀) / R ^ 3

theorem slimVol_pos_FXC2 : 0 < slimVol_FXC2 hR z₀ :=
  div_pos (Classical.choose_spec (exists_loopMetric3_volume_FXC2 hR z₀)).1 (by positivity)

/-- The curvature-derivative constant (nonnegative). -/
def slimCurvA_FXC2 (K : ℕ) : ℝ :=
  max 0 (Classical.choose (exists_loopMetric3_curvature_bounds_FXC2 K))

/-- The function `𝒜` of the threshold: `R^(K+2) A`. -/
def slimA_FXC2 (K : ℕ) (R : ℝ) : ℝ → ℝ := fun _ => R ^ (K + 2) * slimCurvA_FXC2 K

variable {Δ σs vs : ℝ} {K : ℕ}

/-- **The threshold `β₀` of the slim centres of the sphere loop at scale `R`.** -/
def slimBeta0_FXC2 (hΔ : 1 ≤ Δ) (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (hvs : 0 < vs)
    (hK : 5 ≤ K) : ℝ :=
  Classical.choose (exists_slimCentre_with_formula_threshold_vs hΔ hσs hσs1 hvs K hK
    (slimVol_pos_FXC2 hR z₀) (slimA_FXC2 K R))

theorem slimBeta0_pos_FXC2 (hΔ : 1 ≤ Δ) (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (hvs : 0 < vs)
    (hK : 5 ≤ K) : 0 < slimBeta0_FXC2 hR z₀ hΔ hσs hσs1 hvs hK :=
  (Classical.choose_spec (exists_slimCentre_with_formula_threshold_vs hΔ hσs hσs1 hvs K hK
    (slimVol_pos_FXC2 hR z₀) (slimA_FXC2 K R))).1

end Data

/-- The ball volume of the normalized metric is `R⁻³` times the volume of the radius-`R` ball. -/
theorem ballVolume_nCM_FXC2 (ℓ : LoopLen_FXC2) {R : ℝ} (hR : 0 < R) (j : LoopC_FXC2 ℓ) :
    ballVolume (normalizedCenterMetric (loopMetric3_FXC2 ℓ) R hR) j 1 =
      ENNReal.ofReal R⁻¹ ^ 3 *
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ)
          (riemannianBallOf (loopMetric3_FXC2 ℓ) j R) := by
  unfold ballVolume
  rw [normalizedCenterMetric_ball, one_mul]
  unfold normalizedCenterMetric
  rw [Integral.Measure.volume_scale_apply]
  have hs : Real.sqrt ((R ^ 2)⁻¹) = R⁻¹ := by
    rw [Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hR]
  rw [hs]
  have hfin : Module.finrank ℝ E3 = 3 := by simp
  rw [hfin]

theorem loopVolume_lt_top_FXC2 (ℓ : LoopLen_FXC2) (S : Set (LoopC_FXC2 ℓ)) :
    Integral.Measure.riemannianVolumeMeasure (𝓡 3) (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) S < ⊤ := by
  let _ : MeasurableSpace (LoopC_FXC2 ℓ) := borel _
  have _ : BorelSpace (LoopC_FXC2 ℓ) := ⟨rfl⟩
  have := Integral.Measure.riemannianVolumeMeasure_isLocallyFiniteMeasure (I := 𝓡 3)
    (loopMetric3_FXC2 ℓ)
  exact (measure_mono (subset_univ S)).trans_lt isCompact_univ.measure_lt_top

/-- **The LC87 slim centre at a centre of the sphere loop** (threshold form, constants uniform in
the length and the shift). -/
theorem exists_slimCentre_loop_FXC2 {Δ σs vs : ℝ} {K : ℕ} (hΔ : 1 ≤ Δ) (hσs : 0 < σs)
    (hσs1 : σs ≤ 1 / 100) (hvs : 0 < vs) (hK : 5 ≤ K) {R : ℝ} (hR : 0 < R) (hR1 : 1 ≤ R)
    (z₀ : S2) (ℓ : LoopLen_FXC2) (hℓ2 : 2 * R ≤ ℓ.1) (j : LoopC_FXC2 ℓ) (a : ℝ)
    (hja : j = loopDiffeo_FXC2 ℓ (loopCoverS_FXC2 ℓ.1 a (z₀, 0))) {β : ℕ → ℝ} (hβ1 : 0 < β 1)
    (hβ0 : β 1 < slimBeta0_FXC2 hR z₀ hΔ hσs hσs1 hvs hK)
    (hJ : ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
      Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
      Nonempty (@KleinerLottApprox (LoopC_FXC2 ℓ) (WithLp 2 (ℝ × Z))
        ((loopMS3_FXC2 ℓ).rescale R⁻¹ (inv_pos.mpr hR)) _
        j (WithLp.toLp 2 ((0 : ℝ), z))
        (β 1))) :
    ∃ S : SlimCentre (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
        (fun _ => R) (fun _ => hR) (β 1) Δ σs K
        j,
      (let P := S.packet
      letI := S.instZ
      let hMc : CompleteSpace (LoopC_FXC2 ℓ) := complete_of_compact
      letI := (loopMS3_FXC2 ℓ).rescale ((fun _ : LoopC_FXC2 ℓ => R)
        j)⁻¹
        (inv_pos.mpr hR)
      letI := radialScaledBundle (loopMetric3_FXC2 ℓ) ((fun _ : LoopC_FXC2 ℓ => R)
        j)⁻¹ (inv_pos.mpr hR)
      letI : IsContinuousRiemannianBundle E3 (fun x : LoopC_FXC2 ℓ => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous (loopMetric3_FXC2 ℓ) ((fun _ : LoopC_FXC2 ℓ => R)
          j)⁻¹ (inv_pos.mpr hR)
      letI : IsRiemannianManifold 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) :=
        radialScaledManifold (m := loopMS3_FXC2 ℓ) (loopMetric3_FXC2 ℓ)
          (loopMS3_hmetric_FXC2 ℓ) ((fun _ : LoopC_FXC2 ℓ => R)
            j)⁻¹ (inv_pos.mpr hR)
      letI : CompleteSpace (LoopC_FXC2 ℓ) :=
        ((loopMS3_FXC2 ℓ).rescale_completeSpace_iff ((fun _ : LoopC_FXC2 ℓ => R)
          j)⁻¹ (inv_pos.mpr hR)).mpr hMc
      P.cutoff = P.toSlimChart.formulaCutoff) ∧
      ∀ x ∈ ball j (10 ^ 6 * Δ * R),
        |S.coord x - (letI := S.instZ
          @KleinerLottApprox.toFun (LoopC_FXC2 ℓ) (WithLp 2 (ℝ × S.Z))
            ((loopMS3_FXC2 ℓ).rescale R⁻¹ (inv_pos.mpr hR)) _
            j _ (β 1) S.split x).fst| < vs := by
  subst hja
  have hspec := (Classical.choose_spec (exists_slimCentre_with_formula_threshold_vs hΔ hσs hσs1
    hvs K hK (slimVol_pos_FXC2 hR z₀) (slimA_FXC2 K R))).2
  obtain ⟨o⟩ := loopOrientation_FXC2 ℓ
  refine hspec (β 1) hβ1 hβ0 (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ) o
    (fun _ => R) (fun _ => hR) (loopDiffeo_FXC2 ℓ (loopCoverS_FXC2 ℓ.1 a (z₀, 0)))
    (4 * (β 1)⁻¹ + 5) (by linarith) hJ ?_ ?_
  · intro x _
    refine (loopMetric3_sectional_FXC2 ℓ x).mono ?_
    have : 0 ≤ (β 1 / R) ^ 2 := sq_nonneg _
    linarith
  · refine ⟨slimVol_pos_FXC2 hR z₀, ?_, ?_, ?_⟩
    · change slimVol_FXC2 hR z₀ ≤ (ballVolume (normalizedCenterMetric (loopMetric3_FXC2 ℓ) R hR)
        (loopDiffeo_FXC2 ℓ (loopCoverS_FXC2 ℓ.1 a (z₀, 0))) 1).toReal
      have hfin : ballVolume (normalizedCenterMetric (loopMetric3_FXC2 ℓ) R hR)
          (loopDiffeo_FXC2 ℓ (loopCoverS_FXC2 ℓ.1 a (z₀, 0))) 1 ≠ ⊤ := by
        rw [ballVolume_nCM_FXC2]
        exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
          (loopVolume_lt_top_FXC2 ℓ _).ne
      rw [← ENNReal.ofReal_le_iff_le_toReal hfin, ballVolume_nCM_FXC2]
      have hw := (Classical.choose_spec (exists_loopMetric3_volume_FXC2 hR z₀)).2 ℓ a hℓ2
      have h1 : ENNReal.ofReal (slimVol_FXC2 hR z₀) = ENNReal.ofReal R⁻¹ ^ 3 *
          ENNReal.ofReal (Classical.choose (exists_loopMetric3_volume_FXC2 hR z₀)) := by
        rw [← ENNReal.ofReal_pow (inv_nonneg.mpr hR.le), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        unfold slimVol_FXC2
        field_simp
      rw [h1]
      gcongr
    · intro y _
      change SectionalBoundedBelowAt (normalizedCenterMetric (loopMetric3_FXC2 ℓ) R hR) y _
      unfold normalizedCenterMetric
      refine (sectionalBoundedBelowAt_scaleMetric_iff _).mpr
        ((loopMetric3_sectional_FXC2 ℓ y).mono ?_)
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg _)))
        (inv_nonneg.mpr (sq_nonneg _))
    · intro R' _ _ k hk y _
      change curvatureDerivativeNorm (normalizedCenterMetric (loopMetric3_FXC2 ℓ) R hR) k y ≤
        slimA_FXC2 K R R'
      rw [normalizedCenterMetric_derivative, curvatureDerivativeNorm_eq_curvDerivNorm]
      have hA := Classical.choose_spec (exists_loopMetric3_curvature_bounds_FXC2 K) ℓ k hk y
      have hA' : curvDerivNorm k (loopMetric3_FXC2 ℓ) y ≤ slimCurvA_FXC2 K :=
        hA.trans (le_max_right _ _)
      have hA0 : 0 ≤ slimCurvA_FXC2 K := le_max_left _ _
      calc R ^ (k + 2) * curvDerivNorm k (loopMetric3_FXC2 ℓ) y ≤ R ^ (k + 2) * slimCurvA_FXC2 K :=
            mul_le_mul_of_nonneg_left hA' (by positivity)
        _ ≤ R ^ (K + 2) * slimCurvA_FXC2 K :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR1 (by omega)) hA0

end DifferentialGeometry.Geometry.Collapse
