import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity

open private ScalarVectorTimeCoefficients.diffusion ScalarVectorTimeCoefficients.diffusion_eval ScalarVectorTimeCoefficients.radius ScalarVectorTimeCoefficients.radius_pos ScalarVectorTimeCoefficients.reaction ScalarVectorTimeCoefficients.reaction_eval from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState

open private coordinateMultiplication shifted_circle_operator_identity CircleHsPi circleHsPiInclusion shiftedRemainder extendClosedBall extendClosedBall_apply extendClosedBall_bounds circleHsPiCongr circleHsPiCongr_inclusion exists_continuousOn_bounded_intermediate_representative DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private firstJetCoordinates geometric_coefficients_contDiffOn circleFirstJet ambientCoordinate ambientSobolev tensorHsCongrL_ccTensorToHs ambientFirstJet ambientFirstJet_range initial_diffusion_H1 ScalarVectorTimeCoefficients ambientCoefficients DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.tensorHsCongrL_ccTensorToHs from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private ambientFirstJet_eq_initialJet from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientBounds
open private parameterDerivative_forcing_lift_of_contraction parameterDerivativeOperatorBoundsWithMargin parameterDerivativeOperatorBounds parameterDerivativeOperatorBounds_of_margin parameterDerivative_field_lift_of_forcing_lift parameterDerivativeForcingFieldLift ambient_coefficients_h2_norm_le_of_translated_state translated_state_norm_bounds ambient_translated_coefficients_h2_and_margin from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.Analysis.Parabolic
variable {n : ℕ}
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
private local instance vectorTensorHsNormedSpace {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (a : ℝ) :
    NormedSpace ℝ (PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) := inferInstance

private theorem precomposed_reference_coefficient_bounds
    {P X V A : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup A]
    (J : X →L[ℝ] V) {R : ℝ} (hR : 0 < R)
    (a : P → ℝ → Metric.closedBall (0 : V) R → A) (q : A) (Ca : ℝ≥0)
    (ha : ∀ p, LipschitzWith Ca (fun z : ℝ × Metric.closedBall (0 : V) R => a p z.1 z.2))
    (hclose : ∀ p t, t ∈ Set.Icc (0 : ℝ) R → ∀ z, ‖a p t z - q‖ ≤ (Ca : ℝ) * (2 * R)) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ) (hJρ : ‖J‖ * ρ ≤ R),
      ρ = R / (1 + ‖J‖) ∧ ρ ≤ R ∧
      let alpha := fun p => extendClosedBall hρ.le
        (fun t z => a p t (J.closedBallMap hJρ z))
      (∀ p t, t ∈ Set.Icc (0 : ℝ) ρ → ∀ z, ‖z‖ ≤ ρ → ∀ w, ‖w‖ ≤ ρ →
        ‖alpha p t z - alpha p t w‖ ≤ ((Ca : ℝ) * ‖J‖) * ‖z - w‖) ∧
      (∀ p t, t ∈ Set.Icc (0 : ℝ) ρ → ∀ z, ‖z‖ ≤ ρ →
        ‖alpha p t z - q‖ ≤ (2 * (Ca : ℝ) * (1 + ‖J‖)) * ρ) ∧
      (∀ p, Continuous (fun z : Set.Icc (0 : ℝ) ρ × Metric.closedBall (0 : X) ρ =>
        alpha p z.1 z.2)) ∧
      (∀ p t (z : Metric.closedBall (0 : X) ρ), alpha p t z = a p t (J.closedBallMap hJρ z)) := by
  let ρ := R / (1 + ‖J‖)
  have hden : 0 < 1 + ‖J‖ := by positivity
  have hρ : 0 < ρ := div_pos hR hden
  have hρeq : (1 + ‖J‖) * ρ = R := by
    dsimp only [ρ]
    field_simp
  have hρR : ρ ≤ R := by nlinarith [norm_nonneg J]
  have hJρ : ‖J‖ * ρ ≤ R := by nlinarith
  refine ⟨ρ, hρ, hJρ, rfl, hρR, ?_, ?_, ?_, ?_⟩
  · intro p t _ z hz w hw
    dsimp only
    have hz' : z ∈ Metric.closedBall (0 : X) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hw' : w ∈ Metric.closedBall (0 : X) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    rw [extendClosedBall_apply hρ.le _ t z hz', extendClosedBall_apply hρ.le _ t w hw']
    exact ((ha p).norm_sub_time_precomp_closedBall J hJρ t ⟨z, hz'⟩ ⟨w, hw'⟩).trans
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (J.le_opNorm (z - w)) Ca.coe_nonneg)
  · intro p t htt z hz
    dsimp only
    have hz' : z ∈ Metric.closedBall (0 : X) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [extendClosedBall_apply hρ.le _ t z hz']
    calc
      _ ≤ (Ca : ℝ) * (2 * R) := hclose p t ⟨htt.1, htt.2.trans hρR⟩ _
      _ = (2 * (Ca : ℝ) * (1 + ‖J‖)) * ρ := by rw [← hρeq]; ring
  · intro p
    exact (extendClosedBall_bounds hρ.le hρ.le le_rfl
      (fun t z => a p t (J.closedBallMap hJρ z)) (Ca * (1 + ‖J‖₊))
      ((ha p).prod_precomp_closedBall J hJρ)).2.2.2
  · intro p t z
    exact extendClosedBall_apply hρ.le _ t z.val z.property

private theorem scaled_coefficient_radius_bounds
    (m Q J Ca : ℝ≥0) {R : ℝ} (hR : 0 < R)
    (hCa : (Ca : ℝ) * R ≤ 1 / (32 * ((m : ℝ) * Q + 1))) :
    let ρ := R / (1 + (J : ℝ))
    0 < ρ ∧ ρ ≤ R ∧ (J : ℝ) * ρ ≤ R ∧
      ((m : ℝ) * (2 * Ca * (1 + (J : ℝ))) * Q) * ρ ≤ 1 / 16 ∧
      ((m : ℝ) * (Ca * J) * Q) * ρ ≤ 1 / 16 := by
  intro ρ
  have hJ : 0 < 1 + (J : ℝ) := by positivity
  have hρ : 0 < ρ := div_pos hR hJ
  have hρeq : (1 + (J : ℝ)) * ρ = R := by
    dsimp only [ρ]
    field_simp
  have hρR : ρ ≤ R := by nlinarith [J.coe_nonneg]
  have hJρ : (J : ℝ) * ρ ≤ R := by nlinarith
  have hden : 0 < 32 * ((m : ℝ) * Q + 1) := by positivity
  have hscaled : (Ca : ℝ) * R * (32 * ((m : ℝ) * Q + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp hCa
  have hmQ : 0 ≤ (m : ℝ) * Q := mul_nonneg m.coe_nonneg Q.coe_nonneg
  have hbound : 2 * (m : ℝ) * Q * (Ca : ℝ) * R ≤ 1 / 16 := by
    nlinarith [mul_nonneg Ca.coe_nonneg hR.le]
  have hA : ((m : ℝ) * (2 * Ca * (1 + (J : ℝ))) * Q) * ρ ≤ 1 / 16 := by
    calc
      _ = 2 * (m : ℝ) * Q * (Ca : ℝ) * ((1 + (J : ℝ)) * ρ) := by ring
      _ ≤ 1 / 16 := by rw [hρeq]; exact hbound
  refine ⟨hρ, hρR, hJρ, hA, ?_⟩
  calc
    ((m : ℝ) * (Ca * J) * Q) * ρ = (m : ℝ) * Ca * Q * ((J : ℝ) * ρ) := by ring
    _ ≤ (m : ℝ) * Ca * Q * R := by
      gcongr
    _ ≤ 2 * (m : ℝ) * Q * Ca * R := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg m.coe_nonneg Ca.coe_nonneg)
        Q.coe_nonneg) hR.le]
    _ ≤ 1 / 16 := hbound


private theorem circle_laplacian_add_shifted_remainder
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (alpha : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) →
      TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (reaction : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) →
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) (t : ℝ) :
    let m := coordinateMultiplication (ι := ι) (scalarHsMul g 1 (by norm_num))
    let q := ccTensorToHs g 0 ((1 : ℕ) : ℝ)
      (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 1 (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g 1
    let D := AddCircle.parameterDerivativeHsPi (ι := ι) g 1
    let K : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ)) v +
      shiftedRemainder m Q K D d q alpha reaction f t v =
        m (alpha t (K v)) (Q (f + v)) + reaction t (K v) := by
  intro m q d Q D K
  simpa only [shiftedRemainder] using
    shifted_circle_operator_identity g 1 (by norm_num) f v
      (alpha t (K v)) (reaction t (K v))



private theorem circle_shifted_equation_ae
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (alpha : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) →
      TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (reaction : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) →
      PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    {T R : ℝ} (hR : 0 ≤ R)
    (field : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T) :
    let m := coordinateMultiplication (ι := ι) (scalarHsMul g 1 (by norm_num))
    let q := ccTensorToHs g 0 ((1 : ℕ) : ℝ)
      (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 1 (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g 1
    let D := AddCircle.parameterDerivativeHsPi (ι := ι) g 1
    let K : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let hz : (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) ∈
        {v | ‖K v‖ ≤ R} := by
      simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR
    (∀ᵐ t ∂timeMeasure T, field t ∈ {v | ‖K v‖ ≤ R}) →
    (F =ᵐ[timeMeasure T] fun t =>
      shiftedRemainder m Q K D d q alpha reaction f t (aeSetLift hz field t)) →
    ∀ᵐ t ∂timeMeasure T,
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ)) (field t) + F t =
        m (alpha t (K (field t))) (Q (f + field t)) + reaction t (K (field t)) := by
  intro m q d Q D K hz hstate hforce
  have hlift := aeSetLift_coe_ae hz field hstate
  filter_upwards [hforce, hlift] with t ht htval
  change F t = shiftedRemainder m Q K D d q alpha reaction f t (aeSetLift hz field t).val at ht
  rw [htval] at ht
  rw [ht]
  exact circle_laplacian_add_shifted_remainder g f (field t) alpha reaction t

private theorem precomposed_shifted_uniform_time
    {ι A V : Type*} [Fintype ι]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (m : A →L[ℝ] CircleHsPi g ι ((1 : ℕ) : ℝ) →L[ℝ] CircleHsPi g ι ((1 : ℕ) : ℝ))
    (Q : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2) →L[ℝ] CircleHsPi g ι ((1 : ℕ) : ℝ))
    (D : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1) →L[ℝ] CircleHsPi g ι ((1 : ℕ) : ℝ))
    (d : CircleHsPi g ι ((1 : ℕ) : ℝ) →L[ℝ] CircleHsPi g ι ((1 : ℕ) : ℝ))
    (J : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    (q : A) (b₀ : CircleHsPi g ι ((1 : ℕ) : ℝ)) (f₀ : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    {δ R : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R)
    (a : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → A)
    (b : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → CircleHsPi g ι ((1 : ℕ) : ℝ))
    (Ca Cb : ℝ≥0)
    (ha : ∀ f, LipschitzWith Ca (fun z : ℝ × Metric.closedBall (0 : V) R => a f z.1 z.2))
    (hb : ∀ f, LipschitzWith Cb (fun z : ℝ × Metric.closedBall (0 : V) R => b f z.1 z.2))
    (haclose : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ z,
      ‖a f t z - q‖ ≤ (Ca : ℝ) * (2 * R))
    (hbclose : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ z,
      ‖b f t z - b₀‖ ≤ (Cb : ℝ) * (2 * R))
    (hCa : (Ca : ℝ) * R ≤ 1 / (32 * (‖m‖ * ‖Q‖ + 1))) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ) (hJρ : ‖J‖ * ρ ≤ R),
      ρ = R / (1 + ‖J‖) ∧ ρ ≤ R ∧
      let alpha := fun f => extendClosedBall hρ.le
        (fun t z => a f t (J.closedBallMap hJρ z))
      let reaction := fun f => extendClosedBall hρ.le
        (fun t z => b f t (J.closedBallMap hJρ z))
      let K := circleHsPiInclusion g ι
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      let N := fun f t (v : {v : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2) | ‖K v‖ ≤ ρ}) =>
        shiftedRemainder m Q K D d q (alpha f) (reaction f) f t v
      ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ ρ ∧
        ∀ (f : Metric.closedBall f₀ δ) {T : ℝ} (hT : 0 < T), T ≤ T₀ →
        ∃ (u : timeH1 (CircleHsPi g ι ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g ι ((1 : ℕ) : ℝ)) T),
          let field := maximalRegularityDuhamelVectorField
            (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0)
            (a := ((1 : ℕ) : ℝ)) (ι := ι) hT
            (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) gforce
          u = maximalRegularityDuhamelVectorMap
            (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0)
            (a := ((1 : ℕ) : ℝ)) (ι := ι) hT (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) gforce ∧
            (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖K v‖ ≤ ρ}) ∧
            gforce =ᵐ[timeMeasure T] (fun t => N f t (aeSetLift
              (show (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) ∈ {v | ‖K v‖ ≤ ρ} by
                simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hρ.le) field t)) ∧
            u.toFunL2 =
              (circleHsPiInclusion g ι
                (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)).compLpL
                  2 (timeMeasure T) field ∧
            timeH1.trace0 _ T u = 0 ∧
            timeH1.timeDeriv _ T u =
              (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))).compLpL
                  2 (timeMeasure T) field + gforce ∧
            ‖gforce‖ ≤ ρ / 4 := by
  obtain ⟨ρ, hρ, hJρ, hρeq, hρR, halip, haclose', hacont, _⟩ :=
    precomposed_reference_coefficient_bounds
      (P := Metric.closedBall f₀ δ) (X := CircleHsPi g ι (((1 : ℕ) : ℝ) + 1))
      (V := V) (A := A) J hR a q Ca ha haclose
  obtain ⟨ρb, hρb, hJρb, hρbeq, _, hblip, hbclose', hbcont, _⟩ :=
    precomposed_reference_coefficient_bounds
      (P := Metric.closedBall f₀ δ) (X := CircleHsPi g ι (((1 : ℕ) : ℝ) + 1))
      (V := V) (A := CircleHsPi g ι ((1 : ℕ) : ℝ)) J hR b b₀ Cb hb hbclose
  have hρbρ : ρb = ρ := hρbeq.trans hρeq.symm
  clear hρbeq
  subst ρb
  refine ⟨ρ, hρ, hJρ, hρeq, hρR, ?_⟩
  intro alpha reaction K N
  have hsmall := scaled_coefficient_radius_bounds ‖m‖₊ ‖Q‖₊ ‖J‖₊ Ca hR hCa
  simp only [coe_nnnorm] at hsmall
  rw [← hρeq] at hsmall
  have halip' : ∀ f t, t ∈ Set.Icc (0 : ℝ) ρ →
      LipschitzOnWith (Ca * ‖J‖₊) (alpha f t) (Metric.closedBall 0 ρ) := by
    intro f t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [NNReal.coe_mul, coe_nnnorm, dist_eq_norm] using
      halip f t ht z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
        w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)
  have hblip' : ∀ f t, t ∈ Set.Icc (0 : ℝ) ρ →
      LipschitzOnWith (Cb * ‖J‖₊) (reaction f t) (Metric.closedBall 0 ρ) := by
    intro f t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [NNReal.coe_mul, coe_nnnorm, dist_eq_norm] using
      hblip f t ht z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
        w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)
  have hmeas : ∀ f, TimeNemyMeas
      (show (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) ∈ {v | ‖K v‖ ≤ ρ} by
        simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hρ.le) (N f) ρ := by
    intro f
    exact (shiftedRemainder_timeNemyMeas m Q K D d q (alpha f) (reaction f) f
      (show (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) ∈ {v | ‖K v‖ ≤ ρ} by
        simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hρ.le)
      (fun v => v.property) (hacont f) (hbcont f)).2
  obtain ⟨T₀, hT₀eq, hT₀, hsol⟩ :=
    exists_uniform_time_shifted_vector (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 ((1 : ℕ) : ℝ) m Q D d q b₀ f₀ hδ hρ hρ
      alpha reaction (2 * Ca * (1 + ‖J‖₊)) (Ca * ‖J‖₊) (Cb * ‖J‖₊)
      (2 * Cb * (1 + ‖J‖₊)) halip'
      (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one,
        coe_nnnorm] using haclose') hblip'
      (fun f t ht => by
        simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one,
          coe_nnnorm] using hbclose' f t ht 0 (by simpa using hρ.le))
      (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one,
        coe_nnnorm] using hsmall.2.2.2.1)
      (by simpa only [NNReal.coe_mul, coe_nnnorm] using hsmall.2.2.2.2) hmeas
  refine ⟨T₀, hT₀, ?_, hsol⟩
  rw [hT₀eq]
  exact min_le_left _ _


private def referenceCircleSolutionFacts
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (alpha : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (ρ : ℝ) {T : ℝ} (hT : 0 < T)
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) : Prop :=
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let m : TensorHs g₀ 0 0 ((1 : ℕ) : ℝ) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) →L[ℝ]
        CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
    let L : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
          let field := maximalRegularityDuhamelVectorField
            (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (ι := Fin n) (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT
            (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) gforce
          u = maximalRegularityDuhamelVectorMap
              (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (ι := Fin n) (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce ∧
          (∀ᵐ t ∂(timeMeasure T), ‖K (field t)‖ ≤ ρ) ∧
          u.toFunL2 =
            (circleHsPiInclusion g₀ (Fin n)
              (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)).compLpL
                2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u = L.compLpL 2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ ρ / 4 ∧
          (∀ᵐ t ∂(timeMeasure T),
            L (field t) + gforce t =
              m (C (alpha t (K (field t)))) (Q (f + field t)) +
                Cpi (reaction t (K (field t))))


private theorem precomposed_circle_uniform_solutions
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    {δ R : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R)
    (a : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → TensorHs g₀ 0 0 1)
    (b : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → CircleHsPi g₀ (Fin n) 1)
    (Ca Cb : ℝ≥0)
    (halip : ∀ f, LipschitzWith Ca (fun z : ℝ × Metric.closedBall (0 : V) R => a f z.1 z.2))
    (hblip : ∀ f, LipschitzWith Cb (fun z : ℝ × Metric.closedBall (0 : V) R => b f z.1 z.2))
    (hbaseline : a ⟨f₀, Metric.mem_closedBall_self hδ⟩ 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀)))
    (haclose : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ z,
      ‖a f t z - a ⟨f₀, Metric.mem_closedBall_self hδ⟩ 0
        ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤ (Ca : ℝ) * (2 * R))
    (hbclose : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ z,
      ‖b f t z - b ⟨f₀, Metric.mem_closedBall_self hδ⟩ 0
        ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤ (Cb : ℝ) * (2 * R))
    (hCa : let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
      (Ca : ℝ) * R ≤ 1 / (32 * (‖m‖ * ‖Q‖ + 1))) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ) (hJρ : ‖J‖ * ρ ≤ R),
      ρ = R / (1 + ‖J‖) ∧ ρ ≤ R ∧
      let alpha := fun f => extendClosedBall hρ.le
        (fun t z => a f t (J.closedBallMap hJρ z))
      let reaction := fun f => extendClosedBall hρ.le
        (fun t z => b f t (J.closedBallMap hJρ z))
      ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ ρ ∧
        ∀ (f : Metric.closedBall f₀ δ) {T : ℝ} (hT : 0 < T), T ≤ T₀ →
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          referenceCircleSolutionFacts g₀ f.val (alpha f) (reaction f) ρ hT u gforce := by
  let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
  let Cpi := circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
  let m : TensorHs g₀ 0 0 ((1 : ℕ) : ℝ) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) →L[ℝ]
        CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
  let q := ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
  let d : CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      appHs g₀ 0 0 1 (scalarCc g₀ (AddCircle.laplacianDriftCoefficient g₀)))
  let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
  let D₁ := AddCircle.parameterDerivativeHsPi (ι := Fin n) g₀ 1
  let fref : Metric.closedBall f₀ δ := ⟨f₀, Metric.mem_closedBall_self hδ⟩
  let zref : Metric.closedBall (0 : V) R := ⟨0, Metric.mem_closedBall_self hR.le⟩
  change a fref 0 zref = q at hbaseline
  have haclose' : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ z,
      ‖a f t z - q‖ ≤ (Ca : ℝ) * (2 * R) := by
    intro f t htt z
    rw [← hbaseline]
    exact haclose f t htt z
  let a' := fun f t z => C (a f t z)
  let b' := fun f t z => Cpi (b f t z)
  have halip' : ∀ f, LipschitzWith Ca
      (fun z : ℝ × Metric.closedBall
        (0 : V) R => a' f z.1 z.2) := by
    intro f
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [a', dist_eq_norm, ← map_sub, C, tensorHsCongrL_apply, norm_tensorHsCongr]
      using (halip f).dist_le_mul z w
  have hblip' : ∀ f, LipschitzWith Cb
      (fun z : ℝ × Metric.closedBall
        (0 : V) R => b' f z.1 z.2) := by
    intro f
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [b', dist_eq_norm, ← map_sub, Cpi.norm_map]
      using (hblip f).dist_le_mul z w
  have haclose'' : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ z,
      ‖a' f t z - C q‖ ≤ (Ca : ℝ) * (2 * R) := by
    intro f t htt z
    simpa only [a', ← map_sub, C, tensorHsCongrL_apply, norm_tensorHsCongr] using haclose' f t htt z
  have hbclose' : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ z,
      ‖b' f t z - Cpi (b fref 0 zref)‖ ≤ (Cb : ℝ) * (2 * R) := by
    intro f t htt z
    simpa only [b', ← map_sub, Cpi.norm_map] using hbclose f t htt z
  obtain ⟨ρ, hρ, hJρ, hρeq, hρR, T₀, hT₀, hT₀ρ, hsol⟩ :=
    precomposed_shifted_uniform_time g₀ m Q D₁ d J (C q) (Cpi (b fref 0 zref)) f₀
      hδ hR a' b' Ca Cb halip' hblip' haclose'' hbclose' hCa
  let alpha := fun f => extendClosedBall hρ.le (fun t z => a f t (J.closedBallMap hJρ z))
  let reaction := fun f => extendClosedBall hρ.le (fun t z => b f t (J.closedBallMap hJρ z))
  have halpha : (fun f => extendClosedBall hρ.le (fun t z => a' f t (J.closedBallMap hJρ z))) =
      fun f t z => C (alpha f t z) := by
    funext f t z
    simp only [a', alpha, extendClosedBall]
    split_ifs <;> rfl
  have hreaction : (fun f => extendClosedBall hρ.le (fun t z => b' f t (J.closedBallMap hJρ z))) =
      fun f t z => Cpi (reaction f t z) := by
    funext f t z
    simp only [b', reaction, extendClosedBall]
    split_ifs <;> rfl
  refine ⟨ρ, hρ, hJρ, hρeq, hρR, T₀, hT₀, hT₀ρ, ?_⟩
  intro f T hT hTT₀
  obtain ⟨u, gforce, hu, hstate, hforce, hreal, htrace, hderiv, hnorm⟩ := hsol f hT hTT₀
  refine ⟨u, gforce, ?_⟩
  unfold referenceCircleSolutionFacts
  refine ⟨hu, hstate, hreal, htrace, hderiv, hnorm, ?_⟩
  apply circle_shifted_equation_ae g₀ f.val
    (fun t z => C (alpha f t z)) (fun t z => Cpi (reaction f t z)) hρ.le
    (maximalRegularityDuhamelVectorField
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (ι := Fin n)
      (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce) gforce hstate
  have hq : C q = ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀)) := by
    exact DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.tensorHsCongrL_ccTensorToHs g₀ _ _
  rw [halpha, hreaction, hq] at hforce
  exact hforce


end DifferentialGeometry.Analysis.Parabolic
end

noncomputable section
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.Analysis.Parabolic
variable {n : ℕ}
open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation QuasiLinear
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
private def referenceCircleCoefficientFacts
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ] CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (δ ρ : ℝ)
    (alpha : Metric.closedBall f₀ δ → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall f₀ δ → ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1) : Prop :=
  (∀ (f : Metric.closedBall f₀ δ) t, t ∈ Set.Icc (0 : ℝ) ρ → ∀ z, ‖z‖ ≤ ρ →
    Set.range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, P f.val + J z))) ⊆ S) ∧
  (∀ f t, t ∈ Set.Icc (0 : ℝ) ρ → ∀ z, ‖z‖ ≤ ρ → ∀ x,
    scalarH1ToContinuous g₀ (alpha f t z) x =
      F (fun i => match i with
        | none => t
        | some i => scalarH1ToContinuous g₀ ((P f) i + (J z) i) x)) ∧
  (∀ f t, t ∈ Set.Icc (0 : ℝ) ρ → ∀ z, ‖z‖ ≤ ρ → ∀ x j,
    scalarH1ToContinuous g₀ (reaction f t z j) x =
      G (fun i => match i with
        | none => t
        | some i => scalarH1ToContinuous g₀ ((P f) i + (J z) i) x) j)

private theorem referenceCircleCoefficientFacts_precomposed
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ] CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    {δ R ρ : ℝ} (hρ : 0 < ρ) (hJρ : ‖J‖ * ρ ≤ R) (hρR : ρ ≤ R)
    (a : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R → TensorHs g₀ 0 0 1)
    (b : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R → CircleHsPi g₀ (Fin n) 1)
    (hrange : ∀ (f : Metric.closedBall f₀ δ) t
      (v : Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R),
      t ∈ Set.Icc (0 : ℝ) R →
      Set.range (scalarH1PiToContinuous g₀
        (scalarH1TimeCoordinate g₀ (t, P f.val + v.val))) ⊆ S)
    (haeval : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ v x,
      scalarH1ToContinuous g₀ (a f t v) x =
        F (fun i => match i with
          | none => t
          | some i => scalarH1ToContinuous g₀ ((P f) i + v.val i) x))
    (hbeval : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ v x j,
      scalarH1ToContinuous g₀ (b f t v j) x =
        G (fun i => match i with
          | none => t
          | some i => scalarH1ToContinuous g₀ ((P f) i + v.val i) x) j) :
    let alpha := fun f => extendClosedBall hρ.le
      (fun t z => a f t (J.closedBallMap hJρ z))
    let reaction := fun f => extendClosedBall hρ.le
      (fun t z => b f t (J.closedBallMap hJρ z))
    referenceCircleCoefficientFacts g₀ f₀ P J F G S δ ρ alpha reaction := by
  intro alpha reaction
  refine ⟨?_, ?_, ?_⟩
  · intro f t htt z hz
    have hz' : z ∈ Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact hrange f t (J.closedBallMap hJρ ⟨z, hz'⟩) ⟨htt.1, htt.2.trans hρR⟩
  · intro f t htt z hz x
    have hz' : z ∈ Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    dsimp only [alpha]
    rw [extendClosedBall_apply hρ.le _ t z hz']
    exact haeval f t ⟨htt.1, htt.2.trans hρR⟩ (J.closedBallMap hJρ ⟨z, hz'⟩) x
  · intro f t htt z hz x j
    have hz' : z ∈ Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    dsimp only [reaction]
    rw [extendClosedBall_apply hρ.le _ t z hz']
    exact hbeval f t ⟨htt.1, htt.2.trans hρR⟩ (J.closedBallMap hJρ ⟨z, hz'⟩) x j

end DifferentialGeometry.Analysis.Parabolic
end

noncomputable section
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear
variable {n : ℕ}
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
private theorem circle_coefficient_threshold_pos
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
    0 < (1 : ℝ) / (32 * (‖m‖ * ‖Q‖ + 1)) := by
  intro m Q
  positivity

end DifferentialGeometry.Analysis.Parabolic
end

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

open TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem reference_jet_add_correction_eq
    {ι : Type*} [Fintype ι]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f v : PiLp 2 (fun _ : ι => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2))) :
    let J₀ := circleFirstJet (ι := ι) g₀
    let K₀ : PiLp 2 (fun _ : ι => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g₀ 0 0 ((1 : ℝ) + 1)) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr g₀ ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K : PiLp 2 (fun _ : ι => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    P f + J (K v) = P (f + v) := by
  intro J₀ K₀ P J K
  have hK : circleHsPiCongr g₀ ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) (K v) = K₀ v := by
    simpa only [circleHsPiCongr, tensorHsCongr_refl,
      LinearIsometryEquiv.piLpCongrRight_refl, LinearIsometryEquiv.coe_refl, id_eq] using
      circleHsPiCongr_inclusion g₀ ι
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)
        (rfl : ((1 : ℕ) : ℝ) + 2 = ((1 : ℕ) : ℝ) + 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
        (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num) v
  have hJ : J (K v) = P v := congrArg J₀ hK
  rw [hJ, map_add]

end DifferentialGeometry.Analysis.Parabolic
end

noncomputable section
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
open _root_.DifferentialGeometry.MeasureTheory Set Filter
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_diffusion_eq_principal
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (v : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 1))
    (hv : v = ambientFirstJet c₀ (g 0) e he)
    (a : TensorHs (c₀.pullbackMetric (g 0)) 0 0 1)
    (ha : ∀ x, scalarH1ToContinuous (c₀.pullbackMetric (g 0)) a x =
      curveShorteningChartDiffusionCoefficient
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
        (firstJetCoordinates n (fun i => match i with
          | none => 0
          | some i => scalarH1ToContinuous (c₀.pullbackMetric (g 0)) (v i) x))) :
    a = ccTensorToHs (c₀.pullbackMetric (g 0)) 0 1
      (scalarCc (c₀.pullbackMetric (g 0))
        (AddCircle.laplacianPrincipalCoefficient (c₀.pullbackMetric (g 0)))) := by
  apply initial_diffusion_H1 c₀ g he hr hEU hleft β a
  intro x
  rw [ha]
  congr 2
  funext i
  cases i with
  | none => simp only [scalarH1TimeCoordinate_eval_none]
  | some i => simp only [scalarH1TimeCoordinate_eval_some, hv]

private theorem ambient_reference_composition
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {ε : ℝ} (hε : 0 < ε) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)) := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (1 + 1)) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1) := circleFirstJet (ι := Fin n) g₀
    let K : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (1 + 1)) := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1) := J.comp K
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    ∃ (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ), ‖P‖ * δ ≤ R ∧
      ∃ Ca Cb : ℝ≥0,
      R ≤ ε ∧ (Ca : ℝ) * R ≤ ε ∧ (Cb : ℝ) * R ≤ ε ∧
      ∃ alpha : Metric.closedBall f₀ δ → ℝ →
        Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) R →
          TensorHs g₀ 0 0 1,
      ∃ reaction : Metric.closedBall f₀ δ → ℝ →
        Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) R →
          PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1),
      (∀ f, LipschitzWith Ca (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) R => alpha f p.1 p.2)) ∧
      (∀ f, LipschitzWith Cb (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) R => reaction f p.1 p.2)) ∧
      (∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ v,
        ‖alpha f t v - alpha ⟨f₀, Metric.mem_closedBall_self hδ.le⟩ 0
          ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤ (Ca : ℝ) * (2 * R)) ∧
      (∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ v,
        ‖reaction f t v - reaction ⟨f₀, Metric.mem_closedBall_self hδ.le⟩ 0
          ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤ (Cb : ℝ) * (2 * R)) ∧
      (∀ f k t v, ‖alpha f t v - alpha k t v‖ ≤ (Ca : ℝ) * ‖P (f.val - k.val)‖) ∧
      (∀ f k t v, ‖reaction f t v - reaction k t v‖ ≤ (Cb : ℝ) * ‖P (f.val - k.val)‖) ∧
      (∀ (f : Metric.closedBall f₀ δ) t
        (v : Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) R),
        t ∈ Set.Icc (0 : ℝ) R →
        Set.range (scalarH1PiToContinuous g₀ (scalarH1TimeCoordinate g₀ (t, P f.val + v.val))) ⊆ S) ∧
      (∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ v x,
        scalarH1ToContinuous g₀ (alpha f t v) x =
          F (fun i => match i with
            | none => t
            | some i => scalarH1ToContinuous g₀ ((P f) i + v.val i) x)) ∧
      (∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ v x j,
        scalarH1ToContinuous g₀ (reaction f t v j) x =
          G (fun i => match i with
            | none => t
            | some i => scalarH1ToContinuous g₀ ((P f) i + v.val i) x) j) := by
  intro g₀ f₀ J K P F G S
  obtain ⟨hS, hF, hG'⟩ := geometric_coefficients_contDiffOn hG β
  have hjet : ambientFirstJet c₀ (g 0) e he = P f₀ := by
    change circleFirstJet g₀ _ = circleFirstJet g₀ _
    congr 1
  have hreference : Set.range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (0, P f₀))) ⊆ S := by
    rw [← hjet]
    exact ambientFirstJet_range c₀ g ht he hr hEU hleft β
  exact exists_scalar_vectorH1_time_composition_on_translated_closedBall
    g₀ n P f₀ F G hF hG' hS hreference hε


omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambientFirstJet_eq_reference_jet
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e) :
    ambientFirstJet c₀ g e he = circleFirstJet (c₀.pullbackMetric g)
      ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => tensorHsInclusion
        (g := c₀.pullbackMetric g) (r := 0) (s := 0)
        (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)))
          (ambientSobolev c₀ g e he (((1 : ℕ) : ℝ) + 2))) := by
  change circleFirstJet _ _ = circleFirstJet _ _
  congr 1

private theorem reference_diffusion_at_sobolev_jet
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (a : TensorHs (c₀.pullbackMetric (g 0)) 0 0 1) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := (circleFirstJet (ι := Fin n) g₀).comp
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => tensorHsInclusion
        (g := g₀) (r := 0) (s := 0)
        (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)))
    (∀ x, scalarH1ToContinuous g₀ a x =
      (curveShorteningChartDiffusionCoefficient
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n)
        (fun i => match i with
          | none => 0
          | some i => scalarH1ToContinuous g₀ ((P f₀) i + 0) x)) →
    a = ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀)) := by
  intro g₀ f₀ P ha
  apply reference_diffusion_eq_principal c₀ g he hr hEU hleft β (P f₀)
    (ambientFirstJet_eq_reference_jet c₀ (g 0) he).symm a
  intro x
  rw [ha]
  dsimp only [Function.comp_def]
  apply congrArg (curveShorteningChartDiffusionCoefficient
    (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β)
  apply congrArg (firstJetCoordinates n)
  funext i
  cases i with
  | none => rfl
  | some i =>
    simp only [add_zero]
    rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear
variable {n : ℕ}
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_circle_uniform_solutions_le_of_coefficients
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    {δ R : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R) (δcap : ℝ)
    (a : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R → TensorHs g₀ 0 0 1)
    (b : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R → CircleHsPi g₀ (Fin n) 1)
    (Ca Cb : ℝ≥0)
    (halip : ∀ f, LipschitzWith Ca (fun z : ℝ × Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R => a f z.1 z.2))
    (hblip : ∀ f, LipschitzWith Cb (fun z : ℝ × Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R => b f z.1 z.2))
    (hbaseline : a ⟨f₀, Metric.mem_closedBall_self hδ⟩ 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀)))
    (haclose : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ z,
      ‖a f t z - a ⟨f₀, Metric.mem_closedBall_self hδ⟩ 0
        ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤ (Ca : ℝ) * (2 * R))
    (hbclose : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ z,
      ‖b f t z - b ⟨f₀, Metric.mem_closedBall_self hδ⟩ 0
        ⟨0, Metric.mem_closedBall_self hR.le⟩‖ ≤ (Cb : ℝ) * (2 * R))
    (hCa : let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
      (Ca : ℝ) * R ≤ 1 / (32 * (‖m‖ * ‖Q‖ + 1)))
    (hrange : ∀ (f : Metric.closedBall f₀ δ) t
      (v : Metric.closedBall (0 : CircleHsPi g₀ (Fin n ⊕ Fin n) 1) R),
      t ∈ Set.Icc (0 : ℝ) R →
      Set.range (scalarH1PiToContinuous g₀
        (scalarH1TimeCoordinate g₀ (t, P f.val + v.val))) ⊆ S)
    (haeval : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ v x,
      scalarH1ToContinuous g₀ (a f t v) x =
        F (fun i => match i with
          | none => t
          | some i => scalarH1ToContinuous g₀ ((P f) i + v.val i) x))
    (hbeval : ∀ f t, t ∈ Set.Icc (0 : ℝ) R → ∀ v x j,
      scalarH1ToContinuous g₀ (b f t v j) x =
        G (fun i => match i with
          | none => t
          | some i => scalarH1ToContinuous g₀ ((P f) i + v.val i) x) j) :
    ∃ (ρ : ℝ), 0 < ρ ∧ ρ ≤ R ∧
      ∃ alpha : Metric.closedBall f₀ (min δ δcap) → ℝ →
        CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1,
      ∃ reaction : Metric.closedBall f₀ (min δ δcap) → ℝ →
        CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1,
      referenceCircleCoefficientFacts g₀ f₀ P J F G S (min δ δcap) ρ alpha reaction ∧
      ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ ρ ∧
        ∀ (f : Metric.closedBall f₀ (min δ δcap)) {T : ℝ} (hT : 0 < T), T ≤ T₀ →
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          referenceCircleSolutionFacts g₀ f.val (alpha f) (reaction f) ρ hT u gforce := by
  obtain ⟨ρ, hρ, hJρ, _, hρR, hsol⟩ :=
    precomposed_circle_uniform_solutions (n := n)
      (V := CircleHsPi g₀ (Fin n ⊕ Fin n) 1) g₀ f₀ J hδ hR a b Ca Cb halip hblip
      hbaseline haclose hbclose hCa
  let alpha := fun f => extendClosedBall hρ.le (fun t z => a f t (J.closedBallMap hJρ z))
  let reaction := fun f => extendClosedBall hρ.le (fun t z => b f t (J.closedBallMap hJρ z))
  have hcoeff := referenceCircleCoefficientFacts_precomposed g₀ f₀ P J F G S hρ hJρ hρR
    a b hrange haeval hbeval
  let includeInitial : Metric.closedBall f₀ (min δ δcap) → Metric.closedBall f₀ δ :=
    fun f => ⟨f.val, Metric.mem_closedBall.mpr
      ((Metric.mem_closedBall.mp f.property).trans (min_le_left δ δcap))⟩
  refine ⟨ρ, hρ, hρR, (fun f => alpha (includeInitial f)),
    (fun f => reaction (includeInitial f)), ?_, ?_⟩
  · rcases hcoeff with ⟨hrange', haeval', hbeval'⟩
    refine ⟨?_, ?_, ?_⟩
    · intro f t htt z hz
      exact hrange' (includeInitial f) t htt z hz
    · intro f t htt z hz x
      exact haeval' (includeInitial f) t htt z hz x
    · intro f t htt z hz x j
      exact hbeval' (includeInitial f) t htt z hz x j
  · obtain ⟨T₀, hT₀, hT₀ρ, hfamily⟩ := hsol
    refine ⟨T₀, hT₀, hT₀ρ, ?_⟩
    intro f T hT hTT₀
    exact hfamily (includeInitial f) hT hTT₀

end DifferentialGeometry.Analysis.Parabolic
end

noncomputable section
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
open _root_.DifferentialGeometry.MeasureTheory Set Filter
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem ambient_reference_uniform_solutions_le
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    (δcap ρcap : ℝ) (hδcap : 0 < δcap) (hρcap : 0 < ρcap) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J₀ : CircleHsPi g₀ (Fin n) (1 + 1) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1 := circleFirstJet (ι := Fin n) g₀
    let K₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) (1 + 1) := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n ⊕ Fin n) 1  := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    (∀ f v, P f + J (K v) = P (f + v)) ∧
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ δ ≤ δcap ∧ ρ ≤ ρcap ∧
      ∃ alpha : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1,
      ∃ reaction : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →
          CircleHsPi g₀ (Fin n) 1,
      referenceCircleCoefficientFacts g₀ f₀ P J F G S δ ρ alpha reaction ∧
      ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ ρ ∧
        ∀ (f : Metric.closedBall f₀ δ) {T : ℝ} (hT : 0 < T), T ≤ T₀ →
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          referenceCircleSolutionFacts g₀ f.val (alpha f) (reaction f) ρ hT u gforce := by
  intro g₀ f₀ J₀ K₀ P J K F G S
  refine ⟨fun f v => reference_jet_add_correction_eq g₀ f v, ?_⟩
  have hε := lt_min (circle_coefficient_threshold_pos (n := n) g₀) hρcap
  obtain ⟨R, δ, hR, hδ, _, Ca, Cb, hRε, hCaε, _,
      a, b, halip, hblip, haclose, hbclose, _, _, hrange, haeval, hbeval⟩ :=
    ambient_reference_composition c₀ g ht he hr hEU hleft β hG hε
  have hCa := hCaε.trans (min_le_left _ _)
  have hRcap : R ≤ ρcap := hRε.trans (min_le_right _ _)
  let fref := (⟨ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2),
    Metric.mem_closedBall_self hδ.le⟩ :
      Metric.closedBall (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)) δ)
  let zref := (⟨0, Metric.mem_closedBall_self hR.le⟩ :
    Metric.closedBall (0 : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n ⊕ Fin n) 1) R)
  have ha0 := haeval fref 0 ⟨le_rfl, hR.le⟩ zref
  have hbaseline :=
    reference_diffusion_at_sobolev_jet
      (E := E) (H := H) (M := M) (I := I) (n := n)
      c₀ g (e := e) he (r := r) (U := U) hr hEU hleft β
      (a fref 0 zref) ha0
  have hs0 := reference_circle_uniform_solutions_le_of_coefficients (n := n)
    (c₀.pullbackMetric (g 0)) (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
  have hs1 := hs0 J P F G S hδ.le hR δcap
  have hs2 := hs1 a b Ca Cb
  have hs3 := hs2 halip hblip hbaseline
  have hs4 := hs3 haclose hbclose hCa
  dsimp only [P, J₀, K₀, g₀, F, G, S] at hs4
  have hs5a := hs4 hrange
  have hs5b := hs5a haeval
  have hs5 := hs5b hbeval
  obtain ⟨ρ, hρ, hρR, alpha, reaction, hcoeff, hsol⟩ := hs5
  exact ⟨min δ δcap, ρ, lt_min hδ hδcap, hρ, min_le_right _ _, hρR.trans hRcap,
    alpha, reaction, hcoeff, hsol⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Set
open scoped Manifold
namespace DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TimeSobolev MaximalRegularity QuasiLinear
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem reference_solution_exists_continuousOn_representative
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (alpha : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    {ρ T : ℝ} (hT : 0 < T)
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : referenceCircleSolutionFacts g₀ f alpha reaction ρ hT u gforce) :
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let m : TensorHs g₀ 0 0 ((1 : ℕ) : ℝ) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) →L[ℝ]
        CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) :=
      coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
    let L : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (ι := Fin n)
      (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT
      (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) gforce
    ∃ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by norm_num) (w t) = u.toFun t) ∧
      w =ᵐ[timeMeasure T] (fun t => K (field t)) ∧
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) ∧ w 0 = 0 ∧
      (∀ᵐ t ∂timeMeasure T,
        L (field t) + gforce t = m (C (alpha t (w t))) (Q (f + field t)) +
          Cpi (reaction t (w t))) := by
  intro K C Cpi m Q L field
  rcases hfacts with ⟨_, hbound, hreal, htrace, _, _, heq⟩
  obtain ⟨w, hw, hlow, hfield, hwb, hwzero⟩ :=
    exists_continuousOn_bounded_intermediate_representative hT u field hreal hbound htrace
  refine ⟨w, hw, hlow, hfield, hwb, hwzero, ?_⟩
  filter_upwards [heq, hfield] with t ht he
  rw [he]
  exact ht

end DifferentialGeometry.Analysis.Parabolic
end

noncomputable section
open scoped Manifold ContDiff NNReal
open Set
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

open private CircleHsPi circleHsPiInclusion from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients

private theorem reference_coefficients_eq_at_translated_state
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ] CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (K : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ)
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : CircleHsPi g₀ (Fin n ⊕ Fin n) 1)
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hbase : u₀ = P f₀) (hJK : ∀ v, J (K v) = P v)
    {δ ρ : ℝ}
    (alpha : Metric.closedBall f₀ δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall f₀ δ → ℝ →
      CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    (hcoeff : referenceCircleCoefficientFacts g₀ f₀ P J F G S δ ρ alpha reaction)
    (f : Metric.closedBall f₀ δ)
    (w : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) (t : ℝ)
    (htρ : t ∈ Icc 0 ρ) (htC : t ∈ Icc 0 (ScalarVectorTimeCoefficients.radius C))
    (hw : ‖w‖ ≤ ρ)
    (hJ : ‖J (K (f.val - f₀) + w)‖ ≤ ScalarVectorTimeCoefficients.radius C) :
    alpha f t w = extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.diffusion C) t (J (K (f.val - f₀) + w)) ∧
    reaction f t w = extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.reaction C) t (J (K (f.val - f₀) + w)) := by
  have htranslated : u₀ + J (K (f.val - f₀) + w) = P f.val + J w := by
    rw [hbase, map_add, hJK, map_sub]
    abel
  have hz : J (K (f.val - f₀) + w) ∈ Metric.closedBall 0 (ScalarVectorTimeCoefficients.radius C) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hJ
  have hcoords (x : AddCircle (1 : ℝ)) :
      (fun i => match i with
        | none => 0 + t
        | some i => scalarH1ToContinuous g₀
            (u₀ i + (J (K (f.val - f₀) + w)) i) x) =
      (fun i => match i with
        | none => t
        | some i => scalarH1ToContinuous g₀ ((P f.val) i + (J w) i) x) := by
    funext i
    cases i with
    | none => exact zero_add t
    | some i =>
      change scalarH1ToContinuous g₀ ((u₀ + J (K (f.val - f₀) + w)) i) x =
        scalarH1ToContinuous g₀ ((P f.val + J w) i) x
      rw [htranslated]
  constructor
  · apply scalarH1ToContinuous_injective g₀
    apply ContinuousMap.ext
    intro x
    rw [hcoeff.2.1 f t htρ w hw x,
      extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t _ hz,
      (ScalarVectorTimeCoefficients.diffusion_eval C) t htC]
    exact congrArg F (hcoords x).symm
  · apply PiLp.ext
    intro j
    apply scalarH1ToContinuous_injective g₀
    apply ContinuousMap.ext
    intro x
    rw [hcoeff.2.2 f t htρ w hw x j,
      extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t _ hz,
      (ScalarVectorTimeCoefficients.reaction_eval C) t htC]
    exact congrArg (fun z => G z j) (hcoords x).symm

private theorem reference_coefficients_eq_ambient_at_translated_state
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J₀ := circleFirstJet (ι := Fin n) g₀
    let K₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi g₀ (Fin n) ((1 : ℝ) + 1) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    ∀ {δ ρ : ℝ}
      (alpha : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
      (reaction : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1),
      referenceCircleCoefficientFacts g₀ f₀ P J F G S δ ρ alpha reaction →
      ∀ (f : Metric.closedBall f₀ δ)
        (w : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) (t : ℝ),
      t ∈ Icc 0 ρ → t ∈ Icc 0 (ScalarVectorTimeCoefficients.radius C) → ‖w‖ ≤ ρ →
      ‖J (K (f.val - f₀) + w)‖ ≤ (ScalarVectorTimeCoefficients.radius C) →
      alpha f t w = extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (f.val - f₀) + w)) ∧
      reaction f t w = extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (f.val - f₀) + w)) := by
  intro g₀ f₀ J₀ K₀ P J K F G S C δ ρ alpha reaction hcoeff f w t htρ htC hw hJ
  have hJK (v : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) : J (K v) = P v := by
    simpa only [J, K, P, J₀, K₀, circleHsPiInclusion, map_zero, zero_add] using
      reference_jet_add_correction_eq g₀ 0 v
  have hbase : ambientFirstJet c₀ (g 0) e he = P f₀ :=
    (ambientFirstJet_eq_initialJet c₀ (g 0) he).trans (hJK f₀)
  exact reference_coefficients_eq_at_translated_state g₀ f₀ P J K F G S
    (ambientFirstJet c₀ (g 0) e he) C hbase hJK alpha reaction hcoeff f w t htρ htC hw hJ

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal
open MeasureTheory Filter Set
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem eventually_coefficients_comp_eq_of_state_eq
    {A X Y Z Y' Z' : Type*} {l : Filter A} {s : Set A}
    {w v : A → X} (hstate : w =ᶠ[l] v) (hs : ∀ᶠ t in l, t ∈ s)
    (F₁ : A → X → Y) (F₂ : A → X → Z) (G₁ : A → Y) (G₂ : A → Z)
    (L₁ : Y → Y') (L₂ : Z → Z') (a : A → Y') (b : A → Z')
    (ha : a =ᶠ[l] (fun t => L₁ (G₁ t)))
    (hb : b =ᶠ[l] (fun t => L₂ (G₂ t)))
    (hcoeff : ∀ t ∈ s, F₁ t (w t) = G₁ t ∧ F₂ t (w t) = G₂ t) :
    a =ᶠ[l] (fun t => L₁ (F₁ t (v t))) ∧
    b =ᶠ[l] (fun t => L₂ (F₂ t (v t))) := by
  have hpair : ∀ᶠ t in l,
      L₁ (G₁ t) = L₁ (F₁ t (v t)) ∧ L₂ (G₂ t) = L₂ (F₂ t (v t)) := by
    filter_upwards [hstate, hs] with t hwt ht
    obtain ⟨h₁, h₂⟩ := hcoeff t ht
    rw [hwt] at h₁ h₂
    exact ⟨congrArg L₁ h₁.symm, congrArg L₂ h₂.symm⟩
  exact ⟨ha.trans (hpair.mono (fun _ h => h.1)), hb.trans (hpair.mono (fun _ h => h.2))⟩

private theorem reference_coefficient_lifts_with_margin_at_ae_state
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J₀ := circleFirstJet (ι := Fin n) g₀
    let K₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi g₀ (Fin n) ((1 : ℝ) + 1) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let HP := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    let C₁ := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    ∀ {δ ρ T : ℝ}, T ≤ ρ → ρ ≤ ScalarVectorTimeCoefficients.radius C →
      ∀ (alpha : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
        (reaction : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1),
      referenceCircleCoefficientFacts g₀ f₀ P J F G S δ ρ alpha reaction →
      ∀ (f : Metric.closedBall f₀ δ)
        (field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T)
        (w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)),
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
      (∀ t ∈ Icc 0 T, ‖J (K (f.val - f₀) + w t)‖ ≤ ScalarVectorTimeCoefficients.radius C) →
      (∃ (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
        (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T),
        (fun t => H (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => C₁ (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (f.val - f₀) + w t)))) ∧
        (fun t => HP (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => Cpi (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (K (f.val - f₀) + w t)))) ∧
        parameterDerivativeOperatorBoundsWithMargin (n := n) g₀ a₂ (3 / 4)) →
      ∃ (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
        (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T),
        (fun t => H (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => C₁ (alpha f t (K (field t)))) ∧
        (fun t => HP (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => Cpi (reaction f t (K (field t)))) ∧
        parameterDerivativeOperatorBoundsWithMargin (n := n) g₀ a₂ (3 / 4) := by
  intro g₀ f₀ J₀ K₀ P J K F G S H HP C₁ Cpi C δ ρ T hTρ hρC
    alpha reaction hcoeff f field w hwu hbound hJw hlifts
  obtain ⟨a₂, b₂, ha₂, hb₂, hab⟩ := hlifts
  dsimp only [C, g₀, f₀, J₀, K₀, P, J, K, F, G, S] at hcoeff hJw hρC
  have heq (t : ℝ) (htt : t ∈ Icc 0 T) :=
    reference_coefficients_eq_ambient_at_translated_state c₀ g ht he hr hEU hleft β hG
      alpha reaction hcoeff f (w t) t ⟨htt.1, htt.2.trans hTρ⟩
      ⟨htt.1, htt.2.trans (hTρ.trans hρC)⟩ (hbound t htt) (hJw t htt)
  have htmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  obtain ⟨haeq, hbeq⟩ := eventually_coefficients_comp_eq_of_state_eq hwu htmem
    (alpha f) (reaction f) _ _ (fun x => C₁ x) (fun x => Cpi x)
    (fun t => H (a₂ t)) (fun t => HP (b₂ t)) ha₂ hb₂ heq
  exact ⟨a₂, b₂, haeq, hbeq, hab⟩

private theorem reference_coefficients_h2_lifts_and_margin_of_continuous_state
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J₀ := circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℝ) + 1) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    ∃ δcap : ℝ, 0 < δcap ∧ ∀ {δ ρ : ℝ}, δ ≤ δcap → ρ ≤ δcap →
      ∀ (alpha : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs (c₀.pullbackMetric (g 0)) 0 0 1)
        (reaction : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) 1),
      referenceCircleCoefficientFacts (c₀.pullbackMetric (g 0)) f₀ P J F G S δ ρ alpha reaction →
      ∀ (f : Metric.closedBall f₀ δ) {T : ℝ} (hT : 0 < T), T ≤ ρ →
      ∀ (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
      let field := maximalRegularityDuhamelVectorField (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) → ‖gforce‖ ≤ ρ / 4 →
      ∃ a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∃ b₂ : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL (c₀.pullbackMetric (g 0)) 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha f t (K (field t)))) ∧
        (fun t => (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
            (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))) (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) (reaction f t (K (field t)))) ∧
        parameterDerivativeOperatorBoundsWithMargin (n := n) (c₀.pullbackMetric (g 0)) a₂ (3 / 4) := by
  intro f₀ J₀ K₀ P J K F G S
  obtain ⟨δcap, hδcap, hδC, _, hlift⟩ :=
    ambient_translated_coefficients_h2_and_margin c₀ g ht he hr hEU hleft β hG
  refine ⟨δcap, hδcap, ?_⟩
  intro δ ρ hδ hρ alpha reaction hcoeff f T hT hTρ gforce field w hw hwu hbound hforce
  have hf : ‖f.val - f₀‖ ≤ δcap :=
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using f.property : ‖f.val - f₀‖ ≤ δ).trans hδ
  obtain ⟨hJw, hlifts⟩ :=
    hlift f.val hf hT hTρ hρ gforce w hw hwu hbound hforce
  have htransfer := reference_coefficient_lifts_with_margin_at_ae_state c₀ g ht he hr hEU hleft β hG
    (δ := δ) (ρ := ρ) (T := T)
  dsimp only [f₀, J₀, K₀, P, J, K, F, G, S] at hcoeff
  exact htransfer hTρ (hρ.trans hδC) alpha reaction hcoeff
    f field w hwu hbound hJw hlifts


private theorem reference_coefficients_h2_lifts_and_margin_for_selected_solution
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J₀ := circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℝ) + 1) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    ∃ δcap : ℝ, 0 < δcap ∧ ∀ {δ ρ : ℝ}, δ ≤ δcap → ρ ≤ δcap →
      ∀ (alpha : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs (c₀.pullbackMetric (g 0)) 0 0 1)
        (reaction : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) 1),
      referenceCircleCoefficientFacts (c₀.pullbackMetric (g 0)) f₀ P J F G S δ ρ alpha reaction →
      ∀ (f : Metric.closedBall f₀ δ) {T : ℝ} (hT : 0 < T), T ≤ ρ →
      ∀ (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
        (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
      referenceCircleSolutionFacts (c₀.pullbackMetric (g 0)) f.val (alpha f) (reaction f) ρ hT u gforce →
      let field := maximalRegularityDuhamelVectorField (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∃ a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∃ b₂ : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL (c₀.pullbackMetric (g 0)) 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha f t (K (field t)))) ∧
        (fun t => (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
            (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))) (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) (reaction f t (K (field t)))) ∧
        parameterDerivativeOperatorBoundsWithMargin (n := n) (c₀.pullbackMetric (g 0)) a₂ (3 / 4) := by
  intro f₀ J₀ K₀ P J K F G S
  obtain ⟨δcap, hδcap, hlift⟩ :=
    reference_coefficients_h2_lifts_and_margin_of_continuous_state
      c₀ g ht he hr hEU hleft β hG
  refine ⟨δcap, hδcap, ?_⟩
  intro δ ρ hδ hρ alpha reaction hcoeff f T hT hTρ u gforce hfacts field
  obtain ⟨w, hw, _, hwu, hbound, _, _⟩ :=
    reference_solution_exists_continuousOn_representative (c₀.pullbackMetric (g 0)) f.val (alpha f) (reaction f)
      hT u gforce hfacts
  have hforce : ‖gforce‖ ≤ ρ / 4 := hfacts.2.2.2.2.2.1
  dsimp only [f₀, J₀, K₀, P, J, K, F, G, S] at hcoeff
  exact hlift hδ hρ alpha reaction hcoeff f hT hTρ gforce w hw hwu hbound hforce

private theorem reference_coefficients_h2_lifts_and_contraction_for_selected_solution
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J₀ := circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℝ) + 1) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    ∃ δcap : ℝ, 0 < δcap ∧ ∀ {δ ρ : ℝ}, δ ≤ δcap → ρ ≤ δcap →
      ∀ (alpha : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs (c₀.pullbackMetric (g 0)) 0 0 1)
        (reaction : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) 1),
      referenceCircleCoefficientFacts (c₀.pullbackMetric (g 0)) f₀ P J F G S δ ρ alpha reaction →
      ∀ (f : Metric.closedBall f₀ δ) {T : ℝ} (hT : 0 < T), T ≤ ρ →
      ∀ (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
        (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
      referenceCircleSolutionFacts (c₀.pullbackMetric (g 0)) f.val (alpha f) (reaction f) ρ hT u gforce →
      let field := maximalRegularityDuhamelVectorField (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∃ a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∃ b₂ : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL (c₀.pullbackMetric (g 0)) 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha f t (K (field t)))) ∧
        (fun t => (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
            (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))) (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) (reaction f t (K (field t)))) ∧
        parameterDerivativeOperatorBounds (n := n) (c₀.pullbackMetric (g 0)) a₂ := by
  intro f₀ J₀ K₀ P J K F G S
  obtain ⟨δcap, hδcap, hmargin⟩ :=
    reference_coefficients_h2_lifts_and_margin_for_selected_solution c₀ g ht he hr hEU hleft β hG
  refine ⟨δcap, hδcap, ?_⟩
  intro δ ρ hδ hρ alpha reaction hcoeff f T hT hTρ u gforce hfacts field
  obtain ⟨a₂, b₂, ha₂, hb₂, hmargin⟩ :=
    hmargin hδ hρ alpha reaction hcoeff f hT hTρ u gforce hfacts
  exact ⟨a₂, b₂, ha₂, hb₂, parameterDerivativeOperatorBounds_of_margin
    (c₀.pullbackMetric (g 0)) a₂ (by norm_num : (3 / 4 : ℝ) < 1) hmargin⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Spectral
open TensorHeatEquation TensorSpectral TimeSobolev MaximalRegularity QuasiLinear
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

open private parameterDerivativeOperatorBounds parameterDerivativeForcingFieldLift
  parameterDerivative_forcing_lift_of_contraction parameterDerivative_field_lift_of_forcing_lift from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity

private theorem reference_parameterDerivative_forcing_lift_of_h2_coefficients
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (alpha : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    {ρ T : ℝ} (hT : 0 < T)
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (hfacts : referenceCircleSolutionFacts g₀ f alpha reaction ρ hT u gforce) :
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let K₄ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2))
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (ι := Fin n)
      (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT
      (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) gforce
    K₄ f₄ = f →
    (fun t => H (a₂ t)) =ᵐ[timeMeasure T]
      (fun t => C (alpha t (K (field t)))) →
    (fun t => P (b₂ t)) =ᵐ[timeMeasure T]
      (fun t => Cpi (reaction t (K (field t)))) →
    parameterDerivativeOperatorBounds (n := n) g₀ a₂ →
    parameterDerivativeForcingFieldLift g₀ hT gforce := by
  intro K K₄ H P C Cpi field hf₄ ha hb hbounds
  obtain ⟨_, _, _, _, _, _, heq⟩ := hfacts
  obtain ⟨C₂h, C₂l, hC₂h, hC₂l, hsmallh, hsmalll⟩ := hbounds
  have hweak : ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (field t i) +
        gforce t i = scalarHsMul g₀ 1 (by norm_num) (H (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g₀ 1
            (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
              (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
                (f₄ i) + field t i)) + H (b₂ t i) := by
    filter_upwards [heq, ha, hb] with t ht hat hbt
    intro i
    have hbase := congrArg (fun v => v i) hf₄
    change tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2) (f₄ i) = f i at hbase
    rw [hbase]
    rw [← hat, ← hbt] at ht
    exact congrArg (fun v : CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) => v i) ht
  obtain ⟨FH, hFH⟩ := parameterDerivative_forcing_lift_of_contraction g₀ hT gforce
    f₄ a₂ b₂ C₂h C₂l hC₂h hC₂l hsmallh hsmalll hweak
  exact ⟨FH, hFH, parameterDerivative_field_lift_of_forcing_lift g₀ hT gforce FH hFH⟩

end DifferentialGeometry.Analysis.Parabolic
end

noncomputable section
open scoped Manifold ContDiff NNReal
open MeasureTheory Filter Set
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_parameterDerivative_for_selected_solution
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J₀ := circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℝ) + 1) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    ∃ δcap : ℝ, 0 < δcap ∧ ∀ {δ ρ : ℝ}, δ ≤ δcap → ρ ≤ δcap →
      ∀ (alpha : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs (c₀.pullbackMetric (g 0)) 0 0 1)
        (reaction : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) 1),
      referenceCircleCoefficientFacts (c₀.pullbackMetric (g 0)) f₀ P J F G S δ ρ alpha reaction →
      ∀ (f : Metric.closedBall f₀ δ)
        (f₄ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((2 : ℕ) : ℝ) + 2)),
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2))) f₄ = f.val →
      ∀ {T : ℝ} (hT : 0 < T), T ≤ ρ →
      ∀ (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
        (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
      referenceCircleSolutionFacts (c₀.pullbackMetric (g 0)) f.val (alpha f) (reaction f) ρ hT u gforce →
        parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce := by
  intro f₀ J₀ K₀ P J F G S
  obtain ⟨δcap, hδcap, hlift⟩ :=
    reference_coefficients_h2_lifts_and_contraction_for_selected_solution
      c₀ g ht he hr hEU hleft β hG
  refine ⟨δcap, hδcap, ?_⟩
  intro δ ρ hδ hρ alpha reaction hcoeff f f₄ hbase T hT hTρ u gforce hfacts
  obtain ⟨a₂, b₂, ha₂, hb₂, hab⟩ :=
    hlift hδ hρ alpha reaction hcoeff f hT hTρ u gforce hfacts
  exact reference_parameterDerivative_forcing_lift_of_h2_coefficients (c₀.pullbackMetric (g 0)) f.val f₄
    (alpha f) (reaction f) hT u gforce a₂ b₂ hfacts hbase ha₂ hb₂ hab

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal
open MeasureTheory Filter Set
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem ambient_reference_uniform_solutions_with_parameterDerivative
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J₀ := circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (1 + 1) := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
        (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    (∀ f v, P f + J (K v) = P (f + v)) ∧
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∃ alpha : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs (c₀.pullbackMetric (g 0)) 0 0 1,
      ∃ reaction : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) 1,
      referenceCircleCoefficientFacts (c₀.pullbackMetric (g 0)) f₀ P J F G S δ ρ alpha reaction ∧
      ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ ρ ∧
        ∀ (f : Metric.closedBall f₀ δ)
          (f₄ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((2 : ℕ) : ℝ) + 2)),
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
            (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2))) f₄ = f.val →
        ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
        ∃ (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
          referenceCircleSolutionFacts (c₀.pullbackMetric (g 0)) f.val (alpha f) (reaction f) ρ hT u gforce ∧
            parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce := by
  intro f₀ J₀ K₀ P J K F G S
  obtain ⟨δcap, hδcap, hlift⟩ :=
    reference_parameterDerivative_for_selected_solution c₀ g ht he hr hEU hleft β hG
  have hfamily := ambient_reference_uniform_solutions_le c₀ g ht he hr hEU hleft β hG
    δcap δcap hδcap hδcap
  dsimp only at hfamily
  obtain ⟨hadd, δ, ρ, hδ, hρ, hδcap', hρcap, alpha, reaction, hcoeff,
      T₀, hT₀, hT₀ρ, hsol⟩ := hfamily
  have hcoeff' : referenceCircleCoefficientFacts (c₀.pullbackMetric (g 0))
      f₀ P J F G S δ ρ alpha reaction := hcoeff
  dsimp only [f₀, J₀, K₀, P, J, K, F, G, S]
  refine ⟨?_, δ, ρ, hδ, hρ, alpha, reaction, ?_, T₀, hT₀, hT₀ρ, ?_⟩
  · exact hadd
  · exact hcoeff'
  · intro f f₄ hbase T hT hTT₀
    obtain ⟨u, gforce, hfacts⟩ := hsol f hT hTT₀
    have hfacts' : referenceCircleSolutionFacts (c₀.pullbackMetric (g 0))
        f.val (alpha f) (reaction f) ρ hT u gforce := hfacts
    refine ⟨u, gforce, hfacts', ?_⟩
    have hlift₀ := hlift hδcap' hρcap
    have hlift₁ := hlift₀ alpha reaction
    have hlift₂ := hlift₁ hcoeff'
    have hlift₃ := hlift₂ f f₄ hbase (T := T)
    have hlift₄ := hlift₃ hT (hTT₀.trans hT₀ρ)
    exact hlift₄ u gforce hfacts'

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end


noncomputable section

open Set Filter
open scoped Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem eventually_ambient_derivative_sub_lt {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (c : SmoothImmersion (I := I) (M := M)) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    let := smoothImmersionTopology e
    ∀ᶠ d in 𝓝 c, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv m (fun y : ℝ => e.map (d.map (y : AddCircle (1 : ℝ)))) x -
        iteratedDeriv m (fun y : ℝ => e.map (c.map (y : AddCircle (1 : ℝ)))) x‖ < ε := by
  let := smoothImmersionTopology e
  have hopen : IsOpen {d : SmoothImmersion (I := I) (M := M) |
      ∀ x ∈ Icc (0 : ℝ) 1,
        ‖iteratedDeriv m (fun y : ℝ => e.map (d.map (y : AddCircle (1 : ℝ)))) x -
          iteratedDeriv m (fun y : ℝ => e.map (c.map (y : AddCircle (1 : ℝ)))) x‖ < ε} :=
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨c, m, ε, hε, rfl⟩
  exact hopen.mem_nhds (by intro x hx; simpa only [sub_self, norm_zero] using hε)

private theorem continuous_of_ambient_derivative_bound {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {F : Type*} [NormedAddCommGroup F]
    (f : SmoothImmersion (I := I) (M := M) → F) (m : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ c d ε, 0 < ε →
      (∀ j ≤ m, ∀ x ∈ Icc (0 : ℝ) 1,
        ‖iteratedDeriv j (fun y : ℝ => e.map (d.map (y : AddCircle (1 : ℝ)))) x -
          iteratedDeriv j (fun y : ℝ => e.map (c.map (y : AddCircle (1 : ℝ)))) x‖ ≤ ε) →
      ‖f d - f c‖ ≤ C * ε) :
    @Continuous _ _ (smoothImmersionTopology e) inferInstance f := by
  let := smoothImmersionTopology e
  apply continuous_iff_continuousAt.mpr
  intro c
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hpos : 0 < C + 1 := by positivity
  have hδ : 0 < ε / (C + 1) := div_pos hε hpos
  have hevent : ∀ᶠ d in 𝓝 c, ∀ j ∈ Finset.range (m + 1),
      ∀ x ∈ Icc (0 : ℝ) 1,
        ‖iteratedDeriv j (fun y : ℝ => e.map (d.map (y : AddCircle (1 : ℝ)))) x -
          iteratedDeriv j (fun y : ℝ => e.map (c.map (y : AddCircle (1 : ℝ)))) x‖ <
            ε / (C + 1) := by
    apply (Finset.eventually_all _).mpr
    intro j _
    exact eventually_ambient_derivative_sub_lt e c j hδ
  filter_upwards [hevent] with d hd
  rw [dist_eq_norm]
  refine (hbound c d _ hδ ?_).trans_lt ?_
  · intro j hj x hx
    exact (hd j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)) x hx).le
  · calc
      C * (ε / (C + 1)) < (C + 1) * (ε / (C + 1)) :=
        mul_lt_mul_of_pos_right (by linarith) hδ
      _ = ε := mul_div_cancel₀ _ (ne_of_gt hpos)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem continuous_ccTensorToHs_ambientCoordinate {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (i : Fin N) :
    @Continuous _ _ (smoothImmersionTopology e) inferInstance
      (fun d : SmoothImmersion (I := I) (M := M) =>
        ccTensorToHs g 0 3 (scalarCc g (ambientCoordinate d e.map e.smooth i))) := by
  obtain ⟨C, hC, hbound⟩ := AddCircle.exists_norm_sub_ccTensorToHs_three_le_iteratedDeriv g
  apply CurveShortening.continuous_of_ambient_derivative_bound e _ 4 C hC
  intro c d ε hε hcd
  apply hbound _ _ ε hε.le
  intro j hj x hx
  simp only [scalar0_scalarCc]
  change |iteratedDeriv j (fun y : ℝ => e.map (d.map (y : AddCircle (1 : ℝ))) i) x -
    iteratedDeriv j (fun y : ℝ => e.map (c.map (y : AddCircle (1 : ℝ))) i) x| ≤ ε
  have hd : ContDiff ℝ ∞ (fun y : ℝ => e.map (d.map (y : AddCircle (1 : ℝ)))) :=
    contMDiff_iff_contDiff.mp (e.smooth.comp d.smooth)
  have hc : ContDiff ℝ ∞ (fun y : ℝ => e.map (c.map (y : AddCircle (1 : ℝ)))) :=
    contMDiff_iff_contDiff.mp (e.smooth.comp c.smooth)
  exact (PiLp.norm_iteratedDeriv_apply_sub_le
    (hd.of_le (by exact_mod_cast le_top)).contDiffAt (hc.of_le (by exact_mod_cast le_top)).contDiffAt i).trans (hcd j hj x hx)

private theorem continuous_toLp_ccTensorToHs_ambientCoordinate {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    @Continuous _ _ (smoothImmersionTopology e) inferInstance
      (fun d : SmoothImmersion (I := I) (M := M) =>
        WithLp.toLp 2 (fun i =>
          ccTensorToHs g 0 3 (scalarCc g (ambientCoordinate d e.map e.smooth i)))) := by
  let := smoothImmersionTopology e
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N => TensorHs g 0 0 3)).comp
    (continuous_pi fun i => continuous_ccTensorToHs_ambientCoordinate e g i)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private def fixedAmbientSobolev
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (d : SmoothImmersion (I := I) (M := M)) :
    PiLp 2 (fun _ : Fin N => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)) :=
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr g₀ (Fin N)
    (by norm_num : (3 : ℝ) = ((1 : ℕ) : ℝ) + 2)
    (WithLp.toLp 2 (fun i =>
      ccTensorToHs g₀ 0 3 (scalarCc g₀ (ambientCoordinate d e.map e.smooth i))))

private theorem continuous_fixedAmbientSobolev
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    @Continuous _ _ (smoothImmersionTopology e) inferInstance (fixedAmbientSobolev e g₀) := by
  let := smoothImmersionTopology e
  exact (DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr g₀ (Fin N)
    (by norm_num : (3 : ℝ) = ((1 : ℕ) : ℝ) + 2)).continuous.comp
      (continuous_toLp_ccTensorToHs_ambientCoordinate e g₀)

variable [IsManifold I ∞ M]

private theorem fixedAmbientSobolev_pullbackMetric_eq
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (c₀ : SmoothImmersion (I := I) (M := M)) (g : SmoothRiemannianMetric I M) :
    fixedAmbientSobolev e (c₀.pullbackMetric g) c₀ =
      ambientSobolev c₀ g e.map e.smooth (((1 : ℕ) : ℝ) + 2) := by
  apply PiLp.ext
  intro i
  change tensorHsCongrL (c₀.pullbackMetric g) 0 0
      (by norm_num : (3 : ℝ) = ((1 : ℕ) : ℝ) + 2)
      (ccTensorToHs (c₀.pullbackMetric g) 0 3
        (scalarCc (c₀.pullbackMetric g) (ambientCoordinate c₀ e.map e.smooth i))) = _
  exact tensorHsCongrL_ccTensorToHs (c₀.pullbackMetric g) _ _

private theorem exists_isOpen_fixedAmbientSobolev_mem_closedBall
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (c₀ : SmoothImmersion (I := I) (M := M)) (g : SmoothRiemannianMetric I M)
    {r : ℝ} (hr : 0 < r) :
    let := smoothImmersionTopology e
    ∃ U : Set (SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ c₀ ∈ U ∧ ∀ d ∈ U,
        fixedAmbientSobolev e (c₀.pullbackMetric g) d ∈
          Metric.closedBall (ambientSobolev c₀ g e.map e.smooth (((1 : ℕ) : ℝ) + 2)) r := by
  let := smoothImmersionTopology e
  let f₀ := ambientSobolev c₀ g e.map e.smooth (((1 : ℕ) : ℝ) + 2)
  refine ⟨(fixedAmbientSobolev e (c₀.pullbackMetric g)) ⁻¹' Metric.ball f₀ r,
    (continuous_fixedAmbientSobolev e (c₀.pullbackMetric g)).isOpen_preimage _ Metric.isOpen_ball,
    ?_, ?_⟩
  · change fixedAmbientSobolev e (c₀.pullbackMetric g) c₀ ∈ Metric.ball f₀ r
    rw [fixedAmbientSobolev_pullbackMetric_eq]
    exact Metric.mem_ball_self hr
  · intro d hd
    exact Metric.ball_subset_closedBall hd

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private def fixedAmbientSobolevFourth
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (d : SmoothImmersion (I := I) (M := M)) :
    PiLp 2 (fun _ : Fin N => TensorHs g₀ 0 0 (((2 : ℕ) : ℝ) + 2)) :=
  WithLp.toLp 2 (fun i => ccTensorToHs g₀ 0 (((2 : ℕ) : ℝ) + 2)
    (scalarCc g₀ (ambientCoordinate d e.map e.smooth i)))

private theorem fixedAmbientSobolevFourth_inclusion
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (d : SmoothImmersion (I := I) (M := M)) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : Fin N =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)))
      (fixedAmbientSobolevFourth e g₀ d) = fixedAmbientSobolev e g₀ d := by
  apply PiLp.ext
  intro i
  change tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2) (ccTensorToHs g₀ 0 (((2 : ℕ) : ℝ) + 2)
      (scalarCc g₀ (ambientCoordinate d e.map e.smooth i))) =
    tensorHsCongrL g₀ 0 0 (by norm_num : (3 : ℝ) = ((1 : ℕ) : ℝ) + 2)
      (ccTensorToHs g₀ 0 3 (scalarCc g₀ (ambientCoordinate d e.map e.smooth i)))
  rw [tensorHsInclusion_ccTensorToHs, tensorHsCongrL_ccTensorToHs]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal
open MeasureTheory Filter Set
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_parameterDerivative_for_smooth_initial_solution
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) n)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e.map ⊆ U) (hleft : ∀ p, r (e.map p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr)) :
    let f₀ := ambientSobolev c₀ (g 0) e.map e.smooth (((1 : ℕ) : ℝ) + 2)
    let J₀ := circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℝ) + 1) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr) β
    ∃ δcap : ℝ, 0 < δcap ∧ ∀ {δ ρ : ℝ}, δ ≤ δcap → ρ ≤ δcap →
      ∀ (alpha : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs (c₀.pullbackMetric (g 0)) 0 0 1)
        (reaction : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) 1),
      referenceCircleCoefficientFacts (c₀.pullbackMetric (g 0)) f₀ P J F G S δ ρ alpha reaction →
      ∀ (d : SmoothImmersion (I := I) (M := M))
        (hd : fixedAmbientSobolev e (c₀.pullbackMetric (g 0)) d ∈ Metric.closedBall f₀ δ),
      let f : Metric.closedBall f₀ δ := ⟨fixedAmbientSobolev e (c₀.pullbackMetric (g 0)) d, hd⟩
      ∀ {T : ℝ} (hT : 0 < T), T ≤ ρ →
      ∀ (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
        (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
      referenceCircleSolutionFacts (c₀.pullbackMetric (g 0)) f.val (alpha f) (reaction f) ρ hT u gforce →
        parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce := by
  intro f₀ J₀ K₀ P J F G S
  obtain ⟨δcap, hδcap, hlift⟩ :=
    reference_parameterDerivative_for_selected_solution c₀ g ht e.smooth hr hEU hleft β hG
  refine ⟨δcap, hδcap, ?_⟩
  intro δ ρ hδ hρ alpha reaction hcoeff d hd f T hT hTρ u gforce hfacts
  exact hlift hδ hρ alpha reaction hcoeff f (fixedAmbientSobolevFourth e (c₀.pullbackMetric (g 0)) d)
    (fixedAmbientSobolevFourth_inclusion e (c₀.pullbackMetric (g 0)) d) hT hTρ u gforce hfacts

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal
open MeasureTheory Filter Set
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem ambient_reference_uniform_solutions_on_smooth_neighborhood
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) n)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e.map ⊆ U) (hleft : ∀ p, r (e.map p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr)) :
    let f₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) := ambientSobolev c₀ (g 0) e.map e.smooth (((1 : ℕ) : ℝ) + 2)
    let J₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (1 + 1) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n ⊕ Fin n) 1 := circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (1 + 1) := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
        (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n ⊕ Fin n) 1  := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr) β
    (∀ f v, P f + J (K v) = P (f + v)) ∧
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∃ alpha : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs (c₀.pullbackMetric (g 0)) 0 0 1,
      ∃ reaction : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) 1,
      referenceCircleCoefficientFacts (c₀.pullbackMetric (g 0)) f₀ P J F G S δ ρ alpha reaction ∧
      ∃ V : Set (SmoothImmersion (I := I) (M := M)),
        @IsOpen _ (smoothImmersionTopology e) V ∧ c₀ ∈ V ∧
        ∃ hV : ∀ d ∈ V, fixedAmbientSobolev e (c₀.pullbackMetric (g 0)) d ∈ Metric.closedBall f₀ δ,
        ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ ≤ ρ ∧
          ∀ (d : V) {T : ℝ} (hT : 0 < T), T ≤ T₀ →
          ∃ (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
            (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
            referenceCircleSolutionFacts (c₀.pullbackMetric (g 0)) (fixedAmbientSobolev e (c₀.pullbackMetric (g 0)) d.val)
              (alpha ⟨fixedAmbientSobolev e (c₀.pullbackMetric (g 0)) d.val, hV d.val d.property⟩)
              (reaction ⟨fixedAmbientSobolev e (c₀.pullbackMetric (g 0)) d.val, hV d.val d.property⟩)
              ρ hT u gforce ∧ parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce := by
  intro f₀ J₀ K₀ P J K F G S
  obtain ⟨hadd, δ, ρ, hδ, hρ, alpha, reaction, hcoeff, T₀, hT₀, hT₀ρ, hfamily⟩ :=
    ambient_reference_uniform_solutions_with_parameterDerivative
      c₀ g ht e.smooth hr hEU hleft β hG
  obtain ⟨V, hVopen, hc₀, hV⟩ :=
    exists_isOpen_fixedAmbientSobolev_mem_closedBall e c₀ (g 0) hδ
  refine ⟨hadd, δ, ρ, hδ, hρ, alpha, reaction, hcoeff,
    V, hVopen, hc₀, hV, T₀, hT₀, hT₀ρ, ?_⟩
  intro d T hT hTT₀
  exact hfamily ⟨fixedAmbientSobolev e (c₀.pullbackMetric (g 0)) d.val, hV d.val d.property⟩
    (fixedAmbientSobolevFourth e (c₀.pullbackMetric (g 0)) d.val)
    (fixedAmbientSobolevFourth_inclusion e (c₀.pullbackMetric (g 0)) d.val) hT hTT₀

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem lp_eq_of_continuousLinearMap_ae_eq
    {X Y Ω : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Ω]
    {p : ℝ≥0∞} {μ : Measure Ω}
    (D : X →L[ℝ] Y) (hD : Function.Injective D)
    (u v : Lp X p μ) (h : ∀ᵐ t ∂μ, D (u t) = D (v t)) : u = v := by
  apply Lp.ext
  filter_upwards [h] with t ht
  exact hD ht

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
end

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem timeL2_tensorHs_eq_of_inclusion_ae_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a a' : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (h : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a t) =
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a' t)) :
    a = a' := by
  apply TimeSobolev.lp_eq_of_continuousLinearMap_ae_eq
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))
    (tensorHsInclusion_injective (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))
    a a' h

private theorem timeL2_piLp_eq_of_inclusion_ae_eq
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ}
    (b b' : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T)
    (h : ∀ᵐ t ∂timeMeasure T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion (g := g)
        (r := 0) (s := 0) (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))) (b t) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion (g := g)
        (r := 0) (s := 0) (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))) (b' t)) :
    b = b' := by
  apply TimeSobolev.lp_eq_of_continuousLinearMap_ae_eq
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion (g := g)
      (r := 0) (s := 0) (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))) ?_ b b' h
  intro x y hxy
  apply PiLp.ext
  intro i
  apply tensorHsInclusion_injective (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
  exact congrArg (fun z => z i) hxy


private theorem timeL2_parameter_coefficient_pair_eq_of_inclusion_ae_eq
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a a' : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b b' : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T)
    (ha : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a t) =
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a' t))
    (hb : ∀ᵐ t ∂timeMeasure T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion (g := g)
        (r := 0) (s := 0) (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))) (b t) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion (g := g)
        (r := 0) (s := 0) (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))) (b' t)) :
    a = a' ∧ b = b' := by
  exact ⟨timeL2_tensorHs_eq_of_inclusion_ae_eq g a a' ha,
    timeL2_piLp_eq_of_inclusion_ae_eq g b b' hb⟩

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open private vectorTensorHsNormedSpace from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.ShiftedCoefficients
open scoped Manifold ContDiff NNReal
open MeasureTheory Set Filter
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_coefficients_h2_norm_le_for_selected_solution
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J₀ := circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℝ) + 1) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    ∃ δcap : ℝ, 0 < δcap ∧ ∃ A B : ℝ≥0, ∀ {δ ρ : ℝ}, δ ≤ δcap → ρ ≤ δcap →
      ∀ (alpha : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs (c₀.pullbackMetric (g 0)) 0 0 1)
        (reaction : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) 1),
      referenceCircleCoefficientFacts (c₀.pullbackMetric (g 0)) f₀ P J F G S δ ρ alpha reaction →
      ∀ (f : Metric.closedBall f₀ δ) {T : ℝ} (hT : 0 < T), T ≤ ρ →
      ∀ (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
        (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
      referenceCircleSolutionFacts (c₀.pullbackMetric (g 0)) f.val (alpha f) (reaction f) ρ hT u gforce →
      let field := maximalRegularityDuhamelVectorField (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∃ a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∃ b₂ : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL (c₀.pullbackMetric (g 0)) 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha f t (K (field t)))) ∧
        (fun t => (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
            (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))) (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) (reaction f t (K (field t)))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) ∧
        ‖b₂‖ ≤ B * (Real.sqrt T + (1 + T) * ρ / 4) := by
  intro f₀ J₀ K₀ P J K F G S
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  obtain ⟨δ₀, hδ₀, hδ₀C, _, A, B, hlift⟩ :=
    ambient_coefficients_h2_norm_le_of_translated_state c₀ g ht he hr hEU hleft β hG
  let δcap := min (δ₀ / 2)
    (ScalarVectorTimeCoefficients.radius C / (2 * (1 + ‖J‖)))
  have hδcap : 0 < δcap := by
    have hC := ScalarVectorTimeCoefficients.radius_pos C
    dsimp only [δcap]
    positivity
  have hcaphalf : δcap ≤ δ₀ / 2 := min_le_left _ _
  have hcapC : δcap ≤ ScalarVectorTimeCoefficients.radius C :=
    (hcaphalf.trans (by linarith only [hδ₀])).trans hδ₀C
  have hcapJ : 2 * ‖J‖ * δcap ≤ ScalarVectorTimeCoefficients.radius C := by
    have hp := (le_div_iff₀ (by positivity : 0 < 2 * (1 + ‖J‖))).mp
      (min_le_right (δ₀ / 2)
        (ScalarVectorTimeCoefficients.radius C / (2 * (1 + ‖J‖))))
    change δcap * (2 * (1 + ‖J‖)) ≤ ScalarVectorTimeCoefficients.radius C at hp
    nlinarith only [hp, hδcap]
  refine ⟨δcap, hδcap, A, B, ?_⟩
  intro δ ρ hδ hρ alpha reaction hcoeff f T hT hTρ u gforce hfacts field
  obtain ⟨w, hw, _, hwu, hbound, _, _⟩ :=
    reference_solution_exists_continuousOn_representative
      (c₀.pullbackMetric (g 0)) f.val (alpha f) (reaction f) hT u gforce hfacts
  have hforce : ‖gforce‖ ≤ ρ / 4 := hfacts.2.2.2.2.2.1
  have hf : ‖f.val - f₀‖ ≤ δcap :=
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using f.property :
      ‖f.val - f₀‖ ≤ δ).trans hδ
  obtain ⟨_, hJw⟩ := translated_state_norm_bounds K J
    (ContinuousLinearMap.norm_piLpMap_le _ zero_le_one
      (fun _ => tensorHsInclusion_opNorm_le_one _))
    hcapJ (f.val - f₀) hf (Icc 0 T) w
    (fun t htt => (hbound t htt).trans hρ)
  obtain ⟨a₂, b₂, ha₂, hb₂, hanorm, hbnorm⟩ :=
    hlift f.val (hf.trans hcaphalf) hT hTρ (hρ.trans hcaphalf)
      gforce w hw hwu hbound hforce
  have hρC := hρ.trans hcapC
  dsimp only [C, f₀, J₀, K₀, P, J, K, F, G, S] at hcoeff hJw hρC
  have heq (t : ℝ) (htt : t ∈ Icc 0 T) :=
    reference_coefficients_eq_ambient_at_translated_state c₀ g ht he hr hEU hleft β hG
      alpha reaction hcoeff f (w t) t ⟨htt.1, htt.2.trans hTρ⟩
      ⟨htt.1, htt.2.trans (hTρ.trans hρC)⟩ (hbound t htt) (hJw t htt)
  have htmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T :=
    ae_restrict_mem measurableSet_Icc
  refine ⟨a₂, b₂, ?_, ?_, hanorm, hbnorm⟩
  · filter_upwards [ha₂, hwu, htmem] with t hat hwt htt
    obtain ⟨haeq, _⟩ := heq t htt
    rw [← hwt]
    exact hat.trans (congrArg (tensorHsCongrL (c₀.pullbackMetric (g 0)) 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))) haeq.symm)
  · filter_upwards [hb₂, hwu, htmem] with t hbt hwt htt
    obtain ⟨_, hbeq⟩ := heq t htt
    rw [← hwt]
    exact hbt.trans (congrArg (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))) hbeq.symm)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open private affineHeatLift weakParameterEquation principalOperatorHigh principalOperatorLow
  driftOperatorHigh driftOperatorLow memLp_parameterDrift_high memLp_parameterDrift_low
  coefficientContractionBound normalizeZeroPi from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleLinearizedLift
open scoped Manifold ContDiff NNReal ENNReal
open MeasureTheory Filter Set
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
attribute [local instance] DifferentialGeometry.Analysis.Parabolic.vectorTensorHsNormedSpace
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem reference_parameterDerivative_weakEquation_of_h2_coefficients
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (alpha : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin n) 1)
    {ρ T : ℝ} (hT : 0 < T)
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (hfacts : referenceCircleSolutionFacts g₀ f alpha reaction ρ hT u gforce) :
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let K₄ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2))
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    let C := tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (ι := Fin n)
      (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT
      (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) gforce
    K₄ f₄ = f →
    (fun t => H (a₂ t)) =ᵐ[timeMeasure T]
      (fun t => C (alpha t (K (field t)))) →
    (fun t => P (b₂ t)) =ᵐ[timeMeasure T]
      (fun t => Cpi (reaction t (K (field t)))) →
    weakParameterEquation g₀ hT gforce f₄ a₂ b₂ := by
  intro K K₄ H P C Cpi field hf₄ ha hb
  obtain ⟨_, _, _, _, _, _, heq⟩ := hfacts
  have hweak : ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (field t i) +
        gforce t i = scalarHsMul g₀ 1 (by norm_num) (H (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g₀ 1
            (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
              (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
                (f₄ i) + field t i)) + H (b₂ t i) := by
    filter_upwards [heq, ha, hb] with t ht hat hbt
    intro i
    have hbase := congrArg (fun v => v i) hf₄
    change tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2) (f₄ i) = f i at hbase
    rw [hbase]
    rw [← hat, ← hbt] at ht
    exact congrArg (fun v : CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) => v i) ht
  exact hweak

private theorem parameterDerivative_forcing_lift_norm_le_of_margin
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (hbounds : parameterDerivativeOperatorBoundsWithMargin (n := n) g₀ a₂ (3 / 4))
    (hweak : weakParameterEquation g₀ hT gforce f₄ a₂ b₂) :
    ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      affineHeatLift (ι := Fin n) g₀ hT (principalOperatorHigh g₀ a₂) (driftOperatorHigh g₀ a₂)
        (AddCircle.parameterDerivativeBaselineForcingLp g₀ f₄ a₂ b₂)
        (parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce) FH ∧
      ‖FH‖ ≤ ‖AddCircle.parameterDerivativeBaselineForcingHsPi g₀ f₄‖ *
        (‖a₂‖ + ‖b₂‖) / (1 - (3 / 4 : ℝ)) := by
  obtain ⟨C₂h, C₂l, hC₂h, hC₂l, hmargin, hsmalll⟩ := hbounds
  apply exists_parameterDerivativeDuhamelForcing_lift_norm_le g₀ hT gforce
    f₄ a₂ b₂ C₂h C₂l (3 / 4) (by norm_num) hC₂h hC₂l
    (by erw [Lp.norm_toLp]; exact hmargin)
    (by change _ + _ * ‖_‖ < (1 : ℝ); erw [Lp.norm_toLp]; exact hsmalll)
  exact hweak

private theorem parameterDerivative_forcing_lift_norm_le_of_coefficient_bounds
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (A B R : ℝ)
    (hbounds : parameterDerivativeOperatorBoundsWithMargin (n := n) g₀ a₂ (3 / 4))
    (hweak : weakParameterEquation g₀ hT gforce f₄ a₂ b₂)
    (hanorm : ‖a₂‖ ≤ A * R) (hbnorm : ‖b₂‖ ≤ B * R) :
    ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce =
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := g₀) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
              2 (timeMeasure T) FH ∧
      ‖FH‖ ≤ 4 * ‖AddCircle.parameterDerivativeBaselineForcingHsPi g₀ f₄‖ * (A + B) * R := by
  obtain ⟨FH, hFH, hnorm⟩ := parameterDerivative_forcing_lift_norm_le_of_margin
    g₀ hT gforce f₄ a₂ b₂ hbounds hweak
  refine ⟨FH, hFH.2, hnorm.trans ?_⟩
  calc
    _ ≤ ‖AddCircle.parameterDerivativeBaselineForcingHsPi g₀ f₄‖ *
        (A * R + B * R) / (1 - (3 / 4 : ℝ)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hanorm hbnorm) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

private theorem reference_coefficients_h2_margin_and_norm_le_for_selected_solution
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J₀ := circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℝ) + 1) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    ∃ δcap : ℝ, 0 < δcap ∧ ∃ A B : ℝ≥0, ∀ {δ ρ : ℝ}, δ ≤ δcap → ρ ≤ δcap →
      ∀ (alpha : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs (c₀.pullbackMetric (g 0)) 0 0 1)
        (reaction : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) 1),
      referenceCircleCoefficientFacts (c₀.pullbackMetric (g 0)) f₀ P J F G S δ ρ alpha reaction →
      ∀ (f : Metric.closedBall f₀ δ) {T : ℝ} (hT : 0 < T), T ≤ ρ →
      ∀ (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
        (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
      referenceCircleSolutionFacts (c₀.pullbackMetric (g 0)) f.val (alpha f) (reaction f) ρ hT u gforce →
      let field := maximalRegularityDuhamelVectorField (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∃ a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∃ b₂ : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL (c₀.pullbackMetric (g 0)) 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha f t (K (field t)))) ∧
        (fun t => (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
            (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))) (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) (reaction f t (K (field t)))) ∧
        parameterDerivativeOperatorBoundsWithMargin (n := n) (c₀.pullbackMetric (g 0)) a₂ (3 / 4) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) ∧
        ‖b₂‖ ≤ B * (Real.sqrt T + (1 + T) * ρ / 4) := by
  intro f₀ J₀ K₀ P J K F G S
  obtain ⟨δm, hδm, hliftm⟩ :=
    reference_coefficients_h2_lifts_and_margin_for_selected_solution
      c₀ g ht he hr hEU hleft β hG
  obtain ⟨δn, hδn, A, B, hliftn⟩ :=
    reference_coefficients_h2_norm_le_for_selected_solution
      c₀ g ht he hr hEU hleft β hG
  refine ⟨min δm δn, lt_min hδm hδn, A, B, ?_⟩
  intro δ ρ hδ hρ alpha reaction hcoeff f T hT hTρ u gforce hfacts field
  obtain ⟨a₂, b₂, ha₂, hb₂, hab⟩ :=
    hliftm (hδ.trans (min_le_left _ _)) (hρ.trans (min_le_left _ _))
      alpha reaction hcoeff f hT hTρ u gforce hfacts
  obtain ⟨a₂', b₂', ha₂', hb₂', hanorm, hbnorm⟩ :=
    hliftn (hδ.trans (min_le_right _ _)) (hρ.trans (min_le_right _ _))
      alpha reaction hcoeff f hT hTρ u gforce hfacts
  obtain ⟨haeq, hbeq⟩ := timeL2_parameter_coefficient_pair_eq_of_inclusion_ae_eq
    (c₀.pullbackMetric (g 0)) a₂ a₂' b₂ b₂' (ha₂.trans ha₂'.symm) (hb₂.trans hb₂'.symm)
  rw [← haeq] at hanorm
  rw [← hbeq] at hbnorm
  exact ⟨a₂, b₂, ha₂, hb₂, hab, hanorm, hbnorm⟩

private def parameterDerivativeForcingLiftBound
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (A B R : ℝ) : Prop :=
  ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
    parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce =
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
            2 (timeMeasure T) FH ∧
    ‖FH‖ ≤ 4 * ‖AddCircle.parameterDerivativeBaselineForcingHsPi g₀ f₄‖ * (A + B) * R

private theorem reference_parameterDerivative_forcing_lift_norm_le_for_selected_solution
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J₀ := circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℝ) + 1) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
    ∃ δcap : ℝ, 0 < δcap ∧ ∃ A B : ℝ≥0, ∀ {δ ρ : ℝ}, δ ≤ δcap → ρ ≤ δcap →
      ∀ (alpha : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs (c₀.pullbackMetric (g 0)) 0 0 1)
        (reaction : Metric.closedBall f₀ δ → ℝ →
          CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) 1),
      referenceCircleCoefficientFacts (c₀.pullbackMetric (g 0)) f₀ P J F G S δ ρ alpha reaction →
      ∀ (f : Metric.closedBall f₀ δ)
        (f₄ : CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((2 : ℕ) : ℝ) + 2)),
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2))) f₄ = f.val →
      ∀ {T : ℝ} (hT : 0 < T), T ≤ ρ →
      ∀ (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
        (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
      referenceCircleSolutionFacts (c₀.pullbackMetric (g 0)) f.val (alpha f) (reaction f) ρ hT u gforce →
      parameterDerivativeForcingLiftBound (c₀.pullbackMetric (g 0))
        hT gforce f₄ A B (Real.sqrt T + (1 + T) * ρ / 4) := by
  intro f₀ J₀ K₀ P J F G S
  obtain ⟨δcap, hδcap, A, B, hlift⟩ :=
    reference_coefficients_h2_margin_and_norm_le_for_selected_solution
      c₀ g ht he hr hEU hleft β hG
  refine ⟨δcap, hδcap, A, B, ?_⟩
  intro δ ρ hδ hρ alpha reaction hcoeff f f₄ hbase T hT hTρ u gforce hfacts
  obtain ⟨a₂, b₂, ha₂, hb₂, hab, hanorm, hbnorm⟩ :=
    hlift hδ hρ alpha reaction hcoeff f hT hTρ u gforce hfacts
  have hweak := reference_parameterDerivative_weakEquation_of_h2_coefficients
    (c₀.pullbackMetric (g 0)) f.val f₄ (alpha f) (reaction f) hT u gforce a₂ b₂
      hfacts hbase ha₂ hb₂
  exact parameterDerivative_forcing_lift_norm_le_of_coefficient_bounds
    (c₀.pullbackMetric (g 0)) hT gforce f₄ a₂ b₂ A B
      (Real.sqrt T + (1 + T) * ρ / 4) hab hweak hanorm hbnorm

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end
