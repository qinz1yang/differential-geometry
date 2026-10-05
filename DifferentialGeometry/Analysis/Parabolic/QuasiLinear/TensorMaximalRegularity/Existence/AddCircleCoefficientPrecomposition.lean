import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.CoefficientPrecomposition
import DifferentialGeometry.Analysis.FunctionalAnalysis.ContinuousLinearMap.PiLp
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Basic.ExponentCongruence
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacian
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.Multiplication

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev (scalarCc)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {ι : Type*} [Fintype ι]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private local instance vectorTensorHsNormedSpace
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (a : ℝ) :
    NormedSpace ℝ (PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) := inferInstance

private def circleScalarHsMul
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (hk : Module.finrank ℝ ℝ / 2 + 1 ≤ k) :
    TensorHs g 0 0 (k : ℝ) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (k : ℝ)) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 (k : ℝ)) :=
  (ContinuousLinearMap.piLpMapL 2).comp
    (ContinuousLinearMap.pi (fun _ : ι => scalarHsMul g k hk))

private def circleDriftHsMul
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (k : ℝ)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (k : ℝ)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    appHs g 0 0 k (scalarCc g (AddCircle.laplacianDriftCoefficient g)))

private def circleTensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {a b : ℝ} (hab : a ≤ b) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 b) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 a) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
      (g := g) (r := 0) (s := 0) hab)

private theorem circle_laplacian_principal_add_drift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (hk : Module.finrank ℝ ℝ / 2 + 1 ≤ k)
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))) :
    have m := circleScalarHsMul (ι := ι) g k hk
    have q := ccTensorToHs g 0 (k : ℝ)
      (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    have d := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 k (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
    have Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g k
    have D := AddCircle.parameterDerivativeHsPi (ι := ι) g k
    have K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (k : ℝ) + 1 ≤ (k : ℝ) + 2 by linarith))
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (k : ℝ)) v =
      m q (Q v) + d (D (K v)) := by
  intro m q d Q D K
  have hq : m q = ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 k (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))) := by
    change ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      scalarHsMul g k hk
        (ccTensorToHs g 0 (k : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g)))) = _
    rw [scalarHsMul_apply_ccTensorToHs_left]
  rw [AddCircle.piLpMap_tensorScaleLaplacian_eq_principal_add_drift]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  rw [hq]

theorem circle_laplacian_add_shifted_remainder
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (hk : Module.finrank ℝ ℝ / 2 + 1 ≤ k)
    (f v : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2)))
    (alpha : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) → TensorHs g 0 0 (k : ℝ))
    (reaction : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) → PiLp 2 (fun _ : ι => TensorHs g 0 0 (k : ℝ))) (t : ℝ) :
    let m := (ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi (fun _ : ι => scalarHsMul g k hk))
    let q := ccTensorToHs g 0 (k : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 k (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g k
    let D := AddCircle.parameterDerivativeHsPi (ι := ι) g k
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (k : ℝ) + 1 ≤ (k : ℝ) + 2 by linarith))
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) (k : ℝ)) v +
      shiftedRemainder m Q J D d q alpha reaction f t v =
      m (alpha t (J v)) (Q (f + v)) + reaction t (J v) := by
  intro m q d Q D J
  have hbase := circle_laplacian_principal_add_drift (ι := ι) g k hk v
  rw [hbase]
  exact shifted_remainder_operator_identity m Q J D d q alpha reaction f t v

theorem circle_shifted_equation_ae
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (hk : Module.finrank ℝ ℝ / 2 + 1 ≤ k)
    (f : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2)))
    (alpha : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) →
      TensorHs g 0 0 (k : ℝ))
    (reaction : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) →
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (k : ℝ)))
    {T R : ℝ} (hR : 0 ≤ R)
    (field : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))) T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (k : ℝ))) T) :
    let m := (ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi (fun _ : ι => scalarHsMul g k hk))
    let q := ccTensorToHs g 0 (k : ℝ)
      (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 k (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g k
    let D := AddCircle.parameterDerivativeHsPi (ι := ι) g k
    let K : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2)) →L[ℝ]
        PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (k : ℝ) + 1 ≤ (k : ℝ) + 2 by linarith))
    let hz : (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2))) ∈
        {v | ‖K v‖ ≤ R} := by
      simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR
    (∀ᵐ t ∂timeMeasure T, field t ∈ {v | ‖K v‖ ≤ R}) →
    (F =ᵐ[timeMeasure T] fun t =>
      shiftedRemainder m Q K D d q alpha reaction f t (aeSetLift hz field t)) →
    ∀ᵐ t ∂timeMeasure T,
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorScaleLaplacian (g := g) (r := 0) (s := 0) (k : ℝ)) (field t) + F t =
        m (alpha t (K (field t))) (Q (f + field t)) + reaction t (K (field t)) := by
  intro m q d Q D K hz hstate hforce
  have hlift := aeSetLift_coe_ae hz field hstate
  filter_upwards [hforce, hlift] with t ht htval
  change F t = shiftedRemainder m Q K D d q alpha reaction f t (aeSetLift hz field t).val at ht
  rw [htval] at ht
  rw [ht]
  exact circle_laplacian_add_shifted_remainder g k hk f (field t) alpha reaction t

theorem exists_uniform_time_precomposed_circle_solutions
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (hk : Module.finrank ℝ ℝ / 2 + 1 ≤ k)
    {σ : ℝ} (hσ : σ = (k : ℝ))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2)))
    (J : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) →L[ℝ] V)
    {δ R ρ : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R)
    (hρeq : ρ = R / (1 + ‖J‖)) :
    have hJρ : ‖J‖ * ρ ≤ R := by
      rw [hρeq, ← mul_div_assoc]
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith [hR.le])
    ∀ (b₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (alpha₀ : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → TensorHs g 0 0 σ)
    (reaction₀ : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (alpha : Metric.closedBall f₀ δ → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) → TensorHs g 0 0 σ)
    (reaction : Metric.closedBall f₀ δ → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) → PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (Ca Cb : ℝ≥0)
    (ha : ∀ f, LipschitzWith Ca
      (fun z : ℝ × Metric.closedBall (0 : V) R => alpha₀ f z.1 z.2))
    (hb : ∀ f, LipschitzWith Cb
      (fun z : ℝ × Metric.closedBall (0 : V) R => reaction₀ f z.1 z.2))
    (haclose : ∀ f t, t ∈ Icc (0 : ℝ) R → ∀ z,
      ‖alpha₀ f t z - ccTensorToHs g 0 σ
        (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))‖ ≤ (Ca : ℝ) * (2 * R))
    (hbclose : ∀ f t, t ∈ Icc (0 : ℝ) R → ∀ z,
      ‖reaction₀ f t z - b₀‖ ≤ (Cb : ℝ) * (2 * R))
    (halpha : ∀ f t, t ∈ Icc (0 : ℝ) ρ → ∀ z : Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) ρ,
      alpha f t z = alpha₀ f t (J.closedBallMap hJρ z))
    (hbeta : ∀ f t, t ∈ Icc (0 : ℝ) ρ → ∀ z : Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) ρ,
      reaction f t z = reaction₀ f t (J.closedBallMap hJρ z))
    (hCa : have m := (ContinuousLinearMap.piLpMapL 2).comp (ContinuousLinearMap.pi (fun _ : ι => scalarHsMul g k hk));
      have Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g k;
      (Ca : ℝ) * R ≤ 1 / (32 * (‖m‖ * ‖Q‖ + 1))),
    have C := tensorHsCongr g 0 0 hσ
    have Cpi := LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => tensorHsCongr g 0 0 hσ)
    have m := (ContinuousLinearMap.piLpMapL 2).comp
      (ContinuousLinearMap.pi (fun _ : ι => scalarHsMul g k hk))
    have q := C (ccTensorToHs g 0 σ (scalarCc g (AddCircle.laplacianPrincipalCoefficient g)))
    have d := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 k (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
    have Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g k
    have D := AddCircle.parameterDerivativeHsPi (ι := ι) g k
    have beta := fun f t z => C (alpha f t z)
    have gamma := fun f t z => Cpi (reaction f t z)
    have hρ : 0 < ρ := by rw [hρeq]; exact div_pos hR (by positivity)
    have K := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (show (k : ℝ) + 1 ≤ (k : ℝ) + 2 by linarith))
    have N := fun f t (v : {v : PiLp 2 (fun _ : ι => TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 ((k : ℝ) + 2)) |
      ‖K v‖ ≤ ρ}) => shiftedRemainder m Q K D d q (beta f) (gamma f) f t v
    have Bconst : ℝ≥0 := ‖m‖₊ * (Ca * ‖J‖₊) * (‖Q f₀‖ + ‖Q‖ * δ).toNNReal + (Cb * ‖J‖₊) + ‖d‖₊ * ‖D‖₊
    have D₀ := ‖m‖ * (‖q‖ + ((2 * Ca * (1 + ‖J‖₊)) : ℝ) * ρ) * (‖Q f₀‖ + ‖Q‖ * δ) +
      ‖Cpi b₀‖ + ((2 * Cb * (1 + ‖J‖₊)) : ℝ) * ρ
    ∃ T₀ : ℝ,
      T₀ = min ρ (min 1 (min (1 / (64 * ((Bconst : ℝ) + 1) ^ 2))
        (((ρ / 4) / (2 * (D₀ + 1))) ^ 2))) ∧
      0 < T₀ ∧ T₀ ≤ ρ ∧ ∀ (f : Metric.closedBall f₀ δ) {T : ℝ} (hT : 0 < T), T ≤ T₀ →
      ∃ (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 (k : ℝ))) T)
        (gforce : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 (k : ℝ))) T),
        have field := maximalRegularityDuhamelVectorField hT
          (0 : PiLp 2 (fun _ : ι => TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 ((k : ℝ) + 2))) gforce
        u = maximalRegularityDuhamelVectorMap hT
            (0 : PiLp 2 (fun _ : ι => TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 ((k : ℝ) + 2))) gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖K v‖ ≤ ρ}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N f t (aeSetLift
            (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 ((k : ℝ) + 2))) ∈
              {v | ‖K v‖ ≤ ρ} by
                simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hρ.le) field t)) ∧
          u.toFunL2 =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
              (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (show (k : ℝ) ≤ (k : ℝ) + 2 by linarith))).compLpL
                2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (k : ℝ))).compLpL
                2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ ρ / 4 ∧
          (∀ᵐ t ∂timeMeasure T,
            ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                tensorScaleLaplacian (g := g) (r := 0) (s := 0) (k : ℝ)) (field t) +
              gforce t =
              m (beta f t
                (K (field t))) (Q (f.val + field t)) +
                gamma f t (K (field t))) := by
  cases hσ
  intro hJρ b₀ alpha₀ reaction₀ alpha reaction Ca Cb ha hb haclose hbclose halpha hbeta hCa C Cpi m q d Q D beta gamma hρ K N Bconst D₀
  have hsolution :=
    exists_uniform_time_precomposed_vector (ι := ι) (E := ℝ) (H := ℝ)
      (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
      (A := TensorHs g 0 0 (k : ℝ)) (V := V) (δ := δ) (R := R) (ρ := ρ)
      g 0 0 (k : ℝ) m Q D d q (Cpi b₀) f₀ J hδ hR hρeq
      alpha₀ reaction₀ beta gamma Ca Cb ha hb haclose hbclose halpha hbeta
      hCa
  refine Exists.elim hsolution ?_
  intro T₀ hfacts
  have hT₀eq := hfacts.1
  have hT₀ := hfacts.2.1
  have hT₀ρ := hfacts.2.2.1
  have hsol := hfacts.2.2.2
  refine ⟨T₀, hT₀eq, hT₀, hT₀ρ, ?_⟩
  intro f T hT hTT₀
  refine Exists.elim (hsol f hT hTT₀) ?_
  intro u hforces
  refine Exists.elim hforces ?_
  intro gforce hsolutionFacts
  have hu := hsolutionFacts.1
  have hstate := hsolutionFacts.2.1
  have hforce := hsolutionFacts.2.2.1
  have hreal := hsolutionFacts.2.2.2.1
  have htrace := hsolutionFacts.2.2.2.2.1
  have hderiv := hsolutionFacts.2.2.2.2.2.1
  have hnorm := hsolutionFacts.2.2.2.2.2.2
  refine ⟨u, ?_⟩
  refine ⟨gforce, ?_⟩
  refine And.intro hu ?_
  refine And.intro hstate ?_
  refine And.intro hforce ?_
  refine And.intro hreal ?_
  refine And.intro htrace ?_
  refine And.intro hderiv ?_
  refine And.intro hnorm ?_
  exact circle_shifted_equation_ae (ι := ι) g k hk f.val (beta f) (gamma f) hρ.le
    (maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
      (g := g) (r := 0) (s := 0) (a := (k : ℝ)) hT 0 gforce) gforce hstate hforce

theorem exists_uniform_time_precomposed_circle_translated_solutions_lipschitz
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (hk : Module.finrank ℝ ℝ / 2 + 1 ≤ k)
    {σ : ℝ} (hσ : σ = (k : ℝ))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2)))
    (J : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) →L[ℝ] V)
    {δ R ρ : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R)
    (hρeq : ρ = R / (1 + ‖J‖)) :
    have hJρ : ‖J‖ * ρ ≤ R := by
      rw [hρeq, ← mul_div_assoc]
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith [hR.le])
    ∀ (b₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (alpha₀ : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → TensorHs g 0 0 σ)
    (reaction₀ : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (alpha : Metric.closedBall f₀ δ → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) → TensorHs g 0 0 σ)
    (reaction : Metric.closedBall f₀ δ → ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) → PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (P : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 2)) →L[ℝ] V)
    (Ca Cb : ℝ≥0)
    (ha : ∀ f, LipschitzWith Ca
      (fun z : ℝ × Metric.closedBall (0 : V) R => alpha₀ f z.1 z.2))
    (hb : ∀ f, LipschitzWith Cb
      (fun z : ℝ × Metric.closedBall (0 : V) R => reaction₀ f z.1 z.2))
    (haclose : ∀ f t, t ∈ Icc (-R) R → ∀ z,
      ‖alpha₀ f t z - ccTensorToHs g 0 σ
        (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))‖ ≤ (Ca : ℝ) * (2 * R))
    (hbclose : ∀ f t, t ∈ Icc (-R) R → ∀ z,
      ‖reaction₀ f t z - b₀‖ ≤ (Cb : ℝ) * (2 * R))
    (halpha : ∀ f t, t ∈ Icc (-ρ) ρ → ∀ z : Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) ρ,
      alpha f t z = alpha₀ f t (J.closedBallMap hJρ z))
    (hbeta : ∀ f t, t ∈ Icc (-ρ) ρ → ∀ z : Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) ρ,
      reaction f t z = reaction₀ f t (J.closedBallMap hJρ z))
    (haparam : ∀ f l t s z, ‖alpha₀ f t z - alpha₀ l s z‖ ≤
      (Ca : ℝ) * max |t - s| ‖P (f.val - l.val)‖)
    (hbparam : ∀ f l t s z, ‖reaction₀ f t z - reaction₀ l s z‖ ≤
      (Cb : ℝ) * max |t - s| ‖P (f.val - l.val)‖)
    (hCa : have m := circleScalarHsMul (ι := ι) g k hk;
      have Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g k;
      (Ca : ℝ) * R ≤ 1 / (32 * (‖m‖ * ‖Q‖ + 1))),
    have C := tensorHsCongr g 0 0 hσ
    have Cpi := LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => tensorHsCongr g 0 0 hσ)
    have m := circleScalarHsMul (ι := ι) g k hk
    have q := C (ccTensorToHs g 0 σ (scalarCc g (AddCircle.laplacianPrincipalCoefficient g)))
    have d := circleDriftHsMul (ι := ι) g k
    have Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g k
    have D := AddCircle.parameterDerivativeHsPi (ι := ι) g k
    have beta := fun f t z => C (alpha f t z)
    have gamma := fun f t z => Cpi (reaction f t z)
    have hρ : 0 < ρ := by rw [hρeq]; exact div_pos hR (by positivity)
    have K := circleTensorHsInclusion (ι := ι) g
      (show (k : ℝ) + 1 ≤ (k : ℝ) + 2 by linarith)
    have Cq := ‖Q f₀‖ + ‖Q‖ * δ
    have A₀ := (‖q‖ + ((2 * Ca * (1 + ‖J‖₊)) : ℝ) * ρ).toNNReal
    have Hparam : ℝ≥0 := max 1 ‖P‖₊
    have K₁ := ‖m‖₊ * Ca * Hparam * ‖Q‖₊
    have K₀ := ‖m‖₊ * A₀ * ‖Q‖₊ + ‖m‖₊ * Ca * Hparam * Cq.toNNReal +
      Cb * Hparam
    have N := fun (p : (Icc (-ρ / 4) (ρ / 4) × Metric.closedBall f₀ δ)) t
      (v : {v : PiLp 2 (fun _ : ι => TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 ((k : ℝ) + 2)) |
      ‖K v‖ ≤ ρ}) => shiftedRemainder m Q K D d q
        (fun t z => beta p.2 ((p.1 : ℝ) + t) z)
        (fun t z => gamma p.2 ((p.1 : ℝ) + t) z) p.2 t v
    have Bconst : ℝ≥0 := ‖m‖₊ * (Ca * ‖J‖₊) * (‖Q f₀‖ + ‖Q‖ * δ).toNNReal + (Cb * ‖J‖₊) + ‖d‖₊ * ‖D‖₊
    have D₀ := ‖m‖ * (‖q‖ + ((2 * Ca * (1 + ‖J‖₊)) : ℝ) * ρ) * (‖Q f₀‖ + ‖Q‖ * δ) +
      ‖Cpi b₀‖ + ((2 * Cb * (1 + ‖J‖₊)) : ℝ) * ρ
    ∃ T₀ : ℝ,
      T₀ = min (ρ / 4) (min 1 (min (1 / (64 * ((Bconst : ℝ) + 1) ^ 2))
        (((ρ / 4) / (2 * (D₀ + 1))) ^ 2))) ∧
      0 < T₀ ∧ T₀ ≤ ρ / 4 ∧ ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
      have κ := (‖m‖ * (2 * Ca * (1 + ‖J‖₊)) * ‖Q‖) * ρ * (1 + T) +
        (Bconst : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
        2 * (‖m‖ * (Ca * ‖J‖₊) * ‖Q‖) * (ρ / 4) * Real.sqrt (1 + T) * (1 + T)
      ∃ (u : (Icc (-ρ / 4) (ρ / 4) × Metric.closedBall f₀ δ) → timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 (k : ℝ))) T)
        (gforce : (Icc (-ρ / 4) (ρ / 4) × Metric.closedBall f₀ δ) → timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 (k : ℝ))) T),
        LipschitzWith
          ((K₁ * (1 + T).toNNReal * (ρ / 4).toNNReal + (Real.sqrt T).toNNReal * K₀) /
            (1 - κ).toNNReal) gforce ∧
        LipschitzWith
          (2 * ((K₁ * (1 + T).toNNReal * (ρ / 4).toNNReal + (Real.sqrt T).toNNReal * K₀) /
            (1 - κ).toNNReal)) u ∧
        ∀ f,
        have field := maximalRegularityDuhamelVectorField hT
          (0 : PiLp 2 (fun _ : ι => TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 ((k : ℝ) + 2))) (gforce f)
        u f = maximalRegularityDuhamelVectorMap hT
            (0 : PiLp 2 (fun _ : ι => TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 ((k : ℝ) + 2))) (gforce f) ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖K v‖ ≤ ρ}) ∧
          gforce f =ᵐ[timeMeasure T] (fun t => N f t (aeSetLift
            (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0 ((k : ℝ) + 2))) ∈
              {v | ‖K v‖ ≤ ρ} by
                simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hρ.le) field t)) ∧
          (u f).toFunL2 =
            (circleTensorHsInclusion (ι := ι) g
              (show (k : ℝ) ≤ (k : ℝ) + 2 by linarith)).compLpL
                2 (timeMeasure T) field ∧
          timeH1.trace0 _ T (u f) = 0 ∧
          timeH1.timeDeriv _ T (u f) =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (k : ℝ))).compLpL
                2 (timeMeasure T) field + gforce f ∧
          ‖gforce f‖ ≤ ρ / 4 ∧
          (∀ᵐ t ∂timeMeasure T,
            ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                tensorScaleLaplacian (g := g) (r := 0) (s := 0) (k : ℝ)) (field t) +
              gforce f t =
              m (beta f.2 ((f.1 : ℝ) + t)
                (K (field t))) (Q (f.2.val + field t)) +
                gamma f.2 ((f.1 : ℝ) + t) (K (field t))) := by
  cases hσ
  intro hJρ b₀ alpha₀ reaction₀ alpha reaction P Ca Cb ha hb haclose hbclose halpha hbeta haparam hbparam hCa C Cpi m q d Q D beta gamma hρ K Cq A₀ Hparam K₁ K₀ N Bconst D₀
  have hproducer := exists_uniform_time_precomposed_translated_vector_solutions_lipschitz
    (ι := ι) (E := ℝ) (H := ℝ) (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
    (A := TensorHs g 0 0 (k : ℝ)) (V := V) (δ := δ) (R := R) (ρ := ρ)
    g 0 0 (k : ℝ) m Q D d q (Cpi b₀) f₀ J hδ hR hρeq
  have hcoefficients := hproducer
    alpha₀ reaction₀ beta gamma P Ca Cb ha hb haclose hbclose halpha hbeta
    haparam hbparam hCa
  have hsolution := hcoefficients
    (circle_laplacian_principal_add_drift (ι := ι) g k hk)
  exact hsolution

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
