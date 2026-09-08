import DifferentialGeometry.Geometry.Metric.RicciSoliton.CompactAnisotropy
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [I.Boundaryless]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem compact_positive_three_gradientRicciSoliton_einstein_scalar
    [CompactSpace M] [ConnectedSpace M] [Nonempty M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (h : gradientRicciSoliton (I := I) g f sigma)
    (hdim : Module.finrank Real E = 3)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v) :
    (∀ (x : M) (v w : TangentSpace I x),
      metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v w) =
        (metricScalarAt (I := I) (M := M) g x / 3) * g.inner x v w) ∧
      (∀ x : M,
        metricScalarAt (I := I) (M := M) g x = 3 * sigma / 2) := by
  have hdimAt (x : M) : Module.finrank Real (TangentSpace I x) = 3 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  have hscalar : ∀ x : M, 0 < metricScalarAt (I := I) (M := M) g x := by
    intro x
    exact metricScalarAt_pos_of_sectional_pos_of_finrank_eq_three
      (I := I) (M := M) g x (hdimAt x) (hsec x)
  have hdefect : ∀ x : M, ricciReactionDefectAt (I := I) g x = 0 :=
    gradientRicciSoliton_ricciReactionDefectAt_eq_zero_of_compact_of_finrank_eq_three
      (I := I) (M := M) h hscalar hdim
  have hEin : ∀ (x : M) (v w : TangentSpace I x),
      metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v w) =
        (metricScalarAt (I := I) (M := M) g x / 3) * g.inner x v w := by
    intro x
    exact metricRicciAt_eq_scalar_div_three_of_ricciReactionDefectAt_eq_zero_of_sectional_pos
      (I := I) (M := M) g x (hdimAt x) (hdefect x) (hsec x)
  have hdScalar :
      ∀ x : M, ∀ X : TangentSpace I x,
        differential1FormFun (I := I)
            (fun y : M => metricScalarAt (I := I) (M := M) g y)
            x (fun _ : Fin 1 => X) = 0 := by
    intro x X
    obtain ⟨basis, _lambda, _mu, _nu, horth, _hdiag⟩ :=
      exists_orthonormal_curvature_eigenframe
        (I := I) (M := M) g x (hdimAt x)
    have hinv : MetricInverseInBasisGen (I := I) g x basis delta3 :=
      orthonormal_invBasis3 (I := I) g basis horth
    exact dScalar_zero_ein3_at (I := I) (M := M) g basis delta3 hinv hEin X
  obtain ⟨R0, hR0⟩ :=
    metricScalar_const_of_dScalar_zero (I := I) (M := M) g hdScalar
  let mu : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  let _ : IsFiniteMeasure mu :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let _ : mu.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have hmuPos : 0 < mu.real univ := by
    apply ENNReal.toReal_pos
    · exact (isOpen_univ.measure_pos mu univ_nonempty).ne'
    · exact measure_ne_top mu univ
  have hf :
      (⟨fun x : M => f x, f.contMDiff⟩ : C^∞⟮I, M; Real⟯) = f := by
    ext x
    rfl
  have hlap :
      ∫ x, ΔG (I := I) g f x ∂mu = 0 := by
    simpa only [mu, hf] using
      laplacian_integral_eq_zero (I := I) (M := M) g f.contMDiff
  have hlapPoint (x : M) :
      ΔG (I := I) g f x = 3 * sigma / 2 - R0 := by
    have htrace := gradientRicciSoliton_trace (I := I) h x
    rw [hR0 x, hdim] at htrace
    norm_num at htrace ⊢
    linarith
  have hlapConst :
      ∫ x, ΔG (I := I) g f x ∂mu =
        mu.real univ * (3 * sigma / 2 - R0) := by
    calc
      ∫ x, ΔG (I := I) g f x ∂mu =
          ∫ _x : M, 3 * sigma / 2 - R0 ∂mu := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hlapPoint
      _ = mu.real univ * (3 * sigma / 2 - R0) := by
        rw [MeasureTheory.integral_const, smul_eq_mul]
  have hR0sigma : R0 = 3 * sigma / 2 := by
    rw [hlap] at hlapConst
    nlinarith
  exact ⟨hEin, fun x => by rw [hR0 x, hR0sigma]⟩

theorem gradientRicciSoliton_metricScalarAt_eq_three_mul_sigma_div_two_of_compact_of_finrank_eq_three_of_sectional_pos
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (h : gradientRicciSoliton (I := I) g f sigma)
    (hdim : Module.finrank Real E = 3)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v) :
    ∀ x : M, metricScalarAt (I := I) (M := M) g x = 3 * sigma / 2 := by
  cases isEmpty_or_nonempty M
  · intro x
    exact isEmptyElim x
  · exact (compact_positive_three_gradientRicciSoliton_einstein_scalar
      (I := I) (M := M) h hdim hsec).2

theorem normalizedGradientRicciSoliton_potential_eq_three_div_two_of_compact_of_finrank_eq_three_of_sectional_pos
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v) :
    ∀ x : M, f x = 3 / 2 := by
  cases isEmpty_or_nonempty M
  · intro x
    exact isEmptyElim x
  · have hscalar :=
      gradientRicciSoliton_metricScalarAt_eq_three_mul_sigma_div_two_of_compact_of_finrank_eq_three_of_sectional_pos
        (I := I) (M := M) h.2.1 hdim hsec
    have hlap (x : M) : ΔG (I := I) g f x = 0 := by
      have htrace := gradientRicciSoliton_trace (I := I) h.2.1 x
      rw [hscalar x, hdim] at htrace
      linarith
    let mu : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
    have henergy :
        ∫ x, normGradSqFun (I := I) g f x ∂mu = 0 := by
      have hgreen :=
        green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
          (I := I) g f.contMDiff f.contMDiff
            (HasCompactSupport.of_compactSpace _)
      change ∫ x, normGradSqFun (I := I) g f x ∂mu =
          -∫ x, f x * ΔG (I := I) g f x ∂mu at hgreen
      rw [show (∫ x, f x * ΔG (I := I) g f x ∂mu) = 0 by
        apply integral_eq_zero_of_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [Pi.zero_apply, hlap x, mul_zero]] at hgreen
      simpa using hgreen
    have henergyIntegrable : Integrable (normGradSqFun (I := I) g f) mu :=
      Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
        (I := I) g (normGradSqFun_continuous (I := I) g f.contMDiff)
          (HasCompactSupport.of_compactSpace _)
    have hae : normGradSqFun (I := I) g f =ᵐ[mu] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg
        (normGradSqFun_nonneg (I := I) g f) henergyIntegrable).mp henergy
    let _ : mu.IsOpenPosMeasure :=
      riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
    have hgradNorm : normGradSqFun (I := I) g f = 0 :=
      (Continuous.ae_eq_iff_eq mu
        (normGradSqFun_continuous (I := I) g f.contMDiff) continuous_const).mp hae
    intro x
    have hpotential := normalizedGradientRicciSoliton_potential_equation (I := I) h x
    have hnorm :
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) = 0 := by
      exact congrFun hgradNorm x
    rw [hscalar x, hnorm] at hpotential
    norm_num at hpotential ⊢
    linarith

theorem gradientRicciSoliton_constant_sectional_curvature_of_compact_of_finrank_eq_three_of_sectional_pos
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (h : gradientRicciSoliton (I := I) g f sigma)
    (hdim : Module.finrank Real E = 3)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v) :
    ∀ (x : M) (v w : TangentSpace I x),
      metricRm04StdAt (I := I) (M := M) g x v w w v =
        (sigma / 4) *
          (g.inner x v v * g.inner x w w -
            g.inner x v w * g.inner x v w) := by
  cases isEmpty_or_nonempty M
  · intro x
    exact isEmptyElim x
  · have hdimAt (x : M) : Module.finrank Real (TangentSpace I x) = 3 := by
      rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
      exact hdim
    obtain ⟨hEin, hscalar⟩ :=
      compact_positive_three_gradientRicciSoliton_einstein_scalar
        (I := I) (M := M) h hdim hsec
    intro x v w
    calc
      metricRm04StdAt (I := I) (M := M) g x v w w v =
          (metricScalarAt (I := I) (M := M) g x / 6) *
            (g.inner x v v * g.inner x w w -
              g.inner x v w * g.inner x v w) :=
        metricRm04StdAt_eq_scalar_div_six_of_finrank_eq_three_of_einstein
          (I := I) (M := M) g x (hdimAt x) (hEin x) v w
      _ = (sigma / 4) *
            (g.inner x v v * g.inner x w w -
              g.inner x v w * g.inner x v w) := by
        rw [hscalar x]
        ring

end DifferentialGeometry.Geometry
