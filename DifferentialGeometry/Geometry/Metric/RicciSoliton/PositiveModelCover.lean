import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PositiveRoundness
import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceIdentities
import DifferentialGeometry.Geometry.Metric.Sphere.TwoDimensionalQuotient

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric MeasureTheory
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem normalizedGradientRicciSoliton_potential_eq_one_of_compact_of_finrank_eq_two_of_constant_sectional_curvature
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hsec : ∀ x : M, ∀ v w : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x v w w v =
        (1 / 2 : Real) * (g.inner x v v * g.inner x w w -
          g.inner x v w * g.inner x v w)) :
    ∀ x : M, f x = 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : NeZero (Module.finrank Real E) := ⟨by omega⟩
  have hscalar : ∀ x : M,
      metricScalarAt (I := I) (M := M) g x = 1 := by
    intro x
    let i : Fin (Module.finrank Real E) := ⟨0, by omega⟩
    let v : TangentSpace I x := smoothOrthoFrame (I := I) g x i x
    have hv : g.inner x v v = 1 := by
      simpa only [v, i, if_pos] using
        smoothOrthoFrame_orthonormal_at_center (I := I) g x i i
    have hRicDim :=
      ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two
        (I := I) g hdim x v v
    have hRicSec := Curvature.ricci_of_sec (I := I) g (1 / 2 : Real)
      hsec x v v
    rw [hdim, hRicDim, hv] at hRicSec
    norm_num at hRicSec
    linarith
  have hlap : ∀ x : M, ΔG (I := I) g f x = 0 := by
    intro x
    have htrace := gradientRicciSoliton_trace (I := I) h.2.1 x
    have hrhs : (Module.finrank Real E : Real) * 1 / 2 = 1 := by
      rw [hdim]
      norm_num
    rw [hscalar x, hrhs] at htrace
    apply add_left_cancel (a := (1 : Real))
    simpa only [add_zero] using htrace
  let mu : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have henergy : ∫ x, normGradSqFun (I := I) g f x ∂mu = 0 := by
    have hgreen :=
      green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
        (I := I) g f.contMDiff f.contMDiff
          (HasCompactSupport.of_compactSpace _)
    change ∫ x, normGradSqFun (I := I) g f x ∂mu =
        -∫ x, f x * ΔG (I := I) g f x ∂mu at hgreen
    rw [show (∫ x, f x * ΔG (I := I) g f x ∂mu) = 0 by
      apply integral_eq_zero_of_ae
      exact Filter.Eventually.of_forall fun x => by
        change f x * ΔG (I := I) g f x = (0 : Real)
        simp only [hlap x, mul_zero]] at hgreen
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
  have hnorm := congrFun hgradNorm x
  change g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g f x) = 0 at hnorm
  rw [hscalar x, hnorm] at hpotential
  linarith

theorem exists_roundTwoSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_two_of_constant_sectional_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hsec : ∀ x : M, ∀ v w : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x v w w v =
        (1 / 2 : Real) * (g.inner x v v * g.inner x w w -
          g.inner x v w * g.inner x v w)) :
    ∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 → M,
      solitonModelCovering roundTwoSphereShrinkerMetric
        roundTwoSphereShrinkerPotential g f cover ∧
      IsQuotientCoveringMap cover (coveringDeckGroup cover) := by
  obtain ⟨cover, hcoverLocal, hquotient, hcoverMetric⟩ :=
    exists_round_two_sphere_quotient_cover_of_constant_positive_sectional_curvature
      (I := I) (M := M) inferInstance inferInstance inferInstance hdim g
        (1 / 2) (by norm_num) hsec
  have hpotential :=
    normalizedGradientRicciSoliton_potential_eq_one_of_compact_of_finrank_eq_two_of_constant_sectional_curvature
      (I := I) h hdim hsec
  refine ⟨cover, ?_, hquotient⟩
  refine ⟨normalizedGradientRicciSoliton_roundTwoSphere, h,
    hcoverLocal, hquotient.surjective, hquotient.isCoveringMap, ?_, ?_⟩
  · intro x v w
    have hmetric := hcoverMetric x v w
    rw [scaleMetric_inner] at hmetric
    rw [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric,
      scaleMetric_inner]
    norm_num [roundSphereShrinkerRadius] at hmetric ⊢
    linarith
  · intro x
    rw [roundTwoSphereShrinkerPotential_apply, hpotential (cover x)]

theorem exists_roundTwoSphere_solitonModelCovering_of_compact_of_finrank_eq_two_of_constant_sectional_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hsec : ∀ x : M, ∀ v w : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x v w w v =
        (1 / 2 : Real) * (g.inner x v v * g.inner x w w -
          g.inner x v w * g.inner x v w)) :
    ∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 → M,
      solitonModelCovering roundTwoSphereShrinkerMetric
        roundTwoSphereShrinkerPotential g f cover := by
  obtain ⟨cover, hcover, _⟩ :=
    exists_roundTwoSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_two_of_constant_sectional_curvature
      (I := I) (M := M) h hdim hsec
  exact ⟨cover, hcover⟩

theorem exists_roundThreeSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_three_of_sectional_pos
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v) :
    ∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric
        roundThreeSphereShrinkerPotential g f cover ∧
      IsQuotientCoveringMap cover (coveringDeckGroup cover) := by
  have hround :=
    gradientRicciSoliton_constant_sectional_curvature_of_compact_of_finrank_eq_three_of_sectional_pos
      (I := I) (M := M) h.2.1 hdim hsec
  obtain ⟨cover, hcoverLocal, hquotient, hcoverMetric⟩ :=
    exists_round_three_sphere_quotient_cover_of_constant_positive_sectional_curvature
      (I := I) (M := M) inferInstance inferInstance inferInstance hdim g
        (1 / 4) (by norm_num) (by simpa using hround)
  have hpotential :=
    normalizedGradientRicciSoliton_potential_eq_three_div_two_of_compact_of_finrank_eq_three_of_sectional_pos
      (I := I) (M := M) h hdim hsec
  refine ⟨cover, ?_, hquotient⟩
  refine ⟨normalizedGradientRicciSoliton_roundThreeSphere, h,
    hcoverLocal, hquotient.surjective, hquotient.isCoveringMap, ?_, ?_⟩
  · intro x v w
    have hmetric := hcoverMetric x v w
    rw [scaleMetric_inner] at hmetric
    rw [roundThreeSphereShrinkerMetric, roundSphereShrinkerMetric,
      scaleMetric_inner]
    norm_num [roundSphereShrinkerRadius] at hmetric ⊢
    linarith
  · intro x
    rw [roundThreeSphereShrinkerPotential_apply, hpotential (cover x)]

theorem exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_sectional_pos
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v) :
    ∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric
        roundThreeSphereShrinkerPotential g f cover := by
  obtain ⟨cover, hcover, _⟩ :=
    exists_roundThreeSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_three_of_sectional_pos
      (I := I) (M := M) h hdim hsec
  exact ⟨cover, hcover⟩

end DifferentialGeometry.Geometry
