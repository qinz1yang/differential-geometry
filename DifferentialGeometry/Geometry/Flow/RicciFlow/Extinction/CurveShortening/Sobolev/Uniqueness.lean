import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CurveRepresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication

open private
  ScalarVectorTimeCoefficients.radius
  ScalarVectorTimeCoefficients.radius_pos
  ScalarVectorTimeCoefficients.diffusionLipschitz
  ScalarVectorTimeCoefficients.reactionLipschitz
  ScalarVectorTimeCoefficients.diffusion
  ScalarVectorTimeCoefficients.reaction
  ScalarVectorTimeCoefficients.diffusion_lipschitz
  ScalarVectorTimeCoefficients.reaction_lipschitz
from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState


open private
  coordinateMultiplication
  DifferentialGeometry.Analysis.Parabolic.coordinateMultiplication
  shifted_circle_operator_identity
  DifferentialGeometry.Analysis.Parabolic.shifted_circle_operator_identity
  shifted_tame_estimate
  DifferentialGeometry.Analysis.Parabolic.shifted_tame_estimate
  CircleHsPi
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CircleHsPi
  circleHsPiInclusion
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.circleHsPiInclusion
  shiftedRemainder
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.shiftedRemainder
  extendClosedBall
  DifferentialGeometry.Analysis.Parabolic.extendClosedBall
  extendClosedBall_apply
  DifferentialGeometry.Analysis.Parabolic.extendClosedBall_apply
  extendClosedBall_bounds
  DifferentialGeometry.Analysis.Parabolic.extendClosedBall_bounds
  exists_small_coefficient_radius
  DifferentialGeometry.Analysis.Parabolic.exists_small_coefficient_radius
  circleHsPiCongr
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr
  circleHsPiCongr_apply
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr_apply
  circleHsPiCongr_norm
  DifferentialGeometry.Analysis.Parabolic.circleHsPiCongr_norm from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients

open private
  circleFirstJet
  DifferentialGeometry.Analysis.Parabolic.circleFirstJet
  ambientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ambientSobolev
  scalarH1ToContinuous_ambientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.scalarH1ToContinuous_ambientSobolev
  tensorHsCongrL_ccTensorToHs
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.tensorHsCongrL_ccTensorToHs
  ScalarVectorTimeCoefficients
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ScalarVectorTimeCoefficients
  ambientCoefficients
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ambientCoefficients
  initial_diffusion_coefficients
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.initial_diffusion_coefficients
  ambientCoefficients_eval_of_eq_circleFirstJet
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.ambientCoefficients_eval_of_eq_circleFirstJet from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState

open private
  scalarVectorTimeCoefficients_rhs_continuousOn
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.scalarVectorTimeCoefficients_rhs_continuousOn from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity

open private
  fixedAmbientSobolev
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.fixedAmbientSobolev from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions

open private
  exists_continuousOn_fixedAmbientSobolev_curve_with_initial
  DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion.exists_continuousOn_fixedAmbientSobolev_curve_with_initial from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CurveRepresentation

section
noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalarH1PiToContinuous_parameter_rhs
    {n : ℕ} (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (W : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (a : TensorHs g₀ 0 0 ((1 : ℕ) : ℝ))
    (b : CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) (x : ℝ) :
    let P := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    let f := fun y : ℝ => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P W) (y : AddCircle (1 : ℝ)))
    WithLp.toLp 2 (scalarH1PiToContinuous g₀ (S (m a (Q W) + b))
      (x : AddCircle (1 : ℝ))) =
        scalarH1ToContinuous g₀
          (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) a)
          (x : AddCircle (1 : ℝ)) • deriv (deriv f) x +
        WithLp.toLp 2 (scalarH1PiToContinuous g₀ (S b) (x : AddCircle (1 : ℝ))) := by
  intro P S Q m f
  let u := fun y : ℝ => scalarH1PiToContinuous g₀ (P W) (y : AddCircle (1 : ℝ))
  let L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap
  let W₃ := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2) W
  have hlo : ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) + 1)) W₃ = P W := by
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply (by norm_num) (by norm_num) (W i)).symm
  have hu : ContDiff ℝ 2 u := by
    have h := AddCircle.contDiff_two_scalarH1PiToContinuous g₀ W₃
    rw [hlo] at h
    exact h
  have hd (q : ℝ → (Fin n → ℝ)) (hq : Differentiable ℝ q) :
      deriv (fun y => L (q y)) = fun y => L (deriv q y) := by
    funext y
    exact (L.hasFDerivAt.comp_hasDerivAt y (hq y).hasDerivAt).deriv
  have hu₁ : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hsecond : deriv (deriv f) x = L (deriv (deriv u) x) := by
    change deriv (deriv (fun y => L (u y))) x = _
    rw [hd u (hu.differentiable (by norm_num)),
      hd (deriv u) (hu₁.differentiable (by norm_num))]
  have hu₂ : deriv (deriv u) x =
      scalarH1PiToContinuous g₀ (S (Q W)) (x : AddCircle (1 : ℝ)) :=
    AddCircle.deriv_deriv_scalarH1PiToContinuous g₀ W x
  rw [hsecond, hu₂]
  apply PiLp.ext
  intro i
  change scalarH1ToContinuous g₀
    (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
      (scalarHsMul g₀ 1 (by norm_num) a (Q W i) + b i)) _ = _
  rw [map_add, map_add, ContinuousMap.add_apply, scalarH1ToContinuous_scalarHsMul]
  rfl

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {n : ℕ}

variable (c₀ : SmoothImmersion (I := I) (M := M))
  (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht₀ : 0 ∈ D.regular)
  {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
  {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
  (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
  (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
  (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private theorem ambient_rhs_eval_of_h3_state :
    let C := ambientCoefficients c₀ g ht₀ he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    ∀ (t : ℝ) (_ : t ∈ Icc (0 : ℝ) (ScalarVectorTimeCoefficients.radius C))
      (W : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
      (_ : ‖J (K (W - f₀))‖ ≤ (ScalarVectorTimeCoefficients.radius C)),
      let alpha := tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W - f₀))))
      let reaction := circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (K (W - f₀))))
      let f := fun y : ℝ => WithLp.toLp 2
        (scalarH1PiToContinuous g₀ (P W) (y : AddCircle (1 : ℝ)))
      ∀ x : ℝ,
        (t, f x, deriv f x) ∈ curveShorteningChartFirstJetDomain D
          (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β ∧
        WithLp.toLp 2 (scalarH1PiToContinuous g₀ (S (m alpha (Q W) + reaction))
          (x : AddCircle (1 : ℝ))) =
          curveShorteningParametricChartRhs
            (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
            (t, f x, deriv f x, deriv (deriv f) x) := by
  intro C g₀ f₀ J K P S Q m t ht W hJW alpha reaction f x
  have hcoeff {a b : ℝ} (hab : a = b) (z : TensorHs g₀ 0 0 a) :
      (tensorHsCongr g₀ 0 0 hab z).coeff = z.coeff := by
    cases hab
    rfl
  let w₂ := circleHsPiCongr g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) (K (W - f₀))
  have hv : J (K (W - f₀)) ∈ Metric.closedBall 0 (ScalarVectorTimeCoefficients.radius C) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hJW
  let v : Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
        (ScalarVectorTimeCoefficients.radius C) :=
    ⟨J (K (W - f₀)), hv⟩
  have hvJ : v.val = circleFirstJet g₀ w₂ := rfl
  have hgeom := ambientCoefficients_eval_of_eq_circleFirstJet
    c₀ g ht₀ he hr hEU hleft β hG t ht w₂ v hvJ x
  have hw₂ (i : Fin n) :
      tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 1 + 1) (w₂ i) =
        (P (W - f₀)) i := by
    apply TensorHs.ext
    simp only [w₂, K, P, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
      circleHsPiCongr_apply, tensorHsInclusion_coeff, tensorHsCongrL_apply, hcoeff]
  have hF : f = fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ))) +
      WithLp.toLp 2 (fun i => scalarH1ToContinuous g₀
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 1 + 1) (w₂ i))
          (y : AddCircle (1 : ℝ))) := by
    funext y
    apply PiLp.ext
    intro i
    change scalarH1ToContinuous g₀ (P W i) (y : AddCircle (1 : ℝ)) =
      e (c₀.map (y : AddCircle (1 : ℝ))) i +
        scalarH1ToContinuous g₀
          (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 1 + 1) (w₂ i))
          (y : AddCircle (1 : ℝ))
    rw [hw₂, map_sub, PiLp.sub_apply, map_sub, ContinuousMap.sub_apply]
    have hbase := scalarH1ToContinuous_ambientSobolev c₀ (g 0) e he
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2) (y : AddCircle (1 : ℝ)) i
    change scalarH1ToContinuous g₀ (P f₀ i) (y : AddCircle (1 : ℝ)) = _ at hbase
    rw [hbase]
    ring
  have hgeom' : (t, f x, deriv f x) ∈ curveShorteningChartFirstJetDomain D
      (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β ∧
      scalarH1ToContinuous g₀ ((ScalarVectorTimeCoefficients.diffusion C) t v) (x : AddCircle (1 :
        ℝ)) =
        curveShorteningChartDiffusionCoefficient
          (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
          (t, f x, deriv f x) ∧
      ∀ i, scalarH1ToContinuous g₀ ((ScalarVectorTimeCoefficients.reaction C) t v i) (x :
        AddCircle (1 : ℝ)) =
        curveShorteningParametricChartReaction
          (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
          (t, f x, deriv f x) i := by
    simpa only [hF] using hgeom
  have ha : scalarH1ToContinuous g₀
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) alpha)
      (x : AddCircle (1 : ℝ)) =
      curveShorteningChartDiffusionCoefficient
        (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
        (t, f x, deriv f x) := by
    rw [← hgeom'.2.1]
    apply congrArg (fun z => scalarH1ToContinuous g₀ z (x : AddCircle (1 : ℝ)))
    apply TensorHs.ext
    simp only [alpha, extendClosedBall_apply _ _ _ _ hv,
      tensorHsInclusion_coeff, tensorHsCongrL_apply, hcoeff, v]
  have hb : WithLp.toLp 2 (scalarH1PiToContinuous g₀ (S reaction)
      (x : AddCircle (1 : ℝ))) =
      curveShorteningParametricChartReaction
        (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
        (t, f x, deriv f x) := by
    apply PiLp.ext
    intro i
    rw [← hgeom'.2.2 i]
    change scalarH1ToContinuous g₀ (S reaction i) (x : AddCircle (1 : ℝ)) = _
    apply congrArg (fun z => scalarH1ToContinuous g₀ z (x : AddCircle (1 : ℝ)))
    apply TensorHs.ext
    simp only [reaction, extendClosedBall_apply _ _ _ _ hv, S, circleHsPiInclusion,
      ContinuousLinearMap.piLpMap_apply, circleHsPiCongr_apply,
      tensorHsInclusion_coeff, tensorHsCongrL_apply, hcoeff, v]
  refine ⟨hgeom'.1, ?_⟩
  have hrhs := scalarH1PiToContinuous_parameter_rhs g₀ W alpha reaction x
  change WithLp.toLp 2 (scalarH1PiToContinuous g₀ (S (m alpha (Q W) + reaction))
    (x : AddCircle (1 : ℝ))) = _ at hrhs
  rw [ha, hb] at hrhs
  exact hrhs

private theorem ambient_rhs_eval_of_curve_state :
    let C := ambientCoefficients c₀ g ht₀ he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    ∀ (c : CurveMap M) (t : ℝ) (_ : t ∈ Icc (0 : ℝ) (ScalarVectorTimeCoefficients.radius C))
      (W : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
      (_ : ∀ z : AddCircle (1 : ℝ),
        scalarH1PiToContinuous g₀ (P W) z = fun i => e (c z t) i)
      (_ : ‖J (K (W - f₀))‖ ≤ (ScalarVectorTimeCoefficients.radius C)),
      let alpha := tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W - f₀))))
      let reaction := circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (K (W - f₀))))
      ∀ x : ℝ,
        (t, e (c.lift x t), deriv (fun y => e (c.lift y t)) x) ∈
          curveShorteningChartFirstJetDomain D
            (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β ∧
        WithLp.toLp 2 (scalarH1PiToContinuous g₀ (S (m alpha (Q W) + reaction))
          (x : AddCircle (1 : ℝ))) =
          curveShorteningParametricChartRhs
            (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
            (t, e (c.lift x t), deriv (fun y => e (c.lift y t)) x,
              deriv (deriv (fun y => e (c.lift y t))) x) := by
  intro C g₀ f₀ J K P S Q m c t ht W hW hJW alpha reaction x
  have hF : (fun y : ℝ => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P W) (y : AddCircle (1 : ℝ)))) =
      fun y => e (c.lift y t) := by
    funext y
    apply PiLp.ext
    intro i
    exact congrFun (hW (y : AddCircle (1 : ℝ))) i
  dsimp only [g₀, P] at hF
  have h := ambient_rhs_eval_of_h3_state c₀ g ht₀ he hr hEU hleft β hG t ht W hJW x
  simpa only [hF, congrFun hF x] using h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end
end

section
noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {n : ℕ}

variable (c₀ : SmoothImmersion (I := I) (M := M))
  (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht₀ : 0 ∈ D.regular)
  {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
  {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
  (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
  (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
  (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private theorem ambient_rhs_eval_of_curve_state_at :
    let C := ambientCoefficients c₀ g ht₀ he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    ∀ (c : CurveMap M) (t : ℝ) (_ : t ∈ Icc (0 : ℝ) (ScalarVectorTimeCoefficients.radius C))
      (W : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
      (_ : ∀ z : AddCircle (1 : ℝ),
        scalarH1PiToContinuous g₀ (P W) z = fun i => e (c z t) i)
      (_ : ‖J (K (W - f₀))‖ ≤ ScalarVectorTimeCoefficients.radius C)
      (x : ℝ),
      let alpha := tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W - f₀))))
      let reaction := circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (K (W - f₀))))
      WithLp.toLp 2 (scalarH1PiToContinuous g₀
        (S (m alpha (Q W) + reaction)) (x : AddCircle (1 : ℝ))) =
      curveShorteningParametricChartRhs
        (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
        (t, e (c.lift x t), deriv (fun y => e (c.lift y t)) x,
          deriv (deriv (fun y => e (c.lift y t))) x) := by
  intro C g₀ f₀ J K P S Q m c t ht W hW hJW x alpha reaction
  exact (ambient_rhs_eval_of_curve_state c₀ g ht₀ he hr hEU hleft β hG
    c t ht W hW hJW x).2

private theorem ambient_rhs_eval_of_curve_state_projected_at :
    let C := ambientCoefficients c₀ g ht₀ he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    ∀ (c : CurveMap M) (t : ℝ) (_ : t ∈ Icc (0 : ℝ) (ScalarVectorTimeCoefficients.radius C))
      (W : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
      (_ : ∀ z : AddCircle (1 : ℝ),
        scalarH1PiToContinuous g₀ (P W) z = fun i => e (c z t) i)
      (_ : ‖J (K (W - f₀))‖ ≤ ScalarVectorTimeCoefficients.radius C)
      (x : ℝ),
      let alpha := tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W - f₀))))
      let reaction := circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (K (W - f₀))))
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ))
        (curveShorteningParametricChartRhs
          (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
          (t, e (c.lift x t), deriv (fun y => e (c.lift y t)) x,
            deriv (deriv (fun y => e (c.lift y t))) x)) =
      scalarH1PiToContinuous g₀
        (S (m alpha (Q W) + reaction)) (x : AddCircle (1 : ℝ)) := by
  intro C g₀ f₀ J K P S Q m c t ht W hW hJW x alpha reaction
  have h := ambient_rhs_eval_of_curve_state c₀ g ht₀ he hr hEU hleft β hG
    c t ht W hW hJW x
  have hproj := congrArg
    (fun v : EuclideanSpace ℝ (Fin n) =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) v) h.2.symm
  have hto (y : Fin n → ℝ) :
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ))
          (WithLp.toLp 2 y) = y := rfl
  simpa only [hto, alpha, reaction] using hproj

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end
end

section
noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {n : ℕ}

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

omit [TopologicalSpace M] [T2Space M] in
private theorem hasDerivWithinAt_displacement_of_chart_rhs
    {c : CurveMap M} {Jset : Set ℝ}
    {e : M → EuclideanSpace ℝ (Fin n)}
    {g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))}
    {P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) (1 : ℝ)}
    {W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)}
    {f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)}
    {V : ℝ → CircleHsPi g₀ (Fin n) (1 : ℝ)}
    {x t : ℝ} {rhs : EuclideanSpace ℝ (Fin n)}
    (ht : t ∈ Jset)
    (hgeom : HasDerivWithinAt (fun s => e (c.lift x s)) rhs Jset t)
    (hVeq : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) rhs =
      scalarH1PiToContinuous g₀ (V t) (x : AddCircle (1 : ℝ)))
    (hWeval : ∀ s ∈ Jset, ∀ z : AddCircle (1 : ℝ),
      scalarH1PiToContinuous g₀ (P (W s)) z = fun i => e (c z s) i) :
    HasDerivWithinAt (fun s => scalarH1PiToContinuous g₀ (P (W s - f₀))
      (x : AddCircle (1 : ℝ)))
      (scalarH1PiToContinuous g₀ (V t) (x : AddCircle (1 : ℝ))) Jset t := by
  let A : (PiLp 2 (fun _ : Fin n => ℝ)) →L[ℝ] (Fin n → ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toContinuousLinearMap
  have hobs := A.hasFDerivAt.comp_hasDerivWithinAt t hgeom
  change HasDerivWithinAt (fun s => A (e (c.lift x s))) (A rhs) Jset t at hobs
  change A rhs = scalarH1PiToContinuous g₀ (V t) (x : AddCircle (1 : ℝ)) at hVeq
  rw [hVeq] at hobs
  apply (hobs.sub_const
    (scalarH1PiToContinuous g₀ (P f₀) (x : AddCircle (1 : ℝ)))).congr_of_mem _
      ht
  intro s hs
  rw [map_sub, map_sub, ContinuousMap.sub_apply, hWeval s hs]
  rfl



omit [TopologicalSpace M] [T2Space M] in
private theorem exists_strongPair_of_observed_curve
    (c : CurveMap M) (e : M → EuclideanSpace ℝ (Fin n))
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (P L : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) (1 : ℝ))
    {T : ℝ} (hT : 0 < T)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (V : ℝ → CircleHsPi g₀ (Fin n) (1 : ℝ))
    (R : ℝ → ℝ → EuclideanSpace ℝ (Fin n))
    (hW : ContinuousOn W (Icc 0 T))
    (hV : ContinuousOn V (Icc 0 T))
    (hzero : W 0 = f₀)
    (hWeval : ∀ t ∈ Icc 0 T, ∀ z : AddCircle (1 : ℝ),
      scalarH1PiToContinuous g₀ (P (W t)) z = fun i => e (c z t) i)
    (hgeom : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => e (c.lift x s)) (R x t) (Icc 0 T) t)
    (hR : ∀ x t, t ∈ Icc 0 T →
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) (R x t) =
        scalarH1PiToContinuous g₀ (V t) (x : AddCircle (1 : ℝ))) :
    ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) (1 : ℝ)) T)
      (field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T)
      (force : timeL2 (CircleHsPi g₀ (Fin n) (1 : ℝ)) T),
      timeH1.trace0 _ T u = 0 ∧
        EqOn u.toFun (fun t => P (W t - f₀)) (Icc 0 T) ∧
        field =ᵐ[timeMeasure T] (fun t => W t - f₀) ∧
        force =ᵐ[timeMeasure T] (fun t => V t - L (W t - f₀)) ∧
        P.compLpL 2 (timeMeasure T) field = u.toFunL2 ∧
        timeH1.timeDeriv _ T u = L.compLpL 2 (timeMeasure T) field + force := by
  let Obs (z : AddCircle (1 : ℝ)) :=
    (ContinuousMap.evalCLM ℝ z).comp (scalarH1PiToContinuous (ι := Fin n) g₀)
  have hObs : Function.Injective
      (fun x : CircleHsPi g₀ (Fin n) (1 : ℝ) => fun z => Obs z x) := by
    intro x y hxy
    apply scalarH1PiToContinuous_injective g₀
    apply ContinuousMap.ext
    exact fun z => congrFun hxy z
  have hderiv (z : AddCircle (1 : ℝ)) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun s => Obs z (P (W s - f₀)))
        (Obs z (V t)) (Icc 0 T) t := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact hasDerivWithinAt_displacement_of_chart_rhs ht (hgeom x t ht)
      (hR x t ht) hWeval
  obtain ⟨u, field, force, htrace, hrep, hfield, hforce, hcons, hpde⟩ :=
    exists_timeH1_lift_of_hasDerivWithinAt_separating P L Obs hObs hT
      (fun t => W t - f₀) V (hW.sub continuousOn_const) hV hderiv
  refine ⟨u, field, force, ?_, hrep, hfield, hforce, hcons, hpde⟩
  simpa only [hzero, sub_self, map_zero] using htrace

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end
end

section
noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {n : ℕ}

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem exists_strongPair_of_parametric_curve
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht₀ : 0 ∈ D.regular)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) n)
    {r : EuclideanSpace ℝ (Fin n) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : range e.map ⊆ U) (hleft : ∀ p, r (e.map p) = p) (β : U)
    (hG : MetricFamilySmoothOn D
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr)) :
    let C := ambientCoefficients c₀ g ht₀ e.smooth hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e.map e.smooth (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    let L := S.comp (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)))
    ∀ {T : ℝ}, 0 < T → T ≤ (ScalarVectorTimeCoefficients.radius C) → ∀ c : CurveMap M,
      ∀ (hc : c.SmoothOn (I := I) (Icc 0 T)) (hi : c.ImmersedOn (I := I) (Icc 0 T)),
      (∀ z, c z 0 = c₀.map z) →
      (∀ x t, t ∈ Icc 0 T →
        c.velocity (I := I) (Icc 0 T) x t = c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t) →
      (∀ t (ht : t ∈ Icc 0 T),
        ‖J (K (fixedAmbientSobolev e g₀ (slice c hc hi t ht) - f₀))‖ ≤
          ScalarVectorTimeCoefficients.radius C) →
      ∃ W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2),
        ContinuousOn W (Icc 0 T) ∧ W 0 = f₀ ∧
        (∀ t (ht : t ∈ Icc 0 T),
          W t = fixedAmbientSobolev e g₀ (slice c hc hi t ht)) ∧
        (∀ t ∈ Icc 0 T, ∀ z : AddCircle (1 : ℝ),
          scalarH1PiToContinuous g₀ (P (W t)) z = fun i => e.map (c z t) i) ∧
        let alpha := fun t => tensorHsCongrL g₀ 0 0
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t - f₀))))
        let reaction := fun t => circleHsPiCongr g₀ (Fin n)
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t - f₀))))
        let V := fun t => S (m (alpha t) (Q (W t)) + reaction t)
        ContinuousOn V (Icc 0 T) ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) (1 : ℝ)) T)
          (field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T)
          (force : timeL2 (CircleHsPi g₀ (Fin n) (1 : ℝ)) T),
          timeH1.trace0 _ T u = 0 ∧
            EqOn u.toFun (fun t => P (W t - f₀)) (Icc 0 T) ∧
            field =ᵐ[timeMeasure T] (fun t => W t - f₀) ∧
            force =ᵐ[timeMeasure T] (fun t => V t - L (W t - f₀)) ∧
            P.compLpL 2 (timeMeasure T) field = u.toFunL2 ∧
            timeH1.timeDeriv _ T u = L.compLpL 2 (timeMeasure T) field + force := by
  generalize hC : ambientCoefficients c₀ g ht₀ e.smooth hr hEU hleft β hG = C₁
  intro C g₀ f₀ J K P S Q m L T hT hTR c hc hi hinit heq hsmall
  obtain ⟨W, hWcont, hWzero, hWslice, hWeval⟩ :=
    exists_continuousOn_fixedAmbientSobolev_curve_with_initial e (g 0) c₀ hT hc hi hinit
  refine ⟨W, hWcont, hWzero, hWslice, hWeval, ?_⟩
  intro alpha reaction V
  have hJW (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖J (K (W t - f₀))‖ ≤ ScalarVectorTimeCoefficients.radius C := by
    rw [hWslice t ht]
    exact hsmall t ht
  have hdisp : ContinuousOn (fun t => W t - f₀) (Icc 0 T) :=
    hWcont.sub continuousOn_const
  have hadd (t : ℝ) : f₀ + (W t - f₀) = W t := by abel
  have hraw : ContinuousOn (fun t => m (alpha t) (Q (W t)) + reaction t) (Icc 0 T) := by
    simpa only [hadd] using scalarVectorTimeCoefficients_rhs_continuousOn
      g₀ _ _ _ _ C f₀ J (fun t => W t - f₀) hdisp hJW
  have hV : ContinuousOn V (Icc 0 T) := S.continuous.comp_continuousOn hraw
  refine ⟨hV, ?_⟩
  let R := fun x t => curveShorteningParametricChartRhs
    (fun s => Geometry.Riemannian.retractionMetric (g s) e.smooth hr) β
    (t, e.map (c.lift x t), deriv (fun y => e.map (c.lift y t)) x,
      deriv (deriv (fun y => e.map (c.lift y t))) x)
  have hgeom (x t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun s => e.map (c.lift x s)) (R x t) (Icc 0 T) t :=
    CurveMap.hasDerivWithinAt_retraction_chart_of_parametric_equation
      g e.smooth hr hEU hleft β hc ht ((uniqueDiffOn_Icc hT) t ht) (heq x t ht)
  have hRraw := ambient_rhs_eval_of_curve_state_projected_at
    (c₀ := c₀) (g := g) (ht₀ := ht₀) (e := e.map) (he := e.smooth)
    (hr := hr) (hEU := hEU) (hleft := hleft) (β := β) (hG := hG)
  rw [hC] at hRraw
  dsimp only [C, g₀, f₀, J, K] at hJW
  have hR (x t : ℝ) (ht : t ∈ Icc 0 T) :
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) (R x t) =
        scalarH1PiToContinuous g₀ (V t) (x : AddCircle (1 : ℝ)) := by
    exact hRraw c t ⟨ht.1, ht.2.trans hTR⟩
      (W t) (hWeval t ht) (hJW t ht) x
  exact exists_strongPair_of_observed_curve c e.map g₀ P L hT f₀ W V R
    hWcont hV hWzero hWeval hgeom hR

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end
end

section
noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

local notation "earlyShiftedRemainder" => DifferentialGeometry.Analysis.Parabolic.QuasiLinear.shiftedRemainder

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private local instance {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (a : ℝ) :
    NormedSpace ℝ (PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) := inferInstance

private theorem circle_shifted_strongPair_eq
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (m : TensorHs g 0 0 (n : ℝ) →L[ℝ] CircleHsPi g ι (n : ℝ) →L[ℝ] CircleHsPi g ι (n : ℝ))
    (Q : CircleHsPi g ι ((n : ℝ) + 2) →L[ℝ] CircleHsPi g ι (n : ℝ))
    (D : CircleHsPi g ι ((n : ℝ) + 1) →L[ℝ] CircleHsPi g ι (n : ℝ))
    (c : CircleHsPi g ι (n : ℝ)) (d : CircleHsPi g ι (n : ℝ) →L[ℝ] CircleHsPi g ι (n : ℝ))
    (q : TensorHs g 0 0 (n : ℝ))
    (alpha : ℝ → CircleHsPi g ι ((n : ℝ) + 1) → TensorHs g 0 0 (n : ℝ))
    (reaction : ℝ → CircleHsPi g ι ((n : ℝ) + 1) → CircleHsPi g ι (n : ℝ))
    {R τ T : ℝ} (hR : 0 ≤ R) (hT : 0 < T) (hTτ : T ≤ τ) (K L M : ℝ≥0)
    (halip : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖alpha t z - alpha t w‖ ≤ (L : ℝ) * ‖z - w‖)
    (haclose : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R →
      ‖alpha t z - q‖ ≤ (K : ℝ) * R)
    (hreaction : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖reaction t z - reaction t w‖ ≤ (M : ℝ) * ‖z - w‖)
    (force₁ force₂ : timeL2 (CircleHsPi g ι (n : ℝ)) T)
    (u₁ u₂ : timeH1 (CircleHsPi g ι (n : ℝ)) T)
    (field₁ field₂ : timeL2 (CircleHsPi g ι ((n : ℝ) + 2)) T) :
    let J := circleHsPiInclusion g ι (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)
    let N := earlyShiftedRemainder m Q J D c d q alpha reaction R
    let hzero : (0 : CircleHsPi g ι ((n : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ R} := by
      simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR
    timeH1.trace0 _ T u₁ = timeH1.trace0 _ T u₂ →
    u₁.toFunL2 = (circleHsPiInclusion g ι (show (n : ℝ) ≤ (n : ℝ) + 2 by linarith)).compLpL
      2 (timeMeasure T) field₁ →
    u₂.toFunL2 = (circleHsPiInclusion g ι (show (n : ℝ) ≤ (n : ℝ) + 2 by linarith)).compLpL
      2 (timeMeasure T) field₂ →
    timeH1.timeDeriv _ T u₁ =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
        (g := g) (r := 0) (s := 0) (n : ℝ))).compLpL 2 (timeMeasure T) field₁ + force₁ →
    timeH1.timeDeriv _ T u₂ =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
        (g := g) (r := 0) (s := 0) (n : ℝ))).compLpL 2 (timeMeasure T) field₂ + force₂ →
    (∀ᵐ t ∂(timeMeasure T), field₁ t ∈ {v | ‖J v‖ ≤ R}) →
    (∀ᵐ t ∂(timeMeasure T), field₂ t ∈ {v | ‖J v‖ ≤ R}) →
    (force₁ =ᵐ[timeMeasure T] fun t => N t (aeSetLift hzero field₁ t)) →
    (force₂ =ᵐ[timeMeasure T] fun t => N t (aeSetLift hzero field₂ t)) →
    (‖m‖ * (K : ℝ) * ‖Q‖) * R * (1 + T) +
      (‖m‖ * (L : ℝ) * ‖c‖ + (M : ℝ) + ‖d‖ * ‖D‖) * Real.sqrt T * Real.sqrt (1 + T) +
        (‖m‖ * (L : ℝ) * ‖Q‖) * Real.sqrt (1 + T) * (‖field₁‖ + ‖field₂‖) < 1 →
    force₁ = force₂ ∧ field₁ = field₂ ∧ u₁ = u₂ := by
  intro J N hzero htrace hlink₁ hlink₂ heq₁ heq₂ hstate₁ hstate₂ hforce₁ hforce₂ hsmall
  let Aconst : ℝ≥0 := ‖m‖₊ * K * ‖Q‖₊
  let Bconst : ℝ≥0 := ‖m‖₊ * L * ‖c‖₊ + M + ‖d‖₊ * ‖D‖₊
  let Cconst : ℝ≥0 := ‖m‖₊ * L * ‖Q‖₊
  have htime : ∀ᵐ t ∂(timeMeasure T), t ∈ Icc (0 : ℝ) τ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ⟨ht.1, ht.2.trans hTτ⟩
  have htame : ∀ᵐ t ∂(timeMeasure T), ∀ v w,
      ‖N t v - N t w‖ ≤ (Aconst : ℝ) * R * ‖v.val - w.val‖ +
        (Bconst : ℝ) * ‖J (v.val - w.val)‖ +
        (Cconst : ℝ) * (‖v.val‖ + ‖w.val‖) * ‖J (v.val - w.val)‖ := by
    filter_upwards [htime] with t ht
    intro v w
    exact (shifted_tame_estimate m Q J D c d q alpha reaction t
      (halip t ht) (haclose t ht) (hreaction t ht) v.property w.property).1
  have hsmall' : (Aconst : ℝ) * R * (1 + T) +
      (Bconst : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
        (Cconst : ℝ) * Real.sqrt (1 + T) * (‖field₁‖ + ‖field₂‖) < 1 := by
    simpa only [Aconst, Bconst, Cconst, NNReal.coe_mul, NNReal.coe_add, coe_nnnorm] using hsmall
  exact strongPair_eq_of_tame_vector hT hR hzero N Aconst Bconst Cconst htame
    force₁ force₂ u₁ u₂ field₁ field₂ htrace hlink₁.symm hlink₂.symm heq₁ heq₂
    hstate₁ hstate₂ hforce₁ hforce₂ hsmall'

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
end

section
open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem exists_pos_shifted_tame_radius_window
    {A X Y Z : Type*}
    [SeminormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
    (m : A →L[ℝ] Y →L[ℝ] Y) (Q : X →L[ℝ] Y) (D : Z →L[ℝ] Y)
    (d : Y →L[ℝ] Y) (f₀ : X) (K L M : ℝ≥0)
    {R T : ℝ} (hR : 0 < R) (hT : 0 < T) (hT1 : T ≤ 1)
    (field₁ field₂ : timeL2 X T) :
    let Aconst : ℝ≥0 := ‖m‖₊ * K * ‖Q‖₊
    let Bconst : ℝ≥0 := ‖m‖₊ * L * ‖Q f₀‖₊ + M + ‖d‖₊ * ‖D‖₊
    let Cconst : ℝ≥0 := ‖m‖₊ * L * ‖Q‖₊
    ∃ r > 0, r ≤ R ∧ r ≤ 1 ∧
      (Aconst : ℝ) * r ≤ 1 / 16 ∧ (Cconst : ℝ) * r ≤ 1 / 16 ∧
      ∃ δ > 0, δ ≤ T ∧ ∀ a b : ℝ, ∀ ha : 0 ≤ a, ∀ hbT : b ≤ T,
        0 ≤ b - a → b - a ≤ δ →
          (Aconst : ℝ) * r * (1 + (b - a)) +
            (Bconst : ℝ) * Real.sqrt (b - a) * Real.sqrt (1 + (b - a)) +
              (Cconst : ℝ) * Real.sqrt (1 + (b - a)) *
                (‖timeL2.slice field₁ a b ha hbT‖ +
                  ‖timeL2.slice field₂ a b ha hbT‖) < 1 := by
  intro Aconst Bconst Cconst
  obtain ⟨r, hr, hrR, hr1, hAr, hCr⟩ :=
    exists_small_coefficient_radius hR Aconst Cconst
  have hbase : (Aconst : ℝ) * r * (1 + T) < 1 := by
    have hbound := mul_le_mul_of_nonneg_left (show 1 + T ≤ 2 by linarith)
      (mul_nonneg Aconst.coe_nonneg hr.le)
    nlinarith
  let P := Real.sqrt (1 + T)
  obtain ⟨δ, hδ, hδT, hsmall⟩ := exists_pos_l2_slice_pair_contraction_lt hT field₁ field₂
    hbase (mul_nonneg Bconst.coe_nonneg (Real.sqrt_nonneg (1 + T)))
      (mul_nonneg Cconst.coe_nonneg (Real.sqrt_nonneg (1 + T)))
  refine ⟨r, hr, hrR, hr1, hAr, hCr, δ, hδ, hδT, ?_⟩
  intro a b ha hbT hd hdδ
  have hdT : b - a ≤ T := by linarith
  have hP : Real.sqrt (1 + (b - a)) ≤ P := Real.sqrt_le_sqrt (by linarith)
  have hnorm : 0 ≤ ‖timeL2.slice field₁ a b ha hbT‖ +
      ‖timeL2.slice field₂ a b ha hbT‖ := by positivity
  have hA := mul_le_mul_of_nonneg_left (show 1 + (b - a) ≤ 1 + T by linarith)
    (mul_nonneg Aconst.coe_nonneg hr.le)
  have hB := mul_le_mul_of_nonneg_left hP
    (mul_nonneg Bconst.coe_nonneg (Real.sqrt_nonneg (b - a)))
  have hC := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hP Cconst.coe_nonneg) hnorm
  have h := hsmall a b ha hbT hd hdδ
  dsimp only [P] at hB hC
  nlinarith

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

section
open Set

private theorem exists_common_initial_interval_norm_le
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    {T r : ℝ} (hT : 0 < T) (hr : 0 < r) (L : E →L[ℝ] F)
    {W₁ W₂ : ℝ → E} {f₀ : E}
    (hW₁ : ContinuousOn W₁ (Icc 0 T)) (hW₂ : ContinuousOn W₂ (Icc 0 T))
    (hW₁₀ : W₁ 0 = f₀) (hW₂₀ : W₂ 0 = f₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ T ∧ ∀ t ∈ Icc 0 δ,
      ‖L (W₁ t - f₀)‖ ≤ r ∧ ‖L (W₂ t - f₀)‖ ≤ r := by
  let Φ : ℝ × ℝ → F × F := fun p => (L (W₁ p.2 - f₀), L (W₂ p.2 - f₀))
  have h₁ : ContinuousOn (fun t => L (W₁ t - f₀)) (Icc 0 T) :=
    L.continuous.comp_continuousOn (hW₁.sub continuousOn_const)
  have h₂ : ContinuousOn (fun t => L (W₂ t - f₀)) (Icc 0 T) :=
    L.continuous.comp_continuousOn (hW₂.sub continuousOn_const)
  have hΦ : ContinuousOn Φ (({0} : Set ℝ) ×ˢ Icc 0 T) :=
    (h₁.prodMk h₂).comp continuousOn_snd (fun _ hp => hp.2)
  have hinit : ∀ x ∈ ({0} : Set ℝ),
      Φ (x, 0) ∈ Metric.ball (0 : F) r ×ˢ Metric.ball (0 : F) r := by
    intro x hx
    simp only [Φ, hW₁₀, hW₂₀, sub_self, map_zero, mem_prod,
      Metric.mem_ball, dist_self]
    exact ⟨hr, hr⟩
  obtain ⟨δ, hδ, hδT, hδΦ⟩ := IsCompact.exists_Icc_mapsTo_of_continuousOn
    isCompact_singleton hT (Metric.isOpen_ball.prod Metric.isOpen_ball) hΦ hinit
  refine ⟨δ, hδ, by simpa only [sub_zero] using hδT, ?_⟩
  intro t ht
  have hp := hδΦ 0 (mem_singleton 0) t (by simpa only [zero_add] using ht)
  have hb : ‖L (W₁ t - f₀)‖ < r ∧ ‖L (W₂ t - f₀)‖ < r := by
    simpa only [Φ, mem_prod, Metric.mem_ball, dist_zero_right] using hp
  exact ⟨hb.1.le, hb.2.le⟩
end

section
noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

local notation "earlyShiftedRemainder" => DifferentialGeometry.Analysis.Parabolic.QuasiLinear.shiftedRemainder

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private local instance {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (a : ℝ) :
    NormedSpace ℝ (PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) := inferInstance

private theorem circle_physical_rhs_sub_laplacian_eq_shifted
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (K : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g ι (((1 : ℕ) : ℝ) + 1))
    (Q : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g ι ((1 : ℕ) : ℝ))
    (D : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      CircleHsPi g ι ((1 : ℕ) : ℝ))
    (m : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ]
      CircleHsPi g ι ((1 : ℕ) : ℝ) →L[ℝ] CircleHsPi g ι ((1 : ℕ) : ℝ))
    (d : CircleHsPi g ι ((1 : ℕ) : ℝ) →L[ℝ] CircleHsPi g ι ((1 : ℕ) : ℝ))
    (q : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (L : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g ι ((1 : ℕ) : ℝ))
    (hK : K = circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    (hQ : Q = AddCircle.parameterSecondDerivativeHsPi (ι := ι) g (1 : ℕ))
    (hD : D = AddCircle.parameterDerivativeHsPi (ι := ι) g (1 : ℕ))
    (hm : m = coordinateMultiplication (ι := ι) (scalarHsMul g (1 : ℕ) (by norm_num)))
    (hd : d = ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 (1 : ℕ) (scalarCc g (AddCircle.laplacianDriftCoefficient g))))
    (hq : q = ccTensorToHs g 0 ((1 : ℕ) : ℝ)
      (scalarCc g (AddCircle.laplacianPrincipalCoefficient g)))
    (hL : L = ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ)))
    (f₀ W : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (alpha : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (reaction : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 1) → CircleHsPi g ι ((1 : ℕ) : ℝ))
    (r t : ℝ) (hW : ‖K (W - f₀)‖ ≤ r) :
    m (alpha t (K (W - f₀))) (Q W) + reaction t (K (W - f₀)) - L (W - f₀) =
      earlyShiftedRemainder m Q K D (Q f₀) d q alpha reaction r t ⟨W - f₀, hW⟩ := by
  subst K Q D m d q L
  have hid := shifted_circle_operator_identity g 1 (by norm_num) f₀ (W - f₀)
    (alpha t (circleHsPiInclusion g ι (by norm_num) (W - f₀)))
    (reaction t (circleHsPiInclusion g ι (by norm_num) (W - f₀)))
  have hadd : f₀ + (W - f₀) = W := by abel
  dsimp only at hid
  rw [hadd] at hid
  apply (sub_eq_iff_eq_add).2
  exact hid.symm.trans (add_comm _ _)

private theorem circle_initial_slice_eqOn_of_eq
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {T δ : ℝ} (hδT : δ ≤ T) (u₁ u₂ : timeH1 Y T)
    (h : u₁.slice 0 δ le_rfl hδT = u₂.slice 0 δ le_rfl hδT) :
    EqOn u₁.toFun u₂.toFun (Icc 0 δ) := by
  intro t ht
  have ht' : t ∈ Icc 0 (δ - 0) := by simpa only [sub_zero] using ht
  have heq := congrArg (fun u : timeH1 Y (δ - 0) => u.toFun t) h
  rw [timeH1.slice_toFun u₁ 0 δ le_rfl hδT ht',
    timeH1.slice_toFun u₂ 0 δ le_rfl hδT ht'] at heq
  simpa only [zero_add] using heq

private theorem circle_physical_strongPair_eq
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    let K : (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) →L[ℝ] (CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)) :=
      circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P : (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) →L[ℝ] (CircleHsPi g ι ((1 : ℕ) : ℝ)) :=
      circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let Q : (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) →L[ℝ] (CircleHsPi g ι ((1 : ℕ) : ℝ)) :=
      AddCircle.parameterSecondDerivativeHsPi (ι := ι) g (1 : ℕ)
    let D : (CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)) →L[ℝ] (CircleHsPi g ι ((1 : ℕ) : ℝ)) :=
      AddCircle.parameterDerivativeHsPi (ι := ι) g (1 : ℕ)
    let m : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ]
      (CircleHsPi g ι ((1 : ℕ) : ℝ)) →L[ℝ] (CircleHsPi g ι ((1 : ℕ) : ℝ)) :=
      coordinateMultiplication (ι := ι) (scalarHsMul g (1 : ℕ) (by norm_num))
    let d : (CircleHsPi g ι ((1 : ℕ) : ℝ)) →L[ℝ] (CircleHsPi g ι ((1 : ℕ) : ℝ)) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 (1 : ℕ) (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
    let q : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ)
      (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    let L : (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) →L[ℝ] (CircleHsPi g ι ((1 : ℕ) : ℝ)) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    ∀ {outer R τ T : ℝ} (_ : 0 ≤ R) (_ : R ≤ outer) (_ : 0 < T) (_ : T ≤ τ)
      (Ca Cb : ℝ≥0)
      (alpha : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 ((1 : ℕ) : ℝ))
      (reaction : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 1) → CircleHsPi g ι ((1 : ℕ) : ℝ))
      (_ : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
        ‖alpha t z - alpha t w‖ ≤ (Ca : ℝ) * ‖z - w‖)
      (_ : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R →
        ‖alpha t z - q‖ ≤ (Ca : ℝ) * R)
      (_ : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
        ‖reaction t z - reaction t w‖ ≤ (Cb : ℝ) * ‖z - w‖)
      (f₀ : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
      (W₁ W₂ : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
      (u₁ u₂ : timeH1 (CircleHsPi g ι ((1 : ℕ) : ℝ)) T)
      (field₁ field₂ : timeL2 (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) T)
      (force₁ force₂ : timeL2 (CircleHsPi g ι ((1 : ℕ) : ℝ)) T),
      timeH1.trace0 _ T u₁ = timeH1.trace0 _ T u₂ →
      field₁ =ᵐ[timeMeasure T] (fun t => W₁ t - f₀) →
      field₂ =ᵐ[timeMeasure T] (fun t => W₂ t - f₀) →
      (∀ᵐ t ∂timeMeasure T, ‖K (W₁ t - f₀)‖ ≤ outer → force₁ t =
        m (alpha t (K (W₁ t - f₀))) (Q (W₁ t)) + reaction t (K (W₁ t - f₀)) -
          L (W₁ t - f₀)) →
      (∀ᵐ t ∂timeMeasure T, ‖K (W₂ t - f₀)‖ ≤ outer → force₂ t =
        m (alpha t (K (W₂ t - f₀))) (Q (W₂ t)) + reaction t (K (W₂ t - f₀)) -
          L (W₂ t - f₀)) →
      P.compLpL 2 (timeMeasure T) field₁ = u₁.toFunL2 →
      P.compLpL 2 (timeMeasure T) field₂ = u₂.toFunL2 →
      timeH1.timeDeriv _ T u₁ = L.compLpL 2 (timeMeasure T) field₁ + force₁ →
      timeH1.timeDeriv _ T u₂ = L.compLpL 2 (timeMeasure T) field₂ + force₂ →
      (∀ᵐ t ∂timeMeasure T, field₁ t ∈ {v | ‖K v‖ ≤ R}) →
      (∀ᵐ t ∂timeMeasure T, field₂ t ∈ {v | ‖K v‖ ≤ R}) →
      (‖m‖ * (Ca : ℝ) * ‖Q‖) * R * (1 + T) +
        (‖m‖ * (Ca : ℝ) * ‖Q f₀‖ + (Cb : ℝ) + ‖d‖ * ‖D‖) *
          Real.sqrt T * Real.sqrt (1 + T) +
        (‖m‖ * (Ca : ℝ) * ‖Q‖) * Real.sqrt (1 + T) *
          (‖field₁‖ + ‖field₂‖) < 1 → u₁ = u₂ := by
  intro K P Q D m d q L outer R τ T hR hRouter hT hTτ Ca Cb alpha reaction
    halip haclose hreaction f₀ W₁ W₂ u₁ u₂ field₁ field₂ force₁ force₂
    htrace hfield₁ hfield₂ hforce₁ hforce₂ hlink₁ hlink₂ hpde₁ hpde₂
    hstate₁ hstate₂ hcontract
  let N := earlyShiftedRemainder m Q K D (Q f₀) d q alpha reaction R
  have hzero : (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) ∈ {v | ‖K v‖ ≤ R} := by
    change ‖K 0‖ ≤ R
    rw [map_zero, norm_zero]
    exact hR
  let F := fun t W => m (alpha t (K (W - f₀))) (Q W) +
    reaction t (K (W - f₀)) - L (W - f₀)
  have hresidual (W : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) (t : ℝ)
      (hW : ‖K (W - f₀)‖ ≤ R) : F t W = N t ⟨W - f₀, hW⟩ :=
    circle_physical_rhs_sub_laplacian_eq_shifted g K Q D m d q L
      rfl rfl rfl rfl rfl rfl rfl f₀ W alpha reaction R t hW
  have hf₁ := ae_residual_lift_of_ball_imp K hzero N field₁ force₁ W₁ f₀ F hRouter
    hfield₁ hstate₁ hforce₁ (fun t hW => hresidual (W₁ t) t hW)
  have hf₂ := ae_residual_lift_of_ball_imp K hzero N field₂ force₂ W₂ f₀ F hRouter
    hfield₂ hstate₂ hforce₂ (fun t hW => hresidual (W₂ t) t hW)
  exact (circle_shifted_strongPair_eq
    g 1 m Q D (Q f₀) d q alpha reaction hR hT hTτ Ca Ca Cb
    halip haclose hreaction force₁ force₂ u₁ u₂ field₁ field₂
    htrace hlink₁.symm hlink₂.symm hpde₁ hpde₂ hstate₁ hstate₂ hf₁ hf₂ hcontract).2.2

private theorem circle_continuous_state_eq_on_of_radius
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    let K : (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) →L[ℝ] (CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)) :=
      circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P : (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) →L[ℝ] (CircleHsPi g ι ((1 : ℕ) : ℝ)) :=
      circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let Q : (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) →L[ℝ] (CircleHsPi g ι ((1 : ℕ) : ℝ)) :=
      AddCircle.parameterSecondDerivativeHsPi (ι := ι) g (1 : ℕ)
    let D : (CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)) →L[ℝ] (CircleHsPi g ι ((1 : ℕ) : ℝ)) :=
      AddCircle.parameterDerivativeHsPi (ι := ι) g (1 : ℕ)
    let m : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ]
      (CircleHsPi g ι ((1 : ℕ) : ℝ)) →L[ℝ] (CircleHsPi g ι ((1 : ℕ) : ℝ)) :=
      coordinateMultiplication (ι := ι) (scalarHsMul g (1 : ℕ) (by norm_num))
    let d : (CircleHsPi g ι ((1 : ℕ) : ℝ)) →L[ℝ] (CircleHsPi g ι ((1 : ℕ) : ℝ)) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 (1 : ℕ) (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
    let q : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ)
      (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    let L : (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) →L[ℝ] (CircleHsPi g ι ((1 : ℕ) : ℝ)) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    ∀ {outer T r δ : ℝ} (houter : 0 < outer) (_ : 0 ≤ r) (_ : r ≤ outer)
    (_ : 0 < δ) (hδT : δ ≤ T) (_ : δ ≤ r)
    (A : ℝ → Metric.closedBall
      (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)) outer → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (B : ℝ → Metric.closedBall
      (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)) outer → CircleHsPi g ι ((1 : ℕ) : ℝ))
    (Ca Cb : ℝ≥0)
    (_ : LipschitzWith Ca (fun p : ℝ × Metric.closedBall
      (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)) outer => A p.1 p.2))
    (_ : LipschitzWith Cb (fun p : ℝ × Metric.closedBall
      (0 : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)) outer => B p.1 p.2))
    (_ : A 0 ⟨0, Metric.mem_closedBall_self houter.le⟩ = q)
    (f₀ : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (W₁ W₂ : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (u₁ u₂ : timeH1 (CircleHsPi g ι ((1 : ℕ) : ℝ)) T)
    (field₁ field₂ : timeL2 (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) T)
    (force₁ force₂ : timeL2 (CircleHsPi g ι ((1 : ℕ) : ℝ)) T)
    (_ : timeH1.trace0 _ T u₁ = timeH1.trace0 _ T u₂)
    (_ : field₁ =ᵐ[timeMeasure T] (fun t => W₁ t - f₀))
    (_ : field₂ =ᵐ[timeMeasure T] (fun t => W₂ t - f₀))
    (_ : ∀ᵐ t ∂timeMeasure T, ‖K (W₁ t - f₀)‖ ≤ outer → force₁ t =
      m ((extendClosedBall houter.le A) t (K (W₁ t - f₀))) (Q (W₁ t)) +
        (extendClosedBall houter.le B) t (K (W₁ t - f₀)) - L (W₁ t - f₀))
    (_ : ∀ᵐ t ∂timeMeasure T, ‖K (W₂ t - f₀)‖ ≤ outer → force₂ t =
      m ((extendClosedBall houter.le A) t (K (W₂ t - f₀))) (Q (W₂ t)) +
        (extendClosedBall houter.le B) t (K (W₂ t - f₀)) - L (W₂ t - f₀))
    (_ : P.compLpL 2 (timeMeasure T) field₁ = u₁.toFunL2)
    (_ : P.compLpL 2 (timeMeasure T) field₂ = u₂.toFunL2)
    (_ : timeH1.timeDeriv _ T u₁ = L.compLpL 2 (timeMeasure T) field₁ + force₁)
    (_ : timeH1.timeDeriv _ T u₂ = L.compLpL 2 (timeMeasure T) field₂ + force₂)
    (_ : ∀ t ∈ Icc (0 : ℝ) δ,
      ‖K (W₁ t - f₀)‖ ≤ r ∧ ‖K (W₂ t - f₀)‖ ≤ r)
    (_ :
      (‖m‖ * (Ca : ℝ) * ‖Q‖) * r * (1 + (δ - 0)) +
        (‖m‖ * (Ca : ℝ) * ‖Q f₀‖ + (Cb : ℝ) + ‖d‖ * ‖D‖) *
          Real.sqrt (δ - 0) * Real.sqrt (1 + (δ - 0)) +
        (‖m‖ * (Ca : ℝ) * ‖Q‖) * Real.sqrt (1 + (δ - 0)) *
          (‖timeL2.slice field₁ 0 δ le_rfl hδT‖ +
            ‖timeL2.slice field₂ 0 δ le_rfl hδT‖) < 1),
    EqOn u₁.toFun u₂.toFun (Icc 0 δ) := by
  intro K P Q D m d q L outer T r δ houter hr hrOuter hδ hδT hδr
    A B Ca Cb hA hB hA0 f₀ W₁ W₂ u₁ u₂ field₁ field₂ force₁ force₂
    htrace hfield₁ hfield₂ hforce₁ hforce₂ hlink₁ hlink₂ hpde₁ hpde₂ hstates hcontract
  let alpha : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 1) →
      TensorHs g 0 0 ((1 : ℕ) : ℝ) := extendClosedBall houter.le A
  let reaction : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 1) →
      CircleHsPi g ι ((1 : ℕ) : ℝ) := extendClosedBall houter.le B
  have haBounds := extendClosedBall_bounds houter.le hr hrOuter A Ca hA
  have hbBounds := extendClosedBall_bounds houter.le hr hrOuter B Cb hB
  have haclose : ∀ t ∈ Icc (0 : ℝ) r, ∀ z, ‖z‖ ≤ r →
      ‖alpha t z - q‖ ≤ (Ca : ℝ) * r := by
    intro t ht z hz
    simpa only [alpha, hA0] using haBounds.2.1 t ht z hz
  let u₁s := u₁.slice 0 δ le_rfl hδT
  let u₂s := u₂.slice 0 δ le_rfl hδT
  let field₁s := timeL2.slice field₁ 0 δ le_rfl hδT
  let field₂s := timeL2.slice field₂ 0 δ le_rfl hδT
  let force₁s := timeL2.slice force₁ 0 δ le_rfl hδT
  let force₂s := timeL2.slice force₂ 0 δ le_rfl hδT
  have hδs : 0 < δ - 0 := by simpa only [sub_zero] using hδ
  have hδsr : δ - 0 ≤ r := by simpa only [sub_zero] using hδr
  have htraces : timeH1.trace0 _ (δ - 0) u₁s = timeH1.trace0 _ (δ - 0) u₂s := by
    change u₁.toFun 0 = u₂.toFun 0
    simpa only [timeH1.toFun_zero, timeH1.trace0_apply] using htrace
  obtain ⟨hlink₁s, hpde₁s⟩ := timeH1.slice_compLpL_eq_and_timeDeriv_eq
    P L u₁ field₁ force₁ (a := 0) (b := δ) le_rfl hδT hlink₁ hpde₁
  obtain ⟨hlink₂s, hpde₂s⟩ := timeH1.slice_compLpL_eq_and_timeDeriv_eq
    P L u₂ field₂ force₂ (a := 0) (b := δ) le_rfl hδT hlink₂ hpde₂
  have hfield₁s : field₁s =ᵐ[timeMeasure (δ - 0)] fun t => W₁ t - f₀ :=
    timeL2.slice_zero_ae_eq field₁ hδT hfield₁
  have hfield₂s : field₂s =ᵐ[timeMeasure (δ - 0)] fun t => W₂ t - f₀ :=
    timeL2.slice_zero_ae_eq field₂ hδT hfield₂
  have htime : ∀ᵐ t ∂timeMeasure (δ - 0), t ∈ Icc (0 : ℝ) δ := by
    simpa only [timeMeasure, sub_zero] using
      (ae_restrict_mem (μ := volume) (s := Icc (0 : ℝ) δ) measurableSet_Icc)
  have hstate₁s : ∀ᵐ t ∂timeMeasure (δ - 0), field₁s t ∈ {v | ‖K v‖ ≤ r} := by
    filter_upwards [hfield₁s, htime] with t ht hs
    rw [ht]
    exact (hstates t hs).1
  have hstate₂s : ∀ᵐ t ∂timeMeasure (δ - 0), field₂s t ∈ {v | ‖K v‖ ≤ r} := by
    filter_upwards [hfield₂s, htime] with t ht hs
    rw [ht]
    exact (hstates t hs).2
  have hcontract' :
      (‖m‖ * (Ca : ℝ) * ‖Q‖) * r * (1 + (δ - 0)) +
        (‖m‖ * (Ca : ℝ) * ‖Q f₀‖ + (Cb : ℝ) + ‖d‖ * ‖D‖) *
          Real.sqrt (δ - 0) * Real.sqrt (1 + (δ - 0)) +
        (‖m‖ * (Ca : ℝ) * ‖Q‖) * Real.sqrt (1 + (δ - 0)) *
          (‖field₁s‖ + ‖field₂s‖) < 1 := by
    simpa only [field₁s, field₂s] using hcontract
  have huEq := circle_physical_strongPair_eq g hr hrOuter hδs hδsr Ca Cb
    alpha reaction haBounds.1 haclose hbBounds.1 f₀ W₁ W₂ u₁s u₂s
    field₁s field₂s force₁s force₂s htraces hfield₁s hfield₂s
    (timeL2.slice_zero_ae_imp_eq force₁ hδT hforce₁)
    (timeL2.slice_zero_ae_imp_eq force₂ hδT hforce₂)
    hlink₁s hlink₂s hpde₁s hpde₂s hstate₁s hstate₂s hcontract'
  exact circle_initial_slice_eqOn_of_eq hδT u₁ u₂ huEq

private theorem circle_continuous_state_local_uniqueness
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    let X : Type _ := CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)
    let Y : Type _ := CircleHsPi g ι ((1 : ℕ) : ℝ)
    let Z : Type _ := CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)
    let K : X →L[ℝ] Z := circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P : X →L[ℝ] Y := circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let Q : X →L[ℝ] Y := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g (1 : ℕ)
    let m : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] Y →L[ℝ] Y :=
      coordinateMultiplication (ι := ι) (scalarHsMul g (1 : ℕ) (by norm_num))
    let q : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ)
      (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    let L : X →L[ℝ] Y := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    ∀ {outer T : ℝ} (houter : 0 < outer) (hT : 0 < T), T ≤ 1 →
    ∀ (A : ℝ → Metric.closedBall (0 : Z) outer → TensorHs g 0 0 ((1 : ℕ) : ℝ))
      (B : ℝ → Metric.closedBall (0 : Z) outer → Y) (Ca Cb : ℝ≥0),
      LipschitzWith Ca (fun p : ℝ × Metric.closedBall (0 : Z) outer => A p.1 p.2) →
      LipschitzWith Cb (fun p : ℝ × Metric.closedBall (0 : Z) outer => B p.1 p.2) →
      A 0 ⟨0, Metric.mem_closedBall_self houter.le⟩ = q →
    let alpha : ℝ → Z → TensorHs g 0 0 ((1 : ℕ) : ℝ) := extendClosedBall houter.le A
    let reaction : ℝ → Z → Y := extendClosedBall houter.le B
    ∀ (f₀ : X) (W₁ W₂ : ℝ → X),
      ContinuousOn W₁ (Icc 0 T) → ContinuousOn W₂ (Icc 0 T) →
      W₁ 0 = f₀ → W₂ 0 = f₀ →
    ∀ (u₁ u₂ : timeH1 Y T) (field₁ field₂ : timeL2 X T) (force₁ force₂ : timeL2 Y T),
      timeH1.trace0 _ T u₁ = timeH1.trace0 _ T u₂ →
      field₁ =ᵐ[timeMeasure T] (fun t => W₁ t - f₀) →
      field₂ =ᵐ[timeMeasure T] (fun t => W₂ t - f₀) →
      (∀ᵐ t ∂timeMeasure T, ‖K (W₁ t - f₀)‖ ≤ outer → force₁ t =
        m (alpha t (K (W₁ t - f₀))) (Q (W₁ t)) + reaction t (K (W₁ t - f₀)) -
          L (W₁ t - f₀)) →
      (∀ᵐ t ∂timeMeasure T, ‖K (W₂ t - f₀)‖ ≤ outer → force₂ t =
        m (alpha t (K (W₂ t - f₀))) (Q (W₂ t)) + reaction t (K (W₂ t - f₀)) -
          L (W₂ t - f₀)) →
      P.compLpL 2 (timeMeasure T) field₁ = u₁.toFunL2 →
      P.compLpL 2 (timeMeasure T) field₂ = u₂.toFunL2 →
      timeH1.timeDeriv _ T u₁ = L.compLpL 2 (timeMeasure T) field₁ + force₁ →
      timeH1.timeDeriv _ T u₂ = L.compLpL 2 (timeMeasure T) field₂ + force₂ →
      ∃ δ > 0, δ ≤ T ∧ EqOn u₁.toFun u₂.toFun (Icc 0 δ) := by
  intro X Y Z K P Q m q L outer T houter hT hT1 A B Ca Cb hA hB hA0
    alpha reaction f₀ W₁ W₂ hW₁ hW₂ hW₁0 hW₂0 u₁ u₂ field₁ field₂ force₁ force₂
    htrace hfield₁ hfield₂ hforce₁ hforce₂ hlink₁ hlink₂ hpde₁ hpde₂
  let D : Z →L[ℝ] Y := AddCircle.parameterDerivativeHsPi (ι := ι) g (1 : ℕ)
  let d : Y →L[ℝ] Y := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    appHs g 0 0 (1 : ℕ) (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
  obtain ⟨r, hr, hrOuter, _, _, _, η, hη, hηT, hcontract⟩ :=
    exists_pos_shifted_tame_radius_window m Q D d f₀ Ca Ca Cb houter hT hT1 field₁ field₂
  obtain ⟨ζ, hζ, _, hKsmall⟩ := exists_common_initial_interval_norm_le
    hT hr K hW₁ hW₂ hW₁0 hW₂0
  let δ := min η (min ζ r)
  have hδ : 0 < δ := lt_min hη (lt_min hζ hr)
  have hδη : δ ≤ η := min_le_left _ _
  have hδζ : δ ≤ ζ := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ r := (min_le_right _ _).trans (min_le_right _ _)
  have hδT : δ ≤ T := hδη.trans hηT
  have hstates (t : ℝ) (ht : t ∈ Icc 0 δ) :
      ‖K (W₁ t - f₀)‖ ≤ r ∧ ‖K (W₂ t - f₀)‖ ≤ r :=
    hKsmall t ⟨ht.1, ht.2.trans hδζ⟩
  have hcontract' :
      (‖m‖ * (Ca : ℝ) * ‖Q‖) * r * (1 + (δ - 0)) +
        (‖m‖ * (Ca : ℝ) * ‖Q f₀‖ + (Cb : ℝ) + ‖d‖ * ‖D‖) *
          Real.sqrt (δ - 0) * Real.sqrt (1 + (δ - 0)) +
        (‖m‖ * (Ca : ℝ) * ‖Q‖) * Real.sqrt (1 + (δ - 0)) *
          (‖timeL2.slice field₁ 0 δ le_rfl hδT‖ +
            ‖timeL2.slice field₂ 0 δ le_rfl hδT‖) < 1 := by
    simpa only [NNReal.coe_mul, NNReal.coe_add, coe_nnnorm] using
      hcontract 0 δ le_rfl hδT (by simpa only [sub_zero] using hδ.le)
        (by simpa only [sub_zero] using hδη)
  refine ⟨δ, hδ, hδT, ?_⟩
  exact circle_continuous_state_eq_on_of_radius (ι := ι) g
    houter hr.le hrOuter hδ hδT hδr A B Ca Cb hA hB hA0 f₀ W₁ W₂
    u₁ u₂ field₁ field₂ force₁ force₂ htrace hfield₁ hfield₂ hforce₁ hforce₂
    hlink₁ hlink₂ hpde₁ hpde₂ hstates hcontract'

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
end

section
noncomputable section

open private exists_timeH1_strongPair_comp from
  DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication

open MeasureTheory Set
open scoped Manifold NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem circle_continuous_state_local_uniqueness_projected
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    let X : Type _ := CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)
    let Y : Type _ := CircleHsPi g ι ((1 : ℕ) : ℝ)
    let Y₀ : Type _ := CircleHsPi g ι (1 : ℝ)
    let S₀ : Y →L[ℝ] Y₀ := circleHsPiInclusion g ι
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let Z : Type _ := CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)
    let K : X →L[ℝ] Z := circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P : X →L[ℝ] Y := circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let Q : X →L[ℝ] Y := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g (1 : ℕ)
    let m : TensorHs g 0 0 ((1 : ℕ) : ℝ) →L[ℝ] Y →L[ℝ] Y :=
      coordinateMultiplication (ι := ι) (scalarHsMul g (1 : ℕ) (by norm_num))
    let q : TensorHs g 0 0 ((1 : ℕ) : ℝ) := ccTensorToHs g 0 ((1 : ℕ) : ℝ)
      (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    let L : X →L[ℝ] Y := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    ∀ {outer T : ℝ} (houter : 0 < outer) (hT : 0 < T), T ≤ 1 →
    ∀ (A : ℝ → Metric.closedBall (0 : Z) outer → TensorHs g 0 0 ((1 : ℕ) : ℝ))
      (B : ℝ → Metric.closedBall (0 : Z) outer → Y) (Ca Cb : ℝ≥0),
      LipschitzWith Ca (fun p : ℝ × Metric.closedBall (0 : Z) outer => A p.1 p.2) →
      LipschitzWith Cb (fun p : ℝ × Metric.closedBall (0 : Z) outer => B p.1 p.2) →
      A 0 ⟨0, Metric.mem_closedBall_self houter.le⟩ = q →
    let alpha : ℝ → Z → TensorHs g 0 0 ((1 : ℕ) : ℝ) := extendClosedBall houter.le A
    let reaction : ℝ → Z → Y := extendClosedBall houter.le B
    ∀ (f₀ : X) (W₁ W₂ : ℝ → X),
      ContinuousOn W₁ (Icc 0 T) → ContinuousOn W₂ (Icc 0 T) →
      W₁ 0 = f₀ → W₂ 0 = f₀ →
    ∀ (u₁ u₂ : timeH1 Y₀ T) (field₁ field₂ : timeL2 X T) (force₁ force₂ : timeL2 Y₀ T),
      timeH1.trace0 _ T u₁ = 0 → timeH1.trace0 _ T u₂ = 0 →
      field₁ =ᵐ[timeMeasure T] (fun t => W₁ t - f₀) →
      field₂ =ᵐ[timeMeasure T] (fun t => W₂ t - f₀) →
      (∀ᵐ t ∂timeMeasure T, ‖K (W₁ t - f₀)‖ ≤ outer → force₁ t =
        S₀ (m (alpha t (K (W₁ t - f₀))) (Q (W₁ t)) + reaction t (K (W₁ t - f₀))) -
          S₀ (L (W₁ t - f₀))) →
      (∀ᵐ t ∂timeMeasure T, ‖K (W₂ t - f₀)‖ ≤ outer → force₂ t =
        S₀ (m (alpha t (K (W₂ t - f₀))) (Q (W₂ t)) + reaction t (K (W₂ t - f₀))) -
          S₀ (L (W₂ t - f₀))) →
      (S₀.comp P).compLpL 2 (timeMeasure T) field₁ = u₁.toFunL2 →
      (S₀.comp P).compLpL 2 (timeMeasure T) field₂ = u₂.toFunL2 →
      timeH1.timeDeriv _ T u₁ = (S₀.comp L).compLpL 2 (timeMeasure T) field₁ + force₁ →
      timeH1.timeDeriv _ T u₂ = (S₀.comp L).compLpL 2 (timeMeasure T) field₂ + force₂ →
      ∃ δ > 0, δ ≤ T ∧ EqOn u₁.toFun u₂.toFun (Icc 0 δ) := by
  intro X Y Y₀ S₀ Z K P Q m q L outer T houter hT hT1 A B Ca Cb hA hB hA0
    alpha reaction f₀ W₁ W₂ hW₁ hW₂ hW₁0 hW₂0 u₁ u₂ field₁ field₂ force₁ force₂
    hzero₁ hzero₂ hfield₁ hfield₂ hforce₁ hforce₂ hlink₁ hlink₂ hpde₁ hpde₂
  let R : Y₀ →L[ℝ] Y := circleHsPiInclusion g ι
    (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
  have hRS (v : Y) : R (S₀ v) = v := by
    apply PiLp.ext
    intro i
    change tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) (v i)) = v i
    rw [← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]
  have hSR (v : Y₀) : S₀ (R v) = v := by
    apply PiLp.ext
    intro i
    change tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
      (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ)) (v i)) = v i
    rw [← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]
  obtain ⟨v₁, hvzero₁, hvrep₁, hvlink₁, hvpde₁⟩ := exists_timeH1_strongPair_comp
    (S₀.comp P) (S₀.comp L) P L R
    (fun x => hRS (P x)) (fun x => hRS (L x)) u₁ field₁ force₁ hzero₁ hlink₁ hpde₁
  obtain ⟨v₂, hvzero₂, hvrep₂, hvlink₂, hvpde₂⟩ := exists_timeH1_strongPair_comp
    (S₀.comp P) (S₀.comp L) P L R
    (fun x => hRS (P x)) (fun x => hRS (L x)) u₂ field₂ force₂ hzero₂ hlink₂ hpde₂
  have hf₁ : ∀ᵐ t ∂timeMeasure T, ‖K (W₁ t - f₀)‖ ≤ outer →
      R.compLpL 2 (timeMeasure T) force₁ t =
        m (alpha t (K (W₁ t - f₀))) (Q (W₁ t)) + reaction t (K (W₁ t - f₀)) -
          L (W₁ t - f₀) := by
    filter_upwards [R.coeFn_compLpL force₁, hforce₁] with t ht hf
    intro hz
    rw [ht, hf hz, map_sub, hRS, hRS]
  have hf₂ : ∀ᵐ t ∂timeMeasure T, ‖K (W₂ t - f₀)‖ ≤ outer →
      R.compLpL 2 (timeMeasure T) force₂ t =
        m (alpha t (K (W₂ t - f₀))) (Q (W₂ t)) + reaction t (K (W₂ t - f₀)) -
          L (W₂ t - f₀) := by
    filter_upwards [R.coeFn_compLpL force₂, hforce₂] with t ht hf
    intro hz
    rw [ht, hf hz, map_sub, hRS, hRS]
  obtain ⟨δ, hδ, hδT, heq⟩ := circle_continuous_state_local_uniqueness
    g houter hT hT1 A B Ca Cb hA hB hA0 f₀ W₁ W₂ hW₁ hW₂ hW₁0 hW₂0
    v₁ v₂ field₁ field₂ (R.compLpL 2 (timeMeasure T) force₁)
      (R.compLpL 2 (timeMeasure T) force₂) (hvzero₁.trans hvzero₂.symm)
      hfield₁ hfield₂ hf₁ hf₂ hvlink₁ hvlink₂ hvpde₁ hvpde₂
  refine ⟨δ, hδ, hδT, ?_⟩
  intro t ht
  have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hδT⟩
  have h : R (u₁.toFun t) = R (u₂.toFun t) :=
    (hvrep₁ htT).symm.trans ((heq ht).trans (hvrep₂ htT))
  simpa only [hSR] using congrArg S₀ h

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
end

section
noncomputable section

open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem continuous_state_local_uniqueness_of_coefficients
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ}
    {G : (Option (Fin n ⊕ Fin n) → ℝ) → Fin n → ℝ}
    {domain : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    {jet : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)}
    (C : ScalarVectorTimeCoefficients g₀ F G domain jet)
    (hC0 : ScalarVectorTimeCoefficients.diffusion C 0
      ⟨0, Metric.mem_closedBall_self (ScalarVectorTimeCoefficients.radius_pos C).le⟩ =
      ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S₀ := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    let L₀ := S₀.comp (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)))
    let rawAlpha := fun t z => tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J z))
    let rawReaction := fun t z => circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J z))
    ∀ {S : ℝ}, 0 < S → S ≤ 1 →
    ∀ (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) (W₁ W₂ : ℝ → _),
      ContinuousOn W₁ (Icc 0 S) → ContinuousOn W₂ (Icc 0 S) →
      W₁ 0 = f₀ → W₂ 0 = f₀ →
    ∀ (u₁ u₂ : timeH1 (CircleHsPi g₀ (Fin n) (1 : ℝ)) S)
      (field₁ field₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) S)
      (force₁ force₂ : timeL2 (CircleHsPi g₀ (Fin n) (1 : ℝ)) S),
      timeH1.trace0 _ S u₁ = 0 → timeH1.trace0 _ S u₂ = 0 →
      field₁ =ᵐ[timeMeasure S] (fun t => W₁ t - f₀) →
      field₂ =ᵐ[timeMeasure S] (fun t => W₂ t - f₀) →
      force₁ =ᵐ[timeMeasure S] (fun t =>
        S₀ (m (rawAlpha t (K (W₁ t - f₀))) (Q (W₁ t)) +
          rawReaction t (K (W₁ t - f₀))) - L₀ (W₁ t - f₀)) →
      force₂ =ᵐ[timeMeasure S] (fun t =>
        S₀ (m (rawAlpha t (K (W₂ t - f₀))) (Q (W₂ t)) +
          rawReaction t (K (W₂ t - f₀))) - L₀ (W₂ t - f₀)) →
      P.compLpL 2 (timeMeasure S) field₁ = u₁.toFunL2 →
      P.compLpL 2 (timeMeasure S) field₂ = u₂.toFunL2 →
      timeH1.timeDeriv _ S u₁ = L₀.compLpL 2 (timeMeasure S) field₁ + force₁ →
      timeH1.timeDeriv _ S u₂ = L₀.compLpL 2 (timeMeasure S) field₂ + force₂ →
      ∃ δ > 0, δ ≤ S ∧ EqOn u₁.toFun u₂.toFun (Icc 0 δ) := by
  intro J K P S₀ Q m L₀ rawAlpha rawReaction S hS hS1 f₀ W₁ W₂ hW₁ hW₂
    hW₁0 hW₂0 u₁ u₂ field₁ field₂ force₁ force₂ htrace₁ htrace₂
    hfield₁ hfield₂ hforce₁ hforce₂ hlink₁ hlink₂ hpde₁ hpde₂
  let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
    (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
  obtain ⟨outer, houter, _, hJouter⟩ :=
    J.exists_pos_norm_mul_le (ScalarVectorTimeCoefficients.radius_pos C)
  let A := fun t (z : Metric.closedBall
      (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer) =>
    tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (ScalarVectorTimeCoefficients.diffusion C t (J.closedBallMap hJouter z))
  let B := fun t (z : Metric.closedBall
      (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer) =>
    circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (ScalarVectorTimeCoefficients.reaction C t (J.closedBallMap hJouter z))
  let Ca := ScalarVectorTimeCoefficients.diffusionLipschitz C * (1 + ‖J‖₊)
  let Cb := ScalarVectorTimeCoefficients.reactionLipschitz C * (1 + ‖J‖₊)
  have hA : LipschitzWith Ca
      (fun p : ℝ × Metric.closedBall
        (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer => A p.1 p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change dist (tensorHsCongrL g₀ 0 0 _ _) (tensorHsCongrL g₀ 0 0 _ _) ≤ _
    rw [dist_eq_norm, ← map_sub, tensorHsCongrL_apply, norm_tensorHsCongr]
    simpa only [dist_eq_norm] using
      ((ScalarVectorTimeCoefficients.diffusion_lipschitz C).prod_precomp_closedBall
        J hJouter).dist_le_mul p q
  have hB : LipschitzWith Cb
      (fun p : ℝ × Metric.closedBall
        (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer => B p.1 p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change dist (circleHsPiCongr g₀ (Fin n) _ _) (circleHsPiCongr g₀ (Fin n) _ _) ≤ _
    rw [dist_eq_norm, ← map_sub, circleHsPiCongr_norm]
    simpa only [dist_eq_norm] using
      ((ScalarVectorTimeCoefficients.reaction_lipschitz C).prod_precomp_closedBall
        J hJouter).dist_le_mul p q
  have hA0 : A 0 ⟨0, Metric.mem_closedBall_self houter.le⟩ = q := by
    change tensorHsCongrL g₀ 0 0 _ (ScalarVectorTimeCoefficients.diffusion C 0 _) = _
    have hz : J.closedBallMap hJouter ⟨0, Metric.mem_closedBall_self houter.le⟩ =
        ⟨0, Metric.mem_closedBall_self (ScalarVectorTimeCoefficients.radius_pos C).le⟩ := by
      apply Subtype.ext
      exact map_zero J
    rw [hz, hC0,
      tensorHsCongrL_ccTensorToHs]
  let alpha := extendClosedBall houter.le A
  let reaction := extendClosedBall houter.le B
  have hcoeff (t : ℝ) (z : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
      (hz : ‖z‖ ≤ outer) :
      alpha t z = tensorHsCongrL g₀ 0 0
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J z)) ∧
      reaction t z = circleHsPiCongr g₀ (Fin n)
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J z)) := by
    have hzo : z ∈ Metric.closedBall 0 outer := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hzJ : J z ∈ Metric.closedBall 0 (ScalarVectorTimeCoefficients.radius C) := by
      have hnorm := (J.le_opNorm z).trans
        ((mul_le_mul_of_nonneg_left (hz) (norm_nonneg J)).trans hJouter)
      simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
    constructor
    · rw [show alpha t z = A t ⟨z, hzo⟩ from extendClosedBall_apply houter.le A t z hzo,
        extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J z) hzJ]
      rfl
    · rw [show reaction t z = B t ⟨z, hzo⟩ from extendClosedBall_apply houter.le B t z hzo,
        extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J z) hzJ]
      rfl
  have hforce₁outer : ∀ᵐ t ∂timeMeasure S,
      ‖K (W₁ t - f₀)‖ ≤ outer → force₁ t =
        S₀ (m (alpha t (K (W₁ t - f₀))) (Q (W₁ t)) +
          reaction t (K (W₁ t - f₀))) - L₀ (W₁ t - f₀) := by
    filter_upwards [hforce₁] with t ht
    intro hz
    dsimp only [rawAlpha, rawReaction] at ht
    rw [ht, ← (hcoeff t (K (W₁ t - f₀)) hz).1,
      ← (hcoeff t (K (W₁ t - f₀)) hz).2]
  have hforce₂outer : ∀ᵐ t ∂timeMeasure S,
      ‖K (W₂ t - f₀)‖ ≤ outer → force₂ t =
        S₀ (m (alpha t (K (W₂ t - f₀))) (Q (W₂ t)) +
          reaction t (K (W₂ t - f₀))) - L₀ (W₂ t - f₀) := by
    filter_upwards [hforce₂] with t ht
    intro hz
    dsimp only [rawAlpha, rawReaction] at ht
    rw [ht, ← (hcoeff t (K (W₂ t - f₀)) hz).1,
      ← (hcoeff t (K (W₂ t - f₀)) hz).2]
  have hpde₁' : timeH1.timeDeriv _ S u₁ =
      L₀.compLpL 2 (timeMeasure S) field₁ + force₁ := by
    exact hpde₁
  have hpde₂' : timeH1.timeDeriv _ S u₂ =
      L₀.compLpL 2 (timeMeasure S) field₂ + force₂ := by
    exact hpde₂
  let P₁ := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
  have hP : S₀.comp P₁ = P := by
    apply ContinuousLinearMap.ext
    intro v
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2) (v i)).symm
  have hlink₁' : (S₀.comp P₁).compLpL 2 (timeMeasure S) field₁ = u₁.toFunL2 := by
    rw [hP]
    exact hlink₁
  have hlink₂' : (S₀.comp P₁).compLpL 2 (timeMeasure S) field₂ = u₂.toFunL2 := by
    rw [hP]
    exact hlink₂
  exact circle_continuous_state_local_uniqueness_projected
    g₀ houter hS hS1 A B Ca Cb hA hB hA0 f₀ W₁ W₂ hW₁ hW₂ hW₁0 hW₂0
      u₁ u₂ field₁ field₂ force₁ force₂ htrace₁ htrace₂
      hfield₁ hfield₂ hforce₁outer hforce₂outer hlink₁' hlink₂' hpde₁' hpde₂'

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end
end

section
noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem curve_eq_on_of_displacement_eq
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {n : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) n)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {Jset : Set ℝ} {c₁ c₂ : CurveMap M}
    {P : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) (1 : ℝ)}
    {W₁ W₂ : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)}
    {f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)}
    {u₁ u₂ : ℝ → CircleHsPi g₀ (Fin n) (1 : ℝ)}
    (hrep₁ : EqOn u₁ (fun t => P (W₁ t - f₀)) Jset)
    (hrep₂ : EqOn u₂ (fun t => P (W₂ t - f₀)) Jset)
    (heval₁ : ∀ t ∈ Jset, ∀ z : AddCircle (1 : ℝ),
      scalarH1PiToContinuous g₀ (P (W₁ t)) z = fun i => e.map (c₁ z t) i)
    (heval₂ : ∀ t ∈ Jset, ∀ z : AddCircle (1 : ℝ),
      scalarH1PiToContinuous g₀ (P (W₂ t)) z = fun i => e.map (c₂ z t) i)
    (heq : EqOn u₁ u₂ Jset) :
    ∀ z t, t ∈ Jset → c₁ z t = c₂ z t := by
  intro z t ht
  apply e.isClosedEmbedding.injective
  have hdisp : P (W₁ t - f₀) = P (W₂ t - f₀) :=
    (hrep₁ ht).symm.trans ((heq ht).trans (hrep₂ ht))
  have hobs := congrArg (fun v => scalarH1PiToContinuous g₀ v z) hdisp
  simp only [map_sub, ContinuousMap.sub_apply] at hobs
  have hw := sub_left_inj.mp hobs
  rw [heval₁ t ht z, heval₂ t ht z] at hw
  exact PiLp.ext fun i => congrFun hw i

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end
end

section
noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem parametric_equation_mono
    (g : ℝ → SmoothRiemannianMetric I M) {T S : ℝ}
    {c : CurveMap M} (hc : c.SmoothOn (I := I) (Icc 0 T))
    (heq : ∀ x t, t ∈ Icc 0 T →
      c.velocity (I := I) (Icc 0 T) x t =
        c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t)
    (hS : 0 < S) (hST : S ≤ T) :
    ∀ x t, t ∈ Icc 0 S →
      c.velocity (I := I) (Icc 0 S) x t =
        c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  intro x t ht
  have hsub : Icc (0 : ℝ) S ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl hST
  have houter := (c.time_slice_contMDiffWithinAt (Icc 0 T) hc x t
    (hsub ht)).mdifferentiableWithinAt (by simp)
  have hmap : MapsTo (fun s : ℝ => s + 0) (Icc 0 S) (Icc 0 T) := by
    intro s hs
    simpa only [add_zero] using hsub hs
  have hv := CurveMap.velocity_time_translate (c := c) 0 hmap
    (by simpa only [add_zero] using houter) ((uniqueDiffOn_Icc hS) t ht)
  have hc0 : (fun z s => c z (s + 0)) = c := by
    funext z s
    rw [add_zero]
  rw [hc0, add_zero] at hv
  exact hv.trans (heq x t (hsub ht))


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end
end

section
noncomputable section

open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {n : ℕ}

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem local_uniqueness_of_parametric_curve_and_observed_pair
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    (ht₀ : 0 ∈ D.regular)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) n)
    {ret : EuclideanSpace ℝ (Fin n) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hret : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ ret U)
    (hEU : range e.map ⊆ U) (hleft : ∀ p, ret (e.map p) = p) (β : U)
    (hG : MetricFamilySmoothOn D
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hret)) :
  let C := ambientCoefficients c₀ g ht₀ e.smooth hret hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  let f₀ := ambientSobolev c₀ (g 0) e.map e.smooth (((1 : ℕ) : ℝ) + 2)
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let K := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    let L := S.comp (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)))
    ∀ {T : ℝ} (hT : 0 < T), T ≤ ScalarVectorTimeCoefficients.radius C → T ≤ 1 →
    ∀ {c₁ c₂ : CurveMap M}
      (hc₂ : c₂.SmoothOn (I := I) (Icc 0 T))
      (hi₂ : c₂.ImmersedOn (I := I) (Icc 0 T)),
      (∀ z, c₂ z 0 = c₀.map z) →
      (∀ x t, t ∈ Icc 0 T → c₂.velocity (I := I) (Icc 0 T) x t =
        c₂.speed g x t ^ (-2 : ℤ) • c₂.Dx g c₂.X x t) →
      (∀ t (ht : t ∈ Icc 0 T),
        ‖J (K (fixedAmbientSobolev e g₀ (slice c₂ hc₂ hi₂ t ht) - f₀))‖ ≤
          ScalarVectorTimeCoefficients.radius C) →
    ∀ W₁ : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2),
      ContinuousOn W₁ (Icc 0 T) → W₁ 0 = f₀ →
      (∀ t ∈ Icc 0 T, ∀ z : AddCircle (1 : ℝ),
        scalarH1PiToContinuous g₀ (P (W₁ t)) z = fun i => e.map (c₁ z t) i) →
    let alpha := fun t => tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W₁ t - f₀))))
    let reaction := fun t => circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (K (W₁ t - f₀))))
    let V := fun t => S (m (alpha t) (Q (W₁ t)) + reaction t)
    ∀ (u₁ : timeH1 (CircleHsPi g₀ (Fin n) (1 : ℝ)) T)
      (field₁ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T)
      (force₁ : timeL2 (CircleHsPi g₀ (Fin n) (1 : ℝ)) T),
      timeH1.trace0 _ T u₁ = 0 →
      EqOn u₁.toFun (fun t => P (W₁ t - f₀)) (Icc 0 T) →
      field₁ =ᵐ[timeMeasure T] (fun t => W₁ t - f₀) →
      force₁ =ᵐ[timeMeasure T] (fun t => V t - L (W₁ t - f₀)) →
      P.compLpL 2 (timeMeasure T) field₁ = u₁.toFunL2 →
      timeH1.timeDeriv _ T u₁ = L.compLpL 2 (timeMeasure T) field₁ + force₁ →
      ∃ δ > 0, δ ≤ T ∧ ∀ z t, t ∈ Icc 0 δ → c₁ z t = c₂ z t := by
  generalize hC : ambientCoefficients c₀ g ht₀ e.smooth hret hEU hleft β hG = C₁
  intro C g₀ f₀ J K P S Q m L T hT hTC hT1 c₁ c₂ hc₂ hi₂ hinit₂ heq₂ hsmall₂
    W₁ hW₁ hW₁0 hW₁eval alpha reaction V u₁ field₁ force₁
    htrace₁ hrep₁ hfield₁ hforce₁ hlink₁ hpde₁
  dsimp only [C, g₀, f₀, J, K, P, S, Q, m, L, alpha, reaction, V] at *
  have hprod := exists_strongPair_of_parametric_curve c₀ g ht₀ e hret hEU hleft β hG (T := T)
  rw [hC] at hprod
  dsimp only at hprod
  obtain ⟨W₂, hW₂, hW₂0, _, hW₂eval, _, u₂, field₂, force₂,
      htrace₂, hrep₂, hfield₂, hforce₂, hlink₂, hpde₂⟩ :=
    hprod hT hTC c₂ hc₂ hi₂ hinit₂ heq₂ hsmall₂
  have hinitial := initial_diffusion_coefficients c₀ g e.smooth hret hEU hleft β C
  have huniq := continuous_state_local_uniqueness_of_coefficients g₀ C hinitial (S := T)
  dsimp only [C, g₀, f₀, J, K, P, S, Q, m, L] at huniq
  specialize huniq hT hT1 f₀ W₁ W₂ hW₁ hW₂ hW₁0 hW₂0
  specialize huniq u₁ u₂ field₁ field₂ force₁ force₂
  specialize huniq htrace₁ htrace₂ hfield₁ hfield₂
  specialize huniq hforce₁ hforce₂
  specialize huniq hlink₁ hlink₂ hpde₁ hpde₂
  obtain ⟨δ, hδ, hδT, huEq⟩ := huniq
  have hδsub : Icc (0 : ℝ) δ ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl hδT
  refine ⟨δ, hδ, hδT, ?_⟩
  exact curve_eq_on_of_displacement_eq e g₀
    (hrep₁.mono hδsub) (hrep₂.mono hδsub)
    (fun t ht => hW₁eval t (hδsub ht)) (fun t ht => hW₂eval t (hδsub ht)) huEq

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end
end

section
noncomputable section

open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {n : ℕ}

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem local_uniqueness_of_small_parametric_curves
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    (ht₀ : 0 ∈ D.regular)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) n)
    {ret : EuclideanSpace ℝ (Fin n) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hret : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ ret U)
    (hEU : range e.map ⊆ U) (hleft : ∀ p, ret (e.map p) = p) (β : U)
    (hG : MetricFamilySmoothOn D
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hret)) :
  let C := ambientCoefficients c₀ g ht₀ e.smooth hret hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  let f₀ := ambientSobolev c₀ (g 0) e.map e.smooth (((1 : ℕ) : ℝ) + 2)
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let K := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    ∀ {T : ℝ} (hT : 0 < T), T ≤ ScalarVectorTimeCoefficients.radius C → T ≤ 1 →
    ∀ {c₁ c₂ : CurveMap M}
      (hc₁ : c₁.SmoothOn (I := I) (Icc 0 T))
      (hc₂ : c₂.SmoothOn (I := I) (Icc 0 T))
      (hi₁ : c₁.ImmersedOn (I := I) (Icc 0 T))
      (hi₂ : c₂.ImmersedOn (I := I) (Icc 0 T)),
      (∀ z, c₁ z 0 = c₀.map z) → (∀ z, c₂ z 0 = c₀.map z) →
      (∀ x t, t ∈ Icc 0 T → c₁.velocity (I := I) (Icc 0 T) x t =
        c₁.speed g x t ^ (-2 : ℤ) • c₁.Dx g c₁.X x t) →
      (∀ x t, t ∈ Icc 0 T → c₂.velocity (I := I) (Icc 0 T) x t =
        c₂.speed g x t ^ (-2 : ℤ) • c₂.Dx g c₂.X x t) →
      (∀ t (ht : t ∈ Icc 0 T),
        ‖J (K (fixedAmbientSobolev e g₀ (slice c₁ hc₁ hi₁ t ht) - f₀))‖ ≤
          ScalarVectorTimeCoefficients.radius C) →
      (∀ t (ht : t ∈ Icc 0 T),
        ‖J (K (fixedAmbientSobolev e g₀ (slice c₂ hc₂ hi₂ t ht) - f₀))‖ ≤
          ScalarVectorTimeCoefficients.radius C) →
      ∃ δ > 0, δ ≤ T ∧ ∀ z t, t ∈ Icc 0 δ → c₁ z t = c₂ z t := by
  generalize hC : ambientCoefficients c₀ g ht₀ e.smooth hret hEU hleft β hG = C₁
  intro C g₀ f₀ J K T hT hTC hT1 c₁ c₂ hc₁ hc₂ hi₁ hi₂ hinit₁ hinit₂
    heq₁ heq₂ hsmall₁ hsmall₂
  dsimp only [C, g₀, f₀, J, K] at *
  have hprod := exists_strongPair_of_parametric_curve c₀ g ht₀ e hret hEU hleft β hG (T := T)
  rw [hC] at hprod
  dsimp only at hprod
  obtain ⟨W₁, hW₁, hW₁0, _, hW₁eval, _, u₁, field₁, force₁,
      htrace₁, hrep₁, hfield₁, hforce₁, hlink₁, hpde₁⟩ :=
    hprod hT hTC c₁ hc₁ hi₁ hinit₁ heq₁ hsmall₁
  have hnext := local_uniqueness_of_parametric_curve_and_observed_pair
    c₀ g ht₀ e hret hEU hleft β hG (T := T)
  rw [hC] at hnext
  dsimp only [C, g₀, f₀, J, K] at hnext
  exact hnext hT hTC hT1 hc₂ hi₂ hinit₂ heq₂ hsmall₂ W₁ hW₁ hW₁0 hW₁eval
    u₁ field₁ force₁ htrace₁ hrep₁ hfield₁ hforce₁ hlink₁ hpde₁

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end
end

section
noncomputable section

open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {n : ℕ}

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem exists_initial_interval_eq_of_parametric_curves_of_retraction
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    (ht₀ : 0 ∈ D.regular)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) n)
    {ret : EuclideanSpace ℝ (Fin n) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hret : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ ret U)
    (hEU : range e.map ⊆ U) (hleft : ∀ p, ret (e.map p) = p) (β : U)
    (hG : MetricFamilySmoothOn D
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hret))
    {T : ℝ} (hT : 0 < T) {c₁ c₂ : CurveMap M}
    (hc₁ : c₁.SmoothOn (I := I) (Icc 0 T))
    (hc₂ : c₂.SmoothOn (I := I) (Icc 0 T))
    (hi₁ : c₁.ImmersedOn (I := I) (Icc 0 T))
    (hi₂ : c₂.ImmersedOn (I := I) (Icc 0 T))
    (hinit₁ : ∀ z, c₁ z 0 = c₀.map z) (hinit₂ : ∀ z, c₂ z 0 = c₀.map z)
    (heq₁ : ∀ x t, t ∈ Icc 0 T → c₁.velocity (I := I) (Icc 0 T) x t =
      c₁.speed g x t ^ (-2 : ℤ) • c₁.Dx g c₁.X x t)
    (heq₂ : ∀ x t, t ∈ Icc 0 T → c₂.velocity (I := I) (Icc 0 T) x t =
      c₂.speed g x t ^ (-2 : ℤ) • c₂.Dx g c₂.X x t) :
    ∃ δ > 0, δ ≤ T ∧ ∀ z t, t ∈ Icc 0 δ → c₁ z t = c₂ z t := by
  classical
  let C := ambientCoefficients c₀ g ht₀ e.smooth hret hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  let f₀ := ambientSobolev c₀ (g 0) e.map e.smooth (((1 : ℕ) : ℝ) + 2)
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let K := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
  obtain ⟨Wa, hWa, hWa0, hWaslice, _⟩ :=
    exists_continuousOn_fixedAmbientSobolev_curve_with_initial e (g 0) c₀ hT hc₁ hi₁ hinit₁
  obtain ⟨Wb, hWb, hWb0, hWbslice, _⟩ :=
    exists_continuousOn_fixedAmbientSobolev_curve_with_initial e (g 0) c₀ hT hc₂ hi₂ hinit₂
  obtain ⟨s, hs, hsT, hstate⟩ := exists_common_initial_interval_norm_le
    hT (ScalarVectorTimeCoefficients.radius_pos C) (J.comp K) hWa hWb hWa0 hWb0
  let S := min s (min (ScalarVectorTimeCoefficients.radius C) 1)
  have hS : 0 < S := lt_min hs (lt_min (ScalarVectorTimeCoefficients.radius_pos C) zero_lt_one)
  have hSs : S ≤ s := min_le_left _ _
  have hST : S ≤ T := hSs.trans hsT
  have hSC : S ≤ ScalarVectorTimeCoefficients.radius C :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hS1 : S ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : Icc (0 : ℝ) S ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl hST
  have hc₁S : c₁.SmoothOn (I := I) (Icc 0 S) :=
    hc₁.mono (prod_mono le_rfl hsub)
  have hc₂S : c₂.SmoothOn (I := I) (Icc 0 S) :=
    hc₂.mono (prod_mono le_rfl hsub)
  have hi₁S : c₁.ImmersedOn (I := I) (Icc 0 S) := fun x t ht => hi₁ x t (hsub ht)
  have hi₂S : c₂.ImmersedOn (I := I) (Icc 0 S) := fun x t ht => hi₂ x t (hsub ht)
  have hsmall₁ (t : ℝ) (ht : t ∈ Icc 0 S) :
      ‖J (K (fixedAmbientSobolev e g₀ (slice c₁ hc₁S hi₁S t ht) - f₀))‖ ≤
        ScalarVectorTimeCoefficients.radius C := by
    have h := (hstate t ⟨ht.1, ht.2.trans hSs⟩).1
    rw [hWaslice t (hsub ht)] at h
    exact h
  have hsmall₂ (t : ℝ) (ht : t ∈ Icc 0 S) :
      ‖J (K (fixedAmbientSobolev e g₀ (slice c₂ hc₂S hi₂S t ht) - f₀))‖ ≤
        ScalarVectorTimeCoefficients.radius C := by
    have h := (hstate t ⟨ht.1, ht.2.trans hSs⟩).2
    rw [hWbslice t (hsub ht)] at h
    exact h
  have hlocal := local_uniqueness_of_small_parametric_curves
    c₀ g ht₀ e hret hEU hleft β hG (T := S)
  dsimp only [C, g₀, f₀, J, K] at hSC hsmall₁ hsmall₂
  dsimp only at hlocal
  obtain ⟨δ, hδ, hδS, heqδ⟩ := hlocal hS hSC hS1 hc₁S hc₂S hi₁S hi₂S
    hinit₁ hinit₂ (CurveMap.parametric_equation_mono g hc₁ heq₁ hS hST)
    (CurveMap.parametric_equation_mono g hc₂ heq₂ hS hST) hsmall₁ hsmall₂
  exact ⟨δ, hδ, hδS.trans hST, heqδ⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

end
