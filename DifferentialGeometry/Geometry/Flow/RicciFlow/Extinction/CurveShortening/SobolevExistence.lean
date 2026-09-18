import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.ClassicalEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParametricEquationNaturality
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.PairedSmallness
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Approximation.Slice
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.Local
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication
import DifferentialGeometry.Topology.Compactness.TimeInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.TimeTranslation
import DifferentialGeometry.Geometry.Metric.Family.TimeShift
import Mathlib.Tactic.DefEqTransformations
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.AddCircleIteratedDerivativeContinuity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleDerivativeForcingLift
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.LpInclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleFirstJet
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleParameterNorm
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.PiLp
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.TranslatedComposition
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.ShiftedTimeDependent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicReconstruction
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.AddCircleDerivativeContinuity
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleFiniteRegularity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleLinearizedLift
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleContractionRadius
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.ShiftedCoefficients
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcing
import DifferentialGeometry.Analysis.Integration.Lp.PiLp
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleTimeTameComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleContinuousComposition
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.PointwiseEquation
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleClassicalDerivative
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.ContinuousRepresentative
import Mathlib.MeasureTheory.Measure.OpenPos
import DifferentialGeometry.Analysis.FunctionalAnalysis.ContinuousLinearMap.ClosedBall
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacian
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivativeLift
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.Multiplication
import Mathlib.Tactic.Module
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.TimeInterval
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.FiniteProduct
import DifferentialGeometry.Topology.Manifold.AddCircle
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Tactic.Positivity
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuousInjective
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ChartEquation
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.SimultaneousComposition
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Retraction
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuous
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.PullbackMetric
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet

section
noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private def coordinateMultiplication
    {ι X : Type*} [Fintype ι] [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : X →L[ℝ] X →L[ℝ] X) :
    X →L[ℝ] PiLp 2 (fun _ : ι => X) →L[ℝ] PiLp 2 (fun _ : ι => X) :=
  LinearMap.mkContinuous
    { toFun := fun x => ContinuousLinearMap.piLpMap 2 (fun _ : ι => m x)
      map_add' := by
        intro x y
        ext v i
        simp only [ContinuousLinearMap.piLpMap_apply, map_add,
          add_apply, PiLp.add_apply]
      map_smul' := by
        intro c x
        ext v i
        simp only [ContinuousLinearMap.piLpMap_apply, map_smul,
          smul_apply, PiLp.smul_apply, RingHom.id_apply] }
    ‖m‖ (fun x => (ContinuousLinearMap.norm_piLpMap_le
      (fun _ : ι => m x) (norm_nonneg (m x)) (fun _ => le_refl _)).trans (m.le_opNorm x))

private theorem shifted_circle_operator_identity
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (hn : Module.finrank ℝ ℝ / 2 + 1 ≤ n)
    (f₀ v : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2)))
    (a : TensorHs g 0 0 (n : ℝ))
    (b : PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) :
    let m := coordinateMultiplication (ι := ι) (scalarHsMul g n hn)
    let q := ccTensorToHs g 0 (n : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 n (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g n
    let D := AddCircle.parameterDerivativeHsPi (ι := ι) g n
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith))
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ)) v +
      (m (a - q) (Q v) + m a (Q f₀) + b - d (D (J v))) =
      m a (Q (f₀ + v)) + b := by
  dsimp only
  rw [AddCircle.piLpMap_tensorScaleLaplacian_eq_principal_add_drift]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  have hq : coordinateMultiplication (ι := ι) (scalarHsMul g n hn)
      (ccTensorToHs g 0 (n : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))) =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        appHs g 0 0 n (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))) := by
    change ContinuousLinearMap.piLpMap 2 (fun _ : ι => _) = _
    rw [scalarHsMul_apply_ccTensorToHs_left]
  rw [← hq]
  simp only [map_add, map_sub, sub_apply]
  module

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

private theorem shifted_time_nemy_meas
    {A X Y Z : Type*}
    [SeminormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
    (m : A →L[ℝ] Y →L[ℝ] Y)
    (Q : X →L[ℝ] Y) (J : X →L[ℝ] Z) (D : Z →L[ℝ] Y)
    (c : Y) (d : Y →L[ℝ] Y) (q : A)
    (a : ℝ → Z → A) (B : ℝ → Z → Y)
    {R τ : ℝ} {S : Set X} (hzero : (0 : X) ∈ S)
    (hS : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (ha : Continuous (fun p : Set.Icc (0 : ℝ) τ × Metric.closedBall (0 : Z) R =>
      a p.1 p.2))
    (hB : Continuous (fun p : Set.Icc (0 : ℝ) τ × Metric.closedBall (0 : Z) R =>
      B p.1 p.2)) :
    let N := fun t (u : S) =>
      m (a t (J (u : X)) - q) (Q (u : X)) + m (a t (J (u : X))) c +
        B t (J (u : X)) - d (D (J (u : X)))
    Continuous (fun p : Set.Icc (0 : ℝ) τ × S => N p.1 p.2) ∧
      QuasiLinear.TimeNemyMeas hzero N τ := by
  let j : S → Metric.closedBall (0 : Z) R :=
    fun u => ⟨J (u : X), by simpa only [Metric.mem_closedBall, dist_zero_right] using hS u⟩
  have hj : Continuous j :=
    (J.continuous.comp continuous_subtype_val).subtype_mk _
  have hJ : Continuous (fun p : Set.Icc (0 : ℝ) τ × S => J (p.2 : X)) :=
    J.continuous.comp (continuous_subtype_val.comp continuous_snd)
  have hQ : Continuous (fun p : Set.Icc (0 : ℝ) τ × S => Q (p.2 : X)) :=
    Q.continuous.comp (continuous_subtype_val.comp continuous_snd)
  have ha' : Continuous (fun p : Set.Icc (0 : ℝ) τ × S => a p.1 (J (p.2 : X))) :=
    ha.comp (continuous_fst.prodMk (hj.comp continuous_snd))
  have hB' : Continuous (fun p : Set.Icc (0 : ℝ) τ × S => B p.1 (J (p.2 : X))) :=
    hB.comp (continuous_fst.prodMk (hj.comp continuous_snd))
  have hN : Continuous (fun p : Set.Icc (0 : ℝ) τ × S =>
      m (a p.1 (J (p.2 : X)) - q) (Q (p.2 : X)) +
        m (a p.1 (J (p.2 : X))) c + B p.1 (J (p.2 : X)) -
        d (D (J (p.2 : X)))) :=
    ((((m.continuous.comp (ha'.sub continuous_const)).clm_apply hQ).add
      ((m.continuous.comp ha').clm_apply continuous_const)).add hB').sub
        (d.continuous.comp (D.continuous.comp hJ))
  dsimp only
  refine ⟨hN, ?_⟩
  apply QuasiLinear.timeNemy_of_contOn_Icc hzero
  exact hN

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

private theorem shifted_tame_estimate
    {T A X Y Z : Type*}
    [SeminormedAddCommGroup A] [NormedSpace ℝ A]
    [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
    (m : A →L[ℝ] Y →L[ℝ] Y)
    (Q : X →L[ℝ] Y) (J : X →L[ℝ] Z) (D : Z →L[ℝ] Y)
    (c : Y) (d : Y →L[ℝ] Y) (q : A)
    (a : T → Z → A) (B : T → Z → Y)
    {R K L M : ℝ}
    (t : T)
    (ha_lip : ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖a t z - a t w‖ ≤ L * ‖z - w‖)
    (ha_close : ∀ z, ‖z‖ ≤ R → ‖a t z - q‖ ≤ K * R)
    (hB_lip : ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖B t z - B t w‖ ≤ M * ‖z - w‖)
    {u v : X} (hu : ‖J u‖ ≤ R) (hv : ‖J v‖ ≤ R) :
    let N := fun w : X =>
      m (a t (J w) - q) (Q w) + m (a t (J w)) c + B t (J w) - d (D (J w))
    (‖N u - N v‖ ≤
      (‖m‖ * K * ‖Q‖) * R * ‖u - v‖ +
      (‖m‖ * L * ‖c‖ + M + ‖d‖ * ‖D‖) * ‖J (u - v)‖ +
      (‖m‖ * L * ‖Q‖) * (‖u‖ + ‖v‖) * ‖J (u - v)‖) ∧
    ‖N 0‖ ≤ ‖m‖ * ‖a t 0‖ * ‖c‖ + ‖B t 0‖ := by
  dsimp only
  have hcoef_u := ha_close (J u) hu
  have hcoef_lip : ‖a t (J u) - a t (J v)‖ ≤ L * ‖J (u - v)‖ := by
    simpa only [map_sub] using ha_lip (J u) hu (J v) hv
  have hB : ‖B t (J u) - B t (J v)‖ ≤ M * ‖J (u - v)‖ := by
    simpa only [map_sub] using hB_lip (J u) hu (J v) hv
  have hprincipal :
      ‖m (a t (J u) - q) (Q u) - m (a t (J v) - q) (Q v)‖ ≤
        (‖m‖ * K * ‖Q‖) * R * ‖u - v‖ +
        (‖m‖ * L * ‖Q‖) * (‖u‖ + ‖v‖) * ‖J (u - v)‖ := by
    have heq : m (a t (J u) - q) (Q u) - m (a t (J v) - q) (Q v) =
        m (a t (J u) - q) (Q (u - v)) +
          m (a t (J u) - a t (J v)) (Q v) := by
      simp only [map_sub, sub_apply]
      module
    rw [heq]
    calc
      ‖m (a t (J u) - q) (Q (u - v)) +
          m (a t (J u) - a t (J v)) (Q v)‖ ≤
          ‖m (a t (J u) - q) (Q (u - v))‖ +
            ‖m (a t (J u) - a t (J v)) (Q v)‖ := norm_add_le _ _
      _ ≤ ‖m‖ * (K * R) * (‖Q‖ * ‖u - v‖) +
            ‖m‖ * (L * ‖J (u - v)‖) * (‖Q‖ * (‖u‖ + ‖v‖)) := by
        apply add_le_add
        · exact m.le_of_opNorm₂_le_of_le le_rfl hcoef_u (Q.le_opNorm _)
        · exact m.le_of_opNorm₂_le_of_le le_rfl hcoef_lip
            ((Q.le_opNorm v).trans
              (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg u)) (norm_nonneg Q)))
      _ = _ := by ring
  have hshift :
      ‖m (a t (J u)) c - m (a t (J v)) c‖ ≤
        (‖m‖ * L * ‖c‖) * ‖J (u - v)‖ := by
    have heq : m (a t (J u)) c - m (a t (J v)) c =
        m (a t (J u) - a t (J v)) c := by
      simp only [map_sub, sub_apply]
    rw [heq]
    calc
      ‖m (a t (J u) - a t (J v)) c‖ ≤
          ‖m‖ * ‖a t (J u) - a t (J v)‖ * ‖c‖ := m.le_opNorm₂ _ _
      _ ≤ ‖m‖ * (L * ‖J (u - v)‖) * ‖c‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoef_lip (norm_nonneg m)) (norm_nonneg c)
      _ = _ := by ring
  have hcorrection :
      ‖d (D (J u)) - d (D (J v))‖ ≤
        (‖d‖ * ‖D‖) * ‖J (u - v)‖ := by
    rw [← d.map_sub, ← D.map_sub, ← J.map_sub]
    calc
      ‖d (D (J (u - v)))‖ ≤ ‖d‖ * ‖D (J (u - v))‖ := d.le_opNorm _
      _ ≤ ‖d‖ * (‖D‖ * ‖J (u - v)‖) :=
        mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg d)
      _ = _ := by ring
  constructor
  · calc
      ‖(m (a t (J u) - q) (Q u) + m (a t (J u)) c + B t (J u) - d (D (J u))) -
          (m (a t (J v) - q) (Q v) + m (a t (J v)) c + B t (J v) - d (D (J v)))‖ =
        ‖(m (a t (J u) - q) (Q u) - m (a t (J v) - q) (Q v)) +
          (m (a t (J u)) c - m (a t (J v)) c) +
          (B t (J u) - B t (J v)) +
          -(d (D (J u)) - d (D (J v)))‖ := by congr 1; module
      _ ≤ ‖m (a t (J u) - q) (Q u) - m (a t (J v) - q) (Q v)‖ +
          ‖m (a t (J u)) c - m (a t (J v)) c‖ +
          ‖B t (J u) - B t (J v)‖ +
          ‖d (D (J u)) - d (D (J v))‖ := by
        simpa only [norm_neg] using (norm_add₄_le :
          ‖(m (a t (J u) - q) (Q u) - m (a t (J v) - q) (Q v)) +
              (m (a t (J u)) c - m (a t (J v)) c) +
              (B t (J u) - B t (J v)) +
              (-(d (D (J u)) - d (D (J v))))‖ ≤ _)
      _ ≤ _ := by linarith only [hprincipal, hshift, hB, hcorrection]
  · simp only [map_zero, zero_add, sub_zero]
    exact (norm_add_le _ _).trans (add_le_add (m.le_opNorm₂ _ _) le_rfl)

end DifferentialGeometry.Analysis.Parabolic


noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private abbrev CircleHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (a : ℝ) :=
  TensorHs g 0 0 a

private abbrev CircleHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (ι : Type*) (a : ℝ) :=
  PiLp 2 (fun _ : ι => CircleHs g a)

private def circleHsPiInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (ι : Type*) [hι : Fintype ι] {a b : ℝ} (hab : a ≤ b) :
    CircleHsPi g ι b →L[ℝ] CircleHsPi g ι a :=
  let _ := hι
  ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion (g := g)
    (r := 0) (s := 0) hab)

private def shiftedRemainder
    {A X Y Z : Type*}
    [SeminormedAddCommGroup A] [NormedSpace ℝ A]
    [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
    (m : A →L[ℝ] Y →L[ℝ] Y)
    (Q : X →L[ℝ] Y) (J : X →L[ℝ] Z) (D : Z →L[ℝ] Y)
    (c : Y) (d : Y →L[ℝ] Y) (q : A)
    (alpha : ℝ → Z → A) (reaction : ℝ → Z → Y) (R : ℝ)
    (t : ℝ) (v : {u : X | ‖J u‖ ≤ R}) : Y :=
  m (alpha t (J v.val) - q) (Q v.val) + m (alpha t (J v.val)) c +
    reaction t (J v.val) - d (D (J v.val))

variable {ι : Type*} [Fintype ι]

private theorem circle_shifted_time_partial_tame
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (m : CircleHs g (n : ℝ) →L[ℝ] CircleHsPi g ι (n : ℝ) →L[ℝ] CircleHsPi g ι (n : ℝ))
    (Q : CircleHsPi g ι ((n : ℝ) + 2) →L[ℝ] CircleHsPi g ι (n : ℝ))
    (D : CircleHsPi g ι ((n : ℝ) + 1) →L[ℝ] CircleHsPi g ι (n : ℝ))
    (c : CircleHsPi g ι (n : ℝ)) (d : CircleHsPi g ι (n : ℝ) →L[ℝ] CircleHsPi g ι (n : ℝ))
    (q : CircleHs g (n : ℝ))
    (alpha : ℝ → CircleHsPi g ι ((n : ℝ) + 1) → CircleHs g (n : ℝ))
    (reaction : ℝ → CircleHsPi g ι ((n : ℝ) + 1) → CircleHsPi g ι (n : ℝ))
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (K L M A₀ B₀ : ℝ≥0)
    (halip : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖alpha t z - alpha t w‖ ≤ (L : ℝ) * ‖z - w‖)
    (haclose : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R →
      ‖alpha t z - q‖ ≤ (K : ℝ) * R)
    (hreaction : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖reaction t z - reaction t w‖ ≤ (M : ℝ) * ‖z - w‖)
    (halpha_zero : ∀ t ∈ Icc (0 : ℝ) τ, ‖alpha t 0‖ ≤ A₀)
    (hreaction_zero : ∀ t ∈ Icc (0 : ℝ) τ, ‖reaction t 0‖ ≤ B₀)
    (hmeas : TimeNemyMeas
      (show (0 : CircleHsPi g ι ((n : ℝ) + 2)) ∈
          {u | ‖circleHsPiInclusion g ι (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith) u‖ ≤ R} by
        simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le)
      (shiftedRemainder m Q (circleHsPiInclusion g ι (by linarith)) D c d q alpha reaction R) τ)
    (hsmallA : (‖m‖ * K * ‖Q‖) * R ≤ 1 / 16)
    (hsmallC : (‖m‖ * L * ‖Q‖) * R ≤ 1 / 16) :
    let J := circleHsPiInclusion g ι (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)
    let N := shiftedRemainder m Q J D c d q alpha reaction R
    let B : ℝ := ‖m‖ * (L : ℝ) * ‖c‖ + (M : ℝ) + ‖d‖ * ‖D‖
    let D₀ : ℝ := ‖m‖ * (A₀ : ℝ) * ‖c‖ + (B₀ : ℝ)
    ∃ T₀ : ℝ,
      T₀ = min τ (min 1 (min (1 / (64 * (B + 1) ^ 2))
        (((R / 4) / (2 * (D₀ + 1))) ^ 2))) ∧
      0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
      ∃ (u : timeH1 (CircleHsPi g ι (n : ℝ)) T) (gforce : timeL2 (CircleHsPi g ι (n : ℝ)) T),
        let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
          (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := (n : ℝ)) hT 0 gforce
        u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := (n : ℝ)) hT 0 gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖J v‖ ≤ R}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N t (aeSetLift
            (show (0 : CircleHsPi g ι ((n : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ R} by
              simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le) field t)) ∧
          u.toFunL2 = (circleHsPiInclusion g ι (show (n : ℝ) ≤ (n : ℝ) + 2 by linarith)).compLpL
            2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
                (g := g) (r := 0) (s := 0) (n : ℝ))).compLpL 2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ R / 4 := by
  let J := circleHsPiInclusion g ι (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)
  let N := shiftedRemainder m Q J D c d q alpha reaction R
  let Aconst : ℝ≥0 := ‖m‖₊ * K * ‖Q‖₊
  let Bconst : ℝ≥0 := ‖m‖₊ * L * ‖c‖₊ + M + ‖d‖₊ * ‖D‖₊
  let Cconst : ℝ≥0 := ‖m‖₊ * L * ‖Q‖₊
  let Dconst : ℝ := ‖m‖ * A₀ * ‖c‖ + B₀
  have hD : 0 ≤ Dconst := by dsimp only [Dconst]; positivity
  have hzero : ∀ t ∈ Icc (0 : ℝ) τ,
      ‖N t ⟨0, by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le⟩‖ ≤ Dconst := by
    intro t ht
    have hz : ‖J (0 : CircleHsPi g ι ((n : ℝ) + 2))‖ ≤ R := by
      simpa only [map_zero, norm_zero] using hR.le
    have hb := (shifted_tame_estimate m Q J D c d q alpha reaction t
      (halip t ht) (haclose t ht) (hreaction t ht) hz hz).2
    exact hb.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (halpha_zero t ht) (norm_nonneg m)) (norm_nonneg c)) (hreaction_zero t ht))
  have htame : ∀ t ∈ Icc (0 : ℝ) τ, ∀ u v,
      ‖N t u - N t v‖ ≤ (Aconst : ℝ) * R * ‖u.val - v.val‖ +
        (Bconst : ℝ) * ‖J (u.val - v.val)‖ +
        (Cconst : ℝ) * (‖u.val‖ + ‖v.val‖) * ‖J (u.val - v.val)‖ := by
    intro t ht u v
    exact (shifted_tame_estimate m Q J D c d q alpha reaction t
      (halip t ht) (haclose t ht) (hreaction t ht) u.property v.property).1
  exact time_partial_tame_vector (ι := ι) g 0 0 (n : ℝ) hR hτ N hmeas
    Aconst Bconst Cconst Dconst hD hzero hsmallA hsmallC htame

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {ι : Type*} [Fintype ι]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem circle_shifted_solution_of_continuous_coefficients
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (m : CircleHs g (n : ℝ) →L[ℝ] CircleHsPi g ι (n : ℝ) →L[ℝ] CircleHsPi g ι (n : ℝ))
    (Q : CircleHsPi g ι ((n : ℝ) + 2) →L[ℝ] CircleHsPi g ι (n : ℝ))
    (D : CircleHsPi g ι ((n : ℝ) + 1) →L[ℝ] CircleHsPi g ι (n : ℝ))
    (c : CircleHsPi g ι (n : ℝ)) (d : CircleHsPi g ι (n : ℝ) →L[ℝ] CircleHsPi g ι (n : ℝ))
    (q : CircleHs g (n : ℝ))
    (alpha : ℝ → CircleHsPi g ι ((n : ℝ) + 1) → CircleHs g (n : ℝ))
    (reaction : ℝ → CircleHsPi g ι ((n : ℝ) + 1) → CircleHsPi g ι (n : ℝ))
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (K L M A₀ B₀ : ℝ≥0)
    (halip : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖alpha t z - alpha t w‖ ≤ (L : ℝ) * ‖z - w‖)
    (haclose : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R →
      ‖alpha t z - q‖ ≤ (K : ℝ) * R)
    (hreaction : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖reaction t z - reaction t w‖ ≤ (M : ℝ) * ‖z - w‖)
    (halpha_zero : ∀ t ∈ Icc (0 : ℝ) τ, ‖alpha t 0‖ ≤ A₀)
    (hreaction_zero : ∀ t ∈ Icc (0 : ℝ) τ, ‖reaction t 0‖ ≤ B₀)
    (halpha_cont : Continuous (fun p : Icc (0 : ℝ) τ ×
      Metric.closedBall (0 : CircleHsPi g ι ((n : ℝ) + 1)) R => alpha p.1 p.2))
    (hreaction_cont : Continuous (fun p : Icc (0 : ℝ) τ ×
      Metric.closedBall (0 : CircleHsPi g ι ((n : ℝ) + 1)) R => reaction p.1 p.2))
    (hsmallA : (‖m‖ * K * ‖Q‖) * R ≤ 1 / 16)
    (hsmallC : (‖m‖ * L * ‖Q‖) * R ≤ 1 / 16) :
    let J := circleHsPiInclusion g ι (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)
    let N := shiftedRemainder m Q J D c d q alpha reaction R
    ∃ (T : ℝ) (hT : 0 < T), T ≤ τ ∧
      ∃ (u : timeH1 (CircleHsPi g ι (n : ℝ)) T) (gforce : timeL2 (CircleHsPi g ι (n : ℝ)) T),
        let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
          (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := (n : ℝ)) hT 0 gforce
        u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := (n : ℝ)) hT 0 gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖J v‖ ≤ R}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N t (aeSetLift
            (show (0 : CircleHsPi g ι ((n : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ R} by
              simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le) field t)) ∧
          u.toFunL2 = (circleHsPiInclusion g ι (show (n : ℝ) ≤ (n : ℝ) + 2 by linarith)).compLpL
            2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
                (g := g) (r := 0) (s := 0) (n : ℝ))).compLpL 2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ R / 4 := by
  intro J N
  have hz : (0 : CircleHsPi g ι ((n : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ R} := by
    simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le
  have hmeas : TimeNemyMeas hz N τ :=
    (shifted_time_nemy_meas m Q J D c d q alpha reaction hz
      (fun u => u.property) halpha_cont hreaction_cont).2
  obtain ⟨T₀, hT₀eq, hT₀pos, hex⟩ := circle_shifted_time_partial_tame g n m Q D
    c d q alpha reaction hR hτ K L M A₀ B₀ halip haclose hreaction
    halpha_zero hreaction_zero hmeas hsmallA hsmallC
  have hTτ : T₀ ≤ τ := hT₀eq ▸ min_le_left _ _
  exact ⟨T₀, hT₀pos, hTτ, hex hT₀pos le_rfl⟩


private theorem circle_shifted_solution_of_coefficient_bounds
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (hn : Module.finrank ℝ ℝ / 2 + 1 ≤ n)
    (f₀ : CircleHsPi g ι ((n : ℝ) + 2))
    (alpha : ℝ → CircleHsPi g ι ((n : ℝ) + 1) → CircleHs g (n : ℝ))
    (reaction : ℝ → CircleHsPi g ι ((n : ℝ) + 1) → CircleHsPi g ι (n : ℝ))
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (K L M A₀ B₀ : ℝ≥0)
    (halip : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖alpha t z - alpha t w‖ ≤ (L : ℝ) * ‖z - w‖)
    (haclose : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R →
      ‖alpha t z - ccTensorToHs g 0 (n : ℝ)
        (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))‖ ≤ (K : ℝ) * R)
    (hreaction : ∀ t ∈ Icc (0 : ℝ) τ, ∀ z, ‖z‖ ≤ R → ∀ w, ‖w‖ ≤ R →
      ‖reaction t z - reaction t w‖ ≤ (M : ℝ) * ‖z - w‖)
    (halpha_zero : ∀ t ∈ Icc (0 : ℝ) τ, ‖alpha t 0‖ ≤ A₀)
    (hreaction_zero : ∀ t ∈ Icc (0 : ℝ) τ, ‖reaction t 0‖ ≤ B₀)
    (halpha_cont : Continuous (fun p : Icc (0 : ℝ) τ ×
      Metric.closedBall (0 : CircleHsPi g ι ((n : ℝ) + 1)) R => alpha p.1 p.2))
    (hreaction_cont : Continuous (fun p : Icc (0 : ℝ) τ ×
      Metric.closedBall (0 : CircleHsPi g ι ((n : ℝ) + 1)) R => reaction p.1 p.2)) :
    let m := coordinateMultiplication (ι := ι) (scalarHsMul g n hn)
    let q := ccTensorToHs g 0 (n : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 n (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g n
    let D := AddCircle.parameterDerivativeHsPi (ι := ι) g n
    let J := circleHsPiInclusion g ι (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)
    let N := shiftedRemainder m Q J D (Q f₀) d q alpha reaction R
    (‖m‖ * K * ‖Q‖) * R ≤ 1 / 16 →
    (‖m‖ * L * ‖Q‖) * R ≤ 1 / 16 →
    ∃ (T : ℝ) (hT : 0 < T), T ≤ τ ∧
      ∃ (u : timeH1 (CircleHsPi g ι (n : ℝ)) T) (gforce : timeL2 (CircleHsPi g ι (n : ℝ)) T),
        let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
          (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := (n : ℝ)) hT 0 gforce
        u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := (n : ℝ)) hT 0 gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖J v‖ ≤ R}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N t (aeSetLift
            (show (0 : CircleHsPi g ι ((n : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ R} by
              simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le) field t)) ∧
          u.toFunL2 = (circleHsPiInclusion g ι (show (n : ℝ) ≤ (n : ℝ) + 2 by linarith)).compLpL
            2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
                (g := g) (r := 0) (s := 0) (n : ℝ))).compLpL 2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ R / 4 ∧
          (∀ᵐ t ∂(timeMeasure T),
            ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
              (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (n : ℝ))
                (field t) + gforce t =
              m (alpha t (J (field t))) (Q (f₀ + field t)) + reaction t (J (field t))) := by
  intro m q d Q D J N hsmallA hsmallC
  have hsel := circle_shifted_solution_of_continuous_coefficients
    g n m Q D (Q f₀) d q alpha reaction hR hτ K L M A₀ B₀
    halip haclose hreaction halpha_zero hreaction_zero halpha_cont hreaction_cont
    hsmallA hsmallC
  obtain ⟨T₀, hT₀pos, hTτ, u, F, hu, hstate, hforce, hcons, htrace, hpde, hnorm⟩ := hsel
  refine ⟨T₀, hT₀pos, hTτ, u, F, hu, hstate, hforce, hcons, htrace, hpde, hnorm, ?_⟩
  have hz : (0 : CircleHsPi g ι ((n : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ R} := by
    simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le
  let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
    (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := (n : ℝ)) hT₀pos 0 F
  have hlift := aeSetLift_coe_ae hz field hstate
  filter_upwards [hforce, hlift] with t ht htval
  change F t = N t (aeSetLift hz field t) at ht
  change (aeSetLift hz field t).val = field t at htval
  dsimp only [N, shiftedRemainder] at ht
  rw [htval] at ht
  rw [ht]
  exact shifted_circle_operator_identity g n hn f₀ (field t)
    (alpha t (J (field t))) (reaction t (J (field t)))

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
end
end


section
noncomputable section
open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic

private def extendClosedBall
    {X Y : Type*} [SeminormedAddCommGroup X] {R : ℝ} (hR : 0 ≤ R)
    (N : ℝ → Metric.closedBall (0 : X) R → Y) (t : ℝ) (x : X) : Y := by
  classical
  exact if hx : x ∈ Metric.closedBall (0 : X) R then N t ⟨x, hx⟩
    else N t ⟨0, Metric.mem_closedBall_self hR⟩

private theorem extendClosedBall_apply
    {X Y : Type*} [SeminormedAddCommGroup X] {R : ℝ} (hR : 0 ≤ R)
    (N : ℝ → Metric.closedBall (0 : X) R → Y) (t : ℝ) (x : X)
    (hx : x ∈ Metric.closedBall (0 : X) R) :
    extendClosedBall hR N t x = N t ⟨x, hx⟩ := by
  simp only [extendClosedBall, dif_pos hx]

private theorem extendClosedBall_bounds
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (N : ℝ → Metric.closedBall (0 : X) R → Y) (C : ℝ≥0)
    (hN : LipschitzWith C (fun p : ℝ × Metric.closedBall (0 : X) R => N p.1 p.2)) :
    (∀ t ∈ Set.Icc (0 : ℝ) r, ∀ z, ‖z‖ ≤ r → ∀ w, ‖w‖ ≤ r →
      ‖extendClosedBall hR N t z - extendClosedBall hR N t w‖ ≤ (C : ℝ) * ‖z - w‖) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) r, ∀ z, ‖z‖ ≤ r →
      ‖extendClosedBall hR N t z - N 0 ⟨0, Metric.mem_closedBall_self hR⟩‖ ≤ (C : ℝ) * r) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) r,
      ‖extendClosedBall hR N t 0‖ ≤ ‖N 0 ⟨0, Metric.mem_closedBall_self hR⟩‖ + (C : ℝ) * R) ∧
    Continuous (fun p : Set.Icc (0 : ℝ) r × Metric.closedBall (0 : X) r =>
      extendClosedBall hR N p.1 p.2) := by
  have hin (z : X) (hz : ‖z‖ ≤ r) : z ∈ Metric.closedBall (0 : X) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz.trans hrR
  have hdiff (t : ℝ) (z w : X) (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
      ‖extendClosedBall hR N t z - extendClosedBall hR N t w‖ ≤ (C : ℝ) * ‖z - w‖ := by
    rw [extendClosedBall_apply hR N t z (hin z hz), extendClosedBall_apply hR N t w (hin w hw)]
    simpa only [Prod.dist_eq, dist_self, Subtype.dist_eq, max_eq_right dist_nonneg, dist_eq_norm, max_eq_right (norm_nonneg (z-w))] using
      hN.dist_le_mul (t, ⟨z, hin z hz⟩) (t, ⟨w, hin w hw⟩)
  have hbase (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) r) (z : X) (hz : ‖z‖ ≤ r) :
      ‖extendClosedBall hR N t z - N 0 ⟨0, Metric.mem_closedBall_self hR⟩‖ ≤ (C : ℝ) * r := by
    rw [extendClosedBall_apply hR N t z (hin z hz)]
    have h := hN.dist_le_mul (t, ⟨z, hin z hz⟩) (0, ⟨0, Metric.mem_closedBall_self hR⟩)
    change dist (N t ⟨z, hin z hz⟩) (N 0 ⟨0, Metric.mem_closedBall_self hR⟩) ≤ (C : ℝ) * max (dist t 0) (dist z 0) at h
    rw [dist_eq_norm, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1, dist_zero_right] at h
    exact (show ‖N t ⟨z, hin z hz⟩ - N 0 ⟨0, Metric.mem_closedBall_self hR⟩‖ ≤ _ from h).trans
      (mul_le_mul_of_nonneg_left (max_le ht.2 hz) C.coe_nonneg)
  refine ⟨fun t _ z hz w hw => hdiff t z w hz hw, hbase, ?_, ?_⟩
  · intro t ht
    have hz := hbase t ht 0 (by simpa using hr)
    exact (norm_le_norm_sub_add _ _).trans
      (by linarith only [hz, mul_le_mul_of_nonneg_left hrR C.coe_nonneg])
  · let f : Set.Icc (0 : ℝ) r × Metric.closedBall (0 : X) r →
        ℝ × Metric.closedBall (0 : X) R := fun p =>
      (p.1, ⟨p.2, Metric.closedBall_subset_closedBall hrR p.2.2⟩)
    have hf : Continuous f := continuous_subtype_val.fst'.prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
    apply (hN.continuous.comp hf).congr
    intro p
    exact (extendClosedBall_apply hR N p.1 p.2 _).symm

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

private theorem exists_small_coefficient_radius
    {R : ℝ} (hR : 0 < R) (A C : ℝ≥0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ r ≤ 1 ∧ (A : ℝ) * r ≤ 1 / 16 ∧ (C : ℝ) * r ≤ 1 / 16 := by
  let r := min R (min 1 (1 / (16 * ((A : ℝ) + (C : ℝ) + 1))))
  have hden : 0 < 16 * ((A : ℝ) + (C : ℝ) + 1) := by positivity
  have hr : 0 < r := lt_min hR (lt_min zero_lt_one (one_div_pos.mpr hden))
  have hrR : r ≤ R := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrd : r ≤ 1 / (16 * ((A : ℝ) + (C : ℝ) + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hAr : (A : ℝ) * r ≤ 1 / 16 := by
    have h := (le_div_iff₀ hden).mp hrd
    nlinarith [mul_nonneg C.coe_nonneg hr.le]
  have hCr : (C : ℝ) * r ≤ 1 / 16 := by
    have h := (le_div_iff₀ hden).mp hrd
    nlinarith [mul_nonneg A.coe_nonneg hr.le]
  exact ⟨r, hr, hrR, hr1, hAr, hCr⟩

end DifferentialGeometry.Analysis.Parabolic

end
end


section
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem retractionMetric_inner_parameterTangent
    (c₀ : SmoothImmersion (I := I) (M := M)) (g : SmoothRiemannianMetric I M)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p)
    (z : AddCircle (1 : ℝ)) :
    (Geometry.Riemannian.retractionMetric g he hr).inner
      ⟨e (c₀.map z), hEU (Set.mem_range_self (c₀.map z))⟩
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (e ∘ c₀.map) z (AddCircle.parameterTangent z))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (e ∘ c₀.map) z (AddCircle.parameterTangent z)) =
        AddCircle.metricCoefficient (c₀.pullbackMetric g) z := by
  simpa only [AddCircle.metricCoefficient_apply, pullbackMetric,
    SmoothRiemannianMetric.pullback_inner] using
      Geometry.Riemannian.retractionMetric_inner_comp g he hr hEU hleft
        c₀.contMDiff_map z (AddCircle.parameterTangent z) (AddCircle.parameterTangent z)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion



noncomputable section
open scoped ContDiff NNReal Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private def firstJetCoordinates (n : ℕ) :
    (Option (Fin n ⊕ Fin n) → ℝ) → ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  fun z => (z none, WithLp.toLp 2 (fun i => z (some (Sum.inl i : Fin n ⊕ Fin n))),
    WithLp.toLp 2 (fun i => z (some (Sum.inr i : Fin n ⊕ Fin n))))

private theorem contDiff_firstJetCoordinates (n : ℕ) :
    ContDiff ℝ ∞ (firstJetCoordinates n) := by
  have hz : ContDiff ℝ ∞ (fun z : Option (Fin n ⊕ Fin n) → ℝ =>
      WithLp.toLp 2 (fun i => z (some (Sum.inl i : Fin n ⊕ Fin n)))) :=
    (contDiff_piLp 2).mpr (fun i => contDiff_apply ℝ _ (some (Sum.inl i : Fin n ⊕ Fin n)))
  have hp : ContDiff ℝ ∞ (fun z : Option (Fin n ⊕ Fin n) → ℝ =>
      WithLp.toLp 2 (fun i => z (some (Sum.inr i : Fin n ⊕ Fin n)))) :=
    (contDiff_piLp 2).mpr (fun i => contDiff_apply ℝ _ (some (Sum.inr i : Fin n ⊕ Fin n)))
  exact (contDiff_apply ℝ ℝ (none : Option (Fin n ⊕ Fin n))).prodMk (hz.prodMk hp)

private theorem isOpen_firstJetCoordinates_preimage
    {n : ℕ} {S : Set (ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    (hS : IsOpen S) : IsOpen (firstJetCoordinates n ⁻¹' S) :=
  hS.preimage (contDiff_firstJetCoordinates n).continuous

private theorem contDiffOn_firstJetCoordinates_comp
    {n : ℕ} {S : Set (ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))}
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {F : (ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → A}
    (hF : ContDiffOn ℝ ∞ F S) :
    ContDiffOn ℝ ∞ (F ∘ firstJetCoordinates n) (firstJetCoordinates n ⁻¹' S) :=
  hF.comp (contDiff_firstJetCoordinates n).contDiffOn (fun _ h => h)

private theorem geometric_coefficients_contDiffOn
    {n : ℕ} {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    {g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M}
    (hg : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn D g) (β : M) :
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D g β
    IsOpen S ∧
      ContDiffOn ℝ ∞ (curveShorteningChartDiffusionCoefficient g β ∘ firstJetCoordinates n) S ∧
      ContDiffOn ℝ ∞ (fun z => fun j => curveShorteningParametricChartReaction g β (firstJetCoordinates n z) j) S := by
  refine ⟨isOpen_firstJetCoordinates_preimage (isOpen_curveShorteningChartFirstJetDomain hg β),
    contDiffOn_firstJetCoordinates_comp (contDiffOn_curveShorteningChartDiffusionCoefficient hg β), ?_⟩
  apply contDiffOn_pi.mpr
  intro j
  exact (contDiff_piLp_apply (p := 2) (i := j)).contDiffOn.comp
    (contDiffOn_firstJetCoordinates_comp (contDiffOn_curveShorteningParametricChartReaction hg β))
    (fun _ _ => Set.mem_univ _)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening


noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem chart_diffusion_eq_inner_on_open
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : TopologicalSpace.Opens F}
    (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U) (β : U)
    (t : ℝ) (z : U) (v : F) :
    curveShorteningChartDiffusionCoefficient G β (t, (z : F), v) =
      ((G t).inner z v v)⁻¹ := by
  unfold curveShorteningChartDiffusionCoefficient
  rw [extChartAt_opens_symm_apply,
    Analysis.Parabolic.TensorSpectral.chartGramBilin_opens_model]

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem initial_diffusion_baseline
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p)
    (β : U) (z : AddCircle (1 : ℝ)) :
    curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
      (0, e (c₀.map z),
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (e ∘ c₀.map) z (AddCircle.parameterTangent z)) =
      (AddCircle.metricCoefficient (c₀.pullbackMetric (g 0)) z)⁻¹ := by
  have hchart := chart_diffusion_eq_inner_on_open
    (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β 0
    ⟨e (c₀.map z), hEU (Set.mem_range_self _)⟩
    (show F from mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (e ∘ c₀.map) z (AddCircle.parameterTangent z))
  exact hchart.trans (congrArg (fun a : ℝ => a⁻¹)
    (c₀.retractionMetric_inner_parameterTangent (g 0) he hr hEU hleft z))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening


noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private def circleDerivativeH1
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    TensorHs g 0 0 (1 + 1) →L[ℝ] TensorHs g 0 0 1 :=
  (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)).comp
    ((AddCircle.parameterDerivativeHs g 1).comp
      (tensorHsCongrL g 0 0 (by norm_num : (1 : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1)))

private def circleFirstJet
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι ⊕ ι => TensorHs g 0 0 1) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ⊕ ι => TensorHs g 0 0 1)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => match j with
      | .inl i =>
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ 1 + 1)).comp
              (PiLp.proj 2 (fun _ : ι => TensorHs g 0 0 (1 + 1)) i)
      | .inr i =>
          (circleDerivativeH1 g).comp
            (PiLp.proj 2 (fun _ : ι => TensorHs g 0 0 (1 + 1)) i))

private theorem scalarH1PiToContinuous_circleFirstJet
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 (1 + 1)))
    (x : AddCircle (1 : ℝ)) :
    scalarH1PiToContinuous g (circleFirstJet g u) x = Sum.elim
      (fun i => scalarH1ToContinuous g (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ 1 + 1) (u i)) x)
      (fun i => scalarH1ToContinuous g (circleDerivativeH1 g (u i)) x) := by
  funext j
  cases j <;> rfl

end DifferentialGeometry.Analysis.Parabolic

end

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private def ambientCoordinate (c₀ : SmoothImmersion (I := I) (M := M))
    (e : M → EuclideanSpace ℝ (Fin n)) (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (i : Fin n) : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯ :=
  ⟨fun z => e (c₀.map z) i, by
    exact ((PiLp.proj 2 (fun _ : Fin n => ℝ) i).contDiff.contMDiff).comp
      (he.comp c₀.contMDiff_map)⟩

private def ambientCoordinateCc (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e) (i : Fin n) :
    SmoothCcTensor (c₀.pullbackMetric g) 0 0 :=
  scalarCc (c₀.pullbackMetric g) (ambientCoordinate c₀ e he i)

private theorem scalar0_ambientCoordinateCc (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e) (i : Fin n) :
    TensorRSField.scalar0 (ambientCoordinateCc c₀ g e he i).toSection =
      fun z => e (c₀.map z) i := by
  rw [ambientCoordinateCc, scalar0_scalarCc]
  rfl

private def ambientSobolev (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e) (s : ℝ) :
    PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric g) 0 0 s) :=
  WithLp.toLp 2 (fun i => ccTensorToHs (c₀.pullbackMetric g) 0 s
    (ambientCoordinateCc c₀ g e he i))

private theorem scalarH1ToContinuous_ambientSobolev (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e) {s : ℝ} (hs : 1 ≤ s)
    (z : AddCircle (1 : ℝ)) (i : Fin n) :
    scalarH1ToContinuous (c₀.pullbackMetric g)
      (tensorHsInclusion (g := c₀.pullbackMetric g) (r := 0) (s := 0)
        hs (ambientSobolev c₀ g e he s i)) z = e (c₀.map z) i := by
  change scalarH1ToContinuous (c₀.pullbackMetric g)
    (tensorHsInclusion _ (ccTensorToHs (c₀.pullbackMetric g) 0 s
      (ambientCoordinateCc c₀ g e he i))) z = _
  rw [tensorHsInclusion_ccTensorToHs, scalarH1ToContinuous_apply_ccTensorToHs,
    scalar0_ambientCoordinateCc]

private theorem scalarH1PiToContinuous_ambientSobolev (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e) {s : ℝ} (hs : 1 ≤ s)
    (z : AddCircle (1 : ℝ)) :
    scalarH1PiToContinuous (c₀.pullbackMetric g)
      ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := c₀.pullbackMetric g) (r := 0) (s := 0)
          hs)) (ambientSobolev c₀ g e he s)) z = fun i => e (c₀.map z) i := by
  funext i
  exact scalarH1ToContinuous_ambientSobolev c₀ g e he hs z i

private theorem scalarH1ToContinuous_parameterDerivative_ambientSobolev (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (x : ℝ) (i : Fin n) :
    scalarH1ToContinuous (c₀.pullbackMetric g)
      (tensorHsInclusion (g := c₀.pullbackMetric g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
        (AddCircle.parameterDerivativeHsPi (c₀.pullbackMetric g) 2
          ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
            tensorHsInclusion (g := c₀.pullbackMetric g) (r := 0) (s := 0)
              (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ (3 : ℝ))))
            (ambientSobolev c₀ g e he 3)) i)) (x : AddCircle (1 : ℝ)) =
      deriv (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ))) i) x := by
  change scalarH1ToContinuous (c₀.pullbackMetric g)
    (tensorHsInclusion _ (AddCircle.parameterDerivativeHs (c₀.pullbackMetric g) 2
      (tensorHsInclusion (by norm_num) (ccTensorToHs (c₀.pullbackMetric g) 0 3
        (ambientCoordinateCc c₀ g e he i))))) (x : AddCircle (1 : ℝ)) = _
  rw [tensorHsInclusion_ccTensorToHs, AddCircle.parameterDerivativeHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs, scalarH1ToContinuous_apply_ccTensorToHs,
    AddCircle.scalar0_parameterDerivativeCcTensor_coe, scalar0_ambientCoordinateCc]

private theorem scalarH1ToContinuous_parameterSecondDerivative_ambientSobolev (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (x : ℝ) (i : Fin n) :
    scalarH1ToContinuous (c₀.pullbackMetric g)
      (tensorHsInclusion (g := c₀.pullbackMetric g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
        (AddCircle.parameterSecondDerivativeHsPi (c₀.pullbackMetric g) 1
          ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
            tensorHsInclusion (g := c₀.pullbackMetric g) (r := 0) (s := 0)
              (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ (3 : ℝ))))
            (ambientSobolev c₀ g e he 3)) i)) (x : AddCircle (1 : ℝ)) =
      deriv (deriv (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ))) i)) x := by
  change scalarH1ToContinuous (c₀.pullbackMetric g)
    (tensorHsInclusion _ (AddCircle.parameterSecondDerivativeHs (c₀.pullbackMetric g) 1
      (tensorHsInclusion (by norm_num) (ccTensorToHs (c₀.pullbackMetric g) 0 3
        (ambientCoordinateCc c₀ g e he i))))) (x : AddCircle (1 : ℝ)) = _
  rw [tensorHsInclusion_ccTensorToHs,
    AddCircle.parameterSecondDerivativeHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs, scalarH1ToContinuous_apply_ccTensorToHs,
    AddCircle.scalar0_parameterDerivativeCcTensor_twice_coe, scalar0_ambientCoordinateCc]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem tensorHsCongrL_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {a b : ℝ}
    (h : a = b) (S : SmoothCcTensor g 0 0) :
    tensorHsCongrL g 0 0 h (ccTensorToHs g 0 a S) = ccTensorToHs g 0 b S := by
  cases h
  rfl

private def ambientFirstJet (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e) :
    PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs (c₀.pullbackMetric g) 0 0 1) :=
  circleFirstJet (c₀.pullbackMetric g) (ambientSobolev c₀ g e he (1 + 1))

private theorem scalarH1PiToContinuous_ambientFirstJet_inl
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (z : AddCircle (1 : ℝ)) (i : Fin n) :
    scalarH1PiToContinuous (c₀.pullbackMetric g) (ambientFirstJet c₀ g e he) z (Sum.inl i) =
      e (c₀.map z) i := by
  rw [ambientFirstJet, scalarH1PiToContinuous_circleFirstJet]
  exact scalarH1ToContinuous_ambientSobolev c₀ g e he (by norm_num) z i

private theorem scalarH1PiToContinuous_ambientFirstJet_inr
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (x : ℝ) (i : Fin n) :
    scalarH1PiToContinuous (c₀.pullbackMetric g) (ambientFirstJet c₀ g e he)
      (x : AddCircle (1 : ℝ)) (Sum.inr i) =
      deriv (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ))) i) x := by
  rw [ambientFirstJet, scalarH1PiToContinuous_circleFirstJet]
  change scalarH1ToContinuous (c₀.pullbackMetric g)
    (circleDerivativeH1 (c₀.pullbackMetric g)
      (ccTensorToHs (c₀.pullbackMetric g) 0 (1 + 1)
        (ambientCoordinateCc c₀ g e he i))) (x : AddCircle (1 : ℝ)) = _
  simp only [circleDerivativeH1, ContinuousLinearMap.comp_apply,
    tensorHsCongrL_ccTensorToHs, AddCircle.parameterDerivativeHs_apply_ccTensorToHs,
    scalarH1ToContinuous_apply_ccTensorToHs, AddCircle.scalar0_parameterDerivativeCcTensor_coe,
    scalar0_ambientCoordinateCc]

private theorem scalarH1PiToContinuous_ambientFirstJet
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e) (x : ℝ) :
    scalarH1PiToContinuous (c₀.pullbackMetric g) (ambientFirstJet c₀ g e he)
      (x : AddCircle (1 : ℝ)) =
      Sum.elim (fun i => e (c₀.map (x : AddCircle (1 : ℝ))) i)
        (fun i => deriv (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ))) i) x) := by
  funext j
  cases j with
  | inl i => exact scalarH1PiToContinuous_ambientFirstJet_inl c₀ g e he _ i
  | inr i => exact scalarH1PiToContinuous_ambientFirstJet_inr c₀ g e he x i

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem firstJetCoordinates_ambientFirstJet
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e) (t0 x : ℝ) :
    firstJetCoordinates n
      (scalarH1PiToContinuous (c₀.pullbackMetric g)
        (scalarH1TimeCoordinate (c₀.pullbackMetric g) (t0, ambientFirstJet c₀ g e he))
          (x : AddCircle (1 : ℝ))) =
      (t0, e (c₀.map (x : AddCircle (1 : ℝ))),
        deriv (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ)))) x) := by
  apply Prod.ext
  · exact scalarH1TimeCoordinate_eval_none _ _ _
  apply Prod.ext
  · apply PiLp.ext
    intro i
    change scalarH1ToContinuous (c₀.pullbackMetric g)
      (ambientFirstJet c₀ g e he (Sum.inl i)) (x : AddCircle (1 : ℝ)) = _
    exact scalarH1PiToContinuous_ambientFirstJet_inl c₀ g e he _ i
  · apply PiLp.ext
    intro i
    change scalarH1ToContinuous (c₀.pullbackMetric g)
      (ambientFirstJet c₀ g e he (Sum.inr i)) (x : AddCircle (1 : ℝ)) = _
    rw [show scalarH1ToContinuous (c₀.pullbackMetric g)
      (ambientFirstJet c₀ g e he (Sum.inr i)) (x : AddCircle (1 : ℝ)) =
        deriv (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ))) i) x from
          scalarH1PiToContinuous_ambientFirstJet_inr c₀ g e he x i]
    have hd : DifferentiableAt ℝ (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ)))) x :=
      ((he.comp c₀.contMDiff_map).comp AddCircle.contMDiff_coe).contDiff.differentiable (by decide) x
    exact ((PiLp.proj 2 (fun _ : Fin n => ℝ) i).hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt).deriv

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem ambientFirstJet_range
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U) :
    Set.range (scalarH1PiToContinuous (c₀.pullbackMetric (g 0))
      (scalarH1TimeCoordinate (c₀.pullbackMetric (g 0))
        (0, ambientFirstJet c₀ (g 0) e he))) ⊆
      firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β := by
  rintro q ⟨z, rfl⟩
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  change firstJetCoordinates n _ ∈ curveShorteningChartFirstJetDomain D
    (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
  rw [firstJetCoordinates_ambientFirstJet]
  change 0 ∈ D.regular ∧
    e (c₀.map (x : AddCircle (1 : ℝ))) ∈ interior (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β).target ∧
    0 < Analysis.Parabolic.TensorSpectral.chartGramBilin
      (Geometry.Riemannian.retractionMetric (g 0) he hr) β
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β).symm (e (c₀.map (x : AddCircle (1 : ℝ)))))
      (deriv (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ)))) x)
      (deriv (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ)))) x)
  refine ⟨ht, mem_interior_extChartAt_opens_target U β
    ⟨e (c₀.map (x : AddCircle (1 : ℝ))), hEU (Set.mem_range_self _)⟩, ?_⟩
  have hd := AddCircle.deriv_comp_coe ((he.comp c₀.contMDiff_map).mdifferentiableAt (by decide)
    (x := (x : AddCircle (1 : ℝ))))
  change deriv (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ)))) x = _ at hd
  rw [extChartAt_opens_symm_apply U β
    ⟨e (c₀.map (x : AddCircle (1 : ℝ))), hEU (Set.mem_range_self _)⟩,
    Analysis.Parabolic.TensorSpectral.chartGramBilin_opens_model, hd]
  rw [c₀.retractionMetric_inner_parameterTangent (g 0) he hr hEU hleft]
  exact AddCircle.metricCoefficient_pos _ _

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem initial_diffusion_eval
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (z : AddCircle (1 : ℝ)) :
    curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
      (firstJetCoordinates n
        (scalarH1PiToContinuous (c₀.pullbackMetric (g 0))
          (scalarH1TimeCoordinate (c₀.pullbackMetric (g 0))
            (0, ambientFirstJet c₀ (g 0) e he)) z)) =
      AddCircle.laplacianPrincipalCoefficient (c₀.pullbackMetric (g 0)) z := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [firstJetCoordinates_ambientFirstJet]
  have hd := AddCircle.deriv_comp_coe ((he.comp c₀.contMDiff_map).mdifferentiableAt (by decide)
    (x := (x : AddCircle (1 : ℝ))))
  change deriv (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ)))) x = _ at hd
  rw [hd]
  exact initial_diffusion_baseline c₀ g he hr hEU hleft β _

private theorem initial_diffusion_H1
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (a : TensorHs (c₀.pullbackMetric (g 0)) 0 0 1)
    (ha : ∀ z, scalarH1ToContinuous (c₀.pullbackMetric (g 0)) a z =
      curveShorteningChartDiffusionCoefficient
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
        (firstJetCoordinates n
          (scalarH1PiToContinuous (c₀.pullbackMetric (g 0))
            (scalarH1TimeCoordinate (c₀.pullbackMetric (g 0))
              (0, ambientFirstJet c₀ (g 0) e he)) z))) :
    a = ccTensorToHs (c₀.pullbackMetric (g 0)) 0 1
      (scalarCc (c₀.pullbackMetric (g 0))
        (AddCircle.laplacianPrincipalCoefficient (c₀.pullbackMetric (g 0)))) := by
  apply scalarH1ToContinuous_injective (c₀.pullbackMetric (g 0))
  apply ContinuousMap.ext
  intro z
  rw [ha, initial_diffusion_eval c₀ g he hr hEU hleft β z,
    scalarH1ToContinuous_apply_ccTensorToHs, scalar0_scalarCc]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end
end
end
end

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal NNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩
variable {ι : Type*} [Fintype ι]

private theorem circle_shifted_solution_with_radius_le_of_lipschitz_coefficients
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (hn : Module.finrank ℝ ℝ / 2 + 1 ≤ n)
    (f₀ : CircleHsPi g ι ((n : ℝ) + 2))
    {R : ℝ} (hR : 0 < R) {ρ : ℝ} (hρ : 0 < ρ)
    (alpha₀ : ℝ → Metric.closedBall (0 : CircleHsPi g ι ((n : ℝ) + 1)) R → CircleHs g (n : ℝ))
    (reaction₀ : ℝ → Metric.closedBall (0 : CircleHsPi g ι ((n : ℝ) + 1)) R → CircleHsPi g ι (n : ℝ))
    (Cα CB : ℝ≥0)
    (hα : LipschitzWith Cα (fun p : ℝ × Metric.closedBall
      (0 : CircleHsPi g ι ((n : ℝ) + 1)) R => alpha₀ p.1 p.2))
    (hB : LipschitzWith CB (fun p : ℝ × Metric.closedBall
      (0 : CircleHsPi g ι ((n : ℝ) + 1)) R => reaction₀ p.1 p.2))
    (hzero : alpha₀ 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g 0 (n : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))) :
    let alpha := extendClosedBall hR.le alpha₀
    let reaction := extendClosedBall hR.le reaction₀
    let m := coordinateMultiplication (ι := ι) (scalarHsMul g n hn)
    let q := ccTensorToHs g 0 (n : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 n (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g n
    let D := AddCircle.parameterDerivativeHsPi (ι := ι) g n
    let J := circleHsPiInclusion g ι (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)
    ∃ r : ℝ, ∃ hr : 0 < r, r ≤ R ∧ r ≤ 1 ∧ r ≤ ρ ∧
    ∃ (T : ℝ) (hT : 0 < T), T ≤ r ∧
      let N := shiftedRemainder m Q J D (Q f₀) d q alpha reaction r
      ∃ (u : timeH1 (CircleHsPi g ι (n : ℝ)) T) (gforce : timeL2 (CircleHsPi g ι (n : ℝ)) T),
        let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
          (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := (n : ℝ)) hT 0 gforce
        u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := (n : ℝ)) hT 0 gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖J v‖ ≤ r}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N t (aeSetLift
            (show (0 : CircleHsPi g ι ((n : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ r} by
              simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hr.le) field t)) ∧
          u.toFunL2 = (circleHsPiInclusion g ι (show (n : ℝ) ≤ (n : ℝ) + 2 by linarith)).compLpL
            2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
                (g := g) (r := 0) (s := 0) (n : ℝ))).compLpL 2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ r / 4 ∧
          (∀ᵐ t ∂(timeMeasure T),
            ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
              (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (n : ℝ))
                (field t) + gforce t =
              m (alpha t (J (field t))) (Q (f₀ + field t)) + reaction t (J (field t))) := by
  intro alpha reaction m q d Q D J
  let A : ℝ≥0 := ‖m‖₊ * Cα * ‖Q‖₊
  obtain ⟨r, hr, hrmin, hr1, hsmall, _⟩ :=
    exists_small_coefficient_radius (lt_min hR hρ) A A
  have hrR : r ≤ R := hrmin.trans (min_le_left _ _)
  have hrρ : r ≤ ρ := hrmin.trans (min_le_right _ _)
  obtain ⟨halip, haclose, hazero, hacont⟩ :=
    extendClosedBall_bounds hR.le hr.le hrR alpha₀ Cα hα
  obtain ⟨hblip, _, hbzero, hbcont⟩ :=
    extendClosedBall_bounds hR.le hr.le hrR reaction₀ CB hB
  let A₀ : ℝ≥0 := ‖alpha₀ 0 ⟨0, Metric.mem_closedBall_self hR.le⟩‖₊ + Cα * ⟨R, hR.le⟩
  let B₀ : ℝ≥0 := ‖reaction₀ 0 ⟨0, Metric.mem_closedBall_self hR.le⟩‖₊ + CB * ⟨R, hR.le⟩
  have haclose' : ∀ t ∈ Icc (0 : ℝ) r, ∀ z, ‖z‖ ≤ r →
      ‖alpha t z - q‖ ≤ (Cα : ℝ) * r := by
    simpa only [hzero] using haclose
  have hs : (‖m‖ * Cα * ‖Q‖) * r ≤ 1 / 16 := hsmall
  refine ⟨r, hr, hrR, hr1, hrρ, ?_⟩
  exact circle_shifted_solution_of_coefficient_bounds g n hn f₀ alpha reaction hr hr
    Cα Cα CB A₀ B₀ halip haclose' hblip hazero hbzero hacont hbcont hs hs

private theorem circle_shifted_solution_of_lipschitz_coefficients
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (hn : Module.finrank ℝ ℝ / 2 + 1 ≤ n)
    (f₀ : CircleHsPi g ι ((n : ℝ) + 2))
    {R : ℝ} (hR : 0 < R)
    (alpha₀ : ℝ → Metric.closedBall (0 : CircleHsPi g ι ((n : ℝ) + 1)) R → CircleHs g (n : ℝ))
    (reaction₀ : ℝ → Metric.closedBall (0 : CircleHsPi g ι ((n : ℝ) + 1)) R → CircleHsPi g ι (n : ℝ))
    (Cα CB : ℝ≥0)
    (hα : LipschitzWith Cα (fun p : ℝ × Metric.closedBall
      (0 : CircleHsPi g ι ((n : ℝ) + 1)) R => alpha₀ p.1 p.2))
    (hB : LipschitzWith CB (fun p : ℝ × Metric.closedBall
      (0 : CircleHsPi g ι ((n : ℝ) + 1)) R => reaction₀ p.1 p.2))
    (hzero : alpha₀ 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g 0 (n : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))) :
    let alpha := extendClosedBall hR.le alpha₀
    let reaction := extendClosedBall hR.le reaction₀
    let m := coordinateMultiplication (ι := ι) (scalarHsMul g n hn)
    let q := ccTensorToHs g 0 (n : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      appHs g 0 0 n (scalarCc g (AddCircle.laplacianDriftCoefficient g)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := ι) g n
    let D := AddCircle.parameterDerivativeHsPi (ι := ι) g n
    let J := circleHsPiInclusion g ι (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)
    ∃ r : ℝ, ∃ hr : 0 < r, r ≤ R ∧ r ≤ 1 ∧
    ∃ (T : ℝ) (hT : 0 < T), T ≤ r ∧
      let N := shiftedRemainder m Q J D (Q f₀) d q alpha reaction r
      ∃ (u : timeH1 (CircleHsPi g ι (n : ℝ)) T) (gforce : timeL2 (CircleHsPi g ι (n : ℝ)) T),
        let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
          (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := (n : ℝ)) hT 0 gforce
        u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := (n : ℝ)) hT 0 gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖J v‖ ≤ r}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N t (aeSetLift
            (show (0 : CircleHsPi g ι ((n : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ r} by
              simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hr.le) field t)) ∧
          u.toFunL2 = (circleHsPiInclusion g ι (show (n : ℝ) ≤ (n : ℝ) + 2 by linarith)).compLpL
            2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
                (g := g) (r := 0) (s := 0) (n : ℝ))).compLpL 2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ r / 4 ∧
          (∀ᵐ t ∂(timeMeasure T),
            ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
              (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (n : ℝ))
                (field t) + gforce t =
              m (alpha t (J (field t))) (Q (f₀ + field t)) + reaction t (J (field t))) := by
  intro alpha reaction m q d Q D J
  obtain ⟨r, hr, hrR, hr1, _, hsol⟩ :=
    circle_shifted_solution_with_radius_le_of_lipschitz_coefficients
      g n hn f₀ hR hR alpha₀ reaction₀ Cα CB hα hB hzero
  exact ⟨r, hr, hrR, hr1, hsol⟩

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private def ambientCoefficientRadius
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :=
  let smooth := geometric_coefficients_contDiffOn hG β
  Classical.indefiniteDescription _ <|
  exists_scalar_vectorH1_time_composition_on_closedBall (c₀.pullbackMetric (g 0)) n
    (curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n)
    (fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j)
    smooth.2.1 smooth.2.2 smooth.1 0 (ambientFirstJet c₀ (g 0) e he)
    (ambientFirstJet_range c₀ g ht he hr hEU hleft β)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

section
noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private def circleHsPiCongr
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (ι : Type*) [Fintype ι] {a b : ℝ} (h : a = b) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 a) ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 b) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => tensorHsCongr g 0 0 h)

private theorem circleHsPiCongr_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (ι : Type*) [Fintype ι] {a b : ℝ} (h : a = b)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) (i : ι) :
    circleHsPiCongr g ι h u i = tensorHsCongrL g 0 0 h (u i) := rfl

private theorem circleHsPiCongr_toContinuousLinearMap
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (ι : Type*) [Fintype ι] {a b : ℝ} (h : a = b) :
    (circleHsPiCongr g ι h).toLinearIsometry.toContinuousLinearMap =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsCongrL g 0 0 h) := by
  ext u i
  rfl

private theorem circleHsPiCongr_norm
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (ι : Type*) [Fintype ι] {a b : ℝ} (h : a = b)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 a)) :
    ‖circleHsPiCongr g ι h u‖ = ‖u‖ :=
  (circleHsPiCongr g ι h).norm_map u

private theorem circleHsPiCongr_inclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (ι : Type*) [Fintype ι] {a b c d : ℝ}
    (hac : a = c) (hbd : b = d) (hab : a ≤ b) (hcd : c ≤ d)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 b)) :
    circleHsPiCongr g ι hac
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0) hab)) u) =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0) hcd)
          (circleHsPiCongr g ι hbd u) := by
  apply PiLp.ext
  intro i
  exact tensorHsCongr_incl hac hbd hab hcd (u i)


end DifferentialGeometry.Analysis.Parabolic
end
end

noncomputable section
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private def ambientCoefficientMaps
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :=
  let radius := ambientCoefficientRadius c₀ g ht he hr hEU hleft β hG
  let ca := Classical.indefiniteDescription _ radius.property.2
  let cb := Classical.indefiniteDescription _ ca.property
  let alpha := Classical.indefiniteDescription _ cb.property
  Classical.indefiniteDescription _ alpha.property

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
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
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

open _root_.MeasureTheory Set Filter
open scoped ENNReal
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

@[irreducible] private def PrecomposedCircleSolution
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    {R : ℝ} (hR : 0 < R)
    (a : ℝ → Metric.closedBall (0 : V) R → TensorHs g₀ 0 0 1)
    (b : ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1))
 : Type :=
  let outer := Classical.indefiniteDescription _ (J.exists_pos_norm_mul_le hR)
  have houter : 0 < outer.val := outer.property.1
  let A : ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val →
      CircleHs g₀ ((1 : ℕ) : ℝ) := fun t u =>
    tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (a t (J.closedBallMap outer.property.2.2 u))
  let B : ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val →
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := fun t u =>
    circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (b t (J.closedBallMap outer.property.2.2 u))
    let alpha := extendClosedBall houter.le A
    let reaction := extendClosedBall houter.le B
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ) (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) =>
      appHs g₀ 0 0 (1 : ℕ) (scalarCc g₀ (AddCircle.laplacianDriftCoefficient g₀)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let D := AddCircle.parameterDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let J := circleHsPiInclusion g₀ (Fin n) (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    {r : ℝ // ∃ hr : 0 < r, r ≤ outer.val ∧ r ≤ 1 ∧
    ∃ (T : ℝ) (hT : 0 < T), T ≤ r ∧
      let N := shiftedRemainder m Q J D (Q f₀) d q alpha reaction r
      ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
        let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
          (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce
        u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖J v‖ ≤ r}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N t (aeSetLift
            (show (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ r} by
              simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hr.le) field t)) ∧
          u.toFunL2 = (circleHsPiInclusion g₀ (Fin n) (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)).compLpL
            2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) =>
              tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
                (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))).compLpL 2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ r / 4 ∧
          (∀ᵐ t ∂(timeMeasure T),
            ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) => tensorScaleLaplacian
              (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
                (field t) + gforce t =
              m (alpha t (J (field t))) (Q (f₀ + field t)) + reaction t (J (field t))) }

private theorem precomposed_circle_solution_with_radius_le
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    {R : ℝ} (hR : 0 < R) {ρcap : ℝ} (hρcap : 0 < ρcap)
    (a : ℝ → Metric.closedBall (0 : V) R → TensorHs g₀ 0 0 1)
    (b : ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1))
    (Ca Cb : ℝ≥0)
    (ha : LipschitzWith Ca (fun p : ℝ × Metric.closedBall (0 : V) R => a p.1 p.2))
    (hb : LipschitzWith Cb (fun p : ℝ × Metric.closedBall (0 : V) R => b p.1 p.2))
    (ha0 : a 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))) :
  let outer := Classical.indefiniteDescription _ (J.exists_pos_norm_mul_le hR)
  have houter : 0 < outer.val := outer.property.1
  let A : ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val →
      CircleHs g₀ ((1 : ℕ) : ℝ) := fun t u =>
    tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (a t (J.closedBallMap outer.property.2.2 u))
  let B : ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val →
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := fun t u =>
    circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (b t (J.closedBallMap outer.property.2.2 u))
    let alpha := extendClosedBall houter.le A
    let reaction := extendClosedBall houter.le B
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ) (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) =>
      appHs g₀ 0 0 (1 : ℕ) (scalarCc g₀ (AddCircle.laplacianDriftCoefficient g₀)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let D := AddCircle.parameterDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let J := circleHsPiInclusion g₀ (Fin n) (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ r : ℝ, ∃ hr : 0 < r, r ≤ outer.val ∧ r ≤ 1 ∧ r ≤ ρcap ∧
    ∃ (T : ℝ) (hT : 0 < T), T ≤ r ∧
      let N := shiftedRemainder m Q J D (Q f₀) d q alpha reaction r
      ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
        let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
          (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce
        u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖J v‖ ≤ r}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N t (aeSetLift
            (show (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ r} by
              simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hr.le) field t)) ∧
          u.toFunL2 = (circleHsPiInclusion g₀ (Fin n) (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)).compLpL
            2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) =>
              tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
                (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))).compLpL 2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ r / 4 ∧
          (∀ᵐ t ∂(timeMeasure T),
            ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) => tensorScaleLaplacian
              (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
                (field t) + gforce t =
              m (alpha t (J (field t))) (Q (f₀ + field t)) + reaction t (J (field t))) :=
  let outer := Classical.indefiniteDescription _ (J.exists_pos_norm_mul_le hR)
  have houter : 0 < outer.val := outer.property.1
  let A : ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val →
      CircleHs g₀ ((1 : ℕ) : ℝ) := fun t u =>
    tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (a t (J.closedBallMap outer.property.2.2 u))
  let B : ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val →
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := fun t u =>
    circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (b t (J.closedBallMap outer.property.2.2 u))
  have hA : LipschitzWith (Ca * (1 + ‖J‖₊))
      (fun p : ℝ × Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val => A p.1 p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change dist (tensorHsCongrL g₀ 0 0 _ _) (tensorHsCongrL g₀ 0 0 _ _) ≤ _
    rw [dist_eq_norm, ← map_sub, tensorHsCongrL_apply, norm_tensorHsCongr]
    simpa only [dist_eq_norm] using (ha.prod_precomp_closedBall J outer.property.2.2).dist_le_mul p q
  have hB : LipschitzWith (Cb * (1 + ‖J‖₊))
      (fun p : ℝ × Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val => B p.1 p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change dist (circleHsPiCongr g₀ (Fin n) _ _) (circleHsPiCongr g₀ (Fin n) _ _) ≤ _
    rw [dist_eq_norm, ← map_sub, circleHsPiCongr_norm]
    simpa only [dist_eq_norm] using (hb.prod_precomp_closedBall J outer.property.2.2).dist_le_mul p q
  have hA0 : A 0 ⟨0, Metric.mem_closedBall_self houter.le⟩ =
      ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ) (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀)) := by
    change tensorHsCongrL g₀ 0 0 _ (a 0 _) = _
    have hz : J.closedBallMap outer.property.2.2 ⟨0, Metric.mem_closedBall_self houter.le⟩ =
        ⟨0, Metric.mem_closedBall_self hR.le⟩ := by
      apply Subtype.ext
      exact map_zero J
    rw [hz, ha0, tensorHsCongrL_ccTensorToHs]
  circle_shifted_solution_with_radius_le_of_lipschitz_coefficients g₀ 1 (by norm_num)
      f₀ houter hρcap A B (Ca * (1 + ‖J‖₊)) (Cb * (1 + ‖J‖₊)) hA hB hA0


private theorem precomposed_circle_solution
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    {R : ℝ} (hR : 0 < R)
    (a : ℝ → Metric.closedBall (0 : V) R → TensorHs g₀ 0 0 1)
    (b : ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1))
    (Ca Cb : ℝ≥0)
    (ha : LipschitzWith Ca (fun p : ℝ × Metric.closedBall (0 : V) R => a p.1 p.2))
    (hb : LipschitzWith Cb (fun p : ℝ × Metric.closedBall (0 : V) R => b p.1 p.2))
    (ha0 : a 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))) :
  let outer := Classical.indefiniteDescription _ (J.exists_pos_norm_mul_le hR)
  have houter : 0 < outer.val := outer.property.1
  let A : ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val →
      CircleHs g₀ ((1 : ℕ) : ℝ) := fun t u =>
    tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (a t (J.closedBallMap outer.property.2.2 u))
  let B : ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val →
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := fun t u =>
    circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (b t (J.closedBallMap outer.property.2.2 u))
    let alpha := extendClosedBall houter.le A
    let reaction := extendClosedBall houter.le B
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ) (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) =>
      appHs g₀ 0 0 (1 : ℕ) (scalarCc g₀ (AddCircle.laplacianDriftCoefficient g₀)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let D := AddCircle.parameterDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let J := circleHsPiInclusion g₀ (Fin n) (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ r : ℝ, ∃ hr : 0 < r, r ≤ outer.val ∧ r ≤ 1 ∧
    ∃ (T : ℝ) (hT : 0 < T), T ≤ r ∧
      let N := shiftedRemainder m Q J D (Q f₀) d q alpha reaction r
      ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
        let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
          (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce
        u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖J v‖ ≤ r}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N t (aeSetLift
            (show (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ r} by
              simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hr.le) field t)) ∧
          u.toFunL2 = (circleHsPiInclusion g₀ (Fin n) (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)).compLpL
            2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) =>
              tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
                (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))).compLpL 2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ r / 4 ∧
          (∀ᵐ t ∂(timeMeasure T),
            ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) => tensorScaleLaplacian
              (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
                (field t) + gforce t =
              m (alpha t (J (field t))) (Q (f₀ + field t)) + reaction t (J (field t))) := by
  obtain ⟨r, hr, hrR, hr1, _, hsol⟩ :=
    precomposed_circle_solution_with_radius_le g₀ f₀ J hR zero_lt_one
      a b Ca Cb ha hb ha0
  exact ⟨r, hr, hrR, hr1, hsol⟩

private def precomposedCircleSolutionRadius
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    {R : ℝ} (hR : 0 < R)
    (a : ℝ → Metric.closedBall (0 : V) R → TensorHs g₀ 0 0 1)
    (b : ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1))
    (sol : PrecomposedCircleSolution g₀ f₀ J hR a b) : ℝ := by
  unfold PrecomposedCircleSolution at sol
  exact sol.val

private def precomposedCircleSolutionWithRadiusLe
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    {R : ℝ} (hR : 0 < R) {ρcap : ℝ} (hρcap : 0 < ρcap)
    (a : ℝ → Metric.closedBall (0 : V) R → TensorHs g₀ 0 0 1)
    (b : ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1))
    (Ca Cb : ℝ≥0)
    (ha : LipschitzWith Ca (fun p : ℝ × Metric.closedBall (0 : V) R => a p.1 p.2))
    (hb : LipschitzWith Cb (fun p : ℝ × Metric.closedBall (0 : V) R => b p.1 p.2))
    (ha0 : a 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))) :
    {sol : PrecomposedCircleSolution g₀ f₀ J hR a b //
      precomposedCircleSolutionRadius g₀ f₀ J hR a b sol ≤ ρcap} := by
  apply Classical.indefiniteDescription
  obtain ⟨r, hr, hrR, hr1, hrcap, hsol⟩ :=
    precomposed_circle_solution_with_radius_le g₀ f₀ J hR hρcap
      a b Ca Cb ha hb ha0
  unfold PrecomposedCircleSolution
  refine ⟨⟨r, hr, hrR, hr1, hsol⟩, ?_⟩
  unfold precomposedCircleSolutionRadius
  exact hrcap

private theorem precomposed_circle_solution_spec_with_radius_le
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    {R : ℝ} (hR : 0 < R)
    (a : ℝ → Metric.closedBall (0 : V) R → TensorHs g₀ 0 0 1)
    (b : ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1))
    (sol : PrecomposedCircleSolution g₀ f₀ J hR a b) {ρcap : ℝ}
    (hcap : precomposedCircleSolutionRadius g₀ f₀ J hR a b sol ≤ ρcap) :
  let outer := Classical.indefiniteDescription _ (J.exists_pos_norm_mul_le hR)
  have houter : 0 < outer.val := outer.property.1
  let A : ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val →
      CircleHs g₀ ((1 : ℕ) : ℝ) := fun t u =>
    tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (a t (J.closedBallMap outer.property.2.2 u))
  let B : ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val →
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := fun t u =>
    circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (b t (J.closedBallMap outer.property.2.2 u))
    let alpha := extendClosedBall houter.le A
    let reaction := extendClosedBall houter.le B
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ) (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) =>
      appHs g₀ 0 0 (1 : ℕ) (scalarCc g₀ (AddCircle.laplacianDriftCoefficient g₀)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let D := AddCircle.parameterDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let J := circleHsPiInclusion g₀ (Fin n) (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ r : ℝ, ∃ hr : 0 < r, r ≤ outer.val ∧ r ≤ 1 ∧ r ≤ ρcap ∧
    ∃ (T : ℝ) (hT : 0 < T), T ≤ r ∧
      let N := shiftedRemainder m Q J D (Q f₀) d q alpha reaction r
      ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
        let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
          (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce
        u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖J v‖ ≤ r}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N t (aeSetLift
            (show (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ r} by
              simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hr.le) field t)) ∧
          u.toFunL2 = (circleHsPiInclusion g₀ (Fin n) (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)).compLpL
            2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) =>
              tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
                (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))).compLpL 2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ r / 4 ∧
          (∀ᵐ t ∂(timeMeasure T),
            ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) => tensorScaleLaplacian
              (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
                (field t) + gforce t =
              m (alpha t (J (field t))) (Q (f₀ + field t)) + reaction t (J (field t))) := by
  unfold PrecomposedCircleSolution at sol
  change sol.val ≤ ρcap at hcap
  obtain ⟨hr, hrR, hr1, hsol⟩ := sol.property
  exact ⟨sol.val, hr, hrR, hr1, hcap, hsol⟩


private theorem precomposed_circle_solution_spec
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    {R : ℝ} (hR : 0 < R)
    (a : ℝ → Metric.closedBall (0 : V) R → TensorHs g₀ 0 0 1)
    (b : ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1))
    (sol : PrecomposedCircleSolution g₀ f₀ J hR a b) :
  let outer := Classical.indefiniteDescription _ (J.exists_pos_norm_mul_le hR)
  have houter : 0 < outer.val := outer.property.1
  let A : ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val →
      CircleHs g₀ ((1 : ℕ) : ℝ) := fun t u =>
    tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (a t (J.closedBallMap outer.property.2.2 u))
  let B : ℝ → Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val →
      CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) := fun t u =>
    circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (b t (J.closedBallMap outer.property.2.2 u))
    let alpha := extendClosedBall houter.le A
    let reaction := extendClosedBall houter.le B
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ) (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    let d := ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) =>
      appHs g₀ 0 0 (1 : ℕ) (scalarCc g₀ (AddCircle.laplacianDriftCoefficient g₀)))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let D := AddCircle.parameterDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let J := circleHsPiInclusion g₀ (Fin n) (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ r : ℝ, ∃ hr : 0 < r, r ≤ outer.val ∧ r ≤ 1 ∧
    ∃ (T : ℝ) (hT : 0 < T), T ≤ r ∧
      let N := shiftedRemainder m Q J D (Q f₀) d q alpha reaction r
      ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
        let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
          (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce
        u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖J v‖ ≤ r}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N t (aeSetLift
            (show (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) ∈ {v | ‖J v‖ ≤ r} by
              simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hr.le) field t)) ∧
          u.toFunL2 = (circleHsPiInclusion g₀ (Fin n) (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)).compLpL
            2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) =>
              tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
                (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))).compLpL 2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ r / 4 ∧
          (∀ᵐ t ∂(timeMeasure T),
            ContinuousLinearMap.piLpMap 2 (fun _ : (Fin n) => tensorScaleLaplacian
              (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
                (field t) + gforce t =
              m (alpha t (J (field t))) (Q (f₀ + field t)) + reaction t (J (field t))) := by
  obtain ⟨r, hr, hrR, hr1, _, hsol⟩ :=
    precomposed_circle_solution_spec_with_radius_le g₀ f₀ J hR a b sol le_rfl
  exact ⟨r, hr, hrR, hr1, hsol⟩

private def precomposedCircleSolution
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    {R : ℝ} (hR : 0 < R)
    (a : ℝ → Metric.closedBall (0 : V) R → TensorHs g₀ 0 0 1)
    (b : ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1))
    (Ca Cb : ℝ≥0)
    (ha : LipschitzWith Ca (fun p : ℝ × Metric.closedBall (0 : V) R => a p.1 p.2))
    (hb : LipschitzWith Cb (fun p : ℝ × Metric.closedBall (0 : V) R => b p.1 p.2))
    (ha0 : a 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))) : PrecomposedCircleSolution g₀ f₀ J hR a b := by
  unfold PrecomposedCircleSolution
  exact Classical.indefiniteDescription _ (precomposed_circle_solution g₀ f₀ J hR a b Ca Cb ha hb ha0)

private structure ScalarVectorTimeCoefficients
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) where
  radius : ℝ
  radius_pos : 0 < radius
  diffusionLipschitz : ℝ≥0
  reactionLipschitz : ℝ≥0
  diffusion : ℝ → Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) radius → TensorHs g₀ 0 0 1
  reaction : ℝ → Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) radius → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1)
  diffusion_lipschitz : LipschitzWith diffusionLipschitz (fun p : ℝ × Metric.closedBall
    (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) radius => diffusion p.1 p.2)
  reaction_lipschitz : LipschitzWith reactionLipschitz (fun p : ℝ × Metric.closedBall
    (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) radius => reaction p.1 p.2)
  range_mem : ∀ t ∈ Set.Icc (0 : ℝ) radius,
    ∀ u ∈ Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) radius,
      Set.range (scalarH1PiToContinuous g₀ (scalarH1TimeCoordinate g₀ (0 + t, u₀ + u))) ⊆ S
  diffusion_eval : ∀ t ∈ Set.Icc (0 : ℝ) radius, ∀ u x,
    scalarH1ToContinuous g₀ (diffusion t u) x = F (fun i => match i with
      | none => 0 + t
      | some i => scalarH1ToContinuous g₀ (u₀ i + u.1 i) x)
  reaction_eval : ∀ t ∈ Set.Icc (0 : ℝ) radius, ∀ u x j,
    scalarH1ToContinuous g₀ (reaction t u j) x = G (fun i => match i with
      | none => 0 + t
      | some i => scalarH1ToContinuous g₀ (u₀ i + u.1 i) x) j

private def ambientCoefficients
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    ScalarVectorTimeCoefficients (c₀.pullbackMetric (g 0))
      (curveShorteningChartDiffusionCoefficient (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n)
      (fun z j => curveShorteningParametricChartReaction (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j)
      (firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β)
      (ambientFirstJet c₀ (g 0) e he) := by
  let radius := ambientCoefficientRadius c₀ g ht he hr hEU hleft β hG
  let ca := Classical.indefiniteDescription _ radius.property.2
  let cb := Classical.indefiniteDescription _ ca.property
  let a := Classical.indefiniteDescription _ cb.property
  let b := Classical.indefiniteDescription _ a.property
  exact ⟨radius.val, radius.property.1, ca.val, cb.val, a.val, b.val,
    b.property.1, b.property.2.1, b.property.2.2.1, b.property.2.2.2.1, b.property.2.2.2.2⟩

private theorem initial_diffusion_coefficients
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (C : ScalarVectorTimeCoefficients (c₀.pullbackMetric (g 0))
      (curveShorteningChartDiffusionCoefficient (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n)
      (fun z j => curveShorteningParametricChartReaction (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j)
      (firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β)
      (ambientFirstJet c₀ (g 0) e he)) :
    C.diffusion 0 ⟨0, Metric.mem_closedBall_self C.radius_pos.le⟩ =
      ccTensorToHs (c₀.pullbackMetric (g 0)) 0 1
        (scalarCc (c₀.pullbackMetric (g 0)) (AddCircle.laplacianPrincipalCoefficient (c₀.pullbackMetric (g 0)))) := by
  apply initial_diffusion_H1 c₀ g he hr hEU hleft β
  intro z
  rw [C.diffusion_eval 0 ⟨le_rfl, C.radius_pos.le⟩]
  dsimp only [Function.comp_def]
  congr 2
  funext j
  cases j with
  | none => simp only [zero_add, scalarH1TimeCoordinate_eval_none]
  | some i => simp only [PiLp.zero_apply, add_zero, scalarH1TimeCoordinate_eval_some]

private def ambientSobolevSolutionOfCoefficients
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (C : ScalarVectorTimeCoefficients (c₀.pullbackMetric (g 0))
      (curveShorteningChartDiffusionCoefficient (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n)
      (fun z j => curveShorteningParametricChartReaction (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j)
      (firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β)
      (ambientFirstJet c₀ (g 0) e he)) :
    PrecomposedCircleSolution (c₀.pullbackMetric (g 0))
      (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
      ((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
        (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap)
      C.radius_pos C.diffusion C.reaction :=
  precomposedCircleSolution (c₀.pullbackMetric (g 0))
    (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
    ((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
      (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap)
    C.radius_pos C.diffusion C.reaction C.diffusionLipschitz C.reactionLipschitz
    C.diffusion_lipschitz C.reaction_lipschitz
    (initial_diffusion_coefficients c₀ g he hr hEU hleft β C)


private def ambientSobolevSolution
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :=
  ambientSobolevSolutionOfCoefficients c₀ g he hr hEU hleft β
    (ambientCoefficients c₀ g ht he hr hEU hleft β hG)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end


noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open TensorHeatEquation TensorSpectral TimeSobolev

private theorem norm_le_on_Icc_of_ae_le
    {X : Type*} [SeminormedAddCommGroup X] {w : ℝ → X} {a b C : ℝ}
    (hab : a ≠ b) (hw : ContinuousOn w (Icc a b))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc a b), ‖w t‖ ≤ C) :
    ∀ t ∈ Icc a b, ‖w t‖ ≤ C := by
  have heq : (fun t => max ‖w t‖ C) =ᵐ[volume.restrict (Icc a b)] fun _ => C := by
    filter_upwards [hbound] with t ht
    exact max_eq_right ht
  have h := Measure.eqOn_Icc_of_ae_eq volume hab heq
    (fun t ht => (hw t ht).norm.max continuousWithinAt_const) continuousOn_const
  intro t ht
  exact (le_max_left ‖w t‖ C).trans_eq (h ht)

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T R : ℝ}

private theorem exists_continuousOn_bounded_intermediate_representative
    (hT : 0 < T)
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T)
    (v : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) T)
    (hreal : u.toFunL2 = (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith))).compLpL 2 (timeMeasure T) v)
    (hbound : ∀ᵐ t ∂timeMeasure T,
      ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith)) (v t)‖ ≤ R)
    (htrace : timeH1.trace0 _ T u = 0) :
    ∃ w : ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)),
      ContinuousOn w (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 1 by linarith)) (w t) = u.toFun t) ∧
      w =ᵐ[timeMeasure T] (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith)) (v t)) ∧
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ R) ∧ w 0 = 0 := by
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith))
  have hlink : ∀ᵐ t ∂timeMeasure T, L (v t) = u.toFun t := by
    have ha := L.coeFn_compLpL (p := 2) (μ := timeMeasure T) v
    have hb := coeFn_ofContinuousOn u.continuousOn_toFun
    filter_upwards [ha, hb] with t hta htb
    change (L.compLpL 2 (timeMeasure T) v) t = L (v t) at hta
    change u.toFunL2 t = u.toFun t at htb
    rw [← hreal] at hta
    exact hta.symm.trans htb
  obtain ⟨w, hw, hlo, hhi⟩ := exists_continuousOn_intermediate_representative hT u v hlink
  refine ⟨w, hw, hlo, hhi, ?_, ?_⟩
  · apply norm_le_on_Icc_of_ae_le (ne_of_lt hT) hw
    filter_upwards [hbound, hhi] with t ht heq
    rwa [heq]
  · apply PiLp.ext
    intro i
    apply tensorHsInclusion_injective (show a ≤ a + 1 by linarith)
    have hu0 : u.toFun 0 = 0 := by
      simpa only [timeH1.toFun_zero, timeH1.trace0_apply] using htrace
    have h := congrArg (fun z => z i) (hlo 0 ⟨le_rfl, hT.le⟩)
    simpa only [hu0, ContinuousLinearMap.piLpMap_apply, PiLp.zero_apply, map_zero] using h

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem precomposed_circle_solution_exists_with_radius_le
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    {R : ℝ} (hR : 0 < R)
    (a : ℝ → Metric.closedBall (0 : V) R → TensorHs g₀ 0 0 1)
    (b : ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1))
    (sol : PrecomposedCircleSolution g₀ f₀ J hR a b) {ρcap : ℝ}
    (hcap : precomposedCircleSolutionRadius g₀ f₀ J hR a b sol ≤ ρcap) :
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
        (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ρ ≤ 1 ∧ ρ ≤ ρcap ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0)
              (a := ((1 : ℕ) : ℝ)) hT 0 gforce
          u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
              (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0)
                (a := ((1 : ℕ) : ℝ)) hT 0 gforce ∧
            (∀ᵐ t ∂(timeMeasure T), ‖K (field t)‖ ≤ ρ) ∧
            u.toFunL2 = (circleHsPiInclusion g₀ (Fin n)
              (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)).compLpL
                2 (timeMeasure T) field ∧
            timeH1.trace0 _ T u = 0 ∧
            timeH1.timeDeriv _ T u = L.compLpL 2 (timeMeasure T) field + gforce ∧
            ‖gforce‖ ≤ ρ / 4 ∧
            (∀ᵐ t ∂(timeMeasure T), ∃ z : Metric.closedBall (0 : V) R,
              (z : V) = J (K (field t)) ∧
              L (field t) + gforce t = m (tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                (a t z)) (Q (f₀ + field t)) +
                circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (b t z)) ∧
            ∃ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
              ContinuousOn w (Set.Icc 0 T) ∧
              (∀ t ∈ Set.Icc 0 T,
                circleHsPiInclusion g₀ (Fin n)
                  (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by linarith)
                  (w t) = u.toFun t) ∧
              w =ᵐ[timeMeasure T] (fun t => K (field t)) ∧
              (∀ t ∈ Set.Icc 0 T, ‖w t‖ ≤ ρ) ∧ w 0 = 0 ∧
              (∀ t ∈ Set.Icc 0 T, ‖J (w t)‖ ≤ R) ∧
              let alpha := fun t => tensorHsCongrL g₀ 0 0
                (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (extendClosedBall hR.le a t (J (w t)))
              let reaction := fun t => circleHsPiCongr g₀ (Fin n)
                (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (extendClosedBall hR.le b t (J (w t)))
              let S := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
                (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
              let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => S)
              let K₀ := circleHsPiInclusion g₀ (Fin n)
                (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P (K₀ f₀ + u.toFun t))
                (x : AddCircle (1 : ℝ))
              (∀ᵐ t ∂timeMeasure T,
                L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) ∧
              (∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (f t) ∧ ∀ x : ℝ,
                HasDerivAt (fun s => f s x)
                  (scalarH1ToContinuous g₀ (S (alpha t)) (x : AddCircle (1 : ℝ)) •
                    deriv (deriv (f t)) x + scalarH1PiToContinuous g₀ (P (reaction t))
                      (x : AddCircle (1 : ℝ))) t) := by
  let outer := Classical.indefiniteDescription _ (J.exists_pos_norm_mul_le hR)
  obtain ⟨ρ, hρ, hρouter, hρone, hρcap, T, hT, hTρ, u, gforce,
    hu, hstate, hforce, hreal, htrace, hderiv, hnorm, heq⟩ :=
      precomposed_circle_solution_spec_with_radius_le g₀ f₀ J hR a b sol hcap
  obtain ⟨w, hw, hwlo, hwhi, hwbound, hwzero⟩ :=
    exists_continuousOn_bounded_intermediate_representative hT u
      (maximalRegularityDuhamelVectorField hT 0 gforce) hreal hstate htrace
  have hJbound : ∀ t ∈ Set.Icc 0 T, ‖J (w t)‖ ≤ R := by
    intro t ht
    exact (J.le_opNorm (w t)).trans
      ((mul_le_mul_of_nonneg_left ((hwbound t ht).trans hρouter) (norm_nonneg J)).trans
        outer.property.2.2)
  have heqz : ∀ᵐ t ∂timeMeasure T, ∃ z : Metric.closedBall (0 : V) R,
      (z : V) = J (circleHsPiInclusion g₀ (Fin n)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (maximalRegularityDuhamelVectorField hT 0 gforce t)) ∧
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => tensorScaleLaplacian
        (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
          (maximalRegularityDuhamelVectorField hT 0 gforce t) + gforce t =
      coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
        (tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) (a t z))
        (AddCircle.parameterSecondDerivativeHsPi g₀ 1
          (f₀ + maximalRegularityDuhamelVectorField hT 0 gforce t)) +
      circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)) (b t z) := by
    filter_upwards [hstate, heq] with t ht heq
    have htouter : circleHsPiInclusion g₀ (Fin n)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
          (maximalRegularityDuhamelVectorField hT 0 gforce t) ∈
        Metric.closedBall (0 : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) outer.val := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using ht.trans hρouter
    refine ⟨J.closedBallMap outer.property.2.2 ⟨_, htouter⟩, rfl, ?_⟩
    simpa only [extendClosedBall_apply _ _ _ _ htouter] using heq
  dsimp only
  refine ⟨ρ, hρ, hρouter.trans outer.property.2.1, hρone, hρcap, T, hT, hTρ,
    u, gforce, hu, hstate, hreal, htrace, hderiv, hnorm, heqz,
    w, hw, hwlo, hwhi, hwbound, hwzero, hJbound, ?_⟩
  have heqw : ∀ᵐ t ∂timeMeasure T,
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => tensorScaleLaplacian
        (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
          (maximalRegularityDuhamelVectorField hT 0 gforce t) + gforce t =
      coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
        (tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall hR.le a t (J (w t))))
        (AddCircle.parameterSecondDerivativeHsPi g₀ 1
          (f₀ + maximalRegularityDuhamelVectorField hT 0 gforce t)) +
      circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall hR.le b t (J (w t))) := by
    filter_upwards [heqz, hwhi] with t ht hwt
    rcases ht with ⟨z, hz, heq⟩
    have hJw : J (w t) = z.val := by
      rw [hwt]
      exact hz.symm
    rw [hJw]
    simpa only [extendClosedBall_apply hR.le a t z z.property,
      extendClosedBall_apply hR.le b t z z.property] using heq
  refine ⟨heqw, ?_⟩
  exact ae_hasDerivAt_of_circle_sobolev_evolution g₀ u
    (maximalRegularityDuhamelVectorField hT 0 gforce) f₀ gforce
    (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => tensorScaleLaplacian
      (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)))
    (fun t => tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (extendClosedBall hR.le a t (J (w t))))
    (fun t => circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (extendClosedBall hR.le b t (J (w t)))) hreal hderiv heqw


private theorem precomposed_circle_solution_exists
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ] V)
    {R : ℝ} (hR : 0 < R)
    (a : ℝ → Metric.closedBall (0 : V) R → TensorHs g₀ 0 0 1)
    (b : ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1))
    (sol : PrecomposedCircleSolution g₀ f₀ J hR a b) :
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
        (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0)
              (a := ((1 : ℕ) : ℝ)) hT 0 gforce
          u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
              (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0)
                (a := ((1 : ℕ) : ℝ)) hT 0 gforce ∧
            (∀ᵐ t ∂(timeMeasure T), ‖K (field t)‖ ≤ ρ) ∧
            u.toFunL2 = (circleHsPiInclusion g₀ (Fin n)
              (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)).compLpL
                2 (timeMeasure T) field ∧
            timeH1.trace0 _ T u = 0 ∧
            timeH1.timeDeriv _ T u = L.compLpL 2 (timeMeasure T) field + gforce ∧
            ‖gforce‖ ≤ ρ / 4 ∧
            (∀ᵐ t ∂(timeMeasure T), ∃ z : Metric.closedBall (0 : V) R,
              (z : V) = J (K (field t)) ∧
              L (field t) + gforce t = m (tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                (a t z)) (Q (f₀ + field t)) +
                circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (b t z)) ∧
            ∃ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
              ContinuousOn w (Set.Icc 0 T) ∧
              (∀ t ∈ Set.Icc 0 T,
                circleHsPiInclusion g₀ (Fin n)
                  (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by linarith)
                  (w t) = u.toFun t) ∧
              w =ᵐ[timeMeasure T] (fun t => K (field t)) ∧
              (∀ t ∈ Set.Icc 0 T, ‖w t‖ ≤ ρ) ∧ w 0 = 0 ∧
              (∀ t ∈ Set.Icc 0 T, ‖J (w t)‖ ≤ R) ∧
              let alpha := fun t => tensorHsCongrL g₀ 0 0
                (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (extendClosedBall hR.le a t (J (w t)))
              let reaction := fun t => circleHsPiCongr g₀ (Fin n)
                (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (extendClosedBall hR.le b t (J (w t)))
              let S := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
                (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
              let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => S)
              let K₀ := circleHsPiInclusion g₀ (Fin n)
                (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P (K₀ f₀ + u.toFun t))
                (x : AddCircle (1 : ℝ))
              (∀ᵐ t ∂timeMeasure T,
                L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) ∧
              (∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (f t) ∧ ∀ x : ℝ,
                HasDerivAt (fun s => f s x)
                  (scalarH1ToContinuous g₀ (S (alpha t)) (x : AddCircle (1 : ℝ)) •
                    deriv (deriv (f t)) x + scalarH1PiToContinuous g₀ (P (reaction t))
                      (x : AddCircle (1 : ℝ))) t) := by
  obtain ⟨ρ, hρ, hρR, hρone, _, hsol⟩ :=
    precomposed_circle_solution_exists_with_radius_le g₀ f₀ J hR a b sol le_rfl
  exact ⟨ρ, hρ, hρR, hρone, hsol⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end


noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem hasDerivAt_circleH2 (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (v : TensorHs g 0 0 (1 + 1)) (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 1 + 1) v)
          (t : AddCircle (1 : ℝ)))
      (scalarH1ToContinuous g (circleDerivativeH1 g v) (x : AddCircle (1 : ℝ))) x := by
  have hcoeff {a b : ℝ} (hab : a = b) (w : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 hab w).coeff = w.coeff := by
    cases hab
    rfl
  let w := tensorHsCongrL g 0 0
    (by norm_num : (1 : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1) v
  have h := AddCircle.hasDerivAt_scalarH1ToContinuous g w x
  convert h using 1
  · funext t
    apply congrArg (fun u : TensorHs g 0 0 1 => scalarH1ToContinuous g u (t : AddCircle (1 : ℝ)))
    apply TensorHs.ext
    rw [tensorHsInclusion_coeff, tensorHsInclusion_coeff]
    exact (hcoeff _ v).symm
  · apply congrArg (fun u : TensorHs g 0 0 1 => scalarH1ToContinuous g u (x : AddCircle (1 : ℝ)))
    apply TensorHs.ext
    simp only [circleDerivativeH1, ContinuousLinearMap.comp_apply,
      hcoeff, tensorHsInclusion_coeff]
    rfl

private theorem hasDerivAt_circleH2Pi {n : ℕ}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (v : PiLp 2 (fun _ : Fin n => TensorHs g 0 0 (1 + 1))) (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => WithLp.toLp 2 (fun i => scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 1 + 1) (v i))
          (t : AddCircle (1 : ℝ))))
      (WithLp.toLp 2 (fun i => scalarH1ToContinuous g
        (circleDerivativeH1 g (v i)) (x : AddCircle (1 : ℝ)))) x := by
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt x
    (hasDerivAt_pi.mpr (fun i => hasDerivAt_circleH2 g (v i) x))


omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem firstJetCoordinates_ambientFirstJet_add
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (v : PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric g) 0 0 (1 + 1))) (t x : ℝ) :
    firstJetCoordinates n
      (scalarH1PiToContinuous (c₀.pullbackMetric g)
        (scalarH1TimeCoordinate (c₀.pullbackMetric g)
          (t, ambientFirstJet c₀ g e he + circleFirstJet (c₀.pullbackMetric g) v))
          (x : AddCircle (1 : ℝ))) =
      (t, e (c₀.map (x : AddCircle (1 : ℝ))) + WithLp.toLp 2 (fun i =>
        scalarH1ToContinuous (c₀.pullbackMetric g)
          (tensorHsInclusion (g := c₀.pullbackMetric g) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ 1 + 1) (v i)) (x : AddCircle (1 : ℝ))),
        deriv (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ)))) x + WithLp.toLp 2 (fun i =>
          scalarH1ToContinuous (c₀.pullbackMetric g)
            (circleDerivativeH1 (c₀.pullbackMetric g) (v i)) (x : AddCircle (1 : ℝ)))) := by
  have hbase := firstJetCoordinates_ambientFirstJet c₀ g e he t x
  apply Prod.ext
  · exact scalarH1TimeCoordinate_eval_none _ _ _
  apply Prod.ext
  · apply PiLp.ext
    intro i
    change scalarH1ToContinuous (c₀.pullbackMetric g)
      ((ambientFirstJet c₀ g e he + circleFirstJet (c₀.pullbackMetric g) v) (Sum.inl i))
      (x : AddCircle (1 : ℝ)) = _
    rw [PiLp.add_apply, map_add, ContinuousMap.add_apply]
    exact congrArg₂ (· + ·) (scalarH1PiToContinuous_ambientFirstJet_inl c₀ g e he _ i) rfl
  · apply PiLp.ext
    intro i
    change scalarH1ToContinuous (c₀.pullbackMetric g)
      ((ambientFirstJet c₀ g e he + circleFirstJet (c₀.pullbackMetric g) v) (Sum.inr i))
      (x : AddCircle (1 : ℝ)) = _
    rw [PiLp.add_apply, map_add, ContinuousMap.add_apply]
    have hb := congrArg (fun p : ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.2.2 i) hbase
    exact congrArg₂ (· + ·) hb rfl

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem firstJetCoordinates_ambientFirstJet_add_deriv
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (v : PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric g) 0 0 (1 + 1))) (t x : ℝ) :
    let f := fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ))) + WithLp.toLp 2 (fun i =>
      scalarH1ToContinuous (c₀.pullbackMetric g)
        (tensorHsInclusion (g := c₀.pullbackMetric g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 1 + 1) (v i)) (y : AddCircle (1 : ℝ)))
    firstJetCoordinates n
      (scalarH1PiToContinuous (c₀.pullbackMetric g)
        (scalarH1TimeCoordinate (c₀.pullbackMetric g)
          (t, ambientFirstJet c₀ g e he + circleFirstJet (c₀.pullbackMetric g) v))
          (x : AddCircle (1 : ℝ))) = (t, f x, deriv f x) := by
  intro f
  have hd : DifferentiableAt ℝ (fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ)))) x :=
    ((he.comp c₀.contMDiff_map).comp AddCircle.contMDiff_coe).contDiff.differentiable (by decide) x
  have hf := hd.hasDerivAt.add (hasDerivAt_circleH2Pi (c₀.pullbackMetric g) v x)
  rw [firstJetCoordinates_ambientFirstJet_add]
  exact congrArg (fun p => (t, f x, p)) hf.deriv.symm

private theorem coefficients_eval
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ}
    {G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ)}
    {S : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    {u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)}
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) C.radius)
    (v : Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) C.radius)
    (z : AddCircle (1 : ℝ)) :
    let q := scalarH1PiToContinuous g₀ (scalarH1TimeCoordinate g₀ (t, u₀ + v.val)) z
    q ∈ S ∧
    scalarH1ToContinuous g₀ (C.diffusion t v) z = F q ∧
    ∀ j, scalarH1ToContinuous g₀ (C.reaction t v j) z = G q j := by
  intro q
  have hcoords : (fun i : Option (Fin n ⊕ Fin n) => match i with
      | none => 0 + t
      | some i => scalarH1ToContinuous g₀ (u₀ i + v.val i) z) = q := by
    funext i
    cases i with
    | none => simpa only [zero_add] using
        (scalarH1TimeCoordinate_eval_none g₀ (t, u₀ + v.val) z).symm
    | some i => rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa only [zero_add] using C.range_mem t ht v.val v.property (Set.mem_range_self z)
  · rw [C.diffusion_eval t ht v z, hcoords]
  · intro j
    rw [C.reaction_eval t ht v z j, hcoords]

private theorem coefficients_eval_of_eq_circleFirstJet
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (β : U)
    (C : ScalarVectorTimeCoefficients (c₀.pullbackMetric (g 0))
      (curveShorteningChartDiffusionCoefficient (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n)
      (fun z j => curveShorteningParametricChartReaction (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j)
      (firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β)
      (ambientFirstJet c₀ (g 0) e he))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) C.radius)
    (u : PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 (1 + 1)))
    (v : Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 1)) C.radius)
    (hv : v.val = circleFirstJet (c₀.pullbackMetric (g 0)) u)
    (x : ℝ) :
    let g₀ := c₀.pullbackMetric (g 0)
    let z := (x : AddCircle (1 : ℝ))
    let f := fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ))) + WithLp.toLp 2 (fun i =>
      scalarH1ToContinuous g₀
        (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 1 + 1) (u i)) (y : AddCircle (1 : ℝ)))
    let q := (t, f x, deriv f x)
    q ∈ curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∧
    scalarH1ToContinuous g₀ (C.diffusion t v) z = curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β q ∧
    ∀ j, scalarH1ToContinuous g₀ (C.reaction t v j) z = curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β q j := by
  intro g₀ z f q
  have hq : firstJetCoordinates n (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, ambientFirstJet c₀ (g 0) e he + v.val)) z) = q := by
    rw [hv]
    exact firstJetCoordinates_ambientFirstJet_add_deriv c₀ (g 0) e he u t x
  have h := coefficients_eval g₀ C t ht v z
  refine ⟨?_, ?_, ?_⟩
  · have hm := h.1
    change firstJetCoordinates n
      (scalarH1PiToContinuous g₀
        (scalarH1TimeCoordinate g₀ (t, ambientFirstJet c₀ (g 0) e he + v.val)) z) ∈ curveShorteningChartFirstJetDomain D
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β at hm
    rwa [hq] at hm
  · have hd := h.2.1
    change _ = curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
      (firstJetCoordinates n
        (scalarH1PiToContinuous g₀
          (scalarH1TimeCoordinate g₀ (t, ambientFirstJet c₀ (g 0) e he + v.val)) z)) at hd
    rwa [hq] at hd
  · intro j
    have hb := h.2.2 j
    change _ = curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
      (firstJetCoordinates n
        (scalarH1PiToContinuous g₀
          (scalarH1TimeCoordinate g₀ (t, ambientFirstJet c₀ (g 0) e he + v.val)) z)) j at hb
    rwa [hq] at hb

private theorem ambientCoefficients_eval_of_eq_circleFirstJet
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht₀ : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht₀ he hr hEU hleft β hG
    ∀ (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) C.radius)
    (u : PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 (1 + 1)))
    (v : Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 1)) C.radius)
    (_ : v.val = circleFirstJet (c₀.pullbackMetric (g 0)) u)
    (x : ℝ),
    let g₀ := c₀.pullbackMetric (g 0)
    let z := (x : AddCircle (1 : ℝ))
    let f := fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ))) + WithLp.toLp 2 (fun i =>
      scalarH1ToContinuous g₀
        (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 1 + 1) (u i)) (y : AddCircle (1 : ℝ)))
    let q := (t, f x, deriv f x)
    q ∈ curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∧
    scalarH1ToContinuous g₀ (C.diffusion t v) z = curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β q ∧
    ∀ j, scalarH1ToContinuous g₀ (C.reaction t v j) z = curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β q j := by
  intro C t ht u v hv x
  exact coefficients_eval_of_eq_circleFirstJet c₀ g he hr β C t ht u v hv x

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end



noncomputable section
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩


variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}

private theorem ambient_sobolev_solution_exists
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
        (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ C.radius ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0)
              (a := ((1 : ℕ) : ℝ)) hT 0 gforce
          u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
              (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0)
                (a := ((1 : ℕ) : ℝ)) hT 0 gforce ∧
            (∀ᵐ t ∂(timeMeasure T), ‖K (field t)‖ ≤ ρ) ∧
            u.toFunL2 = (circleHsPiInclusion g₀ (Fin n)
              (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)).compLpL
                2 (timeMeasure T) field ∧
            timeH1.trace0 _ T u = 0 ∧
            timeH1.timeDeriv _ T u = L.compLpL 2 (timeMeasure T) field + gforce ∧
            ‖gforce‖ ≤ ρ / 4 ∧
            (∀ᵐ t ∂(timeMeasure T), ∃ z : Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) C.radius,
              (z : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) = J (K (field t)) ∧
              L (field t) + gforce t = m (tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                (C.diffusion t z)) (Q (f₀ + field t)) +
                circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (C.reaction t z)) ∧
            ∃ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
              ContinuousOn w (Set.Icc 0 T) ∧
              (∀ t ∈ Set.Icc 0 T,
                circleHsPiInclusion g₀ (Fin n)
                  (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by linarith)
                  (w t) = u.toFun t) ∧
              w =ᵐ[timeMeasure T] (fun t => K (field t)) ∧
              (∀ t ∈ Set.Icc 0 T, ‖w t‖ ≤ ρ) ∧ w 0 = 0 ∧
              (∀ t ∈ Set.Icc 0 T, ‖J (w t)‖ ≤ C.radius) ∧
              let alpha := fun t => tensorHsCongrL g₀ 0 0
                (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))
              let reaction := fun t => circleHsPiCongr g₀ (Fin n)
                (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))
              let S := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
                (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
              let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => S)
              let K₀ := circleHsPiInclusion g₀ (Fin n)
                (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P (K₀ f₀ + u.toFun t))
                (x : AddCircle (1 : ℝ))
              (∀ᵐ t ∂timeMeasure T,
                L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) ∧
              (∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (f t) ∧ ∀ x : ℝ,
                HasDerivAt (fun s => f s x)
                  (scalarH1ToContinuous g₀ (S (alpha t)) (x : AddCircle (1 : ℝ)) •
                    deriv (deriv (f t)) x + scalarH1PiToContinuous g₀ (P (reaction t))
                      (x : AddCircle (1 : ℝ))) t) := by
  intro C
  exact precomposed_circle_solution_exists
    (c₀.pullbackMetric (g 0))
    (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
    ((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
      (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap)
    C.radius_pos C.diffusion C.reaction
    (ambientSobolevSolutionOfCoefficients c₀ g he hr hEU hleft β C)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {ι : Type*} [Fintype ι]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem circleFirstJet_eq_normalized_firstJetHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : CircleHsPi g ι (1 + 1)) :
    circleFirstJet g u =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
        (AddCircle.firstJetHs g 1
          (circleHsPiCongr g ι (by norm_num : (1 : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1) u)) := by
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  apply PiLp.ext
  intro j
  cases j with
  | inl i =>
    apply TensorHs.ext
    change (u i).coeff =
      (tensorHsCongrL g 0 0 (by norm_num : (1 : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1)
        (u i)).coeff
    rw [hcongr]
  | inr i =>
    apply TensorHs.ext
    change (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
      ((AddCircle.parameterDerivativeHs g 1)
        (tensorHsCongrL g 0 0
          (by norm_num : (1 : ℝ) + 1 = ((1 : ℕ) : ℝ) + 1) (u i)))).coeff = _
    rw [hcongr]
    rfl

private theorem circle_firstJetHs_normalized
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (u : CircleHsPi g ι (((1 : ℕ) : ℝ) + 1)) :
    circleFirstJet g
      (circleHsPiCongr g ι (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) u) =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))) (AddCircle.firstJetHs g 1 u) := by
  have hc {a b : ℝ} (h : a = b) (v : CircleHsPi g ι a) :
      circleHsPiCongr g ι h.symm (circleHsPiCongr g ι h v) = v := by
    cases h
    rfl
  rw [circleFirstJet_eq_normalized_firstJetHs, hc]

private theorem circle_timeL2_h2_composition
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (T : ℝ)
    (f₀ : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (u : timeL2 (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) T)
    (w : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 1))
    (hw : ContinuousOn w (Icc 0 T))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {S : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (a : ℝ → TensorHs g 0 0 1) (ha : AEStronglyMeasurable a (timeMeasure T)) :
    let J := (circleFirstJet (ι := ι) g).comp
      (circleHsPiCongr g ι
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g ι
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let q := fun t => scalarH1TimeCoordinate g (t, J (K f₀ + w t))
    w =ᵐ[timeMeasure T] (fun t => K (u t)) →
    (∀ t ∈ Icc 0 T, range (scalarH1PiToContinuous g (q t)) ⊆ S) →
    (∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (a t) x =
      F (scalarH1PiToContinuous g (q t) x)) →
    ∃ a₂ : timeL2 (TensorHs g 0 0 2) T,
      (fun t => tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T] a := by
  intro J K q hwu hRange hEval
  let E := (circleHsPiCongr g ι
    (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let u₂ := E.compLpL 2 (timeMeasure T) u
  let K₂ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1))
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  have hK₂ (v : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) : K₂ (E v) = K v := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    change (tensorHsCongrL g 0 0
      (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1) (v i)).coeff = (v i).coeff
    rw [hcongr]
  have hw₂ : w =ᵐ[timeMeasure T] (fun t => K₂ (u₂ t)) := by
    filter_upwards [hwu, E.coeFn_compLpL (p := 2) (μ := timeMeasure T) u] with t ht he
    change u₂ t = E (u t) at he
    rw [he, hK₂]
    exact ht
  have hq (t : ℝ) :
      scalarH1TimeCoordinate g (t, L (AddCircle.firstJetHs g 1 (K₂ (E f₀) + w t))) = q t := by
    rw [hK₂, ← circle_firstJetHs_normalized]
    rfl
  apply AddCircle.exists_timeL2_scalarH2_composition_firstJet g T (E f₀) u₂ w hw
    F hF hS a ha hw₂
  · intro t ht
    change range (scalarH1PiToContinuous g
      (scalarH1TimeCoordinate g (t, L (AddCircle.firstJetHs g 1 (K₂ (E f₀) + w t))))) ⊆ S
    rw [hq]
    exact hRange t ht
  · filter_upwards [hEval] with t ht
    change ∀ x, scalarH1ToContinuous g (a t) x = F (scalarH1PiToContinuous g
      (scalarH1TimeCoordinate g (t, L (AddCircle.firstJetHs g 1 (K₂ (E f₀) + w t)))) x)
    rw [hq]
    exact ht

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Geometry.Curvature

variable {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalarVectorTimeCoefficients_diffusion_h2
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S) (T : ℝ) (hT : T ≤ C.radius)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T)
    (w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hw : ContinuousOn w (Icc 0 T)) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    u₀ = J (K f₀) →
    w =ᵐ[timeMeasure T] (fun t => K (field t)) →
    (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
    ∃ a₂ : timeL2 (TensorHs g₀ 0 0 2) T,
      (fun t => tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T]
        (fun t => extendClosedBall C.radius_pos.le C.diffusion t (J (w t))) := by
  classical
  intro J K hu₀ hwu hbound
  let a := fun t => extendClosedBall C.radius_pos.le C.diffusion t (J (w t))
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) C.radius := fun t =>
    ⟨J (w t), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  have hz : Continuous z :=
    (J.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hw)).subtype_mk _
  have he (t : Icc (0 : ℝ) T) : a t = C.diffusion t (z t) :=
    extendClosedBall_apply C.radius_pos.le C.diffusion t (J (w t)) (z t).2
  have ha : ContinuousOn a (Icc 0 T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply (C.diffusion_lipschitz.continuous.comp (continuous_subtype_val.prodMk hz)).congr
    intro t
    exact (he t).symm
  apply circle_timeL2_h2_composition g₀ T f₀ field w hw F hF hS a
    (memLp_of_continuousOn ha).aestronglyMeasurable hwu
  · intro t ht
    have h := C.range_mem t ⟨ht.1, ht.2.trans hT⟩ (J (w t)) (z ⟨t, ht⟩).2
    change range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t)))) ⊆ S
    rw [map_add, ← hu₀]
    simpa only [zero_add] using h
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t htt
    intro x
    change scalarH1ToContinuous g₀ (a t) x = F
      (scalarH1PiToContinuous g₀ (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))) x)
    rw [map_add, ← hu₀, he ⟨t, htt⟩, C.diffusion_eval t ⟨htt.1, htt.2.trans hT⟩]
    congr 1
    funext i
    cases i with
    | none => simp only [zero_add, scalarH1TimeCoordinate_eval_none]
    | some i =>
      simp only [scalarH1TimeCoordinate_eval_some, PiLp.add_apply]
      rfl

private theorem scalarVectorTimeCoefficients_diffusion_higher_order
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S) (k : ℕ)
    (T : ℝ) (hT : T ≤ C.radius)
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (field : timeL2
      (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (w : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hw : ContinuousOn w (Icc 0 T))
    (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1))
    (ha : AEStronglyMeasurable a (timeMeasure T)) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    u₀ = J (K f₀) →
    w =ᵐ[timeMeasure T] (fun t => K (field t)) →
    (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
    (fun t => A (a t)) =ᵐ[timeMeasure T]
      (fun t => extendClosedBall C.radius_pos.le C.diffusion t (J (w t))) →
    ∃ aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T,
      (fun t => tensorHsInclusion (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
        (aHigh t)) =ᵐ[timeMeasure T] a := by
  classical
  intro K L J A hu₀ hwu hbound hactual
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) C.radius := fun t =>
    ⟨J (w t), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  apply AddCircle.exists_timeL2_scalarHs_composition_firstJet g₀ k T f₀ field w hw
    F hF hS a ha hwu
  · intro t ht
    have h := C.range_mem t ⟨ht.1, ht.2.trans hT⟩ (J (w t)) (z ⟨t, ht⟩).2
    change range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t)))) ⊆ S
    rw [map_add, ← hu₀]
    simpa only [zero_add] using h
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht, hactual] with t htt hat
    intro x
    change scalarH1ToContinuous g₀ (A (a t)) x =
      F (scalarH1PiToContinuous g₀
        (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))) x)
    rw [hat, extendClosedBall_apply C.radius_pos.le C.diffusion t (J (w t))
      (z ⟨t, htt⟩).2, C.diffusion_eval t ⟨htt.1, htt.2.trans hT⟩]
    rw [map_add, ← hu₀]
    congr 1
    funext i
    cases i with
    | none => simp only [zero_add, scalarH1TimeCoordinate_eval_none]
    | some i =>
      simp only [scalarH1TimeCoordinate_eval_some, PiLp.add_apply]

private theorem scalarVectorTimeCoefficients_reaction_higher_order
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (j : Fin n)
    (hF : ContDiffOn ℝ ∞ (fun z => G z j) S) (hS : IsOpen S) (k : ℕ)
    (T : ℝ) (hT : T ≤ C.radius)
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (field : timeL2
      (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T)
    (w : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hw : ContinuousOn w (Icc 0 T))
    (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1))
    (ha : AEStronglyMeasurable a (timeMeasure T)) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    u₀ = J (K f₀) →
    w =ᵐ[timeMeasure T] (fun t => K (field t)) →
    (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
    (fun t => A (a t)) =ᵐ[timeMeasure T]
      (fun t => extendClosedBall C.radius_pos.le C.reaction t (J (w t)) j) →
    ∃ aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T,
      (fun t => tensorHsInclusion (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
        (aHigh t)) =ᵐ[timeMeasure T] a := by
  classical
  intro K L J A hu₀ hwu hbound hactual
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) C.radius := fun t =>
    ⟨J (w t), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  apply AddCircle.exists_timeL2_scalarHs_composition_firstJet g₀ k T f₀ field w hw
    (fun z => G z j) hF hS a ha hwu
  · intro t ht
    have h := C.range_mem t ⟨ht.1, ht.2.trans hT⟩ (J (w t)) (z ⟨t, ht⟩).2
    change range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t)))) ⊆ S
    rw [map_add, ← hu₀]
    simpa only [zero_add] using h
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht, hactual] with t htt hat
    intro x
    change scalarH1ToContinuous g₀ (A (a t)) x =
      (fun z => G z j) (scalarH1PiToContinuous g₀
        (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))) x)
    rw [hat, extendClosedBall_apply C.radius_pos.le C.reaction t (J (w t))
      (z ⟨t, htt⟩).2, C.reaction_eval t ⟨htt.1, htt.2.trans hT⟩]
    rw [map_add, ← hu₀]
    congr 1
    funext i
    cases i with
    | none => simp only [zero_add, scalarH1TimeCoordinate_eval_none]
    | some i =>
      simp only [scalarH1TimeCoordinate_eval_some, PiLp.add_apply]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambientFirstJet_eq_initialJet
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e) :
    let g₀ := c₀.pullbackMetric g
    let f₀ := ambientSobolev c₀ g e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ambientFirstJet c₀ g e he = J (K f₀) := by
  intro g₀ f₀ J K
  change circleFirstJet g₀ _ = circleFirstJet g₀ _
  congr 1
  apply PiLp.ext
  intro i
  change ccTensorToHs g₀ 0 (1 + 1) (ambientCoordinateCc c₀ g e he i) =
    tensorHsCongrL g₀ 0 0
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)
      (tensorHsInclusion
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (ccTensorToHs g₀ 0 (((1 : ℕ) : ℝ) + 2) (ambientCoordinateCc c₀ g e he i)))
  rw [tensorHsInclusion_ccTensorToHs, tensorHsCongrL_ccTensorToHs]

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambientFirstJet_eq_higher_initialJet
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (k : ℕ) :
    let g₀ := c₀.pullbackMetric g
    let f₀ := ambientSobolev c₀ g e he (((k + 2 : ℕ) : ℝ) + 1)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    ambientFirstJet c₀ g e he = J (K f₀) := by
  intro g₀ f₀ K L J
  apply PiLp.ext
  intro j
  cases j with
  | inl i =>
    change tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 1 + 1)
      (ccTensorToHs g₀ 0 (1 + 1) (ambientCoordinateCc c₀ g e he i)) =
      tensorHsInclusion
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
        (tensorHsInclusion (by linarith : ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1)
          (tensorHsInclusion
            (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1)
        (ccTensorToHs g₀ 0 (((k + 2 : ℕ) : ℝ) + 1) (ambientCoordinateCc c₀ g e he i))))
    simp only [tensorHsInclusion_ccTensorToHs]
  | inr i =>
    change circleDerivativeH1 g₀
      (ccTensorToHs g₀ 0 (1 + 1) (ambientCoordinateCc c₀ g e he i)) =
      tensorHsInclusion
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
        (AddCircle.parameterDerivativeHs g₀ (k + 1)
          (tensorHsInclusion
            (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1)
            (ccTensorToHs g₀ 0 (((k + 2 : ℕ) : ℝ) + 1)
          (ambientCoordinateCc c₀ g e he i))))
    simp only [circleDerivativeH1, ContinuousLinearMap.comp_apply,
      tensorHsInclusion_ccTensorToHs, tensorHsCongrL_ccTensorToHs,
      AddCircle.parameterDerivativeHs_apply_ccTensorToHs]

private theorem ambient_diffusion_higher_order
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    (k : ℕ) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    ∀ T : ℝ, T ≤ C.radius →
      ∀ field : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T,
      ∀ w : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)),
      ContinuousOn w (Icc 0 T) →
      ∀ a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1),
      AEStronglyMeasurable a (timeMeasure T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
      (fun t => A (a t)) =ᵐ[timeMeasure T]
        (fun t => extendClosedBall C.radius_pos.le C.diffusion t (J (w t))) →
      ∃ aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T,
        (fun t => tensorHsInclusion (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
          (aHigh t)) =ᵐ[timeMeasure T] a := by
  intro C g₀ K L J A T hT field w hw a ha hwu hbound hactual
  let f₀ := ambientSobolev c₀ (g 0) e he (((k + 2 : ℕ) : ℝ) + 1)
  obtain ⟨hS, hF, _⟩ := geometric_coefficients_contDiffOn hG β
  exact scalarVectorTimeCoefficients_diffusion_higher_order g₀ _ _ _ _ C
    hF hS k T hT f₀ field w hw a ha
    (ambientFirstJet_eq_higher_initialJet c₀ (g 0) he k) hwu hbound hactual

private theorem ambient_reaction_higher_order
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    (j : Fin n) (k : ℕ) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    ∀ T : ℝ, T ≤ C.radius →
      ∀ field : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T,
      ∀ w : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)),
      ContinuousOn w (Icc 0 T) →
      ∀ a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1),
      AEStronglyMeasurable a (timeMeasure T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
      (fun t => A (a t)) =ᵐ[timeMeasure T]
        (fun t => extendClosedBall C.radius_pos.le C.reaction t (J (w t)) j) →
      ∃ aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T,
        (fun t => tensorHsInclusion (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
          (aHigh t)) =ᵐ[timeMeasure T] a := by
  intro C g₀ K L J A T hT field w hw a ha hwu hbound hactual
  let f₀ := ambientSobolev c₀ (g 0) e he (((k + 2 : ℕ) : ℝ) + 1)
  obtain ⟨hS, _, hG'⟩ := geometric_coefficients_contDiffOn hG β
  exact scalarVectorTimeCoefficients_reaction_higher_order g₀ _ _ _ _ C j
    (contDiffOn_pi.mp hG' j) hS k T hT f₀ field w hw a ha
    (ambientFirstJet_eq_higher_initialJet c₀ (g 0) he k) hwu hbound hactual

private theorem ambient_diffusion_h2
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∀ T : ℝ, T ≤ C.radius →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 2) T,
        (fun t => tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))) := by
  intro C g₀ J K T hT field w hw hwu hbound
  let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
  obtain ⟨hS, hF, _⟩ := geometric_coefficients_contDiffOn hG β
  obtain ⟨a₂, ha₂⟩ := scalarVectorTimeCoefficients_diffusion_h2 g₀ _ _ _ _ C
    hF hS T hT f₀ field w hw (ambientFirstJet_eq_initialJet c₀ (g 0) he) hwu hbound
  refine ⟨a₂, ?_⟩
  filter_upwards [ha₂] with t htt
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  have hc : tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =
      tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (a₂ t) := by
    apply TensorHs.ext
    rw [hcongr]
    rfl
  rw [← hc, htt]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Geometry.Curvature
variable {ι : Type*} [Fintype ι]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem circle_timeCoordinate_firstJet_h3_projection
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (t : ℝ) (v : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) :
    let E := (circleHsPiCongr g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let J := (circleFirstJet (ι := ι) g).comp
      (circleHsPiCongr g ι
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ 2))
      (AddCircle.scalarHsTimeCoordinate g 2 (t, AddCircle.firstJetHs g 2 (E v))) =
      scalarH1TimeCoordinate g (t, J (K v)) := by
  intro E J K
  have hcongr {a b : ℝ} (h : a = b) (z : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 h z).coeff = z.coeff := by
    cases h
    rfl
  rw [AddCircle.tensorHsInclusion_scalarHsTimeCoordinate]
  congr 1
  apply Prod.ext
  · rfl
  · let K₂ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    have hK₂ : K₂ (E v) = K v := by
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      change (tensorHsCongrL g 0 0
        (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1) (v i)).coeff = (v i).coeff
      rw [hcongr]
    have hjet := congrArg (fun A => A (E v))
      (AddCircle.firstJetHs_comp_tensorHsInclusion (ι := ι) g (by decide : 1 ≤ 2))
    change AddCircle.firstJetHs g 1 (K₂ (E v)) = _ at hjet
    rw [hK₂] at hjet
    have hnormalized : J (K v) = L (AddCircle.firstJetHs g 1 (K v)) :=
      circle_firstJetHs_normalized g (K v)
    rw [hnormalized, hjet]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl

private theorem continuousOn_circle_timeCoordinate_firstJet_h3
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (f₀ : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (W : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T)) :
    let E := (circleHsPiCongr g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    ContinuousOn (fun t => AddCircle.scalarHsTimeCoordinate g 2
      (t, AddCircle.firstJetHs g 2 (E (f₀ + W t)))) (Icc 0 T) := by
  intro E
  exact (AddCircle.scalarHsTimeCoordinate g 2).continuous.comp_continuousOn
    (continuousOn_id.prodMk ((AddCircle.firstJetHs g 2).continuous.comp_continuousOn
      (E.continuous.comp_continuousOn (continuousOn_const.add hW))))

private theorem circle_exists_continuousOn_h2_composition_of_h3
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (f₀ : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (W : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {S : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (a : ℝ → TensorHs g 0 0 1) :
    let J := (circleFirstJet (ι := ι) g).comp
      (circleHsPiCongr g ι
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let q := fun t => scalarH1TimeCoordinate g (t, J (K (f₀ + W t)))
    (∀ t ∈ Icc 0 T, range (scalarH1PiToContinuous g (q t)) ⊆ S) →
    (∀ t ∈ Icc 0 T, ∀ x, scalarH1ToContinuous g (a t) x =
      F (scalarH1PiToContinuous g (q t) x)) →
    ∃ a₂ : ℝ → TensorHs g 0 0 2, ContinuousOn a₂ (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t) = a t := by
  intro J K q hRange hEval
  let E := (circleHsPiCongr g ι
    (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let V := fun t => AddCircle.scalarHsTimeCoordinate g 2
    (t, AddCircle.firstJetHs g 2 (E (f₀ + W t)))
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
    tensorHsInclusion (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2))
  have hV : ContinuousOn V (Icc 0 T) :=
    continuousOn_circle_timeCoordinate_firstJet_h3 g f₀ W hW
  have hq (t : ℝ) : P (V t) = q t :=
    circle_timeCoordinate_firstJet_h3_projection g t (f₀ + W t)
  have hRangeV (t : ℝ) (ht : t ∈ Icc 0 T) :
      range (scalarH1PiToContinuous g (P (V t))) ⊆ S := by
    rw [hq]
    exact hRange t ht
  obtain ⟨a₂, ha₂, hEval₂⟩ :=
    AddCircle.exists_continuousOn_scalarH2_composition g F hF hS V hV hRangeV
  refine ⟨a₂, ha₂, ?_⟩
  intro t ht
  apply scalarH1ToContinuous_injective g
  apply ContinuousMap.ext
  intro x
  exact (hEval₂ t ht x).trans (by rw [hq]; exact (hEval t ht x).symm)

private theorem scalarVectorTimeCoefficients_continuousOn_h2
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    {T : ℝ} (hT : T ≤ (ScalarVectorTimeCoefficients.radius C))
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T)) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    u₀ = J (K f₀) →
    (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
    ∃ (a₂ : ℝ → TensorHs g₀ 0 0 2)
      (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)),
      ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t)))) ∧
      (∀ t ∈ Icc 0 T, (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2))) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t)))) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, ‖a₂ t‖ + ‖b₂ t‖ ≤ B := by
  classical
  intro J K hu₀ hbound
  let q := fun t => scalarH1TimeCoordinate g₀ (t, J (K (f₀ + W t)))
  let a := fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t)))
  let b := fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t)))
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) (ScalarVectorTimeCoefficients.radius C) := fun t =>
    ⟨J (K (W t)), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  have hRange (t : ℝ) (ht : t ∈ Icc 0 T) :
      range (scalarH1PiToContinuous g₀ (q t)) ⊆ S := by
    have h := (ScalarVectorTimeCoefficients.range_mem C) t ⟨ht.1, ht.2.trans hT⟩ (J (K (W t))) (z ⟨t, ht⟩).2
    change range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, J (K (f₀ + W t))))) ⊆ S
    rw [map_add, map_add, ← hu₀]
    simpa only [zero_add] using h
  have hcoord (t : ℝ) (x : AddCircle (1 : ℝ)) :
      (fun i : Option (Fin n ⊕ Fin n) => match i with
        | none => 0 + t
        | some j => scalarH1ToContinuous g₀ (u₀ j + J (K (W t)) j) x) =
      scalarH1PiToContinuous g₀ (q t) x := by
    funext i
    cases i with
    | none => simp only [q, scalarH1TimeCoordinate_eval_none, zero_add]
    | some j =>
      simp only [q, map_add, ← hu₀, scalarH1TimeCoordinate_eval_some, PiLp.add_apply]
  have haEval (t : ℝ) (ht : t ∈ Icc 0 T) (x : AddCircle (1 : ℝ)) :
      scalarH1ToContinuous g₀ (a t) x = F (scalarH1PiToContinuous g₀ (q t) x) := by
    rw [show a t = (ScalarVectorTimeCoefficients.diffusion C) t (z ⟨t, ht⟩) from
      extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))) (z ⟨t, ht⟩).2]
    rw [(ScalarVectorTimeCoefficients.diffusion_eval C) t ⟨ht.1, ht.2.trans hT⟩]
    congr 1
    funext i
    exact congrFun (hcoord t x) i
  have hbEval (j : Fin n) (t : ℝ) (ht : t ∈ Icc 0 T) (x : AddCircle (1 : ℝ)) :
      scalarH1ToContinuous g₀ (b t j) x = G (scalarH1PiToContinuous g₀ (q t) x) j := by
    rw [show b t = (ScalarVectorTimeCoefficients.reaction C) t (z ⟨t, ht⟩) from
      extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))) (z ⟨t, ht⟩).2]
    rw [(ScalarVectorTimeCoefficients.reaction_eval C) t ⟨ht.1, ht.2.trans hT⟩]
    congr 2
    funext i
    exact congrFun (hcoord t x) i
  obtain ⟨a₂, ha₂, ha₂eq⟩ := circle_exists_continuousOn_h2_composition_of_h3
    g₀ f₀ W hW F hF hS a hRange haEval
  choose b₂j hb₂j hb₂jeq using fun j : Fin n =>
    circle_exists_continuousOn_h2_composition_of_h3 g₀ f₀ W hW
      (fun y => G y j) (contDiffOn_pi.mp hG j) hS (fun t => b t j) hRange (hbEval j)
  let b₂ := fun t => WithLp.toLp 2 (fun j => b₂j j t)
  have hb₂ : ContinuousOn b₂ (Icc 0 T) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr hb₂j)
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn ha₂
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hb₂
  refine ⟨a₂, b₂, ha₂, hb₂, ha₂eq, ?_, max 0 (A + B), le_max_left _ _, ?_⟩
  · intro t ht
    apply PiLp.ext
    intro j
    exact hb₂jeq j t ht
  · intro t ht
    exact (add_le_add (hA t ht) (hB t ht)).trans (le_max_right _ _)

private theorem ambient_coefficients_continuousOn_h2
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {n : ℕ}
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {T : ℝ}
    (W : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    T ≤ ScalarVectorTimeCoefficients.radius C →
    (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C) →
    let alpha := fun t => tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))
    let reaction := fun t => circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))
    ∃ (a₂ : ℝ → TensorHs g₀ 0 0 2)
      (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)),
      ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (a₂ t) = alpha t) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (b₂ t) = reaction t) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, ‖a₂ t‖ + ‖b₂ t‖ ≤ B := by
  intro C g₀ J K hT hbound alpha reaction
  have hcongr {a b : ℝ} (h : a = b) (z : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 h z).coeff = z.coeff := by
    cases h
    rfl
  let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
  obtain ⟨hS, hF, hReaction⟩ := geometric_coefficients_contDiffOn hG β
  obtain ⟨a₂, b₂, ha₂, hb₂, haeq, hbeq, B, hB, hbound₂⟩ :=
    scalarVectorTimeCoefficients_continuousOn_h2 g₀ _ _ _ _ C
      hF hReaction hS hT f₀ W hW
      (ambientFirstJet_eq_initialJet c₀ (g 0) he) hbound
  refine ⟨a₂, b₂, ha₂, hb₂, ?_, ?_, B, hB, hbound₂⟩
  · intro t htt
    have h := congrArg (tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))) (haeq t htt)
    refine Eq.trans ?_ h
    apply TensorHs.ext
    rw [hcongr]
    rfl
  · intro t htt
    have h := congrArg (circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))) (hbeq t htt)
    refine Eq.trans ?_ h
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    simp only [circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
      circleHsPiCongr_apply, hcongr, tensorHsInclusion_coeff]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {ι : Type*} [Fintype ι]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem circle_timeL2_h2_composition_norm_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2))
    (F : (Option (ι ⊕ ι) → ℝ) → ℝ) {S Krange : Set (Option (ι ⊕ ι) → ℝ)}
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (hK : IsCompact Krange) (hKS : Krange ⊆ S) (R : ℝ) :
    let J := (circleFirstJet (ι := ι) g).comp
      (circleHsPiCongr g ι
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g ι
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T ≤ 1 →
      ∀ u : timeL2 (CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g ι (((1 : ℕ) : ℝ) + 1),
      let q := fun t => scalarH1TimeCoordinate g (t, J (K f₀ + w t))
      ∀ a : ℝ → TensorHs g 0 0 1, AEStronglyMeasurable a (timeMeasure T) →
      w =ᵐ[timeMeasure T] (fun t => K (u t)) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g (q t)) ⊆ Krange) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖q t i‖) ≤ R) →
      (∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (a t) x =
        F (scalarH1PiToContinuous g (q t) x)) →
      ∃ a₂ : timeL2 (TensorHs g 0 0 2) T,
        (fun t => tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T] a ∧
        ‖a₂‖ ≤ C * (Real.sqrt T + ‖u‖) := by
  intro J K
  let E := (circleHsPiCongr g ι
    (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  obtain ⟨C, hC, hc⟩ := AddCircle.exists_timeL2_scalarH2_composition_firstJet_norm_le
    g (E f₀) F hF hS hK hKS R
  refine ⟨C, hC, ?_⟩
  intro T hT u w q a ha hwu hRange hBound hEval
  let u₂ := E.compLpL 2 (timeMeasure T) u
  let K₂ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1))
  let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (2 : ℝ) ≤ ((2 : ℕ) : ℝ)))
  let V := fun t z => P (AddCircle.scalarHsTimeCoordinate g ((2 : ℕ) : ℝ)
    (t, AddCircle.firstJetHs g 2 z))
  let Q := ContinuousLinearMap.piLpMap 2 (fun _ : Option (ι ⊕ ι) =>
    tensorHsInclusion (g := g) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2))
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  have hK₂ (v : CircleHsPi g ι (((1 : ℕ) : ℝ) + 2)) : K₂ (E v) = K v := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    change (tensorHsCongrL g 0 0
      (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1) (v i)).coeff = (v i).coeff
    rw [hcongr]
  have hw₂ : w =ᵐ[timeMeasure T] (fun t => K₂ (u₂ t)) := by
    filter_upwards [hwu, E.coeFn_compLpL (p := 2) (μ := timeMeasure T) u] with t ht he
    change u₂ t = E (u t) at he
    rw [he, hK₂]
    exact ht
  have hq (t : ℝ) :
      scalarH1TimeCoordinate g (t, L (AddCircle.firstJetHs g 1 (K₂ (E f₀) + w t))) = q t := by
    rw [hK₂, ← circle_firstJetHs_normalized]
    rfl
  have hproject := AddCircle.scalarHsTimeCoordinate_firstJetHs_ae_eq
    g (by decide : 1 ≤ 2) T (E f₀) u₂ w hw₂
  have hqv : (fun t => Q (V t (E f₀ + u₂ t))) =ᵐ[timeMeasure T] q := by
    filter_upwards [hproject] with t ht
    rw [← hq]
    refine Eq.trans ?_ ht
    apply PiLp.ext
    intro j
    apply TensorHs.ext
    rfl
  have hrange : ∀ᵐ t ∂timeMeasure T,
      range (scalarH1PiToContinuous g (Q (V t (E f₀ + u₂ t)))) ⊆ Krange := by
    filter_upwards [hRange, hqv] with t ht he
    rwa [he]
  have hbound : ∀ᵐ t ∂timeMeasure T, (∑ i, ‖Q (V t (E f₀ + u₂ t)) i‖) ≤ R := by
    filter_upwards [hBound, hqv] with t ht he
    rwa [he]
  have heval : ∀ᵐ t ∂timeMeasure T, ∀ x, scalarH1ToContinuous g (a t) x =
      F (scalarH1PiToContinuous g (Q (V t (E f₀ + u₂ t))) x) := by
    filter_upwards [hEval, hqv] with t ht he
    rwa [he]
  obtain ⟨a₂, ha₂, hnorm⟩ := hc T hT u₂ a ha hrange hbound heval
  refine ⟨a₂, ha₂, hnorm.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  apply add_le_add le_rfl
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [E.coeFn_compLpL (p := 2) (μ := timeMeasure T) u] with t ht
  change u₂ t = E (u t) at ht
  rw [ht]
  exact (circleHsPiCongr g ι
    (by norm_num : ((1 : ℕ) : ℝ) + 2 = ((2 : ℕ) : ℝ) + 1)).norm_map (u t) |>.le

end DifferentialGeometry.Analysis.Parabolic
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Geometry.Curvature

variable {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalarVectorTimeCoefficients_diffusion_h2_norm_le
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hS : IsOpen S)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {Krange : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hK : IsCompact Krange) (hKS : Krange ⊆ S) (R : ℝ) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T ≤ 1 → T ≤ C.radius →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let q := fun t => scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))
      ContinuousOn w (Icc 0 T) →
      u₀ = J (K f₀) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g₀ (q t)) ⊆ Krange) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖q t i‖) ≤ R) →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 2) T,
        (fun t => tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => extendClosedBall C.radius_pos.le C.diffusion t (J (w t))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + ‖field‖) := by
  classical
  intro J K
  obtain ⟨A, hA, ha₂⟩ := circle_timeL2_h2_composition_norm_le g₀ f₀ F hF hS hK hKS R
  refine ⟨A, hA, ?_⟩
  intro T hT1 hT field w q hw hu₀ hwu hbound hRange hBound
  let a := fun t => extendClosedBall C.radius_pos.le C.diffusion t (J (w t))
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) C.radius := fun t =>
    ⟨J (w t), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  have hz : Continuous z :=
    (J.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hw)).subtype_mk _
  have he (t : Icc (0 : ℝ) T) : a t = C.diffusion t (z t) :=
    extendClosedBall_apply C.radius_pos.le C.diffusion t (J (w t)) (z t).2
  have ha : ContinuousOn a (Icc 0 T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply (C.diffusion_lipschitz.continuous.comp (continuous_subtype_val.prodMk hz)).congr
    intro t
    exact (he t).symm
  apply ha₂ T hT1 field w a (memLp_of_continuousOn ha).aestronglyMeasurable
    hwu hRange hBound
  have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  filter_upwards [ht] with t htt
  intro x
  change scalarH1ToContinuous g₀ (a t) x = F
    (scalarH1PiToContinuous g₀ (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))) x)
  rw [map_add, ← hu₀, he ⟨t, htt⟩, C.diffusion_eval t ⟨htt.1, htt.2.trans hT⟩]
  congr 1
  funext i
  cases i with
  | none => simp only [zero_add, scalarH1TimeCoordinate_eval_none]
  | some i =>
    simp only [scalarH1TimeCoordinate_eval_some, PiLp.add_apply]
    rfl

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem ambient_diffusion_h2_norm_le
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {Krange : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hK : IsCompact Krange)
    (hKS : Krange ⊆ firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β) (R : ℝ) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T ≤ 1 → T ≤ C.radius →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let q := fun t => scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g₀ (q t)) ⊆ Krange) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖q t i‖) ≤ R) →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 2) T,
        (fun t => tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + ‖field‖) := by
  intro C g₀ f₀ J K
  obtain ⟨hS, hF, _⟩ := geometric_coefficients_contDiffOn hG β
  obtain ⟨A, hA, ha₂⟩ := scalarVectorTimeCoefficients_diffusion_h2_norm_le g₀ _ _ _ _ C
    hF hS f₀ hK hKS R
  refine ⟨A, hA, ?_⟩
  intro T hT1 hT field w q hw hwu hbound hRange hBound
  obtain ⟨a₂, hproject, hnorm⟩ := ha₂ T hT1 hT field w hw
    (ambientFirstJet_eq_initialJet c₀ (g 0) he) hwu hbound hRange hBound
  refine ⟨a₂, ?_, hnorm⟩
  filter_upwards [hproject] with t htt
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  have hc : tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =
      tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (a₂ t) := by
    apply TensorHs.ext
    rw [hcongr]
    rfl
  rw [← hc, htt]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem ambient_firstJet_bounds_on_closedBall
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let q := fun t v => scalarH1TimeCoordinate g₀ (t, J (K f₀ + v))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ C.radius ∧ δ ≤ 1 ∧ ‖J‖ * δ ≤ C.radius ∧
      ∃ Krange : Set (Option (Fin n ⊕ Fin n) → ℝ), IsCompact Krange ∧
        Krange ⊆ firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
          (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∧
        ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) δ,
          ∀ v : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1), ‖v‖ ≤ δ →
            range (scalarH1PiToContinuous g₀ (q t v)) ⊆ Krange ∧
              (∑ i, ‖q t v i‖) ≤ R := by
  intro C g₀ f₀ J K q
  let q₀ := scalarH1TimeCoordinate g₀ (0, J (K f₀))
  have hbase := ambientFirstJet_range c₀ g ht he hr hEU hleft β
  rw [ambientFirstJet_eq_initialJet c₀ (g 0) he] at hbase
  obtain ⟨hS, _, _⟩ := geometric_coefficients_contDiffOn hG β
  obtain ⟨η, hη, Krange, hK, hKS, hrange⟩ :=
    exists_scalarH1Pi_ball_range_subset g₀ q₀ hS hbase
  let X := CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)
  let B : ℝ × X →L[ℝ] PiLp 2 (fun _ : Option (Fin n ⊕ Fin n) => TensorHs g₀ 0 0 1) :=
    (scalarH1TimeCoordinate g₀).comp
      ((ContinuousLinearMap.fst ℝ ℝ X).prod (J.comp (ContinuousLinearMap.snd ℝ ℝ X)))
  obtain ⟨δJ, hδJ, hδJC, hJ⟩ := J.exists_pos_norm_mul_le C.radius_pos
  obtain ⟨δB, hδB, _, hB⟩ := B.exists_pos_norm_mul_le (half_pos hη)
  let δ := min δJ (min δB 1)
  have hδ : 0 < δ := lt_min hδJ (lt_min hδB zero_lt_one)
  have hδJle : δ ≤ δJ := min_le_left _ _
  have hδBle : δ ≤ δB := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  let R := (Fintype.card (Option (Fin n ⊕ Fin n)) : ℝ) * (‖q₀‖ + η)
  have hR : 0 ≤ R := mul_nonneg (Nat.cast_nonneg _) (by positivity)
  refine ⟨δ, hδ, hδJle.trans hδJC, hδ1,
    (mul_le_mul_of_nonneg_left hδJle (norm_nonneg J)).trans hJ,
    Krange, hK, hKS, R, hR, ?_⟩
  intro t ht v hv
  have hp : ‖(t, v)‖ ≤ δ := by
    rw [Prod.norm_def]
    apply max_le
    · simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
    · exact hv
  have hpert : ‖B (t, v)‖ < η := by
    calc
      _ ≤ ‖B‖ * ‖(t, v)‖ := B.le_opNorm _
      _ ≤ ‖B‖ * δB := mul_le_mul_of_nonneg_left (hp.trans hδBle) (norm_nonneg B)
      _ ≤ η / 2 := hB
      _ < η := half_lt_self hη
  have hq : q t v = q₀ + B (t, v) := by
    change scalarH1TimeCoordinate g₀ (t, J (K f₀ + v)) =
      scalarH1TimeCoordinate g₀ (0, J (K f₀)) + scalarH1TimeCoordinate g₀ (t, J v)
    rw [← map_add]
    congr 1
    simp only [Prod.mk_add_mk, zero_add, map_add]
  have hmem : q t v ∈ Metric.ball q₀ η := by
    rw [Metric.mem_ball, dist_eq_norm, hq, add_sub_cancel_left]
    exact hpert
  refine ⟨hrange _ hmem, ?_⟩
  have hnorm : ‖q t v‖ ≤ ‖q₀‖ + η := by
    rw [hq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hpert.le)
  calc
    _ ≤ ∑ _i : Option (Fin n ⊕ Fin n), ‖q t v‖ :=
      Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
    _ = (Fintype.card (Option (Fin n ⊕ Fin n)) : ℝ) * ‖q t v‖ := by simp
    _ ≤ R := mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem ambient_diffusion_h2_norm_le_of_small_state
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ C.radius ∧ δ ≤ 1 ∧ ∃ A : ℝ, 0 ≤ A ∧
      ∀ T : ℝ, T ≤ δ →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ δ) →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 2) T,
        (fun t => tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + ‖field‖) := by
  intro C g₀ J K
  obtain ⟨δ, hδ, hδC, hδ1, hJδ, Krange, hK, hKS, R, _, hb⟩ :=
    ambient_firstJet_bounds_on_closedBall c₀ g ht he hr hEU hleft β hG
  obtain ⟨A, hA, ha₂⟩ := ambient_diffusion_h2_norm_le c₀ g ht he hr hEU hleft β hG
    hK hKS R
  refine ⟨δ, hδ, hδC, hδ1, A, hA, ?_⟩
  intro T hT field w hw hwu hbound
  change ‖J‖ * δ ≤ C.radius at hJδ
  have hJw : ∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius := by
    intro t htt
    calc
      ‖J (w t)‖ ≤ ‖J‖ * ‖w t‖ := J.le_opNorm _
      _ ≤ ‖J‖ * δ := mul_le_mul_of_nonneg_left (hbound t htt) (norm_nonneg J)
      _ ≤ C.radius := hJδ
  apply ha₂ T (hT.trans hδ1) (hT.trans hδC) field w hw hwu hJw
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t htt
    exact (hb t ⟨htt.1, htt.2.trans hT⟩ (w t) (hbound t htt)).1
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t htt
    exact (hb t ⟨htt.1, htt.2.trans hT⟩ (w t) (hbound t htt)).2

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Geometry.Curvature

variable {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalarVectorTimeCoefficients_reaction_h2_norm_le
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    {Krange : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hK : IsCompact Krange) (hKS : Krange ⊆ S) (R : ℝ) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T ≤ 1 → T ≤ C.radius →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let q := fun t => scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))
      ContinuousOn w (Icc 0 T) →
      u₀ = J (K f₀) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g₀ (q t)) ⊆ Krange) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖q t i‖) ≤ R) →
      ∃ b₂ : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)) T,
        (fun t => (ContinuousLinearMap.piLpMap 2 fun _ : Fin n =>
          tensorHsInclusion (g := g₀) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ 2)) (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => extendClosedBall C.radius_pos.le C.reaction t (J (w t))) ∧
        ‖b₂‖ ≤ A * (Real.sqrt T + ‖field‖) := by
  classical
  intro J K
  choose A hA hc using fun j : Fin n =>
    circle_timeL2_h2_composition_norm_le g₀ f₀ (fun z => G z j)
      (contDiffOn_pi.mp hG j) hS hK hKS R
  refine ⟨∑ j, A j, Finset.sum_nonneg (fun j _ => hA j), ?_⟩
  intro T hT1 hT field w q hw hu₀ hwu hbound hRange hBound
  let b := fun t => extendClosedBall C.radius_pos.le C.reaction t (J (w t))
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) C.radius := fun t =>
    ⟨J (w t), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  have hz : Continuous z :=
    (J.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hw)).subtype_mk _
  have he (t : Icc (0 : ℝ) T) : b t = C.reaction t (z t) :=
    extendClosedBall_apply C.radius_pos.le C.reaction t (J (w t)) (z t).2
  have hb : ContinuousOn b (Icc 0 T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply (C.reaction_lipschitz.continuous.comp (continuous_subtype_val.prodMk hz)).congr
    intro t
    exact (he t).symm
  have heval (j : Fin n) : ∀ᵐ t ∂timeMeasure T, ∀ x,
      scalarH1ToContinuous g₀ (b t j) x = G (scalarH1PiToContinuous g₀ (q t) x) j := by
    have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t htt
    intro x
    change scalarH1ToContinuous g₀ (b t j) x = G
      (scalarH1PiToContinuous g₀ (scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))) x) j
    rw [map_add, ← hu₀, he ⟨t, htt⟩, C.reaction_eval t ⟨htt.1, htt.2.trans hT⟩]
    congr 2
    funext i
    cases i with
    | none => simp only [zero_add, scalarH1TimeCoordinate_eval_none]
    | some i =>
      simp only [scalarH1TimeCoordinate_eval_some, PiLp.add_apply]
      rfl
  have hj (j : Fin n) := hc j T hT1 field w (fun t => b t j)
    (memLp_of_continuousOn ((PiLp.continuous_apply 2 (fun _ : Fin n => TensorHs g₀ 0 0 1) j).comp_continuousOn hb)).aestronglyMeasurable
    hwu hRange hBound (heval j)
  choose v hv hvnorm using hj
  let e₂ := Lp.piLpEquiv (𝕜 := ℝ)
    (X := fun _ : Fin n => TensorHs g₀ 0 0 2) (timeMeasure T)
  let vpi : PiLp 2 (fun _ : Fin n => timeL2 (TensorHs g₀ 0 0 2) T) := WithLp.toLp 2 v
  let b₂ := e₂.symm vpi
  have hb₂ : ∀ᵐ t ∂timeMeasure T, ∀ j, b₂ t j = v j t := by
    filter_upwards [Lp.piLpEquiv_symm_apply (𝕜 := ℝ) (timeMeasure T) vpi] with t ht
    intro j
    exact congrArg (fun z : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2) => z j) ht
  have hb₂norm : ‖b₂‖ ≤ ∑ j, ‖v j‖ := by
    change ‖e₂.symm vpi‖ ≤ _
    rw [e₂.symm.norm_map]
    have hs : vpi = ∑ j, PiLp.single 2 j (v j) := by
      apply PiLp.ext
      intro j
      simp [vpi]
    rw [hs]
    simpa only [PiLp.norm_single] using norm_sum_le Finset.univ
      (fun j : Fin n => (PiLp.single 2 j (v j) :
        PiLp 2 (fun _ : Fin n => timeL2 (TensorHs g₀ 0 0 2) T)))
  refine ⟨b₂, ?_, hb₂norm.trans ?_⟩
  · filter_upwards [hb₂, Filter.eventually_all.mpr hv] with t ht hvt
    apply PiLp.ext
    intro j
    change tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (b₂ t j) = b t j
    rw [ht j]
    exact hvt j
  · calc
      ∑ j, ‖v j‖ ≤ ∑ j, A j * (Real.sqrt T + ‖field‖) :=
        Finset.sum_le_sum (fun j _ => hvnorm j)
      _ = (∑ j, A j) * (Real.sqrt T + ‖field‖) := (Finset.sum_mul _ _ _).symm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem ambient_reaction_h2_norm_le
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {Krange : Set (Option (Fin n ⊕ Fin n) → ℝ)}
    (hK : IsCompact Krange)
    (hKS : Krange ⊆ firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β) (R : ℝ) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T ≤ 1 → T ≤ C.radius →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let q := fun t => scalarH1TimeCoordinate g₀ (t, J (K f₀ + w t))
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
      (∀ᵐ t ∂timeMeasure T, range (scalarH1PiToContinuous g₀ (q t)) ⊆ Krange) →
      (∀ᵐ t ∂timeMeasure T, (∑ i, ‖q t i‖) ≤ R) →
      ∃ b₂ : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)) T,
        (fun t => (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)) (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))) ∧
        ‖b₂‖ ≤ A * (Real.sqrt T + ‖field‖) := by
  intro C g₀ f₀ J K
  obtain ⟨hS, _, hReaction⟩ := geometric_coefficients_contDiffOn hG β
  obtain ⟨A, hA, hb₂⟩ := scalarVectorTimeCoefficients_reaction_h2_norm_le g₀ _ _ _ _ C
    hReaction hS f₀ hK hKS R
  refine ⟨A, hA, ?_⟩
  intro T hT1 hT field w q hw hwu hbound hRange hBound
  obtain ⟨b₂, hproject, hnorm⟩ := hb₂ T hT1 hT field w hw
    (ambientFirstJet_eq_initialJet c₀ (g 0) he) hwu hbound hRange hBound
  refine ⟨b₂, ?_, hnorm⟩
  filter_upwards [hproject] with t htt
  have hcongr {a b : ℝ} (h : a = b) (v : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 h v).coeff = v.coeff := by
    cases h
    rfl
  apply PiLp.ext
  intro j
  have hp := congrArg (fun v : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1) => v j) htt
  change tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (b₂ t j) =
    extendClosedBall C.radius_pos.le C.reaction t (J (w t)) j at hp
  change tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ 2) (b₂ t j) =
    tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (extendClosedBall C.radius_pos.le C.reaction t (J (w t)) j)
  apply TensorHs.ext
  rw [hcongr, ← hp]
  rfl

private theorem ambient_reaction_h2_norm_le_of_small_state
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ C.radius ∧ δ ≤ 1 ∧ ∃ A : ℝ, 0 ≤ A ∧
      ∀ T : ℝ, T ≤ δ →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ δ) →
      ∃ b₂ : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)) T,
        (fun t => (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)) (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))) ∧
        ‖b₂‖ ≤ A * (Real.sqrt T + ‖field‖) := by
  intro C g₀ J K
  obtain ⟨δ, hδ, hδC, hδ1, hJδ, Krange, hK, hKS, R, _, hb⟩ :=
    ambient_firstJet_bounds_on_closedBall c₀ g ht he hr hEU hleft β hG
  obtain ⟨A, hA, hb₂⟩ := ambient_reaction_h2_norm_le c₀ g ht he hr hEU hleft β hG
    hK hKS R
  refine ⟨δ, hδ, hδC, hδ1, A, hA, ?_⟩
  intro T hT field w hw hwu hbound
  change ‖J‖ * δ ≤ C.radius at hJδ
  have hJw : ∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius := by
    intro t htt
    calc
      ‖J (w t)‖ ≤ ‖J‖ * ‖w t‖ := J.le_opNorm _
      _ ≤ ‖J‖ * δ := mul_le_mul_of_nonneg_left (hbound t htt) (norm_nonneg J)
      _ ≤ C.radius := hJδ
  apply hb₂ T (hT.trans hδ1) (hT.trans hδC) field w hw hwu hJw
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t htt
    exact (hb t ⟨htt.1, htt.2.trans hT⟩ (w t) (hbound t htt)).1
  · have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t htt
    exact (hb t ⟨htt.1, htt.2.trans hT⟩ (w t) (hbound t htt)).2

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem ambient_coefficients_h2_norm_le_of_small_state
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ C.radius ∧ δ ≤ 1 ∧
      ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ T : ℝ, T ≤ δ →
      ∀ field : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) T,
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ δ) →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 2) T,
      ∃ b₂ : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)) T,
        (fun t => H (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))) ∧
        (fun t => P (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + ‖field‖) ∧
        ‖b₂‖ ≤ B * (Real.sqrt T + ‖field‖) := by
  intro C g₀ J K H P
  obtain ⟨δa, hδa, hδaC, hδa1, A, hA, ha⟩ :=
    ambient_diffusion_h2_norm_le_of_small_state c₀ g ht he hr hEU hleft β hG
  obtain ⟨δb, hδb, _, _, B, hB, hb⟩ :=
    ambient_reaction_h2_norm_le_of_small_state c₀ g ht he hr hEU hleft β hG
  refine ⟨min δa δb, lt_min hδa hδb, (min_le_left _ _).trans hδaC,
    (min_le_left _ _).trans hδa1, A, B, hA, hB, ?_⟩
  intro T hTδ field w hw hwu hbound
  have hwa : ∀ t ∈ Icc 0 T, ‖w t‖ ≤ δa := fun t ht =>
    (hbound t ht).trans (min_le_left _ _)
  have hwb : ∀ t ∈ Icc 0 T, ‖w t‖ ≤ δb := fun t ht =>
    (hbound t ht).trans (min_le_right _ _)
  obtain ⟨a₂, ha₂, hanorm⟩ := ha T (hTδ.trans (min_le_left _ _)) field w hw hwu hwa
  obtain ⟨b₂, hb₂, hbnorm⟩ := hb T (hTδ.trans (min_le_right _ _)) field w hw hwu hwb
  exact ⟨a₂, b₂, ha₂, hb₂, hanorm, hbnorm⟩

private theorem ambient_parameterDerivative_duhamel_equation
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    ∀ (T : ℝ) (hT : 0 < T),
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))
      let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))
      let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
      let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
      (∀ᵐ t ∂timeMeasure T,
        L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) →
      let Gforce := parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce
      let V := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((0 : ℕ) : ℝ)) hT 0 Gforce
      ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ)) (Gforce t i) =
            AddCircle.parameterDerivativeParabolicForcing g₀
              (alpha t) (reaction t i) (f₀ i) (V t i) := by
  intro C g₀ f₀ J T hT gforce field w alpha reaction L Q m heq Gforce V
  apply parameterDerivativeDuhamelForcing_ae_eq g₀ hT gforce f₀ alpha reaction
  filter_upwards [heq] with t ht
  intro i
  exact congrArg (fun v : CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) => v i) ht

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev (scalarCc)
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem ambient_diffusion_sub_baseline_norm_le
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ Cα : ℝ≥0, ∀ {ρ T : ℝ}, 0 ≤ ρ → T ≤ ρ →
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
      ∀ t ∈ Icc 0 T,
        ‖tensorHsCongrL g₀ 0 0
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall C.radius_pos.le C.diffusion t (J (w t))) - q‖ ≤ Cα * ρ := by
  intro C g₀ J q
  refine ⟨C.diffusionLipschitz * max 1 ‖J‖₊, ?_⟩
  intro ρ T hρ hTρ w hw hJ t ht
  let z₀ : Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) C.radius :=
    ⟨0, Metric.mem_closedBall_self C.radius_pos.le⟩
  have hz : J (w t) ∈ Metric.closedBall 0 C.radius := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hJ t ht
  have hbase : C.diffusion 0 z₀ =
      ccTensorToHs g₀ 0 1 (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀)) :=
    initial_diffusion_coefficients c₀ g he hr hEU hleft β C
  have hmax : max t ‖J (w t)‖ ≤ max 1 ‖J‖ * ρ := by
    apply max_le
    · exact (ht.2.trans hTρ).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 ‖J‖) hρ)
    · exact (J.le_opNorm (w t)).trans
        ((mul_le_mul_of_nonneg_left (hw t ht) (norm_nonneg J)).trans
          (mul_le_mul_of_nonneg_right (le_max_right 1 ‖J‖) hρ))
  have hbound : ‖extendClosedBall C.radius_pos.le C.diffusion t (J (w t)) -
      C.diffusion 0 z₀‖ ≤ C.diffusionLipschitz * (max 1 ‖J‖ * ρ) := by
    rw [extendClosedBall_apply C.radius_pos.le C.diffusion t (J (w t)) hz]
    have h := C.diffusion_lipschitz.dist_le_mul (t, ⟨J (w t), hz⟩) (0, z₀)
    simp only [Prod.dist_eq, Subtype.dist_eq, z₀, dist_eq_norm, sub_zero,
      Real.norm_eq_abs, abs_of_nonneg ht.1] at h
    exact h.trans (mul_le_mul_of_nonneg_left hmax C.diffusionLipschitz.coe_nonneg)
  change ‖tensorHsCongrL g₀ 0 0 _ _ -
    ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))‖ ≤ _
  rw [← tensorHsCongrL_ccTensorToHs g₀
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ)), ← hbase,
    ← map_sub, tensorHsCongrL_apply, norm_tensorHsCongr]
  simpa only [NNReal.coe_mul, NNReal.coe_max, NNReal.coe_one, coe_nnnorm, mul_assoc]
    using hbound

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem ambient_coefficients_h2_norm_le_of_forcing_bound
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ C.radius ∧ δ ≤ 1 ∧
      ∃ A B : ℝ≥0, ∀ {ρ T : ℝ} (hT : 0 < T), T ≤ ρ → ρ ≤ δ →
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
      ‖gforce‖ ≤ ρ / 4 →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∃ b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => H (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))) ∧
        (fun t => P (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) ∧
        ‖b₂‖ ≤ B * (Real.sqrt T + (1 + T) * ρ / 4) := by
  intro C g₀ J K H P
  obtain ⟨δ, hδ, hδC, hδ1, A, B, hA, hB, hab⟩ :=
    ambient_coefficients_h2_norm_le_of_small_state c₀ g ht he hr hEU hleft β hG
  refine ⟨δ, hδ, hδC, hδ1, ⟨A, hA⟩, ⟨B, hB⟩, ?_⟩
  intro ρ T hT hTρ hρδ gforce field w hw hwu hbound hforce
  obtain ⟨a₂, b₂, ha₂, hb₂, hanorm, hbnorm⟩ :=
    hab T (hTρ.trans hρδ) field w hw hwu (fun t ht => (hbound t ht).trans hρδ)
  let S := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ 2)
  let SP := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => S)
  let aa := S.compLpL 2 (timeMeasure T) a₂
  let bb := SP.compLpL 2 (timeMeasure T) b₂
  have hSnorm : ‖S‖ ≤ 1 := tensorHsInclusion_opNorm_le_one _
  have hSPnorm : ‖SP‖ ≤ 1 :=
    ContinuousLinearMap.norm_piLpMap_le _ zero_le_one (fun _ => hSnorm)
  have han : ‖aa‖ ≤ ‖a₂‖ := by
    exact (S.norm_compLp_le a₂).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hSnorm (norm_nonneg a₂))
  have hbn : ‖bb‖ ≤ ‖b₂‖ := by
    exact (SP.norm_compLp_le b₂).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hSPnorm (norm_nonneg b₂))
  have hfield : ‖field‖ ≤ (1 + T) * ρ / 4 := by
    exact (norm_maximalRegularityDuhamelVectorField_zero_le hT gforce).trans
      (by simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left hforce (by linarith : 0 ≤ 1 + T))
  refine ⟨aa, bb, ?_, ?_, han.trans (hanorm.trans ?_), hbn.trans (hbnorm.trans ?_)⟩
  · filter_upwards [S.coeFn_compLpL a₂, ha₂] with t hta hta₂
    change H (aa t) = _
    rw [hta]
    exact (tensorHsInclusion_trans_apply _ _ _).symm.trans hta₂
  · filter_upwards [SP.coeFn_compLpL b₂, hb₂] with t htb htb₂
    change P (bb t) = _
    rw [htb, ← htb₂]
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ 2) (b₂ t i)).symm
  · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hfield) hA
  · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hfield) hB

private theorem ambient_parameter_equation_of_h2_coefficients
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let f₄ := ambientSobolev c₀ (g 0) e he (((2 : ℕ) : ℝ) + 2)
    let K₄ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    ∀ (T : ℝ) (hT : 0 < T),
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))
      let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))
      let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
      let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∀ b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
      (fun t => H (a₂ t)) =ᵐ[timeMeasure T] alpha →
      (fun t => P (b₂ t)) =ᵐ[timeMeasure T] reaction →
      (∀ᵐ t ∂timeMeasure T,
        L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) →
      ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (field t i) +
          gforce t i = scalarHsMul g₀ 1 (by norm_num) (H (a₂ t))
            (AddCircle.parameterSecondDerivativeHs g₀ 1 (K₄ (f₄ i) + field t i)) +
              H (b₂ t i) := by
  intro C g₀ f₀ f₄ K₄ H P J T hT gforce field w alpha reaction L Q m a₂ b₂ ha hb heq
  have hbase (i : Fin n) : K₄ (f₄ i) = f₀ i := by
    exact tensorHsInclusion_ccTensorToHs g₀ 0
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
      (ambientCoordinateCc c₀ (g 0) e he i)
  filter_upwards [heq, ha, hb] with t ht hat hbt
  intro i
  rw [hbase]
  rw [← hat, ← hbt] at ht
  exact congrArg (fun v : CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ) => v i) ht

private theorem parameterDerivativeH0Pi_normalized_contraction
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (C₂ : ℝ≥0) :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let Z : CircleHsPi g₀ (Fin n) 0 →L[ℝ] CircleHsPi g₀ (Fin n) ((0 : ℕ) : ℝ) :=
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ)))
    let A₂ : ℝ → CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 2) →L[ℝ]
        CircleHsPi g₀ (Fin n) 0 :=
      fun t => AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (H (a₂ t))
    let A₁ : ℝ → CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 1) →L[ℝ]
        CircleHsPi g₀ (Fin n) 0 :=
      fun t => AddCircle.parameterDriftOperatorH0Pi (ι := Fin n) g₀ (a₂ t)
    let hA₁ : MemLp A₁ 2 (timeMeasure T) := AddCircle.memLp_parameterDriftOperatorH0Pi (ι := Fin n) g₀ (Lp.memLp a₂)
    (∀ᵐ t ∂timeMeasure T,
      ‖A₂ t‖ ≤ C₂) →
    (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) * ‖hA₁.toLp A₁‖ < 1 →
    (∀ᵐ t ∂timeMeasure T,
      ‖Z.comp (A₂ t)‖ ≤ C₂) ∧
    (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (fun t => Z.comp (A₁ t)) 2 (timeMeasure T)).toReal < 1 := by
  intro H Z A₂ A₁ hA₁ hC hsmall
  have hZ : ‖Z‖ ≤ 1 :=
    ContinuousLinearMap.norm_piLpMap_le _ zero_le_one
      (fun _ => tensorHsInclusion_opNorm_le_one _)
  have hpoint {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
      (L : X →L[ℝ] CircleHsPi g₀ (Fin n) 0) : ‖Z.comp L‖ ≤ ‖L‖ :=
    (ContinuousLinearMap.opNorm_comp_le Z L).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hZ (norm_nonneg L))
  have hn : (eLpNorm (fun t => Z.comp (A₁ t)) 2 (timeMeasure T)).toReal ≤
      (eLpNorm A₁ 2 (timeMeasure T)).toReal :=
    ENNReal.toReal_mono hA₁.eLpNorm_lt_top.ne
      (eLpNorm_mono (fun t => hpoint (A₁ t)))
  refine ⟨?_, ?_⟩
  · filter_upwards [hC] with t ht
    exact (hpoint _).trans ht
  · rw [Lp.norm_toLp] at hsmall
    exact lt_of_le_of_lt
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg (1 + T)))) hsmall

private abbrev parameterPrincipalHigh
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) :=
  fun t => AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀
    (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))

private abbrev parameterNormalizeZero
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ)))

private abbrev parameterPrincipalLow
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) :=
  fun t => (parameterNormalizeZero (n := n) g₀).comp
    (AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀
      (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)))

private abbrev parameterDriftHigh
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) :=
  fun t => AddCircle.parameterDriftOperatorHsPi (ι := Fin n) g₀ (a₂ t)

private abbrev parameterDriftLow
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) :=
  fun t => (parameterNormalizeZero (n := n) g₀).comp
    (AddCircle.parameterDriftOperatorH0Pi (ι := Fin n) g₀ (a₂ t))

private abbrev parameterDerivativeLiftOfCoefficients
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)
    (F : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (C₂h C₂l : ℝ≥0) :=
  exists_unique_parameterDerivativeDuhamelForcing_lift g₀ hT F f₄ a₂ b₂ C₂h C₂l

section

variable (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ} (hT : 0 < T)

variable (F : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)

variable (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))

variable (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)

variable (b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T)

variable (C₂h C₂l : ℝ≥0)

variable (hC₂h : ∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalHigh (n := n) g₀ a₂ t‖ ≤ C₂h)

variable (hC₂l : ∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂l)

variable (hsmallh : (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1)

variable (hsmalll : (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1)

private abbrev parameterDerivativeLiftWithHighBound :=
  parameterDerivativeLiftOfCoefficients
    g₀ hT F f₄ a₂ b₂ C₂h C₂l hC₂h hC₂l
      (by change _ + _ * ‖_‖ < (1 : ℝ); erw [Lp.norm_toLp]; exact hsmallh)

private abbrev parameterDerivativeLiftWithBounds :=
  parameterDerivativeLiftWithHighBound (g₀ := g₀) (hT := hT) (F := F) (f₄ := f₄)
    (a₂ := a₂) (b₂ := b₂) (C₂h := C₂h) (C₂l := C₂l) (hC₂h := hC₂h) (hC₂l := hC₂l)
    (hsmallh := hsmallh)
    (by change _ + _ * ‖_‖ < (1 : ℝ); erw [Lp.norm_toLp]; exact hsmalll)

include hC₂h hC₂l hsmallh hsmalll in
private theorem parameterDerivative_forcing_lift_of_contraction :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let K₄ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
    let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 F
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (field t i) + F t i =
        scalarHsMul g₀ 1 (by norm_num) (H (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g₀ 1 (K₄ (f₄ i) + field t i)) + H (b₂ t i)) →
    ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT F =
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := g₀) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
              2 (timeMeasure T) FH := by
  intro H K₄ field hweak
  obtain ⟨FH, hFH, _⟩ := parameterDerivativeLiftWithBounds
    (g₀ := g₀) (hT := hT) (F := F) (f₄ := f₄) (a₂ := a₂) (b₂ := b₂)
    (C₂h := C₂h) (C₂l := C₂l) (hC₂h := hC₂h) (hC₂l := hC₂l)
    (hsmallh := hsmallh) (hsmalll := hsmalll) hweak
  exact ⟨FH, hFH.2⟩

end


section

variable (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
variable (Cα A : ℝ≥0) {R : ℝ} (hR : 0 < R)

include hR in
private theorem exists_pos_parameterDerivative_high_contraction_radius :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (DifferentialGeometry.Analysis.Sobolev.scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
      0 < T → T ≤ ρ → ρ ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - q‖ ≤ Cα * ρ) →
      ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
      ∃ C₂h : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalHigh (n := n) g₀ a₂ t‖ ≤ C₂h) ∧
        (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
          (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1 := by
  intro H q
  obtain ⟨δ, hδ, hδR, hδ1, hh⟩ :=
    AddCircle.exists_pos_parameterDerivativeHsPi_contraction_radius (ι := Fin n) g₀ Cα A hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hclose hnorm
  obtain ⟨C₂h, hC₂h, hsmallh⟩ := hh hT hTρ hρδ a₂ hclose hnorm
  refine ⟨C₂h, hC₂h, ?_⟩
  simpa only [Lp.norm_toLp] using hsmallh

private def parameterDerivativeRawLowContraction
    {T : ℝ} (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) : Prop :=
  let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
  let A₂ := fun t => AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (H (a₂ t))
  let A₁ := fun t => AddCircle.parameterDriftOperatorH0Pi (ι := Fin n) g₀ (a₂ t)
  let hA₁ := AddCircle.memLp_parameterDriftOperatorH0Pi (ι := Fin n) g₀ (Lp.memLp a₂)
  ∃ C₂ : ℝ≥0, (∀ᵐ t ∂timeMeasure T, ‖A₂ t‖ ≤ C₂) ∧
    (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) * ‖hA₁.toLp A₁‖ < 1

private def parameterDerivativeNormalizedLowContraction
    {T : ℝ} (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) : Prop :=
  ∃ C₂ : ℝ≥0,
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂) ∧
    (C₂ : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1

private theorem parameterDerivative_normalizedLowContraction_of_raw
    {T : ℝ} (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (hraw : parameterDerivativeRawLowContraction (n := n) g₀ a₂) :
    parameterDerivativeNormalizedLowContraction (n := n) g₀ a₂ := by
  obtain ⟨C₂, hC₂, hsmall⟩ := hraw
  exact ⟨C₂, parameterDerivativeH0Pi_normalized_contraction g₀ a₂ C₂ hC₂ hsmall⟩

private def parameterDerivativeLowContractionRadiusStatement : Prop :=
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (DifferentialGeometry.Analysis.Sobolev.scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
      0 < T → T ≤ ρ → ρ ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - q‖ ≤ Cα * ρ) →
      ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
      ∃ C₂l : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂l) ∧
        (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) *
          (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1

include hR in
private theorem exists_pos_parameterDerivative_low_contraction_radius :
    parameterDerivativeLowContractionRadiusStatement (n := n) g₀ Cα A (R := R) := by
  unfold parameterDerivativeLowContractionRadiusStatement
  intro H q
  obtain ⟨δ, hδ, hδR, hδ1, hl⟩ :=
    AddCircle.exists_pos_parameterDerivativeH0Pi_contraction_radius (ι := Fin n) g₀ Cα A hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hclose hnorm
  obtain ⟨C₂l, hC₂l, hsmalll⟩ := hl hT hTρ hρδ a₂ hclose hnorm
  exact parameterDerivative_normalizedLowContraction_of_raw g₀ a₂ ⟨C₂l, hC₂l, hsmalll⟩


private def parameterDerivativeContractionRadiusStatement : Prop :=
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (DifferentialGeometry.Analysis.Sobolev.scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
      0 < T → T ≤ ρ → ρ ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - q‖ ≤ Cα * ρ) →
      ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
      ∃ C₂h C₂l : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalHigh (n := n) g₀ a₂ t‖ ≤ C₂h) ∧
        (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂l) ∧
        (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
          (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1 ∧
        (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) *
          (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1

include hR in
private theorem exists_pos_parameterDerivative_contraction_radius :
    parameterDerivativeContractionRadiusStatement (n := n) g₀ Cα A (R := R) := by
  unfold parameterDerivativeContractionRadiusStatement
  intro H q
  obtain ⟨δh, hδh, hδhR, hδh1, hh⟩ :=
    exists_pos_parameterDerivative_high_contraction_radius (n := n) g₀ Cα A hR
  obtain ⟨δl, hδl, _, _, hl⟩ :=
    exists_pos_parameterDerivative_low_contraction_radius (n := n) g₀ Cα A hR
  refine ⟨min δh δl, lt_min hδh hδl, (min_le_left _ _).trans hδhR,
    (min_le_left _ _).trans hδh1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hclose hnorm
  obtain ⟨C₂h, hC₂h, hsmallh⟩ := hh hT hTρ (hρδ.trans (min_le_left _ _)) a₂ hclose hnorm
  obtain ⟨C₂l, hC₂l, hsmalll⟩ := hl hT hTρ (hρδ.trans (min_le_right _ _)) a₂ hclose hnorm
  exact ⟨C₂h, C₂l, hC₂h, hC₂l, hsmallh, hsmalll⟩

end

section

variable (c₀ : SmoothImmersion (I := I) (M := M))

variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}

variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)

variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)

variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private def ambientH2Control :=
  Classical.indefiniteDescription _
    (ambient_coefficients_h2_norm_le_of_forcing_bound c₀ g ht he hr hEU hleft β hG)

private def ambientH2ControlBounds :=
  Classical.indefiniteDescription _
    (ambientH2Control c₀ g ht he hr hEU hleft β hG).property.2.2.2

private def ambientDiffusionClosenessControl :=
  Classical.indefiniteDescription _
    (ambient_diffusion_sub_baseline_norm_le c₀ g ht he hr hEU hleft β hG)

private def ambientParameterDerivativeControl :=
  Classical.indefiniteDescription _
    (exists_pos_parameterDerivative_contraction_radius (n := n) (c₀.pullbackMetric (g 0))
      (ambientDiffusionClosenessControl c₀ g ht he hr hEU hleft β hG).val
      (ambientH2ControlBounds c₀ g ht he hr hEU hleft β hG).val
      (ambientH2Control c₀ g ht he hr hEU hleft β hG).property.1)

private def ambientDiffusionProjection {T : ℝ}
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T) : Prop :=
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  (fun t => tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
    (fun t => tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (extendClosedBall C.radius_pos.le C.diffusion t (J (w t))))

private def ambientReactionProjection {T : ℝ}
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (b₂ : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) T) : Prop :=
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  (fun t => (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1))) (b₂ t)) =ᵐ[timeMeasure T]
    (fun t => circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (extendClosedBall C.radius_pos.le C.reaction t (J (w t))))

private theorem ambient_diffusion_h2_sub_baseline_norm_le :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    ∀ {ρ T : ℝ}, 0 ≤ ρ → T ≤ ρ →
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ambientDiffusionProjection c₀ g ht he hr hEU hleft β hG w a₂ →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
      ∀ᵐ t ∂timeMeasure T,
        ‖H (a₂ t) - ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
          (DifferentialGeometry.Analysis.Sobolev.scalarCc g₀
            (AddCircle.laplacianPrincipalCoefficient g₀))‖ ≤
              (ambientDiffusionClosenessControl c₀ g ht he hr hEU hleft β hG).val * ρ := by
  intro C g₀ J H ρ T hρ hTρ w a₂ ha hbound hJ
  have htmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  filter_upwards [ha, htmem] with t hat htt
  rw [hat]
  exact (ambientDiffusionClosenessControl c₀ g ht he hr hEU hleft β hG).property
    hρ hTρ w hbound hJ t htt

private abbrev ambientDiffusionH2ClosenessAtState
    {ρ T : ℝ} (hρ : 0 ≤ ρ) (hTρ : T ≤ ρ)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T) :=
  ambient_diffusion_h2_sub_baseline_norm_le c₀ g ht he hr hEU hleft β hG hρ hTρ w a₂

private abbrev ambientParameterDerivativeContractionAtState
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρδ : ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val)
    (a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T) :=
  (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).property.2.2.2
    hT hTρ hρδ a₂

private def ambientParameterDerivativeLiftAtRadius (δ : ℝ) : Prop :=
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    ∀ {ρ T : ℝ} (hT : 0 < T), T ≤ ρ → ρ ≤ δ →
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))
      let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))
      let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
      let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
      ‖gforce‖ ≤ ρ / 4 →
      (∀ᵐ t ∂timeMeasure T,
        L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) →
      ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
        parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce =
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
            tensorHsInclusion (g := g₀) (r := 0) (s := 0)
              (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
                2 (timeMeasure T) FH


private def ambientParameterDerivativeLiftAtControlRadius
    (C : ScalarVectorTimeCoefficients (c₀.pullbackMetric (g 0))
      (curveShorteningChartDiffusionCoefficient (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n)
      (fun z j => (curveShorteningParametricChartReaction (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z)).ofLp j)
      (firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β)
      (c₀.ambientFirstJet (g 0) e he))
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 2)))
    (J : (PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1))) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 (1 : ℝ)))
    (K : PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : Fin n => TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1))) : Prop :=
    ∀ {ρ T : ℝ} (hT : 0 < T), T ≤ ρ → ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val →
      ∀ gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1),
      let alpha := fun t => tensorHsCongrL (c₀.pullbackMetric (g 0)) 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))
      let reaction := fun t => circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))
      let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorScaleLaplacian (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) (c₀.pullbackMetric (g 0)) 1
      let m := coordinateMultiplication (ι := Fin n) (scalarHsMul (c₀.pullbackMetric (g 0)) 1 (by norm_num))
      ContinuousOn w (Icc 0 T) →
      w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
      (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
      ‖gforce‖ ≤ ρ / 4 →
      (∀ᵐ t ∂timeMeasure T,
        L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) →
      ∃ FH : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T,
        parameterDerivativeDuhamelForcing (ι := Fin n) (c₀.pullbackMetric (g 0)) 0 hT gforce =
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
            tensorHsInclusion (g := (c₀.pullbackMetric (g 0))) (r := 0) (s := 0)
              (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
                2 (timeMeasure T) FH

private def ambientParameterDerivativeLiftOfOperatorBounds : Prop :=
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    ∀ (T : ℝ) (hT : 0 < T),
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))
      let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))
      let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
      let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
      let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∀ b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
      ambientDiffusionProjection c₀ g ht he hr hEU hleft β hG w a₂ →
      ambientReactionProjection c₀ g ht he hr hEU hleft β hG w b₂ →
      (∀ᵐ t ∂timeMeasure T,
        L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) →
      ∀ C₂h C₂l : ℝ≥0,
      (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalHigh (n := n) g₀ a₂ t‖ ≤ C₂h) →
      (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂l) →
      (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
        (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1 →
      (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) *
        (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1 →
      ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
        parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce =
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
            tensorHsInclusion (g := g₀) (r := 0) (s := 0)
              (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
                2 (timeMeasure T) FH

private theorem ambient_parameterDerivative_forcing_lift_of_operator_bounds :
    ambientParameterDerivativeLiftOfOperatorBounds c₀ g ht he hr hEU hleft β hG := by
  unfold ambientParameterDerivativeLiftOfOperatorBounds
  intro C g₀ f₀ J T hT gforce field w alpha reaction L Q m a₂ b₂ ha hb heq C₂h C₂l hC₂h hC₂l hsmallh hsmalll
  have hweak := ambient_parameter_equation_of_h2_coefficients c₀ g ht he hr hEU hleft β hG
    T hT gforce w a₂ b₂ ha hb heq
  exact parameterDerivative_forcing_lift_of_contraction g₀ hT gforce
    (ambientSobolev c₀ (g 0) e he (((2 : ℕ) : ℝ) + 2)) a₂ b₂ C₂h C₂l hC₂h hC₂l
    hsmallh hsmalll hweak

private abbrev ambientParameterDerivativeOperatorLift
    (T : ℝ) (hT : 0 < T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) T) :=
  ambient_parameterDerivative_forcing_lift_of_operator_bounds c₀ g ht he hr hEU hleft β hG
    T hT gforce w a₂ b₂

private def parameterDerivativeOperatorBoundsWithMargin {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) (q : ℝ) : Prop :=
  ∃ C₂h C₂l : ℝ≥0,
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalHigh (n := n) g₀ a₂ t‖ ≤ C₂h) ∧
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂l) ∧
    (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal ≤ q ∧
    (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1

private def parameterDerivativeOperatorBounds
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) : Prop :=
  ∃ C₂h C₂l : ℝ≥0,
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalHigh (n := n) g₀ a₂ t‖ ≤ C₂h) ∧
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalLow (n := n) g₀ a₂ t‖ ≤ C₂l) ∧
    (C₂h : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1 ∧
    (C₂l : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftLow (n := n) g₀ a₂) 2 (timeMeasure T)).toReal < 1

private theorem parameterDerivativeOperatorBounds_of_margin
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T q : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (hq : q < 1) (h : parameterDerivativeOperatorBoundsWithMargin (n := n) g₀ a₂ q) :
    parameterDerivativeOperatorBounds (n := n) g₀ a₂ := by
  obtain ⟨C₂h, C₂l, hhigh, hlow, hmargin, hsmall⟩ := h
  exact ⟨C₂h, C₂l, hhigh, hlow, hmargin.trans_lt hq, hsmall⟩

private theorem ambient_h2_coefficient_contraction
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρδ : ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (ha : ambientDiffusionProjection c₀ g ht he hr hEU hleft β hG w a₂)
    (hanorm : ‖a₂‖ ≤ (ambientH2ControlBounds c₀ g ht he hr hEU hleft β hG).val *
      (Real.sqrt T + (1 + T) * ρ / 4))
    (hbound : ∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ)
    (hJ : ∀ t ∈ Icc 0 T, ‖((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
      (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap) (w t)‖ ≤
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG).radius) :
    parameterDerivativeOperatorBounds (n := n) (c₀.pullbackMetric (g 0)) a₂ := by
  have hclose₂ := ambientDiffusionH2ClosenessAtState c₀ g ht he hr hEU hleft β hG
    (hT.le.trans hTρ) hTρ w a₂ ha hbound hJ
  exact ambientParameterDerivativeContractionAtState c₀ g ht he hr hEU hleft β hG
    hT hTρ hρδ a₂ hclose₂ hanorm

private def ambientSobolevEquation
    (T : ℝ) (hT : 0 < T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) : Prop :=
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))
    let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
    (∀ᵐ t ∂timeMeasure T,
      L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t)

private theorem ambient_parameterDerivative_forcing_lift_for_coefficients
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρδ : ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (a₂ : timeL2 (TensorHs (c₀.pullbackMetric (g 0)) 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (b₂ : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) T)
    (ha : ambientDiffusionProjection c₀ g ht he hr hEU hleft β hG w a₂)
    (hb : ambientReactionProjection c₀ g ht he hr hEU hleft β hG w b₂)
    (hanorm : ‖a₂‖ ≤ (ambientH2ControlBounds c₀ g ht he hr hEU hleft β hG).val *
      (Real.sqrt T + (1 + T) * ρ / 4))
    (hbound : ∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ)
    (hJ : ∀ t ∈ Icc 0 T, ‖((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
      (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap) (w t)‖ ≤
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG).radius)
    (heq : ambientSobolevEquation c₀ g ht he hr hEU hleft β hG T hT gforce w) :
    ∃ FH : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T,
      parameterDerivativeDuhamelForcing (ι := Fin n) (c₀.pullbackMetric (g 0)) 0 hT gforce =
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := c₀.pullbackMetric (g 0)) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
              2 (timeMeasure T) FH := by
  obtain ⟨C₂h, C₂l, hC₂h, hC₂l, hsmallh, hsmalll⟩ :=
    ambient_h2_coefficient_contraction c₀ g ht he hr hEU hleft β hG
      hT hTρ hρδ w a₂ ha hanorm hbound hJ
  have heq' := (show ambientSobolevEquation c₀ g ht he hr hEU hleft β hG T hT gforce w from heq)
  exact ambientParameterDerivativeOperatorLift c₀ g ht he hr hEU hleft β hG
    T hT gforce w a₂ b₂ ha hb heq' C₂h C₂l hC₂h hC₂l hsmallh hsmalll

private abbrev ambientH2CoefficientsAtState
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρδ : ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) :=
  (ambientH2ControlBounds c₀ g ht he hr hEU hleft β hG).property.choose_spec
    hT hTρ (hρδ.trans (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).property.2.1)
    gforce w

private theorem ambient_parameterDerivative_forcing_lift_at_small_state :
    ambientParameterDerivativeLiftAtControlRadius c₀ g ht he hr hEU hleft β hG
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG)
      (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
      ((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
        (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap)
      (circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)) := by
  unfold ambientParameterDerivativeLiftAtControlRadius
  intro ρ T hT hTρ hρδ gforce field w alpha reaction L Q m hw hwu hbound hJ hforce heq
  obtain ⟨a₂, b₂, ha, hb, hanorm, _⟩ :=
    ambientH2CoefficientsAtState c₀ g ht he hr hEU hleft β hG
      hT hTρ hρδ gforce w hw hwu hbound hforce
  have hpa : ambientDiffusionProjection c₀ g ht he hr hEU hleft β hG w a₂ := ha
  have hpb : ambientReactionProjection c₀ g ht he hr hEU hleft β hG w b₂ := hb
  have heq' : ambientSobolevEquation c₀ g ht he hr hEU hleft β hG T hT gforce w := by
    simpa only [ambientSobolevEquation] using heq
  exact ambient_parameterDerivative_forcing_lift_for_coefficients c₀ g ht he hr hEU hleft β hG
    hT hTρ hρδ gforce w a₂ b₂ hpa hpb hanorm hbound hJ heq'



private def ambientParameterDerivativeLiftOfSmallState : Prop :=
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ C.radius ∧ δ ≤ 1 ∧
    ambientParameterDerivativeLiftAtRadius c₀ g ht he hr hEU hleft β hG δ

private theorem ambient_parameterDerivative_forcing_lift_of_small_state :
    ambientParameterDerivativeLiftOfSmallState c₀ g ht he hr hEU hleft β hG := by
  unfold ambientParameterDerivativeLiftOfSmallState
  intro C
  let co := ambientH2Control c₀ g ht he hr hEU hleft β hG
  let control := ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG
  refine ⟨control.val, control.property.1,
    control.property.2.1.trans co.property.2.1,
    control.property.2.1.trans co.property.2.2.1, ?_⟩
  exact ambient_parameterDerivative_forcing_lift_at_small_state c₀ g ht he hr hEU hleft β hG

end

private abbrev parameterDerivativeHighField
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :=
(ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ)))).comp
      ((AddCircle.parameterDerivativeHsPi (ι := Fin n) g₀ 2).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
          tensorHsInclusion (g := g₀) (r := 0) (s := 0)
            (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))))

section

variable (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)

variable (gforce FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)

private theorem heatDuhamel_zero_eq_maximalRegularity
    (G : timeL2 (CircleHsPi g₀ (Fin n) ((0 : ℕ) : ℝ)) T) :
    heatDuhamelVectorField (g := g₀) (r := 0) (s := 0)
      (a := ((0 : ℕ) : ℝ)) hT 0 G =
    maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
      (a := ((0 : ℕ) : ℝ)) hT 0 G := by
  have hc := tensorResolventL2_isCompactOperator (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g₀ 0 0
  simpa only [map_zero] using heatDuhamelVectorField_inclusion
    (g := g₀) (r := 0) (s := 0) (a := ((0 : ℕ) : ℝ)) hT hc 0 G

private theorem heatDuhamel_zero_inclusion_eq_maximalRegularity :
    let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let J₂ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2))
    J₂.compLpL 2 (timeMeasure T)
      (heatDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 FH) =
      maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((0 : ℕ) : ℝ)) hT 0 (J₀.compLpL 2 (timeMeasure T) FH) := by
  intro J₀ J₂
  have hc := tensorResolventL2_isCompactOperator (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g₀ 0 0
  have hi := heatDuhamelVectorField_compLpL_tensorHsInclusion (ι := Fin n)
    (g := g₀) (r := 0) (s := 0) (a := ((0 : ℕ) : ℝ)) (b := ((1 : ℕ) : ℝ))
    (by norm_num) hT hc 0 FH
  change J₂.compLpL 2 (timeMeasure T) _ =
    heatDuhamelVectorField hT _ (J₀.compLpL 2 (timeMeasure T) FH) at hi
  rw [map_zero] at hi
  exact hi.trans (heatDuhamel_zero_eq_maximalRegularity g₀ hT _)

private theorem parameterDerivative_field_lift_of_forcing_lift :
    let G := parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce
    let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    let Dh := parameterDerivativeHighField (n := n) g₀
    let J₀ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let J₂ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2))
    G = J₀.compLpL 2 (timeMeasure T) FH →
    Dh.compLpL 2 (timeMeasure T) field = J₂.compLpL 2 (timeMeasure T)
      (heatDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 FH) := by
  intro G field Dh J₀ J₂ hG
  let V := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
    (a := ((0 : ℕ) : ℝ)) hT 0 G
  have hder : Dh.compLpL 2 (timeMeasure T) field = V :=
    (parameterDerivative_duhamel_vector_eq g₀ 0 hT gforce).1
  have hi := heatDuhamel_zero_inclusion_eq_maximalRegularity g₀ hT FH
  change J₂.compLpL 2 (timeMeasure T) _ =
    maximalRegularityDuhamelVectorField hT 0 (J₀.compLpL 2 (timeMeasure T) FH) at hi
  rw [← hG] at hi
  exact hder.trans hi.symm

end

section

variable (c₀ : SmoothImmersion (I := I) (M := M))

variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}

variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)

variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)

variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private def ambientSobolevSolutionOfCoefficientsWithRadiusLe
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (C : ScalarVectorTimeCoefficients (c₀.pullbackMetric (g 0))
      (curveShorteningChartDiffusionCoefficient (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∘ firstJetCoordinates n)
      (fun z j => curveShorteningParametricChartReaction (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (firstJetCoordinates n z) j)
      (firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β)
      (ambientFirstJet c₀ (g 0) e he))
    {δ : ℝ} (hδ : 0 < δ) :
    {sol : PrecomposedCircleSolution (c₀.pullbackMetric (g 0))
      (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
      ((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
        (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap)
      C.radius_pos C.diffusion C.reaction //
      precomposedCircleSolutionRadius (c₀.pullbackMetric (g 0))
        (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
        ((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
          (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
            (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap)
        C.radius_pos C.diffusion C.reaction sol ≤ δ} :=
  precomposedCircleSolutionWithRadiusLe (c₀.pullbackMetric (g 0))
    (ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2))
    ((circleFirstJet (ι := Fin n) (c₀.pullbackMetric (g 0))).comp
      (circleHsPiCongr (c₀.pullbackMetric (g 0)) (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap)
    C.radius_pos hδ C.diffusion C.reaction C.diffusionLipschitz C.reactionLipschitz
    C.diffusion_lipschitz C.reaction_lipschitz
    (initial_diffusion_coefficients c₀ g he hr hEU hleft β C)


private abbrev ambientCappedSobolevSolutionSpec {δ : ℝ} (hδ : 0 < δ) :=
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let sol := ambientSobolevSolutionOfCoefficientsWithRadiusLe c₀ g he hr hEU hleft β C hδ
  precomposed_circle_solution_exists_with_radius_le g₀ f₀ J C.radius_pos
    C.diffusion C.reaction sol.val sol.property

private def parameterDerivativeForcingFieldLift
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) : Prop :=
  let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
    (a := ((1 : ℕ) : ℝ)) hT 0 gforce
  ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
    parameterDerivativeDuhamelForcing (ι := Fin n) g₀ 0 hT gforce =
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
            2 (timeMeasure T) FH ∧
    (parameterDerivativeHighField (n := n) g₀).compLpL 2 (timeMeasure T) field =
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2))).compLpL
            2 (timeMeasure T)
              (heatDuhamelVectorField (g := g₀) (r := 0) (s := 0)
                (a := ((1 : ℕ) : ℝ)) hT 0 FH)

private def ambientSobolevSolutionFacts (ρ : ℝ) {T : ℝ} (hT : 0 < T)
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T) : Prop :=
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
        (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
          let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
            (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0)
              (a := ((1 : ℕ) : ℝ)) hT 0 gforce
          u = maximalRegularityDuhamelVectorMap (I := 𝓘(ℝ, ℝ))
              (M := AddCircle (1 : ℝ)) (g := g₀) (r := 0) (s := 0)
                (a := ((1 : ℕ) : ℝ)) hT 0 gforce ∧
            (∀ᵐ t ∂(timeMeasure T), ‖K (field t)‖ ≤ ρ) ∧
            u.toFunL2 = (circleHsPiInclusion g₀ (Fin n)
              (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)).compLpL
                2 (timeMeasure T) field ∧
            timeH1.trace0 _ T u = 0 ∧
            timeH1.timeDeriv _ T u = L.compLpL 2 (timeMeasure T) field + gforce ∧
            ‖gforce‖ ≤ ρ / 4 ∧
            (∀ᵐ t ∂(timeMeasure T), ∃ z : Metric.closedBall (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) C.radius,
              (z : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) = J (K (field t)) ∧
              L (field t) + gforce t = m (tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                (C.diffusion t z)) (Q (f₀ + field t)) +
                circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (C.reaction t z)) ∧
            ∃ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
              ContinuousOn w (Set.Icc 0 T) ∧
              (∀ t ∈ Set.Icc 0 T,
                circleHsPiInclusion g₀ (Fin n)
                  (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by linarith)
                  (w t) = u.toFun t) ∧
              w =ᵐ[timeMeasure T] (fun t => K (field t)) ∧
              (∀ t ∈ Set.Icc 0 T, ‖w t‖ ≤ ρ) ∧ w 0 = 0 ∧
              (∀ t ∈ Set.Icc 0 T, ‖J (w t)‖ ≤ C.radius) ∧
              let alpha := fun t => tensorHsCongrL g₀ 0 0
                (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (extendClosedBall C.radius_pos.le C.diffusion t (J (w t)))
              let reaction := fun t => circleHsPiCongr g₀ (Fin n)
                (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                  (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))
              let S := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
                (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
              let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => S)
              let K₀ := circleHsPiInclusion g₀ (Fin n)
                (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P (K₀ f₀ + u.toFun t))
                (x : AddCircle (1 : ℝ))
              (∀ᵐ t ∂timeMeasure T,
                L (field t) + gforce t = m (alpha t) (Q (f₀ + field t)) + reaction t) ∧
              (∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (f t) ∧ ∀ x : ℝ,
                HasDerivAt (fun s => f s x)
                  (scalarH1ToContinuous g₀ (S (alpha t)) (x : AddCircle (1 : ℝ)) •
                    deriv (deriv (f t)) x + scalarH1PiToContinuous g₀ (P (reaction t))
                      (x : AddCircle (1 : ℝ))) t)

private def ambientSobolevSolutionWithParameterDerivativeLift : Prop :=
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ C.radius ∧ ρ ≤ 1 ∧
    ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
      ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
        (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
        ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
          parameterDerivativeForcingFieldLift g₀ hT gforce

private theorem ambient_parameterDerivative_lift_of_solution_facts
    {δ ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ) (hρδ : ρ ≤ δ)
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : ambientParameterDerivativeLiftAtRadius c₀ g ht he hr hEU hleft β hG δ) :
    parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce := by
  rcases hfacts with ⟨_, _, _, _, _, hforce, _, w,
    hw, _, hwu, hbound, _, hJ, heq', _⟩
  obtain ⟨FH, hFH⟩ := hlift hT hTρ hρδ gforce w hw hwu hbound hJ hforce heq'
  exact ⟨FH, hFH, parameterDerivative_field_lift_of_forcing_lift
    (c₀.pullbackMetric (g 0)) hT gforce FH hFH⟩


private theorem ambient_sobolev_solution_exists_with_parameterDerivative_lift_of_radius
    {δ : ℝ} (hδ : 0 < δ)
    (hlift : ambientParameterDerivativeLiftAtRadius c₀ g ht he hr hEU hleft β hG δ) :
    ambientSobolevSolutionWithParameterDerivativeLift c₀ g ht he hr hEU hleft β hG := by
  unfold ambientSobolevSolutionWithParameterDerivativeLift
  intro C g₀
  obtain ⟨ρ, hρ, hρC, hρ1, hρδ, T, hT, hTρ, u, gforce, hpacket⟩ :=
    ambientCappedSobolevSolutionSpec c₀ g ht he hr hEU hleft β hG hδ
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hpacket, ?_⟩
  exact ambient_parameterDerivative_lift_of_solution_facts c₀ g ht he hr hEU hleft β hG
    hT hTρ hρδ u gforce hpacket hlift


private theorem ambient_sobolev_solution_exists_with_parameterDerivative_lift :
    ambientSobolevSolutionWithParameterDerivativeLift c₀ g ht he hr hEU hleft β hG := by
  obtain ⟨δ, hδ, _, _, hlift⟩ :=
    ambient_parameterDerivative_forcing_lift_of_small_state c₀ g ht he hr hEU hleft β hG
  exact ambient_sobolev_solution_exists_with_parameterDerivative_lift_of_radius
    c₀ g ht he hr hEU hleft β hG hδ hlift

private def ambientSobolevFourthOrderLift
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) : Prop :=
  ∃ field₄ : timeL2 (CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2)) T,
    (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2))).compLpL
          2 (timeMeasure T) field₄ =
      maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce

private theorem ambient_fourth_order_lift_of_parameterDerivative_lift
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hlift : parameterDerivativeForcingFieldLift g₀ hT gforce) :
    ambientSobolevFourthOrderLift g₀ hT gforce := by
  rcases hlift with ⟨FH, _, hfield⟩
  let U := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
    (a := ((1 : ℕ) : ℝ)) hT 0 gforce
  let V := heatDuhamelVectorField (g := g₀) (r := 0) (s := 0)
    (a := ((1 : ℕ) : ℝ)) hT 0 FH
  let Dh : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 2) := parameterDerivativeHighField g₀
  let J₂ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2))
  change Dh.compLpL 2 (timeMeasure T) U = J₂.compLpL 2 (timeMeasure T) V at hfield
  apply AddCircle.exists_timeL2_tensorHsInclusion_eq_of_parameterDerivative_lift
    g₀ 1 (σ := ((0 : ℕ) : ℝ) + 2) (by norm_num) U V
  filter_upwards [Dh.coeFn_compLpL U, J₂.coeFn_compLpL V] with t hDh hJ
  intro i
  have ht : Dh (U t) = J₂ (V t) := by
    rw [← hDh, ← hJ]
    exact congrArg (fun z : timeL2 (CircleHsPi g₀ (Fin n) (((0 : ℕ) : ℝ) + 2)) T => z t) hfield
  have hi := congrArg (fun z => z i) ht
  simpa only [Dh, J₂, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.piLpMap_apply, AddCircle.parameterDerivativeHsPi_apply] using hi

private def ambientSobolevSolutionWithFourthOrderLift : Prop :=
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ C.radius ∧ ρ ≤ 1 ∧
    ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
      ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
        (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
        ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
          parameterDerivativeForcingFieldLift g₀ hT gforce ∧
          ambientSobolevFourthOrderLift g₀ hT gforce

private theorem ambient_sobolev_solution_exists_with_fourth_order_lift :
    ambientSobolevSolutionWithFourthOrderLift c₀ g ht he hr hEU hleft β hG := by
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift⟩ :=
    ambient_sobolev_solution_exists_with_parameterDerivative_lift
      c₀ g ht he hr hEU hleft β hG
  exact ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift,
    ambient_fourth_order_lift_of_parameterDerivative_lift
      (c₀.pullbackMetric (g 0)) hT gforce hlift⟩

private theorem ambient_spatial_contDiff_two_of_parameterDerivative_forcing_lift
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hlift : parameterDerivativeForcingFieldLift g₀ hT gforce) :
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let u := maximalRegularityDuhamelVectorMap (g := g₀) (r := 0) (s := 0)
      (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t))
      (x : AddCircle (1 : ℝ))
    (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (f t)) ∧
      ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (f p.1)) p.2) (Icc 0 T ×ˢ univ) := by
  intro P u S f
  obtain ⟨FH, hFH, _⟩ := hlift
  obtain ⟨w, hw, hwlo, _⟩ :=
    exists_continuousOn_representative_of_parameterDerivative_forcing_lift g₀ 0 hT gforce FH hFH
  have h := AddCircle.contDiff_and_continuousOn_iteratedDeriv_scalarH1PiToContinuous
    g₀ 2 (fun t => P f₀ + S (u.toFun t))
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)) (f₀ + w t))
    ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))).continuous.comp_continuousOn
      (continuousOn_const.add hw)) (fun t ht => by
      apply PiLp.ext
      intro i
      simp only [ContinuousLinearMap.piLpMap_apply, PiLp.add_apply,
        ← tensorHsInclusion_trans_apply, map_add]
      change _ = (P f₀) i + (S (u.toFun t)) i
      congr 1
      have hwi := congrArg (fun z => z i) (hwlo t ht)
      have hwi' := congrArg (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))) hwi
      simpa only [S, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
        ← tensorHsInclusion_trans_apply] using hwi')
  simpa only [f, iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat] using h

private theorem ambient_sobolev_solution_exists_with_contDiff_two :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ C.radius ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
            parameterDerivativeForcingFieldLift g₀ hT gforce ∧
            ambientSobolevFourthOrderLift g₀ hT gforce ∧
            let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t))
              (x : AddCircle (1 : ℝ))
            (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (f t)) ∧
              ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (f p.1)) p.2) (Icc 0 T ×ˢ univ) := by
  intro C g₀ f₀ P S
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hfour⟩ :=
    ambient_sobolev_solution_exists_with_fourth_order_lift c₀ g ht he hr hEU hleft β hG
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hfour, ?_⟩
  rw [hfacts.1]
  exact ambient_spatial_contDiff_two_of_parameterDerivative_forcing_lift g₀ hT f₀ gforce hlift


private theorem circleHsPi_eq_of_inclusion_eq
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (v : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (V : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (h : circleHsPiInclusion g₀ (Fin n) (by linarith :
        ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) v =
      circleHsPiInclusion g₀ (Fin n) (by linarith :
        ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2) V) :
    v = circleHsPiInclusion g₀ (Fin n) (by linarith :
      ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2) V := by
  apply PiLp.ext
  intro i
  apply tensorHsInclusion_injective
    (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
  have hi := congrArg (fun z => z i) h
  simpa only [circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
    ← tensorHsInclusion_trans_apply] using hi

private theorem scalarVectorTimeCoefficients_rhs_continuousOn
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    {T : ℝ}
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T)) :
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ C.radius) →
      let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall C.radius_pos.le C.diffusion t (J (K (W t))))
      let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall C.radius_pos.le C.reaction t (J (K (W t))))
      ContinuousOn (fun t => m (alpha t) (Q (f₀ + W t)) + reaction t) (Icc 0 T) := by
  intro K Q m hJW alpha reaction
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1)) C.radius := fun t =>
    ⟨J (K (W t)), by simpa only [Metric.mem_closedBall, dist_zero_right] using hJW t t.2⟩
  have hz : Continuous z :=
    (J.continuous.comp (K.continuous.comp
      (continuousOn_iff_continuous_domRestrict.mp hW))).subtype_mk _
  have halpha : ContinuousOn alpha (Icc 0 T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ((tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))).continuous.comp
        (C.diffusion_lipschitz.continuous.comp (continuous_subtype_val.prodMk hz))).congr
    intro t
    change tensorHsCongrL g₀ 0 0 _ (C.diffusion t (z t)) =
      tensorHsCongrL g₀ 0 0 _ (extendClosedBall _ C.diffusion t (J (K (W t))))
    exact congrArg (tensorHsCongrL g₀ 0 0 _) (extendClosedBall_apply
      C.radius_pos.le C.diffusion t (J (K (W t))) (z t).2).symm
  have hreaction : ContinuousOn reaction (Icc 0 T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ((circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))).continuous.comp
        (C.reaction_lipschitz.continuous.comp (continuous_subtype_val.prodMk hz))).congr
    intro t
    change circleHsPiCongr g₀ (Fin n) _ (C.reaction t (z t)) =
      circleHsPiCongr g₀ (Fin n) _ (extendClosedBall _ C.reaction t (J (K (W t))))
    exact congrArg (circleHsPiCongr g₀ (Fin n) _) (extendClosedBall_apply
      C.radius_pos.le C.reaction t (J (K (W t))) (z t).2).symm
  have hRHS : ContinuousOn (fun t => m (alpha t) (Q (f₀ + W t)) + reaction t) (Icc 0 T) :=
    ((m.continuous.comp_continuousOn halpha).clm_apply
      (Q.continuous.comp_continuousOn (continuousOn_const.add hW))).add hreaction
  exact hRHS

private def scalarVectorClassicalTimeEquation
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    {ρ T : ℝ} (hT : 0 < T)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) : Prop :=
    let K := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let K₀ := circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    ∃ W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2),
      ContinuousOn W (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, K₀ (W t) = u.toFun t) ∧
      W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce ∧
      (∀ t ∈ Icc 0 T, ‖K (W t)‖ ≤ ρ) ∧
      (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ C.radius) ∧
      let alpha := fun t => tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall C.radius_pos.le C.diffusion t (J (K (W t))))
      let reaction := fun t => circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall C.radius_pos.le C.reaction t (J (K (W t))))
      ContinuousOn (fun t => m (alpha t) (Q (f₀ + W t)) + reaction t) (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt u.toFun
        (m (alpha t) (Q (f₀ + W t)) + reaction t) (Icc 0 T) t

private theorem scalarVectorTimeCoefficients_hasDerivWithinAt_of_parameterDerivative_lift
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    {ρ T : ℝ} (hT : 0 < T)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (J : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →L[ℝ]
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T) :
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ (1 : ℕ)
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ (1 : ℕ) (by norm_num))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField hT 0 gforce
    u = maximalRegularityDuhamelVectorMap hT 0 gforce →
    parameterDerivativeForcingFieldLift g₀ hT gforce →
    ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
    (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
      (by linarith : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (w t) = u.toFun t) →
    (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) →
    (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ C.radius) →
    (∀ᵐ t ∂timeMeasure T,
      L (field t) + gforce t =
        m (tensorHsCongrL g₀ 0 0
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall C.radius_pos.le C.diffusion t (J (w t))))
          (Q (f₀ + field t)) +
        circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall C.radius_pos.le C.reaction t (J (w t)))) →
    scalarVectorClassicalTimeEquation (ρ := ρ) g₀ F G S u₀ C hT f₀ J u gforce := by
  intro Q m L field hu hlift w hwlow hwbound hJ heq
  let K := circleHsPiInclusion g₀ (Fin n)
    (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
  let K₀ := circleHsPiInclusion g₀ (Fin n)
    (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
  change ∃ W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2), _
  rcases hlift with ⟨FH, hFH, _⟩
  obtain ⟨W, hW, hWlow, hWfield⟩ :=
    exists_continuousOn_representative_of_parameterDerivative_forcing_lift
      g₀ 0 hT gforce FH hFH
  have hWlow' : ∀ t ∈ Icc 0 T, K₀ (W t) = u.toFun t := by
    intro t htt
    rw [hu]
    exact hWlow t htt
  have hwW (t : ℝ) (htt : t ∈ Icc 0 T) : w t = K (W t) :=
    circleHsPi_eq_of_inclusion_eq g₀ (w t) (W t)
      ((hwlow t htt).trans (hWlow' t htt).symm)
  have hJW (t : ℝ) (htt : t ∈ Icc 0 T) : ‖J (K (W t))‖ ≤ C.radius := by
    rw [← hwW t htt]
    exact hJ t htt
  refine ⟨W, hW, hWlow', hWfield, ?_, hJW, ?_⟩
  · intro t htt
    rw [← hwW t htt]
    exact hwbound t htt
  intro alpha reaction
  have hRHS : ContinuousOn (fun t => m (alpha t) (Q (f₀ + W t)) + reaction t) (Icc 0 T) :=
    scalarVectorTimeCoefficients_rhs_continuousOn g₀ _ _ _ _ C f₀ J W hW hJW
  refine ⟨hRHS, ?_⟩
  have hder : u.deriv = L.compLpL 2 (timeMeasure T) field + gforce := by
    rw [hu]
    exact maximalRegularityDuhamelVectorMap_timeDeriv_eq hT
      (tensorResolventL2_isCompactOperator
        (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g₀ 0 0) 0 gforce
  have hrep : u.deriv =ᵐ[timeMeasure T]
      (fun t => m (alpha t) (Q (f₀ + W t)) + reaction t) := by
    rw [hder]
    filter_upwards [Lp.coeFn_add (L.compLpL 2 (timeMeasure T) field) gforce,
      L.coeFn_compLpL field, heq, hWfield, ae_restrict_mem measurableSet_Icc]
      with t hadd hL htEq htW htmem
    rw [hadd, Pi.add_apply, hL, htEq, ← htW]
    change m _ (Q (f₀ + W t)) + _ = m _ (Q (f₀ + W t)) + _
    rw [hwW t htmem]
  intro t htt
  exact u.hasDerivWithinAt_toFun_of_continuousOn hRHS hrep htt

private theorem ambientCoefficients_eval_of_sobolev_representative
    {ρ T : ℝ} (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) (((1 : ℕ) : ℝ) + 1)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F := fun t (x : ℝ) => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    let alpha := fun t => tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (w t)))
    let reaction := fun t => circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))
    (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
      (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by norm_num) (w t) = u.toFun t) →
    (∀ t ∈ Icc 0 T, ‖J (w t)‖ ≤ ScalarVectorTimeCoefficients.radius C) →
    ∀ t ∈ Icc 0 T, ∀ x : ℝ,
      let q := (t, F t x, deriv (F t) x)
      q ∈ curveShorteningChartFirstJetDomain D
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∧
      scalarH1ToContinuous g₀
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) (alpha t))
        (x : AddCircle (1 : ℝ)) = curveShorteningChartDiffusionCoefficient
          (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β q ∧
      WithLp.toLp 2 (scalarH1PiToContinuous g₀ (S (reaction t))
        (x : AddCircle (1 : ℝ))) = curveShorteningParametricChartReaction
          (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β q := by
  intro C g₀ f₀ J P S F alpha reaction hwu hJ t htt x
  have hcoeff {a b : ℝ} (hab : a = b) (z : TensorHs g₀ 0 0 a) :
      (tensorHsCongr g₀ 0 0 hab z).coeff = z.coeff := by
    cases hab
    rfl
  let w₂ := circleHsPiCongr g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) (w t)
  have hv : J (w t) ∈ Metric.closedBall 0 (ScalarVectorTimeCoefficients.radius C) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hJ t htt
  let v : Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
      (ScalarVectorTimeCoefficients.radius C) := ⟨J (w t), hv⟩
  have hvJ : v.val = circleFirstJet g₀ w₂ := rfl
  have htime : t ∈ Icc 0 (ScalarVectorTimeCoefficients.radius C) :=
    ⟨htt.1, htt.2.trans (hTρ.trans hρC)⟩
  have hgeom := ambientCoefficients_eval_of_eq_circleFirstJet
    c₀ g ht he hr hEU hleft β hG t htime w₂ v hvJ x
  have hF : F t = fun y : ℝ => e (c₀.map (y : AddCircle (1 : ℝ))) +
      WithLp.toLp 2 (fun i => scalarH1ToContinuous g₀
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 1 + 1) (w₂ i))
        (y : AddCircle (1 : ℝ))) := by
    funext y
    apply PiLp.ext
    intro i
    change scalarH1ToContinuous g₀ ((P f₀ + S (u.toFun t)) i)
      (y : AddCircle (1 : ℝ)) = _
    rw [PiLp.add_apply, map_add, ContinuousMap.add_apply]
    congr 1
    · exact scalarH1ToContinuous_ambientSobolev c₀ (g 0) e he (by norm_num) _ i
    · rw [← hwu t htt]
      apply congrArg (fun z => scalarH1ToContinuous g₀ z (y : AddCircle (1 : ℝ)))
      apply TensorHs.ext
      simp only [S, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
        tensorHsInclusion_coeff, w₂, circleHsPiCongr_apply, tensorHsCongrL_apply, hcoeff]
  change (t, F t x, deriv (F t) x) ∈ _ ∧ _ ∧ _
  have hgeom' : (t, F t x, deriv (F t) x) ∈ curveShorteningChartFirstJetDomain D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β ∧
    scalarH1ToContinuous g₀ (ScalarVectorTimeCoefficients.diffusion C t v)
      (x : AddCircle (1 : ℝ)) = curveShorteningChartDiffusionCoefficient
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β (t, F t x, deriv (F t) x) ∧
    ∀ j, scalarH1ToContinuous g₀ (ScalarVectorTimeCoefficients.reaction C t v j)
      (x : AddCircle (1 : ℝ)) = curveShorteningParametricChartReaction
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
          (t, F t x, deriv (F t) x) j := by
    simpa only [hF] using hgeom
  refine ⟨hgeom'.1, ?_, ?_⟩
  · rw [← hgeom'.2.1]
    apply congrArg (fun z => scalarH1ToContinuous g₀ z (x : AddCircle (1 : ℝ)))
    apply TensorHs.ext
    simp only [alpha, extendClosedBall_apply _ _ _ _ hv,
      tensorHsInclusion_coeff, tensorHsCongrL_apply, hcoeff, v]
  · apply PiLp.ext
    intro i
    rw [← hgeom'.2.2 i]
    change scalarH1ToContinuous g₀ ((S (reaction t)) i) (x : AddCircle (1 : ℝ)) = _
    apply congrArg (fun z => scalarH1ToContinuous g₀ z (x : AddCircle (1 : ℝ)))
    apply TensorHs.ext
    simp only [reaction, extendClosedBall_apply _ _ _ _ hv, S, circleHsPiInclusion,
      ContinuousLinearMap.piLpMap_apply, circleHsPiCongr_apply,
      tensorHsInclusion_coeff, tensorHsCongrL_apply, hcoeff, v]

private theorem ambient_firstJet_mem_of_sobolev_solution_facts
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F := fun t (x : ℝ) => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    ∀ t ∈ Icc 0 T, ∀ x : ℝ, (t, F t x, deriv (F t) x) ∈
      curveShorteningChartFirstJetDomain D
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β := by
  intro g₀ f₀ P S F t htt x
  rcases hfacts with ⟨_, _, _, _, _, _, _, w, _, hwu, _, _, _, hJ, _, _⟩
  exact (ambientCoefficients_eval_of_sobolev_representative c₀ g ht he hr hEU hleft β hG
    hTρ hρC u w hwu hJ t htt x).1

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambient_first_order_regular_of_sobolev_representative
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {T : ℝ}
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric g) (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi (c₀.pullbackMetric g) (Fin n) (((1 : ℕ) : ℝ) + 1))
    (hw : ContinuousOn w (Icc 0 T))
    (hwu : ∀ t ∈ Icc 0 T, circleHsPiInclusion (c₀.pullbackMetric g) (Fin n)
      (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by norm_num) (w t) = u.toFun t)
    (hu₀ : u.toFun 0 = 0) :
    let g₀ := c₀.pullbackMetric g
    let f₀ := ambientSobolev c₀ g e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F := fun t (x : ℝ) => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    (∀ t, Function.Periodic (F t) 1) ∧
      ContinuousOn (fun p : ℝ × ℝ => F p.2 p.1) (Icc 0 1 ×ˢ Icc 0 T) ∧
      ContinuousOn (fun p : ℝ × ℝ => deriv (F p.2) p.1) (Icc 0 1 ×ˢ Icc 0 T) ∧
      ∀ x, F 0 x = e (c₀.map (x : AddCircle (1 : ℝ))) := by
  intro g₀ f₀ P S F
  let f := fun t (x : ℝ) =>
    scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ))
  let K := circleHsPiInclusion g₀ (Fin n)
    (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
  have h := AddCircle.contDiff_and_continuousOn_iteratedDeriv_scalarH1PiToContinuous
    g₀ 1 (fun t => P f₀ + S (u.toFun t)) (fun t => K f₀ + w t)
    (continuousOn_const.add hw) (fun t ht => by
      apply PiLp.ext
      intro i
      simp only [ContinuousLinearMap.piLpMap_apply, PiLp.add_apply, map_add]
      change _ = (P f₀) i + (S (u.toFun t)) i
      apply congrArg₂ (· + ·)
      · exact (tensorHsInclusion_trans_apply
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
          (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2) (f₀ i)).symm
      · have hi := congrArg (fun z => z i) (hwu t ht)
        have hi' := congrArg (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))) hi
        simpa only [S, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
          ← tensorHsInclusion_trans_apply] using hi')
  have hf : ∀ t ∈ Icc 0 T, ContDiff ℝ 1 (f t) := h.1
  have hd : ContinuousOn (fun p : ℝ × ℝ => deriv (f p.1) p.2) (Icc 0 T ×ˢ univ) := by
    simpa only [f, iteratedDeriv_succ, iteratedDeriv_zero] using h.2
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have hder (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) :
      deriv (F t) x = L (deriv (f t) x) := by
    exact ((PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (f t x)).comp_hasDerivAt x
      ((hf t ht).differentiable (by norm_num) x).hasDerivAt).deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t x
    simp only [F, AddCircle.coe_add_period]
  · apply L.continuous.comp_continuousOn
    have hstate : ContinuousOn (fun t => P f₀ + S (u.toFun t)) (Icc 0 T) :=
      continuousOn_const.add (S.continuous.comp_continuousOn u.continuousOn_toFun)
    exact (((scalarH1PiToContinuous g₀).continuous.comp_continuousOn hstate).comp
      continuousOn_snd (fun _ hp => hp.2)).eval
        ((AddCircle.continuous_mk' 1).comp continuous_fst).continuousOn
  · have hswap : ContinuousOn (fun p : ℝ × ℝ => (p.2, p.1))
        (Icc 0 1 ×ˢ Icc 0 T) := continuousOn_snd.prodMk continuousOn_fst
    have hd' := L.continuous.comp_continuousOn
      (hd.comp hswap (fun _ hp => ⟨hp.2, mem_univ _⟩))
    apply hd'.congr
    intro p hp
    exact hder p.2 hp.2 p.1
  · intro x
    simp only [F, hu₀, map_zero, add_zero]
    apply PiLp.ext
    intro i
    exact congrArg (fun z => z i)
      (scalarH1PiToContinuous_ambientSobolev c₀ g e he
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2) (x : AddCircle (1 : ℝ)))

private theorem ambient_classical_time_equation_of_parameterDerivative_lift
    {ρ T : ℝ} (hT : 0 < T)
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    scalarVectorClassicalTimeEquation (ρ := ρ) g₀ _ _ _ _ C hT f₀ J u gforce := by
  intro C g₀ f₀ J
  rcases hfacts with ⟨hu, _, _, _, _, _, _, w,
    _, hwlow, _, hwbound, _, hJ, heq, _⟩
  exact scalarVectorTimeCoefficients_hasDerivWithinAt_of_parameterDerivative_lift
    g₀ _ _ _ _ C hT f₀ J u gforce hu hlift w hwlow hwbound
    (by simpa only [C, g₀, J] using hJ)
    (by simpa only [C, g₀, f₀, J] using heq)

private theorem ambient_chart_equation_of_parameterDerivative_lift
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    ∀ t ∈ Icc 0 T, ∀ x : ℝ, HasDerivWithinAt (fun τ => F τ x)
      (curveShorteningParametricChartRhs
        (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β
        (t, F t x, deriv (F t) x, deriv (deriv (F t)) x)) (Icc 0 T) t := by
  intro g₀ f₀ P S F
  let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let K := circleHsPiInclusion g₀ (Fin n)
    (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
  let K₀ := circleHsPiInclusion g₀ (Fin n)
    (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
  have hresult := ambient_classical_time_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT u gforce hfacts hlift
  obtain ⟨W, _, hWlo, _, _, hJW, htime⟩ := hresult
  let alpha := fun t => tensorHsCongrL g₀ 0 0
    (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))
  let reaction := fun t => circleHsPiCongr g₀ (Fin n)
    (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))
  have hlink (t : ℝ) (htt : t ∈ Icc 0 T) :
      K₀ (f₀ + W t) = K₀ f₀ + u.toFun t := by rw [map_add, hWlo t htt]
  have hclassical := hasDerivWithinAt_of_circle_sobolev_equation g₀ u.toFun
    (fun t => f₀ + W t) (K₀ f₀) alpha reaction hlink htime.2
  have hwlow (t : ℝ) (htt : t ∈ Icc 0 T) :
      circleHsPiInclusion g₀ (Fin n)
        (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 by norm_num) (K (W t)) = u.toFun t := by
    rw [← hWlo t htt]
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply (by norm_num) (by norm_num) (W t i)).symm
  have hcoeff := ambientCoefficients_eval_of_sobolev_representative
    c₀ g ht he hr hEU hleft β hG hTρ hρC u (fun t => K (W t)) hwlow hJW
  let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t))
    (x : AddCircle (1 : ℝ))
  have hlo (t : ℝ) : S (K₀ f₀ + u.toFun t) = P f₀ + S (u.toFun t) := by
    rw [map_add]
    congr 1
  have hc : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (f t) ∧ ∀ x : ℝ,
      HasDerivWithinAt (fun τ => f τ x)
        (scalarH1ToContinuous g₀
          (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) (alpha t))
            (x : AddCircle (1 : ℝ)) • deriv (deriv (f t)) x +
          scalarH1PiToContinuous g₀ (S (reaction t)) (x : AddCircle (1 : ℝ))) (Icc 0 T) t := by
    dsimp only [f]
    simp_rw [← hlo]
    exact hclassical
  intro t htt x
  let L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap
  have hd (q : ℝ → (Fin n → ℝ)) (hq : Differentiable ℝ q) :
      deriv (fun y => L (q y)) = fun y => L (deriv q y) := by
    funext y
    exact (L.hasFDerivAt.comp_hasDerivAt y (hq y).hasDerivAt).deriv
  have hf' : ContDiff ℝ 1 (deriv (f t)) := (hc t htt).1.deriv'
  have hsecond : deriv (deriv (F t)) x = L (deriv (deriv (f t)) x) := by
    change deriv (deriv (fun y => L (f t y))) x = _
    rw [hd (f t) ((hc t htt).1.differentiable (by norm_num))]
    rw [hd (deriv (f t)) (hf'.differentiable (by norm_num))]
  have hh := L.hasFDerivAt.comp_hasDerivWithinAt t ((hc t htt).2 x)
  have hdiff := (hcoeff t htt x).2.1
  have hreact := (hcoeff t htt x).2.2
  have hh' : HasDerivWithinAt (fun τ => F τ x)
      (scalarH1ToContinuous g₀
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) (alpha t))
          (x : AddCircle (1 : ℝ)) • deriv (deriv (F t)) x +
        WithLp.toLp 2 (scalarH1PiToContinuous g₀ (S (reaction t))
          (x : AddCircle (1 : ℝ)))) (Icc 0 T) t := by
    rw [hsecond]
    change HasDerivWithinAt (fun τ => L (f τ x))
      (_ • L (deriv (deriv (f t)) x) +
        L (scalarH1PiToContinuous g₀ (S (reaction t)) (x : AddCircle (1 : ℝ))))
      (Icc 0 T) t
    simpa only [map_add, map_smul, Function.comp_def] using hh
  rw [hdiff, hreact] at hh'
  exact hh'

private theorem ambient_mem_range_of_parameterDerivative_lift [I.Boundaryless]
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    ∀ t ∈ Icc 0 T, ∀ x : ℝ, F t x ∈ range e := by
  intro g₀ f₀ P S F
  have hchart := ambient_chart_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hjet := ambient_firstJet_mem_of_sobolev_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  have hspatial := ambient_spatial_contDiff_two_of_parameterDerivative_forcing_lift
    g₀ hT f₀ gforce hlift
  have hu := hfacts.1
  rw [← hu] at hspatial
  rcases hfacts with ⟨_, _, _, _, _, _, _, w, hw, hwu, _, _, hw₀, _, _, _⟩
  have hu₀ : u.toFun 0 = 0 := by
    rw [← hwu 0 ⟨le_rfl, hT.le⟩, hw₀, map_zero]
  obtain ⟨hper, hcont, hDu, hinit⟩ :=
    ambient_first_order_regular_of_sobolev_representative c₀ (g 0) he u w hw hwu hu₀
  change ∀ t, Function.Periodic (F t) 1 at hper
  change ContinuousOn (fun p : ℝ × ℝ => F p.2 p.1) (Icc 0 1 ×ˢ Icc 0 T) at hcont
  change ContinuousOn (fun p : ℝ × ℝ => deriv (F p.2) p.1) (Icc 0 1 ×ˢ Icc 0 T) at hDu
  change ∀ x, F 0 x = e (c₀.map (x : AddCircle (1 : ℝ))) at hinit
  let L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap
  have hx (x t : ℝ) (htt : t ∈ Ioo 0 T) : ContDiffAt ℝ 2 (F t) x := by
    exact (L.contDiff.comp (hspatial.1 t ⟨htt.1.le, htt.2.le⟩)).contDiffAt
  have hrange := periodic_mem_range_of_retraction_equation_of_firstJet_mem
    g he hr hG hEU hleft β (u := fun x t => F t x) hT (fun x t => hper t x) hcont
    (fun x => by rw [hinit x]; exact mem_range_self _) hx hDu
    (fun x t htt => hjet t htt x)
    (fun x t htt => (hchart t ⟨htt.1.le, htt.2.le⟩ x).hasDerivAt
      (Icc_mem_nhds htt.1 htt.2))
  intro t htt x
  exact hrange x t htt

private theorem ambient_sobolev_solution_exists_with_mem_range [I.Boundaryless] :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ScalarVectorTimeCoefficients.radius C ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
            parameterDerivativeForcingFieldLift g₀ hT gforce ∧
            ambientSobolevFourthOrderLift g₀ hT gforce ∧
            let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t))
              (x : AddCircle (1 : ℝ))
            (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (f t)) ∧
              ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (f p.1)) p.2) (Icc 0 T ×ˢ univ) ∧
              ∀ t ∈ Icc 0 T, ∀ x : ℝ, WithLp.toLp 2 (f t x) ∈ range e := by
  intro C g₀ f₀ P S
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hfour, hc, hd⟩ :=
    ambient_sobolev_solution_exists_with_contDiff_two c₀ g ht he hr hEU hleft β hG
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hfour, hc, hd, ?_⟩
  exact ambient_mem_range_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift


private theorem ambient_retraction_contMDiff_two_and_immersed_of_parameterDerivative_lift
    [I.Boundaryless] {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
    let c : CurveMap M := fun z t => r (d z t)
    (∀ z, c z 0 = c₀.map z) ∧
      (∀ z t, t ∈ Icc 0 T → e (c z t) = d z t) ∧
      (∀ t ∈ Icc 0 T, ContMDiff 𝓘(ℝ, ℝ) I 2 (fun x : ℝ => c.lift x t)) ∧
      c.ImmersedOn (I := I) (Icc 0 T) := by
  intro g₀ f₀ P S d c
  have himage := ambient_mem_range_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hjet := ambient_firstJet_mem_of_sobolev_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  have hspatial := ambient_spatial_contDiff_two_of_parameterDerivative_forcing_lift
    g₀ hT f₀ gforce hlift
  have hu := hfacts.1
  rw [← hu] at hspatial
  rcases hfacts with ⟨_, _, _, _, _, _, _, w, hw, hwu, _, _, hw₀, _, _, _⟩
  have hu₀ : u.toFun 0 = 0 := by
    rw [← hwu 0 ⟨le_rfl, hT.le⟩, hw₀, map_zero]
  obtain ⟨_, _, _, hinit⟩ :=
    ambient_first_order_regular_of_sobolev_representative c₀ (g 0) he u w hw hwu hu₀
  change ∀ x : ℝ, d (x : AddCircle (1 : ℝ)) 0 = e (c₀.map (x : AddCircle (1 : ℝ))) at hinit
  have hrange (z : AddCircle (1 : ℝ)) (t : ℝ) (htt : t ∈ Icc 0 T) : d z t ∈ range e := by
    induction z using QuotientAddGroup.induction_on with
    | H x => exact himage t htt x
  have hce (z : AddCircle (1 : ℝ)) (t : ℝ) (htt : t ∈ Icc 0 T) : e (c z t) = d z t := by
    obtain ⟨p, hp⟩ := hrange z t htt
    change e (r (d z t)) = d z t
    rw [← hp, hleft]
  let L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap
  have hd (t : ℝ) (htt : t ∈ Icc 0 T) :
      ContDiff ℝ 2 (fun x : ℝ => d.lift x t) :=
    L.contDiff.comp (hspatial.1 t htt)
  have hc (t : ℝ) (htt : t ∈ Icc 0 T) :
      ContMDiff 𝓘(ℝ, ℝ) I 2 (fun x : ℝ => c.lift x t) :=
    (hr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp_contMDiff
      (hd t htt).contMDiff (fun x => hEU (hrange (x : AddCircle (1 : ℝ)) t htt))
  refine ⟨?_, hce, hc, ?_⟩
  · intro z
    induction z using QuotientAddGroup.induction_on with
    | H x => change r (d (x : AddCircle (1 : ℝ)) 0) = _; rw [hinit x, hleft]
  · intro x t htt hzero
    have hdne : deriv (fun y => d.lift y t) x ≠ 0 := by
      have hpos := (hjet t htt x).2.2
      let B := TensorSpectral.chartGramBilin (Geometry.Riemannian.retractionMetric (g t) he hr) β
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β).symm (d.lift x t))
      change 0 < B (deriv (fun y => d.lift y t) x) (deriv (fun y => d.lift y t) x) at hpos
      intro h
      rw [h, map_zero] at hpos
      exact lt_irrefl _ hpos
    have hcomp := mfderiv_comp_apply x (he.mdifferentiableAt (by simp))
      ((hc t htt).mdifferentiableAt (by norm_num)) (1 : ℝ)
    have heq : (fun y : ℝ => e (c.lift y t)) = fun y => d.lift y t :=
      funext (fun y => hce (y : AddCircle (1 : ℝ)) t htt)
    change e ∘ (fun y : ℝ => c.lift y t) = (fun y => d.lift y t) at heq
    rw [heq, mfderiv_eq_fderiv] at hcomp
    change deriv (fun y => d.lift y t) x =
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e (c.lift x t) (c.X (I := I) x t) at hcomp
    rw [hzero, map_zero] at hcomp
    exact hdne hcomp

private theorem ambient_contDiffOn_one_of_parameterDerivative_lift
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    ContDiffOn ℝ 1 (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set ℝ)) := by
  intro g₀ f₀ P S F
  have hchart := ambient_chart_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hjet := ambient_firstJet_mem_of_sobolev_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  have hspatial := ambient_spatial_contDiff_two_of_parameterDerivative_forcing_lift
    g₀ hT f₀ gforce hlift
  rw [← hfacts.1] at hspatial
  rcases hfacts with ⟨_, _, _, _, _, _, _, w, hw, hwu, _, _, hw₀, _, _, _⟩
  let L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap
  let f := fun t (x : ℝ) => scalarH1PiToContinuous g₀
    (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ))
  change (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (f t)) ∧
    ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (f p.1)) p.2) (Icc 0 T ×ˢ univ) at hspatial
  have hd (q : ℝ → (Fin n → ℝ)) (hq : Differentiable ℝ q) :
      deriv (fun y => L (q y)) = fun y => L (deriv q y) := by
    funext y
    exact (L.hasFDerivAt.comp_hasDerivAt y (hq y).hasDerivAt).deriv
  have hFd (t : ℝ) (htt : t ∈ Icc 0 T) :
      deriv (F t) = fun y => L (deriv (f t) y) :=
    hd (f t) ((hspatial.1 t htt).differentiable (by norm_num))
  have hFdd (t : ℝ) (htt : t ∈ Icc 0 T) :
      deriv (deriv (F t)) = fun y => L (deriv (deriv (f t)) y) := by
    rw [hFd t htt]
    exact hd (deriv (f t)) (show Differentiable ℝ (deriv (f t)) from
      (show ContDiff ℝ 1 (deriv (f t)) from (hspatial.1 t htt).deriv').differentiable (by norm_num))
  let K := circleHsPiInclusion g₀ (Fin n)
    (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
  have hfirst := AddCircle.contDiff_and_continuousOn_iteratedDeriv_scalarH1PiToContinuous
    g₀ 1 (fun t => P f₀ + S (u.toFun t)) (fun t => K f₀ + w t)
    (continuousOn_const.add hw) (fun t htt => by
      apply PiLp.ext
      intro i
      simp only [ContinuousLinearMap.piLpMap_apply, PiLp.add_apply, map_add]
      change _ = (P f₀) i + (S (u.toFun t)) i
      apply congrArg₂ (· + ·)
      · exact (tensorHsInclusion_trans_apply
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
          (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2) (f₀ i)).symm
      · have hi := congrArg (fun z => z i) (hwu t htt)
        have hi' := congrArg (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))) hi
        simpa only [S, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
          ← tensorHsInclusion_trans_apply] using hi')
  have hC0 : ContinuousOn (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set ℝ)) := by
    apply L.continuous.comp_continuousOn
    have hstate : ContinuousOn (fun t => P f₀ + S (u.toFun t)) (Icc 0 T) :=
      continuousOn_const.add (S.continuous.comp_continuousOn u.continuousOn_toFun)
    exact (((scalarH1PiToContinuous g₀).continuous.comp_continuousOn hstate).comp
      continuousOn_fst (fun _ hp => hp.1)).eval
        ((AddCircle.continuous_mk' 1).comp continuous_snd).continuousOn
  have hDx : ContinuousOn (fun p : ℝ × ℝ => deriv (F p.1) p.2)
      (Icc 0 T ×ˢ (univ : Set ℝ)) := by
    have hh : ContinuousOn (fun p : ℝ × ℝ => deriv (f p.1) p.2)
        (Icc 0 T ×ˢ (univ : Set ℝ)) := by
      simpa only [f, iteratedDeriv_succ, iteratedDeriv_zero] using hfirst.2
    apply (L.continuous.comp_continuousOn hh).congr
    intro p hp
    exact congrFun (hFd p.1 hp.1) p.2
  have hDxx : ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (F p.1)) p.2)
      (Icc 0 T ×ˢ (univ : Set ℝ)) := by
    apply (L.continuous.comp_continuousOn (hspatial.2.mono
      (fun p hp => ⟨hp.1, mem_univ _⟩))).congr
    intro p hp
    exact congrFun (hFdd p.1 hp.1) p.2
  apply contDiffOn_one_of_parametric_chart_equation hG β (hab := hT) (hV := isOpen_univ)
    hC0 (fun t htt => (L.contDiff.comp (hspatial.1 t htt)).differentiable (by norm_num) |>.differentiableOn) hDx hDxx
  · intro t ht x hx
    exact hjet t ht x
  · intro t ht x hx
    exact hchart t ht x

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
private theorem contMDiffOn_retraction_of_contDiffOn
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (d : CurveMap (EuclideanSpace ℝ (Fin n))) (J : Set ℝ)
    (hd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => d.lift p.2 p.1) (J ×ˢ univ))
    (hmap : ∀ x t, t ∈ J → d.lift x t ∈ (U : Set (EuclideanSpace ℝ (Fin n)))) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun p : ℝ × ℝ => r (d.lift p.1 p.2)) (univ ×ˢ J) := by
  have hswap : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (p.2, p.1)) (univ ×ˢ J) :=
    contDiffOn_snd.prodMk contDiffOn_fst
  have hd' : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => d.lift p.1 p.2) (univ ×ˢ J) :=
    hd.comp hswap (fun _ hp => ⟨hp.2, hp.1⟩)
  exact (hr.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp hd'.contMDiffOn
    (fun p hp => hmap p.1 p.2 hp.2)

private theorem ambient_retraction_contMDiffOn_one_of_parameterDerivative_lift
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
    let c : CurveMap M := fun z t => r (d z t)
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun p : ℝ × ℝ => c.lift p.1 p.2)
      (univ ×ˢ Icc 0 T) := by
  intro g₀ f₀ P S d c
  have hjoint : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => d.lift p.2 p.1)
      (Icc 0 T ×ˢ univ) :=
    ambient_contDiffOn_one_of_parameterDerivative_lift
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hjet : ∀ t ∈ Icc 0 T, ∀ x : ℝ,
      (t, d.lift x t, deriv (fun y => d.lift y t) x) ∈
        curveShorteningChartFirstJetDomain D
          (fun t => Geometry.Riemannian.retractionMetric (g t) he hr) β :=
    ambient_firstJet_mem_of_sobolev_solution_facts
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  apply contMDiffOn_retraction_of_contDiffOn (U := U) (r := r) hr d (Icc 0 T) hjoint
  intro x t htt
  simpa only [DifferentialGeometry.extChartAt_opens_target, U.isOpen.interior_eq] using
    (hjet t htt x).2.1

private theorem ambient_sobolev_solution_exists_with_retraction_regular [I.Boundaryless] :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ScalarVectorTimeCoefficients.radius C ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
            parameterDerivativeForcingFieldLift g₀ hT gforce ∧
            ambientSobolevFourthOrderLift g₀ hT gforce ∧
            let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
              (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
            let c : CurveMap M := fun z t => r (d z t)
            (∀ z, c z 0 = c₀.map z) ∧
              (∀ z t, t ∈ Icc 0 T → e (c z t) = d z t) ∧
              ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun p : ℝ × ℝ => c.lift p.1 p.2)
                (univ ×ˢ Icc 0 T) ∧
              (∀ t ∈ Icc 0 T, ContMDiff 𝓘(ℝ, ℝ) I 2 (fun x : ℝ => c.lift x t)) ∧
              c.ImmersedOn (I := I) (Icc 0 T) ∧
              ∀ x t, t ∈ Icc 0 T →
                mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e (c.lift x t)
                  (c.velocity (I := I) (Icc 0 T) x t) =
                    d.velocity (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Icc 0 T) x t := by
  intro C g₀ f₀ P S
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hfour, _⟩ :=
    ambient_sobolev_solution_exists_with_mem_range c₀ g ht he hr hEU hleft β hG
  obtain ⟨hinit, hce, hc2, himm⟩ :=
    ambient_retraction_contMDiff_two_and_immersed_of_parameterDerivative_lift
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hc1 := ambient_retraction_contMDiffOn_one_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce,
    hfacts, hlift, hfour, hinit, hce, hc1, hc2, himm, ?_⟩
  let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
    (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
  let c : CurveMap M := fun z t => r (d z t)
  change ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun p : ℝ × ℝ => c.lift p.1 p.2)
    (univ ×ˢ Icc 0 T) at hc1
  change ∀ z t, t ∈ Icc 0 T → e (c z t) = d z t at hce
  intro x t htt
  have hslice : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) 1
      (fun τ : ℝ => (x, τ)) (Icc 0 T) :=
    (show ContDiffOn ℝ 1 (fun τ : ℝ => (x, τ)) (Icc 0 T) from
      contDiffOn_const.prodMk contDiffOn_id).contMDiffOn
  have htime : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (c.lift x) (Icc 0 T) t :=
    ((hc1.comp hslice (fun τ hτ => ⟨mem_univ x, hτ⟩)) t htt).mdifferentiableWithinAt (by norm_num)
  have hvel := CurveMap.velocity_comp he htime (uniqueDiffOn_Icc hT t htt)
  have heq : CurveMap.velocity (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun z τ => e (c z τ)) (Icc 0 T) x t =
        d.velocity (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Icc 0 T) x t := by
    unfold CurveMap.velocity
    have h := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (f₁ := fun τ => e (c.lift x τ)) (f := d.lift x)
      (fun τ hτ => hce (x : AddCircle (1 : ℝ)) τ hτ) htt
    exact congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1) h
  exact hvel.symm.trans heq

private theorem ambient_retraction_parametric_equation_of_parameterDerivative_lift [I.Boundaryless]
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
    let c : CurveMap M := fun z t => r (d z t)
    ∀ x t, t ∈ Icc 0 T → c.velocity (I := I) (Icc 0 T) x t =
      c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  intro g₀ f₀ P S d c
  have hcjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1
      (fun p : ℝ × ℝ => c.lift p.1 p.2) (univ ×ˢ Icc 0 T) :=
    ambient_retraction_contMDiffOn_one_of_parameterDerivative_lift
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hfinite := ambient_retraction_contMDiff_two_and_immersed_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hce : ∀ z t, t ∈ Icc 0 T → e (c z t) = d z t := hfinite.2.1
  have hcspace : ∀ t ∈ Icc 0 T, ContMDiff 𝓘(ℝ, ℝ) I 2 (fun x => c.lift x t) :=
    hfinite.2.2.1
  have hpde : ∀ t ∈ Icc 0 T, ∀ x,
      HasDerivWithinAt (fun s => d.lift x s)
        (curveShorteningParametricChartRhs
          (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
          (t, d.lift x t, deriv (fun y => d.lift y t) x,
            deriv (deriv (fun y => d.lift y t)) x)) (Icc 0 T) t :=
    ambient_chart_equation_of_parameterDerivative_lift
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  let j : M → U := fun p => ⟨e p, hEU (mem_range_self p)⟩
  have hj : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ j :=
    (ContMDiff.subtypeVal_comp_iff U j).mp he
  have hmetric : ∀ t p v w,
      (Geometry.Riemannian.retractionMetric (g t) he hr).inner (j p)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) j p v)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) j p w) = (g t).inner p v w := by
    intro t p v w
    rw [← mfderiv_subtypeVal_comp j p]
    exact Geometry.Riemannian.retractionMetric_inner_map (g t) he hr hEU hleft p v w
  intro x t htt
  have htime : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (c.lift x) (Icc 0 T) t := by
    have hslice : ContMDiffWithinAt 𝓘(ℝ, ℝ) I 1 (c.lift x) (Icc 0 T) t :=
      (hcjoint (x, t) ⟨mem_univ _, htt⟩).comp t
        ((contDiffWithinAt_const.prodMk contDiffWithinAt_id).contMDiffWithinAt)
        (fun s hs => ⟨mem_univ x, hs⟩)
    exact hslice.mdifferentiableWithinAt one_ne_zero
  apply CurveMap.velocity_eq_parametric_acceleration_of_comp_of_contMDiffAt hj hmetric
    (fun s => Geometry.Riemannian.hasVanishingSecondFundamentalFormAlongCurves_retractionMetric
      (g s) he hr hEU hleft) htime (hcspace t htt x) (uniqueDiffOn_Icc hT t htt)
  apply CurveMap.velocity_eq_parametric_acceleration_of_chart_of_contMDiffAt β x t
    ((hj.mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt t htime)
    ((hj.contMDiffAt.of_le (by decide : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp x (hcspace t htt x))
    (uniqueDiffOn_Icc hT t htt)
    (by rw [DifferentialGeometry.extChartAt_opens_source]; trivial)
  have hspace : (fun y => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β
      (j (c.lift y t))) = (fun y => d.lift y t) := by
    funext y
    exact hce (y : AddCircle (1 : ℝ)) t htt
  change HasDerivWithinAt (fun s => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β
    (j (c.lift x s)))
    (curveShorteningParametricChartRhs
      (fun s => Geometry.Riemannian.retractionMetric (g s) he hr) β
      (t, extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β (j (c.lift x t)),
        deriv (fun y => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β (j (c.lift y t))) x,
        deriv (deriv (fun y => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β
          (j (c.lift y t)))) x)) (Icc 0 T) t
  rw [hspace, show extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) β (j (c.lift x t)) =
    d.lift x t from congrFun hspace x]
  apply (hpde t htt x).congr
  · intro s hs
    exact hce (x : AddCircle (1 : ℝ)) s hs
  · exact hce (x : AddCircle (1 : ℝ)) t htt

private theorem ambient_sobolev_solution_exists_with_parametric_equation [I.Boundaryless] :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ScalarVectorTimeCoefficients.radius C ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
            parameterDerivativeForcingFieldLift g₀ hT gforce ∧
            ambientSobolevFourthOrderLift g₀ hT gforce ∧
            let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
              (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
            let c : CurveMap M := fun z t => r (d z t)
            (∀ z, c z 0 = c₀.map z) ∧
              (∀ z t, t ∈ Icc 0 T → e (c z t) = d z t) ∧
              ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun p : ℝ × ℝ => c.lift p.1 p.2)
                (univ ×ˢ Icc 0 T) ∧
              (∀ t ∈ Icc 0 T, ContMDiff 𝓘(ℝ, ℝ) I 2 (fun x : ℝ => c.lift x t)) ∧
              c.ImmersedOn (I := I) (Icc 0 T) ∧
              (∀ x t, t ∈ Icc 0 T →
                mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e (c.lift x t)
                  (c.velocity (I := I) (Icc 0 T) x t) =
                    d.velocity (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (Icc 0 T) x t) ∧
              ∀ x t, t ∈ Icc 0 T → c.velocity (I := I) (Icc 0 T) x t =
                c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  intro C g₀ f₀ P S
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce,
    hfacts, hlift, hfour, hinit, hce, hc1, hc2, himm, hvel⟩ :=
    ambient_sobolev_solution_exists_with_retraction_regular c₀ g ht he hr hEU hleft β hG
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce,
    hfacts, hlift, hfour, hinit, hce, hc1, hc2, himm, hvel, ?_⟩
  exact ambient_retraction_parametric_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem curveMap_smoothOn_retraction_of_contDiffOn
    {d : CurveMap (EuclideanSpace ℝ (Fin n))} {J : Set ℝ}
    {r : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => d.lift p.2 p.1) (J ×ˢ univ))
    (hU : ∀ x t, t ∈ J → d.lift x t ∈ U) :
    CurveMap.SmoothOn (I := I) (fun z t => r (d z t)) J := by
  have hswap : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.2, p.1))
      (univ ×ˢ J) := contDiffOn_snd.prodMk contDiffOn_fst
  have hmap : MapsTo (fun p : ℝ × ℝ => (p.2, p.1))
      (univ ×ˢ J) (J ×ˢ univ) := fun _ hp => ⟨hp.2, hp.1⟩
  have hdsmooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => d.lift p.1 p.2)
      (univ ×ˢ J) := hd.comp hswap hmap
  exact hr.comp hdsmooth.contMDiffOn (fun p hp => hU p.1 p.2 hp.2)

private theorem ambient_retraction_smooth_of_contDiffOn
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hsmooth :
      let g₀ := c₀.pullbackMetric (g 0)
      let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
      let P := circleHsPiInclusion g₀ (Fin n)
        (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
      let S := circleHsPiInclusion g₀ (Fin n)
        (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
      let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
        (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
      ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set ℝ))) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
    let c : CurveMap M := fun z t => r (d z t)
    c.SmoothOn (I := I) (Icc 0 T) := by
  intro g₀ f₀ P S d c
  have hjet := ambient_firstJet_mem_of_sobolev_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  change ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => d.lift p.2 p.1)
    (Icc 0 T ×ˢ univ) at hsmooth
  apply curveMap_smoothOn_retraction_of_contDiffOn (d := d) (J := Icc 0 T) hr hsmooth
  intro x t ht
  simpa only [d, g₀, f₀, P, S, CurveMap.lift,
    DifferentialGeometry.extChartAt_opens_target, U.isOpen.interior_eq] using
    (hjet t ht x).2.1

private theorem ambient_retraction_exists_reparametrization_of_contDiffOn [I.Boundaryless]
    (hg : MetricFamilySmoothOn D g)
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce)
    (hsmooth :
      let g₀ := c₀.pullbackMetric (g 0)
      let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
      let P := circleHsPiInclusion g₀ (Fin n)
        (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
      let S := circleHsPiInclusion g₀ (Fin n)
        (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
      let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
        (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
      ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set ℝ))) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
    let c : CurveMap M := fun z t => r (d z t)
    (∀ z, c z 0 = c₀.map z) ∧
      (∀ z t, t ∈ Icc 0 T → e (c z t) = d z t) ∧
      c.SmoothOn (I := I) (Icc 0 T) ∧
      c.ImmersedOn (I := I) (Icc 0 T) ∧
      ∃ φ : CircleReparametrization (Icc 0 T),
        (∀ z, φ.map 0 z = z) ∧
        CurveMap.IsSolutionOn (I := I) (fun z t => c (φ.map t z) t) g (Icc 0 T) ∧
        (∀ z, c (φ.map 0 z) 0 = c₀.map z) ∧
        (∀ z t, t ∈ Icc 0 T → e (c (φ.map t z) t) = d (φ.map t z) t) ∧
        ∀ t, t ∈ Icc 0 T →
          range (fun z => e (c (φ.map t z) t)) = range (fun z => d z t) := by
  intro g₀ f₀ P S d c
  have hfinite := ambient_retraction_contMDiff_two_and_immersed_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hparametric := ambient_retraction_parametric_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hcsmooth : c.SmoothOn (I := I) (Icc 0 T) :=
    ambient_retraction_smooth_of_contDiffOn
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hsmooth
  have hjet := ambient_firstJet_mem_of_sobolev_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  have hJD : Icc (0 : ℝ) T ⊆ D.regular := fun t htt => (hjet t htt 0).1
  have hgeo := CurveMap.isGeometricSolutionOn_of_parabolicGauge
    hg (uniqueDiffOn_Icc hT) hJD hcsmooth hfinite.2.2.2 hparametric
  obtain ⟨φ, hφ, hsol⟩ := hgeo.exists_reparametrization_isSolutionOn hg hT hJD
  refine ⟨hfinite.1, hfinite.2.1, hcsmooth, hfinite.2.2.2, φ, hφ, hsol, ?_, ?_, ?_⟩
  · intro z
    rw [hφ]
    exact hfinite.1 z
  · intro z t ht
    exact hfinite.2.1 (φ.map t z) t ht
  · intro t ht
    have hpoint : (fun z => e (c (φ.map t z) t)) =
        (fun z => d z t) ∘ (φ.map t) := by
      funext z
      exact hfinite.2.1 (φ.map t z) t ht
    rw [hpoint]
    exact (φ.map t).surjective.range_comp (fun z => d z t)

end

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

open private exists_pos_contraction_radius from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleContractionRadius

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem exists_pos_parameterPrincipal_norm_le {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : TensorHs g₀ 0 0 ((1 : ℕ) : ℝ), ‖a - q‖ ≤ ε →
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ a‖ ≤ (1 / 4 : ℝ) ∧
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ a‖ ≤ (1 / 4 : ℝ) := by
  intro q
  let m := scalarHsMul g₀ 1 (by norm_num)
  let c := (scalarH1ToContinuous g₀).comp (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let Z := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let M := scalarH0ContinuousMul g₀
  let Ch := ‖m‖ * ‖AddCircle.parameterSecondDerivativeHs g₀ 1‖
  let Cl := ‖M‖ * ‖c‖ * ‖Z.comp (AddCircle.parameterSecondDerivativeHs g₀ 0)‖
  have hCh : 0 ≤ Ch := by positivity
  have hCl : 0 ≤ Cl := by positivity
  let ε := (1 / 4 : ℝ) / (Ch + Cl + 1)
  have hε : 0 < ε := by positivity
  have hεeq : ε * (Ch + Cl + 1) = 1 / 4 := by
    exact div_mul_cancel₀ _ (by positivity)
  have hChε : Ch * ε ≤ 1 / 4 := by
    nlinarith [mul_nonneg hCl hε.le]
  have hClε : Cl * ε ≤ 1 / 4 := by
    nlinarith [mul_nonneg hCh hε.le]
  refine ⟨ε, hε, ?_⟩
  intro a ht
  constructor
  · calc
      _ ≤ ‖m‖ * ‖a - q‖ * ‖AddCircle.parameterSecondDerivativeHs g₀ 1‖ :=
        AddCircle.norm_parameterPrincipalOperatorHsPi_le g₀ a
      _ ≤ ‖m‖ * ε * ‖AddCircle.parameterSecondDerivativeHs g₀ 1‖ := by gcongr
      _ = Ch * ε := by dsimp only [Ch]; ring
      _ ≤ 1 / 4 := hChε
  · calc
      _ ≤ ‖M‖ * (‖c‖ * ‖a - q‖) *
          ‖Z.comp (AddCircle.parameterSecondDerivativeHs g₀ 0)‖ :=
        AddCircle.norm_parameterPrincipalOperatorH0Pi_le g₀ a
      _ ≤ ‖M‖ * (‖c‖ * ε) * ‖Z.comp (AddCircle.parameterSecondDerivativeHs g₀ 0)‖ := by gcongr
      _ = Cl * ε := by dsimp only [Cl]; ring
      _ ≤ 1 / 4 := hClε

private theorem exists_pos_parameterDrift_norm_lt {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (A : ℝ≥0) {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
      0 < T → T ≤ ρ → ρ ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
      Real.sqrt (1 + T) * (eLpNorm
        (fun t => AddCircle.parameterDriftOperatorHsPi (ι := Fin n) g₀ (a₂ t))
        2 (timeMeasure T)).toReal < 1 / 4 ∧
      Real.sqrt (1 + T) * (eLpNorm
        (fun t => AddCircle.parameterDriftOperatorH0Pi (ι := Fin n) g₀ (a₂ t))
        2 (timeMeasure T)).toReal < 1 / 4 := by
  let D := AddCircle.parameterDerivativeHs g₀ 1
  let m := scalarHsMul g₀ 1 (by norm_num)
  let d := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
    (scalarCc g₀ (AddCircle.laplacianDriftCoefficient g₀))
  let c := (scalarH1ToContinuous g₀).comp (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let Z := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let D₀ := Z.comp (AddCircle.parameterDerivativeHs g₀ 0)
  let M := scalarH0ContinuousMul g₀
  let Kh := ‖m‖ * ‖D‖ ^ 2
  let Kl := ‖M‖ * ‖c‖ * ‖D‖ * ‖D₀‖
  let Bh := ‖m‖ * ‖d‖ * ‖D‖
  let Bl := ‖M‖ * ‖c‖ * ‖d‖ * ‖D₀‖
  let K := max Kh Kl
  let B := max Bh Bl
  have hKh : 0 ≤ Kh := by positivity
  have hKl : 0 ≤ Kl := by positivity
  have hBh : 0 ≤ Bh := by positivity
  have hBl : 0 ≤ Bl := by positivity
  obtain ⟨δ, hδ, hδR, hδ1, hsmall⟩ := exists_pos_contraction_radius
    0 (4 * K * A) (4 * B) le_rfl (by positivity) (by positivity) hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hnorm
  have hρ : 0 ≤ ρ := hT.le.trans hTρ
  have hcommon : Real.sqrt (1 + T) *
      (K * A * (Real.sqrt T + (1 + T) * ρ / 4) + Real.sqrt T * B) < 1 / 4 := by
    have hs := hsmall hT.le hTρ hρδ
    simp only [zero_mul, zero_add] at hs
    nlinarith
  let hh := AddCircle.memLp_parameterDriftOperatorHsPi (ι := Fin n) g₀ (Lp.memLp a₂)
  let hl := AddCircle.memLp_parameterDriftOperatorH0Pi (ι := Fin n) g₀ (Lp.memLp a₂)
  have hnh : ‖hh.toLp (fun t => AddCircle.parameterDriftOperatorHsPi (ι := Fin n) g₀ (a₂ t))‖ ≤
      K * A * (Real.sqrt T + (1 + T) * ρ / 4) + Real.sqrt T * B := by
    calc
      _ ≤ Kh * ‖a₂‖ + Real.sqrt T * Bh := AddCircle.norm_toLp_parameterDriftOperatorHsPi_le g₀ a₂
      _ ≤ Kh * (A * (Real.sqrt T + (1 + T) * ρ / 4)) + Real.sqrt T * Bh :=
        add_le_add (mul_le_mul_of_nonneg_left hnorm hKh) le_rfl
      _ ≤ K * (A * (Real.sqrt T + (1 + T) * ρ / 4)) + Real.sqrt T * B :=
        add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg T))
      _ = _ := by ring
  have hnl : ‖hl.toLp (fun t => AddCircle.parameterDriftOperatorH0Pi (ι := Fin n) g₀ (a₂ t))‖ ≤
      K * A * (Real.sqrt T + (1 + T) * ρ / 4) + Real.sqrt T * B := by
    calc
      _ ≤ Kl * ‖a₂‖ + Real.sqrt T * Bl := AddCircle.norm_toLp_parameterDriftOperatorH0Pi_le g₀ a₂
      _ ≤ Kl * (A * (Real.sqrt T + (1 + T) * ρ / 4)) + Real.sqrt T * Bl :=
        add_le_add (mul_le_mul_of_nonneg_left hnorm hKl) le_rfl
      _ ≤ K * (A * (Real.sqrt T + (1 + T) * ρ / 4)) + Real.sqrt T * B :=
        add_le_add
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg T))
      _ = _ := by ring
  have hhbound := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hnh (Real.sqrt_nonneg (1 + T))) hcommon
  have hlbound := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hnl (Real.sqrt_nonneg (1 + T))) hcommon
  exact ⟨by simpa only [Lp.norm_toLp] using hhbound,
    by simpa only [Lp.norm_toLp] using hlbound⟩

private theorem exists_pos_parameterDerivative_contraction_margin {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ ε : ℝ, 0 < ε ∧ ∀ A : ℝ≥0, ∀ R : ℝ, 0 < R →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
        0 < T → T ≤ ρ → ρ ≤ δ →
        ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
        (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - q‖ ≤ ε) →
        ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
        parameterDerivativeOperatorBoundsWithMargin (n := n) g₀ a₂ (3 / 4) := by
  intro H q
  obtain ⟨ε, hε, hp⟩ := exists_pos_parameterPrincipal_norm_le (n := n) g₀
  refine ⟨ε, hε, ?_⟩
  intro A R hR
  obtain ⟨δ, hδ, hδR, hδ1, hd⟩ := exists_pos_parameterDrift_norm_lt (n := n) g₀ A hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hclose hnorm
  have hT1 : T ≤ 1 := hTρ.trans (hρδ.trans hδ1)
  obtain ⟨hdh, hdl⟩ := hd hT hTρ hρδ a₂ hnorm
  have hph : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (H (a₂ t))‖ ≤ (1 / 4 : ℝ) := by
    filter_upwards [hclose] with t ht
    exact (hp _ ht).1
  have hpl : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (H (a₂ t))‖ ≤ (1 / 4 : ℝ) := by
    filter_upwards [hclose] with t ht
    exact (hp _ ht).2
  have hmargin : (1 / 4 : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      (eLpNorm (parameterDriftHigh (n := n) g₀ a₂) 2 (timeMeasure T)).toReal ≤ 3 / 4 := by
    linarith
  have hsmalll : (1 / 4 : ℝ) * (1 + T) + Real.sqrt (1 + T) *
      ‖(AddCircle.memLp_parameterDriftOperatorH0Pi (ι := Fin n) g₀ (Lp.memLp a₂)).toLp
        (fun t => AddCircle.parameterDriftOperatorH0Pi (ι := Fin n) g₀ (a₂ t))‖ < 1 := by
    rw [Lp.norm_toLp]
    linarith
  obtain ⟨hpl', hsmalll'⟩ := parameterDerivativeH0Pi_normalized_contraction g₀ a₂
    (1 / 4) hpl hsmalll
  exact ⟨1 / 4, 1 / 4, hph, hpl', hmargin, hsmalll'⟩

private theorem exists_pos_parameterDerivative_contraction_threshold {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ ε : ℝ, 0 < ε ∧ ∀ A : ℝ≥0, ∀ R : ℝ, 0 < R →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ δ ≤ 1 ∧ ∀ {ρ T : ℝ},
        0 < T → T ≤ ρ → ρ ≤ δ →
        ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
        (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - q‖ ≤ ε) →
        ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
        parameterDerivativeOperatorBounds (n := n) g₀ a₂ := by
  intro H q
  obtain ⟨ε, hε, hcontract⟩ := exists_pos_parameterDerivative_contraction_margin (n := n) g₀
  refine ⟨ε, hε, ?_⟩
  intro A R hR
  obtain ⟨δ, hδ, hδR, hδ1, hmargin⟩ := hcontract A R hR
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ T hT hTρ hρδ a₂ hclose hnorm
  exact parameterDerivativeOperatorBounds_of_margin g₀ a₂ (by norm_num : (3 / 4 : ℝ) < 1)
    (hmargin hT hTρ hρδ a₂ hclose hnorm)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem exists_normalized_timeL2_h2_coefficients
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (a₂ : timeL2 (TensorHs g₀ 0 0 2) T)
    (b₂ : timeL2 (CircleHsPi g₀ (Fin n) 2) T) :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)
    let P₂ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H₂)
    ∃ aa : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
    ∃ bb : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
      (fun t => H (aa t)) =ᵐ[timeMeasure T] (fun t => H₂ (a₂ t)) ∧
      (fun t => P (bb t)) =ᵐ[timeMeasure T] (fun t => P₂ (b₂ t)) ∧
      ‖aa‖ ≤ ‖a₂‖ ∧ ‖bb‖ ≤ ‖b₂‖ := by
  intro H P H₂ P₂
  let S := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ 2)
  let SP := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => S)
  let aa := S.compLpL 2 (timeMeasure T) a₂
  let bb := SP.compLpL 2 (timeMeasure T) b₂
  have hS : ‖S‖ ≤ 1 := tensorHsInclusion_opNorm_le_one _
  have hSP : ‖SP‖ ≤ 1 := ContinuousLinearMap.norm_piLpMap_le _ zero_le_one (fun _ => hS)
  refine ⟨aa, bb, ?_, ?_, ?_, ?_⟩
  · filter_upwards [S.coeFn_compLpL a₂] with t ht
    change H (aa t) = _
    rw [ht]
    exact (tensorHsInclusion_trans_apply _ _ _).symm
  · filter_upwards [SP.coeFn_compLpL b₂] with t ht
    change P (bb t) = _
    rw [ht]
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ 2) (b₂ t i)).symm
  · exact (S.norm_compLp_le a₂).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hS (norm_nonneg a₂))
  · exact (SP.norm_compLp_le b₂).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hSP (norm_nonneg b₂))

private theorem ambient_coefficients_h2_norm_le_of_translated_state
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ δ ≤ 1 ∧
      ∃ A B : ℝ≥0, ∀ f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2),
      ‖f - f₀‖ ≤ δ / 2 → ∀ {ρ T : ℝ} (hT : 0 < T), T ≤ ρ → ρ ≤ δ / 2 →
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) → w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) → ‖gforce‖ ≤ ρ / 4 →
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∃ b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => H (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (f - f₀) + w t)))) ∧
        (fun t => P (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (f - f₀) + w t)))) ∧
        ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) ∧
        ‖b₂‖ ≤ B * (Real.sqrt T + (1 + T) * ρ / 4) := by
  intro C g₀ f₀ J K H P
  obtain ⟨δ, hδ, hδC, hδ1, A, B, hA, hB, hab⟩ :=
    ambient_coefficients_h2_norm_le_of_small_state c₀ g ht he hr hEU hleft β hG
  let D := 1 + δ / 2
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨δ, hδ, hδC, hδ1, ⟨A * D, mul_nonneg hA hD⟩, ⟨B * D, mul_nonneg hB hD⟩, ?_⟩
  intro f hf ρ T hT hTρ hρδ gforce field w hw hwu hbound hforce
  let field' := TimeSobolev.const T (f - f₀) + field
  let w' := fun t => K (f - f₀) + w t
  have hKnorm : ‖K‖ ≤ 1 := ContinuousLinearMap.norm_piLpMap_le _ zero_le_one
    (fun _ => tensorHsInclusion_opNorm_le_one _)
  have hKf : ‖K (f - f₀)‖ ≤ δ / 2 := (K.le_opNorm _).trans
    ((show ‖K‖ * ‖f - f₀‖ ≤ ‖f - f₀‖ from by simpa only [one_mul] using mul_le_mul_of_nonneg_right hKnorm (norm_nonneg (f - f₀))).trans hf)
  have hw' : ContinuousOn w' (Icc 0 T) := continuousOn_const.add hw
  have hwu' : w' =ᵐ[timeMeasure T] fun t => K (field' t) := by
    filter_upwards [hwu, TimeSobolev.coeFn_const (T := T) (f - f₀),
      Lp.coeFn_add (TimeSobolev.const T (f - f₀)) field] with t ht hc hsum
    change K (f - f₀) + w t = K ((TimeSobolev.const T (f - f₀) + field) t)
    rw [hsum, Pi.add_apply, hc, map_add, ht]
  have hb' (t : ℝ) (ht : t ∈ Icc 0 T) : ‖w' t‖ ≤ δ := by
    exact (norm_add_le _ _).trans (by linarith [hbound t ht])
  obtain ⟨a₂, b₂, ha₂, hb₂, hanorm, hbnorm⟩ :=
    hab T (by linarith) field' w' hw' hwu' hb'
  obtain ⟨aa, bb, haa, hbb, haanorm, hbbnorm⟩ :=
    exists_normalized_timeL2_h2_coefficients g₀ a₂ b₂
  have hfield : ‖field‖ ≤ (1 + T) * ρ / 4 :=
    (norm_maximalRegularityDuhamelVectorField_zero_le hT gforce).trans
      (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hforce (by linarith : 0 ≤ 1 + T))
  have hfield' : ‖field'‖ ≤ Real.sqrt T * (δ / 2) + (1 + T) * ρ / 4 := by
    calc
      ‖field'‖ ≤ ‖TimeSobolev.const T (f - f₀)‖ + ‖field‖ := norm_add_le _ _
      _ = Real.sqrt T * ‖f - f₀‖ + ‖field‖ := by rw [TimeSobolev.norm_const]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hf (Real.sqrt_nonneg T)) hfield
  have htotal : Real.sqrt T + ‖field'‖ ≤ D * (Real.sqrt T + (1 + T) * ρ / 4) := by
    dsimp only [D]
    have hpos : 0 ≤ (1 + T) * ρ / 4 := by have : 0 ≤ ρ := hT.le.trans hTρ; positivity
    nlinarith [mul_nonneg (by positivity : 0 ≤ δ / 2) hpos]
  refine ⟨aa, bb, haa.trans ha₂, hbb.trans hb₂,
    haanorm.trans (hanorm.trans ?_), hbbnorm.trans (hbnorm.trans ?_)⟩
  · change A * (Real.sqrt T + ‖field'‖) ≤ (A * D) * (Real.sqrt T + (1 + T) * ρ / 4)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left htotal hA
  · change B * (Real.sqrt T + ‖field'‖) ≤ (B * D) * (Real.sqrt T + (1 + T) * ρ / 4)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left htotal hB

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

open private vectorTensorHsNormedSpace from DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.ShiftedCoefficients

noncomputable section
attribute [local instance] vectorTensorHsNormedSpace
open scoped Manifold ContDiff NNReal ENNReal BigOperators Topology
open MeasureTheory Filter Set
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩


private theorem exists_pos_parameterDerivative_translated_margin_radius
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (A Cα : ℝ≥0) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (Jn : ℝ) (hJn : 0 ≤ Jn) :
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let q := ccTensorToHs g₀ 0 ((1 : ℕ) : ℝ)
      (DifferentialGeometry.Analysis.Sobolev.scalarCc g₀ (AddCircle.laplacianPrincipalCoefficient g₀))
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R / 2 ∧ δ ≤ 1 ∧ 2 * Jn * δ ≤ r ∧
      ∀ {ρ T : ℝ}, 0 < T → T ≤ ρ → ρ ≤ δ →
      ∀ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (∀ᵐ t ∂timeMeasure T, ‖H (a₂ t) - q‖ ≤ (Cα : ℝ) * (2 * δ)) →
      ‖a₂‖ ≤ A * (Real.sqrt T + (1 + T) * ρ / 4) →
      parameterDerivativeOperatorBoundsWithMargin (n := n) g₀ a₂ (3 / 4) := by
  intro H q
  obtain ⟨ε, hε, hεcontract⟩ := exists_pos_parameterDerivative_contraction_margin (n := n) g₀
  let r₀ := min (R / 2) (min (r / (2 * (1 + Jn))) (ε / (2 * (1 + (Cα : ℝ)))))
  have hr₀ : 0 < r₀ := by dsimp only [r₀]; positivity
  have hrR : r₀ ≤ R / 2 := min_le_left _ _
  have hrJ : 2 * Jn * r₀ ≤ r := by
    have hp : r₀ ≤ r / (2 * (1 + Jn)) := (min_le_right _ _).trans (min_le_left _ _)
    have he := (le_div_iff₀ (by positivity : 0 < 2 * (1 + Jn))).mp hp
    nlinarith
  have hrα : (Cα : ℝ) * (2 * r₀) ≤ ε := by
    have hp : r₀ ≤ ε / (2 * (1 + (Cα : ℝ))) := (min_le_right _ _).trans (min_le_right _ _)
    have he := (le_div_iff₀ (by positivity : 0 < 2 * (1 + (Cα : ℝ)))).mp hp
    nlinarith [Cα.coe_nonneg]
  obtain ⟨δ, hδ, hδr, hδ1, hcontract⟩ := hεcontract A r₀ hr₀
  refine ⟨δ, hδ, hδr.trans hrR, hδ1, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hδr (by positivity)).trans hrJ
  · intro ρ T hT hTρ hρδ a₂ hclose hnorm
    apply hcontract hT hTρ hρδ a₂ ?_ hnorm
    filter_upwards [hclose] with t ht
    exact ht.trans ((mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hδr (by norm_num : (0 : ℝ) ≤ 2)) Cα.coe_nonneg).trans hrα)

private theorem translated_state_norm_bounds
    {X Y Z : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
    (K : X →L[ℝ] Y) (J : Y →L[ℝ] Z) (hK : ‖K‖ ≤ 1)
    {δ R : ℝ} (hJ : 2 * ‖J‖ * δ ≤ R) (f : X) (hf : ‖f‖ ≤ δ)
    {A : Type*} (s : Set A) (w : A → Y) (hw : ∀ t ∈ s, ‖w t‖ ≤ δ) :
    (∀ t ∈ s, ‖K f + w t‖ ≤ 2 * δ) ∧ (∀ t ∈ s, ‖J (K f + w t)‖ ≤ R) := by
  have hKnorm : ‖K‖ * ‖f‖ ≤ ‖f‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (norm_nonneg f)
  have hKf : ‖K f‖ ≤ δ := (K.le_opNorm f).trans (hKnorm.trans hf)
  have hnorm (t : A) (ht : t ∈ s) : ‖K f + w t‖ ≤ 2 * δ :=
    (norm_add_le _ _).trans (by linarith only [hKf, hw t ht])
  refine ⟨hnorm, ?_⟩
  intro t ht
  exact (J.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hnorm t ht) (norm_nonneg J)).trans
    (by nlinarith only [hJ]))

private theorem ambient_translated_coefficients_h2_and_margin
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr)) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => H)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ δ ≤ 1 ∧
      ∀ f : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2), ‖f - f₀‖ ≤ δ →
      ∀ {ρ T : ℝ} (hT : 0 < T), T ≤ ρ → ρ ≤ δ →
      ∀ gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T,
      let field := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
        (a := ((1 : ℕ) : ℝ)) hT 0 gforce
      ∀ w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1),
      ContinuousOn w (Icc 0 T) → w =ᵐ[timeMeasure T] (fun t => K (field t)) →
      (∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) → ‖gforce‖ ≤ ρ / 4 →
      (∀ t ∈ Icc 0 T, ‖J (K (f - f₀) + w t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) ∧
      ∃ a₂ : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      ∃ b₂ : timeL2 (CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => H (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.diffusion C) t (J (K (f - f₀) + w t)))) ∧
        (fun t => P (b₂ t)) =ᵐ[timeMeasure T]
          (fun t => circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le (ScalarVectorTimeCoefficients.reaction C) t (J (K (f - f₀) + w t)))) ∧
        parameterDerivativeOperatorBoundsWithMargin (n := n) g₀ a₂ (3 / 4) := by
  intro C g₀ f₀ J K H P
  obtain ⟨δ₀, hδ₀, hδ₀C, hδ₀1, A, B, hab⟩ :=
    ambient_coefficients_h2_norm_le_of_translated_state c₀ g ht he hr hEU hleft β hG
  obtain ⟨Cα, hclose⟩ := ambient_diffusion_sub_baseline_norm_le c₀ g ht he hr hEU hleft β hG
  obtain ⟨δ, hδ, hδδ, hδ1, hδJ, hcontract⟩ :=
    exists_pos_parameterDerivative_translated_margin_radius (n := n) g₀ A Cα hδ₀
      (ScalarVectorTimeCoefficients.radius_pos C) ‖J‖ (norm_nonneg J)
  have hδC : δ ≤ ScalarVectorTimeCoefficients.radius C :=
    (hδδ.trans (by linarith only [hδ₀])).trans hδ₀C
  refine ⟨δ, hδ, hδC, hδ1, ?_⟩
  intro f hf ρ T hT hTρ hρδ gforce field w hw hwu hbound hforce
  let w' := fun t => K (f - f₀) + w t
  obtain ⟨hw', hJw⟩ := translated_state_norm_bounds K J
    (ContinuousLinearMap.norm_piLpMap_le _ zero_le_one (fun _ => tensorHsInclusion_opNorm_le_one _))
    hδJ (f - f₀) hf (Icc 0 T) w (fun t ht => (hbound t ht).trans hρδ)
  obtain ⟨a₂, b₂, ha₂, hb₂, hanorm, _⟩ :=
    hab f (hf.trans hδδ) hT hTρ (hρδ.trans hδδ) gforce w hw hwu hbound hforce
  refine ⟨hJw, a₂, b₂, ha₂, hb₂, ?_⟩
  have hδtwo : 0 ≤ 2 * δ := by positivity
  have hTtwo : T ≤ 2 * δ := by linarith only [hTρ, hρδ, hδ]
  have hclosew := hclose hδtwo hTtwo w'
  dsimp only [C, g₀, J, K, w'] at hw' hJw
  have hpoint0 := hclosew hw'
  have hpoint := hpoint0 hJw
  apply hcontract hT hTρ hρδ a₂ ?_ hanorm
  have htmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  filter_upwards [ha₂, htmem] with t hat htt
  rw [hat]
  exact hpoint t htt

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
variable (c₀ : SmoothImmersion (I := I) (M := M))
variable {e : M → EuclideanSpace ℝ (Fin n)}
variable (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambient_original_forcing_higher_equation
    (gM : SmoothRiemannianMetric I M) {m : ℕ} (hm : 2 ≤ m)
    {T : ℝ} (hT : 0 < T)
    (F₂ : timeL2 (CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((2 : ℕ) : ℝ)) T)
    (a₂ : ℝ → TensorHs (c₀.pullbackMetric gM) 0 0 ((2 : ℕ) : ℝ))
    (b₂ : ℝ → CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((2 : ℕ) : ℝ))
    (U : timeL2 (CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((m : ℝ) + 2)) T)
    (a : ℝ → TensorHs (c₀.pullbackMetric gM) 0 0 (m : ℝ))
    (b : ℝ → CircleHsPi (c₀.pullbackMetric gM) (Fin n) (m : ℝ))
    (ha : ContinuousOn a (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T)) :
    let g₀ := c₀.pullbackMetric gM
    let J := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (show ((2 : ℕ) : ℝ) ≤ (m : ℝ) by exact_mod_cast hm)
    let K := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (show ((2 : ℕ) : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right hm 2)
    let U₂ := maximalRegularityDuhamelVectorField hT 0 F₂
    (fun t => J (a t)) =ᵐ[timeMeasure T] a₂ →
    (∀ᵐ t ∂timeMeasure T, ∀ i, J (b t i) = b₂ t i) →
    (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => K)).compLpL
      2 (timeMeasure T) U = U₂ →
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ) (U₂ t i) + F₂ t i =
        scalarHsMul g₀ 2 (by norm_num) (a₂ t)
          (AddCircle.parameterSecondDerivativeHs g₀ 2
            (ambientSobolev c₀ gM e he (((2 : ℕ) : ℝ) + 2) i + U₂ t i)) + b₂ t i) →
    ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) (m : ℝ)) T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => J)).compLpL
        2 (timeMeasure T) FH = F₂ ∧
      U = maximalRegularityDuhamelVectorField hT 0 FH ∧
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) (m : ℝ) (U t i) + FH t i =
          scalarHsMul g₀ m (by simpa using (show 1 ≤ m by omega)) (a t)
            (AddCircle.parameterSecondDerivativeHs g₀ m
              (ambientSobolev c₀ gM e he ((m : ℝ) + 2) i + U t i)) + b t i := by
  intro g₀ J K U₂ ha₂ hb₂ hU heq
  let f₀ := ambientSobolev c₀ gM e he ((m : ℝ) + 2)
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => K)
  have hUae : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, K (U t i) = U₂ t i := by
    have hP := P.coeFn_compLpL U
    rw [hU] at hP
    filter_upwards [hP] with t ht
    intro i
    exact congrArg (fun z => z i) ht.symm
  have hf₀ (i : Fin n) : K (f₀ i) = ambientSobolev c₀ gM e he (((2 : ℕ) : ℝ) + 2) i := by
    change tensorHsInclusion _ (ccTensorToHs g₀ 0 ((m : ℝ) + 2) _) = _
    rw [tensorHsInclusion_ccTensorToHs]
    rfl
  have hweak : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ) (K (U t i)) + F₂ t i =
        scalarHsMul g₀ 2 (by norm_num) (J (a t))
          (AddCircle.parameterSecondDerivativeHs g₀ 2 (K (f₀ i + U t i))) + J (b t i) := by
    filter_upwards [ha₂, hb₂, hUae, heq] with t hat hbt hUt het
    intro i
    rw [K.map_add, hf₀, hUt i, hat, hbt i]
    exact het i
  exact AddCircle.exists_timeL2_parabolic_forcing_lift_of_continuousOn
    g₀ (by decide : 1 ≤ 2) hm hT f₀ U F₂ a b ha hb hU hweak

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

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

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear (CircleHsPi circleHsPiInclusion)

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

open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion (parameterDerivativeOperatorBounds parameterDerivativeForcingFieldLift
  parameterDerivative_forcing_lift_of_contraction parameterDerivative_field_lift_of_forcing_lift)

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
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem circle_firstJetHs_eq_of_projection
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (v : CircleHsPi g ι ((k : ℝ) + 3)) (w : CircleHsPi g ι 3)
    (hp : circleHsPiInclusion g ι
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3) v = w) :
    let Em := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
    let Lm := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    Lm (AddCircle.firstJetHs g (k + 2) (Em v)) =
      circleFirstJet g
        (circleHsPiInclusion g ι (by norm_num : (1 : ℝ) + 1 ≤ 3) w) := by
  intro Em Lm
  let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
        ((1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
  let z := K (Em v)
  let L₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  have hcoeff {a b : ℝ} (h : a = b) (u : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 h u).coeff = u.coeff := by
    cases h
    rfl
  have hz : circleHsPiCongr g ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) z =
        circleHsPiInclusion g ι (by norm_num : (1 : ℝ) + 1 ≤ 3) w := by
    rw [← hp]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rw [circleHsPiCongr_apply, hcoeff]
    rfl
  let L₁ := ContinuousLinearMap.piLpMap 2 (fun _ : ι ⊕ ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show ((1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) by exact_mod_cast (show 1 ≤ k + 2 by omega)))
  have hjet := congrArg (fun A => A (Em v))
    (AddCircle.firstJetHs_comp_tensorHsInclusion (ι := ι) g
      (show 1 ≤ k + 2 by omega))
  change AddCircle.firstJetHs g 1 z = L₁ (AddCircle.firstJetHs g (k + 2) (Em v)) at hjet
  have hnormalized := circle_firstJetHs_normalized g z
  rw [hz, hjet] at hnormalized
  change circleFirstJet g
      (circleHsPiInclusion g ι (by norm_num : (1 : ℝ) + 1 ≤ 3) w) =
        L₀ (L₁ (AddCircle.firstJetHs g (k + 2) (Em v))) at hnormalized
  calc
    Lm (AddCircle.firstJetHs g (k + 2) (Em v)) =
        L₀ (L₁ (AddCircle.firstJetHs g (k + 2) (Em v))) := by
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      rfl
    _ = circleFirstJet g
        (circleHsPiInclusion g ι (by norm_num : (1 : ℝ) + 1 ≤ 3) w) := hnormalized.symm

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Geometry.Curvature
variable {ι : Type*} [Fintype ι]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem ambient_spatial_jets_of_sobolev_representative
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ}
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (k : ℕ) {T : ℝ}
    (u : ℝ → CircleHsPi (c₀.pullbackMetric g) (Fin n) ((1 : ℕ) : ℝ))
    (W : ℝ → CircleHsPi (c₀.pullbackMetric g) (Fin n) ((k : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T))
    (hWu : ∀ t ∈ Icc 0 T, circleHsPiInclusion (c₀.pullbackMetric g) (Fin n)
      (by have hk := Nat.cast_nonneg (α := ℝ) k; norm_num at *; linarith :
              ((1 : ℕ) : ℝ) ≤ (k : ℝ) + 2) (W t) = u t) :
    let g₀ := c₀.pullbackMetric g
    let f₀ := ambientSobolev c₀ g e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u t)) (x : AddCircle (1 : ℝ)))
    (∀ t ∈ Icc 0 T, ContDiff ℝ (k + 1) (F t)) ∧
      ∀ j ≤ k + 1, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv j (F p.1) p.2)
        (Icc 0 T ×ˢ univ) := by
  intro g₀ f₀ P S F
  let f := fun t (x : ℝ) =>
    scalarH1PiToContinuous g₀ (P f₀ + S (u t)) (x : AddCircle (1 : ℝ))
  let f₀H := ambientSobolev c₀ g e he ((k : ℝ) + 2)
  have hlow (t : ℝ) (ht : t ∈ Icc 0 T) :
      circleHsPiInclusion g₀ (Fin n)
        (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ (k : ℝ) + 2) (f₀H + W t) = P f₀ + S (u t) := by
    apply PiLp.ext
    intro i
    simp only [circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply, PiLp.add_apply, map_add]
    apply congrArg₂ (· + ·)
    · change tensorHsInclusion (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ (k : ℝ) + 2) (ccTensorToHs g₀ 0 ((k : ℝ) + 2)
          (ambientCoordinateCc c₀ g e he i)) =
        tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
          (ccTensorToHs g₀ 0 (((1 : ℕ) : ℝ) + 2)
          (ambientCoordinateCc c₀ g e he i))
      rw [tensorHsInclusion_ccTensorToHs, tensorHsInclusion_ccTensorToHs]
    · have hi := congrArg (fun z => z i) (hWu t ht)
      have hi' := congrArg (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))) hi
      simpa only [S, circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
        ← tensorHsInclusion_trans_apply] using hi'
  have hjet (j : ℕ) (hj : j ≤ k + 1) :
      (∀ t ∈ Icc 0 T, ContDiff ℝ j (f t)) ∧
        ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv j (f p.1) p.2)
          (Icc 0 T ×ˢ univ) := by
    have hjk : (j : ℝ) + 1 ≤ (k : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hj 1
    let K := circleHsPiInclusion g₀ (Fin n) hjk
    exact AddCircle.contDiff_and_continuousOn_iteratedDeriv_scalarH1PiToContinuous
      g₀ j (fun t => P f₀ + S (u t)) (fun t => K (f₀H + W t))
      (K.continuous.comp_continuousOn (continuousOn_const.add hW)) (fun t ht => by
        refine Eq.trans ?_ (hlow t ht)
        apply PiLp.ext
        intro i
        exact (tensorHsInclusion_trans_apply
          (by norm_num : (1 : ℝ) ≤ (j : ℝ) + 1) hjk ((f₀H + W t) i)).symm)
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have hder (j : ℕ) (t x : ℝ) :
      iteratedDeriv j (F t) x = L (iteratedDeriv j (f t) x) := by
    change iteratedDeriv j (L ∘ f t) x = _
    rw [iteratedDeriv_eq_iteratedFDeriv, L.iteratedFDeriv_comp_left]
    rfl
  constructor
  · intro t ht
    exact L.contDiff.comp ((hjet (k + 1) le_rfl).1 t ht)
  · intro j hj
    have hc := L.continuous.comp_continuousOn (hjet j hj).2
    apply hc.congr
    intro p _
    exact hder j p.1 p.2

private theorem ambient_spatial_jets_of_sobolev_tower
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ}
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    {e : M → EuclideanSpace ℝ (Fin n)}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {T : ℝ}
    (u : ℝ → CircleHsPi (c₀.pullbackMetric g) (Fin n) ((1 : ℕ) : ℝ))
    (htower : ∀ k : ℕ,
      ∃ W : ℝ → CircleHsPi (c₀.pullbackMetric g) (Fin n) ((k : ℝ) + 2),
        ContinuousOn W (Icc 0 T) ∧
          ∀ t ∈ Icc 0 T, circleHsPiInclusion (c₀.pullbackMetric g) (Fin n)
            (by have hk := Nat.cast_nonneg (α := ℝ) k; norm_num at *; linarith :
              ((1 : ℕ) : ℝ) ≤ (k : ℝ) + 2) (W t) = u t) :
    let g₀ := c₀.pullbackMetric g
    let f₀ := ambientSobolev c₀ g e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u t)) (x : AddCircle (1 : ℝ)))
    (∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (F t)) ∧
      ∀ j : ℕ, ContinuousOn
        (fun p : ℝ × ℝ => iteratedFDeriv ℝ j (F p.1) p.2)
        (Icc 0 T ×ˢ univ) := by
  intro g₀ f₀ P S F
  have hfinite (k : ℕ) :
      (∀ t ∈ Icc 0 T, ContDiff ℝ (k + 1) (F t)) ∧
        ∀ j ≤ k + 1, ContinuousOn
          (fun p : ℝ × ℝ => iteratedDeriv j (F p.1) p.2)
          (Icc 0 T ×ˢ univ) := by
    obtain ⟨W, hW, hWu⟩ := htower k
    exact ambient_spatial_jets_of_sobolev_representative c₀ g he k u W hW hWu
  constructor
  · intro t ht
    rw [contDiff_infty]
    intro k
    exact ((hfinite k).1 t ht).of_le (by exact_mod_cast Nat.le_succ k)
  · intro j
    have h := (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j)
      (EuclideanSpace ℝ (Fin n))).continuous.comp_continuousOn
        ((hfinite j).2 j (Nat.le_succ j))
    simp only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply]
    convert! h using 1

private theorem ambient_contDiffOn_of_sobolev_tower
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {n : ℕ} (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D
      (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce)
    (htower : ∀ k : ℕ,
      ∃ W : ℝ → CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((k : ℝ) + 2),
        ContinuousOn W (Icc 0 T) ∧
          ∀ t ∈ Icc 0 T, circleHsPiInclusion (c₀.pullbackMetric (g 0)) (Fin n)
            (by have hk := Nat.cast_nonneg (α := ℝ) k; norm_num at *; linarith :
              ((1 : ℕ) : ℝ) ≤ (k : ℝ) + 2) (W t) = u.toFun t) :
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
      (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
    ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set ℝ)) := by
  intro g₀ f₀ P S F
  have hspatial := ambient_spatial_jets_of_sobolev_tower c₀ (g 0) he u.toFun htower
  have hchart := ambient_chart_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hjet := ambient_firstJet_mem_of_sobolev_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts
  exact contDiffOn_of_parametric_chart_equation_spatial_jets hG β hT isOpen_univ
    (fun t ht => (hspatial.1 t ht).contDiffOn) hspatial.2
    (fun t ht x _ => hjet t ht x)
    (fun t ht x _ => (hchart t ⟨ht.1.le, ht.2.le⟩ x).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
variable {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem scalarVectorTimeCoefficients_continuousOn_higher_order
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (k : ℕ) {T : ℝ} (hT : T ≤ (ScalarVectorTimeCoefficients.radius C))
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1)))
    (W : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (hW : ContinuousOn W (Icc 0 T)) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    u₀ = J (K f₀) →
    (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
    ∃ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1))
      (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 1))),
      ContinuousOn a (Icc 0 T) ∧ ContinuousOn b (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, A (a t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) ∧
      ∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (W t)) := by
  classical
  intro K L J A hu₀ hbound
  let B := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; rfl : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ)))
  let qLow := fun t => B (AddCircle.scalarHsTimeCoordinate g₀ ((k + 1 : ℕ) : ℝ)
    (t, AddCircle.firstJetHs g₀ (k + 1) (K f₀ + W t)))
  let P := ContinuousLinearMap.piLpMap 2 (fun _ : Option (Fin n ⊕ Fin n) => A)
  let q := fun t => scalarH1TimeCoordinate g₀ (t, J (K f₀ + W t))
  have hqLow : ContinuousOn qLow (Icc 0 T) :=
    B.continuous.comp_continuousOn
      ((AddCircle.scalarHsTimeCoordinate g₀ _).continuous.comp_continuousOn
        (continuousOn_id.prodMk ((AddCircle.firstJetHs g₀ (k + 1)).continuous.comp_continuousOn
          (continuousOn_const.add hW))))
  have hq (t : ℝ) : P (qLow t) = q t := by
    have hh := AddCircle.tensorHsInclusion_scalarHsTimeCoordinate g₀
      (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
        (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
      (t, AddCircle.firstJetHs g₀ (k + 1) (K f₀ + W t))
    refine Eq.trans ?_ hh
    apply PiLp.ext
    intro j
    apply TensorHs.ext
    rfl
  let z : Icc (0 : ℝ) T → Metric.closedBall
      (0 : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
        (ScalarVectorTimeCoefficients.radius C) := fun t =>
    ⟨J (W t), by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t t.2⟩
  have hRange (t : ℝ) (ht : t ∈ Icc 0 T) :
      range (scalarH1PiToContinuous g₀ (P (qLow t))) ⊆ S := by
    rw [hq]
    have hh := (ScalarVectorTimeCoefficients.range_mem C) t ⟨ht.1, ht.2.trans hT⟩
      (J (W t)) (z ⟨t, ht⟩).2
    change range (scalarH1PiToContinuous g₀
      (scalarH1TimeCoordinate g₀ (t, J (K f₀ + W t)))) ⊆ S
    rw [map_add, ← hu₀]
    simpa only [zero_add] using hh
  have hcoord (t : ℝ) (x : AddCircle (1 : ℝ)) :
      (fun i : Option (Fin n ⊕ Fin n) => match i with
        | none => 0 + t
        | some j => scalarH1ToContinuous g₀ (u₀ j + J (W t) j) x) =
      scalarH1PiToContinuous g₀ (q t) x := by
    funext i
    cases i with
    | none => simp only [q, scalarH1TimeCoordinate_eval_none, zero_add]
    | some j =>
      simp only [q, map_add, ← hu₀, scalarH1TimeCoordinate_eval_some, PiLp.add_apply]
  obtain ⟨a, ha, hae⟩ := AddCircle.exists_continuousOn_scalarHs_composition
    g₀ k F hF hS qLow hqLow hRange
  have hFi (j : Fin n) : ContDiffOn ℝ ∞ (fun q => G q j) S :=
    contDiffOn_pi.mp hG j
  choose bᵢ hbᵢ hbe using fun j : Fin n =>
    AddCircle.exists_continuousOn_scalarHs_composition
      g₀ k (fun q => G q j) (hFi j) hS qLow hqLow hRange
  let b := fun t => WithLp.toLp 2 (fun j => bᵢ j t)
  have hb : ContinuousOn b (Icc 0 T) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr hbᵢ)
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · intro t ht
    apply scalarH1ToContinuous_injective g₀
    apply ContinuousMap.ext
    intro x
    rw [extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.diffusion C) t (J (W t)) (z ⟨t, ht⟩).2,
      (ScalarVectorTimeCoefficients.diffusion_eval C) t ⟨ht.1, ht.2.trans hT⟩]
    exact (hae t ht x).trans ((congrArg
      (fun v => F (scalarH1PiToContinuous g₀ v x)) (hq t)).trans
        (congrArg F (hcoord t x).symm))
  · intro t ht
    apply PiLp.ext
    intro j
    apply scalarH1ToContinuous_injective g₀
    apply ContinuousMap.ext
    intro x
    change scalarH1ToContinuous g₀ (A (bᵢ j t)) x = _
    rw [extendClosedBall_apply (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.reaction C) t (J (W t)) (z ⟨t, ht⟩).2,
      (ScalarVectorTimeCoefficients.reaction_eval C) t ⟨ht.1, ht.2.trans hT⟩]
    exact (hbe j t ht x).trans ((congrArg
      (fun v => G (scalarH1PiToContinuous g₀ v x) j) (hq t)).trans
        (congrArg (fun v => G v j) (hcoord t x).symm))

private theorem scalarVectorTimeCoefficients_timeL2_higher_order
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    {k : ℕ}
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    u₀ = J (K f₀) →
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ Z : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T,
      ∀ W : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)),
      ContinuousOn W (Icc 0 T) →
      W =ᵐ[timeMeasure T] (fun t => K (Z t)) →
      (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∀ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1))
        (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 1))),
      ContinuousOn a (Icc 0 T) → ContinuousOn b (Icc 0 T) →
      (∀ t ∈ Icc 0 T, A (a t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) →
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) →
      ∃ (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T)
        (bHigh : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 2))) T),
        (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))
          =ᵐ[timeMeasure T] b := by
  classical
  intro K L J A Q hu₀ T hT Z W hW hWZ hbound a b ha hb hae hbe
  have htime : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  have haactual : (fun t => A (a t)) =ᵐ[timeMeasure T]
      (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) := by
    filter_upwards [htime] with t htt
    exact hae t htt
  obtain ⟨aHigh, haHigh⟩ := scalarVectorTimeCoefficients_diffusion_higher_order g₀ F G S u₀ C hF hS
    k T hT f₀ Z W hW a (memLp_of_continuousOn ha).aestronglyMeasurable
      hu₀ hWZ hbound haactual
  have hbcoord (j : Fin n) : AEStronglyMeasurable (fun t => b t j) (timeMeasure T) :=
    (memLp_of_continuousOn
      ((PiLp.proj (𝕜 := ℝ) 2
        (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 1)) j).continuous.comp_continuousOn
          hb)).aestronglyMeasurable
  have hbactual (j : Fin n) : (fun t => A (b t j)) =ᵐ[timeMeasure T]
      (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t (J (W t)) j) := by
    filter_upwards [htime] with t htt
    exact congrArg (fun z => z j) (hbe t htt)
  have hblift (j : Fin n) : ∃ z : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T,
      (fun t => Q (z t)) =ᵐ[timeMeasure T] (fun t => b t j) :=
    scalarVectorTimeCoefficients_reaction_higher_order g₀ F G S u₀ C j
      (contDiffOn_pi.mp hG j) hS k T hT f₀ Z W hW
      (fun t => b t j) (hbcoord j) hu₀ hWZ hbound (hbactual j)
  choose B hB using hblift
  let bHigh := (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm (WithLp.toLp 2 B)
  have hbHigh : (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q)
      (bHigh t)) =ᵐ[timeMeasure T] b := by
    have hBall : ∀ᵐ t ∂timeMeasure T, ∀ j, Q (B j t) = b t j := ae_all_iff.mpr hB
    filter_upwards [Lp.piLpEquiv_symm_apply (𝕜 := ℝ) (timeMeasure T) (WithLp.toLp 2 B),
      hBall] with t hbₜ hBₜ
    change bHigh t = WithLp.toLp 2 (fun j => B j t) at hbₜ
    rw [hbₜ]
    apply PiLp.ext
    exact hBₜ
  exact ⟨aHigh, bHigh, haHigh, hbHigh⟩

private theorem scalarVectorTimeCoefficients_higher_order
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    {k : ℕ} (hk : 1 ≤ k)
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          linarith : (2 : ℝ) ≤ (k : ℝ) + 1)
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    u₀ = J (K f₀) →
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ Z : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T,
      ∀ W : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)),
      ContinuousOn W (Icc 0 T) →
      W =ᵐ[timeMeasure T] (fun t => K (Z t)) →
      (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∀ (a₂ : ℝ → TensorHs g₀ 0 0 2)
        (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)),
      (∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) →
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 2)) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) →
      ∃ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1))
        (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 1)))
        (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T)
        (bHigh : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 2))) T),
        ContinuousOn a (Icc 0 T) ∧ ContinuousOn b (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, A (a t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, P (a t) = a₂ t) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) ∧
        (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a ∧
        (fun t =>
          ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t)) =ᵐ[timeMeasure T] b ∧
        (fun t => P (Q (aHigh t))) =ᵐ[timeMeasure T] a₂ ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P)
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))) =ᵐ[timeMeasure T] b₂ := by
  classical
  intro K L J A P Q hu₀ T hT Z W hW hWZ hbound a₂ b₂ ha₂ hb₂
  obtain ⟨a, b, ha, hb, hae, hbe⟩ := scalarVectorTimeCoefficients_continuousOn_higher_order
    g₀ F G S u₀ C hF hG hS k hT f₀ W hW hu₀ hbound
  obtain ⟨aHigh, bHigh, haHigh, hbHigh⟩ :=
    scalarVectorTimeCoefficients_timeL2_higher_order g₀ F G S u₀ C hF hG hS f₀
      hu₀ T hT Z W hW hWZ hbound a b ha hb hae hbe
  have htime : ∀ᵐ t ∂timeMeasure T, t ∈ Icc 0 T := ae_restrict_mem measurableSet_Icc
  have hap (t : ℝ) (htt : t ∈ Icc 0 T) : P (a t) = a₂ t := by
    apply tensorHsInclusion_injective (by norm_num : (1 : ℝ) ≤ 2)
    have hh : tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (P (a t)) = A (a t) := by
      apply TensorHs.ext
      rfl
    rw [hh, hae t htt, ha₂ t htt]
  have hbp (t : ℝ) (htt : t ∈ Icc 0 T) :
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t := by
    apply PiLp.ext
    intro j
    apply tensorHsInclusion_injective (by norm_num : (1 : ℝ) ≤ 2)
    have hh : tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (P (b t j)) = A (b t j) := by
      apply TensorHs.ext
      rfl
    change tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (P (b t j)) = _
    rw [hh]
    exact (congrArg (fun z => z j) (hbe t htt)).trans
      (congrArg (fun z => z j) (hb₂ t htt)).symm
  refine ⟨a, b, aHigh, bHigh, ha, hb, hae, hbe, hap, hbp, haHigh, hbHigh, ?_, ?_⟩
  · filter_upwards [htime, haHigh] with t htt hat
    rw [hat]
    exact hap t htt
  · filter_upwards [htime, hbHigh] with t htt hbt
    rw [hbt]
    exact hbp t htt

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private theorem ambient_coefficients_higher_order
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {k : ℕ} (hk : 1 ≤ k) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) + 1))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)))
    let J := L.comp (AddCircle.firstJetHs g₀ (k + 1))
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          linarith : (2 : ℝ) ≤ (k : ℝ) + 1)
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2)
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ Z : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 2 : ℕ) : ℝ) + 1))) T,
      ∀ W : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)),
      ContinuousOn W (Icc 0 T) →
      W =ᵐ[timeMeasure T] (fun t => K (Z t)) →
      (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∀ (a₂ : ℝ → TensorHs g₀ 0 0 2)
        (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)),
      (∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) →
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 2)) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) →
      ∃ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 1))
        (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 1)))
        (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 2)) T)
        (bHigh : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 2))) T),
        ContinuousOn a (Icc 0 T) ∧ ContinuousOn b (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, A (a t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, P (a t) = a₂ t) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) ∧
        (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a ∧
        (fun t =>
          ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t)) =ᵐ[timeMeasure T] b ∧
        (fun t => P (Q (aHigh t))) =ᵐ[timeMeasure T] a₂ ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P)
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))) =ᵐ[timeMeasure T] b₂ := by
  intro C g₀ K L J A P Q T hT Z W hW hWZ hbound a₂ b₂ ha₂ hb₂
  let f₀ := ambientSobolev c₀ (g 0) e he (((k + 2 : ℕ) : ℝ) + 1)
  obtain ⟨hS, hF, hReaction⟩ := geometric_coefficients_contDiffOn hG β
  exact scalarVectorTimeCoefficients_higher_order g₀ _ _ _ _ C hF hReaction hS hk f₀
    (ambientFirstJet_eq_higher_initialJet c₀ (g 0) he k)
    T hT Z W hW hWZ hbound a₂ b₂ ha₂ hb₂

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem firstJetHs_successor_normalization
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ)
    (x : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 3))) :
    let E := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let Lraw := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ)))
    (Lraw.comp (AddCircle.firstJetHs g₀ (k + 1 + 1))) (E x) =
      (L.comp ((AddCircle.firstJetHs g₀ (k + 2)).comp E)) x := by
  intro E L Lraw
  apply PiLp.ext
  intro i
  apply TensorHs.ext
  rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation (TensorHs tensorHsInclusion)
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem circleHsPi_successor_normalization
    {ι : Type*} [Fintype ι]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (T : ℝ)
    (Z : timeL2 (PiLp 2 (fun _ : ι => TensorHs g₀ 0 0 ((k : ℝ) + 4))) T)
    (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g₀ 0 0 ((k : ℝ) + 3))) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4))
    let E := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
    let EZ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith only : ((k + 1 + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 4))
    let Kraw := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1))
    ContinuousOn W (Icc 0 T) →
    W =ᵐ[timeMeasure T] (fun t => K (Z t)) →
    ContinuousOn (fun t => E (W t)) (Icc 0 T) ∧
      (fun t => E (W t)) =ᵐ[timeMeasure T]
        (fun t => Kraw ((EZ.compLpL 2 (timeMeasure T) Z) t)) := by
  intro K E EZ Kraw hW hWZ
  refine ⟨E.continuous.comp_continuousOn hW, ?_⟩
  filter_upwards [hWZ, EZ.coeFn_compLpL Z] with t hwt hzt
  rw [hzt, hwt]
  apply PiLp.ext
  intro i
  apply TensorHs.ext
  rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
variable {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private def mapTimeL2Real {X Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedSpace ℝ X] [NormedSpace ℝ Y]
    (T : ℝ) (L : X →L[ℝ] Y) (z : timeL2 X T) : timeL2 Y T :=
  L.compLpL 2 (timeMeasure T) z

private theorem mapTimeL2Real_ae {X Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedSpace ℝ X] [NormedSpace ℝ Y]
    (T : ℝ) (L : X →L[ℝ] Y) (z : timeL2 X T) :
    mapTimeL2Real T L z =ᵐ[timeMeasure T] (fun t => L (z t)) :=
  L.coeFn_compLpL z

private theorem exists_four_elim
    {A B C D : Sort*} {P : A → B → C → D → Prop} {Q : Prop}
    (h : ∃ a b c d, P a b c d)
    (hQ : ∀ a b c d, P a b c d → Q) : Q := by
  obtain ⟨a, b, c, d, hp⟩ := h
  exact hQ a b c d hp

private theorem scalarVectorTimeCoefficients_reindex
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (T : ℝ)
    (f₁ : ℝ → TensorHs g₀ 0 0 1)
    (g₁ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 1))
    (a₂ : ℝ → TensorHs g₀ 0 0 2)
    (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2))
    (ar : ℝ → TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1))
    (br : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 1)))
    (aHr : timeL2 (TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2)) T)
    (bHr : timeL2
      (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 : ℕ) : ℝ) + 2))) T) :
    let Araw := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          push_cast
          linarith only [hk] : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1)
    let Praw := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          push_cast
          linarith only [hk] : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1)
    let Qraw := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith only : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 2)
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) ≤ (k : ℝ) + 2)
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith only : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
    ContinuousOn ar (Icc 0 T) → ContinuousOn br (Icc 0 T) →
    (∀ t ∈ Icc 0 T, Araw (ar t) = f₁ t) →
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Araw) (br t) =
      g₁ t) →
    (∀ t ∈ Icc 0 T, Praw (ar t) = a₂ t) →
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Praw) (br t) =
      b₂ t) →
    (fun t => Qraw (aHr t)) =ᵐ[timeMeasure T] ar →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Qraw) (bHr t))
      =ᵐ[timeMeasure T] br →
    ∃ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 2))
      (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 2)))
      (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 3)) T)
      (bHigh : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 3))) T),
      ContinuousOn a (Icc 0 T) ∧ ContinuousOn b (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, A (a t) = f₁ t) ∧
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
        g₁ t) ∧
      (∀ t ∈ Icc 0 T, P (a t) = a₂ t) ∧
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) ∧
      (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))
        =ᵐ[timeMeasure T] b ∧
      (fun t => P (Q (aHigh t))) =ᵐ[timeMeasure T] a₂ ∧
      (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P)
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t)))
          =ᵐ[timeMeasure T] b₂ := by
  intro Araw Praw Qraw A P Q har hbr hae hbe hap hbp haH hbH
  let O := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by push_cast; linarith only : (k : ℝ) + 2 ≤ ((k + 1 : ℕ) : ℝ) + 1)
  let OH := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by push_cast; linarith only : (k : ℝ) + 3 ≤ ((k + 1 : ℕ) : ℝ) + 2)
  let OP := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => O)
  let OHP := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => OH)
  let a := fun t => O (ar t)
  let b := fun t => OP (br t)
  let aHigh := mapTimeL2Real T OH aHr
  let bHigh := mapTimeL2Real T OHP bHr
  have ha : ContinuousOn a (Icc 0 T) := O.continuous.comp_continuousOn har
  have hb : ContinuousOn b (Icc 0 T) := OP.continuous.comp_continuousOn hbr
  have haeval (t : ℝ) (ht : t ∈ Icc 0 T) : A (a t) =
      f₁ t := by
    refine Eq.trans ?_ (hae t ht)
    apply TensorHs.ext
    rfl
  have hbeval (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
      g₁ t := by
    refine Eq.trans ?_ (hbe t ht)
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have ha₂proj (t : ℝ) (ht : t ∈ Icc 0 T) : P (a t) = a₂ t := by
    refine Eq.trans ?_ (hap t ht)
    apply TensorHs.ext
    rfl
  have hb₂proj (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t := by
    refine Eq.trans ?_ (hbp t ht)
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have haHigh : (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a := by
    filter_upwards [mapTimeL2Real_ae T OH aHr, haH] with t hot hht
    change Q (aHigh t) = O (ar t)
    rw [hot, ← hht]
    apply TensorHs.ext
    rfl
  have hab : ((k + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + 2 := by
    linarith only
  have hcd : (k : ℝ) + 2 ≤ (k : ℝ) + 3 := by
    linarith only
  have hca : (k : ℝ) + 2 ≤ ((k + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    linarith only
  have hdb : (k : ℝ) + 3 ≤ ((k + 1 : ℕ) : ℝ) + 2 := by
    push_cast
    linarith only
  have hvector := tensorHsPi_ae_eq_of_inclusion
    (ι := Fin n) (Ω := ℝ) (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
    g₀ 0 0 hab hcd hca hdb (p := 2) (μ := timeMeasure T) bHr br
  whnf at hvector
  have hvectorAE := hvector hbH
  have hbHigh : (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q)
      (bHigh t)) =ᵐ[timeMeasure T] b := by
    dsimp only [bHigh, b, mapTimeL2Real, OP, OHP, O, OH, Q]
    with_reducible exact hvectorAE
  refine ⟨a, b, aHigh, bHigh, ha, hb, haeval, hbeval, ha₂proj, hb₂proj,
    haHigh, hbHigh, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc, haHigh] with t htt hat
    rw [hat]
    exact ha₂proj t htt
  · filter_upwards [ae_restrict_mem measurableSet_Icc, hbHigh] with t htt hbt
    rw [hbt]
    exact hb₂proj t htt


private theorem scalarVectorTimeCoefficients_successor_order
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 1))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    (k : ℕ)
    (f₀ : PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 (((k + 1 + 2 : ℕ) : ℝ) + 1))) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4))
    let E := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let J := L.comp ((AddCircle.firstJetHs g₀ (k + 2)).comp E)
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k
          linarith : (2 : ℝ) ≤ (k : ℝ) + 2)
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
    let Kraw := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith :
          ((k + 1 + 1 : ℕ) : ℝ) + 1 ≤ ((k + 1 + 2 : ℕ) : ℝ) + 1))
    u₀ = L (AddCircle.firstJetHs g₀ (k + 2) (Kraw f₀)) →
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ Z : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 4))) T,
      ∀ W : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 3)),
      ContinuousOn W (Icc 0 T) →
      W =ᵐ[timeMeasure T] (fun t => K (Z t)) →
      (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∀ (a₂ : ℝ → TensorHs g₀ 0 0 2)
        (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)),
      (∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) →
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 2)) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) →
      ∃ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 2))
        (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 2)))
        (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 3)) T)
        (bHigh : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 3))) T),
        ContinuousOn a (Icc 0 T) ∧ ContinuousOn b (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, A (a t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, P (a t) = a₂ t) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) ∧
        (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))
          =ᵐ[timeMeasure T] b ∧
        (fun t => P (Q (aHigh t))) =ᵐ[timeMeasure T] a₂ ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P)
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))) =ᵐ[timeMeasure T] b₂ := by
  intro K E L J A P Q Kraw hu₀ T hT Z W hW hWZ hbound a₂ b₂ ha₂ hb₂
  let EZ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
    tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only : ((k + 1 + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 4))
  let Zraw := EZ.compLpL 2 (timeMeasure T) Z
  let Wraw := fun t => E (W t)
  have hnormalize := circleHsPi_successor_normalization g₀ k T Z W hW hWZ
  have hWraw : ContinuousOn Wraw (Icc 0 T) := hnormalize.1
  have hWZraw : Wraw =ᵐ[timeMeasure T] (fun t => Kraw (Zraw t)) := hnormalize.2
  have hraw := scalarVectorTimeCoefficients_higher_order g₀ F G S u₀ C hF hG hS
    (k := k + 1) (by omega) f₀
  whnf at hraw
  have hs0 := hraw hu₀ T hT
  have hs1 := hs0 Zraw Wraw hWraw hWZraw
  have hsBound := hs1 (fun t ht => by
    refine le_trans ?_ (hbound t ht)
    exact le_of_eq (congrArg norm (firstJetHs_successor_normalization g₀ k (W t))))
  have hs2 := hsBound a₂ b₂
  have hsA := hs2 (fun t ht => by
    refine (ha₂ t ht).trans ?_
    exact congrArg
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t)
      (firstJetHs_successor_normalization g₀ k (W t)).symm)
  have hreactionJet (t : ℝ) := congrArg
    (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.reaction C) t)
    (firstJetHs_successor_normalization g₀ k (W t))
  have hs3 := hsA (fun t ht => by
    with_reducible exact ((hb₂ t ht).trans (hreactionJet t).symm))
  refine exists_four_elim hs3 ?_
  intro ar br aHr bHr hrawFacts
  have har := hrawFacts.1
  have hbr := hrawFacts.2.1
  have hae := hrawFacts.2.2.1
  have hbe := hrawFacts.2.2.2.1
  have hap := hrawFacts.2.2.2.2.1
  have hbp := hrawFacts.2.2.2.2.2.1
  have haH := hrawFacts.2.2.2.2.2.2.1
  have hbH := hrawFacts.2.2.2.2.2.2.2.1
  exact scalarVectorTimeCoefficients_reindex g₀ k T
    (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.diffusion C) t (J (W t)))
    (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.reaction C) t (J (W t)))
    a₂ b₂ ar br aHr bHr har hbr
    (fun t ht => (hae t ht).trans (congrArg
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t)
      (firstJetHs_successor_normalization g₀ k (W t))))
    (fun t ht => (hbe t ht).trans (congrArg
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t)
      (firstJetHs_successor_normalization g₀ k (W t))))
    hap hbp haH hbH

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private theorem ambient_coefficients_successor_order
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    (k : ℕ) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4))
    let E := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let J := L.comp ((AddCircle.firstJetHs g₀ (k + 2)).comp E)
    let A := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2)
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have := Nat.cast_nonneg (α := ℝ) k
          linarith : (2 : ℝ) ≤ (k : ℝ) + 2)
    let Q := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
    ∀ T : ℝ, T ≤ (ScalarVectorTimeCoefficients.radius C) →
      ∀ Z : timeL2
        (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 4))) T,
      ∀ W : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 3)),
      ContinuousOn W (Icc 0 T) →
      W =ᵐ[timeMeasure T] (fun t => K (Z t)) →
      (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
      ∀ (a₂ : ℝ → TensorHs g₀ 0 0 2)
        (b₂ : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 2)),
      (∀ t ∈ Icc 0 T, tensorHsInclusion (by norm_num : (1 : ℝ) ≤ 2) (a₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) →
      (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 2)) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) →
      ∃ (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 2))
        (b : ℝ → PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 2)))
        (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 3)) T)
        (bHigh : timeL2 (PiLp 2 (fun _ : Fin n => TensorHs g₀ 0 0 ((k : ℝ) + 3))) T),
        ContinuousOn a (Icc 0 T) ∧ ContinuousOn b (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, A (a t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A) (b t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.reaction C) t (J (W t))) ∧
        (∀ t ∈ Icc 0 T, P (a t) = a₂ t) ∧
        (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) ∧
        (fun t => Q (aHigh t)) =ᵐ[timeMeasure T] a ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))
          =ᵐ[timeMeasure T] b ∧
        (fun t => P (Q (aHigh t))) =ᵐ[timeMeasure T] a₂ ∧
        (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P)
          (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Q) (bHigh t))) =ᵐ[timeMeasure T] b₂ := by
  intro C g₀ K E L J A P Q T hT Z W hW hWZ hbound a₂ b₂ ha₂ hb₂
  let f₀ := ambientSobolev c₀ (g 0) e he (((k + 1 + 2 : ℕ) : ℝ) + 1)
  obtain ⟨hS, hF, hReaction⟩ := geometric_coefficients_contDiffOn hG β
  exact scalarVectorTimeCoefficients_successor_order g₀ _ _ _ _ C hF hReaction hS k f₀
    (ambientFirstJet_eq_higher_initialJet c₀ (g 0) he (k + 1))
    T hT Z W hW hWZ hbound a₂ b₂ ha₂ hb₂

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem circle_firstJetHs_coefficients_of_projection
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (T ρ : ℝ)
    (W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3))
    (W₃ : ℝ → CircleHsPi g₀ (Fin n) 3)
    (a₂ : ℝ → TensorHs g₀ 0 0 2)
    (b₂ : ℝ → CircleHsPi g₀ (Fin n) 2)
    (diffusion : ℝ → CircleHsPi g₀ (Fin n ⊕ Fin n) 1 → TensorHs g₀ 0 0 1)
    (reaction : ℝ → CircleHsPi g₀ (Fin n ⊕ Fin n) 1 → CircleHsPi g₀ (Fin n) 1) :
    let P := circleHsPiInclusion g₀ (Fin n)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (3 : ℝ) ≤ (k : ℝ) + 3)
    let J₃ := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) + 1 ≤ 3))
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 1 ≤ (k : ℝ) + 3))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ⊕ Fin n =>
      tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by have hk := Nat.cast_nonneg (α := ℝ) k
            push_cast
            linarith only [hk] : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
    let J := L.comp ((AddCircle.firstJetHs g₀ (k + 2)).comp E)
    (∀ t ∈ Icc 0 T, P (W t) = W₃ t) →
    (∀ t ∈ Icc 0 T, ‖J₃ (W₃ t)‖ ≤ ρ) →
    (∀ t ∈ Icc 0 T, A₂ (a₂ t) = diffusion t (J₃ (W₃ t))) →
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) =
      reaction t (J₃ (W₃ t))) →
    (∀ t ∈ Icc 0 T, ‖J (W t)‖ ≤ ρ) ∧
    (∀ t ∈ Icc 0 T, A₂ (a₂ t) = diffusion t (J (W t))) ∧
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) =
      reaction t (J (W t))) := by
  intro P J₃ A₂ E L J hWP hbound hdiffusion hreaction
  have hjet (t : ℝ) (htt : t ∈ Icc 0 T) : J (W t) = J₃ (W₃ t) :=
    circle_firstJetHs_eq_of_projection g₀ k (W t) (W₃ t) (hWP t htt)
  refine ⟨?_, ?_, ?_⟩
  · intro t htt
    exact (le_of_eq (congrArg norm (hjet t htt))).trans (hbound t htt)
  · intro t htt
    exact (hdiffusion t htt).trans (congrArg (diffusion t) (hjet t htt).symm)
  · intro t htt
    exact (hreaction t htt).trans (congrArg (reaction t) (hjet t htt).symm)

private theorem circle_sobolev_boost_data_reindex
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (T : ℝ)
    (W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3))
    (V : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T)
    (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 2))
    (b : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 2))
    (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 3)) T)
    (bHigh : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 3)) T)
    (a₂ : ℝ → TensorHs g₀ 0 0 2) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by linarith only : (k : ℝ) + 3 ≤ (k : ℝ) + 4)
    let Ih := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith only : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
    let Ia := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) ≤ (k : ℝ) + 2)
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    let N₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) ≤ (k : ℝ) + 2)
    let N₂V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₂)
    let N₄ := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
    let VN := N₄.compLpL 2 (timeMeasure T) V
    let aN := fun t => N₂ (a t)
    let bN := fun t => N₂V (b t)
    let N₃ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only : ((k + 3 : ℕ) : ℝ) ≤ (k : ℝ) + 3)
    let N₃V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₃)
    let WN := fun t => N₃V (W t)
    let aHN := N₃.compLpL 2 (timeMeasure T) aHigh
    let bHN := N₃V.compLpL 2 (timeMeasure T) bHigh
    let IhN := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
        ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let I₁N := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
        ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
    let KW := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only :
        ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
    ContinuousOn W (Icc 0 T) →
    W =ᵐ[timeMeasure T] (fun t => R (V t)) →
    (fun t => Ih (aHigh t)) =ᵐ[timeMeasure T] a →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Ih) (bHigh t))
      =ᵐ[timeMeasure T] b →
    (fun t => Ia (Ih (aHigh t))) =ᵐ[timeMeasure T] a₂ →
    ContinuousOn WN (Icc 0 T) ∧
    (fun t => IhN (aHN t)) =ᵐ[timeMeasure T] aN ∧
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, IhN (bHN t i) = bN t i) ∧
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, WN t i = KW (VN t i)) ∧
    (fun t => I₁N (aHN t)) =ᵐ[timeMeasure T] (fun t => E₁ (A₂ (a₂ t))) := by
  intro R Ih Ia A₂ E₁ N₂ N₂V N₄ VN aN bN N₃ N₃V WN aHN bHN IhN I₁N KW
    hW hWV haHigh hbHigh haHigh₂
  have hWN : ContinuousOn WN (Icc 0 T) := N₃V.continuous.comp_continuousOn hW
  have haHN : (fun t => IhN (aHN t)) =ᵐ[timeMeasure T] aN := by
    filter_upwards [N₃.coeFn_compLpL aHigh, haHigh] with t hnt hht
    change IhN (aHN t) = N₂ (a t)
    rw [hnt, ← hht]
    apply TensorHs.ext
    rfl
  have hbHN : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, IhN (bHN t i) = bN t i := by
    filter_upwards [N₃V.coeFn_compLpL bHigh, hbHigh] with t hnt hht
    intro i
    rw [hnt]
    change IhN (N₃ (bHigh t i)) = N₂ (b t i)
    rw [← hht]
    apply TensorHs.ext
    rfl
  have hWNVN : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, WN t i = KW (VN t i) := by
    filter_upwards [hWV, N₄.coeFn_compLpL V] with t hwt hnt
    intro i
    change N₃ (W t i) = KW (VN t i)
    rw [hwt, hnt]
    apply TensorHs.ext
    rfl
  have hprincipal : (fun t => I₁N (aHN t)) =ᵐ[timeMeasure T]
      (fun t => E₁ (A₂ (a₂ t))) := by
    filter_upwards [N₃.coeFn_compLpL aHigh, haHigh₂] with t hnt ht
    rw [hnt]
    have hh := congrArg (E₁.comp A₂) ht
    refine Eq.trans ?_ hh
    apply TensorHs.ext
    rfl
  exact ⟨hWN, haHN, hbHN, hWNVN, hprincipal⟩

private theorem circle_sobolev_successor_of_forcing_lift
    {n : ℕ} (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) {T : ℝ} (hT : 0 < T)
    (Fm : timeL2 (CircleHsPi g₀ (Fin n) ((k + 2 : ℕ) : ℝ)) T)
    (FH : timeL2 (CircleHsPi g₀ (Fin n) 1) T)
    (W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3))
    (V : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T) :
    let N₄ := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
    let VN := N₄.compLpL 2 (timeMeasure T) V
    let R := circleHsPiInclusion g₀ (Fin n)
      (by linarith only : (k : ℝ) + 3 ≤ (k : ℝ) + 4)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by linarith only : (k : ℝ) + 4 ≤ (k : ℝ) + 5)
    ContinuousOn W (Icc 0 T) →
    W =ᵐ[timeMeasure T] (fun t => R (V t)) →
    VN = maximalRegularityDuhamelVectorField hT 0 Fm →
    iteratedParameterDerivativeDuhamelForcing g₀ 0 (k + 2) hT Fm =
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) ≤ (1 : ℝ)))).compLpL
            2 (timeMeasure T) FH →
    ∃ (Wnew : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 4))
      (Vnew : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 5)) T),
      ContinuousOn Wnew (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, R (Wnew t) = W t) ∧
      S.compLpL 2 (timeMeasure T) Vnew = V ∧
      Wnew =ᵐ[timeMeasure T] (fun t => S (Vnew t)) := by
  intro N₄ VN R S hW hWV hVF hFH
  have hVN : VN =ᵐ[timeMeasure T] (fun t => N₄ (V t)) := N₄.coeFn_compLpL V
  obtain ⟨Wraw, hWraw, _, hWrawF⟩ :=
    exists_continuousOn_representative_of_iteratedParameterDerivative_forcing_lift
      g₀ (k + 2) hT Fm FH hFH
  obtain ⟨Vraw, hVrawF⟩ :=
    exists_timeL2_tensorHsInclusion_eq_of_iteratedParameterDerivative_forcing_lift
      g₀ (k + 2) hT Fm FH hFH
  let B₄ := circleHsPiInclusion g₀ (Fin n)
    (by push_cast; linarith only : (k : ℝ) + 4 ≤ ((k + 2 : ℕ) : ℝ) + 2)
  let B₅ := circleHsPiInclusion g₀ (Fin n)
    (by push_cast; linarith only : (k : ℝ) + 5 ≤ ((k + 2 : ℕ) : ℝ) + 3)
  let Wnew := fun t => B₄ (Wraw t)
  let Vnew := B₅.compLpL 2 (timeMeasure T) Vraw
  have hWnew : ContinuousOn Wnew (Icc 0 T) := B₄.continuous.comp_continuousOn hWraw
  have hWrawVN : Wraw =ᵐ[timeMeasure T] VN := by
    rw [hVF]
    exact hWrawF
  have hWnewV : Wnew =ᵐ[timeMeasure T] V := by
    filter_upwards [hWrawVN, hVN] with t hwt hnt
    change B₄ (Wraw t) = V t
    rw [hwt, hnt]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  let Sraw := circleHsPiInclusion g₀ (Fin n)
    (by linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ) + 3)
  have hVrawVN : Sraw.compLpL 2 (timeMeasure T) Vraw = VN := hVrawF.trans hVF.symm
  have hVnewV : S.compLpL 2 (timeMeasure T) Vnew = V := by
    apply Lp.ext
    have hraw := Sraw.coeFn_compLpL Vraw
    rw [hVrawVN] at hraw
    filter_upwards [S.coeFn_compLpL Vnew, B₅.coeFn_compLpL Vraw, hraw, hVN]
      with t hst hbt hrt hnt
    rw [hst, hbt]
    have hc : S (B₅ (Vraw t)) = B₄ (Sraw (Vraw t)) := by
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      rfl
    rw [hc, ← hrt, hnt]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have hWnewW : ∀ t ∈ Icc 0 T, R (Wnew t) = W t := by
    apply Measure.eqOn_Icc_of_ae_eq (μ := (volume : Measure ℝ)) (ne_of_lt hT)
      _ (R.continuous.comp_continuousOn hWnew) hW
    filter_upwards [hWnewV, hWV] with t ht hwt
    change R (Wnew t) = W t
    rw [ht]
    exact hwt.symm
  have hWnewVnew : Wnew =ᵐ[timeMeasure T] (fun t => S (Vnew t)) := by
    have hh := S.coeFn_compLpL Vnew
    rw [hVnewV] at hh
    exact hWnewV.trans hh
  exact ⟨Wnew, Vnew, hWnew, hWnewW, hVnewV, hWnewVnew⟩

private theorem circle_sobolev_forcing_data_reindex
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) (T : ℝ)
    (V : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T)
    (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 2))
    (b : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 2))
    (a₂ : ℝ → TensorHs g₀ 0 0 2)
    (b₂ : ℝ → CircleHsPi g₀ (Fin n) 2)
    (U₂ : timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℝ) + 2)) T) :
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) ≤ (k : ℝ) + 2)
    let Q := circleHsPiInclusion g₀ (Fin n)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) + 2 ≤ (k : ℝ) + 4)
    let N₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) ≤ (k : ℝ) + 2)
    let N₂V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₂)
    let N₄ := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
    let VN := N₄.compLpL 2 (timeMeasure T) V
    let aN := fun t => N₂ (a t)
    let bN := fun t => N₂V (b t)
    let JN := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by exact_mod_cast (show 2 ≤ k + 2 by omega) :
        ((2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))
    let KN := circleHsPiInclusion g₀ (Fin n)
      (by exact_mod_cast (show 2 + 2 ≤ (k + 2) + 2 by omega) :
        ((2 : ℕ) : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ) + 2)
    ContinuousOn a (Icc 0 T) → ContinuousOn b (Icc 0 T) →
    (∀ t ∈ Icc 0 T, P (a t) = a₂ t) →
    (∀ t ∈ Icc 0 T,
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) →
    Q.compLpL 2 (timeMeasure T) V = U₂ →
    ContinuousOn aN (Icc 0 T) ∧ ContinuousOn bN (Icc 0 T) ∧
    (fun t => JN (aN t)) =ᵐ[timeMeasure T] a₂ ∧
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, JN (bN t i) = b₂ t i) ∧
    KN.compLpL 2 (timeMeasure T) VN = U₂ := by
  intro P Q N₂ N₂V N₄ VN aN bN JN KN ha hb ha₂proj hb₂proj hVQ
  have haN : ContinuousOn aN (Icc 0 T) := N₂.continuous.comp_continuousOn ha
  have hbN : ContinuousOn bN (Icc 0 T) := N₂V.continuous.comp_continuousOn hb
  have hapN : (fun t => JN (aN t)) =ᵐ[timeMeasure T] a₂ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t htt
    refine Eq.trans ?_ (ha₂proj t htt)
    apply TensorHs.ext
    rfl
  have hbpN : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, JN (bN t i) = b₂ t i := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t htt
    intro i
    refine Eq.trans ?_ (congrArg (fun z => z i) (hb₂proj t htt))
    apply TensorHs.ext
    rfl
  have hVN : VN =ᵐ[timeMeasure T] (fun t => N₄ (V t)) := N₄.coeFn_compLpL V
  have hVNQ : KN.compLpL 2 (timeMeasure T) VN = U₂ := by
    apply Lp.ext
    have hQ := Q.coeFn_compLpL V
    rw [hVQ] at hQ
    filter_upwards [KN.coeFn_compLpL VN, hVN, hQ] with t hkt hnt hqt
    rw [hkt, hnt, hqt]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  exact ⟨haN, hbN, hapN, hbpN, hVNQ⟩

private theorem circle_sobolev_successor_of_principal_norm_lt_one
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (k : ℕ) {T : ℝ} (hT : 0 < T)
    (Fm : timeL2 (CircleHsPi g₀ (Fin n) ((k + 2 : ℕ) : ℝ)) T)
    (fHigh : CircleHsPi g₀ (Fin n) (((k + 3 : ℕ) : ℝ) + 2))
    (W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3))
    (V : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T)
    (a : ℝ → TensorHs g₀ 0 0 ((k : ℝ) + 2))
    (b : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 2))
    (aHigh : timeL2 (TensorHs g₀ 0 0 ((k : ℝ) + 3)) T)
    (bHigh : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 3)) T)
    (a₂ : ℝ → TensorHs g₀ 0 0 2) (C2h C2l : ℝ≥0) :
    let R := circleHsPiInclusion g₀ (Fin n)
      (by linarith only : (k : ℝ) + 3 ≤ (k : ℝ) + 4)
    let S := circleHsPiInclusion g₀ (Fin n)
      (by linarith only : (k : ℝ) + 4 ≤ (k : ℝ) + 5)
    let Ih := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by linarith only : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
    let Ia := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) ≤ (k : ℝ) + 2)
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    let N₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) ≤ (k : ℝ) + 2)
    let N₂V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₂)
    let N₄ := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
    let VN := N₄.compLpL 2 (timeMeasure T) V
    let aN := fun t => N₂ (a t)
    let bN := fun t => N₂V (b t)
    let Pb := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only :
        ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
    ContinuousOn W (Icc 0 T) →
    W =ᵐ[timeMeasure T] (fun t => R (V t)) →
    (fun t => Ih (aHigh t)) =ᵐ[timeMeasure T] a →
    (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => Ih) (bHigh t))
      =ᵐ[timeMeasure T] b →
    (fun t => Ia (Ih (aHigh t))) =ᵐ[timeMeasure T] a₂ →
    VN = maximalRegularityDuhamelVectorField hT 0 Fm →
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ)
          (VN t i) + Fm t i =
        scalarHsMul g₀ (k + 2) (by simp) (aN t)
          (AddCircle.parameterSecondDerivativeHs g₀ (k + 2)
            (Pb (fHigh i) + VN t i)) + bN t i) →
    (∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (A₂ (a₂ t)))‖ ≤ C2h) →
    (∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (A₂ (a₂ t)))‖ ≤ C2l) →
    (C2h : ℝ) < 1 → (C2l : ℝ) < 1 →
    ∃ (Wnew : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 4))
      (Vnew : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 5)) T),
      ContinuousOn Wnew (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, R (Wnew t) = W t) ∧
      S.compLpL 2 (timeMeasure T) Vnew = V ∧
      Wnew =ᵐ[timeMeasure T] (fun t => S (Vnew t)) := by
  intro R S Ih Ia A₂ E₁ N₂ N₂V N₄ VN aN bN Pb hW hWV haHigh hbHigh haHigh₂ hVF hPDE
    hC2h hC2l hC2hlt hC2llt
  let N₃ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by push_cast; linarith only : ((k + 3 : ℕ) : ℝ) ≤ (k : ℝ) + 3)
  let N₃V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₃)
  let WN := fun t => N₃V (W t)
  let aHN := N₃.compLpL 2 (timeMeasure T) aHigh
  let bHN := N₃V.compLpL 2 (timeMeasure T) bHigh
  let IhN := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by exact_mod_cast (show k + 2 ≤ k + 3 by omega) :
      ((k + 2 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let I₁N := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by exact_mod_cast (show 1 ≤ k + 3 by omega) :
      ((1 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ))
  let KW := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by push_cast; linarith only :
      ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) + 2)
  have hnatural := circle_sobolev_boost_data_reindex g₀ k T W V a b aHigh bHigh a₂
  have hnaturalFacts := hnatural hW hWV haHigh hbHigh haHigh₂
  have hWN : ContinuousOn WN (Icc 0 T) := hnaturalFacts.1
  have haHN : (fun t => IhN (aHN t)) =ᵐ[timeMeasure T] aN := hnaturalFacts.2.1
  have hbHN : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n, IhN (bHN t i) = bN t i :=
    hnaturalFacts.2.2.1
  have hWNVN : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      WN t i = KW (maximalRegularityDuhamelVectorField hT 0 Fm t i) := by
    rw [← hVF]
    exact hnaturalFacts.2.2.2.1
  have hprincipal : (fun t => I₁N (aHN t)) =ᵐ[timeMeasure T]
      (fun t => E₁ (A₂ (a₂ t))) := hnaturalFacts.2.2.2.2
  have hAh : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (I₁N (aHN t))‖ ≤ C2h :=
    (hprincipal.fun_comp (fun z =>
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ z‖)).trans_le hC2h
  have hAl : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (I₁N (aHN t))‖ ≤ C2l :=
    (hprincipal.fun_comp (fun z =>
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ z‖)).trans_le hC2l
  have hboost := exists_iteratedParameterDerivative_forcing_lift_of_principal_norm_lt_one
    (ι := Fin n) g₀ k hT
  obtain ⟨FH, hFH⟩ := hboost Fm fHigh WN hWN aHN bHN bN C2h C2l
    hbHN hWNVN (by
      filter_upwards [hPDE, haHN] with t ht hat
      intro i
      rw [hat, ← hVF]
      exact ht i) hAh hAl hC2hlt hC2llt
  let E := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
  let FH₁ := E.compLpL 2 (timeMeasure T) FH
  let Z := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
  let Z₁ := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((0 : ℕ) : ℝ) ≤ (1 : ℝ))
  have hFH₁ : iteratedParameterDerivativeDuhamelForcing g₀ 0 (k + 2) hT Fm =
      Z₁.compLpL 2 (timeMeasure T) FH₁ := by
    rw [hFH]
    change Z.compLpL 2 (timeMeasure T) FH = _
    apply Lp.ext
    filter_upwards [Z.coeFn_compLpL FH, Z₁.coeFn_compLpL FH₁, E.coeFn_compLpL FH]
      with t hzt hz₁t het
    rw [hzt, hz₁t, het]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  exact circle_sobolev_successor_of_forcing_lift g₀ k hT Fm FH₁ W V hW hWV hVF hFH₁

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambient_original_forcing_successor_order
    (c₀ : SmoothImmersion (I := I) (M := M))
    {e : M → EuclideanSpace ℝ (Fin n)}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (gM : SmoothRiemannianMetric I M) (k : ℕ) {T : ℝ} (hT : 0 < T)
    (F₂ : timeL2 (CircleHsPi (c₀.pullbackMetric gM) (Fin n) 2) T)
    (a₂ : ℝ → TensorHs (c₀.pullbackMetric gM) 0 0 2)
    (b₂ : ℝ → CircleHsPi (c₀.pullbackMetric gM) (Fin n) 2)
    (V : timeL2 (CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((k : ℝ) + 4)) T)
    (a : ℝ → TensorHs (c₀.pullbackMetric gM) 0 0 ((k : ℝ) + 2))
    (b : ℝ → CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((k : ℝ) + 2))
    (ha : ContinuousOn a (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T)) :
    let g₀ := c₀.pullbackMetric gM
    let U₂ := maximalRegularityDuhamelVectorField hT 0 F₂
    let P := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) ≤ (k : ℝ) + 2)
    let Q := circleHsPiInclusion g₀ (Fin n)
      (by have hk := Nat.cast_nonneg (α := ℝ) k
          linarith only [hk] : (2 : ℝ) + 2 ≤ (k : ℝ) + 4)
    let N₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) ≤ (k : ℝ) + 2)
    let N₂V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₂)
    let N₄ := circleHsPiInclusion g₀ (Fin n)
      (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
    let VN := N₄.compLpL 2 (timeMeasure T) V
    let aN := fun t => N₂ (a t)
    let bN := fun t => N₂V (b t)
    let JN := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by exact_mod_cast (show 2 ≤ k + 2 by omega) :
        ((2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ))
    (∀ t ∈ Icc 0 T, P (a t) = a₂ t) →
    (∀ t ∈ Icc 0 T,
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => P) (b t) = b₂ t) →
    Q.compLpL 2 (timeMeasure T) V = U₂ →
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) 2 (U₂ t i) + F₂ t i =
        scalarHsMul g₀ 2 (by norm_num) (a₂ t)
          (AddCircle.parameterSecondDerivativeHs g₀ 2
            (ambientSobolev c₀ gM e he ((2 : ℝ) + 2) i + U₂ t i)) + b₂ t i) →
    ∃ Fm : timeL2 (CircleHsPi g₀ (Fin n) ((k + 2 : ℕ) : ℝ)) T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => JN)).compLpL
        2 (timeMeasure T) Fm = F₂ ∧
      VN = maximalRegularityDuhamelVectorField hT 0 Fm ∧
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((k + 2 : ℕ) : ℝ)
            (VN t i) + Fm t i =
          scalarHsMul g₀ (k + 2) (by simp) (aN t)
            (AddCircle.parameterSecondDerivativeHs g₀ (k + 2)
              (ambientSobolev c₀ gM e he (((k + 2 : ℕ) : ℝ) + 2) i + VN t i)) +
                bN t i := by
  intro g₀ U₂ P Q N₂ N₂V N₄ VN aN bN JN ha₂proj hb₂proj hVQ hPDE₂
  have hinput := circle_sobolev_forcing_data_reindex g₀ k T V a b a₂ b₂ U₂
  have hinputFacts := hinput ha hb ha₂proj hb₂proj hVQ
  dsimp only [g₀] at hinputFacts
  have hproducer := ambient_original_forcing_higher_equation c₀ he gM (m := k + 2)
    (by omega) hT F₂ a₂ b₂ VN aN bN hinputFacts.1 hinputFacts.2.1
  have hresult := hproducer hinputFacts.2.2.1 hinputFacts.2.2.2.1
    hinputFacts.2.2.2.2 hPDE₂
  dsimp only [g₀, VN, aN, bN, N₂, N₂V, N₄, JN]
  exact hresult

private theorem ambient_sobolev_regularity_successor
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {Udom : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r Udom)
    (hEU : Set.range e ⊆ Udom) (hleft : ∀ p, r (e p) = p) (β : Udom)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    (k : ℕ) {T : ℝ} (hT : 0 < T) (C2h C2l : ℝ≥0) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J₃ := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) + 1 ≤ 3))
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    let P := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
    let Q := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 4)
    let R := circleHsPiInclusion g₀ (Fin n)
      (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4)
    T ≤ (ScalarVectorTimeCoefficients.radius C) →
    ∀ (F₂ : timeL2 (CircleHsPi g₀ (Fin n) 2) T)
      (W₃ : ℝ → CircleHsPi g₀ (Fin n) 3)
      (a₂ : ℝ → TensorHs g₀ 0 0 2)
      (b₂ : ℝ → CircleHsPi g₀ (Fin n) 2),
    let U₂ := maximalRegularityDuhamelVectorField hT 0 F₂
    (∀ t ∈ Icc 0 T, ‖J₃ (W₃ t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
    (∀ t ∈ Icc 0 T, A₂ (a₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J₃ (W₃ t))) →
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t (J₃ (W₃ t))) →
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) 2 (U₂ t i) + F₂ t i =
        scalarHsMul g₀ 2 (by norm_num) (a₂ t)
          (AddCircle.parameterSecondDerivativeHs g₀ 2
            (ambientSobolev c₀ (g 0) e he ((2 : ℝ) + 2) i + U₂ t i)) + b₂ t i) →
    (∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (A₂ (a₂ t)))‖ ≤ C2h) →
    (∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (A₂ (a₂ t)))‖ ≤ C2l) →
    (C2h : ℝ) < 1 → (C2l : ℝ) < 1 →
    ∀ (W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3))
      (V : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 4)) T),
    ContinuousOn W (Icc 0 T) →
    (∀ t ∈ Icc 0 T, P (W t) = W₃ t) →
    Q.compLpL 2 (timeMeasure T) V = U₂ →
    W =ᵐ[timeMeasure T] (fun t => R (V t)) →
    ∃ (Wnew : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 4))
      (Vnew : timeL2 (CircleHsPi g₀ (Fin n) ((k : ℝ) + 5)) T),
      ContinuousOn Wnew (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, R (Wnew t) = W t) ∧
      (circleHsPiInclusion g₀ (Fin n)
        (by linarith : (k : ℝ) + 4 ≤ (k : ℝ) + 5)).compLpL
          2 (timeMeasure T) Vnew = V ∧
      Wnew =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ (Fin n)
        (by linarith : (k : ℝ) + 4 ≤ (k : ℝ) + 5) (Vnew t)) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 4)
          (Wnew t) = W₃ t) ∧
      (circleHsPiInclusion g₀ (Fin n)
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 5)).compLpL
          2 (timeMeasure T) Vnew = U₂ := by
  intro C g₀ J₃ A₂ E₁ P Q R hTC F₂ W₃ a₂ b₂ U₂ hJ₃ ha₂ hb₂ hPDE₂
    hC2h hC2l hC2hlt hC2llt W V hW hWP hVQ hWV
  have hjetTransfer := circle_firstJetHs_coefficients_of_projection g₀ k T
    (ScalarVectorTimeCoefficients.radius C) W W₃ a₂ b₂
    (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.diffusion C) t)
    (fun t => extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
      (ScalarVectorTimeCoefficients.reaction C) t)
  have hjetFacts := hjetTransfer hWP hJ₃ ha₂ hb₂
  dsimp only [C, g₀] at hjetFacts
  have hcoeff := ambient_coefficients_successor_order c₀ g ht he hr hEU hleft β hG k
  whnf at hcoeff
  have hcoeffT := hcoeff T hTC
  have hcoeffW := hcoeffT V W hW hWV
  have hcoeffBound := hcoeffW hjetFacts.1
  have hcoeffBase := hcoeffBound a₂ b₂
  have hcoeffDiffusion := hcoeffBase hjetFacts.2.1
  have hcoeffAll := hcoeffDiffusion hjetFacts.2.2
  refine exists_four_elim hcoeffAll ?_
  intro a b aHigh bHigh hcoeffFacts
  have ha := hcoeffFacts.1
  have hb := hcoeffFacts.2.1
  have hae := hcoeffFacts.2.2.1
  have hbe := hcoeffFacts.2.2.2.1
  have ha₂proj := hcoeffFacts.2.2.2.2.1
  have hb₂proj := hcoeffFacts.2.2.2.2.2.1
  have haHigh := hcoeffFacts.2.2.2.2.2.2.1
  have hbHigh := hcoeffFacts.2.2.2.2.2.2.2.1
  have haHigh₂ := hcoeffFacts.2.2.2.2.2.2.2.2.1
  have hbHigh₂ := hcoeffFacts.2.2.2.2.2.2.2.2.2
  let N₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) ≤ (k : ℝ) + 2)
  let N₂V := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => N₂)
  let N₄ := circleHsPiInclusion g₀ (Fin n)
    (by push_cast; linarith only : ((k + 2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) + 4)
  let VN := N₄.compLpL 2 (timeMeasure T) V
  let aN := fun t => N₂ (a t)
  let bN := fun t => N₂V (b t)
  have hforcing := ambient_original_forcing_successor_order c₀ he (g 0) k hT
    F₂ a₂ b₂ V a b ha hb
  obtain ⟨Fm, hFm₂, hVF, hPDE⟩ := hforcing ha₂proj hb₂proj hVQ hPDE₂
  let fHigh := ambientSobolev c₀ (g 0) e he (((k + 3 : ℕ) : ℝ) + 2)
  let Pb := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by push_cast; linarith only :
      ((k + 2 : ℕ) : ℝ) + 2 ≤ ((k + 3 : ℕ) : ℝ) + 2)
  have hbaseline (i : Fin n) : Pb (fHigh i) =
      ambientSobolev c₀ (g 0) e he (((k + 2 : ℕ) : ℝ) + 2) i := by
    change tensorHsInclusion _ (ccTensorToHs g₀ 0 (((k + 3 : ℕ) : ℝ) + 2) _) = _
    rw [tensorHsInclusion_ccTensorToHs]
    rfl
  obtain ⟨Wnew, Vnew, hWnew, hWnewW, hVnewV, hWnewVnew⟩ :=
    circle_sobolev_successor_of_principal_norm_lt_one g₀ k hT Fm fHigh W V
      a b aHigh bHigh a₂ C2h C2l hW hWV haHigh hbHigh haHigh₂ hVF (by
        filter_upwards [hPDE] with t ht
        intro i
        rw [hbaseline]
        exact ht i) hC2h hC2l hC2hlt hC2llt
  let S := circleHsPiInclusion g₀ (Fin n)
    (by linarith only : (k : ℝ) + 4 ≤ (k : ℝ) + 5)
  refine ⟨Wnew, Vnew, hWnew, hWnewW, hVnewV, hWnewVnew, ?_, ?_⟩
  · intro t htt
    have hh := (congrArg P (hWnewW t htt)).trans (hWP t htt)
    refine Eq.trans ?_ hh
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  · apply Lp.ext
    have hS := S.coeFn_compLpL Vnew
    rw [hVnewV] at hS
    have hQ := Q.coeFn_compLpL V
    rw [hVQ] at hQ
    let Rbase := circleHsPiInclusion g₀ (Fin n)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 5)
    filter_upwards [Rbase.coeFn_compLpL Vnew, hS, hQ] with t hr hs hq
    rw [hr, hq, hs]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem scalarVectorTimeCoefficients_continuousOn_h2_weak_equation
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 (1 : ℝ)))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    {T : ℝ} (hT : 0 < T)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1))
    (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (hW : ContinuousOn W (Icc 0 T)) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField
      (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
    T ≤ ScalarVectorTimeCoefficients.radius C →
    u₀ = J (K f₀) →
    w =ᵐ[timeMeasure T] (fun t => K (field t)) →
    W =ᵐ[timeMeasure T] field →
    (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C) →
    (∀ᵐ t ∂timeMeasure T,
      L (field t) + gforce t =
        m (tensorHsCongrL g₀ 0 0
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))))
          (Q (f₀ + field t)) +
          circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
              (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))) →
    ∃ (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
      (b₂ : ℝ → CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)),
      ContinuousOn W (Icc 0 T) ∧
      W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce ∧
      (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C) ∧
      ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, H₂ (a₂ t) = tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (b₂ t) =
          circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))) ∧
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
            (field t i) + gforce t i =
          scalarHsMul g₀ 1 (by norm_num) (H₂ (a₂ t))
            (AddCircle.parameterSecondDerivativeHs g₀ 1 (f₀ i + field t i)) + H₂ (b₂ t i) := by
  intro J K H₂ field L Q m hTC hu₀ hwfield hWfield hJW heq
  have hcongr {a b : ℝ} (h : a = b) (z : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 h z).coeff = z.coeff := by
    cases h
    rfl
  have hcoeffReal :
      ∃ (a₂ : ℝ → TensorHs g₀ 0 0 (2 : ℝ))
        (b₂ : ℝ → CircleHsPi g₀ (Fin n) (2 : ℝ)),
        ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, tensorHsInclusion
          (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ)) (a₂ t) = tensorHsCongrL g₀ 0 0
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
              (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))) ∧
        (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ (2 : ℝ)) (b₂ t) =
            circleHsPiCongr g₀ (Fin n)
              (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                  (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))) := by
    obtain ⟨a₂, b₂, ha₂, hb₂, haeq, hbeq, _⟩ :=
      scalarVectorTimeCoefficients_continuousOn_h2 g₀ F G S u₀ C
        hF hG hS hTC f₀ W hW hu₀ hJW
    refine ⟨a₂, b₂, ha₂, hb₂, ?_, ?_⟩
    · intro t htt
      have h := congrArg (tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))) (haeq t htt)
      refine Eq.trans ?_ h
      apply TensorHs.ext
      rw [hcongr]
      rfl
    · intro t htt
      have h := congrArg (circleHsPiCongr g₀ (Fin n)
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))) (hbeq t htt)
      refine Eq.trans ?_ h
      apply PiLp.ext
      intro i
      apply TensorHs.ext
      simp only [circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
        circleHsPiCongr_apply, hcongr, tensorHsInclusion_coeff]
  have hcoeff :
      ∃ (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
        (b₂ : ℝ → CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)),
        ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, H₂ (a₂ t) = tensorHsCongrL g₀ 0 0
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))) ∧
        (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (b₂ t) =
            circleHsPiCongr g₀ (Fin n)
              (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
                (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                  (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))) := by
    norm_num only [H₂, CircleHsPi] at hcoeffReal ⊢
    exact hcoeffReal
  obtain ⟨a₂, b₂, ha₂, hb₂, haeq, hbeq⟩ := hcoeff
  refine ⟨a₂, b₂, hW, hWfield, hJW, ha₂, hb₂, haeq, hbeq, ?_⟩
  filter_upwards [heq, hwfield, hWfield,
    ae_restrict_mem (μ := volume) measurableSet_Icc] with t heqₜ hwₜ hWₜ htt
  have hwW : w t = K (W t) := by rw [hwₜ, hWₜ]
  have hA : H₂ (a₂ t) = tensorHsCongrL g₀ 0 0
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))) := by
    rw [hwW]
    exact haeq t htt
  have hB : circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (b₂ t) =
    circleHsPiCongr g₀ (Fin n)
      (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
        (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (w t))) := by
    rw [hwW]
    exact hbeq t htt
  intro i
  rw [hA]
  have hb := congrArg (fun z => z i) hB
  change H₂ (b₂ t i) = _ at hb
  rw [hb]
  exact congrArg (fun z => z i) heqₜ

private theorem scalarVectorTimeCoefficients_h2_weak_equation_of_classical_time_equation
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (Option (Fin n ⊕ Fin n) → ℝ) → ℝ)
    (G : (Option (Fin n ⊕ Fin n) → ℝ) → (Fin n → ℝ))
    (S : Set (Option (Fin n ⊕ Fin n) → ℝ))
    (u₀ : PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 (1 : ℝ)))
    (C : ScalarVectorTimeCoefficients g₀ F G S u₀)
    (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S) (hS : IsOpen S)
    {ρ T : ℝ} (hT : 0 < T)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (w : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1)) :
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField
      (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n =>
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    let Q := AddCircle.parameterSecondDerivativeHsPi (ι := Fin n) g₀ 1
    let m := coordinateMultiplication (ι := Fin n) (scalarHsMul g₀ 1 (by norm_num))
    T ≤ ScalarVectorTimeCoefficients.radius C →
    u₀ = J (K f₀) →
    w =ᵐ[timeMeasure T] (fun t => K (field t)) →
    (∀ᵐ t ∂timeMeasure T,
      L (field t) + gforce t =
        m (tensorHsCongrL g₀ 0 0
          (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.diffusion C) t (J (w t))))
          (Q (f₀ + field t)) +
          circleHsPiCongr g₀ (Fin n)
            (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
              (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                (ScalarVectorTimeCoefficients.reaction C) t (J (w t)))) →
    scalarVectorClassicalTimeEquation (ρ := ρ) g₀ F G S u₀ C hT f₀ J u gforce →
    ∃ (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
      (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
      (b₂ : ℝ → CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)),
      ContinuousOn W (Icc 0 T) ∧
      W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce ∧
      (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C) ∧
      ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, H₂ (a₂ t) = tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (b₂ t) =
          circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))) ∧
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
            (field t i) + gforce t i =
          scalarHsMul g₀ 1 (by norm_num) (H₂ (a₂ t))
            (AddCircle.parameterSecondDerivativeHs g₀ 1 (f₀ i + field t i)) + H₂ (b₂ t i) := by
  intro J K H₂ field L Q m hTC hu₀ hwfield heq hclass
  rcases hclass with ⟨W, hW, _, hWfield, _, hJW, _⟩
  change ∀ t ∈ Icc 0 T,
    ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C at hJW
  refine Exists.intro W ?_
  exact scalarVectorTimeCoefficients_continuousOn_h2_weak_equation
    g₀ F G S u₀ C hF hG hS hT f₀ gforce w W hW
    hTC hu₀ hwfield hWfield hJW heq

private theorem circle_exists_forcing_h2_of_weak_equation
    {n : ℕ}
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
    (hlift : parameterDerivativeForcingFieldLift g₀ hT gforce)
    (f₀ : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
    (f₄ : CircleHsPi g₀ (Fin n) (((2 : ℕ) : ℝ) + 2))
    (hf₄ : ∀ i : Fin n, tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2) (f₄ i) = f₀ i)
    (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
    (b₂ : ℝ → CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ))
    (ha₂ : ContinuousOn a₂ (Icc 0 T)) (hb₂ : ContinuousOn b₂ (Icc 0 T)) :
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField hT 0 gforce
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
          (field t i) + gforce t i =
        scalarHsMul g₀ 1 (by norm_num) (H₂ (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g₀ 1 (f₀ i + field t i)) + H₂ (b₂ t i)) →
    ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
      (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) FH = gforce ∧
      (circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
          2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 FH) = field ∧
      let UH := maximalRegularityDuhamelVectorField hT 0 FH
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
            (UH t i) + FH t i =
          scalarHsMul g₀ 2 (by norm_num) (a₂ t)
            (AddCircle.parameterSecondDerivativeHs g₀ 2
              (f₄ i + UH t i)) + b₂ t i := by
  intro H₂ field heq
  let K₄ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)
  let P₄ := ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => K₄)
  obtain ⟨field₄, hfield₄⟩ := ambient_fourth_order_lift_of_parameterDerivative_lift
    g₀ hT gforce hlift
  have hfield₄ae : ∀ᵐ t ∂timeMeasure T, P₄ (field₄ t) = field t := by
    have hh := P₄.coeFn_compLpL field₄
    rw [hfield₄] at hh
    exact hh.symm
  have hweak : ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
          (K₄ (field₄ t i)) + gforce t i =
        scalarHsMul g₀ 1 (by norm_num) (H₂ (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g₀ 1 (K₄ (f₄ i + field₄ t i))) + H₂ (b₂ t i) := by
    filter_upwards [heq, hfield₄ae] with t heqₜ hfieldₜ
    intro i
    have hfi : K₄ (field₄ t i) = field t i := congrArg (fun z => z i) hfieldₜ
    rw [K₄.map_add, hf₄, hfi]
    exact heqₜ i
  obtain ⟨FH, hFH, hU, hhigh⟩ := AddCircle.exists_timeL2_parabolic_forcing_lift_of_continuousOn
    g₀ (by decide : 1 ≤ 1) (by decide : 1 ≤ 2) hT f₄ field₄ gforce a₂ b₂ ha₂ hb₂ hfield₄ hweak
  refine ⟨FH, hFH, ?_, ?_⟩
  · rw [← hU]
    exact hfield₄
  · rw [← hU]
    exact hhigh

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
variable (c₀ : SmoothImmersion (I := I) (M := M))
variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))


omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem tensorHsInclusion_ambientSobolev
    (gM : SmoothRiemannianMetric I M) {a b : ℝ} (hab : a ≤ b) (i : Fin n) :
    tensorHsInclusion (g := c₀.pullbackMetric gM) (r := 0) (s := 0) hab
      (ambientSobolev c₀ gM e he b i) = ambientSobolev c₀ gM e he a i := by
  change tensorHsInclusion hab (ccTensorToHs (c₀.pullbackMetric gM) 0 b _) = _
  rw [tensorHsInclusion_ccTensorToHs]
  rfl

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem ambient_exists_forcing_h2_of_weak_equation
    (gM : SmoothRiemannianMetric I M)
    {T : ℝ} (hT : 0 < T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric gM) hT gforce)
    (a₂ : ℝ → TensorHs (c₀.pullbackMetric gM) 0 0 ((2 : ℕ) : ℝ))
    (b₂ : ℝ → CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((2 : ℕ) : ℝ))
    (ha₂ : ContinuousOn a₂ (Icc 0 T)) (hb₂ : ContinuousOn b₂ (Icc 0 T)) :
    let H₂ := tensorHsInclusion (g := c₀.pullbackMetric gM) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let field := maximalRegularityDuhamelVectorField hT 0 gforce
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := c₀.pullbackMetric gM) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
          (field t i) + gforce t i =
        scalarHsMul (c₀.pullbackMetric gM) 1 (by norm_num) (H₂ (a₂ t))
          (AddCircle.parameterSecondDerivativeHs (c₀.pullbackMetric gM) 1
            (ambientSobolev c₀ gM e he (((1 : ℕ) : ℝ) + 2) i + field t i)) + H₂ (b₂ t i)) →
    ∃ FH : timeL2 (CircleHsPi (c₀.pullbackMetric gM) (Fin n) ((2 : ℕ) : ℝ)) T,
      (circleHsPiInclusion (c₀.pullbackMetric gM) (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
          2 (timeMeasure T) FH = gforce ∧
      (circleHsPiInclusion (c₀.pullbackMetric gM) (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
          2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 FH) = field ∧
      let UH := maximalRegularityDuhamelVectorField hT 0 FH
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := c₀.pullbackMetric gM) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
            (UH t i) + FH t i =
          scalarHsMul (c₀.pullbackMetric gM) 2 (by norm_num) (a₂ t)
            (AddCircle.parameterSecondDerivativeHs (c₀.pullbackMetric gM) 2
              (ambientSobolev c₀ gM e he (((2 : ℕ) : ℝ) + 2) i + UH t i)) + b₂ t i := by
  intro H₂ field hweak
  exact circle_exists_forcing_h2_of_weak_equation
    (c₀.pullbackMetric gM) hT gforce hlift
    (ambientSobolev c₀ gM e he (((1 : ℕ) : ℝ) + 2))
    (ambientSobolev c₀ gM e he (((2 : ℕ) : ℝ) + 2))
    (fun i => tensorHsInclusion_ambientSobolev
      (c₀ := c₀) (he := he) (gM := gM) (by norm_num) i)
    a₂ b₂ ha₂ hb₂ hweak

private theorem ambient_original_coefficients_h2_weak_equation
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let field := maximalRegularityDuhamelVectorField
      (g := g₀) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 gforce
    ∃ (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
      (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
      (b₂ : ℝ → CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)),
      ContinuousOn W (Icc 0 T) ∧
      W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce ∧
      (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C) ∧
      ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, H₂ (a₂ t) = tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (b₂ t) =
          circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))) ∧
      ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
        tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((1 : ℕ) : ℝ)
            (field t i) + gforce t i =
          scalarHsMul g₀ 1 (by norm_num) (H₂ (a₂ t))
            (AddCircle.parameterSecondDerivativeHs g₀ 1 (f₀ i + field t i)) + H₂ (b₂ t i) := by
  intro C g₀ J K H₂ f₀ field
  have hclass := ambient_classical_time_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT u gforce hfacts hlift
  obtain ⟨hS, hF, hReaction⟩ := geometric_coefficients_contDiffOn hG β
  rcases hfacts with ⟨_, _, _, _, _, _, _, w, _, _, hwfield, _, _, _, heq, _⟩
  exact scalarVectorTimeCoefficients_h2_weak_equation_of_classical_time_equation
    g₀ _ _ _ _ C hF hReaction hS hT f₀ u gforce w
    (hTρ.trans hρC) (ambientFirstJet_eq_initialJet c₀ (g 0) he) hwfield heq hclass

private theorem ambient_original_forcing_h2_equation
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))
    ∃ (W : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
      (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ))
      (b₂ : ℝ → CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)),
      ContinuousOn W (Icc 0 T) ∧
      W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce ∧
      (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ ScalarVectorTimeCoefficients.radius C) ∧
      ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, H₂ (a₂ t) = tensorHsCongrL g₀ 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))))) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (b₂ t) =
          circleHsPiCongr g₀ (Fin n) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))))) ∧
      ∃ FH : timeL2 (CircleHsPi g₀ (Fin n) ((2 : ℕ) : ℝ)) T,
        (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ))).compLpL
            2 (timeMeasure T) FH = gforce ∧
        (circleHsPiInclusion g₀ (Fin n)
          (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2)).compLpL
            2 (timeMeasure T) (maximalRegularityDuhamelVectorField hT 0 FH) =
              maximalRegularityDuhamelVectorField hT 0 gforce ∧
        let UH := maximalRegularityDuhamelVectorField hT 0 FH
        ∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
          tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
              (UH t i) + FH t i =
            scalarHsMul g₀ 2 (by norm_num) (a₂ t)
              (AddCircle.parameterSecondDerivativeHs g₀ 2
                (ambientSobolev c₀ (g 0) e he (((2 : ℕ) : ℝ) + 2) i + UH t i)) + b₂ t i := by
  whnf
  have hsource := ambient_original_coefficients_h2_weak_equation
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  whnf at hsource
  refine Exists.imp (fun W => ?_) hsource
  refine Exists.imp (fun a₂ => ?_)
  refine Exists.imp (fun b₂ => ?_)
  refine And.imp (fun h => h) ?_
  refine And.imp (fun h => h) ?_
  refine And.imp (fun h => h) ?_
  rintro ⟨ha₂, hb₂, hcoeff⟩
  refine ⟨ha₂, hb₂, ?_⟩
  refine ⟨hcoeff.1, hcoeff.2.1, ?_⟩
  exact ambient_exists_forcing_h2_of_weak_equation
    (c₀ := c₀) (he := he) (gM := g 0)
    hT gforce hlift a₂ b₂ ha₂ hb₂ hcoeff.2.2

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear (CircleHsPi circleHsPiInclusion)
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem circle_firstJet_h3_normalization
    {ι : Type*} [Fintype ι]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (x : CircleHsPi g₀ ι 3) :
    let J := (circleFirstJet (ι := ι) g₀).comp
      (circleHsPiCongr g₀ ι
        (by norm_num : (2 : ℝ) = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ ι (by norm_num : (2 : ℝ) ≤ 3)
    let J₃ := (circleFirstJet (ι := ι) g₀).comp
      (circleHsPiInclusion g₀ ι (by norm_num : (1 : ℝ) + 1 ≤ 3))
    J (K x) = J₃ x := by
  intro J K J₃
  have hK : circleHsPiCongr g₀ ι
      (by norm_num : (2 : ℝ) = (1 : ℝ) + 1) (K x) =
      circleHsPiInclusion g₀ ι (by norm_num : (1 : ℝ) + 1 ≤ 3) x := by
    simpa only [K, circleHsPiInclusion, circleHsPiCongr, tensorHsCongr_refl,
      LinearIsometryEquiv.piLpCongrRight_refl, LinearIsometryEquiv.coe_refl, id_eq] using
      circleHsPiCongr_inclusion g₀ ι
        (by norm_num : (2 : ℝ) = (1 : ℝ) + 1) (rfl : (3 : ℝ) = 3)
        (by norm_num : (2 : ℝ) ≤ 3) (by norm_num : (1 : ℝ) + 1 ≤ 3) x
  exact congrArg (circleFirstJet (ι := ι) g₀) hK

private theorem circle_firstJet_seed_normalization
    {ι : Type*} [Fintype ι]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (x : CircleHsPi g₀ ι (((1 : ℕ) : ℝ) + 2)) :
    let J := (circleFirstJet (ι := ι) g₀).comp
      (circleHsPiCongr g₀ ι
        (by norm_num : (2 : ℝ) = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ ι (by norm_num : (2 : ℝ) ≤ 3)
    let L₃ := circleHsPiInclusion g₀ ι
      (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let Jraw := fun z => circleFirstJet g₀ (circleHsPiCongr g₀ ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) z)
    let Kraw := circleHsPiInclusion g₀ ι
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    J (K (L₃ x)) = Jraw (Kraw x) := by
  intro J K L₃ Jraw Kraw
  have hcoeff {a b : ℝ} (hab : a = b) (v : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 hab v).coeff = v.coeff := by
    cases hab
    rfl
  have hin : circleHsPiCongr g₀ ι
      (by norm_num : (2 : ℝ) = (1 : ℝ) + 1) (K (L₃ x)) =
      circleHsPiCongr g₀ ι
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) (Kraw x) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    simpa only [circleHsPiCongr_apply, hcoeff] using
      (show (K (L₃ x) i).coeff = (Kraw x i).coeff from rfl)
  exact congrArg (circleFirstJet (ι := ι) g₀) hin

private theorem circleHsPi_ae_eq_of_projection
    {ι : Type*} [Fintype ι]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (T : ℝ) (U : timeL2 (CircleHsPi g₀ ι ((2 : ℝ) + 2)) T)
    (V : timeL2 (CircleHsPi g₀ ι (((1 : ℕ) : ℝ) + 2)) T)
    (W : ℝ → CircleHsPi g₀ ι (((1 : ℕ) : ℝ) + 2)) :
    let L₃ := circleHsPiInclusion g₀ ι
      (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let Praw := circleHsPiInclusion g₀ ι
      (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ (2 : ℝ) + 2)
    let P := circleHsPiInclusion g₀ ι (by norm_num : (3 : ℝ) ≤ (2 : ℝ) + 2)
    W =ᵐ[timeMeasure T] V → Praw.compLpL 2 (timeMeasure T) U = V →
      (fun t => L₃ (W t)) =ᵐ[timeMeasure T] (fun t => P (U t)) := by
  intro L₃ Praw P hW hU
  have hp := Praw.coeFn_compLpL U
  rw [hU] at hp
  filter_upwards [hW, hp] with t hWt hpt
  rw [hWt, hpt]
  apply PiLp.ext
  intro i
  exact (tensorHsInclusion_trans_apply
    (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ (2 : ℝ) + 2) (U t i)).symm

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear (CircleHsPi circleHsPiInclusion)
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem parameterPrincipalLow_norm_eq
    {n : ℕ} (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (a : timeL2 (TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 1)) T) (t : ℝ) :
    ‖parameterPrincipalLow (n := n) g₀ a t‖ =
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀
        (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a t))‖ := by
  let R := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  have hR : ‖R‖ ≤ 1 :=
    ContinuousLinearMap.norm_piLpMap_le _ zero_le_one
      (fun _ => tensorHsInclusion_opNorm_le_one _)
  have hN : ‖parameterNormalizeZero (n := n) g₀‖ ≤ 1 :=
    ContinuousLinearMap.norm_piLpMap_le _ zero_le_one
      (fun _ => tensorHsInclusion_opNorm_le_one _)
  have hrecover : R.comp (parameterPrincipalLow (n := n) g₀ a t) =
      AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀
        (tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a t)) := by
    apply ContinuousLinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    change tensorHsInclusion (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
      (tensorHsInclusion (by norm_num : ((0 : ℕ) : ℝ) ≤ (0 : ℝ))
        (AddCircle.parameterPrincipalOperatorH0Pi g₀
          (tensorHsInclusion
            (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
            (a t)) x i)) = _
    rw [← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]
  apply le_antisymm
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hN (norm_nonneg _))
  · rw [← hrecover]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hR (norm_nonneg _))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
variable (c₀ : SmoothImmersion (I := I) (M := M))
variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private theorem ambient_parameter_principal_bounds_of_sobolev_solution
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρδ : ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val)
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let Jraw := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let Kraw := circleHsPiInclusion g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    ∀ (Wraw : ℝ → CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2))
      (a₂ : ℝ → TensorHs g₀ 0 0 ((2 : ℕ) : ℝ)),
      Wraw =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 gforce →
      (∀ t ∈ Icc 0 T,
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((2 : ℕ) : ℝ)) (a₂ t) =
          tensorHsCongrL g₀ 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
            (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.diffusion C) t (Jraw (Kraw (Wraw t))))) →
      ∃ C2h C2l : ℝ≥0,
        (∀ᵐ t ∂timeMeasure T,
          ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2h) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2l) ∧
        (C2h : ℝ) < 1 ∧ (C2l : ℝ) < 1 := by
  intro C g₀ Jraw Kraw H₂ E₁ Wraw a₂ hWrawfield haRaw
  have hfacts' := hfacts
  rcases hfacts' with ⟨_, _, _, _, _, hforce, _, w, hw, _, hwu,
    hbound, _, hJ, _, _⟩
  obtain ⟨aControl, _, haControl, _, haNorm, _⟩ :=
    ambientH2CoefficientsAtState c₀ g ht he hr hEU hleft β hG
      hT hTρ hρδ gforce w hw hwu hbound hforce
  have hpa : ambientDiffusionProjection c₀ g ht he hr hEU hleft β hG w aControl :=
    haControl
  obtain ⟨C2h, C2l, hC2h, hC2l, hsmallh, hsmalll⟩ :=
    ambient_h2_coefficient_contraction c₀ g ht he hr hEU hleft β hG
      hT hTρ hρδ w aControl hpa haNorm hbound hJ
  have hcoefficient : ∀ᵐ t ∂timeMeasure T,
      E₁ (H₂ (a₂ t)) = tensorHsInclusion (g := g₀) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (aControl t) := by
    dsimp only [ambientDiffusionProjection] at hpa
    filter_upwards [hpa, hwu, hWrawfield, ae_restrict_mem (μ := volume) measurableSet_Icc]
      with t hat hwt hWt htt
    have hstate : w t = Kraw (Wraw t) := by rw [hwt, hWt]
    rw [hat, hstate, ← haRaw t htt]
    apply TensorHs.ext
    rfl
  have hhigh : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2h := by
    filter_upwards [hC2h, hcoefficient] with t ht hct
    rw [hct]
    exact ht
  have hlow : ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2l := by
    filter_upwards [hC2l, hcoefficient] with t ht hct
    rw [hct, ← parameterPrincipalLow_norm_eq (n := n) g₀ aControl t]
    exact ht
  have hC2hlt : (C2h : ℝ) < 1 :=
    (le_mul_of_one_le_right C2h.coe_nonneg
      (le_add_of_nonneg_right hT.le)).trans_lt
      ((le_add_of_nonneg_right
        (mul_nonneg (Real.sqrt_nonneg (1 + T)) ENNReal.toReal_nonneg)).trans_lt hsmallh)
  have hC2llt : (C2l : ℝ) < 1 :=
    (le_mul_of_one_le_right C2l.coe_nonneg
      (le_add_of_nonneg_right hT.le)).trans_lt
      ((le_add_of_nonneg_right
        (mul_nonneg (Real.sqrt_nonneg (1 + T)) ENNReal.toReal_nonneg)).trans_lt hsmalll)
  exact ⟨C2h, C2l, hhigh, hlow, hC2hlt, hC2llt⟩

private theorem ambient_sobolev_solution_h2_forcing
    {ρ T : ℝ} (hT : 0 < T) (hTρ : T ≤ ρ)
    (hρC : ρ ≤ ScalarVectorTimeCoefficients.radius
      (ambientCoefficients c₀ g ht he hr hEU hleft β hG))
    (hρδ : ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val)
    (u : timeH1 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (gforce : timeL2 (CircleHsPi (c₀.pullbackMetric (g 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
    (hfacts : ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce)
    (hlift : parameterDerivativeForcingFieldLift (c₀.pullbackMetric (g 0)) hT gforce) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : (2 : ℝ) = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n) (by norm_num : (2 : ℝ) ≤ 3)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    ∃ F₂ : timeL2 (CircleHsPi g₀ (Fin n) (2 : ℝ)) T,
      (circleHsPiInclusion g₀ (Fin n) (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)).compLpL
        2 (timeMeasure T) F₂ = gforce ∧
      ∃ (W : ℝ → CircleHsPi g₀ (Fin n) (3 : ℝ))
        (a₂ : ℝ → TensorHs g₀ 0 0 (2 : ℝ))
        (b₂ : ℝ → CircleHsPi g₀ (Fin n) (2 : ℝ)) (C2h C2l : ℝ≥0),
        ContinuousOn W (Icc 0 T) ∧
        W =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ (Fin n)
          (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
            (maximalRegularityDuhamelVectorField hT 0 gforce t)) ∧
        W =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ (Fin n)
          (by norm_num : (3 : ℝ) ≤ (2 : ℝ) + 2)
            (maximalRegularityDuhamelVectorField hT 0 F₂ t)) ∧
        (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ (ScalarVectorTimeCoefficients.radius C)) ∧
        ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, H₂ (a₂ t) =
          extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
            (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t)))) ∧
        (∀ t ∈ Icc 0 T,
          circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) ≤ 2) (b₂ t) =
            extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
              (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t)))) ∧
        (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
          tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) (2 : ℝ)
              (maximalRegularityDuhamelVectorField hT 0 F₂ t i) + F₂ t i =
            scalarHsMul g₀ 2 (by norm_num) (a₂ t)
              (AddCircle.parameterSecondDerivativeHs g₀ 2
                (ambientSobolev c₀ (g 0) e he ((2 : ℝ) + 2) i +
                  maximalRegularityDuhamelVectorField hT 0 F₂ t i)) + b₂ t i) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2h) ∧
        (∀ᵐ t ∂timeMeasure T,
          ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2l) ∧
        (C2h : ℝ) < 1 ∧ (C2l : ℝ) < 1 := by
  intro C g₀ J K H₂ E₁
  have hrich := ambient_original_forcing_h2_equation
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  whnf at hrich
  rcases hrich with ⟨Wraw, a₂, b₂, hWraw, hWrawfield, hJWraw, ha₂, hb₂, haRaw, hbRaw,
    F₂, hF₂, hU₂, hPDE⟩
  let L₃ := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
  let W := fun t => L₃ (Wraw t)
  let Jraw : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 1) →
      PiLp 2 (fun _ : Fin n ⊕ Fin n => TensorHs g₀ 0 0 (1 : ℝ)) :=
    fun x => circleFirstJet g₀ (circleHsPiCongr g₀ (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1) x)
  let Kraw := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
  have hcongr {a b : ℝ} (hab : a = b) (v : TensorHs g₀ 0 0 a) :
      (tensorHsCongrL g₀ 0 0 hab v).coeff = v.coeff := by
    cases hab
    rfl
  have hjet (x : CircleHsPi g₀ (Fin n) (((1 : ℕ) : ℝ) + 2)) :
      J (K (L₃ x)) = Jraw (Kraw x) := by
    exact circle_firstJet_seed_normalization g₀ x
  have hW : ContinuousOn W (Icc 0 T) := L₃.continuous.comp_continuousOn hWraw
  have hWfield : W =ᵐ[timeMeasure T] (fun t => L₃
      (maximalRegularityDuhamelVectorField hT 0 gforce t)) := by
    filter_upwards [hWrawfield] with t ht
    exact congrArg L₃ ht
  let Z := maximalRegularityDuhamelVectorField (g := g₀) (r := 0) (s := 0)
    (a := (2 : ℝ)) hT 0 F₂
  let P := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : (3 : ℝ) ≤ (2 : ℝ) + 2)
  have hWU₂ : W =ᵐ[timeMeasure T] (fun t => P (Z t)) := by
    have htransport := circleHsPi_ae_eq_of_projection g₀ T Z _ Wraw hWrawfield
    exact htransport hU₂
  have hJW (t : ℝ) (htt : t ∈ Icc 0 T) :
      ‖J (K (W t))‖ ≤ (ScalarVectorTimeCoefficients.radius C) := by
    change ‖J (K (L₃ (Wraw t)))‖ ≤ (ScalarVectorTimeCoefficients.radius C)
    rw [hjet]
    simpa only [C, g₀, Jraw, Kraw, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
      using hJWraw t htt
  have haactual (t : ℝ) (htt : t ∈ Icc 0 T) : H₂ (a₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t))) := by
    apply TensorHs.ext
    have hh := congrArg TensorHs.coeff (haRaw t htt)
    rw [hcongr] at hh
    change (a₂ t).coeff =
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J (K (L₃ (Wraw t))))).coeff
    rw [hjet]
    exact hh
  have hbactual (t : ℝ) (htt : t ∈ Icc 0 T) :
      circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) ≤ 2) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t))) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    have hh := congrArg (fun z => (z i).coeff) (hbRaw t htt)
    rw [circleHsPiCongr_apply, hcongr] at hh
    change (b₂ t i).coeff =
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t (J (K (L₃ (Wraw t)))) i).coeff
    rw [hjet]
    simpa only [circleHsPiInclusion, ContinuousLinearMap.piLpMap_apply,
      tensorHsInclusion_coeff, C, g₀, Jraw, Kraw, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
      using hh
  have hprincipal := ambient_parameter_principal_bounds_of_sobolev_solution
    c₀ g ht he hr hEU hleft β hG hT hTρ hρδ u gforce hfacts
  whnf at hprincipal
  obtain ⟨C2h, C2l, hhigh, hlow, hC2hlt, hC2llt⟩ :=
    hprincipal Wraw a₂ hWrawfield haRaw
  exact ⟨F₂, hF₂, W, a₂, b₂, C2h, C2l, hW, hWfield, hWU₂,
    hJW, ha₂, hb₂, haactual, hbactual, hPDE, hhigh, hlow, hC2hlt, hC2llt⟩


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
variable (c₀ : SmoothImmersion (I := I) (M := M))
variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private theorem exists_solution_with_property
    {A : Sort*} {B : A → Sort*} {D : ∀ a, B a → Sort*}
    {X : ∀ a b, D a b → Sort*} {Y : ∀ a b d, X a b d → Sort*}
    {P₀ P₁ P₂ P₃ : A → Prop}
    {R : ∀ a b, D a b → Prop}
    {F H Q : ∀ a b d x, Y a b d x → Prop}
    (hsource : ∃ a, P₀ a ∧ P₁ a ∧ P₂ a ∧ P₃ a ∧
      ∃ b d, R a b d ∧ ∃ x y, F a b d x y ∧ H a b d x y)
    (hproperty : ∀ a b d, R a b d → P₁ a → P₃ a →
      ∀ x y, F a b d x y → H a b d x y → Q a b d x y) :
    ∃ a, P₀ a ∧ P₁ a ∧ P₂ a ∧ P₃ a ∧
      ∃ b d, R a b d ∧ ∃ x y, F a b d x y ∧ H a b d x y ∧ Q a b d x y := by
  rcases hsource with ⟨a, hp₀, hp₁, hp₂, hp₃, b, d, hr, x, y, hf, hh⟩
  exact ⟨a, hp₀, hp₁, hp₂, hp₃, b, d, hr, x, y, hf, hh,
    hproperty a b d hr hp₁ hp₃ x y hf hh⟩

private theorem ambient_capped_sobolev_solution_exists_with_parameterDerivative_lift
    {δ : ℝ} (hδ : 0 < δ)
    (hlift : ambientParameterDerivativeLiftAtRadius c₀ g ht he hr hEU hleft β hG δ) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ScalarVectorTimeCoefficients.radius C ∧ ρ ≤ 1 ∧ ρ ≤ δ ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
          parameterDerivativeForcingFieldLift g₀ hT gforce := by
  whnf
  obtain ⟨ρ, hρ, hρC, hρ1, hρδ, T, hT, hTρ, u, gforce, hfacts⟩ :=
    ambientCappedSobolevSolutionSpec c₀ g ht he hr hEU hleft β hG hδ
  have hlift' := ambient_parameterDerivative_lift_of_solution_facts
    c₀ g ht he hr hEU hleft β hG hT hTρ hρδ u gforce hfacts hlift
  exact ⟨ρ, hρ, hρC, hρ1, hρδ, T, hT, hTρ, u, gforce, hfacts, hlift'⟩

private theorem ambient_sobolev_solution_exists_with_h2_forcing :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiCongr g₀ (Fin n)
        (by norm_num : (2 : ℝ) = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g₀ (Fin n) (by norm_num : (2 : ℝ) ≤ 3)
    let H₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ ρ ≤ 1 ∧
      ρ ≤ (ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG).val ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
          parameterDerivativeForcingFieldLift g₀ hT gforce ∧
          ∃ F₂ : timeL2 (CircleHsPi g₀ (Fin n) (2 : ℝ)) T,
            (circleHsPiInclusion g₀ (Fin n) (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)).compLpL
              2 (timeMeasure T) F₂ = gforce ∧
            ∃ (W : ℝ → CircleHsPi g₀ (Fin n) (3 : ℝ))
              (a₂ : ℝ → TensorHs g₀ 0 0 (2 : ℝ))
              (b₂ : ℝ → CircleHsPi g₀ (Fin n) (2 : ℝ)) (C2h C2l : ℝ≥0),
              ContinuousOn W (Icc 0 T) ∧
              W =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ (Fin n)
                (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
                  (maximalRegularityDuhamelVectorField hT 0 gforce t)) ∧
              W =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ (Fin n)
                (by norm_num : (3 : ℝ) ≤ (2 : ℝ) + 2)
                  (maximalRegularityDuhamelVectorField hT 0 F₂ t)) ∧
              (∀ t ∈ Icc 0 T, ‖J (K (W t))‖ ≤ (ScalarVectorTimeCoefficients.radius C)) ∧
              ContinuousOn a₂ (Icc 0 T) ∧ ContinuousOn b₂ (Icc 0 T) ∧
              (∀ t ∈ Icc 0 T, H₂ (a₂ t) =
                extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                  (ScalarVectorTimeCoefficients.diffusion C) t (J (K (W t)))) ∧
              (∀ t ∈ Icc 0 T,
                circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) ≤ 2) (b₂ t) =
                  extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
                    (ScalarVectorTimeCoefficients.reaction C) t (J (K (W t)))) ∧
              (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
                tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) (2 : ℝ)
                    (maximalRegularityDuhamelVectorField hT 0 F₂ t i) + F₂ t i =
                  scalarHsMul g₀ 2 (by norm_num) (a₂ t)
                    (AddCircle.parameterSecondDerivativeHs g₀ 2
                      (ambientSobolev c₀ (g 0) e he ((2 : ℝ) + 2) i +
                        maximalRegularityDuhamelVectorField hT 0 F₂ t i)) + b₂ t i) ∧
              (∀ᵐ t ∂timeMeasure T,
                ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2h) ∧
              (∀ᵐ t ∂timeMeasure T,
                ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (H₂ (a₂ t)))‖ ≤ C2l) ∧
              (C2h : ℝ) < 1 ∧ (C2l : ℝ) < 1 := by
  intro C g₀ J K H₂ E₁
  let control := ambientParameterDerivativeControl c₀ g ht he hr hEU hleft β hG
  have hsource := ambient_capped_sobolev_solution_exists_with_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG control.property.1
    (ambient_parameterDerivative_forcing_lift_at_small_state c₀ g ht he hr hEU hleft β hG)
  whnf at hsource
  refine exists_solution_with_property hsource ?_
  intro ρ T hT hTρ hρC hρδ u gforce hfacts hlift
  with_reducible exact (ambient_sobolev_solution_h2_forcing
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC hρδ u gforce hfacts hlift)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear (CircleHsPi circleHsPiInclusion)
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem circle_sobolev_tower_of_successor
    {ι : Type*} [Fintype ι]
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (T : ℝ)
    (U₂ : timeL2 (CircleHsPi g₀ ι ((2 : ℝ) + 2)) T)
    (W₃ : ℝ → CircleHsPi g₀ ι 3)
    (hW₃ : ContinuousOn W₃ (Icc 0 T))
    (hW₃U₂ : W₃ =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ ι
      (by norm_num : (3 : ℝ) ≤ (2 : ℝ) + 2) (U₂ t)))
    (hstep : ∀ (k : ℕ)
      (W : ℝ → CircleHsPi g₀ ι ((k : ℝ) + 3))
      (V : timeL2 (CircleHsPi g₀ ι ((k : ℝ) + 4)) T),
      ContinuousOn W (Icc 0 T) →
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
          (W t) = W₃ t) →
      (circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 4)).compLpL
          2 (timeMeasure T) V = U₂ →
      W =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ ι
        (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4) (V t)) →
      ∃ (Wnew : ℝ → CircleHsPi g₀ ι ((k : ℝ) + 4))
        (Vnew : timeL2 (CircleHsPi g₀ ι ((k : ℝ) + 5)) T),
        ContinuousOn Wnew (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ ι
          (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 4)
            (Wnew t) = W₃ t) ∧
        (circleHsPiInclusion g₀ ι
          (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 5)).compLpL
            2 (timeMeasure T) Vnew = U₂ ∧
        Wnew =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ ι
          (by linarith : (k : ℝ) + 4 ≤ (k : ℝ) + 5) (Vnew t))) :
    ∀ k : ℕ, ∃ W : ℝ → CircleHsPi g₀ ι ((k : ℝ) + 3),
      ContinuousOn W (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
          (W t) = W₃ t := by
  let regular (k : ℕ) : Prop :=
    ∃ (W : ℝ → CircleHsPi g₀ ι ((k : ℝ) + 3))
      (V : timeL2 (CircleHsPi g₀ ι ((k : ℝ) + 4)) T),
      ContinuousOn W (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
          (W t) = W₃ t) ∧
      (circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 4)).compLpL
          2 (timeMeasure T) V = U₂ ∧
      W =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ ι
        (by linarith : (k : ℝ) + 3 ≤ (k : ℝ) + 4) (V t))
  have hall : ∀ k : ℕ, regular k := by
    intro k
    induction k with
    | zero =>
      dsimp only [regular]
      let P₀ := circleHsPiInclusion g₀ ι
        (by norm_num : ((0 : ℕ) : ℝ) + 3 ≤ 3)
      let W₀ := fun t => P₀ (W₃ t)
      let B := circleHsPiInclusion g₀ ι
        (by norm_num : ((0 : ℕ) : ℝ) + 4 ≤ (2 : ℝ) + 2)
      let Q := circleHsPiInclusion g₀ ι
        (by norm_num : (2 : ℝ) + 2 ≤ ((0 : ℕ) : ℝ) + 4)
      let V₀ := B.compLpL 2 (timeMeasure T) U₂
      have hQB (z : CircleHsPi g₀ ι ((2 : ℝ) + 2)) : Q (B z) = z := by
        apply PiLp.ext
        intro i
        change tensorHsInclusion (by norm_num : (2 : ℝ) + 2 ≤ ((0 : ℕ) : ℝ) + 4)
          (tensorHsInclusion (by norm_num : ((0 : ℕ) : ℝ) + 4 ≤ (2 : ℝ) + 2) (z i)) = z i
        rw [← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]
      refine ⟨W₀, V₀, P₀.continuous.comp_continuousOn hW₃, ?_, ?_, ?_⟩
      · intro t ht
        apply PiLp.ext
        intro i
        change tensorHsInclusion (by norm_num : (3 : ℝ) ≤ ((0 : ℕ) : ℝ) + 3)
          (tensorHsInclusion (by norm_num : ((0 : ℕ) : ℝ) + 3 ≤ 3) (W₃ t i)) = W₃ t i
        rw [← tensorHsInclusion_trans_apply, tensorHsInclusion_refl_apply]
      · apply Lp.ext
        filter_upwards [Q.coeFn_compLpL V₀, B.coeFn_compLpL U₂] with t hQ hB
        exact hQ.trans ((congrArg Q hB).trans (hQB (U₂ t)))
      · filter_upwards [hW₃U₂, B.coeFn_compLpL U₂] with t hW₃t hB
        change P₀ (W₃ t) = _
        rw [hB]
        refine (congrArg P₀ hW₃t).trans ?_
        apply PiLp.ext
        intro i
        apply TensorHs.ext
        rfl
    | succ k hk =>
      obtain ⟨W, V, hW, hWW₃, hVU₂, hWV⟩ := hk
      obtain ⟨Wnew, Vnew, hWnew, hWnewW₃, hVnewU₂, hWnewVnew⟩ :=
        hstep k W V hW hWW₃ hVU₂ hWV
      dsimp only [regular]
      let P := circleHsPiInclusion g₀ ι
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 3 ≤ (k : ℝ) + 4)
      let B := circleHsPiInclusion g₀ ι
        (by push_cast; linarith : ((k + 1 : ℕ) : ℝ) + 4 ≤ (k : ℝ) + 5)
      let Q := circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) (k + 1)
            linarith : (2 : ℝ) + 2 ≤ ((k + 1 : ℕ) : ℝ) + 4)
      let A := circleHsPiInclusion g₀ ι
        (by have := Nat.cast_nonneg (α := ℝ) k
            linarith : (2 : ℝ) + 2 ≤ (k : ℝ) + 5)
      let Vlift := B.compLpL 2 (timeMeasure T) Vnew
      refine ⟨fun t => P (Wnew t), Vlift, P.continuous.comp_continuousOn hWnew,
        ?_, ?_, ?_⟩
      · intro t ht
        refine Eq.trans ?_ (hWnewW₃ t ht)
        apply PiLp.ext
        intro i
        apply TensorHs.ext
        rfl
      · refine Eq.trans ?_ hVnewU₂
        apply Lp.ext
        filter_upwards [Q.coeFn_compLpL Vlift, B.coeFn_compLpL Vnew,
          A.coeFn_compLpL Vnew] with t hQ hB hA
        rw [hQ, hB, hA]
        apply PiLp.ext
        intro i
        apply TensorHs.ext
        rfl
      · filter_upwards [hWnewVnew, B.coeFn_compLpL Vnew] with t hWt hB
        rw [hB]
        refine (congrArg P hWt).trans ?_
        apply PiLp.ext
        intro i
        apply TensorHs.ext
        rfl
  intro k
  obtain ⟨W, _, hW, hWW₃, _, _⟩ := hall k
  exact ⟨W, hW, hWW₃⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
open AddCircle (parameterPrincipalOperatorHsPi parameterPrincipalOperatorH0Pi)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
variable (c₀ : SmoothImmersion (I := I) (M := M))
variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private theorem ambient_sobolev_regularity_all_orders
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {Udom : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r Udom)
    (hEU : Set.range e ⊆ Udom) (hleft : ∀ p, r (e p) = p) (β : Udom)
    (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))
    {T : ℝ} (hT : 0 < T) (C2h C2l : ℝ≥0) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let J₃ := (circleFirstJet (ι := Fin n) g₀).comp
      (circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) + 1 ≤ 3))
    let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2)
    let E₁ := tensorHsInclusion (g := g₀) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ (1 : ℝ))
    T ≤ (ScalarVectorTimeCoefficients.radius C) →
    ∀ (F₂ : timeL2 (CircleHsPi g₀ (Fin n) 2) T)
      (W₃ : ℝ → CircleHsPi g₀ (Fin n) 3)
      (a₂ : ℝ → TensorHs g₀ 0 0 2)
      (b₂ : ℝ → CircleHsPi g₀ (Fin n) 2),
    let U₂ := maximalRegularityDuhamelVectorField hT 0 F₂
    ContinuousOn W₃ (Icc 0 T) →
    (∀ t ∈ Icc 0 T, ‖J₃ (W₃ t)‖ ≤ (ScalarVectorTimeCoefficients.radius C)) →
    (∀ t ∈ Icc 0 T, A₂ (a₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J₃ (W₃ t))) →
    (∀ t ∈ Icc 0 T, ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t (J₃ (W₃ t))) →
    (∀ᵐ t ∂timeMeasure T, ∀ i : Fin n,
      tensorScaleLaplacian (g := g₀) (r := 0) (s := 0) 2 (U₂ t i) + F₂ t i =
        scalarHsMul g₀ 2 (by norm_num) (a₂ t)
          (AddCircle.parameterSecondDerivativeHs g₀ 2
            (ambientSobolev c₀ (g 0) e he ((2 : ℝ) + 2) i + U₂ t i)) + b₂ t i) →
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorHsPi (ι := Fin n) g₀ (E₁ (A₂ (a₂ t)))‖ ≤ C2h) →
    (∀ᵐ t ∂timeMeasure T, ‖parameterPrincipalOperatorH0Pi (ι := Fin n) g₀ (E₁ (A₂ (a₂ t)))‖ ≤ C2l) →
    (C2h : ℝ) < 1 → (C2l : ℝ) < 1 →
    W₃ =ᵐ[timeMeasure T] (fun t => circleHsPiInclusion g₀ (Fin n)
      (by norm_num : (3 : ℝ) ≤ (2 : ℝ) + 2) (U₂ t)) →
    ∀ k : ℕ, ∃ W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 3),
      ContinuousOn W (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
          (W t) = W₃ t := by
  intro C g₀ J₃ A₂ E₁ hTC F₂ W₃ a₂ b₂ U₂ hW₃ hJ₃ ha₂ hb₂ hPDE hC2h hC2l hsmallh hsmalll hW₃U₂
  apply circle_sobolev_tower_of_successor g₀ T U₂ W₃ hW₃ hW₃U₂
  intro k W V hW hWW₃ hVU₂ hWV
  have hstep := ambient_sobolev_regularity_successor
    c₀ g ht he hr hEU hleft β hG k hT C2h C2l
  whnf at hstep
  have hdata := hstep hTC F₂ W₃ a₂ b₂
  whnf at hdata
  dsimp only [C, g₀, J₃] at hJ₃
  have hjet := hdata hJ₃
  dsimp only [C, g₀, J₃, A₂] at ha₂
  have hdiffusion := hjet ha₂
  dsimp only [C, g₀, J₃, A₂] at hb₂
  have hreaction := hdiffusion hb₂
  dsimp only [g₀, U₂] at hPDE
  have hequation := hreaction hPDE
  have hsmall := hequation hC2h hC2l hsmallh hsmalll
  obtain ⟨Wnew, Vnew, hWnew, _, _, hWnewVnew, hWnewW₃, hVnewU₂⟩ :=
    hsmall W V hW hWW₃ hVU₂ hWV
  exact ⟨Wnew, Vnew, hWnew, hWnewW₃, hVnewU₂, hWnewVnew⟩

private theorem ambient_sobolev_solution_exists_with_sobolev_tower :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
          parameterDerivativeForcingFieldLift g₀ hT gforce ∧
          ∀ k : ℕ, ∃ W : ℝ → CircleHsPi g₀ (Fin n) ((k : ℝ) + 2),
            ContinuousOn W (Icc 0 T) ∧
            ∀ t ∈ Icc 0 T, circleHsPiInclusion g₀ (Fin n)
              (by
                have hk := Nat.cast_nonneg (α := ℝ) k;
                norm_num only [Nat.cast_one];
                linarith only [hk] : ((1 : ℕ) : ℝ) ≤ (k : ℝ) + 2) (W t) = u.toFun t := by
  intro C g₀
  have hseed := ambient_sobolev_solution_exists_with_h2_forcing
    c₀ g ht he hr hEU hleft β hG
  whnf at hseed
  obtain ⟨ρ, hρ, hρC, hρ1, _, T, hT, hTρ, u, gforce, hfacts, hlift,
    F₂, _, W₃, a₂, b₂, C2h, C2l, hW₃, hW₃field, hW₃U₂, hJW₃,
    _, _, ha₂, hb₂, hPDE, hC2h, hC2l, hsmallh, hsmalll⟩ := hseed
  let J₃ := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiInclusion g₀ (Fin n) (by norm_num : (1 : ℝ) + 1 ≤ 3))
  let J := (circleFirstJet (ι := Fin n) g₀).comp
    (circleHsPiCongr g₀ (Fin n)
      (by norm_num : (2 : ℝ) = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
  let K := circleHsPiInclusion g₀ (Fin n) (by norm_num : (2 : ℝ) ≤ 3)
  let A₂ := tensorHsInclusion (g := g₀) (r := 0) (s := 0) (by norm_num : (1 : ℝ) ≤ 2)
  have hJ (x : CircleHsPi g₀ (Fin n) 3) : J (K x) = J₃ x := by
    exact circle_firstJet_h3_normalization g₀ x
  have hJbound (t : ℝ) (htt : t ∈ Icc 0 T) :
      ‖J₃ (W₃ t)‖ ≤ (ScalarVectorTimeCoefficients.radius C) := by
    calc
      ‖J₃ (W₃ t)‖ = ‖J (K (W₃ t))‖ := congrArg norm (hJ (W₃ t)).symm
      _ ≤ (ScalarVectorTimeCoefficients.radius C) := by
        dsimp only [C, g₀, J, K, J₃] at hJW₃ ⊢
        exact hJW₃ t htt
  have hae (t : ℝ) (htt : t ∈ Icc 0 T) : A₂ (a₂ t) =
      extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t (J₃ (W₃ t)) := by
    apply TensorHs.ext
    have hphysical := congrArg TensorHs.coeff (ha₂ t htt)
    have hjetTransport := congrArg
      (fun z => (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.diffusion C) t z).coeff) (hJ (W₃ t))
    dsimp only [C, g₀, J₃, J, K, A₂] at hphysical hjetTransport ⊢
    with_reducible exact hphysical.trans hjetTransport
  have hbe (t : ℝ) (htt : t ∈ Icc 0 T) :
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin n => A₂) (b₂ t) =
        extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
          (ScalarVectorTimeCoefficients.reaction C) t (J₃ (W₃ t)) := by
    exact (hb₂ t htt).trans (congrArg
      (extendClosedBall (ScalarVectorTimeCoefficients.radius_pos C).le
        (ScalarVectorTimeCoefficients.reaction C) t) (hJ (W₃ t)))
  have hallProvider := ambient_sobolev_regularity_all_orders
    c₀ g ht he hr hEU hleft β hG hT C2h C2l
  whnf at hallProvider
  have hallData := hallProvider (hTρ.trans hρC) F₂ W₃ a₂ b₂
  whnf at hallData
  have hallContinuous := hallData hW₃
  dsimp only [C, g₀, J₃] at hJbound
  have hallBound := hallContinuous hJbound
  dsimp only [C, g₀, J₃, A₂] at hae
  have hallDiffusion := hallBound hae
  have hallReaction := hallDiffusion hbe
  have hallEquation := hallReaction hPDE
  have hallHigh := hallEquation hC2h
  have hallLow := hallHigh hC2l
  have hallHighSmall := hallLow hsmallh
  have hallLowSmall := hallHighSmall hsmalll
  have hall := hallLowSmall hW₃U₂
  have hclassical := ambient_classical_time_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT u gforce hfacts hlift
  obtain ⟨W₀, hW₀, hW₀u, hW₀field, _, _, _⟩ := hclassical
  let L₃ := circleHsPiInclusion g₀ (Fin n)
    (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
  have hWW₀ae : W₃ =ᵐ[timeMeasure T] (fun t => L₃ (W₀ t)) := by
    filter_upwards [hW₃field, hW₀field] with t h₃ h₀
    exact h₃.trans (congrArg L₃ h₀.symm)
  have hWW₀ : EqOn W₃ (fun t => L₃ (W₀ t)) (Icc 0 T) :=
    Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT)
      hWW₀ae hW₃ (L₃.continuous.comp_continuousOn hW₀)
  have hW₃u (t : ℝ) (htt : t ∈ Icc 0 T) :
      circleHsPiInclusion g₀ (Fin n) (by norm_num : ((1 : ℕ) : ℝ) ≤ 3) (W₃ t) = u.toFun t := by
    rw [hWW₀ htt]
    refine Eq.trans ?_ (hW₀u t htt)
    apply PiLp.ext
    intro i
    exact (tensorHsInclusion_trans_apply
      (by norm_num : ((1 : ℕ) : ℝ) ≤ 3)
      (by norm_num : (3 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2) (W₀ t i)).symm
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, ?_⟩
  intro k
  obtain ⟨W, hW, hWW₃⟩ := hall k
  let P := circleHsPiInclusion g₀ (Fin n)
    (by linarith : (k : ℝ) + 2 ≤ (k : ℝ) + 3)
  refine ⟨fun t => P (W t), P.continuous.comp_continuousOn hW, ?_⟩
  intro t htt
  have hlink : circleHsPiInclusion g₀ (Fin n)
      (by
        have hk := Nat.cast_nonneg (α := ℝ) k;
        norm_num only [Nat.cast_one];
        linarith : ((1 : ℕ) : ℝ) ≤ (k : ℝ) + 2)
        (P (W t)) = circleHsPiInclusion g₀ (Fin n) (by norm_num : ((1 : ℕ) : ℝ) ≤ 3)
          (circleHsPiInclusion g₀ (Fin n)
            (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (3 : ℝ) ≤ (k : ℝ) + 3)
              (W t)) := by
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  rw [hlink, hWW₃ t htt]
  exact hW₃u t htt

private theorem ambient_sobolev_solution_exists_with_smooth_chart :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ (ScalarVectorTimeCoefficients.radius C) ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
          parameterDerivativeForcingFieldLift g₀ hT gforce ∧
          let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
          let P := circleHsPiInclusion g₀ (Fin n)
            (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
          let S := circleHsPiInclusion g₀ (Fin n)
            (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
          let F : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun t x => WithLp.toLp 2
            (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) (x : AddCircle (1 : ℝ)))
          ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set ℝ)) := by
  intro C g₀
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, htower⟩ :=
    ambient_sobolev_solution_exists_with_sobolev_tower c₀ g ht he hr hEU hleft β hG
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, ?_⟩
  exact ambient_contDiffOn_of_sobolev_tower c₀ g ht he hr hEU hleft β hG
    hT hTρ hρC u gforce hfacts hlift htower

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
open AddCircle (parameterPrincipalOperatorHsPi parameterPrincipalOperatorH0Pi)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

variable (c₀ : SmoothImmersion (I := I) (M := M))
variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

private theorem ambient_sobolev_solution_exists_with_reparametrization [I.Boundaryless]
    (hg : MetricFamilySmoothOn D g) :
    let C := ambientCoefficients c₀ g ht he hr hEU hleft β hG
    let g₀ := c₀.pullbackMetric (g 0)
    let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
    let P := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let S := circleHsPiInclusion g₀ (Fin n)
      (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ScalarVectorTimeCoefficients.radius C ∧ ρ ≤ 1 ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ ∧
        ∃ (u : timeH1 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T)
          (gforce : timeL2 (CircleHsPi g₀ (Fin n) ((1 : ℕ) : ℝ)) T),
          ambientSobolevSolutionFacts c₀ g ht he hr hEU hleft β hG ρ hT u gforce ∧
            parameterDerivativeForcingFieldLift g₀ hT gforce ∧
            let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
              (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
            let c : CurveMap M := fun z t => r (d z t)
            (∀ z, c z 0 = c₀.map z) ∧
              (∀ z t, t ∈ Icc 0 T → e (c z t) = d z t) ∧
              c.SmoothOn (I := I) (Icc 0 T) ∧
              c.ImmersedOn (I := I) (Icc 0 T) ∧
              ∃ φ : CircleReparametrization (Icc 0 T),
                (∀ z, φ.map 0 z = z) ∧
                CurveMap.IsSolutionOn (I := I) (fun z t => c (φ.map t z) t) g (Icc 0 T) ∧
                (∀ z, c (φ.map 0 z) 0 = c₀.map z) ∧
                (∀ z t, t ∈ Icc 0 T → e (c (φ.map t z) t) = d (φ.map t z) t) ∧
                ∀ t, t ∈ Icc 0 T →
                  range (fun z => e (c (φ.map t z) t)) = range (fun z => d z t) := by
  intro C g₀ f₀ P S
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hsmooth⟩ :=
    ambient_sobolev_solution_exists_with_smooth_chart c₀ g ht he hr hEU hleft β hG
  refine ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, ?_⟩
  exact ambient_retraction_exists_reparametrization_of_contDiffOn
    c₀ g ht he hr hEU hleft β hG hg hT hTρ hρC u gforce hfacts hlift hsmooth

include ht he hr hEU hleft β hG in
private theorem exists_solution_of_smooth_retraction [I.Boundaryless]
    (hg : MetricFamilySmoothOn D g) :
    ∃ T : ℝ, 0 < T ∧ ∃ c : CurveMap M,
      c.IsSolutionOn (I := I) g (Icc 0 T) ∧ ∀ z, c z 0 = c₀.map z := by
  obtain ⟨ρ, _, _, _, T, hT, _, u, gforce, _, _,
      _, _, _, _, φ, _, hsol, hinit, _, _⟩ :=
    ambient_sobolev_solution_exists_with_reparametrization
      c₀ g ht he hr hEU hleft β hG hg
  exact ⟨T, hT, _, hsol, hinit⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
open DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}

private theorem curve_shortening_local_existence_of_retraction [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {e : M → EuclideanSpace ℝ (Fin n)}
    (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
    (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p) :
    curveShorteningLocalExistence (I := I) (M := M) B := by
  intro t₀ ht₀ c₀
  let gshift : ℝ → SmoothRiemannianMetric I M := fun s => B.family.metric (s + t₀)
  have hgshift : MetricFamilySmoothOn (D.timeShift t₀) gshift := B.smooth.timeShift t₀
  have hzero : (0 : ℝ) ∈ (D.timeShift t₀).regular := by
    change 0 + t₀ ∈ D.regular
    simpa only [zero_add] using B.regular ⟨ht₀.1, ht₀.2.le⟩
  let β : U := ⟨e (c₀.map 0), hEU (mem_range_self _)⟩
  have hG := metricFamilySmoothOn_retractionMetric gshift hgshift he hr
  obtain ⟨T, hT, c, hc, hinit⟩ :=
    SmoothImmersion.exists_solution_of_smooth_retraction
      c₀ gshift hzero he hr hEU hleft β hG hgshift
  let τ := min T (b - t₀)
  have hτ : 0 < τ := lt_min hT (sub_pos.mpr ht₀.2)
  have hτT : τ ≤ T := min_le_left _ _
  have hτb : t₀ + τ ≤ b := by
    have hle : τ ≤ b - t₀ := min_le_right _ _
    linarith
  have hmap : MapsTo (fun t : ℝ => t + -t₀) (Icc t₀ (t₀ + τ)) (Icc 0 T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hshifted := hc.time_translate (-t₀) hmap
    (uniqueDiffOn_Icc (by linarith : t₀ < t₀ + τ))
  let d : CurveMap M := fun z t => c z (t + -t₀)
  have hd : d.IsSolutionOn (I := I) B.family.metric (Icc t₀ (t₀ + τ)) := by
    simpa only [gshift, neg_add_cancel_right] using hshifted
  refine ⟨τ, hτ, hτb, d, hd, ?_⟩
  intro z
  change c z (t₀ + -t₀) = c₀.map z
  rw [add_neg_cancel]
  exact hinit z

theorem curveShorteningLocalExistence_of_compact
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    curveShorteningLocalExistence (I := I) (M := M) B := by
  intro t₀ ht₀ c₀
  let : Nonempty M := ⟨c₀.map 0⟩
  obtain ⟨n, e, he, hemb, hi⟩ :=
    exists_embedding_euclidean_of_compact (I := I) (M := M)
  obtain ⟨r, V, hV, heV, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction
      he hemb.isEmbedding hi
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨V, hV⟩
  have hrU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U := hr
  exact curve_shortening_local_existence_of_retraction
    (I := I) (M := M) (n := n) B he hrU heV hleft t₀ ht₀ c₀

theorem curveShorteningParabolicGaugeLocalExistence_of_compact
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    curveShorteningParabolicGaugeLocalExistence (I := I) (M := M) B := by
  intro t₀ ht₀ c₀
  obtain ⟨τ, hτ, hτb, c, hc, hinit⟩ :=
    curveShorteningLocalExistence_of_compact B t₀ ht₀ c₀
  refine ⟨τ, hτ, hτb, c, hc.smooth, hinit, ?_⟩
  intro x t ht
  have hpar := parabolic_gauge_velocity (I := I) B.family.metric c
    hc.smooth hc.immersed x t ht
  rw [hc.equation x t ht, hpar.2, add_sub_cancel_right]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
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

noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature
open AddCircle (parameterPrincipalOperatorHsPi parameterPrincipalOperatorH0Pi)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

variable (c₀ : SmoothImmersion (I := I) (M := M))
variable (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} (ht : 0 ∈ D.regular)
    {e : M → EuclideanSpace ℝ (Fin n)} (he : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    {r : EuclideanSpace ℝ (Fin n) → M} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
variable (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U)
variable (hEU : Set.range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
variable (hG : MetricFamilySmoothOn D (fun t => Geometry.Riemannian.retractionMetric (g t) he hr))

include ht he hr hEU hleft β hG in
private theorem exists_parametric_solution_of_smooth_retraction [I.Boundaryless] :
    ∃ T : ℝ, 0 < T ∧ ∃ c : CurveMap M,
      c.SmoothOn (I := I) (Icc 0 T) ∧ c.ImmersedOn (I := I) (Icc 0 T) ∧
      (∀ z, c z 0 = c₀.map z) ∧
      ∀ x t, t ∈ Icc 0 T → c.velocity (I := I) (Icc 0 T) x t =
        c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  obtain ⟨ρ, hρ, hρC, hρ1, T, hT, hTρ, u, gforce, hfacts, hlift, hsmooth⟩ :=
    ambient_sobolev_solution_exists_with_smooth_chart c₀ g ht he hr hEU hleft β hG
  let g₀ := c₀.pullbackMetric (g 0)
  let f₀ := ambientSobolev c₀ (g 0) e he (((1 : ℕ) : ℝ) + 2)
  let P := circleHsPiInclusion g₀ (Fin n)
    (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
  let S := circleHsPiInclusion g₀ (Fin n)
    (show (1 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)
  let d : CurveMap (EuclideanSpace ℝ (Fin n)) := fun z t => WithLp.toLp 2
    (scalarH1PiToContinuous g₀ (P f₀ + S (u.toFun t)) z)
  let c : CurveMap M := fun z t => r (d z t)
  have hfinite := ambient_retraction_contMDiff_two_and_immersed_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  have hcsm : c.SmoothOn (I := I) (Icc 0 T) :=
    ambient_retraction_smooth_of_contDiffOn
      c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hsmooth
  have hparam := ambient_retraction_parametric_equation_of_parameterDerivative_lift
    c₀ g ht he hr hEU hleft β hG hT hTρ hρC u gforce hfacts hlift
  exact ⟨T, hT, c, hcsm, hfinite.2.2.2, hfinite.1, hparam⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
open DifferentialGeometry.Geometry.Curvature

theorem exists_parametric_solution_of_compact
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval}
    (ht : 0 ∈ D.regular) (hg : MetricFamilySmoothOn D g) :
    ∃ T : ℝ, 0 < T ∧ ∃ c : CurveMap M,
      c.SmoothOn (I := I) (Icc 0 T) ∧ c.ImmersedOn (I := I) (Icc 0 T) ∧
      (∀ z, c z 0 = c₀.map z) ∧
      ∀ x t, t ∈ Icc 0 T → c.velocity (I := I) (Icc 0 T) x t =
        c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t := by
  let : Nonempty M := ⟨c₀.map 0⟩
  obtain ⟨n, e, he, hemb, hi⟩ :=
    exists_embedding_euclidean_of_compact (I := I) (M := M)
  obtain ⟨r, V, hV, heV, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction
      he hemb.isEmbedding hi
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨V, hV⟩
  have hrU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r U := hr
  let β : U := ⟨e (c₀.map 0), heV (mem_range_self _)⟩
  have hG := metricFamilySmoothOn_retractionMetric g hg he hrU
  exact exists_parametric_solution_of_smooth_retraction c₀ g ht he hrU heV hleft β hG

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end

section
noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem scalarH1PiToContinuous_fixedAmbientSobolev
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (d : SmoothImmersion (I := I) (M := M)) (z : AddCircle (1 : ℝ)) :
    scalarH1PiToContinuous g₀
      ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin N =>
        tensorHsInclusion (g := g₀) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)))
        (fixedAmbientSobolev e g₀ d)) z = fun i => e.map (d.map z) i := by
  funext i
  change scalarH1ToContinuous g₀
    (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
      (tensorHsCongrL g₀ 0 0 (by norm_num : (3 : ℝ) = ((1 : ℕ) : ℝ) + 2)
        (ccTensorToHs g₀ 0 3 (scalarCc g₀ (ambientCoordinate d e.map e.smooth i))))) z = _
  rw [tensorHsCongrL_ccTensorToHs, tensorHsInclusion_ccTensorToHs,
    scalarH1ToContinuous_apply_ccTensorToHs, scalar0_scalarCc]
  rfl

private theorem continuous_fixedAmbientSobolev_slice
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {a b : ℝ} (hab : a < b) {c : CurveMap M}
    (hc : c.SmoothOn (I := I) (Icc a b)) (hi : c.ImmersedOn (I := I) (Icc a b)) :
    Continuous (fun t : Icc a b =>
      fixedAmbientSobolev e g₀ (slice c hc hi t.val t.property)) := by
  let : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a b)
  have hconst : @Continuous Unit (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc a b)) (fun _ => c) := continuous_const
  have hpair : Continuous (fun q : Unit × Icc a b =>
      slice c hc hi q.2.val q.2.property) :=
    continuous_iff_continuousAt.mpr fun q =>
      continuousAt_slice_smoothImmersion e hab hconst (fun _ => hc) (fun _ => hi) q
  have hslice : Continuous (fun t : Icc a b => slice c hc hi t.val t.property) :=
    hpair.comp ((continuous_const : Continuous (fun _ : Icc a b => ())).prodMk continuous_id)
  exact (continuous_fixedAmbientSobolev e g₀).comp hslice

private theorem exists_continuousOn_fixedAmbientSobolev_curve
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {a b : ℝ} (hab : a < b) {c : CurveMap M}
    (hc : c.SmoothOn (I := I) (Icc a b)) (hi : c.ImmersedOn (I := I) (Icc a b)) :
    ∃ W : ℝ → PiLp 2 (fun _ : Fin N => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)),
      ContinuousOn W (Icc a b) ∧
        (∀ t (ht : t ∈ Icc a b), W t = fixedAmbientSobolev e g₀ (slice c hc hi t ht)) ∧
        (∀ t ∈ Icc a b, ∀ z : AddCircle (1 : ℝ),
          scalarH1PiToContinuous g₀
            ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin N =>
              tensorHsInclusion (g := g₀) (r := 0) (s := 0)
                (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))) (W t)) z =
            fun i => e.map (c z t) i) := by
  classical
  let W : ℝ → PiLp 2 (fun _ : Fin N => TensorHs g₀ 0 0 (((1 : ℕ) : ℝ) + 2)) :=
    fun t => if ht : t ∈ Icc a b then fixedAmbientSobolev e g₀ (slice c hc hi t ht)
      else fixedAmbientSobolev e g₀ (slice c hc hi a ⟨le_rfl, hab.le⟩)
  have hW (t : ℝ) (ht : t ∈ Icc a b) :
      W t = fixedAmbientSobolev e g₀ (slice c hc hi t ht) := dif_pos ht
  refine ⟨W, ?_, hW, ?_⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_fixedAmbientSobolev_slice e g₀ hab hc hi).congr
      (fun t => (hW t.val t.property).symm)
  · intro t ht z
    rw [hW t ht]
    exact scalarH1PiToContinuous_fixedAmbientSobolev e g₀ (slice c hc hi t ht) z

variable [IsManifold I ∞ M]

private theorem exists_continuousOn_fixedAmbientSobolev_curve_with_initial
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g : SmoothRiemannianMetric I M) (c₀ : SmoothImmersion (I := I) (M := M))
    {a b : ℝ} (hab : a < b) {c : CurveMap M}
    (hc : c.SmoothOn (I := I) (Icc a b)) (hi : c.ImmersedOn (I := I) (Icc a b))
    (hinit : ∀ z, c z a = c₀.map z) :
    ∃ W : ℝ → PiLp 2 (fun _ : Fin N =>
        TensorHs (c₀.pullbackMetric g) 0 0 (((1 : ℕ) : ℝ) + 2)),
      ContinuousOn W (Icc a b) ∧
        W a = ambientSobolev c₀ g e.map e.smooth (((1 : ℕ) : ℝ) + 2) ∧
        (∀ t (ht : t ∈ Icc a b),
          W t = fixedAmbientSobolev e (c₀.pullbackMetric g) (slice c hc hi t ht)) ∧
        (∀ t ∈ Icc a b, ∀ z : AddCircle (1 : ℝ),
          scalarH1PiToContinuous (c₀.pullbackMetric g)
            ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin N =>
              tensorHsInclusion (g := c₀.pullbackMetric g) (r := 0) (s := 0)
                (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))) (W t)) z =
            fun i => e.map (c z t) i) := by
  obtain ⟨W, hWcont, hW, heval⟩ := exists_continuousOn_fixedAmbientSobolev_curve
    e (c₀.pullbackMetric g) hab hc hi
  refine ⟨W, hWcont, ?_, hW, heval⟩
  rw [hW a ⟨le_rfl, hab.le⟩]
  have hs : slice c hc hi a ⟨le_rfl, hab.le⟩ = c₀ := by
    cases c₀ with
    | mk f hf hif =>
      have hm : (fun z => c z a) = f := funext hinit
      cases hm
      rfl
  rw [hs, fixedAmbientSobolev_pullbackMetric_eq]

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

local notation "earlyShiftedRemainder" => shiftedRemainder

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

local notation "earlyShiftedRemainder" => shiftedRemainder

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

noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open DifferentialGeometry.Geometry.Curvature

theorem exists_initial_interval_eq_of_parametric_curves_of_compact
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} {T : ℝ}
    (hT : 0 < T) (hG : MetricFamilySmoothOn D g) (hJD : Icc (0 : ℝ) T ⊆ D.regular)
    {c₁ c₂ : CurveMap M}
    (hc₁ : c₁.SmoothOn (I := I) (Icc 0 T))
    (hc₂ : c₂.SmoothOn (I := I) (Icc 0 T))
    (hi₁ : c₁.ImmersedOn (I := I) (Icc 0 T))
    (hi₂ : c₂.ImmersedOn (I := I) (Icc 0 T))
    (heq₁ : ∀ x t, t ∈ Icc 0 T → c₁.velocity (I := I) (Icc 0 T) x t =
      c₁.speed g x t ^ (-2 : ℤ) • c₁.Dx g c₁.X x t)
    (heq₂ : ∀ x t, t ∈ Icc 0 T → c₂.velocity (I := I) (Icc 0 T) x t =
      c₂.speed g x t ^ (-2 : ℤ) • c₂.Dx g c₂.X x t)
    (hinit : ∀ z, c₁ z 0 = c₂ z 0) :
    ∃ δ > 0, δ ≤ T ∧ ∀ z t, t ∈ Icc 0 δ → c₁ z t = c₂ z t := by
  classical
  let c₀ := SmoothImmersion.slice c₁ hc₁ hi₁ 0 ⟨le_rfl, hT.le⟩
  let : Nonempty M := ⟨c₀.map 0⟩
  obtain ⟨n, e, he, hemb, hi⟩ :=
    exists_embedding_euclidean_of_compact (I := I) (M := M)
  let emb : Width.SmoothLoopEmbedding (I := I) (Q := M) n := ⟨e, he, hemb, hi⟩
  obtain ⟨ret, V, hV, heV, hret, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction
      he hemb.isEmbedding hi
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨V, hV⟩
  have hretU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ ret U := hret
  let β : U := ⟨e (c₀.map 0), heV (mem_range_self _)⟩
  have hGret := metricFamilySmoothOn_retractionMetric g hG he hretU
  exact SmoothImmersion.exists_initial_interval_eq_of_parametric_curves_of_retraction
    c₀ g (hJD ⟨le_rfl, hT.le⟩) emb hretU heV hleft β hGret hT
    hc₁ hc₂ hi₁ hi₂ (fun _ => rfl) (fun z => (hinit z).symm) heq₁ heq₂

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
end
end
