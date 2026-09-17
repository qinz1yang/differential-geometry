import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicReconstruction
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.AddCircleDerivativeContinuity
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleFiniteRegularity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleLinearizedLift
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleContractionRadius
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

end

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion
end
