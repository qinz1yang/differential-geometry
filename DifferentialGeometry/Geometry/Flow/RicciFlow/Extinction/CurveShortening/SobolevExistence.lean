import DifferentialGeometry.Analysis.FunctionalAnalysis.ContinuousLinearMap.ClosedBall
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacian
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
  let A : ℝ≥0 := ‖m‖₊ * Cα * ‖Q‖₊
  obtain ⟨r, hr, hrR, hr1, hsmall, _⟩ := exists_small_coefficient_radius hR A A
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
  refine ⟨r, hr, hrR, hr1, ?_⟩
  exact circle_shifted_solution_of_coefficient_bounds g n hn f₀ alpha reaction hr hr
    Cα Cα CB A₀ B₀ halip haclose' hblip hazero hbzero hacont hbcont hs hs

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

open MeasureTheory Set Filter
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
  circle_shifted_solution_of_lipschitz_coefficients g₀ 1 (by norm_num)
      f₀ houter A B (Ca * (1 + ‖J‖₊)) (Cb * (1 + ‖J‖₊)) hA hB hA0


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
  unfold PrecomposedCircleSolution at sol
  exact ⟨sol.val, sol.property⟩


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
      (ambientFirstJet c₀ (g 0) e he)) :=
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
