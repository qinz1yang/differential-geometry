import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.LocalExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.SobolevBounds
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleDerivativeForcingLift
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.AddCircleDerivativeContinuity

open private circle_shifted_solution_with_radius_le_of_lipschitz_coefficients extendClosedBall extendClosedBall_apply coordinateMultiplication circleHsPiInclusion from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private graph_coefficient_eq_principal graph_coefficient_eval_eq_slope from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.LocalExistence

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff NNReal
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

namespace AddCircle

open DifferentialGeometry

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem exists_pos_parameterPrincipal_norm_le_of_lipschitz
    {ι X : Type*} [Fintype ι] [NormedAddCommGroup X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {R : ℝ} (hR : 0 < R)
    (alpha : Metric.closedBall (0 : X) R → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    {C : ℝ≥0} (halpha : LipschitzWith C alpha)
    (hzero : alpha ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧
      ∀ v : Metric.closedBall (0 : X) R, ‖v.val‖ ≤ δ →
        ‖parameterPrincipalOperatorHsPi (ι := ι) g (alpha v)‖ ≤ (1 / 4 : ℝ) ∧
        ‖parameterPrincipalOperatorH0Pi (ι := ι) g (alpha v)‖ ≤ (1 / 4 : ℝ) := by
  let m := scalarHsMul g 1 (by norm_num)
  let E := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
  let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
  let M := scalarH0ContinuousMul g
  let Ch := ‖m‖ * ‖parameterSecondDerivativeHs g 1‖
  let Cl := ‖M‖ * ‖E‖ * ‖Z.comp (parameterSecondDerivativeHs g 0)‖
  have hCh : 0 ≤ Ch := by positivity
  have hCl : 0 ≤ Cl := by positivity
  let δ := min R ((1 / 4 : ℝ) / (((Ch + Cl) * C) + 1))
  have hden : 0 < ((Ch + Cl) * C) + 1 := by positivity
  have hδ : 0 < δ := lt_min hR (div_pos (by norm_num) hden)
  have hδsmall : δ * (((Ch + Cl) * C) + 1) ≤ 1 / 4 := by
    exact (le_div_iff₀ hden).mp (min_le_right _ _)
  have hChδ : Ch * (C * δ) ≤ 1 / 4 := by
    nlinarith [mul_nonneg hCl (mul_nonneg C.coe_nonneg hδ.le)]
  have hClδ : Cl * (C * δ) ≤ 1 / 4 := by
    nlinarith [mul_nonneg hCh (mul_nonneg C.coe_nonneg hδ.le)]
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro v hv
  let q := ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (laplacianPrincipalCoefficient g))
  have hdist : ‖alpha v - q‖ ≤ C * δ := by
    have hh := halpha.dist_le_mul v ⟨0, Metric.mem_closedBall_self hR.le⟩
    rw [hzero] at hh
    change dist (alpha v) q ≤ C * dist v.val (0 : X) at hh
    rw [dist_eq_norm, dist_zero_right] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hv C.coe_nonneg)
  constructor
  · calc
      _ ≤ ‖m‖ * ‖alpha v - q‖ * ‖parameterSecondDerivativeHs g 1‖ :=
        norm_parameterPrincipalOperatorHsPi_le g (alpha v)
      _ ≤ ‖m‖ * (C * δ) * ‖parameterSecondDerivativeHs g 1‖ := by gcongr
      _ = Ch * (C * δ) := by dsimp only [Ch]; ring
      _ ≤ 1 / 4 := hChδ
  · calc
      _ ≤ ‖M‖ * (‖E‖ * ‖alpha v - q‖) *
          ‖Z.comp (parameterSecondDerivativeHs g 0)‖ :=
        norm_parameterPrincipalOperatorH0Pi_le g (alpha v)
      _ ≤ ‖M‖ * (‖E‖ * (C * δ)) * ‖Z.comp (parameterSecondDerivativeHs g 0)‖ := by gcongr
      _ = Cl * (C * δ) := by dsimp only [Cl]; ring
      _ ≤ 1 / 4 := hClδ

end AddCircle

namespace DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem graph_h3_inclusion_comp
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1))
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)) v) =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)) v := by
  apply PiLp.ext
  intro i
  exact tensorHsInclusion_trans_apply (by norm_num) (by norm_num) (v i)

private theorem graph_high_field_h2_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {R : ℝ} (hR : 0 < R)
    (alpha : Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R →
        TensorHs g 0 0 1)
    (C : ℝ)
    (hlift : ∀ T : ℝ,
      ∀ v : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 1))) T,
      ∀ w : ℝ → Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R,
      (fun t => (w t).val) =ᵐ[timeMeasure T] (fun t => ContinuousLinearMap.piLpMap 2
        (fun _ : ι => tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1)) (v t)) →
      ∃ a₂ : timeL2 (TensorHs g 0 0 2) T,
        (fun t => tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 2) (a₂ t)) =ᵐ[timeMeasure T]
            (fun t => alpha (w t)) ∧ ‖a₂‖ ≤ C * (Real.sqrt T + ‖v‖))
    {T : ℝ}
    (v : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    let A := fun (_ : ℝ) z => tensorHsCongrL g 0 0
      (by norm_num : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha z)
    (∀ᵐ t ∂timeMeasure T, ‖J (v t)‖ ≤ R) →
    ∃ a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (fun t => tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
          (fun t => extendClosedBall hR.le A t (J (v t))) := by
  intro J A hv
  let N := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
  let H := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) + 1))
  let vN := N.compLpL 2 (timeMeasure T) v
  let vJ := J.compLpL 2 (timeMeasure T) v
  have hvJ : ∀ᵐ t ∂timeMeasure T, vJ t ∈ Metric.closedBall 0 R := by
    filter_upwards [hv, J.coeFn_compLpL (p := 2) (μ := timeMeasure T) v] with t ht he
    simpa only [vJ, he, Metric.mem_closedBall, dist_zero_right] using ht
  let w := aeSetLift (Metric.mem_closedBall_self hR.le) vJ
  have hw : (fun t => (w t).val) =ᵐ[timeMeasure T] fun t => H (vN t) := by
    filter_upwards [aeSetLift_coe_ae (Metric.mem_closedBall_self hR.le) vJ hvJ,
      J.coeFn_compLpL (p := 2) (μ := timeMeasure T) v,
      N.coeFn_compLpL (p := 2) (μ := timeMeasure T) v] with t ht hJ hN
    exact ht.trans (hJ.trans ((congrArg H hN).trans
      (graph_h3_inclusion_comp g (v t))).symm)
  obtain ⟨a₂, ha₂, _⟩ := hlift T vN w hw
  let S := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ 2)
  refine ⟨S.compLpL 2 (timeMeasure T) a₂, ?_⟩
  filter_upwards [ha₂, S.coeFn_compLpL (p := 2) (μ := timeMeasure T) a₂,
    aeSetLift_coe_ae (Metric.mem_closedBall_self hR.le) vJ hvJ,
    J.coeFn_compLpL (p := 2) (μ := timeMeasure T) v] with t ht hS hwJ hJ
  have hwv : (w t).val = J (v t) := hwJ.trans hJ
  have hm : J (v t) ∈ Metric.closedBall 0 R := hwv ▸ (w t).property
  rw [extendClosedBall_apply hR.le A t _ hm, hS]
  have hwsub : (w t) = ⟨J (v t), hm⟩ := Subtype.ext hwv
  apply TensorHs.ext
  have hc {a b : ℝ} (hab : a = b) (z : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 hab z).coeff = z.coeff := by
    cases hab
    rfl
  change (a₂ t).coeff = (tensorHsCongrL g 0 0 _ (alpha ⟨J (v t), hm⟩)).coeff
  rw [hc, ← hwsub]
  exact congrArg TensorHs.coeff ht



private theorem exists_graphical_coefficient_with_h2_field_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    ∃ R : ℝ, ∃ hR : 0 < R, ∃ Ca : ℝ≥0,
      ∃ alpha : Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R →
          TensorHs g 0 0 1,
      LipschitzWith Ca alpha ∧
      (∀ v x, scalarH1ToContinuous g (alpha v) x =
        graphDiffusionCoefficient (WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
          (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
            (AddCircle.parameterDerivativeHsPi g 1 (J f₀ + v.val) i)) x))) ∧
      let A := fun (_ : ℝ) z => tensorHsCongrL g 0 0
        (by norm_num : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha z)
      ∀ T : ℝ,
      ∀ v : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T,
      (∀ᵐ t ∂timeMeasure T, ‖J (v t)‖ ≤ R) →
      ∃ a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
            (fun t => extendClosedBall hR.le A t (J (v t))) := by
  intro J
  let N := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
  obtain ⟨R, hR, Ca, alpha, hα, hαeval, C₂, hC₂, hlift⟩ :=
    exists_graphDiffusionCoefficient_h1_on_closedBall_with_timeL2_h2_bound g (N f₀)
  refine ⟨R, hR, Ca, alpha, hα, ?_, ?_⟩
  · intro v x
    have h := hαeval v x
    rw [graph_h3_inclusion_comp g f₀] at h
    exact h
  · intro A T v hv
    exact graph_high_field_h2_lift g hR alpha C₂ hlift v hv

private theorem graph_coefficient_time_and_principal_bounds
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    {R : ℝ} (hR : 0 < R) {Ca : ℝ≥0}
    (alpha : Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R →
        TensorHs g 0 0 1) (hα : LipschitzWith Ca alpha) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    let slope := fun z x => WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
      (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
        (AddCircle.parameterDerivativeHsPi g 1 z i)) x)
    (∀ v x, scalarH1ToContinuous g (alpha v) x =
      graphDiffusionCoefficient (slope (J f₀ + v.val) x)) →
    (∀ x, AddCircle.metricCoefficient g x = 1 + ‖slope (J f₀) x‖ ^ 2) →
    let A := fun (_ : ℝ) v =>
      tensorHsCongrL g 0 0 (by norm_num : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha v)
    LipschitzWith Ca (fun p : ℝ × Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R => A p.1 p.2) ∧
    A 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g)) ∧
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ v, ‖v.val‖ ≤ δ →
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (A 0 v)‖ ≤ (1 / 4 : ℝ) ∧
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g (A 0 v)‖ ≤ (1 / 4 : ℝ) := by
  intro J slope hαeval' hg A
  have hA : LipschitzWith Ca (fun p : ℝ × Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R => A p.1 p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change dist (tensorHsCongrL g 0 0 _ _) (tensorHsCongrL g 0 0 _ _) ≤ _
    rw [dist_eq_norm, ← map_sub, tensorHsCongrL_apply, norm_tensorHsCongr]
    have hd : dist p.2 q.2 ≤ dist p q := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    simpa only [dist_eq_norm] using ((hα.dist_le_mul p.2 q.2).trans
      (mul_le_mul_of_nonneg_left hd Ca.coe_nonneg))
  have hA0 : A 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g)) := by
    apply graph_coefficient_eq_principal g (alpha ⟨0, Metric.mem_closedBall_self hR.le⟩)
      (fun x => WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J f₀) i)) x))
    · intro x
      simpa only [add_zero] using hαeval' ⟨0, Metric.mem_closedBall_self hR.le⟩ x
    · exact hg
  have hA' : LipschitzWith Ca (A 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    change dist (tensorHsCongrL g 0 0 _ _) (tensorHsCongrL g 0 0 _ _) ≤ _
    rw [dist_eq_norm, ← map_sub, tensorHsCongrL_apply, norm_tensorHsCongr]
    simpa only [dist_eq_norm] using hα.dist_le_mul v w
  obtain ⟨δ, hδ, hδR, hsmall⟩ := AddCircle.exists_pos_parameterPrincipal_norm_le_of_lipschitz
    (ι := ι) g hR (A 0) hA' hA0
  exact ⟨hA, hA0, δ, hδ, hδR, hsmall⟩

private theorem exists_circle_solution_of_lipschitz_diffusion
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (A : ℝ → Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R →
        TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (Ca : ℝ≥0)
    (hA : LipschitzWith Ca (fun p : ℝ × Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R => A p.1 p.2))
    (hA0 : A 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g))) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
        (force : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T),
      let field := maximalRegularityDuhamelVectorField hT 0 force
      u = maximalRegularityDuhamelVectorMap hT 0 force ∧
      (∀ᵐ t ∂timeMeasure T, ‖J (field t)‖ ≤ R ∧ ‖J (field t)‖ ≤ δ) ∧
      u.toFunL2 = K.compLpL 2 (timeMeasure T) field ∧
      timeH1.trace0 _ T u = 0 ∧
      timeH1.timeDeriv _ T u = L.compLpL 2 (timeMeasure T) field + force ∧
      (∀ᵐ t ∂timeMeasure T, L (field t) + force t =
        ContinuousLinearMap.piLpMap 2 (fun _ : ι => scalarHsMul g 1 (by norm_num)
          (extendClosedBall hR.le A t (J (field t))))
            (AddCircle.parameterSecondDerivativeHsPi g 1 (f₀ + field t))) := by
  intro J K L
  let B := fun (_ : ℝ) (_ : Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R) =>
    (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
  have hB : LipschitzWith 0 (fun p : ℝ × Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R => B p.1 p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simp only [B, dist_self, NNReal.coe_zero, zero_mul, le_refl]
  obtain ⟨r, hr, hrR, hr1, hrδ, T, hT, hTr, u, force,
      hu, hstate, hforce, hlink, htrace, hderiv, hnorm, hpde⟩ :=
    circle_shifted_solution_with_radius_le_of_lipschitz_coefficients
      g 1 (by norm_num) f₀ hR hδ A B Ca 0 hA hB hA0
  refine ⟨T, hT, u, force, hu, hstate.mono (fun t ht => ⟨ht.trans hrR, ht.trans hrδ⟩),
    hlink, htrace, hderiv, ?_⟩
  have hbb : ∀ t z, extendClosedBall hR.le B t z = 0 := by
    intro t z
    simp only [extendClosedBall, B]
    split_ifs <;> rfl
  filter_upwards [hpde] with t ht
  simpa only [hbb, add_zero, coordinateMultiplication, LinearMap.mkContinuous_apply,
    LinearMap.coe_mk, AddHom.coe_mk, circleHsPiInclusion, J, L] using ht

private theorem ae_parameter_principal_bounds_of_coefficient_lift
    {ι X : Type*} [Fintype ι] [NormedAddCommGroup X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {R δ T : ℝ} (hR : 0 ≤ R)
    (A : ℝ → Metric.closedBall (0 : X) R → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (v : ℝ → X)
    (a₂ : ℝ → TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))
    (ha₂ : (fun t => tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
        (fun t => extendClosedBall hR A t (v t)))
    (hstate : ∀ᵐ t ∂timeMeasure T, ‖v t‖ ≤ R ∧ ‖v t‖ ≤ δ)
    (hsmall : ∀ t (w : Metric.closedBall (0 : X) R), ‖w.val‖ ≤ δ →
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (A t w)‖ ≤ (1 / 4 : ℝ) ∧
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g (A t w)‖ ≤ (1 / 4 : ℝ)) :
    ∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g
        (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))‖ ≤ (1 / 4 : ℝ) ∧
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g
        (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))‖ ≤ (1 / 4 : ℝ) := by
  filter_upwards [ha₂, hstate] with t ht hs
  rw [ht]
  have hm : v t ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hs.1
  rw [extendClosedBall_apply hR A t _ hm]
  exact hsmall t ⟨v t, hm⟩ hs.2

private theorem ae_circle_component_equation_of_coefficient_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ}
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (field : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (force : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
    (aa : ℝ → TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (ha₂ : (fun t => tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T] aa)
    (hpde : ∀ᵐ t ∂timeMeasure T,
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
        (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))) (field t) + force t =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => scalarHsMul g 1 (by norm_num) (aa t))
        (AddCircle.parameterSecondDerivativeHsPi g 1 (f₀ + field t))) :
    ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (field t i) + force t i =
        scalarHsMul g 1 (by norm_num)
          (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g 1 (f₀ i + field t i)) +
          tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
            ((0 : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T) t i) := by
  filter_upwards [hpde, ha₂, Lp.coeFn_zero
    (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) 2 (timeMeasure T)] with t ht ha hz
  intro i
  rw [ha, hz, Pi.zero_apply, PiLp.zero_apply, map_zero, add_zero]
  have hi := congrArg (fun z => z i) ht
  simpa only [PiLp.add_apply, ContinuousLinearMap.piLpMap_apply,
    AddCircle.parameterSecondDerivativeHsPi_apply] using hi

private theorem exists_circle_solution_with_h2_diffusion
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (A : ℝ → Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R →
        TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (Ca : ℝ≥0)
    (hA : LipschitzWith Ca (fun p : ℝ × Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R => A p.1 p.2))
    (hA0 : A 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g)))
    (hsmall : ∀ t v, ‖v.val‖ ≤ δ →
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g (A t v)‖ ≤ (1 / 4 : ℝ) ∧
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g (A t v)‖ ≤ (1 / 4 : ℝ)) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    (∀ T : ℝ,
      ∀ v : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T,
      (∀ᵐ t ∂timeMeasure T, ‖J (v t)‖ ≤ R) →
      ∃ a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
            (fun t => extendClosedBall hR.le A t (J (v t)))) →
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
        (force : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
        (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T),
      let field := maximalRegularityDuhamelVectorField hT 0 force
      let aa := fun t => extendClosedBall hR.le A t (J (field t))
      u = maximalRegularityDuhamelVectorMap hT 0 force ∧
      (∀ᵐ t ∂timeMeasure T, ‖J (field t)‖ ≤ R) ∧
      u.toFunL2 = K.compLpL 2 (timeMeasure T) field ∧
      timeH1.trace0 _ T u = 0 ∧
      timeH1.timeDeriv _ T u =
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))).compLpL
            2 (timeMeasure T) field + force ∧
      (∀ᵐ t ∂timeMeasure T,
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
          (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))) (field t) + force t =
        ContinuousLinearMap.piLpMap 2 (fun _ : ι => scalarHsMul g 1 (by norm_num) (aa t))
          (AddCircle.parameterSecondDerivativeHsPi g 1 (f₀ + field t))) ∧
      (∀ᵐ t ∂timeMeasure T,
        ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g
          (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))‖ ≤ (1 / 4 : ℝ) ∧
        ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g
          (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))‖ ≤ (1 / 4 : ℝ)) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (field t i) + force t i =
          scalarHsMul g 1 (by norm_num)
            (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))
            (AddCircle.parameterSecondDerivativeHs g 1 (f₀ i + field t i)) +
            tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
              ((0 : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T) t i)) := by
  intro J K hlift
  obtain ⟨T, hT, u, force, hu, hstate, hlink, htrace, hderiv, hpde⟩ :=
    exists_circle_solution_of_lipschitz_diffusion g f₀ hR hδ A Ca hA hA0
  let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
    (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 force
  let aa := fun t => extendClosedBall hR.le A t (J (field t))
  have hstateR : ∀ᵐ t ∂timeMeasure T, ‖J (field t)‖ ≤ R :=
    hstate.mono fun t ht => ht.1
  have hfieldLift : ∃ a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T,
      (fun t => tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T] aa :=
    hlift T field hstateR
  let a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T :=
    Classical.choose hfieldLift
  have ha₂ : (fun t => tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T] aa :=
    Classical.choose_spec hfieldLift
  refine ⟨T, hT, u, force, a₂, hu, hstateR, hlink, htrace, hderiv, hpde, ?_, ?_⟩
  · exact ae_parameter_principal_bounds_of_coefficient_lift g hR.le A
      (fun t => J (field t)) a₂ ha₂ hstate hsmall
  · exact ae_circle_component_equation_of_coefficient_lift g f₀ field force aa a₂ ha₂ hpde

private theorem graph_fixed_point_with_h2_diffusion
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    {R : ℝ} (hR : 0 < R) {Ca : ℝ≥0}
    (alpha : Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R →
        TensorHs g 0 0 1) (hα : LipschitzWith Ca alpha) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    let A := fun (_ : ℝ) z => tensorHsCongrL g 0 0
      (by norm_num : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha z)
    (∀ v x, scalarH1ToContinuous g (alpha v) x =
      graphDiffusionCoefficient (WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J f₀ + v.val) i)) x))) →
    (∀ x, AddCircle.metricCoefficient g x =
      1 + ‖WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J f₀) i)) x)‖ ^ 2) →
    (∀ T : ℝ,
      ∀ v : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T,
      (∀ᵐ t ∂timeMeasure T, ‖J (v t)‖ ≤ R) →
      ∃ a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
            (fun t => extendClosedBall hR.le A t (J (v t)))) →
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
        (force : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
        (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T),
      let field := maximalRegularityDuhamelVectorField hT 0 force
      let aa := fun t => extendClosedBall hR.le A t (J (field t))
      u = maximalRegularityDuhamelVectorMap hT 0 force ∧
      (∀ᵐ t ∂timeMeasure T, ‖J (field t)‖ ≤ R) ∧
      u.toFunL2 = K.compLpL 2 (timeMeasure T) field ∧
      timeH1.trace0 _ T u = 0 ∧
      timeH1.timeDeriv _ T u =
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))).compLpL
            2 (timeMeasure T) field + force ∧
      (∀ᵐ t ∂timeMeasure T,
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
          (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))) (field t) + force t =
        ContinuousLinearMap.piLpMap 2 (fun _ : ι => scalarHsMul g 1 (by norm_num) (aa t))
          (AddCircle.parameterSecondDerivativeHsPi g 1 (f₀ + field t))) ∧
      (∀ᵐ t ∂timeMeasure T,
        ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g
          (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))‖ ≤ (1 / 4 : ℝ) ∧
        ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g
          (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))‖ ≤ (1 / 4 : ℝ)) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (field t i) + force t i =
          scalarHsMul g 1 (by norm_num)
            (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))
            (AddCircle.parameterSecondDerivativeHs g 1 (f₀ i + field t i)) +
            tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
              ((0 : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T) t i)) := by
  intro J K A hαeval' hg hlift
  obtain ⟨hA, hA0, δ, hδ, hδR, hsmall⟩ :=
    graph_coefficient_time_and_principal_bounds g f₀ hR alpha hα hαeval' hg
  exact exists_circle_solution_with_h2_diffusion g f₀ hR hδ A Ca hA hA0
    (fun _ v hv => hsmall v hv) hlift


private theorem graph_ae_equation_of_sobolev_evolution
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    {R : ℝ} (hR : 0 < R)
    (alpha : Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R →
        TensorHs g 0 0 1) {T : ℝ}
    (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (field : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T)
    (force : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let A := fun (_ : ℝ) z => tensorHsCongrL g 0 0
      (by norm_num : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha z)
    let aa := fun t => extendClosedBall hR.le A t (J (field t))
    let L := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ))
    (∀ v x, scalarH1ToContinuous g (alpha v) x =
      graphDiffusionCoefficient (WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J f₀ + v.val) i)) x))) →
    (∀ᵐ t ∂timeMeasure T, ‖J (field t)‖ ≤ R) →
    u.toFunL2 = K.compLpL 2 (timeMeasure T) field →
    timeH1.timeDeriv _ T u = L.compLpL 2 (timeMeasure T) field + force →
    (∀ᵐ t ∂timeMeasure T, L (field t) + force t =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => scalarHsMul g 1 (by norm_num) (aa t))
        (AddCircle.parameterSecondDerivativeHsPi g 1 (f₀ + field t))) →
    let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (K f₀ + u.toFun t))
      (x : AddCircle (1 : ℝ))
    ∀ᵐ t ∂timeMeasure T, ∀ x,
      HasDerivAt (fun s => f s x)
        (graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f t) x)) •
          deriv (deriv (f t)) x) t := by
  intro J K C A aa L hαeval' hstate hlink hderiv hpde
  let bb := fun (_ : ℝ) => (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
  have hbb : ∀ t, bb t = 0 := fun _ => rfl
  have hpoint := ae_hasDerivAt_of_circle_sobolev_evolution g u field f₀ force
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ)))
    aa bb hlink hderiv (hpde.mono fun t ht => by simpa only [bb, add_zero] using ht)
  let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (K f₀ + u.toFun t))
      (x : AddCircle (1 : ℝ))
  have hcoe := K.coeFn_compLpL (p := 2) (μ := timeMeasure T) field
  have hufun := coeFn_ofContinuousOn u.continuousOn_toFun
  filter_upwards [hpoint, hstate, hcoe, hufun] with t ht hst hkt hut
  have hval : u.toFun t = K (field t) := by
    change u.toFunL2 t = u.toFun t at hut
    rw [hlink] at hut
    exact hut.symm.trans hkt
  have halpha : ∀ x : ℝ,
      scalarH1ToContinuous g
        (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) (aa t))
        (x : AddCircle (1 : ℝ)) =
      graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f t) x)) := by
    have he := graph_coefficient_eval_eq_slope g f₀ (field t) hR.le alpha
      hαeval' hst t
    have hf : f t = fun y : ℝ => scalarH1PiToContinuous g
        (C (K (f₀ + field t))) (y : AddCircle (1 : ℝ)) := by
      funext y
      simp only [f, hval, map_add]
    rw [hf]
    exact he
  intro x
  have hd := ht.2 x
  rw [halpha x, hbb t, map_zero, map_zero] at hd
  simpa only [ContinuousMap.zero_apply, add_zero] using hd

private theorem graph_parameterDerivative_forcing_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₄ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    {T : ℝ} (hT : 0 < T)
    (force : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
    (a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2))
    let f₀ := P f₄
    let field := maximalRegularityDuhamelVectorField hT 0 force
    (∀ᵐ t ∂timeMeasure T,
      ‖AddCircle.parameterPrincipalOperatorHsPi (ι := ι) g
        (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))‖ ≤ (1 / 4 : ℝ) ∧
      ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := ι) g
        (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))‖ ≤ (1 / 4 : ℝ)) →
    (∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (field t i) + force t i =
        scalarHsMul g 1 (by norm_num)
          (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g 1 (f₀ i + field t i)) +
          tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
            ((0 : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T) t i)) →
    ∃ FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
      parameterDerivativeDuhamelForcing g 0 hT force =
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
              2 (timeMeasure T) FH := by
  intro P f₀ field hsmall₂ hpde₂
  have hpde₄ : ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ) (field t i) + force t i =
        scalarHsMul g 1 (by norm_num)
          (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t))
          (AddCircle.parameterSecondDerivativeHs g 1
            (tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2) (f₄ i) + field t i)) +
          tensorHsInclusion (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
            ((0 : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) T) t i) := by
    simpa only [f₀, P, ContinuousLinearMap.piLpMap_apply] using hpde₂
  obtain ⟨FH, hFH⟩ := exists_parameterDerivative_forcing_lift_of_principal_norm_lt_one
    g hT force f₄ a₂ 0 (1 / 4) (1 / 4)
    (hsmall₂.mono fun _ ht => ht.1) (hsmall₂.mono fun _ ht => ht.2)
    (by norm_num) (by norm_num) hpde₄
  exact ⟨FH, hFH⟩

private theorem graph_exists_derivative_forcing_lift_of_coefficients
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₄ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2)))
    {R : ℝ} (hR : 0 < R) {Ca : ℝ≥0}
    (alpha : Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R →
        TensorHs g 0 0 1) (hα : LipschitzWith Ca alpha) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2))
    let f₀ := P f₄
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let A := fun (_ : ℝ) z => tensorHsCongrL g 0 0
      (by norm_num : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha z)
    (∀ v x, scalarH1ToContinuous g (alpha v) x =
      graphDiffusionCoefficient (WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J f₀ + v.val) i)) x))) →
    (∀ T : ℝ,
      ∀ v : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) T,
      (∀ᵐ t ∂timeMeasure T, ‖J (v t)‖ ≤ R) →
      ∃ a₂ : timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T,
        (fun t => tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (a₂ t)) =ᵐ[timeMeasure T]
            (fun t => extendClosedBall hR.le A t (J (v t)))) →
    (∀ x, AddCircle.metricCoefficient g x =
      1 + ‖WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J f₀) i)) x)‖ ^ 2) →
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
        (force FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T),
        u = maximalRegularityDuhamelVectorMap hT 0 force ∧
        timeH1.trace0 _ T u = 0 ∧
        parameterDerivativeDuhamelForcing g 0 hT force =
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
                2 (timeMeasure T) FH ∧
        let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (K f₀ + u.toFun t))
          (x : AddCircle (1 : ℝ))
        ∀ᵐ t ∂timeMeasure T, ∀ x,
          HasDerivAt (fun s => f s x)
            (graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f t) x)) •
              deriv (deriv (f t)) x) t := by
  intro P f₀ J K C A hαeval' hlift hg
  obtain ⟨T, hT, u, force, a₂, hu, hstate, hlink, htrace, hderiv, hpde, hsmall₂, hpde₂⟩ :=
    graph_fixed_point_with_h2_diffusion g f₀ hR alpha hα hαeval' hg hlift
  let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
    (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 force
  have hforcing : ∃ FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
      parameterDerivativeDuhamelForcing g 0 hT force =
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
              2 (timeMeasure T) FH :=
    graph_parameterDerivative_forcing_lift g f₄ hT force a₂ hsmall₂ hpde₂
  let FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T := hforcing.choose
  refine ⟨T, hT, u, force, FH, hu, htrace, ?_, ?_⟩
  · exact hforcing.choose_spec
  · exact graph_ae_equation_of_sobolev_evolution g f₀ hR alpha u field force
      hαeval' hstate hlink hderiv hpde

private theorem exists_graphical_curve_shortening_with_derivative_forcing_lift
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₄ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2))) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2))
    let f₀ := P f₄
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    (∀ x, AddCircle.metricCoefficient g x =
      1 + ‖WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J f₀) i)) x)‖ ^ 2) →
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
        (force FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T),
        u = maximalRegularityDuhamelVectorMap hT 0 force ∧
        timeH1.trace0 _ T u = 0 ∧
        parameterDerivativeDuhamelForcing g 0 hT force =
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
                2 (timeMeasure T) FH ∧
        let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (K f₀ + u.toFun t))
          (x : AddCircle (1 : ℝ))
        ∀ᵐ t ∂timeMeasure T, ∀ x,
          HasDerivAt (fun s => f s x)
            (graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f t) x)) •
              deriv (deriv (f t)) x) t := by
  intro P f₀ J K C hg
  obtain ⟨R, hR, Ca, alpha, hα, hαeval', hlift⟩ :=
    exists_graphical_coefficient_with_h2_field_lift g f₀
  exact graph_exists_derivative_forcing_lift_of_coefficients g f₄ hR alpha hα
    hαeval' hlift hg

private theorem contDiff_two_of_circle_h3_representative
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ W : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    K W = u → ContDiff ℝ 2 (fun x : ℝ =>
      scalarH1PiToContinuous g (C (K f₀ + u)) (x : AddCircle (1 : ℝ))) := by
  intro K C hW
  let N := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
  let V := N (f₀ + W)
  have hV : ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) + 1)) V = C (K f₀ + u) := by
    rw [← hW, ← map_add]
    apply PiLp.ext
    intro i
    apply TensorHs.ext
    rfl
  have h := AddCircle.contDiff_two_scalarH1PiToContinuous g V
  rw [hV] at h
  exact h

theorem exists_graphical_curve_shortening_with_continuous_h3_representative_of_metric_coefficient
    {ι : Type*} [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₄ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((2 : ℕ) : ℝ) + 2))) :
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 2 ≤ ((2 : ℕ) : ℝ) + 2))
    let f₀ := P f₄
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    (∀ x, AddCircle.metricCoefficient g x =
      1 + ‖WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J f₀) i)) x)‖ ^ 2) →
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
        (force FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T)
        (W : ℝ → PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))),
        u = maximalRegularityDuhamelVectorMap hT 0 force ∧
        timeH1.trace0 _ T u = 0 ∧
        parameterDerivativeDuhamelForcing g 0 hT force =
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ)))).compLpL
                2 (timeMeasure T) FH ∧
        ContinuousOn W (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, K (W t) = u.toFun t) ∧
        W =ᵐ[timeMeasure T] maximalRegularityDuhamelVectorField hT 0 force ∧
        let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (K f₀ + u.toFun t))
          (x : AddCircle (1 : ℝ))
        (∀ x, f 0 x = scalarH1PiToContinuous g (C (K f₀)) (x : AddCircle (1 : ℝ))) ∧
        (∀ t, Function.Periodic (f t) 1) ∧
        (∀ t ∈ Icc 0 T, ContDiff ℝ 2 (f t)) ∧
        ∀ᵐ t ∂timeMeasure T, ∀ x,
          HasDerivAt (fun s => f s x)
            (graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f t) x)) •
              deriv (deriv (f t)) x) t := by
  intro P f₀ J K C hg
  obtain ⟨T, hT, u, force, FH, hu, htrace, hFH, hpde⟩ :=
    exists_graphical_curve_shortening_with_derivative_forcing_lift g f₄ hg
  obtain ⟨W, hW, hWlow, hWfield⟩ :=
    exists_continuousOn_representative_of_parameterDerivative_forcing_lift g 0 hT force FH hFH
  have hWlow' : ∀ t ∈ Icc 0 T, K (W t) = u.toFun t := by
    rw [hu]
    exact hWlow
  refine ⟨T, hT, u, force, FH, W, hu, htrace, hFH, hW, hWlow', hWfield, ?_, ?_, ?_, ?_⟩
  · intro x
    dsimp only
    rw [u.toFun_zero, ← timeH1.trace0_apply, htrace, add_zero]
  · intro t x
    dsimp only
    rw [AddCircle.coe_add_period]
  · intro t ht
    exact contDiff_two_of_circle_h3_representative g f₀ (W t) (u.toFun t) (hWlow' t ht)
  · exact hpde


end DifferentialGeometry.Analysis.Parabolic
