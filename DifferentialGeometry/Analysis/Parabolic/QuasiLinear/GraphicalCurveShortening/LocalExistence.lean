import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Sobolev
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients

open private circle_shifted_solution_with_radius_le_of_lipschitz_coefficients extendClosedBall extendClosedBall_apply from
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff NNReal
namespace DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem graph_slope_inclusion
    {ι : Type*} [Fintype ι] (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (w : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2))) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    deriv (fun x : ℝ => scalarH1PiToContinuous g (K w) (x : AddCircle (1 : ℝ))) =
      fun x : ℝ => fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J w) i)) (x : AddCircle (1 : ℝ)) := by
  intro J K
  have h := AddCircle.deriv_scalarH1PiToContinuous g (n := 1) (by omega) (J w)
  have hinc : ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)) (J w) = K w := by
    apply PiLp.ext
    intro i
    exact tensorHsInclusion_trans_apply (by norm_num) (by norm_num) (w i)
  rw [hinc] at h
  rw [h]
  funext x i
  change scalarH1ToContinuous g (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) _) _ = _
  congr 2
  apply TensorHs.ext
  funext j
  have hc {a b : ℝ} (hab : a = b) (u : TensorHs g 0 0 a) :
      (tensorHsCongrL g 0 0 hab u).coeff = u.coeff := by
    cases hab
    rfl
  simp only [tensorHsInclusion_coeff_apply, hc]
  rfl


private theorem graph_coefficient_eval_eq_slope
    {ι : Type*} [Fintype ι] (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ v : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    {R : ℝ} (hR : 0 ≤ R)
    (alpha : Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R →
        TensorHs g 0 0 1) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let A := fun (_ : ℝ) z =>
      tensorHsCongrL g 0 0 (by norm_num : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha z)
    (∀ z x, scalarH1ToContinuous g (alpha z) x =
      graphDiffusionCoefficient (WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J f₀ + z.val) i)) x))) →
    ‖J v‖ ≤ R → ∀ t (x : ℝ),
      scalarH1ToContinuous g
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
            (extendClosedBall hR A t (J v))) (x : AddCircle (1 : ℝ)) =
      graphDiffusionCoefficient (WithLp.toLp 2 (deriv
        (fun y : ℝ => scalarH1PiToContinuous g (C (K (f₀ + v)))
          (y : AddCircle (1 : ℝ))) x)) := by
  intro J K C A hαeval hv t x
  let K₁ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
  have hfval : C (K (f₀ + v)) = K₁ (f₀ + v) := by
    apply PiLp.ext
    intro i
    exact tensorHsInclusion_trans_apply (by norm_num) (by norm_num) ((f₀ + v) i)
  rw [hfval, graph_slope_inclusion g (f₀ + v)]
  have hmem : J v ∈ Metric.closedBall (0 : PiLp 2
      (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  rw [extendClosedBall_apply hR A t _ hmem]
  have hcast : tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
      (A t ⟨J v, hmem⟩) = alpha ⟨J v, hmem⟩ := by
    dsimp only [A]
    have hc {a b : ℝ} (hab : a = b) (hba : b ≤ a) (w : TensorHs g 0 0 b) :
        tensorHsInclusion hba (tensorHsCongrL g 0 0 hab.symm w) = w := by
      cases hab
      exact tensorHsInclusion_refl_apply w
    exact hc (by norm_num : ((1 : ℕ) : ℝ) = 1) (by norm_num) _
  simp only [hcast, hαeval, map_add]
  rfl


private theorem graph_coefficient_eq_principal
    {ι : Type*} [Fintype ι] (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 1) (p : AddCircle (1 : ℝ) → EuclideanSpace ℝ ι)
    (ha : ∀ x, scalarH1ToContinuous g a x = graphDiffusionCoefficient (p x))
    (hg : ∀ x, AddCircle.metricCoefficient g x = 1 + ‖p x‖ ^ 2) :
    tensorHsCongrL g 0 0 (by norm_num : (1 : ℝ) = ((1 : ℕ) : ℝ)) a =
      ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g)) := by
  have hz : a = ccTensorToHs g 0 1 (scalarCc g (AddCircle.laplacianPrincipalCoefficient g)) := by
    apply scalarH1ToContinuous_injective g
    ext x
    rw [ha, scalarH1ToContinuous_apply_ccTensorToHs, scalar0_scalarCc,
      AddCircle.laplacianPrincipalCoefficient_apply, hg]
    rfl
  rw [hz]
  have hc {a b : ℝ} (hab : a = b) (S : SmoothCcTensor g 0 0) :
      tensorHsCongrL g 0 0 hab (ccTensorToHs g 0 a S) = ccTensorToHs g 0 b S := by
    cases hab
    rfl
  exact hc _ _


theorem exists_graphical_curve_shortening_sobolev_solution_of_metric_coefficient
    {ι : Type*} [Fintype ι] (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)))
    (hg : ∀ x, AddCircle.metricCoefficient g x =
      1 + ‖WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorHsInclusion (g := g) (r := 0) (s := 0)
                (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)) f₀) i)) x)‖ ^ 2) :
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2))
    let C := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    ∃ T : ℝ, 0 < T ∧
      ∃ u : timeH1 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ))) T,
        timeH1.trace0 _ T u = 0 ∧
        let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (K f₀ + u.toFun t))
          (x : AddCircle (1 : ℝ))
        (∀ x, f 0 x = scalarH1PiToContinuous g (C (K f₀)) (x : AddCircle (1 : ℝ))) ∧
        (∀ t, Function.Periodic (f t) 1) ∧
        ∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (f t) ∧ ∀ x,
          HasDerivAt (fun s => f s x)
            (graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f t) x)) •
              deriv (deriv (f t)) x) t := by
  intro K C
  let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2))
  obtain ⟨R, hR, Ca, alpha, hα, hαeval⟩ :=
    exists_graphDiffusionCoefficient_h1_on_closedBall g (J f₀)
  let A := fun (_ : ℝ) v =>
    tensorHsCongrL g 0 0 (by norm_num : (1 : ℝ) = ((1 : ℕ) : ℝ)) (alpha v)
  let B := fun (_ : ℝ) (_ : Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R) =>
    (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((1 : ℕ) : ℝ)))
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
  have hB : LipschitzWith 0 (fun p : ℝ × Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1))) R => B p.1 p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simp only [B, dist_self, NNReal.coe_zero, zero_mul, le_refl]
  have hA0 : A 0 ⟨0, Metric.mem_closedBall_self hR.le⟩ =
      ccTensorToHs g 0 ((1 : ℕ) : ℝ) (scalarCc g (AddCircle.laplacianPrincipalCoefficient g)) := by
    apply graph_coefficient_eq_principal g (alpha ⟨0, Metric.mem_closedBall_self hR.le⟩)
      (fun x => WithLp.toLp 2 (fun i : ι => scalarH1ToContinuous g
        (tensorHsCongrL g 0 0 (by norm_num : ((1 : ℕ) : ℝ) = 1)
          (AddCircle.parameterDerivativeHsPi g 1 (J f₀) i)) x))
    · intro x
      simpa only [add_zero] using hαeval ⟨0, Metric.mem_closedBall_self hR.le⟩ x
    · exact hg
  obtain ⟨r, hr, hrR, hr1, _, T, hT, hTr, u, force,
      hu, hstate, hforce, hlink, htrace, hderiv, hnorm, hpde⟩ :=
    circle_shifted_solution_with_radius_le_of_lipschitz_coefficients
      g 1 (by norm_num) f₀ hR hR A B Ca 0 hA hB hA0
  let field := maximalRegularityDuhamelVectorField (I := 𝓘(ℝ, ℝ))
    (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0) (a := ((1 : ℕ) : ℝ)) hT 0 force
  let aa := fun t => extendClosedBall hR.le A t (J (field t))
  let bb := fun t => extendClosedBall hR.le B t (J (field t))
  have hbb : ∀ t, bb t = 0 := by
    intro t
    simp only [bb, extendClosedBall, B]
    split_ifs <;> rfl
  have hpoint := ae_hasDerivAt_of_circle_sobolev_evolution g u field f₀ force
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((1 : ℕ) : ℝ)))
    aa bb hlink hderiv hpde
  refine ⟨T, hT, u, htrace, ?_, ?_, ?_⟩
  · intro x
    dsimp only
    rw [u.toFun_zero, ← timeH1.trace0_apply, htrace, add_zero]
  · intro t x
    dsimp only
    rw [AddCircle.coe_add_period]
  · let f := fun t (x : ℝ) => scalarH1PiToContinuous g (C (K f₀ + u.toFun t))
        (x : AddCircle (1 : ℝ))
    change ∀ᵐ t ∂timeMeasure T, ContDiff ℝ 2 (f t) ∧ ∀ x,
      HasDerivAt (fun s => f s x)
        (graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f t) x)) •
          deriv (deriv (f t)) x) t
    have hcoe := K.coeFn_compLpL (p := 2) (μ := timeMeasure T) field
    have hufun := coeFn_ofContinuousOn u.continuousOn_toFun
    filter_upwards [hpoint, hstate, hcoe, hufun] with t ht hst hkt hut
    change ContDiff ℝ 2 (f t) ∧ ∀ x : ℝ,
      HasDerivAt (fun s => f s x)
        (scalarH1ToContinuous g
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) (aa t))
          (x : AddCircle (1 : ℝ)) • deriv (deriv (f t)) x +
            scalarH1PiToContinuous g (C (bb t)) (x : AddCircle (1 : ℝ))) t at ht
    clear hu hforce hnorm hpde hr1 hTr
    have hval : u.toFun t = K (field t) := by
      change u.toFunL2 t = u.toFun t at hut
      rw [hlink] at hut
      exact hut.symm.trans hkt
    have halpha : ∀ x : ℝ,
        scalarH1ToContinuous g
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) (aa t))
          (x : AddCircle (1 : ℝ)) =
        graphDiffusionCoefficient (WithLp.toLp 2 (deriv (f t) x)) := by
      have he := graph_coefficient_eval_eq_slope g f₀ (field t) hR.le alpha
        hαeval (hst.trans hrR) t
      have hf : f t = fun y : ℝ => scalarH1PiToContinuous g
          (C (K (f₀ + field t))) (y : AddCircle (1 : ℝ)) := by
        funext y
        simp only [f, hval, map_add]
      rw [hf]
      exact he
    refine ⟨ht.1, fun x => ?_⟩
    have hd := ht.2 x
    rw [halpha x, hbb t, map_zero, map_zero] at hd
    simpa only [ContinuousMap.zero_apply, add_zero] using hd

end DifferentialGeometry.Analysis.Parabolic
