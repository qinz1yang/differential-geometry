import DifferentialGeometry.Geometry.Metric.Conformal.Operators
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open MeasureTheory
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem chartGramMatrix_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯) (a x : M) :
    chartGramMatrix (conformalMetric g u) a x =
      Real.exp (2 * u x) • chartGramMatrix g a x := by
  ext i j
  simp [chartGramMatrix_apply, conformalMetric_inner]

theorem chartDensity_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯) (a x : M) :
    chartDensity (conformalMetric g u) a x =
      Real.exp ((Module.finrank Real E : Real) * u x) * chartDensity g a x := by
  unfold chartDensity
  rw [chartGramMatrix_conformalMetric, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [Real.sqrt_mul (pow_nonneg (Real.exp_pos _).le _), ← Real.exp_nat_mul]
  congr 1
  have heq : Real.exp ((Module.finrank Real E : Real) * (2 * u x)) =
      Real.exp ((Module.finrank Real E : Real) * u x) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq, Real.sqrt_sq (Real.exp_pos _).le]

theorem chartLocalMeasure_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯) (a : M) :
    chartLocalMeasure (I := I) (conformalMetric g u) a =
      (chartLocalMeasure (I := I) g a).withDensity
        (fun x => ENNReal.ofReal (Real.exp ((Module.finrank Real E : Real) * u x))) := by
  let μ := (modelHaar (E := E)).restrict (extChartAt I a).target
  let F := (extChartAt I a).symm
  let d : E → ℝ≥0∞ := fun y => ENNReal.ofReal (chartDensity g a (F y))
  let w : M → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp ((Module.finrank Real E : Real) * u x))
  have hF : AEMeasurable F μ := aemeasurable_extChartAt_symm_restrict_target a
  have hd : AEMeasurable d μ := aemeasurable_chartDensity_symm_pullback g a
  have hw : Measurable w :=
    (Real.continuous_exp.comp (continuous_const.mul u.contMDiff.continuous)).measurable.ennreal_ofReal
  have hwF : AEMeasurable (w ∘ F) μ := hw.comp_aemeasurable hF
  have hF' : AEMeasurable F (μ.withDensity d) :=
    hF.mono' (withDensity_absolutelyContinuous μ d)
  have hF'' : AEMeasurable F (μ.withDensity (d * (w ∘ F))) :=
    hF.mono' (withDensity_absolutelyContinuous μ _)
  have hshape : chartLocalMeasure (I := I) (conformalMetric g u) a =
      Measure.map F (μ.withDensity (d * (w ∘ F))) := by
    unfold chartLocalMeasure
    congr 2
    funext y
    rw [chartDensity_conformalMetric, ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_comm _ _
  rw [hshape]
  change Measure.map F (μ.withDensity (d * (w ∘ F))) =
    (Measure.map F (μ.withDensity d)).withDensity w
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_map' hφ.aemeasurable hF'']
  change (∫⁻ y, (φ ∘ F) y ∂μ.withDensity (d * (w ∘ F))) = _
  rw [lintegral_withDensity_eq_lintegral_mul₀ (hd.mul hwF) (hφ.comp_aemeasurable hF),
    lintegral_withDensity_eq_lintegral_mul₀ hw.aemeasurable hφ.aemeasurable,
    lintegral_map' (hw.mul hφ).aemeasurable hF']
  change _ = ∫⁻ y, ((w * φ) ∘ F) y ∂μ.withDensity d
  rw [lintegral_withDensity_eq_lintegral_mul₀ hd ((hw.mul hφ).comp_aemeasurable hF)]
  apply lintegral_congr
  intro y
  exact mul_assoc _ _ _

theorem riemannianMeasure_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (ρ : SmoothPartitionOfUnity M I M Set.univ) :
    riemannianMeasure (I := I) (conformalMetric g u) ρ =
      (riemannianMeasure (I := I) g ρ).withDensity
        (fun x => ENNReal.ofReal (Real.exp ((Module.finrank Real E : Real) * u x))) := by
  let w : M → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp ((Module.finrank Real E : Real) * u x))
  have hw : Measurable w :=
    (Real.continuous_exp.comp (continuous_const.mul u.contMDiff.continuous)).measurable.ennreal_ofReal
  unfold riemannianMeasure
  rw [withDensity_sum]
  congr 1
  funext a
  rw [chartLocalMeasure_conformalMetric]
  change ((chartLocalMeasure (I := I) g a).withDensity w).withDensity
      (fun x => ENNReal.ofReal (ρ a x)) =
    ((chartLocalMeasure (I := I) g a).withDensity
      (fun x => ENNReal.ofReal (ρ a x))).withDensity w
  have hρ : Measurable (fun x => ENNReal.ofReal (ρ a x)) :=
    (ρ a).contMDiff.continuous.measurable.ennreal_ofReal
  rw [← withDensity_mul _ hw hρ, ← withDensity_mul _ hρ hw, mul_comm]

theorem riemannianVolumeMeasure_conformalMetric [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯) :
    riemannianVolumeMeasure (I := I) (M := M) (conformalMetric g u) =
      (riemannianVolumeMeasure (I := I) (M := M) g).withDensity
        (fun x => ENNReal.ofReal (Real.exp ((Module.finrank Real E : Real) * u x))) := by
  exact riemannianMeasure_conformalMetric g u (chartAtlasPOU I M)

theorem integral_conformalMetric_eq_integral_smul_exp
    [T2Space M] [SigmaCompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯) (f : M → V) :
    (∫ x, f x ∂riemannianVolumeMeasure (I := I) (M := M) (conformalMetric g u)) =
      ∫ x, Real.exp ((Module.finrank Real E : Real) * u x) • f x
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  rw [riemannianVolumeMeasure_conformalMetric]
  let w : M → ENNReal := fun x => ENNReal.ofReal
    (Real.exp ((Module.finrank Real E : Real) * u x))
  have hw : Measurable w :=
    (Real.continuous_exp.comp (continuous_const.mul u.contMDiff.continuous)).measurable.ennreal_ofReal
  have hw_top : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g, w x < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun x => by simp [w]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hw.aemeasurable hw_top]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem integral_inner_gradientFun_conformalMetric
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯) (f h : M → Real) :
    (∫ x, (conformalMetric g u).inner x
        (Geometry.Operator.gradientFun (conformalMetric g u) f x)
        (Geometry.Operator.gradientFun (conformalMetric g u) h x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (conformalMetric g u)) =
      ∫ x, Real.exp (((Module.finrank Real E : Real) - 2) * u x) *
        g.inner x (Geometry.Operator.gradientFun g f x) (Geometry.Operator.gradientFun g h x)
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  rw [integral_conformalMetric_eq_integral_smul_exp]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  dsimp only
  rw [Geometry.Operator.inner_gradientFun_conformalMetric]
  change Real.exp ((Module.finrank Real E : Real) * u x) *
      (Real.exp (-(2 * u x)) * _) = _
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem integral_inner_gradientFun_conformalMetric_of_finrank_eq_two
    [T2Space M] [SigmaCompactSpace M]
    (hn : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (u : C^∞⟮I, M; Real⟯) (f h : M → Real) :
    (∫ x, (conformalMetric g u).inner x
        (Geometry.Operator.gradientFun (conformalMetric g u) f x)
        (Geometry.Operator.gradientFun (conformalMetric g u) h x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (conformalMetric g u)) =
      ∫ x, g.inner x (Geometry.Operator.gradientFun g f x) (Geometry.Operator.gradientFun g h x)
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  rw [integral_inner_gradientFun_conformalMetric]
  simp only [hn, Nat.cast_ofNat, sub_self, zero_mul, Real.exp_zero, one_mul]

end DifferentialGeometry.Integral.Measure
