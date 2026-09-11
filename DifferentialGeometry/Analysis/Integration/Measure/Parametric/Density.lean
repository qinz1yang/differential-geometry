import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Matrix

namespace DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem paramGramMatrix_eq_mul
    (g : SmoothRiemannianMetric I M)
    (f : E → M) {x : E} (hf : MDifferentiableAt (modelWithCornersSelf ℝ E) I f x)
    (y₀ : M) (hy : f x ∈ (trivializationAt E (TangentSpace I) y₀).baseSet) :
    paramGramMatrix (I := I) g f x =
      (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
        (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap)ᵀ *
      chartGramMatrix g y₀ (f x) *
      LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
        (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap := by
  let J : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
      (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap
  have hmul :
      (Matrix.of fun i j =>
          g.inner (f x)
            (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) i))
            (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) j))) =
        Jᵀ * chartGramMatrix g y₀ (f x) * J := by
    ext i j
    have hsum :
        g.inner (f x)
            (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) i))
            (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) j)) =
          ∑ k, ∑ l, J k i * J l j * chartGramMatrix g y₀ (f x) k l := by
      rw [mfderiv_chartModelBasis_eq_sum (I := I) f hf y₀ hy i,
        mfderiv_chartModelBasis_eq_sum (I := I) f hf y₀ hy j]
      have hL :
          g.inner (f x)
              (∑ k, J k i • chartBasisVecFiber (I := I) y₀ k (f x)) =
            ∑ k, J k i •
              g.inner (f x) (chartBasisVecFiber (I := I) y₀ k (f x)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [map_smul]
      rw [hL, sum_apply]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [smul_apply]
      have hR :
          g.inner (f x) (chartBasisVecFiber (I := I) y₀ k (f x))
              (∑ l, J l j • chartBasisVecFiber (I := I) y₀ l (f x)) =
            ∑ l, J l j *
              g.inner (f x) (chartBasisVecFiber (I := I) y₀ k (f x))
                (chartBasisVecFiber (I := I) y₀ l (f x)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [map_smul, smul_eq_mul]
      rw [hR, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [chartGramMatrix_apply]
      ring
    rw [Matrix.of_apply, hsum]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  exact hmul

theorem paramGramMatrix_det_eq_sq_det_mul
    (g : SmoothRiemannianMetric I M)
    (f : E → M) {x : E} (hf : MDifferentiableAt (modelWithCornersSelf ℝ E) I f x)
    (y₀ : M) (hy : f x ∈ (trivializationAt E (TangentSpace I) y₀).baseSet) :
    (paramGramMatrix (I := I) g f x).det =
      (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).det ^ 2 *
        (chartGramMatrix g y₀ (f x)).det := by
  rw [paramGramMatrix_eq_mul (I := I) g f hf y₀ hy,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix]
  ring

theorem paramDensity_eq_abs_det_mul_chartDensity_of_mdifferentiableAt
    (g : SmoothRiemannianMetric I M)
    (f : E → M) {x : E} (hf : MDifferentiableAt (modelWithCornersSelf ℝ E) I f x)
    (y₀ : M) (hy : f x ∈ (trivializationAt E (TangentSpace I) y₀).baseSet) :
    paramDensity (I := I) g f x =
      |(fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).det| *
        chartDensity g y₀ (f x) := by
  rw [paramDensity, paramGramMatrix_det_eq_sq_det_mul (I := I) g f hf y₀ hy]
  unfold chartDensity
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

omit [Module.Finite ℝ E] in
private lemma contDiffOn_extChartAt_comp
    {f : E → M} {U s : Set E} (hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f U)
    (hsU : s ⊆ U) (y₀ : M) (hs_chart : ∀ x ∈ s, f x ∈ (chartAt H y₀).source) :
    ContDiffOn ℝ 1 (fun x : E => extChartAt I y₀ (f x)) s := by
  have hf' : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f s := hf.mono hsU
  have hchart : ContMDiffOn I (modelWithCornersSelf ℝ E) 1 (extChartAt I y₀) (chartAt H y₀).source :=
    contMDiffOn_extChartAt (I := I) (x := y₀) (n := 1)
  have hcomp : ContMDiffOn (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) 1
      ((extChartAt I y₀) ∘ f) s :=
    hchart.comp hf' (fun x hx => hs_chart x hx)
  exact contMDiffOn_iff_contDiffOn.mp hcomp

private lemma continuousOn_paramDensity_on_chart
    (g : SmoothRiemannianMetric I M) {f : E → M} {U s : Set E}
    (hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f U) (hsU : s ⊆ U)
    (hs_open : IsOpen s) (y₀ : M)
    (hs_chart : ∀ x ∈ s,
      f x ∈ (trivializationAt E (TangentSpace I) y₀).baseSet) :
    ContinuousOn (paramDensity (I := I) g f) s := by
  have hcoord : ContDiffOn ℝ 1 (fun x : E => extChartAt I y₀ (f x)) s :=
    contDiffOn_extChartAt_comp (I := I) hf hsU y₀ (fun x hx => by
      simpa only [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hs_chart x hx)
  have hderiv : ContinuousOn
      (fun x : E => fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x) s :=
    hcoord.continuousOn_fderiv_of_isOpen hs_open le_rfl
  have hdet : ContinuousOn
      (fun x : E => |(fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).det|) s :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn hderiv).abs
  have hf_cont : ContinuousOn f s := (hf.mono hsU).continuousOn
  have hdensity : ContinuousOn (fun x => chartDensity g y₀ (f x)) s :=
    (chartDensity_contMDiffOn (I := I) g y₀).continuousOn.comp hf_cont hs_chart
  refine (hdensity.mul hdet).congr (fun x hx => ?_)
  have hmdiff : MDifferentiableAt (modelWithCornersSelf ℝ E) I f x :=
    (((hf.mono hsU) x hx).contMDiffAt (hs_open.mem_nhds hx)).mdifferentiableAt
      (by norm_num)
  exact (paramDensity_eq_abs_det_mul_chartDensity_of_mdifferentiableAt (I := I) g f hmdiff y₀
    (hs_chart x hx)).trans (mul_comm _ _)

lemma paramDensity_continuousOn_chart
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_open : IsOpen s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContinuousOn (paramDensity (I := I) g Ψ) s := by
  exact continuousOn_paramDensity_on_chart (I := I) g Ψ.contMDiffOn_toFun
    hs_source hs_open x₀ hs_chart

theorem continuousOn_paramDensity
    (g : SmoothRiemannianMetric I M) {f : E → M} {U : Set E}
    (hU : IsOpen U) (hf : ContMDiffOn (modelWithCornersSelf ℝ E) I 1 f U) :
    ContinuousOn (paramDensity (I := I) g f) U := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_continuousAt]
  intro x
  let y₀ : M := f x
  let V : Set E := U ∩ f ⁻¹' (chartAt H y₀).source
  have hVopen : IsOpen V := by
    dsimp only [V]
    exact hf.continuousOn.isOpen_inter_preimage hU (chartAt H y₀).open_source
  have hVU : V ⊆ U := by
    dsimp only [V]
    exact inter_subset_left
  have hVchart : ∀ z ∈ V,
      f z ∈ (trivializationAt E (TangentSpace I) y₀).baseSet := by
    intro z hz
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hz.2
  have hxV : (x : E) ∈ V := by
    exact ⟨x.2, mem_chart_source H (f x)⟩
  have hcontV : ContinuousOn (paramDensity (I := I) g f) V :=
    continuousOn_paramDensity_on_chart (I := I) g hf hVU hVopen y₀ hVchart
  exact (hcontV.continuousAt (hVopen.mem_nhds hxV)).comp
    continuous_subtype_val.continuousAt

end DifferentialGeometry.Integral.Measure
