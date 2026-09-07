import DifferentialGeometry.Analysis.Integration.Measure.ParamEvaluation
import DifferentialGeometry.Geometry.Metric.PullbackCross
import Mathlib.Tactic.NormNum

namespace DifferentialGeometry.Integral.Measure

open Manifold Module Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace F := borel F
private local instance : BorelSpace F := ⟨rfl⟩

def chartModelEquiv (h : Module.finrank ℝ E = Module.finrank ℝ F) : E ≃L[ℝ] F :=
  ((chartModelBasis E).equiv (chartModelBasis F) (finCongr h)).toContinuousLinearEquiv

theorem chartModelEquiv_basis (h : Module.finrank ℝ E = Module.finrank ℝ F)
    (i : Fin (Module.finrank ℝ E)) :
    chartModelEquiv h (chartModelBasis E i) = chartModelBasis F (finCongr h i) := by
  exact (chartModelBasis E).equiv_apply i (chartModelBasis F) (finCongr h)

theorem chartModelEquiv_measurePreserving (h : Module.finrank ℝ E = Module.finrank ℝ F) :
    MeasurePreserving (chartModelEquiv h) (modelHaar (E := E)) (modelHaar (E := F)) := by
  refine ⟨(chartModelEquiv h).continuous.measurable, ?_⟩
  rw [modelHaar, Basis.map_addHaar]
  change ((chartModelBasis E).map
    ((chartModelBasis E).equiv (chartModelBasis F) (finCongr h))).addHaar = _
  rw [Basis.map_equiv, Basis.addHaar_reindex]
  rfl

private def linearEquivPartialOne (e : E ≃L[ℝ] F) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F 1 where
  toPartialEquiv := e.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := e.contDiff.contMDiff.contMDiffOn
  contMDiffOn_invFun := e.symm.contDiff.contMDiff.contMDiffOn

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

private def diffeomorphPartialOne (Φ : M ≃ₘ⟮I, J⟯ N) : PartialDiffeomorph I J M N 1 where
  toPartialEquiv := Φ.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun x _ := (Φ.contMDiff x).of_le (by norm_num)
  contMDiffOn_invFun x _ := (Φ.symm.contMDiff x).of_le (by norm_num)

private theorem paramGramMatrix_pullback_trans [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    (h : Module.finrank ℝ E = Module.finrank ℝ F)
    {w : E} (hw : w ∈ Ψ.source) :
    paramGramMatrix (Diffeomorph.pullbackMetricCross g Φ) Ψ w =
      Matrix.reindex (finCongr h).symm (finCongr h).symm
        (paramGramMatrix g
          (((linearEquivPartialOne (chartModelEquiv h).symm).trans Ψ).trans
            (diffeomorphPartialOne Φ)) (chartModelEquiv h w)) := by
  let e := chartModelEquiv h
  have hΨ := (Ψ.contMDiffOn_toFun.mdifferentiableOn one_ne_zero w hw).mdifferentiableAt
    (Ψ.open_source.mem_nhds hw)
  have hΦ := (Φ.contMDiff (Ψ w)).mdifferentiableAt (by simp)
  have he : MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, E) e.symm :=
    (e.symm.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp)
  have hcomp : mfderiv 𝓘(ℝ, F) J
      (((linearEquivPartialOne e.symm).trans Ψ).trans (diffeomorphPartialOne Φ)) (e w) =
      (mfderiv I J Φ (Ψ w)).comp ((mfderiv 𝓘(ℝ, E) I Ψ w).comp
        (e.symm : F →L[ℝ] E)) := by
    change mfderiv 𝓘(ℝ, F) J (Φ ∘ Ψ ∘ e.symm) (e w) = _
    have hw' : e.symm (e w) = w := e.symm_apply_apply w
    have hΨ' : MDifferentiableAt 𝓘(ℝ, E) I Ψ (e.symm (e w)) := by
      simpa only [hw'] using hΨ
    rw [mfderiv_comp (e w) (by simpa only [Function.comp_apply, hw'] using hΦ)
      (hΨ'.comp (e w) (he (e w)))]
    rw [mfderiv_comp (e w) (by simpa only [hw'] using hΨ) (he (e w))]
    simp only [Function.comp_apply, mfderiv_eq_fderiv, e.symm.fderiv]
    rw [hw']
    rfl
  ext i j
  simp only [Matrix.reindex_apply, Equiv.symm_symm, paramGramMatrix_apply,
    Diffeomorph.pullbackMetricCross_inner]
  have hei : e.symm (chartModelBasis F (finCongr h i)) = chartModelBasis E i := by
    rw [← chartModelEquiv_basis h i]
    exact e.symm_apply_apply _
  have hej : e.symm (chartModelBasis F (finCongr h j)) = chartModelBasis E j := by
    rw [← chartModelEquiv_basis h j]
    exact e.symm_apply_apply _
  change g.inner (Φ (Ψ w)) _ _ = g.inner (Φ (Ψ (e.symm (e w))))
    (mfderiv 𝓘(ℝ, F) J
      (((linearEquivPartialOne e.symm).trans Ψ).trans (diffeomorphPartialOne Φ)) (e w)
      (chartModelBasis F (finCongr h i)))
    (mfderiv 𝓘(ℝ, F) J
      (((linearEquivPartialOne e.symm).trans Ψ).trans (diffeomorphPartialOne Φ)) (e w)
      (chartModelBasis F (finCongr h j)))
  rw [hcomp]
  change g.inner (Φ (Ψ w)) _ _ = g.inner (Φ (Ψ (e.symm (e w))))
    ((mfderiv I J Φ (Ψ w)) ((mfderiv 𝓘(ℝ, E) I Ψ w)
      (e.symm (chartModelBasis F (finCongr h i)))))
    ((mfderiv I J Φ (Ψ w)) ((mfderiv 𝓘(ℝ, E) I Ψ w)
      (e.symm (chartModelBasis F (finCongr h j)))))
  rw [hei, hej, e.symm_apply_apply]

private theorem paramDensity_pullback_trans [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    (h : Module.finrank ℝ E = Module.finrank ℝ F)
    {w : E} (hw : w ∈ Ψ.source) :
    paramDensity (Diffeomorph.pullbackMetricCross g Φ) Ψ w =
      paramDensity g
        (((linearEquivPartialOne (chartModelEquiv h).symm).trans Ψ).trans
          (diffeomorphPartialOne Φ)) (chartModelEquiv h w) := by
  rw [paramDensity_apply, paramDensity_apply, paramGramMatrix_pullback_trans g Φ Ψ h hw,
    Matrix.det_reindex_self]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

private def chartParam [I.Boundaryless] (x : M) :
    PartialDiffeomorph 𝓘(ℝ, E) I E M 1 where
  toFun := (extChartAt I x).symm
  invFun := extChartAt I x
  source := (extChartAt I x).target
  target := (extChartAt I x).source
  map_source' := fun {y} hy => (extChartAt I x).map_target hy
  map_target' := fun {y} hy => (extChartAt I x).map_source hy
  left_inv' := fun {y} hy => (extChartAt I x).right_inv hy
  right_inv' := fun {y} hy => (extChartAt I x).left_inv hy
  open_source := isOpen_extChartAt_target (I := I) x
  open_target := isOpen_extChartAt_source (I := I) x
  contMDiffOn_toFun := contMDiffOn_extChartAt_symm (I := I) (n := 1) x
  contMDiffOn_invFun := by
    simpa only [extChartAt_source] using
      contMDiffOn_extChartAt (I := I) (n := 1) (x := x)

private theorem volume_pullback_apply_of_subset_chart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space N] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (α : M) {A : Set M} (hA : MeasurableSet A)
    (hAc : A ⊆ (chartAt H α).source) :
    riemannianVolumeMeasure (I := I) (M := M) (Diffeomorph.pullbackMetricCross g Φ) A =
      Measure.map (Φ.symm : N → M) (riemannianVolumeMeasure (I := J) (M := N) g) A := by
  have hdim : Module.finrank ℝ E = Module.finrank ℝ F :=
    (Φ.mfderivToContinuousLinearEquiv (by simp) α).toLinearEquiv.finrank_eq
  let e := chartModelEquiv hdim
  let Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 := chartParam α
  let Θ : PartialDiffeomorph 𝓘(ℝ, F) J F N 1 :=
    ((linearEquivPartialOne e.symm).trans Ψ).trans (diffeomorphPartialOne Φ)
  let B : Set E := Ψ.symm '' A
  have hAt : A ⊆ Ψ.target := by
    simpa only [Ψ, chartParam, extChartAt_source] using hAc
  have hB : MeasurableSet B := measurableSet_symm_image_param Ψ hA hAt
  have hBs : B ⊆ Ψ.source := by
    rintro w ⟨x, hx, rfl⟩
    exact Ψ.toPartialEquiv.map_target (hAt hx)
  have heB : MeasurableSet (e '' B) := e.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hB
  have heBs : e '' B ⊆ Θ.source := by
    rintro _ ⟨w, hw, rfl⟩
    change (e w ∈ Set.univ ∧ e.symm (e w) ∈ Ψ.source) ∧ _
    exact ⟨⟨Set.mem_univ _, by simpa only [e.symm_apply_apply] using hBs hw⟩, Set.mem_univ _⟩
  have hΨB : Ψ '' B = A :=
    PartialEquiv.image_symm_image_of_subset_target Ψ.toPartialEquiv hAt
  have hΘB : Θ '' (e '' B) = Φ '' A := by
    rw [← hΨB]
    ext y
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨Ψ w, ⟨w, hw, rfl⟩, ?_⟩
      change Φ (Ψ w) = Φ (Ψ (e.symm (e w)))
      rw [e.symm_apply_apply]
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨e w, ⟨w, hw, rfl⟩, ?_⟩
      change Φ (Ψ (e.symm (e w))) = Φ (Ψ w)
      rw [e.symm_apply_apply]
  have hpull := riemannianVolumeMeasure_image_param_eq
    (Diffeomorph.pullbackMetricCross g Φ) Ψ hB hBs
  have htarget := riemannianVolumeMeasure_image_param_eq g Θ heB heBs
  rw [hΨB] at hpull
  rw [hΘB] at htarget
  calc
    riemannianVolumeMeasure (I := I) (M := M) (Diffeomorph.pullbackMetricCross g Φ) A =
        ∫⁻ w in B, ENNReal.ofReal (paramDensity (Diffeomorph.pullbackMetricCross g Φ) Ψ w)
          ∂(modelHaar (E := E)) := hpull
    _ = ∫⁻ w in B, ENNReal.ofReal (paramDensity g Θ (e w)) ∂(modelHaar (E := E)) := by
      apply setLIntegral_congr_fun hB
      intro w hw
      exact congrArg ENNReal.ofReal (paramDensity_pullback_trans g Φ Ψ hdim (hBs hw))
    _ = ∫⁻ z in e '' B, ENNReal.ofReal (paramDensity g Θ z) ∂(modelHaar (E := F)) :=
      (chartModelEquiv_measurePreserving hdim).setLIntegral_comp_emb
        e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
        (fun z => ENNReal.ofReal (paramDensity g Θ z)) B
    _ = riemannianVolumeMeasure (I := J) (M := N) g (Φ '' A) := htarget.symm
    _ = Measure.map (Φ.symm : N → M) (riemannianVolumeMeasure (I := J) (M := N) g) A := by
      rw [Measure.map_apply Φ.symm.continuous.measurable hA]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        change Φ.symm (Φ x) ∈ A
        rw [Φ.symm_apply_apply]
        exact hx
      · intro hy
        exact ⟨Φ.symm y, hy, Φ.apply_symm_apply y⟩

theorem riemannianVolumeMeasure_pullback_cross
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space N] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    riemannianVolumeMeasure (I := I) (M := M) (Diffeomorph.pullbackMetricCross g Φ) =
      Measure.map (Φ.symm : N → M) (riemannianVolumeMeasure (I := J) (M := N) g) := by
  classical
  obtain ⟨S, hSc, hS⟩ :
      ∃ S : Set M, S.Countable ∧ ⋃ (x : M) (_ : x ∈ S), (chartAt H x).source = Set.univ :=
    countable_cover_nhds_of_sigmaCompact (fun x : M => chart_source_mem_nhds H x)
  apply Measure.ext_of_biUnion_eq_univ hSc hS
  intro α _
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  exact volume_pullback_apply_of_subset_chart g Φ α
    (hA.inter (chartAt H α).open_source.measurableSet) Set.inter_subset_right

end

end DifferentialGeometry.Integral.Measure
