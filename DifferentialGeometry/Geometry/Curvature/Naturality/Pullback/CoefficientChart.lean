import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientField
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ChartBridge
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.PartialDiffeomorph
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound
import DifferentialGeometry.Bundle.TangentOpenRestriction
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients

set_option autoImplicit false
noncomputable section
open Set Filter Topology Manifold Metric
open scoped ContDiff Manifold
open DifferentialGeometry.Analysis (jet2 jetRm04 coefficientGram coefficientRm04
  coefficientGram_apply contDiffOn_coefficientGram jet2_congr_of_eventuallyEq
  jetRm04_eq_sectional_order)
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis chartBasisVecFiber)
namespace DifferentialGeometry.Geometry.Curvature

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem sectionalCurvatureNumerator_eq_jetRm04
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (α : M) (v w : TangentSpace I α)
    (hy : extChartAt I α α ∈ interior (extChartAt I α).target)
    (hG : DifferentiableAt ℝ (chartGramPi g α) (extChartAt I α α))
    (hG1 : ∀ᶠ y in 𝓝 (extChartAt I α α), DifferentiableAt ℝ (chartGramPi g α) y)
    (hG2 : DifferentiableAt ℝ (fun y => fderiv ℝ (chartGramPi g α) y) (extChartAt I α α)) :
    DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator g α v w =
      jetRm04 (jet2 (chartGramPi g α) (extChartAt I α α)) v w w v := by
  have hlow (i j k l : Fin (Module.finrank ℝ E)) :
      DifferentialGeometry.Geometry.Riemannian.chartRiemannLower g α i j k l (extChartAt I α α) =
        ∑ m, (jet2 (chartGramPi g α) (extChartAt I α α)).1 l m *
          DifferentialGeometry.Analysis.jetRiemann (chartModelBasis E)
            (jet2 (chartGramPi g α) (extChartAt I α α)) i j k m := by
    refine (DifferentialGeometry.Geometry.Riemannian.chartRiemannLower_def g α i j k l _).trans ?_
    refine Finset.sum_congr rfl (fun m _ => ?_)
    exact congrArg (HMul.hMul _) (chartRiemann_eq_jet g α hy hG hG1 hG2 i j k m)
  have h1 := jetRm04_eq_sectional_order (jet2 (chartGramPi g α) (extChartAt I α α)) v w
  have h2 := DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_def g α v w
  refine h2.trans (Eq.trans ?_ h1.symm)
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
  exact congrArg (HMul.hMul _) (hlow i j k l)

private theorem chartBasisVecFiber_opens_model (U : TopologicalSpace.Opens E) (p x : U)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := 𝓘(ℝ, E)) p i x = chartModelBasis E i := by
  let _ : Nonempty U := ⟨p⟩
  have hx : (x : E) ∈ (chartAt E (p : E)).source := by
    rw [chartAt_self_eq]
    exact Set.mem_univ _
  have hxU : x ∈ (chartAt E p).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hx
  change (trivializationAt E (TangentSpace 𝓘(ℝ, E) (M := U)) p).symmL ℝ x
    (chartModelBasis E i) = chartModelBasis E i
  rw [TangentBundle.symmL_trivializationAt_eq_core (I := 𝓘(ℝ, E)) hxU,
    DifferentialGeometry.tangentCoordChange_opens (I := 𝓘(ℝ, E)) p x x hx,
    TangentBundle.coordChange_model_space]
  rfl

omit [FiniteDimensional ℝ E] in
private theorem extChartAt_opens_model_symm (U : TopologicalSpace.Opens E) (α : U) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) α).target) :
    (((extChartAt 𝓘(ℝ, E) α).symm y : U) : E) = y := by
  have h1 : extChartAt 𝓘(ℝ, E) α ((extChartAt 𝓘(ℝ, E) α).symm y) =
      (((extChartAt 𝓘(ℝ, E) α).symm y : U) : E) := rfl
  exact h1.symm.trans ((extChartAt 𝓘(ℝ, E) α).right_inv hy)

end

section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

private def sourceOpens (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) :
    TopologicalSpace.Opens E :=
  ⟨Φ.source, Φ.open_source⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
private theorem sourceOpens_subset (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) :
    ((sourceOpens Φ : TopologicalSpace.Opens E) : Set E) ⊆ Φ.source :=
  fun _ hx => hx

private def chartPullbackMetric (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) :
    SmoothRiemannianMetric 𝓘(ℝ, E) (sourceOpens Φ) :=
  DifferentialGeometry.Diffeomorph.pullbackMetricCross
    (g.restrictOpen ⟨(Φ : E → M) '' ((sourceOpens Φ : TopologicalSpace.Opens E) : Set E),
      DifferentialGeometry.image_opens_isOpen Φ (sourceOpens_subset Φ)⟩)
    (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ (sourceOpens_subset Φ))

private theorem chartPullbackMetric_inner (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) (z : sourceOpens Φ) (v w : E) :
    (chartPullbackMetric g Φ).inner z v w =
      DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ (z : E) v w := by
  have h := DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner
    (g.restrictOpen ⟨(Φ : E → M) '' ((sourceOpens Φ : TopologicalSpace.Opens E) : Set E),
      DifferentialGeometry.image_opens_isOpen Φ (sourceOpens_subset Φ)⟩)
    (DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ (sourceOpens_subset Φ)) z v w
  have hv := DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ
    (sourceOpens_subset Φ) z v
  have hw := DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ
    (sourceOpens_subset Φ) z w
  exact h.trans (congrArg₂ (fun v' w' => g.inner (Φ (z : E)) v' w') hv hw)

private theorem chartGramMatrix_chartPullbackMetric (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) (α z : sourceOpens Φ)
    (l m : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (chartPullbackMetric g Φ) α z l m =
      DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ (z : E)
        (chartModelBasis E l) (chartModelBasis E m) := by
  have hl := chartBasisVecFiber_opens_model (sourceOpens Φ) α z l
  have hm := chartBasisVecFiber_opens_model (sourceOpens Φ) α z m
  rw [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, hl, hm]
  exact chartPullbackMetric_inner g Φ z _ _

private theorem chartGramPi_chartPullbackMetric (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) (α : sourceOpens Φ) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) α).target) :
    chartGramPi (chartPullbackMetric g Φ) α y =
      coefficientGram (DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ) y := by
  funext l m
  rw [chartGramPi_apply, DifferentialGeometry.Geometry.Operator.chartGramOnE_def,
    chartGramMatrix_chartPullbackMetric g Φ α _ l m, extChartAt_opens_model_symm _ α hy,
    coefficientGram_apply]

private theorem metricRm04StandardAt_chartPullbackMetric
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞)
    (α : sourceOpens Φ) (a b c d : E) :
    metricRm04StandardAt (chartPullbackMetric g Φ) α a b c d =
      metricRm04StandardAt g (Φ (α : E)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (α : E) a)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (α : E) b) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (α : E) c)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (α : E) d) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold 𝓘(ℝ, E) 1 M := IsManifold.of_le (n := ∞) (by decide)
  let V : TopologicalSpace.Opens M :=
    ⟨(Φ : E → M) '' ((sourceOpens Φ : TopologicalSpace.Opens E) : Set E),
      DifferentialGeometry.image_opens_isOpen Φ (sourceOpens_subset Φ)⟩
  let Ψ := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ (sourceOpens_subset Φ)
  have h1 := metricRm04Standard_pullbackCross (g.restrictOpen V) Ψ α a b c d
  have h2 := metricRm04StandardAt_restrictOpen g V (Ψ α) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ α a)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ α b) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ α c)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ α d)
  have ha := (DifferentialGeometry.mfderiv_subtype_val_apply (I := 𝓘(ℝ, E)) V (Ψ α)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ α a)).trans
      (DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ (sourceOpens_subset Φ) α a)
  have hb := (DifferentialGeometry.mfderiv_subtype_val_apply (I := 𝓘(ℝ, E)) V (Ψ α)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ α b)).trans
      (DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ (sourceOpens_subset Φ) α b)
  have hc := (DifferentialGeometry.mfderiv_subtype_val_apply (I := 𝓘(ℝ, E)) V (Ψ α)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ α c)).trans
      (DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ (sourceOpens_subset Φ) α c)
  have hd := (DifferentialGeometry.mfderiv_subtype_val_apply (I := 𝓘(ℝ, E)) V (Ψ α)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ α d)).trans
      (DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ (sourceOpens_subset Φ) α d)
  have e : ∀ X X' Y Y' Z Z' W W' : E, X = X' → Y = Y' → Z = Z' → W = W' →
      metricRm04StandardAt g (Φ (α : E)) X Y Z W =
        metricRm04StandardAt g (Φ (α : E)) X' Y' Z' W' := by
    intro X X' Y Y' Z Z' W W' hX hY hZ hW
    subst hX hY hZ hW
    rfl
  exact h1.trans (h2.trans (e _ _ _ _ _ _ _ _ ha hb hc hd))

private theorem sectionalCurvatureNumerator_chartPullbackMetric
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞)
    {w : E} (hw : w ∈ Φ.source) (v u : E) :
    DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator
        (chartPullbackMetric g Φ) (⟨w, hw⟩ : sourceOpens Φ) v u =
      coefficientRm04 (DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ) w v u u v := by
  have htgt : (extChartAt 𝓘(ℝ, E) (⟨w, hw⟩ : sourceOpens Φ)).target ∈ 𝓝 w :=
    extChartAt_target_mem_nhds (I := 𝓘(ℝ, E)) (⟨w, hw⟩ : sourceOpens Φ)
  have hev : chartGramPi (chartPullbackMetric g Φ) (⟨w, hw⟩ : sourceOpens Φ) =ᶠ[𝓝 w]
      coefficientGram (DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ) := by
    filter_upwards [htgt] with y hy
    exact chartGramPi_chartPullbackMetric g Φ _ hy
  have hBsrc : ContDiffOn ℝ 2 (DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ)
      Φ.source :=
    (DifferentialGeometry.Geometry.contDiffOn_pullback_metric_coefficients g Φ.open_source
      Φ.contMDiffOn).of_le ENat.LEInfty.out
  have hcgU : ContDiffOn ℝ 2
      (coefficientGram (DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ))
      Φ.source := contDiffOn_coefficientGram hBsrc
  have hcg : ContDiffAt ℝ 2
      (coefficientGram (DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ)) w :=
    hcgU.contDiffAt (Φ.open_source.mem_nhds hw)
  have hint : w ∈ interior (extChartAt 𝓘(ℝ, E) (⟨w, hw⟩ : sourceOpens Φ)).target :=
    mem_interior_iff_mem_nhds.mpr htgt
  have hG : DifferentiableAt ℝ (chartGramPi (chartPullbackMetric g Φ)
      (⟨w, hw⟩ : sourceOpens Φ)) w :=
    (hcg.differentiableAt (by norm_num)).congr_of_eventuallyEq hev
  have hG1 : ∀ᶠ y in 𝓝 w, DifferentiableAt ℝ (chartGramPi (chartPullbackMetric g Φ)
      (⟨w, hw⟩ : sourceOpens Φ)) y := by
    filter_upwards [hev.eventuallyEq_nhds, Φ.open_source.mem_nhds hw] with y hy hys
    exact ((hcgU.contDiffAt (Φ.open_source.mem_nhds hys)).differentiableAt
      (by norm_num)).congr_of_eventuallyEq hy
  have hev1 : (fun y => fderiv ℝ (chartGramPi (chartPullbackMetric g Φ)
      (⟨w, hw⟩ : sourceOpens Φ)) y) =ᶠ[𝓝 w]
      (fun y => fderiv ℝ
        (coefficientGram (DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ)) y) :=
    hev.eventuallyEq_nhds.mono fun y hy => hy.fderiv_eq
  have hG2 : DifferentiableAt ℝ (fun y => fderiv ℝ (chartGramPi (chartPullbackMetric g Φ)
      (⟨w, hw⟩ : sourceOpens Φ)) y) w :=
    ((hcg.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).congr_of_eventuallyEq hev1
  have hjet : jet2 (chartGramPi (chartPullbackMetric g Φ) (⟨w, hw⟩ : sourceOpens Φ)) w =
      jet2 (coefficientGram (DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ)) w :=
    jet2_congr_of_eventuallyEq hev
  have hsn := sectionalCurvatureNumerator_eq_jetRm04 (chartPullbackMetric g Φ)
    (⟨w, hw⟩ : sourceOpens Φ) v u hint hG hG1 hG2
  exact hsn.trans (congrArg (fun p => jetRm04 p v u u v) hjet)

theorem metricRm04StandardAt_partialDiffeomorph_eq_coefficientRm04
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞)
    {w : E} (hw : w ∈ Φ.source) (v u : E) :
    metricRm04StandardAt g (Φ w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ w v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ w u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ w u)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ w v) =
      coefficientRm04 (DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ) w v u u v := by
  have h1 := metricRm04StandardAt_chartPullbackMetric g Φ (⟨w, hw⟩ : sourceOpens Φ) v u u v
  have h2 :=
    DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_eq_metricRm04StandardAt
      (chartPullbackMetric g Φ) (⟨w, hw⟩ : sourceOpens Φ) v u
  have h3 := sectionalCurvatureNumerator_chartPullbackMetric g Φ hw v u
  exact h1.symm.trans (h2.symm.trans h3)

theorem coefficientRm04_lower_bound_of_sectionalBoundedBelowAt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞)
    {w : E} (hw : w ∈ Φ.source) {κ : ℝ}
    (hsec : DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt g (Φ w) κ)
    (v u : E) :
    κ * (DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ w v v *
        DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ w u u -
        (DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ w v u) ^ 2) ≤
      coefficientRm04 (DifferentialGeometry.Geometry.pullbackMetricCoefficients g Φ) w v u u v := by
  rw [← metricRm04StandardAt_partialDiffeomorph_eq_coefficientRm04 g Φ hw v u]
  exact hsec (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ w v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ w u)

end

end DifferentialGeometry.Geometry.Curvature
