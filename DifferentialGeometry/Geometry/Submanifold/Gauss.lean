import DifferentialGeometry.Geometry.Connection.ConnectionForm.Curvature
import DifferentialGeometry.Geometry.Curvature.Coordinates.ChristoffelContraction
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.MetricCompatibility
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import Batteries.Tactic.OpenPrivate

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Integral.DivergenceTheorem

open private chartConnectionBilin chartConnectionBilin_apply
  from DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Koszul
open private chartMetricBilin_eq_sum
  from DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.MetricCompatibility

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem chartConnectionBilin_differentiableAt
    (g : SmoothRiemannianMetric I M) (a : M) {z : E}
    (hz : z ∈ interior (extChartAt I a).target) :
    DifferentiableAt ℝ (chartConnectionBilin g a) z := by
  unfold chartConnectionBilin
  refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
  have hsum : DifferentiableAt ℝ (fun y => ∑ k : Fin (Module.finrank ℝ E),
      chartChristoffel g a i j k y • chartModelBasis E k) z := by
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact (((chartChristoffel_contDiffOn_interior g a i j k).contDiffAt
      (isOpen_interior.mem_nhds hz)).differentiableAt (by simp)).smul_const _
  exact (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] E) (chartCoordCLM E i)).differentiableAt.comp z
    ((ContinuousLinearMap.smulRightL ℝ E E (chartCoordCLM E j)).differentiableAt.comp z hsum)

private theorem chartMetricBilin_differentiableAt
    (g : SmoothRiemannianMetric I M) (a : M) {z : E}
    (hz : z ∈ interior (extChartAt I a).target) :
    DifferentiableAt ℝ (chartMetricBilin g a) z := by
  have he : chartMetricBilin g a = fun y =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartGramOnE g a i j y • (chartCoordCLM E i).smulRight (chartCoordCLM E j) := by
    funext y
    ext u v
    simp only [chartMetricBilin_eq_sum, sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, chartCoordCLM_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [chartCoord, Module.Basis.equivFun_apply, mul_assoc]
  rw [he]
  refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
  exact (chartGramOnE_differentiableAt_int g a i j hz).smul_const _

private theorem chartMetricBilin_fderiv [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (a : M) {z : E}
    (hz : z ∈ (extChartAt I a).target) (X u v : E) :
    fderiv ℝ (chartMetricBilin g a) z X u v =
      chartMetricBilin g a z (chartConnectionBilin g a z X u) v +
        chartMetricBilin g a z u (chartConnectionBilin g a z X v) := by
  have hG := chartMetricBilin_differentiableAt g a
    (by rwa [(isOpen_extChartAt_target a).interior_eq])
  let c : ℝ → E := fun t => z + t • X
  have hc : HasDerivAt c X 0 := by
    simpa only [c, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add z
  have hc0 : c 0 = z := by simp [c]
  have hgAt : HasFDerivAt (chartMetricBilin g a) (fderiv ℝ (chartMetricBilin g a) z) (c 0) := by
    rw [hc0]
    exact hG.hasFDerivAt
  have hd := ((hgAt.comp_hasDerivAt 0 hc).clm_apply
    (hasDerivAt_const 0 u)).clm_apply (hasDerivAt_const 0 v)
  have hm := chartMetricBilin_hasDerivAt g a hc (hasDerivAt_const 0 u)
    (hasDerivAt_const 0 v) (by simpa only [hc0] using hz)
  have he := hd.unique hm
  simpa only [Function.comp_apply, hc0, map_zero, add_zero, zero_add,
    chartConnectionBilin_apply] using he

omit [FiniteDimensional ℝ E] in
private theorem chartMetricBilin_symm
    (g : SmoothRiemannianMetric I M) (a : M) (z u v : E) :
    chartMetricBilin g a z u v = chartMetricBilin g a z v u :=
  g.symm _ _ _

private theorem chartConnectionBilin_symm
    (g : SmoothRiemannianMetric I M) (a : M) (z u v : E) :
    chartConnectionBilin g a z u v = chartConnectionBilin g a z v u := by
  rw [chartConnectionBilin_apply, chartConnectionBilin_apply]
  exact chartChristoffelContraction_symm g a u v z

private theorem chartConnectionBilin_fderiv_apply
    (g : SmoothRiemannianMetric I M) (a : M) {z : E}
    (hz : z ∈ interior (extChartAt I a).target) (X Y Z : E) :
    fderiv ℝ (chartConnectionBilin g a) z X Y Z =
      fderiv ℝ (chartChristoffelContraction g a Y Z) z X := by
  have hA := chartConnectionBilin_differentiableAt g a hz
  have hd := ((hA.hasFDerivAt.clm_apply (hasFDerivAt_const Y z)).clm_apply
    (hasFDerivAt_const Z z)).fderiv
  have hf : (fun y => chartConnectionBilin g a y Y Z) =
      chartChristoffelContraction g a Y Z := funext fun y => chartConnectionBilin_apply g a y Y Z
  rw [hf] at hd
  simpa only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add, add_zero] using (congrArg (fun L => L X) hd).symm

private theorem connectionFormCurvature_chartConnectionBilin [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (a : M) (X Y Z : E) :
    connectionFormCurvature (chartConnectionBilin g a) (extChartAt I a a) X Y Z =
      centeredChartTangentEquiv (I := I) a
        (chartRiemannCLM g a ((centeredChartTangentEquiv (I := I) a).symm X)
          ((centeredChartTangentEquiv (I := I) a).symm Y)
          ((centeredChartTangentEquiv (I := I) a).symm Z)) := by
  have ha : extChartAt I a a ∈ interior (extChartAt I a).target := by
    rw [(isOpen_extChartAt_target a).interior_eq]
    exact mem_extChartAt_target a
  rw [chartRiemannCLM_model_eq_contractions, connectionFormCurvature,
    chartConnectionBilin_fderiv_apply g a ha X Y Z,
    chartConnectionBilin_fderiv_apply g a ha Y X Z]
  simp only [chartConnectionBilin_apply]
  rw [show chartChristoffelContraction g a Y Z = chartChristoffelContraction g a Z Y from
      funext fun z => chartChristoffelContraction_symm g a Y Z z,
    show chartChristoffelContraction g a X Z = chartChristoffelContraction g a Z X from
      funext fun z => chartChristoffelContraction_symm g a X Z z]

omit [FiniteDimensional ℝ E] in
private theorem chartMetricBilin_center
    (g : SmoothRiemannianMetric I M) (a : M) (u v : TangentSpace I a) :
    chartMetricBilin g a (extChartAt I a a)
        (tangentSpaceModelContinuousLinearEquiv (I := I) a u)
        (tangentSpaceModelContinuousLinearEquiv (I := I) a v) = g.inner a u v := by
  have ht : (trivToE (I := I) a a : TangentSpace I a →L[ℝ] E) =
      (tangentSpaceModelContinuousLinearEquiv (I := I) a).toContinuousLinearMap := by
    have h := TangentBundle.continuousLinearMapAt_trivializationAt
      (𝕜 := ℝ) (I := I) (x₀ := a) (x := a) (mem_chart_source H a)
    rw [show (trivToE (I := I) a a : TangentSpace I a →L[ℝ] E) =
      (trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ a from rfl]
    rw [h]
    exact mfderiv_extChartAt_self (I := I) (x := a)
  simp_rw [← show ∀ w : TangentSpace I a,
    trivToE (I := I) a a w = tangentSpaceModelContinuousLinearEquiv (I := I) a w from
      fun w => DFunLike.congr_fun ht w]
  exact chartMetricBilin_trivToE g a a (mem_chart_source H a) u v

private theorem metricRm04StandardAt_eq_connectionFormCurvature [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (a : M) (X Y Z W : TangentSpace I a) :
    DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt g a X Y Z W =
      chartMetricBilin g a (extChartAt I a a)
        (connectionFormCurvature (chartConnectionBilin g a) (extChartAt I a a)
          (tangentSpaceModelContinuousLinearEquiv (I := I) a X)
          (tangentSpaceModelContinuousLinearEquiv (I := I) a Y)
          (tangentSpaceModelContinuousLinearEquiv (I := I) a Z))
        (tangentSpaceModelContinuousLinearEquiv (I := I) a W) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [connectionFormCurvature_chartConnectionBilin]
  have hX : (centeredChartTangentEquiv (I := I) a).symm
      (tangentSpaceModelContinuousLinearEquiv (I := I) a X) = X := by
    rw [← centeredChartTangentEquiv_apply (I := I) a X, ContinuousLinearEquiv.symm_apply_apply]
  have hY : (centeredChartTangentEquiv (I := I) a).symm
      (tangentSpaceModelContinuousLinearEquiv (I := I) a Y) = Y := by
    rw [← centeredChartTangentEquiv_apply (I := I) a Y, ContinuousLinearEquiv.symm_apply_apply]
  have hZ : (centeredChartTangentEquiv (I := I) a).symm
      (tangentSpaceModelContinuousLinearEquiv (I := I) a Z) = Z := by
    rw [← centeredChartTangentEquiv_apply (I := I) a Z, ContinuousLinearEquiv.symm_apply_apply]
  rw [hX, hY, hZ, centeredChartTangentEquiv_apply, chartMetricBilin_center,
    metricRm04StandardAt_eq_chartRiemannCLM]
  exact g.symm a W _

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open private chartConnectionBilin chartConnectionBilin_apply
  from DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Koszul
open private gaussDefectModelValue secondFundamentalFormAmbientAt_apply
  from DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem chart_gauss_equation_of_inner_map
    {gN : SmoothRiemannianMetric IN N} {gM : SmoothRiemannianMetric I M} {f : N → M}
    (hf : ContMDiff IN I ∞ f)
    (hmetric : ∀ (x : N) (u v : TangentSpace IN x),
      gM.inner (f x) (mfderiv IN I f x u) (mfderiv IN I f x v) = gN.inner x u v)
    (a : N) (X Y Z W : EN) :
    let F := writtenInExtChartAt IN I a f
    let z := extChartAt IN a a
    let A := chartConnectionBilin gN a
    let C := chartConnectionBilin gM (f a)
    let B := bundleMapCovDeriv A (pullbackConnectionForm C F) (fderiv ℝ F) z
    chartMetricBilin gN a z (connectionFormCurvature A z X Y Z) W =
      chartMetricBilin gM (f a) (F z)
        (connectionFormCurvature C (F z) (fderiv ℝ F z X) (fderiv ℝ F z Y)
          (fderiv ℝ F z Z)) (fderiv ℝ F z W) +
        chartMetricBilin gM (f a) (F z) (B X W) (B Y Z) -
        chartMetricBilin gM (f a) (F z) (B X Z) (B Y W) := by
  let F := writtenInExtChartAt IN I a f
  let z := extChartAt IN a a
  let A := chartConnectionBilin gN a
  let C := chartConnectionBilin gM (f a)
  let G := chartMetricBilin gM (f a)
  let K := chartMetricBilin gN a
  let P := pullbackConnectionForm C F
  have hF3 : ContDiffAt ℝ 3 F z := by
    have h := (contMDiffAt_iff.mp (hf.contMDiffAt (x := a))).2
    rw [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ] at h
    exact h.of_le (by decide : (3 : ℕ∞ω) ≤ ∞)
  have hF2 := hF3.of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)
  have hF1 := hF3.differentiableAt (by norm_num)
  have hFz : F z = extChartAt I (f a) (f a) := by
    simp only [F, z, writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv]
  have hz : z ∈ interior (extChartAt IN a).target := by
    rw [(isOpen_extChartAt_target a).interior_eq]
    exact mem_extChartAt_target a
  have hFzt : F z ∈ interior (extChartAt I (f a)).target := by
    rw [hFz, (isOpen_extChartAt_target (f a)).interior_eq]
    exact mem_extChartAt_target (f a)
  have hA : DifferentiableAt ℝ A z := chartConnectionBilin_differentiableAt gN a hz
  have hC : DifferentiableAt ℝ C (F z) := chartConnectionBilin_differentiableAt gM (f a) hFzt
  have hG : DifferentiableAt ℝ G (F z) := chartMetricBilin_differentiableAt gM (f a) hFzt
  have hJ : ContDiffAt ℝ 2 (fderiv ℝ F) z := hF3.fderiv_right (by norm_num)
  have hP : DifferentiableAt ℝ P z :=
    (hC.comp z hF1).clm_comp (hJ.differentiableAt (by norm_num))
  have hGP : DifferentiableAt ℝ (G ∘ F) z := hG.comp z hF1
  have hpull : ∀ᶠ y in 𝓝 z, ∀ u v, G (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) = K y u v :=
    chartMetricBilin_pullback_eventually_of_inner_map hf hmetric a
  have hcompat (y : EN) (hyF : DifferentiableAt ℝ F y)
      (hy : F y ∈ interior (extChartAt I (f a)).target) (U : EN) (u v : E) :
      fderiv ℝ (G ∘ F) y U u v =
        (G ∘ F) y (P y U u) v + (G ∘ F) y u (P y U v) := by
    rw [fderiv_comp y (chartMetricBilin_differentiableAt gM (f a) hy) hyF,
      ContinuousLinearMap.comp_apply]
    exact chartMetricBilin_fderiv gM (f a) (interior_subset hy) (fderiv ℝ F y U) u v
  have horth : ∀ᶠ y in 𝓝 z, ∀ U u v,
      (G ∘ F) y (bundleMapCovDeriv A P (fderiv ℝ F) y U u) (fderiv ℝ F y v) = 0 := by
    filter_upwards [hF2.eventually (by norm_num), isOpen_interior.mem_nhds hz,
      hF1.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hFzt),
      hpull.eventually_nhds] with y hyF hy hyTarget hmetricY
    intro U u v
    have hdf : DifferentiableAt ℝ (fderiv ℝ F) y :=
      (hyF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hfy := hyF.differentiableAt (by norm_num)
    exact bundleMapCovDeriv_orthogonal_of_symmetric hdf
      ((chartMetricBilin_differentiableAt gM (f a) hyTarget).comp y hfy)
      (chartMetricBilin_differentiableAt gN a hy)
      (chartMetricBilin_symm gM (f a) (F y)) (hcompat y hfy hyTarget)
      (chartMetricBilin_fderiv gN a (interior_subset hy)) hmetricY
      (bundleMapCovDeriv_fderiv_symmetric hyF (chartConnectionBilin_symm gN a y)
        (chartConnectionBilin_symm gM (f a) (F y))) U u v
  have hgauss := gauss_equation_connection_forms hA hP hJ hGP
    (chartMetricBilin_symm gM (f a) (F z)) (hcompat z hF1 hFzt) horth X Y Z W
  rw [show (G ∘ F) z = G (F z) from rfl, hpull.self_of_nhds] at hgauss
  rw [connectionFormCurvature_pullback hC hF2] at hgauss
  exact hgauss

theorem gauss_equation_of_inner_map [T2Space N] [T2Space M]
    {gN : SmoothRiemannianMetric IN N} {gM : SmoothRiemannianMetric I M} {f : N → M}
    (hf : ContMDiff IN I ∞ f)
    (hmetric : ∀ (x : N) (u v : TangentSpace IN x),
      gM.inner (f x) (mfderiv IN I f x u) (mfderiv IN I f x v) = gN.inner x u v)
    (a : N) (X Y Z W : TangentSpace IN a) :
    Curvature.metricRm04StandardAt gN a X Y Z W =
      Curvature.metricRm04StandardAt gM (f a)
        (mfderiv IN I f a X) (mfderiv IN I f a Y)
        (mfderiv IN I f a Z) (mfderiv IN I f a W) +
        gM.inner (f a) (secondFundamentalFormAmbientAt gN gM f a X W)
          (secondFundamentalFormAmbientAt gN gM f a Y Z) -
        gM.inner (f a) (secondFundamentalFormAmbientAt gN gM f a X Z)
          (secondFundamentalFormAmbientAt gN gM f a Y W) := by
  let F := writtenInExtChartAt IN I a f
  let z := extChartAt IN a a
  let A := chartConnectionBilin gN a
  let C := chartConnectionBilin gM (f a)
  let B := bundleMapCovDeriv A (pullbackConnectionForm C F) (fderiv ℝ F) z
  let eN := tangentSpaceModelContinuousLinearEquiv (I := IN) a
  let eM := tangentSpaceModelContinuousLinearEquiv (I := I) (f a)
  have hFz : F z = extChartAt I (f a) (f a) := by
    simp only [F, z, writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv]
  have hdf : tangentLinearMapToModel (mfderiv IN I f a) = fderiv ℝ F z := by
    ext u
    exact tangentLinearMapToModel_mfderiv_eq_fderiv_writtenInExtChartAt
      (hf.mdifferentiableAt (by simp)) u
  have hd (u : TangentSpace IN a) : fderiv ℝ F z (eN u) = eM (mfderiv IN I f a u) := by
    rw [← hdf, tangentLinearMapToModel_apply]
    simp only [eN, eM, ContinuousLinearEquiv.symm_apply_apply]
  have hB (u v : TangentSpace IN a) :
      B (eN u) (eN v) = eM (secondFundamentalFormAmbientAt gN gM f a u v) := by
    rw [secondFundamentalFormAmbientAt_apply]
    change B (eN u) (eN v) = gaussDefectModelValue gN gM f a (eN u) (eN v)
    simp only [B, bundleMapCovDeriv, pullbackConnectionForm, ContinuousLinearMap.comp_apply,
      gaussDefectModelValue, hdf, F, z, A, C, chartConnectionBilin_apply]
    rw [show writtenInExtChartAt IN I a f (extChartAt IN a a) =
      extChartAt I (f a) (f a) from hFz]
  have hgauss := chart_gauss_equation_of_inner_map hf hmetric a (eN X) (eN Y) (eN Z) (eN W)
  change chartMetricBilin gN a z (connectionFormCurvature A z (eN X) (eN Y) (eN Z)) (eN W) =
    chartMetricBilin gM (f a) (F z)
      (connectionFormCurvature C (F z) (fderiv ℝ F z (eN X)) (fderiv ℝ F z (eN Y))
        (fderiv ℝ F z (eN Z))) (fderiv ℝ F z (eN W)) +
      chartMetricBilin gM (f a) (F z) (B (eN X) (eN W)) (B (eN Y) (eN Z)) -
      chartMetricBilin gM (f a) (F z) (B (eN X) (eN Z)) (B (eN Y) (eN W)) at hgauss
  rw [hFz, hB X W, hB Y Z, hB X Z, hB Y W, hd X, hd Y, hd Z, hd W] at hgauss
  rw [metricRm04StandardAt_eq_connectionFormCurvature gN a X Y Z W,
    metricRm04StandardAt_eq_connectionFormCurvature gM (f a)]
  rw [chartMetricBilin_center, chartMetricBilin_center] at hgauss
  exact hgauss

end DifferentialGeometry.Geometry
