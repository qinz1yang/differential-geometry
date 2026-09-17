import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Submanifold.NormalBundle.Defs
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.MetricCompatibility
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.AlongCurve
import DifferentialGeometry.Topology.Manifold.CurveExtension
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold
open scoped ContDiff Manifold

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry

section PointwiseGaussDefect

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [NeZero (Module.finrank ℝ EN)]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [FiniteDimensional ℝ E] [IN.Boundaryless] [I.Boundaryless] in
private theorem trivToE_self_eq_tangentSpaceModel
    (x : M) :
    (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) =
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap := by
  classical
  have h := TangentBundle.continuousLinearMapAt_trivializationAt
    (𝕜 := ℝ) (I := I) (x₀ := x) (x := x) (mem_chart_source H x)
  rw [show (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) =
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x from rfl]
  rw [h]
  exact mfderiv_extChartAt_self (I := I) (x := x)

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [FiniteDimensional ℝ E] [IN.Boundaryless] [I.Boundaryless] in
private theorem trivToE_self_apply_tangentSpaceModel
    (x : M) (v : TangentSpace I x) :
    trivToE (I := I) x x v =
      tangentSpaceModelContinuousLinearEquiv (I := I) x v := by
  rw [trivToE_self_eq_tangentSpaceModel (I := I) x]
  rfl

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
theorem covariantAcceleration_chartCoord
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M) (t : ℝ)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞ gamma) :
    trivToE (I := I) (gamma t) (gamma t)
        (covariantAcceleration (I := I) g gamma t) =
      deriv (deriv (chartCurve (I := I) (gamma t) gamma)) t +
        chartChristoffelContraction (I := I) g (gamma t)
          (deriv (chartCurve (I := I) (gamma t) gamma) t)
          (deriv (chartCurve (I := I) (gamma t) gamma) t)
          (extChartAt I (gamma t) (gamma t)) := by
  classical
  let u : ℝ → E := chartCurve (I := I) (gamma t) gamma
  let V : ∀ s, TangentSpace I (gamma s) := fun s ↦
    (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s : ℝ →L[ℝ] _) (1 : ℝ)
  let rep : ℝ → E := chartRepAt (I := I) gamma V t
  have hsrc : {s : ℝ | gamma s ∈ (chartAt H (gamma t)).source} ∈ nhds t := by
    exact hgamma.continuous.continuousAt.preimage_mem_nhds
      ((chartAt H (gamma t)).open_source.mem_nhds
        (mem_chart_source H (gamma t)))
  have hrepEq : Filter.EventuallyEq (nhds t) rep (deriv u) := by
    filter_upwards [hsrc] with s hs
    dsimp only [rep]
    rw [chartRepAt_apply]
    have hcoord :=
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
        (I := I) (M := M) (γ := gamma) hgamma (gamma t) hs
    change
      (trivializationAt E (TangentSpace I) (gamma t)).continuousLinearMapAt
          ℝ (gamma s)
          ((mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s : ℝ →L[ℝ] _) 1) =
        deriv ((extChartAt I (gamma t)) ∘ gamma) s
    rw [← fderiv_apply_one_eq_deriv]
    exact hcoord
  have hrepSelf : rep t = deriv u t := hrepEq.eq_of_nhds
  have hrepDeriv : deriv rep t = deriv (deriv u) t := hrepEq.deriv_eq
  change trivToE (I := I) (gamma t) (gamma t)
      (covariantAcceleration (I := I) g gamma t) = _
  rw [covariantAcceleration_def]
  change trivToE (I := I) (gamma t) (gamma t)
      (covDerivAlong (I := I) g gamma V t) = _
  rw [covDerivAlong_chartCoord]
  change chartCovDerivAlong (I := I) g (gamma t) gamma rep t = _
  rw [chartCovDerivAlong_def, hrepDeriv, hrepSelf]
  rfl

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
theorem covariantAcceleration_modelCoord
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M) (t : ℝ)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞ gamma) :
    tangentSpaceModelContinuousLinearEquiv (I := I) (gamma t)
        (covariantAcceleration (I := I) g gamma t) =
      deriv (deriv (chartCurve (I := I) (gamma t) gamma)) t +
        chartChristoffelContraction (I := I) g (gamma t)
          (deriv (chartCurve (I := I) (gamma t) gamma) t)
          (deriv (chartCurve (I := I) (gamma t) gamma) t)
          (extChartAt I (gamma t) (gamma t)) := by
  rw [← trivToE_self_apply_tangentSpaceModel (I := I)]
  exact covariantAcceleration_chartCoord (I := I) g gamma t hgamma

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [FiniteDimensional ℝ EN] [IsManifold IN ∞ N]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless] in
theorem tangentLinearMapToModel_mfderiv_eq_fderiv_writtenInExtChartAt
    {iota : N → M} {x : N} (hiota : MDifferentiableAt IN I iota x)
    (v : EN) :
    tangentLinearMapToModel (mfderiv IN I iota x) v =
      fderiv ℝ (writtenInExtChartAt IN I x iota)
        (extChartAt IN x x) v := by
  rw [tangentLinearMapToModel_apply, hiota.mfderiv,
    ModelWithCorners.Boundaryless.range_eq_univ (I := IN),
    fderivWithin_univ]
  rfl

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [FiniteDimensional ℝ EN] [FiniteDimensional ℝ E]
    [IN.Boundaryless] [I.Boundaryless] in
private theorem deriv_deriv_comp
    {F : EN → E} {u : ℝ → EN} {t : ℝ}
    (hF : ContDiffAt ℝ 2 F (u t)) (hu : ContDiffAt ℝ 2 u t) :
    deriv (deriv (F ∘ u)) t =
      fderiv ℝ (fderiv ℝ F) (u t) (deriv u t) (deriv u t) +
        fderiv ℝ F (u t) (deriv (deriv u) t) := by
  have hchain := iteratedDeriv_vcomp_two hF hu
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate] at hchain
  simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply,
    iteratedFDeriv_two_apply] using hchain

private def gaussDefectModelValue
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) (x : N)
    (u v : EN) : E :=
  let F : EN → E := writtenInExtChartAt IN I x iota
  let xE : EN := extChartAt IN x x
  let iotaE : E := extChartAt I (iota x) (iota x)
  let diota : EN →L[ℝ] E :=
    tangentLinearMapToModel (mfderiv IN I iota x)
  fderiv ℝ (fderiv ℝ F) xE u v +
      chartChristoffelContraction (I := I) gM (iota x)
        (diota u) (diota v) iotaE -
    diota (chartChristoffelContraction (I := IN) gN x u v xE)

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [IN.Boundaryless] [I.Boundaryless] in
private theorem gaussDefectModelValue_add_left
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) (x : N)
    (u₁ u₂ v : EN) :
    gaussDefectModelValue gN gM iota x (u₁ + u₂) v =
      gaussDefectModelValue gN gM iota x u₁ v +
        gaussDefectModelValue gN gM iota x u₂ v := by
  simp only [gaussDefectModelValue, map_add, add_apply,
    ChartChristoffel.contraction_add_left]
  abel

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [IN.Boundaryless] [I.Boundaryless] in
private theorem gaussDefectModelValue_smul_left
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) (x : N)
    (a : ℝ) (u v : EN) :
    gaussDefectModelValue gN gM iota x (a • u) v =
      a • gaussDefectModelValue gN gM iota x u v := by
  simp only [gaussDefectModelValue, map_smul,
    ChartChristoffel.contraction_smul_left, smul_add, smul_sub]
  rfl

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [IN.Boundaryless] [I.Boundaryless] in
private theorem gaussDefectModelValue_add_right
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) (x : N)
    (u v₁ v₂ : EN) :
    gaussDefectModelValue gN gM iota x u (v₁ + v₂) =
      gaussDefectModelValue gN gM iota x u v₁ +
        gaussDefectModelValue gN gM iota x u v₂ := by
  simp only [gaussDefectModelValue, map_add,
    ChartChristoffel.contraction_add_right]
  abel

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [IN.Boundaryless] [I.Boundaryless] in
private theorem gaussDefectModelValue_smul_right
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) (x : N)
    (a : ℝ) (u v : EN) :
    gaussDefectModelValue gN gM iota x u (a • v) =
      a • gaussDefectModelValue gN gM iota x u v := by
  simp only [gaussDefectModelValue, map_smul,
    ChartChristoffel.contraction_smul_right, smul_add, smul_sub]

private def gaussDefectModel
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) (x : N) :
    EN →L[ℝ] EN →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ LinearMap.toContinuousLinearMap
        { toFun := fun v ↦ gaussDefectModelValue gN gM iota x u v
          map_add' := gaussDefectModelValue_add_right gN gM iota x u
          map_smul' := by
            intro a v
            simpa using gaussDefectModelValue_smul_right gN gM iota x a u v }
      map_add' := by
        intro u₁ u₂
        ext v
        exact gaussDefectModelValue_add_left gN gM iota x u₁ u₂ v
      map_smul' := by
        intro a u
        ext v
        simpa using gaussDefectModelValue_smul_left gN gM iota x a u v }

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [IN.Boundaryless] [I.Boundaryless] in
@[simp]
private theorem gaussDefectModel_apply
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) (x : N)
    (u v : EN) :
    gaussDefectModel gN gM iota x u v =
      gaussDefectModelValue gN gM iota x u v :=
  rfl

def secondFundamentalFormAmbientAt
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) (x : N) :
    TangentSpace IN x →L[ℝ]
      TangentSpace IN x →L[ℝ] TangentSpace I (iota x) :=
  let eN := tangentSpaceModelContinuousLinearEquiv (I := IN) x
  let eM := tangentSpaceModelContinuousLinearEquiv (I := I) (iota x)
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ eM.symm.toContinuousLinearMap.comp
        ((gaussDefectModel gN gM iota x (eN u)).comp
          eN.toContinuousLinearMap)
      map_add' := by
        intro u v
        ext w
        simp
      map_smul' := by
        intro a u
        ext v
        simp }

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [IN.Boundaryless] [I.Boundaryless] in
@[simp]
private theorem secondFundamentalFormAmbientAt_apply
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) (x : N)
    (u v : TangentSpace IN x) :
    secondFundamentalFormAmbientAt gN gM iota x u v =
      (tangentSpaceModelContinuousLinearEquiv (I := I) (iota x)).symm
        (gaussDefectModelValue gN gM iota x
          (tangentSpaceModelContinuousLinearEquiv (I := IN) x u)
          (tangentSpaceModelContinuousLinearEquiv (I := IN) x v)) :=
  rfl

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
theorem secondFundamentalFormAmbientAt_symmetric
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) {iota : N → M} {x : N}
    (hiota : ContMDiffAt IN I 2 iota x)
    (u v : TangentSpace IN x) :
    secondFundamentalFormAmbientAt gN gM iota x u v =
      secondFundamentalFormAmbientAt gN gM iota x v u := by
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) (iota x)).injective
  simp only [secondFundamentalFormAmbientAt_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  let F : EN → E := writtenInExtChartAt IN I x iota
  let xE : EN := extChartAt IN x x
  let uE : EN := tangentSpaceModelContinuousLinearEquiv (I := IN) x u
  let vE : EN := tangentSpaceModelContinuousLinearEquiv (I := IN) x v
  have hF : ContDiffAt ℝ 2 F xE := by
    have hchart := (contMDiffAt_iff.mp hiota).2
    rw [ModelWithCorners.Boundaryless.range_eq_univ,
      contDiffWithinAt_univ] at hchart
    exact hchart
  have hsecond :
      fderiv ℝ (fderiv ℝ F) xE uE vE =
        fderiv ℝ (fderiv ℝ F) xE vE uE :=
    (hF.isSymmSndFDerivAt (by simp)).eq uE vE
  simp only [gaussDefectModelValue]
  rw [hsecond,
    chartChristoffelContraction_symm (I := I) gM (iota x),
    chartChristoffelContraction_symm (I := IN) gN x]

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
theorem secondFundamentalFormAmbientAt_diagonal_along_curve
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) {iota : N → M}
    (hiota : ContMDiff IN I ∞ iota)
    (gamma : ℝ → N)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) IN ∞ gamma)
    (t : ℝ) :
    secondFundamentalFormAmbientAt gN gM iota (gamma t)
        ((mfderiv (modelWithCornersSelf ℝ ℝ) IN gamma t : ℝ →L[ℝ] _) 1)
        ((mfderiv (modelWithCornersSelf ℝ ℝ) IN gamma t : ℝ →L[ℝ] _) 1) =
      secondFundamentalFormDiagonalAlongCurve gN gM iota gamma t := by
  classical
  let sourceCoord : ℝ → EN :=
    chartCurve (I := IN) (gamma t) gamma
  let targetCurve : ℝ → M := fun s ↦ iota (gamma s)
  let targetCoord : ℝ → E :=
    chartCurve (I := I) (iota (gamma t)) targetCurve
  let F : EN → E := writtenInExtChartAt IN I (gamma t) iota
  let velocity : TangentSpace IN (gamma t) :=
    (mfderiv (modelWithCornersSelf ℝ ℝ) IN gamma t : ℝ →L[ℝ] _) 1
  let sourceAcceleration : TangentSpace IN (gamma t) :=
    covariantAcceleration (I := IN) gN gamma t
  have htargetSmooth :
      ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞ targetCurve := by
    change ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞ (iota ∘ gamma)
    exact hiota.comp hgamma
  have hsourceCoordC2 : ContDiffAt ℝ 2 sourceCoord t := by
    exact (CovariantDerivativeAlong.contDiffAt_chartCurve
      (I := IN) (n := ∞) hgamma t).of_le
        (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have hFC2 : ContDiffAt ℝ 2 F (sourceCoord t) := by
    have hchart :=
      (contMDiffAt_iff.mp (hiota.contMDiffAt (x := gamma t))).2
    rw [ModelWithCorners.Boundaryless.range_eq_univ,
      contDiffWithinAt_univ] at hchart
    exact (by simpa only [F, sourceCoord, chartCurve, writtenInExtChartAt] using
      hchart.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞))
  have hsourceNhd :
      {s : ℝ | gamma s ∈ (extChartAt IN (gamma t)).source} ∈ nhds t := by
    exact hgamma.continuous.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := IN) (gamma t)).mem_nhds
        (mem_extChartAt_source (gamma t)))
  have htargetCoordEq :
      Filter.EventuallyEq (nhds t) targetCoord (F ∘ sourceCoord) := by
    filter_upwards [hsourceNhd] with s hs
    dsimp only [targetCoord, targetCurve, sourceCoord, F, chartCurve,
      writtenInExtChartAt, Function.comp_apply]
    rw [(extChartAt IN (gamma t)).left_inv hs]
  have hsecondEq :
      deriv (deriv targetCoord) t =
        fderiv ℝ (fderiv ℝ F) (sourceCoord t)
            (deriv sourceCoord t) (deriv sourceCoord t) +
          fderiv ℝ F (sourceCoord t) (deriv (deriv sourceCoord) t) := by
    have heq := Filter.EventuallyEq.iteratedDeriv_eq 2 htargetCoordEq
    have hchain := deriv_deriv_comp hFC2 hsourceCoordC2
    have heq' :
        deriv (deriv targetCoord) t = deriv (deriv (F ∘ sourceCoord)) t := by
      simpa only [iteratedDeriv_eq_iterate, Function.iterate_succ_apply,
        Function.iterate_zero_apply] using heq
    exact heq'.trans hchain
  have hvelocityCoord :
      tangentSpaceModelContinuousLinearEquiv (I := IN) (gamma t) velocity =
        deriv sourceCoord t := by
    have hcoord :=
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
        (I := IN) (M := N) (γ := gamma) hgamma (gamma t)
        (mem_chart_source HN (gamma t))
    rw [← trivToE_self_apply_tangentSpaceModel (I := IN)]
    change trivToE (I := IN) (gamma t) (gamma t) velocity = _
    change trivToE (I := IN) (gamma t) (gamma t) velocity =
      deriv ((extChartAt IN (gamma t)) ∘ gamma) t
    rw [← fderiv_apply_one_eq_deriv]
    exact hcoord
  have htargetVelocity :
      deriv targetCoord t =
        fderiv ℝ F (sourceCoord t) (deriv sourceCoord t) := by
    rw [htargetCoordEq.deriv_eq]
    exact ((hFC2.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (hsourceCoordC2.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hmapAcceleration :
      tangentSpaceModelContinuousLinearEquiv (I := I) (iota (gamma t))
          (mfderiv IN I iota (gamma t) sourceAcceleration) =
        tangentLinearMapToModel (mfderiv IN I iota (gamma t))
          (tangentSpaceModelContinuousLinearEquiv (I := IN) (gamma t)
            sourceAcceleration) := by
    rfl
  apply (tangentSpaceModelContinuousLinearEquiv
    (I := I) (iota (gamma t))).injective
  simp only [secondFundamentalFormAmbientAt_apply,
    ContinuousLinearEquiv.apply_symm_apply,
    secondFundamentalFormDiagonalAlongCurve_def, map_sub]
  change gaussDefectModelValue gN gM iota (gamma t)
      (tangentSpaceModelContinuousLinearEquiv (I := IN) (gamma t) velocity)
      (tangentSpaceModelContinuousLinearEquiv (I := IN) (gamma t) velocity) =
    tangentSpaceModelContinuousLinearEquiv (I := I) (iota (gamma t))
        (covariantAcceleration (I := I) gM targetCurve t) -
      tangentSpaceModelContinuousLinearEquiv (I := I) (iota (gamma t))
        (mfderiv IN I iota (gamma t) sourceAcceleration)
  rw [hvelocityCoord, hmapAcceleration,
    covariantAcceleration_modelCoord (I := I) gM targetCurve t htargetSmooth,
    covariantAcceleration_modelCoord (I := IN) gN gamma t hgamma]
  simp_rw [tangentLinearMapToModel_mfderiv_eq_fderiv_writtenInExtChartAt
    (I := I) (IN := IN) (hiota.contMDiffAt.mdifferentiableAt (by simp))]
  dsimp only [F, sourceCoord, targetCoord, targetCurve, chartCurve] at hsecondEq htargetVelocity
  dsimp only [F, sourceCoord, targetCoord, targetCurve, chartCurve]
  simp only [gaussDefectModelValue]
  simp_rw [tangentLinearMapToModel_mfderiv_eq_fderiv_writtenInExtChartAt
    (I := I) (IN := IN) (hiota.contMDiffAt.mdifferentiableAt (by simp))]
  rw [hsecondEq]
  rw [htargetVelocity]
  simp only [map_add]
  abel

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
private theorem gaussDefectModelValue_pair_sum
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (hiota : ContMDiff IN I ∞ iota)
    (hmetric : ∀ (x : N) (u v : TangentSpace IN x),
      gM.inner (iota x) (mfderiv IN I iota x u) (mfderiv IN I iota x v) = gN.inner x u v) (x : N) (u v w : EN) :
    chartMetricBilin gM (iota x) (extChartAt I (iota x) (iota x))
        (gaussDefectModelValue gN gM iota x u v)
        (tangentLinearMapToModel (mfderiv IN I iota x) w) +
      chartMetricBilin gM (iota x) (extChartAt I (iota x) (iota x))
        (tangentLinearMapToModel (mfderiv IN I iota x) v)
        (gaussDefectModelValue gN gM iota x u w) = 0 := by
  let F : EN → E := writtenInExtChartAt IN I x iota
  let z : EN := extChartAt IN x x
  let c : ℝ → EN := fun s => z + s • u
  have hc0 : c 0 = z := by simp [c]
  have hc : HasDerivAt c u 0 := by
    simpa only [c, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z
  have hF : ContDiffAt ℝ 2 F z := by
    have hf := (contMDiffAt_iff.mp (hiota.contMDiffAt (x := x))).2
    rw [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ] at hf
    exact hf.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hFc : HasDerivAt (F ∘ c) (fderiv ℝ F z u) 0 := by
    have hf : HasFDerivAt F (fderiv ℝ F z) (c 0) := by
      simpa only [hc0] using (hF.differentiableAt (by norm_num)).hasFDerivAt
    exact hf.comp_hasDerivAt 0 hc
  have hDc : HasDerivAt ((fderiv ℝ F) ∘ c) (fderiv ℝ (fderiv ℝ F) z u) 0 := by
    have hd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) (c 0) := by
      simpa only [hc0] using hdF.hasFDerivAt
    exact hd.comp_hasDerivAt 0 hc
  have hV (v : EN) : HasDerivAt (fun s => fderiv ℝ F (c s) v)
      (fderiv ℝ (fderiv ℝ F) z u v) 0 := by
    simpa only [Function.comp_apply, map_zero, add_zero] using hDc.clm_apply (hasDerivAt_const 0 v)
  have hFz : F z = extChartAt I (iota x) (iota x) := by
    simp only [F, z, writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv]
  have hsource := chartMetricBilin_hasDerivAt gN x hc
    (hasDerivAt_const 0 v) (hasDerivAt_const 0 w)
    (by simpa only [hc0] using mem_extChartAt_target (I := IN) x)
  have htarget := chartMetricBilin_hasDerivAt gM (iota x) hFc (hV v) (hV w)
    (by simpa only [Function.comp_apply, hc0, hFz] using
      mem_extChartAt_target (I := I) (iota x))
  have heq : Filter.EventuallyEq (nhds (0 : ℝ))
      (fun s => chartMetricBilin gM (iota x) (F (c s))
        (fderiv ℝ F (c s) v) (fderiv ℝ F (c s) w))
      (fun s => chartMetricBilin gN x (c s) v w) := by
    have hevent := chartMetricBilin_pullback_eventually_of_inner_map hiota hmetric x
    have hcTendsto : Filter.Tendsto c (nhds 0) (nhds z) := hc0 ▸ hc.continuousAt
    filter_upwards [hcTendsto.eventually hevent] with s hs
    exact hs v w
  have hderiv := (htarget.congr_of_eventuallyEq heq.symm).unique hsource
  simp only [Function.comp_apply, hc0, hFz, zero_add] at hderiv
  have hpull (a b : EN) :
      chartMetricBilin gM (iota x) (extChartAt I (iota x) (iota x))
        (fderiv ℝ F z a) (fderiv ℝ F z b) = chartMetricBilin gN x z a b := by
    have hself := (chartMetricBilin_pullback_eventually_of_inner_map hiota hmetric x).self_of_nhds a b
    simpa only [← hFz] using hself
  simp only [gaussDefectModelValue]
  simp_rw [tangentLinearMapToModel_mfderiv_eq_fderiv_writtenInExtChartAt
    (hiota.mdifferentiableAt (by simp))]
  rw [← hFz]
  change chartMetricBilin gM (iota x) (F z)
      (fderiv ℝ (fderiv ℝ F) z u v +
        chartChristoffelContraction gM (iota x) (fderiv ℝ F z u) (fderiv ℝ F z v) (F z) -
        fderiv ℝ F z (chartChristoffelContraction gN x u v z)) (fderiv ℝ F z w) +
    chartMetricBilin gM (iota x) (F z) (fderiv ℝ F z v)
      (fderiv ℝ (fderiv ℝ F) z u w +
        chartChristoffelContraction gM (iota x) (fderiv ℝ F z u) (fderiv ℝ F z w) (F z) -
        fderiv ℝ F z (chartChristoffelContraction gN x u w z)) = 0
  rw [hFz]
  simp only [map_sub, sub_apply, hpull]
  linarith only [hderiv]

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
private theorem secondFundamentalFormAmbientAt_pair_sum
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (hiota : ContMDiff IN I ∞ iota)
    (hmetric : ∀ (x : N) (u v : TangentSpace IN x),
      gM.inner (iota x) (mfderiv IN I iota x u) (mfderiv IN I iota x v) = gN.inner x u v) (x : N)
    (u v w : TangentSpace IN x) :
    gM.inner (iota x) (secondFundamentalFormAmbientAt gN gM iota x u v)
        (mfderiv IN I iota x w) +
      gM.inner (iota x) (secondFundamentalFormAmbientAt gN gM iota x u w)
        (mfderiv IN I iota x v) = 0 := by
  have hinner (a b : TangentSpace I (iota x)) :
      chartMetricBilin gM (iota x) (extChartAt I (iota x) (iota x))
        (tangentSpaceModelContinuousLinearEquiv (I := I) (iota x) a)
        (tangentSpaceModelContinuousLinearEquiv (I := I) (iota x) b) =
          gM.inner (iota x) a b := by
    rw [← trivToE_self_apply_tangentSpaceModel, ← trivToE_self_apply_tangentSpaceModel]
    exact chartMetricBilin_trivToE gM (iota x) (iota x) (mem_chart_source H (iota x)) a b
  rw [gM.symm (iota x) (secondFundamentalFormAmbientAt gN gM iota x u w),
    ← hinner, ← hinner]
  have hm := gaussDefectModelValue_pair_sum hiota hmetric x
    (tangentSpaceModelContinuousLinearEquiv (I := IN) x u)
    (tangentSpaceModelContinuousLinearEquiv (I := IN) x v)
    (tangentSpaceModelContinuousLinearEquiv (I := IN) x w)
  simpa only [secondFundamentalFormAmbientAt_apply, ContinuousLinearEquiv.apply_symm_apply,
    tangentLinearMapToModel_apply, ContinuousLinearEquiv.symm_apply_apply] using hm

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
theorem secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (hiota : ContMDiff IN I ∞ iota)
    (hmetric : ∀ (x : N) (u v : TangentSpace IN x),
      gM.inner (iota x) (mfderiv IN I iota x u) (mfderiv IN I iota x v) = gN.inner x u v) (x : N)
    (u v w : TangentSpace IN x) :
    gM.inner (iota x) (secondFundamentalFormAmbientAt gN gM iota x u v)
      (mfderiv IN I iota x w) = 0 := by
  have hsymm := secondFundamentalFormAmbientAt_symmetric gN gM
    (hiota.contMDiffAt (x := x) |>.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞))
  have h1 := secondFundamentalFormAmbientAt_pair_sum hiota hmetric x u v w
  have h2 := secondFundamentalFormAmbientAt_pair_sum hiota hmetric x v u w
  have h3 := secondFundamentalFormAmbientAt_pair_sum hiota hmetric x w u v
  rw [hsymm v u] at h2
  rw [hsymm w u, hsymm w v] at h3
  linarith only [h1, h2, h3]

namespace IsRiemannianIsometricImmersion

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
theorem secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (u v w : TangentSpace IN x) :
    gM.inner (iota x) (secondFundamentalFormAmbientAt gN gM iota x u v)
      (mfderiv IN I iota x w) = 0 :=
  secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map h.contMDiff h.inner_map x u v w

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
theorem secondFundamentalFormAmbientAt_mem_normalSpaceAt
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (u v : TangentSpace IN x) :
    secondFundamentalFormAmbientAt gN gM iota x u v ∈ h.normalSpaceAt x := by
  rw [h.mem_normalSpaceAt_iff]
  exact h.secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero x u v

def normalProjectionAt
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N) :
    TangentSpace I (iota x) →L[ℝ] h.normalSpaceAt x :=
  LinearMap.toContinuousLinearMap
    ((Tensor0SBundle.tangentMetricData (I := I) gM (iota x)).metric.submoduleProjection
      (h.normalSpaceAt x))

def secondFundamentalFormAt
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N) :
    TangentSpace IN x →L[ℝ]
      TangentSpace IN x →L[ℝ] h.normalSpaceAt x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ h.normalProjectionAt x ∘L
        secondFundamentalFormAmbientAt gN gM iota x u
      map_add' := by
        intro u v
        ext w
        simp
      map_smul' := by
        intro a u
        ext v
        simp }

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [IN.Boundaryless] [I.Boundaryless] in
@[simp]
theorem secondFundamentalFormAt_apply
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (u v : TangentSpace IN x) :
    h.secondFundamentalFormAt x u v =
      h.normalProjectionAt x
        (secondFundamentalFormAmbientAt gN gM iota x u v) :=
  rfl

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [FiniteDimensional ℝ EN] [IN.Boundaryless] [I.Boundaryless] in
@[simp]
theorem normalProjectionAt_coe
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (v : h.normalSpaceAt x) :
    h.normalProjectionAt x (v : TangentSpace I (iota x)) = v := by
  exact Tensor0SBundle.MetricFiberData.submoduleProjection_eq_self
    (Tensor0SBundle.tangentMetricData (I := I) gM (iota x)).metric
    (h.normalSpaceAt x) v v.property

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
theorem normalProjectionAt_gauss_defect
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (u v : TangentSpace IN x) :
    (h.normalProjectionAt x (secondFundamentalFormAmbientAt gN gM iota x u v) :
      TangentSpace I (iota x)) = secondFundamentalFormAmbientAt gN gM iota x u v := by
  exact congrArg Subtype.val (h.normalProjectionAt_coe x
    ⟨_, h.secondFundamentalFormAmbientAt_mem_normalSpaceAt x u v⟩)

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
theorem secondFundamentalFormAt_coe_eq_ambient
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N)
    (u v : TangentSpace IN x) :
    (h.secondFundamentalFormAt x u v : TangentSpace I (iota x)) =
      secondFundamentalFormAmbientAt gN gM iota x u v :=
  h.normalProjectionAt_gauss_defect x u v

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
theorem secondFundamentalFormAt_symmetric
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) {x : N}
    (u v : TangentSpace IN x) :
    h.secondFundamentalFormAt x u v =
      h.secondFundamentalFormAt x v u := by
  have hiotaC2 : ContMDiffAt IN I 2 iota x :=
    h.contMDiff.contMDiffAt.of_le
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  rw [secondFundamentalFormAt_apply, secondFundamentalFormAt_apply,
    secondFundamentalFormAmbientAt_symmetric gN gM hiotaC2 u v]

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
theorem secondFundamentalFormAt_diagonal_along_curve
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota)
    (gamma : ℝ → N)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) IN ∞ gamma)
    (t : ℝ) :
    h.secondFundamentalFormAt (gamma t)
        ((mfderiv (modelWithCornersSelf ℝ ℝ) IN gamma t : ℝ →L[ℝ] _) 1)
        ((mfderiv (modelWithCornersSelf ℝ ℝ) IN gamma t : ℝ →L[ℝ] _) 1) =
      h.normalProjectionAt (gamma t)
        (secondFundamentalFormDiagonalAlongCurve gN gM iota gamma t) := by
  rw [secondFundamentalFormAt_apply,
    secondFundamentalFormAmbientAt_diagonal_along_curve
      gN gM h.contMDiff gamma hgamma t]

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
theorem secondFundamentalFormAt_coe_diagonal_along_curve
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota)
    (gamma : ℝ → N)
    (hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) IN ∞ gamma)
    (t : ℝ) :
    (h.secondFundamentalFormAt (gamma t)
        ((mfderiv (modelWithCornersSelf ℝ ℝ) IN gamma t : ℝ →L[ℝ] _) 1)
        ((mfderiv (modelWithCornersSelf ℝ ℝ) IN gamma t : ℝ →L[ℝ] _) 1) :
      TangentSpace I (iota (gamma t))) =
        secondFundamentalFormDiagonalAlongCurve gN gM iota gamma t := by
  rw [h.secondFundamentalFormAt_coe_eq_ambient,
    secondFundamentalFormAmbientAt_diagonal_along_curve gN gM h.contMDiff gamma hgamma t]

def hasVanishingSecondFundamentalForm
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) : Prop :=
  ∀ x : N, h.secondFundamentalFormAt x = 0

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [IN.Boundaryless] [I.Boundaryless] in
theorem hasVanishingSecondFundamentalForm_iff
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (h : IsRiemannianIsometricImmersion gN gM iota) :
    h.hasVanishingSecondFundamentalForm ↔
      ∀ (x : N) (u v : TangentSpace IN x),
        h.secondFundamentalFormAt x u v = 0 := by
  constructor
  · intro hzero x u v
    rw [hzero x]
    simp
  · intro hzero x
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    exact hzero x u v

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
theorem hasVanishingSecondFundamentalForm.along_curves
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    {h : IsRiemannianIsometricImmersion gN gM iota}
    (hII : h.hasVanishingSecondFundamentalForm) :
    hasVanishingSecondFundamentalFormAlongCurves gN gM iota := by
  intro gamma t hgamma
  rw [← h.secondFundamentalFormAt_coe_diagonal_along_curve gamma hgamma t, hII (gamma t)]
  rfl

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
theorem hasVanishingSecondFundamentalForm.hasGeodesicEquationAt_comp
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    {h : IsRiemannianIsometricImmersion gN gM iota}
    (hII : h.hasVanishingSecondFundamentalForm)
    {gamma : ℝ → N} (hgamma : ContMDiff 𝓘(ℝ, ℝ) IN ∞ gamma)
    {t : ℝ} (hgeodesic : HasGeodesicEquationAt (I := IN) gN gamma t) :
    HasGeodesicEquationAt (I := I) gM (iota ∘ gamma) t :=
  hII.along_curves.hasGeodesicEquationAt_comp h.contMDiff hgamma hgeodesic

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)] in
theorem hasVanishingSecondFundamentalForm.isGeodesic_comp
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    {h : IsRiemannianIsometricImmersion gN gM iota}
    (hII : h.hasVanishingSecondFundamentalForm)
    {gamma : ℝ → N} (hgamma : ContMDiff 𝓘(ℝ, ℝ) IN ∞ gamma)
    (hgeodesic : IsGeodesic (I := IN) gN gamma) :
    IsGeodesic (I := I) gM (iota ∘ gamma) :=
  hII.along_curves.isGeodesic_comp h.contMDiff hgamma hgeodesic

end IsRiemannianIsometricImmersion

omit [NeZero (Module.finrank ℝ EN)] [FiniteDimensional ℝ EN]
    [IN.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem isRiemannianIsometricImmersion_id
    (g : SmoothRiemannianMetric I M) :
    IsRiemannianIsometricImmersion g g (id : M → M) where
  isImmersion := IsImmersion.id
  inner_map := by
    intro x u v
    simp

omit [NeZero (Module.finrank ℝ EN)] [FiniteDimensional ℝ EN]
    [IN.Boundaryless] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hasVanishingSecondFundamentalForm_id
    (g : SmoothRiemannianMetric I M) :
    (isRiemannianIsometricImmersion_id g).hasVanishingSecondFundamentalForm := by
  let h := isRiemannianIsometricImmersion_id g
  intro x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hbot : h.normalSpaceAt x = ⊥ :=
    h.normalSpaceAt_eq_bot_of_surjective_derivative x (by
      intro w
      exact ⟨w, by simp⟩)
  apply Subtype.ext
  change (h.secondFundamentalFormAt x u v : TangentSpace I (id x)) = 0
  have hmem : (h.secondFundamentalFormAt x u v : TangentSpace I (id x)) ∈
      h.normalSpaceAt x := Subtype.property _
  exact (Submodule.eq_bot_iff (h.normalSpaceAt x)).mp hbot _ hmem


omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
theorem covariantAcceleration_chartCoord_of_contMDiffAt
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M) (t : ℝ)
    (hgamma : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I 2 gamma t) :
    trivToE (I := I) (gamma t) (gamma t)
        (covariantAcceleration (I := I) g gamma t) =
      deriv (deriv (chartCurve (I := I) (gamma t) gamma)) t +
        chartChristoffelContraction (I := I) g (gamma t)
          (deriv (chartCurve (I := I) (gamma t) gamma) t)
          (deriv (chartCurve (I := I) (gamma t) gamma) t)
          (extChartAt I (gamma t) (gamma t)) := by
  classical
  let u : ℝ → E := chartCurve (I := I) (gamma t) gamma
  let V : ∀ s, TangentSpace I (gamma s) := fun s ↦
    (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s : ℝ →L[ℝ] _) (1 : ℝ)
  let rep : ℝ → E := chartRepAt (I := I) gamma V t
  have hsrc : {s : ℝ | gamma s ∈ (chartAt H (gamma t)).source} ∈ nhds t := by
    exact hgamma.continuousAt.preimage_mem_nhds
      ((chartAt H (gamma t)).open_source.mem_nhds
        (mem_chart_source H (gamma t)))
  have hnear : ∀ᶠ s in nhds t, ContMDiffAt 𝓘(ℝ, ℝ) I 2 gamma s :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hgamma
  have hrepEq : Filter.EventuallyEq (nhds t) rep (deriv u) := by
    filter_upwards [hsrc, hnear] with s hs hgs
    dsimp only [rep]
    rw [chartRepAt_apply]
    have hcoord :=
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) (γ := gamma) (hgs.mdifferentiableAt (by norm_num)) (gamma t) hs
    change
      (trivializationAt E (TangentSpace I) (gamma t)).continuousLinearMapAt
          ℝ (gamma s)
          ((mfderiv (modelWithCornersSelf ℝ ℝ) I gamma s : ℝ →L[ℝ] _) 1) =
        deriv ((extChartAt I (gamma t)) ∘ gamma) s
    rw [← fderiv_apply_one_eq_deriv]
    exact hcoord
  have hrepSelf : rep t = deriv u t := hrepEq.eq_of_nhds
  have hrepDeriv : deriv rep t = deriv (deriv u) t := hrepEq.deriv_eq
  change trivToE (I := I) (gamma t) (gamma t)
      (covariantAcceleration (I := I) g gamma t) = _
  rw [covariantAcceleration_def]
  change trivToE (I := I) (gamma t) (gamma t)
      (covDerivAlong (I := I) g gamma V t) = _
  rw [covDerivAlong_chartCoord]
  change chartCovDerivAlong (I := I) g (gamma t) gamma rep t = _
  rw [chartCovDerivAlong_def, hrepDeriv, hrepSelf]
  rfl

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
theorem covariantAcceleration_modelCoord_of_contMDiffAt
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M) (t : ℝ)
    (hgamma : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I 2 gamma t) :
    tangentSpaceModelContinuousLinearEquiv (I := I) (gamma t)
        (covariantAcceleration (I := I) g gamma t) =
      deriv (deriv (chartCurve (I := I) (gamma t) gamma)) t +
        chartChristoffelContraction (I := I) g (gamma t)
          (deriv (chartCurve (I := I) (gamma t) gamma) t)
          (deriv (chartCurve (I := I) (gamma t) gamma) t)
          (extChartAt I (gamma t) (gamma t)) := by
  rw [← trivToE_self_apply_tangentSpaceModel (I := I)]
  exact covariantAcceleration_chartCoord_of_contMDiffAt (I := I) g gamma t hgamma

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
theorem secondFundamentalFormAmbientAt_diagonal_along_curve_of_contMDiffAt
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) {iota : N → M}
    (gamma : ℝ → N) (t : ℝ)
    (hiota : ContMDiffAt IN I 2 iota (gamma t))
    (hgamma : ContMDiffAt (modelWithCornersSelf ℝ ℝ) IN 2 gamma t) :
    secondFundamentalFormAmbientAt gN gM iota (gamma t)
        ((mfderiv (modelWithCornersSelf ℝ ℝ) IN gamma t : ℝ →L[ℝ] _) 1)
        ((mfderiv (modelWithCornersSelf ℝ ℝ) IN gamma t : ℝ →L[ℝ] _) 1) =
      secondFundamentalFormDiagonalAlongCurve gN gM iota gamma t := by
  classical
  let sourceCoord : ℝ → EN :=
    chartCurve (I := IN) (gamma t) gamma
  let targetCurve : ℝ → M := fun s ↦ iota (gamma s)
  let targetCoord : ℝ → E :=
    chartCurve (I := I) (iota (gamma t)) targetCurve
  let F : EN → E := writtenInExtChartAt IN I (gamma t) iota
  let velocity : TangentSpace IN (gamma t) :=
    (mfderiv (modelWithCornersSelf ℝ ℝ) IN gamma t : ℝ →L[ℝ] _) 1
  let sourceAcceleration : TangentSpace IN (gamma t) :=
    covariantAcceleration (I := IN) gN gamma t
  have htargetSmooth :
      ContMDiffAt (modelWithCornersSelf ℝ ℝ) I 2 targetCurve t := by
    exact hiota.comp t hgamma
  have hsourceCoordC2 : ContDiffAt ℝ 2 sourceCoord t := by
    exact ((contMDiffAt_extChartAt' (mem_chart_source HN (gamma t))).comp t hgamma).contDiffAt
  have hFC2 : ContDiffAt ℝ 2 F (sourceCoord t) := by
    have hchart :=
      (contMDiffAt_iff.mp hiota).2
    rw [ModelWithCorners.Boundaryless.range_eq_univ,
      contDiffWithinAt_univ] at hchart
    exact (by simpa only [F, sourceCoord, chartCurve, writtenInExtChartAt] using
      hchart)
  have hsourceNhd :
      {s : ℝ | gamma s ∈ (extChartAt IN (gamma t)).source} ∈ nhds t := by
    exact hgamma.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := IN) (gamma t)).mem_nhds
        (mem_extChartAt_source (gamma t)))
  have htargetCoordEq :
      Filter.EventuallyEq (nhds t) targetCoord (F ∘ sourceCoord) := by
    filter_upwards [hsourceNhd] with s hs
    dsimp only [targetCoord, targetCurve, sourceCoord, F, chartCurve,
      writtenInExtChartAt, Function.comp_apply]
    rw [(extChartAt IN (gamma t)).left_inv hs]
  have hsecondEq :
      deriv (deriv targetCoord) t =
        fderiv ℝ (fderiv ℝ F) (sourceCoord t)
            (deriv sourceCoord t) (deriv sourceCoord t) +
          fderiv ℝ F (sourceCoord t) (deriv (deriv sourceCoord) t) := by
    have heq := Filter.EventuallyEq.iteratedDeriv_eq 2 htargetCoordEq
    have hchain := deriv_deriv_comp hFC2 hsourceCoordC2
    have heq' :
        deriv (deriv targetCoord) t = deriv (deriv (F ∘ sourceCoord)) t := by
      simpa only [iteratedDeriv_eq_iterate, Function.iterate_succ_apply,
        Function.iterate_zero_apply] using heq
    exact heq'.trans hchain
  have hvelocityCoord :
      tangentSpaceModelContinuousLinearEquiv (I := IN) (gamma t) velocity =
        deriv sourceCoord t := by
    have hcoord :=
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := IN) (M := N) (γ := gamma) (hgamma.mdifferentiableAt (by norm_num)) (gamma t)
        (mem_chart_source HN (gamma t))
    rw [← trivToE_self_apply_tangentSpaceModel (I := IN)]
    change trivToE (I := IN) (gamma t) (gamma t) velocity = _
    change trivToE (I := IN) (gamma t) (gamma t) velocity =
      deriv ((extChartAt IN (gamma t)) ∘ gamma) t
    rw [← fderiv_apply_one_eq_deriv]
    exact hcoord
  have htargetVelocity :
      deriv targetCoord t =
        fderiv ℝ F (sourceCoord t) (deriv sourceCoord t) := by
    rw [htargetCoordEq.deriv_eq]
    exact ((hFC2.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (hsourceCoordC2.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hmapAcceleration :
      tangentSpaceModelContinuousLinearEquiv (I := I) (iota (gamma t))
          (mfderiv IN I iota (gamma t) sourceAcceleration) =
        tangentLinearMapToModel (mfderiv IN I iota (gamma t))
          (tangentSpaceModelContinuousLinearEquiv (I := IN) (gamma t)
            sourceAcceleration) := by
    rfl
  apply (tangentSpaceModelContinuousLinearEquiv
    (I := I) (iota (gamma t))).injective
  simp only [secondFundamentalFormAmbientAt_apply,
    ContinuousLinearEquiv.apply_symm_apply,
    secondFundamentalFormDiagonalAlongCurve_def, map_sub]
  change gaussDefectModelValue gN gM iota (gamma t)
      (tangentSpaceModelContinuousLinearEquiv (I := IN) (gamma t) velocity)
      (tangentSpaceModelContinuousLinearEquiv (I := IN) (gamma t) velocity) =
    tangentSpaceModelContinuousLinearEquiv (I := I) (iota (gamma t))
        (covariantAcceleration (I := I) gM targetCurve t) -
      tangentSpaceModelContinuousLinearEquiv (I := I) (iota (gamma t))
        (mfderiv IN I iota (gamma t) sourceAcceleration)
  rw [hvelocityCoord, hmapAcceleration,
    covariantAcceleration_modelCoord_of_contMDiffAt (I := I) gM targetCurve t htargetSmooth,
    covariantAcceleration_modelCoord_of_contMDiffAt (I := IN) gN gamma t hgamma]
  simp_rw [tangentLinearMapToModel_mfderiv_eq_fderiv_writtenInExtChartAt
    (I := I) (IN := IN) (hiota.mdifferentiableAt (by norm_num))]
  dsimp only [F, sourceCoord, targetCoord, targetCurve, chartCurve] at hsecondEq htargetVelocity
  dsimp only [F, sourceCoord, targetCoord, targetCurve, chartCurve]
  simp only [gaussDefectModelValue]
  simp_rw [tangentLinearMapToModel_mfderiv_eq_fderiv_writtenInExtChartAt
    (I := I) (IN := IN) (hiota.mdifferentiableAt (by norm_num))]
  rw [hsecondEq]
  rw [htargetVelocity]
  simp only [map_add]
  abel

omit [NeZero (Module.finrank ℝ EN)] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
theorem hasVanishingSecondFundamentalFormAlongCurves.covariantAcceleration_comp_of_contMDiffAt
    {gN : SmoothRiemannianMetric IN N} {gM : SmoothRiemannianMetric I M}
    {iota : N → M} (h : hasVanishingSecondFundamentalFormAlongCurves gN gM iota)
    (hiota : ContMDiff IN I ∞ iota) (gamma : ℝ → N) (t : ℝ)
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) IN 2 gamma t) :
    covariantAcceleration gM (fun s => iota (gamma s)) t =
      mfderiv IN I iota (gamma t) (covariantAcceleration gN gamma t) := by
  let v : TangentSpace IN (gamma t) := mfderiv 𝓘(ℝ, ℝ) IN gamma t 1
  obtain ⟨sigma, hsigma, _, hv⟩ := exists_contMDiff_curve_with_velocity_range_subset
    (I := IN) BoundarylessManifold.isInteriorPoint v
    (Filter.univ_mem : Set.univ ∈ nhds (gamma t))
  have hzero := secondFundamentalFormAmbientAt_diagonal_along_curve gN gM hiota sigma hsigma 0
  rw [h sigma 0 hsigma] at hzero
  have hvel := congrArg (fun q : TangentBundle IN N =>
    secondFundamentalFormAmbientAt gN gM iota q.1 q.2 q.2) hv
  have hz : secondFundamentalFormAmbientAt gN gM iota (gamma t) v v = 0 :=
    hvel.symm.trans hzero
  rw [secondFundamentalFormAmbientAt_diagonal_along_curve_of_contMDiffAt
    gN gM gamma t (hiota.contMDiffAt.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)) hgamma] at hz
  exact sub_eq_zero.mp hz


end PointwiseGaussDefect

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion

@[reducible] alias HasVanishingSecondFundamentalForm := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.hasVanishingSecondFundamentalForm
end DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion

namespace DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.HasVanishingSecondFundamentalForm

alias along_curves := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.hasVanishingSecondFundamentalForm.along_curves
alias hasGeodesicEquationAt_comp := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.hasVanishingSecondFundamentalForm.hasGeodesicEquationAt_comp
alias isGeodesic_comp := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.hasVanishingSecondFundamentalForm.isGeodesic_comp
end DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.HasVanishingSecondFundamentalForm
