import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CorrectionContraction
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Function Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def immersionSecondFundamental {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (x : U) (X Y : EuclideanSpace ℝ (Fin m)) : TangentSpace I (F x) := by
  have a : TangentSpace I (F x) := by
    simpa only [zero_smul, add_zero] using
      covDerivAlong g (fun t : ℝ => F ((x : EuclideanSpace ℝ (Fin m)) + t • X))
        (fun t => mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F
          ((x : EuclideanSpace ℝ (Fin m)) + t • X) Y) 0
  exact a - mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x
    ((metricCov h) (fun _ : U => Y) x X)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem trivToE_self_eq_id (x : M) (v : TangentSpace I x) :
    trivToE (I := I) x x v = v := by
  rw [trivToE, TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
    (x₀ := x) (x := x) (mem_chart_source H x), mfderiv_extChartAt_self]
  rfl

omit [FiniteDimensional ℝ E] in
theorem trivToE_mfderiv_eq_fderiv {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {F : A → M} {z : A} (hF : MDifferentiableAt 𝓘(ℝ, A) I F z) {p : M}
    (hp : F z ∈ (chartAt H p).source) (w : A) :
    trivToE (I := I) p (F z) (mfderiv 𝓘(ℝ, A) I F z w)
      = fderiv ℝ ((extChartAt I p) ∘ F) z w := by
  have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, A)) (I' := I) (I'' := 𝓘(ℝ, E)) (x := z)
    (f := F) (g := (↑(extChartAt I p) : M → E)) (mdifferentiableAt_extChartAt (I := I) hp) hF w
  rw [trivToE, TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
    (x₀ := p) (x := F z) hp, ← mfderiv_eq_fderiv]
  exact hcomp.symm

theorem covDerivAlong_sourcePartial_chart (g : SmoothRiemannianMetric I M)
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {F : A → M} {s : Set A} (hs : IsOpen s) (hF : ContMDiffOn 𝓘(ℝ, A) I ∞ F s)
    {x : A} (hx : x ∈ s) (X Y : A) :
    (trivToE (I := I) (F x) (F x))
        (covDerivAlong (I := I) g (fun t : ℝ => F (x + t • X))
          (fun t => mfderiv 𝓘(ℝ, A) I F (x + t • X) Y) 0)
      = fderiv ℝ (fun q => fderiv ℝ ((extChartAt I (F x)) ∘ F) q Y) x X +
        chartChristoffelContraction (I := I) g (F x)
          (fderiv ℝ ((extChartAt I (F x)) ∘ F) x X)
          (fderiv ℝ ((extChartAt I (F x)) ∘ F) x Y)
          (extChartAt I (F x) (F x)) := by
  classical
  have hFx : ContMDiffAt 𝓘(ℝ, A) I ∞ F x := (hF x hx).contMDiffAt (hs.mem_nhds hx)
  have hFc : ContDiffAt ℝ 2 ((extChartAt I (F x)) ∘ F) x :=
    (((contMDiffAt_extChartAt (I := I) (x := F x)).comp x hFx).contDiffAt).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hrepnear : (fun q => trivToE (I := I) (F x) (F q) (mfderiv 𝓘(ℝ, A) I F q Y))
      =ᶠ[𝓝 x] (fun q => fderiv ℝ ((extChartAt I (F x)) ∘ F) q Y) := by
    filter_upwards [hs.mem_nhds hx, hFx.continuousAt
      ((chartAt H (F x)).open_source.mem_nhds (mem_chart_source H (F x)))] with q hq hchart
    exact trivToE_mfderiv_eq_fderiv (I := I)
      (((hF q hq).contMDiffAt (hs.mem_nhds hq)).mdifferentiableAt (by simp)) hchart Y
  let line : ℝ → A := fun t => x + t • X
  have hl0 : line 0 = x := by simp [line]
  have hl : HasDerivAt line X 0 := by
    simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add x
  have ht : Tendsto line (𝓝 0) (𝓝 x) := by
    have h := hl.continuousAt
    change Tendsto line (𝓝 0) (𝓝 (line 0)) at h
    rwa [hl0] at h
  have hrep : chartRepAt (I := I) (F ∘ line)
      (fun t => mfderiv 𝓘(ℝ, A) I F (line t) Y) 0
      =ᶠ[𝓝 0] (fun t => fderiv ℝ ((extChartAt I (F x)) ∘ F) (line t) Y) := by
    filter_upwards [ht.eventually hrepnear] with t hq
    simpa only [chartRepAt_apply, Function.comp_apply, hl0] using hq
  have hdpartial : DifferentiableAt ℝ (fun q => fderiv ℝ ((extChartAt I (F x)) ∘ F) q Y) x :=
    ((hFc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hrepderiv :=
    (hdpartial.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) hl hl0.symm).congr_of_eventuallyEq hrep
  have hcurvederiv : HasDerivAt (chartCurve (I := I) (F x) (F ∘ line))
      (fderiv ℝ ((extChartAt I (F x)) ∘ F) x X) 0 := by
    have h2 : HasDerivAt (((extChartAt I (F x)) ∘ F) ∘ line)
        (fderiv ℝ ((extChartAt I (F x)) ∘ F) x X) 0 :=
      (hFc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) hl hl0.symm
    have hfun : chartCurve (I := I) (F x) (F ∘ line) = ((extChartAt I (F x)) ∘ F) ∘ line := by
      funext t
      rw [chartCurve_def]
      rfl
    rw [hfun]
    exact h2
  have hcov := covDerivAlong_chartCoord (I := I) g (F ∘ line)
    (fun t => mfderiv 𝓘(ℝ, A) I F (line t) Y) 0
  rw [chartCovDerivAlong_def, hrepderiv.deriv, hrep.eq_of_nhds] at hcov
  rw [show (fun t : ℝ => F (x + t • X)) = (F ∘ line) from rfl]
  rw [show (F ∘ line) 0 = F x from by rw [Function.comp_apply, hl0]] at hcov
  refine hcov.trans ?_
  simp only [hl0]
  rw [hcurvederiv.deriv]
  simp only [hl0, chartCurve_def, Function.comp_apply]

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

variable {m : ℕ}
variable (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))

private theorem chartAt_modelSpace_source (y : EuclideanSpace ℝ (Fin m)) :
    (chartAt (EuclideanSpace ℝ (Fin m)) y).source = Set.univ := by
  rw [chartAt_self_eq]
  rfl

private theorem chartAt_modelSpace_apply (y z : EuclideanSpace ℝ (Fin m)) :
    (chartAt (EuclideanSpace ℝ (Fin m)) y) z = z := by
  rw [chartAt_self_eq]
  rfl

private theorem opens_chart_eq (x : U) :
    (chartAt (M := U) (EuclideanSpace ℝ (Fin m)) x : OpenPartialHomeomorph U
        (EuclideanSpace ℝ (Fin m))) =
      ((chartAt (EuclideanSpace ℝ (Fin m)) (Subtype.val x)).subtypeRestr ⟨x⟩ :
        OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin m))) :=
  TopologicalSpace.Opens.chartAt_eq

private theorem opens_chart_source_mem (x p : U) :
    p ∈ (chartAt (M := U) (EuclideanSpace ℝ (Fin m)) x : OpenPartialHomeomorph U
      (EuclideanSpace ℝ (Fin m))).source := by
  rw [opens_chart_eq U x, OpenPartialHomeomorph.subtypeRestr_source,
    chartAt_modelSpace_source]
  trivial

private theorem opens_chart_apply (x p : U) :
    ((chartAt (M := U) (EuclideanSpace ℝ (Fin m)) x : OpenPartialHomeomorph U
      (EuclideanSpace ℝ (Fin m))) p) = (Subtype.val p : EuclideanSpace ℝ (Fin m)) := by
  rw [opens_chart_eq U x, OpenPartialHomeomorph.subtypeRestr_coe]
  exact chartAt_modelSpace_apply (Subtype.val x) (Subtype.val p)

private theorem extChartAt_opens_apply (x p : U) :
    extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x p
      = (Subtype.val p : EuclideanSpace ℝ (Fin m)) := by
  rw [extChartAt_coe]
  simpa only [Function.comp_apply, modelWithCornersSelf_coe, id_eq] using opens_chart_apply U x p

theorem trivToE_opens (x p : U) (w : EuclideanSpace ℝ (Fin m)) :
    trivToE (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) x p w = w := by
  rw [trivToE, TangentBundle.continuousLinearMapAt_trivializationAt
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) (x₀ := x) (x := p)
    (opens_chart_source_mem U x p)]
  have hfun : (⇑(extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x) : U →
      EuclideanSpace ℝ (Fin m)) = Subtype.val :=
    funext fun q => extChartAt_opens_apply U x q
  rw [hfun, mfderiv_subtype_val]
  rfl

theorem trivFromE_opens (x p : U) (w : EuclideanSpace ℝ (Fin m)) :
    trivFromE (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) x p w = w := by
  have hmem : p ∈ (trivializationAt (EuclideanSpace ℝ (Fin m))
      (TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (M := U) (x := x)]
    exact opens_chart_source_mem U x p
  have h := trivToE_trivFromE (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x hmem w
  simpa only [trivToE_opens U x p] using h

private theorem chartESectionRepr_const (x : U) (Y : EuclideanSpace ℝ (Fin m)) :
    chartESectionRepr (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) x
      (fun _ : U => Y) = fun _ : U => Y := by
  funext p
  rw [chartE_section_repr_eq_trivToE]
  exact trivToE_opens U x p Y

private theorem mdifferentiableAt_const_section (x : U) (Y : EuclideanSpace ℝ (Fin m)) :
    MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m))).tangent
      (fun p : U => (⟨p, Y⟩ : TangentBundle (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) U)) x := by
  have h := mdifferentiableAt_tangentConstAt_self (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (M := U) x (Y : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with p
  have hpt : tangentConstAt (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x
      (Y : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x) p = Y := by
    rw [tangentConstAt_apply, TensorLieDeriv.tangentConstInChart_apply,
      trivToE_opens U x x Y, trivFromE_opens U x p Y]
  rw [hpt]

theorem metricCov_const_eq_chartChristoffel
    (h : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) U) (x : U)
    (X Y : EuclideanSpace ℝ (Fin m)) :
    (metricCov (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) h (fun _ : U => Y) x) X
      = chartChristoffelContraction (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) h x X Y
          (Subtype.val x) := by
  have hzgood : x ∈ chartLeviCivitaGoodSet (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x :=
    self_mem_chartLeviCivitaGoodSet x
  rw [show (metricCov (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) h) =
      LeviCivita (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) h from rfl]
  rw [LeviCivita_chart_apply (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) h x hzgood
    (mdifferentiableAt_const_section U x Y) X]
  rw [chartLeviCivita_apply (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) h x
    (fun _ : U => Y) hzgood X]
  rw [chartESectionRepr_const U x Y]
  rw [show ((fun _ : U => Y) ∘ (⇑(extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x).symm)) =
      (fun _ : EuclideanSpace ℝ (Fin m) => Y) from rfl]
  rw [fderiv_const_apply, zero_apply, zero_add]
  rw [correction_eq_contr]
  have hX : (trivToE (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) x x)
      (X : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x) = X := trivToE_opens U x x X
  rw [hX, extChartAt_opens_apply U x x]
  exact trivFromE_opens U x x (chartChristoffelContraction
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) h x X Y (Subtype.val x))

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
theorem immersionSecondFundamental_chartCoord
    {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (x : U) (X Y : EuclideanSpace ℝ (Fin m)) :
    (tangentSpaceModelContinuousLinearEquiv (I := I) (F x))
        (immersionSecondFundamental U F g h x X Y)
      = fderiv ℝ (fun q => fderiv ℝ ((extChartAt I (F x)) ∘ F) q Y) x X +
        chartChristoffelContraction (I := I) g (F x)
          (fderiv ℝ ((extChartAt I (F x)) ∘ F) x X)
          (fderiv ℝ ((extChartAt I (F x)) ∘ F) x Y)
          (extChartAt I (F x) (F x)) -
        (tangentSpaceModelContinuousLinearEquiv (I := I) (F x))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x
            (chartChristoffelContraction (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) h x X Y
              (Subtype.val x))) := by
  have hcov := covDerivAlong_sourcePartial_chart (I := I) g U.2 hF x.2 X Y
  have hsrc := metricCov_const_eq_chartChristoffel U h x X Y
  have hvl : (tangentSpaceModelContinuousLinearEquiv (I := I) (F x))
      (covDerivAlong (I := I) g (fun t : ℝ => F ((x : EuclideanSpace ℝ (Fin m)) + t • X))
        (fun t => mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F
          ((x : EuclideanSpace ℝ (Fin m)) + t • X) Y) 0)
      = (trivToE (I := I) (F x) (F x))
        (covDerivAlong (I := I) g (fun t : ℝ => F ((x : EuclideanSpace ℝ (Fin m)) + t • X))
          (fun t => mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F
            ((x : EuclideanSpace ℝ (Fin m)) + t • X) Y) 0) :=
    (trivToE_self_eq_id (I := I) (F x) _).symm
  have hmap : (tangentSpaceModelContinuousLinearEquiv (I := I) (F x))
      (immersionSecondFundamental U F g h x X Y)
      = (trivToE (I := I) (F x) (F x))
          (covDerivAlong (I := I) g (fun t : ℝ => F ((x : EuclideanSpace ℝ (Fin m)) + t • X))
            (fun t => mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F
              ((x : EuclideanSpace ℝ (Fin m)) + t • X) Y) 0) -
        (tangentSpaceModelContinuousLinearEquiv (I := I) (F x))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x
            ((metricCov (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (M := U) h
              (fun _ : U => Y) x) X)) := by
    rw [immersionSecondFundamental, map_sub]
    congr 1
  rw [hmap, hcov, hsrc]


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry.Geometry

open private gaussDefectModelValue secondFundamentalFormAmbientAt_apply
  from DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise

section ModelCoordinateFormula

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem secondFundamentalFormAmbientAt_modelCoord
    (gN : SmoothRiemannianMetric IN N) (gM : SmoothRiemannianMetric I M)
    (iota : N → M) (x : N) (u v : TangentSpace IN x) :
    tangentSpaceModelContinuousLinearEquiv (I := I) (iota x)
        (secondFundamentalFormAmbientAt gN gM iota x u v) =
      fderiv ℝ (fderiv ℝ (writtenInExtChartAt IN I x iota)) (extChartAt IN x x)
          (tangentSpaceModelContinuousLinearEquiv (I := IN) x u)
          (tangentSpaceModelContinuousLinearEquiv (I := IN) x v) +
        chartChristoffelContraction (I := I) gM (iota x)
          (tangentLinearMapToModel (mfderiv IN I iota x)
            (tangentSpaceModelContinuousLinearEquiv (I := IN) x u))
          (tangentLinearMapToModel (mfderiv IN I iota x)
            (tangentSpaceModelContinuousLinearEquiv (I := IN) x v))
          (extChartAt I (iota x) (iota x)) -
        tangentLinearMapToModel (mfderiv IN I iota x)
          (chartChristoffelContraction (I := IN) gN x
            (tangentSpaceModelContinuousLinearEquiv (I := IN) x u)
            (tangentSpaceModelContinuousLinearEquiv (I := IN) x v)
            (extChartAt IN x x)) := by
  rw [secondFundamentalFormAmbientAt_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp only [gaussDefectModelValue]

end ModelCoordinateFormula

section OpensChart

variable {m : ℕ}

private theorem extChartAt_opens_symm_apply
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m))) (x p : U) :
    (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x).symm (Subtype.val p) = p := by
  rw [← extChartAt_opens_apply U x p]
  refine (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x).left_inv ?_
  change p ∈ ((chartAt (M := U) (EuclideanSpace ℝ (Fin m)) x).extend
    (𝓘(ℝ, EuclideanSpace ℝ (Fin m)))).source
  rw [OpenPartialHomeomorph.extend_source]
  exact opens_chart_source_mem U x p

end OpensChart

section OpensFormula

variable {m : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem writtenInExtChartAt_opens_eventuallyEq
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M) (x : U) :
    writtenInExtChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) I x (fun y : U => F y)
      =ᶠ[𝓝 (Subtype.val x)]
      (fun q : EuclideanSpace ℝ (Fin m) => extChartAt I (F x) (F q)) := by
  refine Filter.eventuallyEq_of_mem (U.2.mem_nhds x.2) ?_
  intro z hz
  simp only [writtenInExtChartAt, Function.comp_apply]
  rw [extChartAt_opens_symm_apply U x ⟨z, hz⟩]

private theorem writtenInExtChartAt_opensModelSpace
    (F : EuclideanSpace ℝ (Fin m) → M) (x : EuclideanSpace ℝ (Fin m)) :
    writtenInExtChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) I x F
      = fun q : EuclideanSpace ℝ (Fin m) => extChartAt I (F x) (F q) := by
  funext q
  simp only [writtenInExtChartAt, Function.comp_apply]
  rw [show (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) x).symm q = q from by
    rw [extChartAt_model_space_eq_id]
    rfl]

end OpensFormula

section CalculusFlip

private theorem fderiv_fderiv_apply_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : V → W} {a : V} (hg : ContDiffAt ℝ 2 g a) (X Y : V) :
    fderiv ℝ (fun q => fderiv ℝ g q Y) a X = (fderiv ℝ (fderiv ℝ g) a) X Y := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) a :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) a) a := hd.hasFDerivAt
  have hu : HasFDerivAt (fun _ : V => Y) (0 : V →L[ℝ] V) a := hasFDerivAt_const Y a
  have h := (hc.clm_apply hu).fderiv
  rw [h]
  simp

end CalculusFlip

section OpensChartFormula

variable {m : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem secondFundamentalFormAmbientAt_modelCoord_opens
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (x : U) (X Y : EuclideanSpace ℝ (Fin m)) :
    (tangentSpaceModelContinuousLinearEquiv (I := I) (F x))
        (secondFundamentalFormAmbientAt (I := I)
          (IN := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) h g (fun y : U => F y) x X Y)
      = fderiv ℝ (fun q => fderiv ℝ ((extChartAt I (F x)) ∘ F) q Y) x X +
        chartChristoffelContraction (I := I) g (F x)
          (fderiv ℝ ((extChartAt I (F x)) ∘ F) x X)
          (fderiv ℝ ((extChartAt I (F x)) ∘ F) x Y)
          (extChartAt I (F x) (F x)) -
        (tangentSpaceModelContinuousLinearEquiv (I := I) (F x))
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x
            (chartChristoffelContraction (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) h x X Y
              (Subtype.val x))) := by
  have hAt : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F (Subtype.val x) :=
    hF.contMDiffAt (U.2.mem_nhds x.2)
  have hmd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F (Subtype.val x) :=
    hAt.mdifferentiableAt (by simp)
  have hG2 : ContDiffAt ℝ 2 ((extChartAt I (F x)) ∘ F) (Subtype.val x) := by
    have h := (contMDiffAt_iff.mp hAt).2
    rw [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ] at h
    refine (h.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)).congr_of_eventuallyEq ?_
    filter_upwards with q
    simp only [Function.comp_apply]
    rw [show (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (Subtype.val x)).symm q = q from by
      rw [extChartAt_model_space_eq_id]
      rfl]
  have hwritten := writtenInExtChartAt_opensModelSpace (I := I) F (Subtype.val x)
  have hcomp := writtenInExtChartAt_opens_eventuallyEq (I := I) U F x
  have hdiote (v : EuclideanSpace ℝ (Fin m)) :
      tangentLinearMapToModel
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I (fun y : U => F y) x) v
        = fderiv ℝ ((extChartAt I (F x)) ∘ F) x v := by
    have h1 := tangentLinearMapToModel_mfderiv_eq_fderiv_writtenInExtChartAt (IN :=
      𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I := I) (iota := F) hmd v
    rw [hwritten,
      show extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (Subtype.val x) (Subtype.val x)
        = (Subtype.val x : EuclideanSpace ℝ (Fin m)) from by
        rw [extChartAt_model_space_eq_id]
        rfl] at h1
    rw [DifferentialGeometry.mfderiv_restrict_open F U x]
    exact h1
  rw [secondFundamentalFormAmbientAt_modelCoord (gN := h) (gM := g)
    (iota := fun y : U => F y) (x := x) (u := X) (v := Y)]
  simp only [tangentSpaceModelContinuousLinearEquiv_apply]
  rw [extChartAt_opens_apply U x x]
  rw [hcomp.fderiv.fderiv_eq]
  rw [fderiv_fderiv_apply_eq (g := (extChartAt I (F x)) ∘ F)
    (hG2.of_le (by norm_num)) X Y]
  rw [hdiote X, hdiote Y]
  rw [tangentLinearMapToModel_apply, tangentSpaceModelContinuousLinearEquiv_symm_apply,
    tangentSpaceModelContinuousLinearEquiv_apply,
    DifferentialGeometry.mfderiv_restrict_open F U x]
  rfl

end OpensChartFormula

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
theorem immersionSecondFundamental_eq_secondFundamentalFormAmbientAt_of_contMDiffOn {m : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U) :
    ∀ (x : U) (X Y : EuclideanSpace ℝ (Fin m)),
      immersionSecondFundamental U F g h x X Y =
        secondFundamentalFormAmbientAt h g (fun y : U => F y) x X Y := by
  intro x X Y
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) (F x)).injective
  rw [DifferentialGeometry.Geometry.secondFundamentalFormAmbientAt_modelCoord_opens
    U F hF g h x X Y, immersionSecondFundamental_chartCoord U F hF g h x X Y]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
