import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CalculusGeometryFrontier
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CorrectionContraction
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Curvature.Metric.Defs

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

omit [CompleteSpace E] in
theorem immersionSecondFundamental_eq_secondFundamentalFormAmbientAt_of_chartCoord
    {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → M)
    (hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ F U)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) U)
    (hchart : ∀ (x : U) (X Y : EuclideanSpace ℝ (Fin m)),
      (tangentSpaceModelContinuousLinearEquiv (I := I) (F x))
          (secondFundamentalFormAmbientAt (I := I) (IN := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
            h g (fun y : U => F y) x X Y)
        = fderiv ℝ (fun q => fderiv ℝ ((extChartAt I (F x)) ∘ F) q Y) x X +
          chartChristoffelContraction (I := I) g (F x)
            (fderiv ℝ ((extChartAt I (F x)) ∘ F) x X)
            (fderiv ℝ ((extChartAt I (F x)) ∘ F) x Y)
            (extChartAt I (F x) (F x)) -
          (tangentSpaceModelContinuousLinearEquiv (I := I) (F x))
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I F x
              (chartChristoffelContraction (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) h x X Y
                (Subtype.val x)))) :
    immersionSecondFundamental_eq_secondFundamentalFormAmbientAt U F g h := by
  intro x X Y
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) (F x)).injective
  rw [hchart x X Y, immersionSecondFundamental_chartCoord U F hF g h x X Y]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
