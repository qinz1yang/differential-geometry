import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import RicciFlower.Coordinates.Normal.Existence

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Coordinate normal coordinates

This file contains the reusable coordinate-defined normal-coordinate front end.
It deliberately starts with relation-valued endpoint data instead of defining
an exponential map as a function.  A functional exponential map requires the
next analytic layer: uniqueness and smooth dependence of the local geodesic
flow on initial velocity.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle
open Set Function
open scoped Manifold ContDiff Topology
open RicciFlower.GlobalGeometry.Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

/-! ## What the current spray package proves -/

/-- The Picard-Lindelof spray producer gives a coordinate-defined geodesic
equation at the initial time. -/
theorem exists_coordGeoAt
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ gamma : Curve M,
      gamma 0 = x ∧
        curveVelocityBundle I gamma 0 =
          (⟨x, v⟩ : TangentBundle I M) ∧
        IsCoordGeodesicOn (I := I) g x gamma ({0} : Set Real) := by
  obtain ⟨gamma, hgamma0, hvel, _hspray, _hode, hacc⟩ :=
    exists_local_geodesic_coordZero (I := I) g x v
  refine ⟨gamma, hgamma0, hvel, ?_⟩
  constructor
  · intro t ht
    have ht0 : t = 0 := by simpa using ht
    subst t
    simpa [hgamma0] using coordinateFrameAt_mem (I := I) x
  · intro t ht
    have ht0 : t = 0 := by simpa using ht
    subst t
    simpa using hacc

/-- The relation-valued endpoint exists at time `0`, by the local spray
producer and the checked initial-time coordinate acceleration theorem. -/
theorem coordExp_zero
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    CoordExpRelAtTime (I := I) g x v 0 x := by
  obtain ⟨gamma, hgamma0, hvel, hgeo⟩ :=
    exists_coordGeoAt (I := I) g x v
  refine ⟨({0} : Set Real), ?_, gamma, ?_, ?_⟩
  · intro t ht
    simpa using ht
  · exact ⟨hgamma0, hvel, hgeo⟩
  · simp [hgamma0]

/-- Local coordinate-geodesic existence on a genuine time ball.

The proof uses the chart-fixed spray IVP, shrinks the time ball so the base
projection remains in the original `extChartAt x` chart, and then applies the
fixed-chart scalar ODE bridge from `SprayChartPush.lean` at each time. -/
theorem exists_coordGeoOn
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ epsilon > 0, ∃ gamma : Curve M,
      gamma 0 = x ∧
        curveVelocityBundle I gamma 0 =
          (⟨x, v⟩ : TangentBundle I M) ∧
        IsCoordGeodesicOn (I := I) g x gamma
          (Metric.ball (0 : Real) epsilon) := by
  classical
  obtain ⟨G, -⟩ := exists_localGeodesicIVPAt_leviCivita (I := I) g x v
  let gamma : Curve M := projectCurve (I := I) G.lift
  have hballG : Metric.ball (0 : Real) G.epsilon ∈ 𝓝 (0 : Real) :=
    Metric.ball_mem_nhds _ G.epsilon_pos
  have hf0 : IsMIntegralCurveAt G.lift
      (leviCivitaGeodesicSprayChart (I := I) g x) 0 :=
    G.spray_integral.isMIntegralCurveAt hballG
  have hproj_cont :
      ContinuousAt (fun t : Real => (G.lift t).proj) 0 := by
    exact (FiberBundle.continuous_proj E
      (TangentSpace I : M -> Type _)).continuousAt.comp hf0.continuousAt
  have hsrc_nhds :
      (extChartAtCoordinateData (I := I) x).domain ∈
        𝓝 ((G.lift 0).proj) := by
    simpa [G.lift_initial, extChartAtCoordinateData, coordinateFrameSet,
      coordinateTrivializationAt, extChartAt_source] using
      extChartAt_source_mem_nhds (I := I) x
  have hsrc_event :
      ∀ᶠ t in 𝓝 (0 : Real),
        (G.lift t).proj ∈
          (extChartAtCoordinateData (I := I) x).domain :=
    hproj_cont.preimage_mem_nhds hsrc_nhds
  have hgood :
      Metric.ball (0 : Real) G.epsilon ∩
          {t : Real | (G.lift t).proj ∈
            (extChartAtCoordinateData (I := I) x).domain} ∈
        𝓝 (0 : Real) :=
    Filter.inter_mem hballG hsrc_event
  rw [Metric.mem_nhds_iff] at hgood
  obtain ⟨epsilon, hepsilon, hepsilon_sub⟩ := hgood
  have hsubsetG :
      Metric.ball (0 : Real) epsilon ⊆
        Metric.ball (0 : Real) G.epsilon := by
    intro t ht
    exact (hepsilon_sub ht).1
  have hf_small : IsMIntegralCurveOn G.lift
      (leviCivitaGeodesicSprayChart (I := I) g x)
      (Metric.ball (0 : Real) epsilon) :=
    G.spray_integral.mono hsubsetG
  have hsrc_small :
      ∀ t ∈ Metric.ball (0 : Real) epsilon,
        projectCurve (I := I) G.lift t ∈
          (extChartAtCoordinateData (I := I) x).domain := by
    intro t ht
    simpa [projectCurve] using (hepsilon_sub ht).2
  refine ⟨epsilon, hepsilon, gamma, ?_, ?_, ?_⟩
  · simpa [gamma] using
      projectCurve_zero_of_lift (I := I)
        (u := (⟨x, v⟩ : TangentBundle I M)) G.lift_initial
  · simpa [gamma] using
      projectCurve_initialVelocity_of_geodesicSprayIntegral
        (I := I) (g := g) (u := (⟨x, v⟩ : TangentBundle I M))
        (f := G.lift) G.lift_initial hf0
  · constructor
    · exact hsrc_small
    · intro t ht
      have hode :=
        coordSprayODEOn (I := I) (g := g) (x := x) (v := v)
          (lift := G.lift) (epsilon := epsilon) (t := t)
          G.lift_initial hf_small ht hsrc_small
      exact hode.zeroAccel

/-- Local relation-valued endpoint existence for small times, produced by the
checked local coordinate-geodesic segment theorem. -/
theorem exists_coordExpTime
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ epsilon > 0, ∀ tau ∈ Metric.ball (0 : Real) epsilon,
      ∃ y : M, CoordExpRelAtTime (I := I) g x v tau y := by
  obtain ⟨epsilon, hepsilon, gamma, hgamma0, hvel, hgeo⟩ :=
    exists_coordGeoOn (I := I) g x v
  refine ⟨epsilon, hepsilon, ?_⟩
  intro tau htau
  refine ⟨gamma tau, Metric.ball (0 : Real) epsilon, ?_,
    gamma, ?_, rfl⟩
  · intro s hs
    rw [Metric.mem_ball]
    have hdist : dist (0 : Real) s ≤ dist (0 : Real) tau :=
      Real.dist_left_le_of_mem_uIcc hs
    have htau' : dist (0 : Real) tau < epsilon := by
      simpa [Metric.mem_ball, dist_comm] using htau
    have hdist' : dist s (0 : Real) ≤ dist (0 : Real) tau := by
      simpa [dist_comm] using hdist
    exact hdist'.trans_lt htau'
  · exact ⟨hgamma0, hvel, hgeo⟩

/-! ## Future normal-coordinate package -/

/-- Data that would make the relation-valued endpoint into a normal-coordinate
chart around `x`.

This is a package of future facts, not an existence theorem.  The field
`exp_realizes` keeps the map tied to the relation-valued endpoint above, while
`source_inj` and `target_open` record the local chart facts that should follow
from smooth dependence of the geodesic flow and the inverse function theorem. -/
structure NormalCoordinateData
    (g : SmoothRiemannianMetric I M) (x : M) where
  radius : Real
  radius_pos : 0 < radius
  exp : TangentSpace I x -> M
  exp_zero : exp 0 = x
  exp_realizes :
    ∀ v : TangentSpace I x,
      v ∈ Metric.ball (0 : TangentSpace I x) radius ->
        CoordExpRel (I := I) g x v (exp v)
  source_inj :
    Set.InjOn exp (Metric.ball (0 : TangentSpace I x) radius)
  target_open :
    IsOpen (exp '' Metric.ball (0 : TangentSpace I x) radius)

/-- Topological normal-coordinate data obtained from the strict inverse
function theorem.

This stores the actual local homeomorphism for
`v ↦ extChartAt I x (exp v)`.  It intentionally does not claim that the
corresponding chart is smooth or belongs to the maximal atlas. -/
structure NormalTopChartData
    (g : SmoothRiemannianMetric I M) (x : M) where
  domain : Set (TangentSpace I x)
  domain_open : IsOpen domain
  zero_mem_domain : (0 : TangentSpace I x) ∈ domain
  exp : TangentSpace I x -> M
  exp_zero : exp 0 = x
  chartExp : OpenPartialHomeomorph (TangentSpace I x) (TangentSpace I x)
  domain_subset_source : domain ⊆ chartExp.source
  exp_realizes :
    ∀ v : TangentSpace I x, v ∈ domain -> expAt (I := I) g x v (exp v)
  exp_mem_source :
    ∀ v : TangentSpace I x, v ∈ domain -> exp v ∈ (extChartAt I x).source
  chartExp_eq :
    ∀ v : TangentSpace I x, v ∈ domain -> chartExp v = extChartAt I x (exp v)

namespace NormalTopChartData

/-- Forget the stored topological local homeomorphism to the older endpoint
package by shrinking the open tangent-domain to a metric ball. -/
def toNormalCoordinateData
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : NormalTopChartData (I := I) g x) :
    NormalCoordinateData (I := I) g x := by
  have hnhds : N.domain ∈ 𝓝 (0 : TangentSpace I x) :=
    N.domain_open.mem_nhds N.zero_mem_domain
  rw [Metric.mem_nhds_iff] at hnhds
  let r : Real := Classical.choose hnhds
  have hr : 0 < r := (Classical.choose_spec hnhds).1
  have hrsub :
      Metric.ball (0 : TangentSpace I x) r ⊆ N.domain :=
    (Classical.choose_spec hnhds).2
  let B : Set (TangentSpace I x) := Metric.ball (0 : TangentSpace I x) r
  have hBsub_source : B ⊆ N.chartExp.source := fun v hv =>
    N.domain_subset_source (hrsub hv)
  have hsrc_exp : ∀ v ∈ B, N.exp v ∈ (extChartAt I x).source := by
    intro v hv
    exact N.exp_mem_source v (hrsub hv)
  have hchartOpen : IsOpen (N.chartExp '' B) :=
    N.chartExp.isOpen_image_of_subset_source Metric.isOpen_ball hBsub_source
  have htargetOpen : IsOpen (N.exp '' B) := by
    have hpreOpen :
        IsOpen ((extChartAt I x).source ∩
          (extChartAt I x) ⁻¹' (N.chartExp '' B)) := by
      rw [extChartAt]
      exact (chartAt H x).isOpen_extend_preimage' (I := I) hchartOpen
    have himage :
        N.exp '' B =
          (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' (N.chartExp '' B) := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨hsrc_exp v hv, v, hv, N.chartExp_eq v (hrsub hv)⟩
      · rintro ⟨hy_src, v, hv, h_eq⟩
        refine ⟨v, hv, ?_⟩
        apply (extChartAt I x).injOn (hsrc_exp v hv) hy_src
        simpa [N.chartExp_eq v (hrsub hv)] using h_eq
    simpa [B, himage] using hpreOpen
  refine {
    radius := r
    radius_pos := hr
    exp := N.exp
    exp_zero := N.exp_zero
    exp_realizes := ?_
    source_inj := ?_
    target_open := ?_
  }
  · intro v hv
    exact (expAt_iff (I := I) g x v (N.exp v)).1 (N.exp_realizes v (hrsub hv))
  · intro v hv w hw h_eq
    have hvN : v ∈ N.domain := hrsub hv
    have hwN : w ∈ N.domain := hrsub hw
    apply N.chartExp.injOn (N.domain_subset_source hvN) (N.domain_subset_source hwN)
    rw [N.chartExp_eq v hvN, N.chartExp_eq w hwN]
    exact congrArg (fun y : M => extChartAt I x y) h_eq
  · simpa [B] using htargetOpen

end NormalTopChartData

/-- C1 chart-level local diffeomorphism data for the chart-pushed exponential
endpoint.

This is intentionally still in fixed tangent coordinates. It upgrades the
topological inverse-function skeleton to a genuine `PartialDiffeomorph` of
model tangent spaces at regularity `1`, but it does not claim the final smooth
manifold-valued exponential `PartialDiffeomorph`. -/
structure NormalC1ChartData
    (g : SmoothRiemannianMetric I M) (x : M) where
  exp : TangentSpace I x -> M
  exp_zero : exp 0 = x
  chartLD :
    PartialDiffeomorph
      (modelWithCornersSelf Real (TangentSpace I x))
      (modelWithCornersSelf Real (TangentSpace I x))
      (TangentSpace I x) (TangentSpace I x) (1 : WithTop ℕ∞)
  zero_mem_source : (0 : TangentSpace I x) ∈ chartLD.source
  exp_realizes :
    ∀ v : TangentSpace I x, v ∈ chartLD.source -> expAt (I := I) g x v (exp v)
  exp_mem_source :
    ∀ v : TangentSpace I x, v ∈ chartLD.source -> exp v ∈ (extChartAt I x).source
  chartLD_eq :
    ∀ v : TangentSpace I x, v ∈ chartLD.source -> chartLD v = extChartAt I x (exp v)

namespace NormalC1ChartData

/-- Forget C1 chart-level local-diffeomorphism data to the topological chart
package. -/
def toTopChartData
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : NormalC1ChartData (I := I) g x) :
    NormalTopChartData (I := I) g x where
  domain := N.chartLD.source
  domain_open := N.chartLD.open_source
  zero_mem_domain := N.zero_mem_source
  exp := N.exp
  exp_zero := N.exp_zero
  chartExp := N.chartLD.toOpenPartialHomeomorph
  domain_subset_source := by
    intro v hv
    simpa using hv
  exp_realizes := N.exp_realizes
  exp_mem_source := N.exp_mem_source
  chartExp_eq := by
    intro v hv
    simpa using N.chartLD_eq v hv

end NormalC1ChartData

/-- C1 manifold-valued local diffeomorphism data for the exponential endpoint.

This is the C1 analogue of the deferred smooth exponential
local-diffeomorphism frontier.  It is useful for the inverse-function skeleton
and for comparison with the reference `expMapPartialDiffeomorph` construction,
but it deliberately does not claim the final smooth normal chart. -/
structure NormalC1ExpData
    (g : SmoothRiemannianMetric I M) (x : M) where
  expLD :
    PartialDiffeomorph
      (modelWithCornersSelf Real (TangentSpace I x)) I
      (TangentSpace I x) M (1 : WithTop ℕ∞)
  zero_mem_source : (0 : TangentSpace I x) ∈ expLD.source
  map_zero : expLD 0 = x
  expAt_realizes :
    ∀ v : TangentSpace I x, v ∈ expLD.source -> expAt (I := I) g x v (expLD v)

namespace NormalC1ExpData

/-- Forget C1 manifold-valued exponential local-diffeomorphism data to the old
relation-valued endpoint package by shrinking the source to a metric ball. -/
def toNormalCoordinateData
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalC1ExpData (I := I) g x) :
    NormalCoordinateData (I := I) g x := by
  have hnhds : D.expLD.source ∈ 𝓝 (0 : TangentSpace I x) :=
    D.expLD.open_source.mem_nhds D.zero_mem_source
  rw [Metric.mem_nhds_iff] at hnhds
  let r : Real := Classical.choose hnhds
  have hr : 0 < r := (Classical.choose_spec hnhds).1
  have hrsub :
      Metric.ball (0 : TangentSpace I x) r ⊆ D.expLD.source :=
    (Classical.choose_spec hnhds).2
  let expHomeomorph := D.expLD.toOpenPartialHomeomorph
  refine {
    radius := r
    radius_pos := hr
    exp := D.expLD
    exp_zero := D.map_zero
    exp_realizes := ?_
    source_inj := ?_
    target_open := ?_
  }
  · intro v hv
    exact (expAt_iff (I := I) g x v (D.expLD v)).1 (D.expAt_realizes v (hrsub hv))
  · intro v hv w hw h_eq
    exact expHomeomorph.injOn (hrsub hv) (hrsub hw) h_eq
  · exact expHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hrsub

/-- The C1 exponential package is a local diffeomorphism at the zero tangent
vector. -/
theorem localDiffAt
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalC1ExpData (I := I) g x) :
    IsLocalDiffeomorphAt
      (modelWithCornersSelf Real (TangentSpace I x)) I
      (1 : WithTop ℕ∞) D.expLD (0 : TangentSpace I x) :=
  PartialDiffeomorph.isLocalDiffeomorphAt
    (I := modelWithCornersSelf Real (TangentSpace I x)) (J := I)
    (n := (1 : WithTop ℕ∞)) D.expLD D.zero_mem_source

end NormalC1ExpData

namespace NormalC1ChartData

/-- Upgrade the C1 chart-pushed endpoint local diffeomorphism to a C1
manifold-valued exponential local diffeomorphism by transporting the target
through the construction chart `extChartAt I x`. -/
def toC1ExpData
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : NormalC1ChartData (I := I) g x) :
    NormalC1ExpData (I := I) g x := by
  classical
  let target : Set M :=
    (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' N.chartLD.target
  let inv : M -> TangentSpace I x :=
    fun y => N.chartLD.symm (extChartAt I x y)
  let expLD :
      PartialDiffeomorph
        (modelWithCornersSelf Real (TangentSpace I x)) I
        (TangentSpace I x) M (1 : WithTop ℕ∞) := {
    toFun := N.exp
    invFun := inv
    source := N.chartLD.source
    target := target
    map_source' := by
      intro v hv
      refine ⟨N.exp_mem_source v hv, ?_⟩
      change extChartAt I x (N.exp v) ∈ N.chartLD.target
      rw [← N.chartLD_eq v hv]
      exact N.chartLD.map_source hv
    map_target' := by
      intro y hy
      exact N.chartLD.map_target hy.2
    left_inv' := by
      intro v hv
      change N.chartLD.symm (extChartAt I x (N.exp v)) = v
      rw [← N.chartLD_eq v hv]
      exact N.chartLD.left_inv hv
    right_inv' := by
      intro y hy
      have hinv_src : inv y ∈ N.chartLD.source := N.chartLD.map_target hy.2
      apply (extChartAt I x).injOn (N.exp_mem_source (inv y) hinv_src) hy.1
      have hright : N.chartLD (inv y) = extChartAt I x y := by
        exact N.chartLD.right_inv hy.2
      rw [← N.chartLD_eq (inv y) hinv_src]
      exact hright
    open_source := N.chartLD.open_source
    open_target := by
      simpa [target] using
        isOpen_extChartAt_preimage' (I := I) (x := x) N.chartLD.open_target
    contMDiffOn_toFun := by
      let extTarget : Set (TangentSpace I x) := (extChartAt I x).target
      let symmT : TangentSpace I x -> M := fun w => (extChartAt I x).symm w
      let candidate : TangentSpace I x -> M :=
        fun v => symmT (N.chartLD v)
      have hchart_maps :
          ∀ v, v ∈ N.chartLD.source -> N.chartLD v ∈ extTarget := by
        intro v hv
        rw [N.chartLD_eq v hv]
        exact (extChartAt I x).map_source (N.exp_mem_source v hv)
      have hsymmT : ContMDiffOn
          (modelWithCornersSelf Real (TangentSpace I x)) I
          (1 : WithTop ℕ∞) symmT extTarget := by
        change ContMDiffOn (modelWithCornersSelf Real E) I
          (1 : WithTop ℕ∞) (extChartAt I x).symm (extChartAt I x).target
        exact contMDiffOn_extChartAt_symm (I := I) (x := x) (n := (1 : WithTop ℕ∞))
      have hcand : ContMDiffOn
          (modelWithCornersSelf Real (TangentSpace I x)) I
          (1 : WithTop ℕ∞) candidate N.chartLD.source := by
        exact hsymmT.comp N.chartLD.contMDiffOn_toFun hchart_maps
      exact hcand.congr (by
        intro v hv
        change N.exp v = (extChartAt I x).symm (N.chartLD v)
        rw [N.chartLD_eq v hv]
        exact ((extChartAt I x).left_inv (N.exp_mem_source v hv)).symm)
    contMDiffOn_invFun := by
      let extT : M -> TangentSpace I x := fun y => extChartAt I x y
      have hext : ContMDiffOn I
          (modelWithCornersSelf Real (TangentSpace I x))
          (1 : WithTop ℕ∞) extT target := by
        change ContMDiffOn I (modelWithCornersSelf Real E)
          (1 : WithTop ℕ∞) (extChartAt I x) target
        exact (contMDiffOn_extChartAt (I := I) (x := x) (n := (1 : WithTop ℕ∞))).mono
          (by
            intro y hy
            simpa [extChartAt_source] using hy.1)
      have hmaps : ∀ y, y ∈ target -> extT y ∈ N.chartLD.target := by
        intro y hy
        exact hy.2
      exact N.chartLD.contMDiffOn_invFun.comp hext hmaps
  }
  refine {
    expLD := expLD
    zero_mem_source := ?_
    map_zero := ?_
    expAt_realizes := ?_
  }
  · simpa [expLD] using N.zero_mem_source
  · simpa [expLD] using N.exp_zero
  · intro v hv
    exact N.exp_realizes v hv

end NormalC1ChartData

/-- The strict inverse-function theorem applied to the endpoint map, retaining
the resulting topological local homeomorphism in tangent coordinates. -/
theorem expAt_topChart
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalTopChartData (I := I) g x) := by
  classical
  obtain ⟨r0, hr0, exp, hexp0, hreal, hstrict⟩ :=
    expAt_strict (I := I) g x
  let chartExp : TangentSpace I x -> TangentSpace I x :=
    fun v => extChartAt I x (exp v)
  let eIso : TangentSpace I x ≃L[Real] TangentSpace I x :=
    ContinuousLinearEquiv.refl Real (TangentSpace I x)
  have hstrictIso :
      HasStrictFDerivAt chartExp (eIso : TangentSpace I x →L[Real] TangentSpace I x)
        (0 : TangentSpace I x) := by
    simpa [chartExp, eIso] using hstrict
  let eIFT := hstrictIso.toOpenPartialHomeomorph chartExp
  have hIFTsrc : (0 : TangentSpace I x) ∈ eIFT.source := by
    simpa [eIFT] using hstrictIso.mem_toOpenPartialHomeomorph_source
  refine ⟨{
    domain := Metric.ball (0 : TangentSpace I x) r0 ∩ eIFT.source
    domain_open := Metric.isOpen_ball.inter eIFT.open_source
    zero_mem_domain := ?_
    exp := exp
    exp_zero := hexp0
    chartExp := eIFT
    domain_subset_source := ?_
    exp_realizes := ?_
    exp_mem_source := ?_
    chartExp_eq := ?_
  }⟩
  · exact ⟨Metric.mem_ball_self hr0, hIFTsrc⟩
  · intro v hv
    exact hv.2
  · intro v hv
    exact hreal v hv.1
  · intro v hv
    have hcoord : exp v ∈ coordinateFrameSet (I := I) x :=
      expAt_mem_source (I := I) (hreal v hv.1)
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hcoord
  · intro v hv
    simp [eIFT, chartExp]

/-- C1 chart-level local diffeomorphism supplied by the variational-flow
endpoint and the C1 inverse-function theorem. -/
theorem expAt_c1Chart
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalC1ChartData (I := I) g x) := by
  classical
  obtain ⟨R, hR, τ, _hτ, Ψ, hexp0, hreal, hchart, hC1, hderiv⟩ :=
    exists_varFlow_c1_endpoint (I := I) g x
  let exp : TangentSpace I x -> M :=
    manifoldEnd (I := I) (varModelFlow (E := E) Ψ) τ x
  let chartExp : TangentSpace I x -> TangentSpace I x :=
    chartEnd (I := I) (varModelFlow (E := E) Ψ) τ x
  let eIso : TangentSpace I x ≃L[Real] TangentSpace I x :=
    ContinuousLinearEquiv.refl Real (TangentSpace I x)
  have hderivIso :
      HasFDerivAt chartExp (eIso : TangentSpace I x →L[Real] TangentSpace I x)
        (0 : TangentSpace I x) := by
    simpa [chartExp, eIso] using hderiv
  let eIFT : OpenPartialHomeomorph (TangentSpace I x) (TangentSpace I x) :=
    ContDiffAt.toOpenPartialHomeomorph (𝕂 := Real)
      (f := chartExp) (f' := eIso) hC1 hderivIso one_ne_zero
  have hIFTsrc : (0 : TangentSpace I x) ∈ eIFT.source := by
    simpa [eIFT] using
      ContDiffAt.mem_toOpenPartialHomeomorph_source hC1 hderivIso one_ne_zero
  obtain ⟨uF, huF_nhds, hF_on⟩ :=
    hC1.contDiffOn (m := (1 : WithTop ℕ∞)) le_rfl (by simp)
  rcases mem_nhds_iff.mp huF_nhds with
    ⟨uOpen, huOpen_sub, huOpen_isOpen, h0uOpen⟩
  have hinvAt :
      ContDiffAt Real 1 eIFT.symm (chartExp (0 : TangentSpace I x)) := by
    simpa [eIFT, ContDiffAt.localInverse] using
      hC1.to_localInverse hderivIso one_ne_zero
  obtain ⟨uInv, huInv_nhds, hInv_on⟩ :=
    hinvAt.contDiffOn (m := (1 : WithTop ℕ∞)) le_rfl (by simp)
  rcases mem_nhds_iff.mp huInv_nhds with
    ⟨wOpen, hwOpen_sub, hwOpen_isOpen, h0wOpen⟩
  let s : Set (TangentSpace I x) :=
    Metric.ball (0 : TangentSpace I x) R ∩
      (uOpen ∩ (eIFT.source ∩ eIFT ⁻¹' wOpen))
  have hsOpen : IsOpen s := by
    exact Metric.isOpen_ball.inter
      (huOpen_isOpen.inter (eIFT.isOpen_inter_preimage hwOpen_isOpen))
  have hsSubSource : s ⊆ eIFT.source := by
    intro v hv
    exact hv.2.2.1
  have hsSubBall :
      s ⊆ Metric.ball (0 : TangentSpace I x) R := by
    intro v hv
    exact hv.1
  have hsSubF : s ⊆ uF := by
    intro v hv
    exact huOpen_sub hv.2.1
  have htargetSubW : eIFT '' s ⊆ wOpen := by
    rintro y ⟨v, hv, rfl⟩
    exact hv.2.2.2
  have hforward :
      ContMDiffOn
        (modelWithCornersSelf Real (TangentSpace I x))
        (modelWithCornersSelf Real (TangentSpace I x))
        (1 : WithTop ℕ∞) eIFT s := by
    have hf : ContDiffOn Real 1 eIFT s := by
      simpa [eIFT, chartExp] using hF_on.mono hsSubF
    exact hf.contMDiffOn
  have hinverse :
      ContMDiffOn
        (modelWithCornersSelf Real (TangentSpace I x))
        (modelWithCornersSelf Real (TangentSpace I x))
        (1 : WithTop ℕ∞) eIFT.symm (eIFT '' s) := by
    have hi : ContDiffOn Real 1 eIFT.symm (eIFT '' s) :=
      hInv_on.mono fun y hy => hwOpen_sub (htargetSubW hy)
    exact hi.contMDiffOn
  let chartLD :
      PartialDiffeomorph
        (modelWithCornersSelf Real (TangentSpace I x))
        (modelWithCornersSelf Real (TangentSpace I x))
        (TangentSpace I x) (TangentSpace I x) (1 : WithTop ℕ∞) :=
    PartialDiffeomorph.ofOpenPartialHomeomorphRestr
      (I := modelWithCornersSelf Real (TangentSpace I x))
      (J := modelWithCornersSelf Real (TangentSpace I x))
      eIFT s hsOpen hsSubSource hforward hinverse
  have h0s : (0 : TangentSpace I x) ∈ s := by
    refine ⟨Metric.mem_ball_self hR, ⟨h0uOpen, ⟨hIFTsrc, ?_⟩⟩⟩
    simpa [eIFT, chartExp] using h0wOpen
  refine ⟨{
    exp := exp
    exp_zero := by simpa [exp] using hexp0
    chartLD := chartLD
    zero_mem_source := ?_
    exp_realizes := ?_
    exp_mem_source := ?_
    chartLD_eq := ?_
  }⟩
  · simpa [chartLD, PartialDiffeomorph.ofOpenPartialHomeomorphRestr] using h0s
  · intro v hv
    have hvs : v ∈ s := by
      simpa [chartLD, PartialDiffeomorph.ofOpenPartialHomeomorphRestr] using hv
    simpa [exp] using hreal v (hsSubBall hvs)
  · intro v hv
    have hvs : v ∈ s := by
      simpa [chartLD, PartialDiffeomorph.ofOpenPartialHomeomorphRestr] using hv
    have hcoord : exp v ∈ coordinateFrameSet (I := I) x :=
      expAt_mem_source (I := I) (hreal v (hsSubBall hvs))
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source, exp] using hcoord
  · intro v hv
    have hvs : v ∈ s := by
      simpa [chartLD, PartialDiffeomorph.ofOpenPartialHomeomorphRestr] using hv
    have hchartv :
        extChartAt I x (exp v) = chartExp v := by
      simpa [exp, chartExp] using hchart v (hsSubBall hvs)
    calc
      chartLD v = eIFT v := rfl
      _ = chartExp v := by simp [eIFT, chartExp]
      _ = extChartAt I x (exp v) := hchartv.symm

/-- C1 manifold-valued local diffeomorphism supplied by the variational-flow
endpoint and the C1 inverse-function theorem. -/
theorem expAt_c1Exp
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalC1ExpData (I := I) g x) := by
  obtain ⟨N⟩ := expAt_c1Chart (I := I) g x
  exact ⟨N.toC1ExpData (I := I)⟩

/-- C1 local-diffeomorphism form of the checked variational-flow endpoint.

This is the current theorem-facing endpoint API: it gives a functional local
exponential map near `0`, proves it is a `C1` local diffeomorphism at `0`, and
records that it realizes the relation-valued endpoint API on a neighborhood of
`0`.  The `C-infinity` version is deferred to
`Coordinates.Normal.Frontier.SmoothChart`. -/
theorem expAt_c1LocalDiff
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ exp : TangentSpace I x -> M,
      exp 0 = x ∧
      IsLocalDiffeomorphAt
        (modelWithCornersSelf Real (TangentSpace I x)) I
        (1 : WithTop ℕ∞) exp (0 : TangentSpace I x) ∧
      ∀ᶠ v : TangentSpace I x in 𝓝 0, expAt (I := I) g x v (exp v) := by
  obtain ⟨D⟩ := expAt_c1Exp (I := I) g x
  refine ⟨D.expLD, D.map_zero, D.localDiffAt (I := I), ?_⟩
  filter_upwards [D.expLD.open_source.mem_nhds D.zero_mem_source] with v hv
  exact D.expAt_realizes v hv

/-- C1 variational-flow version of the topological local inverse-function
skeleton.

This consumes the checked projected variational-flow endpoint rather than the
older `expAt_strict` theorem.  It still stops at `NormalTopChartData`: a C1
inverse-function theorem gives a local homeomorphism in tangent coordinates,
but not the `C∞` partial diffeomorphism needed for smooth normal charts. -/
theorem expAt_c1TopChart
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalTopChartData (I := I) g x) := by
  obtain ⟨N⟩ := expAt_c1Chart (I := I) g x
  exact ⟨N.toTopChartData (I := I)⟩

/-- The topological local inverse-function skeleton supplied by
`expAt_strict`.

This deliberately stops at the older endpoint package: strict differentiability
at the center gives local injectivity and open image, but not smooth maximal
atlas membership for the normal chart. -/
theorem expAt_topData
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalCoordinateData (I := I) g x) := by
  obtain ⟨N⟩ := expAt_topChart (I := I) g x
  exact ⟨N.toNormalCoordinateData (I := I)⟩

/-- C1 variational-flow route to the older relation-valued normal-coordinate
package.  This is still only the compatibility view: the smooth
`PartialDiffeomorph` normal chart remains isolated in the frontier module. -/
theorem expAt_c1TopData
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalCoordinateData (I := I) g x) := by
  obtain ⟨N⟩ := expAt_c1Exp (I := I) g x
  exact ⟨N.toNormalCoordinateData (I := I)⟩

/-- Compatibility existence for the older relation-valued package.

This uses the C1 variational-flow topological skeleton; the smooth normal-chart
frontier is kept outside the default normal-coordinate import path. -/
theorem exists_normalData
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalCoordinateData (I := I) g x) := by
  exact expAt_c1TopData (I := I) g x


end Coordinates
end RicciFlower
