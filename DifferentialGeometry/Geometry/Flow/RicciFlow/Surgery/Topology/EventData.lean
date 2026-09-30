import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WeakLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalCoordinate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Basic
import DifferentialGeometry.Geometry.Metric.Convergence.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u


def standardCapRho (r : ℝ) : ℝ := if r ≤ 0 then 0 else Real.exp (-1 / r)


def standardCapEta (r : ℝ) : ℝ :=
  standardCapRho (1 - r) / (standardCapRho r + standardCapRho (1 - r))


def standardCapA0 : ℝ := Real.pi / Real.sqrt 2 - 1 / 2

def standardCapL : ℝ := standardCapA0 + 1

theorem standardCapL_eq_transitionEnd :
    standardCapL = DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd := rfl


def standardCapAngle (r : ℝ) : ℝ :=
  (Real.sqrt 2)⁻¹ * ∫ u in (0 : ℝ)..r, standardCapEta (u - standardCapA0)

def standardCapWarp (r : ℝ) : ℝ := Real.sqrt 2 * Real.sin (standardCapAngle r)

def standardCapInner (x v w : ThreeSpace) : ℝ :=
  if x = 0 then ⟪v, w⟫_ℝ else
    (standardCapWarp ‖x‖ / ‖x‖) ^ 2 * ⟪v, w⟫_ℝ +
      (1 - (standardCapWarp ‖x‖ / ‖x‖) ^ 2) * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ / ‖x‖ ^ 2

private theorem standardCapRho_eq_expNegInvGlue (r : ℝ) : standardCapRho r = expNegInvGlue r := by
  by_cases hr : r ≤ 0
  · simp [standardCapRho, expNegInvGlue, hr]
  · simp only [standardCapRho, expNegInvGlue, ite_eq_right hr]
    congr 1
    ring

private theorem standardCapEta_eq_smoothTransition (x : ℝ) :
    standardCapEta x = Real.smoothTransition (1 - x) := by
  simp only [standardCapEta, Real.smoothTransition, standardCapRho_eq_expNegInvGlue,
    sub_sub_cancel]
  rw [add_comm]

private theorem standardCapAngle_eq (r : ℝ) :
    standardCapAngle r = DifferentialGeometry.PDE.RicciFlow.StandardCap.angle r := by
  have h1 : (∫ u in (0 : ℝ)..r, standardCapEta (u - standardCapA0)) =
      (∫ u in (0 : ℝ)..r,
        Real.smoothTransition
          (DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd - u)) := by
    apply intervalIntegral.integral_congr
    intro u _
    change standardCapEta (u - standardCapA0) =
      Real.smoothTransition
        (DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd - u)
    rw [standardCapEta_eq_smoothTransition]
    congr 1
    simp only [standardCapA0,
      DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionStart,
      DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd]
    ring
  simp only [standardCapAngle, DifferentialGeometry.PDE.RicciFlow.StandardCap.angle, one_div]
  rw [h1]

private theorem standardCapWarp_eq_warpingFunction (r : ℝ) :
    standardCapWarp r = DifferentialGeometry.PDE.RicciFlow.StandardCap.warpingFunction r := by
  simp only [standardCapWarp, DifferentialGeometry.PDE.RicciFlow.StandardCap.warpingFunction,
    standardCapAngle_eq]

theorem exists_unique_standardCapMetric :
    ∃! g : SmoothRiemannianMetric ThreeModel ThreeSpace,
      ∀ x v w : ThreeSpace, g.inner x v w = standardCapInner x v w := by
  have hinner : ∀ (x v w : ThreeSpace),
      (DifferentialGeometry.PDE.RicciFlow.StandardCap.metric).inner x v w =
        standardCapInner x v w := by
    intro x v w
    by_cases hx : x = 0
    · subst x
      rw [DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_inner_zero, standardCapInner,
        ite_eq_left rfl]
    · rw [DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_inner_of_ne_zero hx,
        standardCapInner, ite_eq_right hx]
      rw [DifferentialGeometry.Geometry.Riemannian.radialBilinearField_apply]
      simp only [standardCapWarp_eq_warpingFunction]
      field_simp
  exact ⟨DifferentialGeometry.PDE.RicciFlow.StandardCap.metric, hinner, fun g' hg' =>
    SmoothRiemannianMetric.ext_inner fun x v w => (hg' x v w).trans (hinner x v w).symm⟩

def standardCapMetric : SmoothRiemannianMetric ThreeModel ThreeSpace :=
  Classical.choose exists_unique_standardCapMetric

theorem standardCapMetric_inner (x v w : ThreeSpace) :
    standardCapMetric.inner x v w = standardCapInner x v w :=
  (Classical.choose_spec exists_unique_standardCapMetric).1 x v w

def standardCapConformalCoordinate (r : Ioi (0 : ℝ)) : ℝ :=
  ∫ u in standardCapL..r.1, Real.sqrt 2 / standardCapWarp u

theorem standardCapConformalCoordinate_eq_conformalCoordinate (r : Ioi (0 : ℝ)) :
    standardCapConformalCoordinate r =
      DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalCoordinate r.1 := by
  simp only [standardCapConformalCoordinate,
    DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalCoordinate, standardCapL,
    standardCapA0, DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd,
    DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionStart, div_eq_mul_inv]
  simp only [standardCapWarp_eq_warpingFunction]
  rw [intervalIntegral.integral_const_mul]

theorem standardCapConformalCoordinate_bijective :
    Function.Bijective standardCapConformalCoordinate := by
  constructor
  · intro a b hab
    apply Subtype.ext
    rw [standardCapConformalCoordinate_eq_conformalCoordinate a,
      standardCapConformalCoordinate_eq_conformalCoordinate b] at hab
    exact DifferentialGeometry.PDE.RicciFlow.StandardCap.strictMonoOn_conformalCoordinate.injOn
      a.2 b.2 hab
  · intro y
    refine ⟨⟨DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalRadius y,
      DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalRadius_pos y⟩, ?_⟩
    rw [standardCapConformalCoordinate_eq_conformalCoordinate,
      DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalCoordinate_conformalRadius]


def standardCapRadiusOfZ (z : ℝ) : ℝ :=
  (Function.invFun standardCapConformalCoordinate z).1

theorem standardCapRadiusOfZ_eq_conformalRadius (z : ℝ) :
    standardCapRadiusOfZ z = DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalRadius z := by
  let r : Ioi (0 : ℝ) :=
    ⟨DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalRadius z,
      DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalRadius_pos z⟩
  have hr : standardCapConformalCoordinate r = z := by
    rw [standardCapConformalCoordinate_eq_conformalCoordinate]
    exact DifferentialGeometry.PDE.RicciFlow.StandardCap.conformalCoordinate_conformalRadius z
  have he : Function.invFun standardCapConformalCoordinate z = r := by
    apply standardCapConformalCoordinate_bijective.injective
    rw [Function.rightInverse_invFun standardCapConformalCoordinate_bijective.surjective, hr]
  exact congrArg Subtype.val he

structure OrientedThreeStage where
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charts : ChartedSpace ThreeSpace Carrier]
  [smooth : IsManifold ThreeModel ∞ Carrier]
  [hausdorff : T2Space Carrier]
  [compact : CompactSpace Carrier]
  orientation : TangentOrientationSection Carrier

attribute [instance] OrientedThreeStage.topology OrientedThreeStage.charts
  OrientedThreeStage.smooth OrientedThreeStage.hausdorff OrientedThreeStage.compact

namespace OrientedThreeStage


abbrev Metric (P : OrientedThreeStage.{u}) := SmoothRiemannianMetric ThreeModel P.Carrier

def chartVector (P : OrientedThreeStage.{u}) (p x : P.Carrier) (i : Fin 3) :
    TangentSpace ThreeModel x :=
  (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).symmL ℝ x
    (EuclideanSpace.single i (1 : ℝ))

def MetricSmoothUpTo (P : OrientedThreeStage.{u}) (g : ℝ → P.Metric) (J : Set ℝ) : Prop :=
  ∀ p : P.Carrier, ∀ t ∈ J,
    ∃ U : Set P.Carrier, IsOpen U ∧ p ∈ U ∧
      U ⊆ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet ∧
      ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∃ A : ℝ × P.Carrier → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j : Fin 3, ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
          𝓘(ℝ, ℝ) ∞ (fun z => A z i j) (V ×ˢ U)) ∧
        ∀ s ∈ V ∩ J, ∀ x ∈ U, ∀ i j : Fin 3,
          A (s, x) i j = (g s).inner x (P.chartVector p x i) (P.chartVector p x j)

structure IncomingSlab (P : OrientedThreeStage.{u}) (a s : ℝ) where
  lt : a < s
  flow : SolutionOn (I := ThreeModel) (M := P.Carrier) (RealTimeInterval.closedOpen a s lt)
  equation : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn flow
  smoothUpTo : P.MetricSmoothUpTo flow.base.metric (Ico a s)

structure ClosedSlab (P : OrientedThreeStage.{u}) (a b : ℝ) where
  lt : a < b
  flow : SolutionOn (I := ThreeModel) (M := P.Carrier) (RealTimeInterval.closed a b lt.le)
  equation : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn flow
  smoothUpTo : P.MetricSmoothUpTo flow.base.metric (Icc a b)

namespace IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)


def riemannNorm (t : ℝ) (x : P.Carrier) : ℝ :=
  Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (G.flow.base.rm04 t x))

def terminalRegularRegion : Set P.Carrier :=
  {x | ∃ U : Set P.Carrier, IsOpen U ∧ x ∈ U ∧
    ∃ a' ∈ Ico a s, ∃ K : ℝ, 0 ≤ K ∧
      ∀ y ∈ U, ∀ t ∈ Ico a' s, G.riemannNorm t y ≤ K}


theorem terminalRegularRegion_isOpen : IsOpen G.terminalRegularRegion := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨U, hU, hxU, a', ha', K, hK, hbound⟩
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy
  exact ⟨U, hU, hy, a', ha', K, hK, hbound⟩


def terminalRegularOpen : TopologicalSpace.Opens P.Carrier :=
  ⟨G.terminalRegularRegion, G.terminalRegularRegion_isOpen⟩

def TerminalMetricConverges
    (gbar : SmoothRiemannianMetric ThreeModel G.terminalRegularOpen) : Prop :=
  letI : SecondCountableTopology P.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  letI : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace G.terminalRegularOpen
  ∀ K : Set G.terminalRegularOpen, IsCompact K → ∀ j : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s, ∀ x ∈ K,
      DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm j
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) gbar gbar x < ε

structure TerminalLimitMetric where
  metric : SmoothRiemannianMetric ThreeModel G.terminalRegularOpen
  converges : G.TerminalMetricConverges metric

def SingularEndpoint : Prop :=
  ∀ L : ℝ, 0 < L → ∀ d ∈ Ico a s, ∃ t ∈ Ioo d s,
    ∃ x : P.Carrier, L < G.riemannNorm t x

end IncomingSlab
end OrientedThreeStage

structure SmoothCutCapTransition (P Q D N : OrientedThreeStage.{u}) where
  trace : CutCapTopology P.Carrier Q.Carrier D.Carrier N.Carrier
  source_nonempty : Nonempty P.Carrier
  tube_smooth :
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    ∀ a : trace.tubes.Index,
      IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (trace.tubes.tube a)
  [coreCharts : ChartedSpace (EuclideanHalfSpace 3) trace.tubes.core]
  [coreSmooth : IsManifold (𝓡∂ 3) ∞ trace.tubes.core]
  core_induced : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
    (Subtype.val : trace.tubes.core → P.Carrier)
  core_boundary : (𝓡∂ 3).boundary trace.tubes.core =
    ⋃ b : trace.tubes.Boundary, Set.range (trace.tubes.coreBoundarySphere b)
  core_inclusion_smooth : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ trace.capping.coreInclusion
  [ballCharts : ChartedSpace (EuclideanHalfSpace 3) ThreeBall]
  [ballSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall]
  ball_induced : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (Subtype.val : ThreeBall → ThreeSpace)
  ball_boundary : (𝓡∂ 3).boundary ThreeBall = Set.range sphereToThreeBall
  cap_smooth : ∀ b, IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (trace.capping.cap b)
  attaching : ∀ _b : trace.tubes.Boundary, Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2
  attaching_eq : ∀ b, (attaching b : Sphere 2 → Sphere 2) = trace.capping.attaching b
  core_positive : ∀ x : trace.tubes.core, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : trace.tubes.core → P.Carrier) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel trace.capping.coreInclusion x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : trace.tubes.core → P.Carrier) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective
            (mfderiv (𝓡∂ 3) ThreeModel trace.capping.coreInclusion x).toLinearMap hj))
        (P.orientation.orientation x.1) =
          N.orientation.orientation (trace.capping.coreInclusion x)
  cap_positive : ∀ b, ∀ x : ThreeBall, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : ThreeBall → ThreeSpace) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel (trace.capping.cap b) x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective
            (mfderiv (𝓡∂ 3) ThreeModel (trace.capping.cap b) x).toLinearMap hj))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
          (if b.2 then (1 : ℝˣ) else -1) • N.orientation.orientation (trace.capping.cap b x)
  presentation : N.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ (Q.Carrier ⊕ D.Carrier)
  presentation_eq : (presentation : N.Carrier → Q.Carrier ⊕ D.Carrier) = trace.presentation
  presentation_positive : ∀ x : N.Carrier,
    ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel presentation x),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel presentation x).toLinearMap hf)
        (N.orientation.orientation x) =
          match presentation x with
          | Sum.inl q => Q.orientation.orientation q
          | Sum.inr d => D.orientation.orientation d

structure MetricCutCapEvent (P Q : OrientedThreeStage.{u}) (a s : ℝ) where
  discarded : OrientedThreeStage.{u}
  capped : OrientedThreeStage.{u}
  transition : SmoothCutCapTransition P Q discarded capped
  incoming : P.IncomingSlab a s
  terminal : incoming.TerminalLimitMetric
  outputMetric : Q.Metric
  old : Set transition.trace.tubes.core
  old_compact : IsCompact old
  old_retained : old ⊆ transition.trace.retainedCore
  [oldCharts : ChartedSpace (EuclideanHalfSpace 3) old]
  [oldSmooth : IsManifold (𝓡∂ 3) ∞ old]
  old_induced : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
    (fun x : old => (x.1.1 : P.Carrier))
  oldTerminal : C(old, incoming.terminalRegularOpen)
  oldTerminal_eq : ∀ x : old, (oldTerminal x).1 = x.1.1
  oldOutput : C(old, Q.Carrier)
  oldOutput_eq : ∀ x : old,
    transition.trace.presentation (transition.trace.capping.coreInclusion x.1) =
      Sum.inl (oldOutput x)
  old_metric_eq : ∀ x : old, ∀ v w : TangentSpace (𝓡∂ 3) x,
    terminal.metric.inner (oldTerminal x)
        (mfderiv (𝓡∂ 3) ThreeModel oldTerminal x v)
        (mfderiv (𝓡∂ 3) ThreeModel oldTerminal x w) =
      outputMetric.inner (oldOutput x)
        (mfderiv (𝓡∂ 3) ThreeModel oldOutput x v)
        (mfderiv (𝓡∂ 3) ThreeModel oldOutput x w)
  old_contains_outside : ∀ x : transition.trace.tubes.core,
    x ∈ transition.trace.retainedCore →
    (∀ a : transition.trace.tubes.Index,
      x.1 ∉ transition.trace.tubes.tube a ''
        {z : TubeDomain | (-2 : ℝ) < z.2.1 ∧ z.2.1 < 2}) → x ∈ old
  every_child_meets_old : ∀ c : ConnectedComponents Q.Carrier,
    ∃ x : old, ConnectedComponents.mk (oldOutput x) = c

structure ObservedHistory where
  horizon : ℝ
  horizon_nonneg : 0 ≤ horizon
  eventCount : ℕ
  time : Fin (eventCount + 1) → ℝ
  time_strictMono : StrictMono time
  time_zero : time 0 = 0
  time_le_horizon : time (Fin.last eventCount) ≤ horizon
  stage : Fin (eventCount + 1) → OrientedThreeStage.{u}
  initialMetric : (i : Fin (eventCount + 1)) → (stage i).Metric
  event : (i : Fin eventCount) →
    MetricCutCapEvent (stage i.castSucc) (stage i.succ) (time i.castSucc) (time i.succ)
  event_initial : ∀ i : Fin eventCount,
    (event i).incoming.flow.base.metric (time i.castSucc) = initialMetric i.castSucc
  event_output : ∀ i : Fin eventCount, (event i).outputMetric = initialMetric i.succ
  finalSlab : time (Fin.last eventCount) < horizon →
    (stage (Fin.last eventCount)).ClosedSlab (time (Fin.last eventCount)) horizon
  final_initial : ∀ h : time (Fin.last eventCount) < horizon,
    (finalSlab h).flow.base.metric (time (Fin.last eventCount)) =
      initialMetric (Fin.last eventCount)

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

def RegularCrossing (p : P.Carrier) (q : Q.Carrier) : Prop :=
  letI := E.oldCharts
  letI := E.oldSmooth
  ∃ x : E.old, (𝓡∂ 3).IsInteriorPoint x ∧ x.1.1 = p ∧ E.oldOutput x = q

theorem oldOutput_injective : Function.Injective E.oldOutput := by
  intro x y hxy
  have hpres : E.transition.trace.presentation (E.transition.trace.capping.coreInclusion x.1) =
      E.transition.trace.presentation (E.transition.trace.capping.coreInclusion y.1) := by
    rw [E.oldOutput_eq, E.oldOutput_eq, hxy]
  exact Subtype.ext (E.transition.trace.capping.coreEmbedding.injective
    (E.transition.trace.presentation.injective hpres))


theorem regularCrossing_right_unique {p : P.Carrier} {q r : Q.Carrier}
    (hq : E.RegularCrossing p q) (hr : E.RegularCrossing p r) : q = r := by
  obtain ⟨x, _, hxp, hxq⟩ := hq
  obtain ⟨y, _, hyp, hyr⟩ := hr
  have hxy : x = y := Subtype.ext (Subtype.ext (hxp.trans hyp.symm))
  subst y
  exact hxq.symm.trans hyr


theorem regularCrossing_left_unique {p r : P.Carrier} {q : Q.Carrier}
    (hp : E.RegularCrossing p q) (hr : E.RegularCrossing r q) : p = r := by
  obtain ⟨x, _, hxp, hxq⟩ := hp
  obtain ⟨y, _, hyr, hyq⟩ := hr
  have hxy := E.oldOutput_injective (hxq.trans hyq.symm)
  subst y
  exact hxp.symm.trans hyr

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem oldOutput_eq_iff_of_regularCrossing (z : E.old) {p : P.Carrier} {q : Q.Carrier}
    (hcross : E.RegularCrossing p q) : E.oldOutput z = q ↔ z.val.val = p := by
  obtain ⟨w, _, hwp, hwq⟩ := hcross
  constructor
  · intro hz
    have hzw := E.oldOutput_injective (hz.trans hwq.symm)
    exact (congrArg (fun z : E.old => z.val.val) hzw).trans hwp
  · intro hz
    have hzw : z = w := Subtype.ext (Subtype.ext (hz.trans hwp.symm))
    exact (congrArg E.oldOutput hzw).trans hwq

theorem mem_image_iff_of_admissible_node {X : Type v}
    (f : X → P.Carrier) (g : X → Q.Carrier) (K : Set X)
    (hcross : ∀ x ∈ K, E.RegularCrossing (f x) (g x))
    {p : P.Carrier} {q : Q.Carrier}
    (hnode : ∃ z : E.old, z.val.val = p ∧ E.oldOutput z = q) :
    q ∈ g '' K ↔ p ∈ f '' K := by
  obtain ⟨z, rfl, rfl⟩ := hnode
  constructor
  · rintro ⟨x, hx, hq⟩
    exact ⟨x, hx, ((E.oldOutput_eq_iff_of_regularCrossing z (hcross x hx)).mp hq.symm).symm⟩
  · rintro ⟨x, hx, hp⟩
    exact ⟨x, hx, ((E.oldOutput_eq_iff_of_regularCrossing z (hcross x hx)).mpr hp.symm).symm⟩

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u v

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem disjoint_old_image_of_discarded_core
    (E : MetricCutCapEvent P Q a s) {X : Type v} (f : X → P.Carrier) (K : Set X)
    (hdiscard : ∀ x ∈ K, ∃ z : E.transition.trace.tubes.core, z.val = f x ∧
      ∃ d : E.discarded.Carrier,
        E.transition.trace.presentation (E.transition.trace.capping.coreInclusion z) = Sum.inr d) :
    Disjoint (f '' K) (range (fun z : E.old => z.val.val)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy⟩
  obtain ⟨z, hz, d, hd⟩ := hdiscard x hx
  have heq : z = y.val := Subtype.ext (hz.trans hy.symm)
  rw [heq] at hd
  exact Sum.inr_ne_inl (hd.symm.trans (E.oldOutput_eq y))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
