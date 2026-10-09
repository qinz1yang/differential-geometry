import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonLocalLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegreeFrontierReduction
import DifferentialGeometry.Geometry.Metric.Restriction
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem riemannianEDistOf_restrictOpen_le_of_subset
    (g : SmoothRiemannianMetric I M) {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    (x y : U) :
    riemannianEDistOf (g.restrictOpen V) (TopologicalSpace.Opens.inclusion hUV x)
        (TopologicalSpace.Opens.inclusion hUV y) ≤
      riemannianEDistOf (g.restrictOpen U) x y := by
  rw [edistOf_iInf, edistOf_iInf]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  let γ' : Path (TopologicalSpace.Opens.inclusion hUV x)
      (TopologicalSpace.Opens.inclusion hUV y) :=
    γ.map (f := TopologicalSpace.Opens.inclusion hUV) (continuous_inclusion hUV)
  have hγ' : CMDiff 1 γ' := by
    change CMDiff 1 (fun t => TopologicalSpace.Opens.inclusion hUV (γ t))
    exact (contMDiff_inclusion (I := I) hUV).comp hγ
  refine iInf_le_of_le γ' (iInf_le_of_le hγ' ?_)
  apply le_of_eq
  apply lintegral_congr
  intro t
  have hc := mfderiv_comp t
    ((contMDiff_inclusion (I := I) hUV).contMDiffAt.mdifferentiableAt one_ne_zero)
    (hγ.mdifferentiableAt one_ne_zero)
  change mfderiv% γ' t = _ at hc
  rw [hc, mfderiv_opens_incl]
  rfl

def OpenEDistDomination (g : SmoothRiemannianMetric I M)
    (A B : TopologicalSpace.Opens M) : Prop :=
  ∀ (x : M) (y : M) (hxA : x ∈ A) (hyA : y ∈ A) (hxB : x ∈ B) (hyB : y ∈ B),
    riemannianEDistOf (g.restrictOpen A) ⟨x, hxA⟩ ⟨y, hyA⟩ ≤
      riemannianEDistOf (g.restrictOpen B) ⟨x, hxB⟩ ⟨y, hyB⟩

theorem openEDistDomination_of_subset (g : SmoothRiemannianMetric I M)
    {A B : TopologicalSpace.Opens M} (hBA : B ≤ A) : OpenEDistDomination g A B :=
  fun x y _ _ hxB hyB =>
    riemannianEDistOf_restrictOpen_le_of_subset g hBA ⟨x, hxB⟩ ⟨y, hyB⟩

def puncturedRealLineOpen : TopologicalSpace.Opens ℝ :=
  ⟨{x : ℝ | x ≠ 0}, isOpen_compl_singleton⟩

def puncturedRealLineNeg : ↥puncturedRealLineOpen :=
  ⟨-1, by exact (by norm_num : (-1 : ℝ) ≠ 0)⟩

def puncturedRealLinePos : ↥puncturedRealLineOpen :=
  ⟨1, by exact (by norm_num : (1 : ℝ) ≠ 0)⟩

theorem puncturedRealLine_isEmpty_path :
    IsEmpty (Path puncturedRealLineNeg puncturedRealLinePos) := by
  refine ⟨?_⟩
  rintro γ
  have hcont : Continuous fun t : unitInterval => ((γ t : ↥puncturedRealLineOpen) : ℝ) :=
    continuous_subtype_val.comp γ.continuous
  have h0 : ((γ (0 : unitInterval) : ↥puncturedRealLineOpen) : ℝ) = -1 := by
    rw [γ.source, puncturedRealLineNeg]
  have h1 : ((γ (1 : unitInterval) : ↥puncturedRealLineOpen) : ℝ) = 1 := by
    rw [γ.target, puncturedRealLinePos]
  have hmem : (0 : ℝ) ∈ Icc
      (((fun t : unitInterval => ((γ t : ↥puncturedRealLineOpen) : ℝ))
        (0 : unitInterval)))
      (((fun t : unitInterval => ((γ t : ↥puncturedRealLineOpen) : ℝ)) 1)) := by
    simp only [h0, h1]
    norm_num
  obtain ⟨c, -, hcv⟩ := intermediate_value_Icc (show (0 : unitInterval) ≤ 1 from zero_le_one)
    hcont.continuousOn hmem
  exact (γ c).2 hcv

theorem not_openEDistDomination_puncturedRealLine :
    ¬ OpenEDistDomination (Geometry.standardEuclideanMetric ℝ) puncturedRealLineOpen ⊤ := by
  intro h
  have htop : riemannianEDistOf
      ((Geometry.standardEuclideanMetric ℝ).restrictOpen puncturedRealLineOpen)
      puncturedRealLineNeg puncturedRealLinePos = ⊤ := by
    rw [edistOf_iInf]
    exact le_antisymm le_top
      (le_iInf fun γ => (puncturedRealLine_isEmpty_path.false γ).elim)
  have hbase : riemannianEDistOf
      ((Geometry.standardEuclideanMetric ℝ).restrictOpen (⊤ : TopologicalSpace.Opens ℝ))
      (⟨(-1 : ℝ), trivial⟩ : ↥(⊤ : TopologicalSpace.Opens ℝ))
      ⟨(1 : ℝ), trivial⟩ = ENNReal.ofReal 2 := by
    rw [DifferentialGeometry.riemannianEDistOf_restrictOpen_of_isClosed _ _
      (show IsClosed (↑(⊤ : TopologicalSpace.Opens ℝ) : Set ℝ) from isClosed_univ)]
    rw [Geometry.riemannianEDistOf_standardEuclideanMetric, edist_dist, Real.dist_eq]
    norm_num
  have hle := h (-1) 1 puncturedRealLineNeg.2 puncturedRealLinePos.2 trivial trivial
  change riemannianEDistOf
      ((Geometry.standardEuclideanMetric ℝ).restrictOpen puncturedRealLineOpen)
      puncturedRealLineNeg puncturedRealLinePos ≤
    riemannianEDistOf
      ((Geometry.standardEuclideanMetric ℝ).restrictOpen (⊤ : TopologicalSpace.Opens ℝ))
      (⟨(-1 : ℝ), trivial⟩ : ↥(⊤ : TopologicalSpace.Opens ℝ))
      ⟨(1 : ℝ), trivial⟩ at hle
  rw [htop, hbase] at hle
  exact absurd hle (by simp)

theorem puncturedRealLine_quadBound_and_not_openEDistDomination :
    (∀ x : ↥puncturedRealLineOpen, ∀ v : TangentSpace (𝓘(ℝ, ℝ)) x,
      ((Geometry.standardEuclideanMetric ℝ).restrictOpen puncturedRealLineOpen).inner x v v ≤
        (1 : ℝ) ^ 2 *
          ((Geometry.standardEuclideanMetric ℝ).restrictOpen puncturedRealLineOpen).inner x v v) ∧
      ¬ OpenEDistDomination (Geometry.standardEuclideanMetric ℝ) puncturedRealLineOpen ⊤ :=
  ⟨fun _ _ => by rw [one_pow, one_mul], not_openEDistDomination_puncturedRealLine⟩

theorem openEDistDomination_top (g : SmoothRiemannianMetric I M)
    (A : TopologicalSpace.Opens M) : OpenEDistDomination g ⊤ A :=
  openEDistDomination_of_subset g le_top

theorem openEDistDomination_puncturedRealLine_top :
    OpenEDistDomination (Geometry.standardEuclideanMetric ℝ) ⊤ puncturedRealLineOpen :=
  openEDistDomination_top _ _

end DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

namespace OrientedThreeStage

variable (P : OrientedThreeStage.{u})

theorem componentOpen_isClosed (c : ConnectedComponents P.Carrier) :
    IsClosed (P.componentOpen c : Set P.Carrier) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  have hset : (P.componentOpen (ConnectedComponents.mk p) : Set P.Carrier) =
      connectedComponent p := by
    ext z
    exact ConnectedComponents.coe_eq_coe'
  rw [hset]
  exact isClosed_connectedComponent

theorem edistOf_componentMetric (g : P.Metric) (c : ConnectedComponents P.Carrier)
    (x y : (P.component c).Carrier) :
    riemannianEDistOf (P.componentMetric g c) x y = riemannianEDistOf g x.1 y.1 :=
  DifferentialGeometry.riemannianEDistOf_restrictOpen_of_isClosed g (P.componentOpen c)
    (P.componentOpen_isClosed c) x y

end OrientedThreeStage

namespace GeometricCutoffRecord

def TerminalParentRegionContainment (G : GeometricCutoffRecord H i parameters) : Prop :=
  ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
    (H.stage i.castSucc).componentOpen (G.transition.childParent c) ≤
      (H.event i).incoming.terminalRegularOpen

def TerminalParentRegionRetainedContainment (G : GeometricCutoffRecord H i parameters) : Prop :=
  ∀ c : ConnectedComponents (H.stage i.succ).Carrier, ∀ x : (G.Parent c).Carrier,
    x.1 ∈ Subtype.val '' (H.event i).transition.trace.retainedCore

theorem terminalParentRegionContainment_of_retained
    (G : GeometricCutoffRecord H i parameters)
    (h : G.TerminalParentRegionRetainedContainment) : G.TerminalParentRegionContainment := by
  intro c x hx
  obtain ⟨y, hy, hyx⟩ := h c ⟨x, hx⟩
  have hxy : x = (y : (H.stage i.castSucc).Carrier) := hyx.symm
  rw [hxy]
  exact G.retained_terminal y hy

def TerminalParentRegionNoShortcut (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (s₀ : ℝ) : Prop :=
  ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x ∈ (Kc c).support.region, ∃ U ∈ 𝓝 x,
    (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
    ∀ y ∈ U, ∀ z ∈ U,
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
      riemannianEDistOf (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen) ⟨y.1, hy⟩ ⟨z.1, hz⟩ ≤
      riemannianEDistOf ((H.stage i.castSucc).componentMetric
        ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) y z

def TerminalParentRegionAmbientConvexity (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (s₀ : ℝ) : Prop :=
  ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x ∈ (Kc c).support.region, ∃ U ∈ 𝓝 x,
    (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
    ∀ y ∈ U, ∀ z ∈ U,
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
      riemannianEDistOf (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen) ⟨y.1, hy⟩ ⟨z.1, hz⟩ =
      riemannianEDistOf ((H.event i).incoming.flow.base.metric s) y.1 z.1

theorem terminalParentRegionEDistComparison_of_containment
    (G : GeometricCutoffRecord H i parameters) (hregion : G.TerminalParentRegionContainment)
    (c : ConnectedComponents (H.stage i.succ).Carrier) (s : ℝ) (y z : (G.Parent c).Carrier)
    (hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion)
    (hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion) :
    riemannianEDistOf (((H.event i).incoming.flow.base.metric s).restrictOpen
        (H.event i).incoming.terminalRegularOpen) ⟨y.1, hy⟩ ⟨z.1, hz⟩ ≤
      riemannianEDistOf ((H.stage i.castSucc).componentMetric
        ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) y z := by
  have hle := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_restrictOpen_le_of_subset
    ((H.event i).incoming.flow.base.metric s) (hregion c) y z
  have hy' : (⟨y.1, hy⟩ : ↥(H.event i).incoming.terminalRegularOpen) =
      TopologicalSpace.Opens.inclusion (hregion c) y := Subtype.ext rfl
  have hz' : (⟨z.1, hz⟩ : ↥(H.event i).incoming.terminalRegularOpen) =
      TopologicalSpace.Opens.inclusion (hregion c) z := Subtype.ext rfl
  rw [hy', hz']
  exact hle

theorem terminalParentRegionNoShortcut_of_containment
    (G : GeometricCutoffRecord H i parameters) (hregion : G.TerminalParentRegionContainment)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (s₀ : ℝ) : G.TerminalParentRegionNoShortcut Kc s₀ := by
  intro c s _ x _
  exact ⟨univ, Filter.univ_mem, fun y _ => hregion c y.2,
    fun y _ z _ hy hz =>
      G.terminalParentRegionEDistComparison_of_containment hregion c s y z hy hz⟩

theorem terminalParentRegionNoShortcut_iff_ambientConvexity
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (s₀ : ℝ) :
    G.TerminalParentRegionNoShortcut Kc s₀ ↔ G.TerminalParentRegionAmbientConvexity Kc s₀ := by
  constructor
  · intro h c s hs x hx
    obtain ⟨U, hU, hreg, hle⟩ := h c s hs x hx
    refine ⟨U, hU, hreg, fun y hy z hz hyr hzr => le_antisymm ?_ ?_⟩
    · exact (hle y hy z hz hyr hzr).trans_eq
        (OrientedThreeStage.edistOf_componentMetric (H.stage i.castSucc)
          ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c) y z)
    · exact DifferentialGeometry.riemannianEDistOf_le_restrictOpen
        ((H.event i).incoming.flow.base.metric s) (H.event i).incoming.terminalRegularOpen
        ⟨y.1, hyr⟩ ⟨z.1, hzr⟩
  · intro h c s hs x hx
    obtain ⟨U, hU, hreg, heq⟩ := h c s hs x hx
    refine ⟨U, hU, hreg, fun y hy z hz hyr hzr => ?_⟩
    rw [heq y hy z hz hyr hzr]
    exact (OrientedThreeStage.edistOf_componentMetric (H.stage i.castSucc)
      ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c) y z).ge

theorem localTerminalParentEDistComparison_of_parentContainment
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hquad : ∀ s ∈ Ioo s₀ (H.time i.succ),
      ∀ x : (H.event i).incoming.terminalRegularOpen, ∀ v : TangentSpace ThreeModel x,
      (H.event i).terminal.metric.inner x v v ≤ (ell s) ^ 2 *
        ((((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen).inner x v v))
    (hcontain : G.TerminalParentRegionContainment)
    (hell : ∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) :
    G.LocalTerminalParentEDistComparison Kc s₀ ell := by
  intro c s hs x _
  refine ⟨univ, Filter.univ_mem, fun y _ => hcontain c y.2, fun y _ z _ hy hz => ?_⟩
  have hells : (0 : ℝ) < ell s := lt_of_lt_of_le zero_lt_one (hell s hs)
  have hmain : riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩ ≤
      ENNReal.ofReal (ell s) * riemannianEDistOf
        (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen) ⟨y.1, hy⟩ ⟨z.1, hz⟩ := by
    have h := DifferentialGeometry.edistOf_le_of_quad
      (((H.event i).incoming.flow.base.metric s).restrictOpen
        (H.event i).incoming.terminalRegularOpen)
      (H.event i).terminal.metric (pow_pos hells 2)
      (fun x v => hquad s hs x v) ⟨y.1, hy⟩ ⟨z.1, hz⟩
    rwa [Real.sqrt_sq hells.le] at h
  exact hmain.trans (mul_le_mul_of_nonneg_left
    (G.terminalParentRegionEDistComparison_of_containment hcontain c s y z hy hz)
    (by positivity))

theorem localLengthComparison_of_parentContainment
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hcollapse : G.LocalTerminalEDistComparison Kc)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hquad : ∀ s ∈ Ioo s₀ (H.time i.succ),
      ∀ x : (H.event i).incoming.terminalRegularOpen, ∀ v : TangentSpace ThreeModel x,
      (H.event i).terminal.metric.inner x v v ≤ (ell s) ^ 2 *
        ((((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen).inner x v v))
    (hcontain : G.TerminalParentRegionContainment)
    (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (hell : ∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1)) :
    G.LocalLengthComparison Kc :=
  G.localLengthComparison_of_terminal_comparisons Kc hs₀ hcollapse
    (G.localTerminalParentEDistComparison_of_parentContainment Kc hquad hcontain hell)
    hell htend

theorem collapseDegreeMetricHalfFrontier_of_parentContainment
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hcollapse : G.LocalTerminalEDistComparison Kc)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hquad : ∀ s ∈ Ioo s₀ (H.time i.succ),
      ∀ x : (H.event i).incoming.terminalRegularOpen, ∀ v : TangentSpace ThreeModel x,
      (H.event i).terminal.metric.inner x v v ≤ (ell s) ^ 2 *
        ((((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen).inner x v v))
    (hcontain : G.TerminalParentRegionContainment)
    (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (hell : ∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1)) :
    G.CollapseDegreeMetricHalfFrontier :=
  ⟨Kc, hcollapse, s₀, hs₀, ell, hell, htend,
    G.localTerminalParentEDistComparison_of_parentContainment Kc hquad hcontain hell⟩

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
