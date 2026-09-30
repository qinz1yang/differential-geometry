import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalRegionConvexity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonFrontierReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonLocalLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegreeFrontierReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WeakLength

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

namespace GeometricCutoffRecord

def regionOfComponent (G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier) :
    TopologicalSpace.Opens (H.stage i.castSucc).Carrier :=
  (H.stage i.castSucc).componentOpen (G.transition.childParent c) ⊓
    (H.event i).incoming.terminalRegularOpen

theorem regionOfComponent_le_terminal (G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier) :
    regionOfComponent G c ≤ (H.event i).incoming.terminalRegularOpen :=
  inf_le_right

theorem regionOfComponent_le_component (G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier) :
    (regionOfComponent G c : Set (H.stage i.castSucc).Carrier) ⊆
      (H.stage i.castSucc).componentOpen (G.transition.childParent c) :=
  inf_le_left

theorem regionEDistOf_le_regionOfComponent (G : GeometricCutoffRecord H i parameters)
    (c : ConnectedComponents (H.stage i.succ).Carrier)
    (g : SmoothRiemannianMetric ThreeModel (H.stage i.castSucc).Carrier)
    (y z : ↥(regionOfComponent G c)) :
    riemannianEDistOf (g.restrictOpen (H.event i).incoming.terminalRegularOpen)
        (TopologicalSpace.Opens.inclusion
          (regionOfComponent_le_terminal G c) y)
        (TopologicalSpace.Opens.inclusion
          (regionOfComponent_le_terminal G c) z) ≤
      riemannianEDistOf (g.restrictOpen (regionOfComponent G c)) y z :=
  DifferentialGeometry.Geometry.Metric.riemannianEDistOf_restrictOpen_le_of_subset
    g (regionOfComponent_le_terminal G c) y z

def LocalTerminalRegionEDistComparison (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (s₀ : ℝ) (ell : ℝ → ℝ) : Prop :=
  ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x ∈ (Kc c).support.region, ∃ U ∈ 𝓝 x,
    (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
    ∀ y ∈ U, ∀ z ∈ U,
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
      riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩ ≤
      ENNReal.ofReal (ell s) *
        riemannianEDistOf (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen) ⟨y.1, hy⟩ ⟨z.1, hz⟩

def LocalRegionEDistComparison (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (s₀ : ℝ) (ell : ℝ → ℝ) : Prop :=
  ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x ∈ (Kc c).support.region, ∃ U ∈ 𝓝 x,
    (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
    ∀ y ∈ U, ∀ z ∈ U,
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
      riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
        ((Kc c).canonicalWholeParentMap y) ((Kc c).canonicalWholeParentMap z) ≤
      ENNReal.ofReal (ell s) *
        riemannianEDistOf (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen) ⟨y.1, hy⟩ ⟨z.1, hz⟩

theorem localTerminalRegionEDistComparison_of_quadFormComparison
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hquad : G.TerminalParentQuadFormComparison s₀ ell)
    (hell : ∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) :
    G.LocalTerminalRegionEDistComparison Kc s₀ ell := by
  intro c s hs x hx
  refine ⟨{y : (G.Parent c).Carrier |
      y.1 ∈ (H.event i).incoming.terminalRegularRegion},
    ((H.event i).incoming.terminalRegularRegion_isOpen.preimage
      continuous_subtype_val).mem_nhds ((Kc c).support_terminal x hx), fun y hy => hy, ?_⟩
  intro y _ z _ hy' hz'
  have hells : (0 : ℝ) < ell s := lt_of_lt_of_le zero_lt_one (hell s hs)
  have h := edistOf_le_of_quad
    (((H.event i).incoming.flow.base.metric s).restrictOpen
      (H.event i).incoming.terminalRegularOpen)
    (H.event i).terminal.metric (pow_pos hells 2)
    (fun x v => hquad s hs x v) ⟨y.1, hy'⟩ ⟨z.1, hz'⟩
  rwa [Real.sqrt_sq hells.le] at h

theorem localRegionEDistComparison_of_terminalRegionComparison
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hcollapse : G.LocalTerminalEDistComparison Kc)
    (hregion : G.LocalTerminalRegionEDistComparison Kc s₀ ell) :
    G.LocalRegionEDistComparison Kc s₀ ell := by
  intro c s hs x hx
  obtain ⟨U, hU, hUsub, hU'⟩ := hcollapse c x hx
  obtain ⟨V, hV, hVsub, hV'⟩ := hregion c s hs x hx
  refine ⟨U ∩ V, Filter.inter_mem hU hV, fun y hy => hUsub y hy.1, ?_⟩
  intro y hy z hz hy' hz'
  exact (hU' y hy.1 z hz.1 hy' hz').trans (hV' y hy.2 z hz.2 hy' hz')

def LocalRegionLengthComparison (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) : Prop :=
  ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
    (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
    Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
    ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x ∈ (Kc c).support.region, ∃ U ∈ 𝓝 x,
      (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
      ∀ (a b : ℝ) (γ : ℝ → ↥(regionOfComponent G c)),
        a ≤ b → ContinuousOn γ (Icc a b) →
        (∀ t ∈ Icc a b, (⟨(γ t).1, (γ t).2.1⟩ : (G.Parent c).Carrier) ∈ U) →
        riemannianCurveLength (((H.event i).incoming.flow.base.metric s).restrictOpen
          (regionOfComponent G c)) γ a b ≠ ⊤ →
        riemannianCurveLength ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
          (fun t => (Kc c).canonicalWholeParentMap ⟨(γ t).1, (γ t).2.1⟩) a b ≤
        ENNReal.ofReal (ell s) *
          riemannianCurveLength (((H.event i).incoming.flow.base.metric s).restrictOpen
            (regionOfComponent G c)) γ a b

theorem localRegionLengthComparison_of_regionEDistComparison
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ)) {ell : ℝ → ℝ}
    (hlocal : G.LocalRegionEDistComparison Kc s₀ ell)
    (hell : ∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1)) :
    G.LocalRegionLengthComparison Kc := by
  refine ⟨s₀, hs₀, ell, hell, htend, ?_⟩
  intro c s hs x hx
  obtain ⟨U, hU, hUsub, hU'⟩ := hlocal c s hs x hx
  refine ⟨U, hU, hUsub, ?_⟩
  intro a b γ hab hγ hγU hlen
  refine riemannianCurveLength_comp_le_of_mapsTo
    (((H.event i).incoming.flow.base.metric s).restrictOpen (regionOfComponent G c))
    ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
    (fun u : ↥(regionOfComponent G c) => (Kc c).canonicalWholeParentMap ⟨u.1, u.2.1⟩)
    {u : ↥(regionOfComponent G c) | (⟨u.1, u.2.1⟩ : (G.Parent c).Carrier) ∈ U}
    ?_ γ a b ?_
  · intro y hy z hz
    have h1 := hU' ⟨y.1, y.2.1⟩ hy ⟨z.1, z.2.1⟩ hz
      (regionOfComponent_le_terminal G c y.2) (regionOfComponent_le_terminal G c z.2)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact regionEDistOf_le_regionOfComponent G c ((H.event i).incoming.flow.base.metric s) y z
  · intro t ht
    exact hγU t ht

theorem rfs_child_comparison_metric_of_regionLengthComparison
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hlocal : G.LocalRegionLengthComparison Kc) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, f c = (Kc c).canonicalWholeParentMap) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : ↥(regionOfComponent G c),
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            ((Kc c).canonicalWholeParentMap ⟨x.1, x.2.1⟩)
            ((Kc c).canonicalWholeParentMap ⟨y.1, y.2.1⟩) ≤
          ENNReal.ofReal (ell s) *
            riemannianEDistOf
              (((H.event i).incoming.flow.base.metric s).restrictOpen
                (regionOfComponent G c)) x y := by
  obtain ⟨s₀, hs₀, ell, hell, htend, hloc⟩ := hlocal
  refine ⟨fun c => (Kc c).canonicalWholeParentMap, fun c => rfl, s₀, hs₀, ell, hell, htend, ?_⟩
  intro c s hs x y
  let W := regionOfComponent G c
  let gs : SmoothRiemannianMetric ThreeModel ↥W :=
    ((H.event i).incoming.flow.base.metric s).restrictOpen W
  let hc : SmoothRiemannianMetric ThreeModel (G.Child c).Carrier :=
    (H.stage i.succ).componentMetric (H.event i).outputMetric c
  have hκ : Continuous fun u : ↥W => (⟨u.1, u.2.1⟩ : (G.Parent c).Carrier) :=
    continuous_subtype_val.subtype_mk fun u => u.2.1
  let F : C(↥W, (G.Child c).Carrier) :=
    ⟨fun u => (Kc c).canonicalWholeParentMap ⟨u.1, u.2.1⟩,
      (Kc c).canonicalWholeParentMap.continuous.comp hκ⟩
  have hL : (0 : ℝ) ≤ ell s := le_trans zero_le_one (hell s hs)
  let : SecondCountableTopology (H.stage i.castSucc).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage i.castSucc).Carrier
  let : SecondCountableTopology (G.Child c).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (G.Child c).Carrier
  have hlocFull : ∀ z : ↥W, ∃ U ∈ 𝓝 z, ∀ (a b : ℝ) (γ : ℝ → ↥W),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveLength gs γ a b ≠ ⊤ →
      riemannianCurveLength hc (F ∘ γ) a b ≤
        (NNReal.mk (ell s) hL : ℝ≥0∞) * riemannianCurveLength gs γ a b := by
    intro z
    by_cases hz : (⟨z.1, z.2.1⟩ : (G.Parent c).Carrier) ∈ (Kc c).support.region
    · obtain ⟨U, hU, hUsub, hU'⟩ := hloc c s hs ⟨z.1, z.2.1⟩ hz
      refine ⟨{u : ↥W | (⟨u.1, u.2.1⟩ : (G.Parent c).Carrier) ∈ U},
        hκ.continuousAt.preimage_mem_nhds hU, ?_⟩
      intro a b γ hab hγ hγU hlen
      have hmain := hU' a b γ hab hγ hγU hlen
      rw [ENNReal.ofReal_eq_coe_nnreal hL] at hmain
      exact hmain
    · obtain ⟨V, hV, hconst⟩ :=
        (Kc c).rfs_whole_parent_map_locallyConstant_of_notMem hz
      refine ⟨{u : ↥W | (⟨u.1, u.2.1⟩ : (G.Parent c).Carrier) ∈ V},
        hκ.continuousAt.preimage_mem_nhds hV, ?_⟩
      intro a b γ hab hγ hγU hlen
      have hconst' : ∀ t ∈ Icc a b, (F ∘ γ) t = F z := fun t ht =>
        hconst ⟨(γ t).1, (γ t).2.1⟩ (hγU ht)
      have hzero := riemannianCurveLength_eq_zero_of_apply_eq_const (g := hc)
        (γ := F ∘ γ) (a := a) (b := b) (q := F z) hconst'
      rw [hzero]
      exact bot_le
  by_cases hfin : riemannianEDistOf gs x y = ⊤
  · rw [hfin, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr
      (lt_of_lt_of_le zero_lt_one (hell s hs))))]
    exact le_top
  · have h := rfs_local_to_global_length_of_ne_top gs hc F (NNReal.mk (ell s) hL)
      hlocFull hfin
    rwa [ENNReal.ofReal_eq_coe_nnreal hL]

def LocalTerminalCoreEDistComparison (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (s₀ : ℝ) (ell : ℝ → ℝ)
    (d : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℝ →
      G.transition.ChildCore c → G.transition.ChildCore c → ℝ≥0∞) : Prop :=
  ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x ∈ (Kc c).support.region, ∃ U ∈ 𝓝 x,
    (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
    ∀ u v : G.transition.ChildCore c,
      G.transition.childCoreIntoParent c u ∈ U →
      G.transition.childCoreIntoParent c v ∈ U →
      riemannianEDistOf (H.event i).terminal.metric
        ⟨u.1.1, G.childCoreIntoParent_terminal c u⟩
        ⟨v.1.1, G.childCoreIntoParent_terminal c v⟩ ≤
      ENNReal.ofReal (ell s) * d c s u v

theorem localTerminalCoreEDistComparison_of_regionComparison
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hregion : G.LocalTerminalRegionEDistComparison Kc s₀ ell)
    {d : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℝ →
      G.transition.ChildCore c → G.transition.ChildCore c → ℝ≥0∞}
    (hdom : ∀ c (s : ℝ) (u v : G.transition.ChildCore c),
      riemannianEDistOf (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen)
        ⟨u.1.1, G.childCoreIntoParent_terminal c u⟩
        ⟨v.1.1, G.childCoreIntoParent_terminal c v⟩ ≤ d c s u v) :
    G.LocalTerminalCoreEDistComparison Kc s₀ ell d := by
  intro c s hs x hx
  obtain ⟨U, hU, hUsub, hU'⟩ := hregion c s hs x hx
  refine ⟨U, hU, hUsub, ?_⟩
  intro u v hu hv
  have h1 := hU' (G.transition.childCoreIntoParent c u) hu
    (G.transition.childCoreIntoParent c v) hv
    (G.childCoreIntoParent_terminal c u) (G.childCoreIntoParent_terminal c v)
  exact h1.trans (mul_le_mul_of_nonneg_left (hdom c s u v) (by positivity))

theorem localTerminalCoreEDistComparison_of_regionComparison_self
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hregion : G.LocalTerminalRegionEDistComparison Kc s₀ ell) :
    G.LocalTerminalCoreEDistComparison Kc s₀ ell
      (fun c s u v => riemannianEDistOf
        (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen)
        ⟨u.1.1, G.childCoreIntoParent_terminal c u⟩
        ⟨v.1.1, G.childCoreIntoParent_terminal c v⟩) :=
  G.localTerminalCoreEDistComparison_of_regionComparison Kc hregion (fun _ _ _ _ => le_rfl)

theorem localTerminalParentEDistComparison_of_regionComparison
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hregion : G.LocalTerminalRegionEDistComparison Kc s₀ ell)
    (hconv : G.TerminalParentRegionConvexity Kc s₀) :
    G.LocalTerminalParentEDistComparison Kc s₀ ell := by
  intro c s hs x hx
  obtain ⟨U, hU, hUsub, hU'⟩ := hregion c s hs x hx
  obtain ⟨V, hV, hVsub, hV'⟩ := hconv c s hs x hx
  refine ⟨U ∩ V, Filter.inter_mem hU hV, fun y hy => hUsub y hy.1, ?_⟩
  intro y hy z hz hy' hz'
  exact (hU' y hy.1 z hz.1 hy' hz').trans
    (mul_le_mul_of_nonneg_left (hV' y hy.2 z hz.2 hy' hz') (by positivity))

theorem localTerminalRegionEDistComparison_of_parentComparison
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (h : G.LocalTerminalParentEDistComparison Kc s₀ ell) :
    G.LocalTerminalRegionEDistComparison Kc s₀ ell := by
  intro c s hs x hx
  obtain ⟨U, hU, hUsub, hU'⟩ := h c s hs x hx
  refine ⟨U, hU, hUsub, ?_⟩
  intro y hy z hz hy' hz'
  refine (hU' y hy z hz hy' hz').trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [OrientedThreeStage.edistOf_componentMetric (H.stage i.castSucc)
    ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c) y z]
  exact DifferentialGeometry.riemannianEDistOf_le_restrictOpen
    ((H.event i).incoming.flow.base.metric s) (H.event i).incoming.terminalRegularOpen
    ⟨y.1, hy'⟩ ⟨z.1, hz'⟩

theorem rfs_child_comparison_metric_coreDominated_of_regionLengthComparison
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hlocal : G.LocalRegionLengthComparison Kc)
    {d : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℝ →
      G.transition.ChildCore c → G.transition.ChildCore c → ℝ≥0∞}
    (hdom : ∀ c (s : ℝ) (u v : G.transition.ChildCore c),
      riemannianEDistOf (((H.event i).incoming.flow.base.metric s).restrictOpen
          (regionOfComponent G c))
        ⟨u.1.1, ⟨(G.transition.childCoreIntoParent c u).2,
          G.childCoreIntoParent_terminal c u⟩⟩
        ⟨v.1.1, ⟨(G.transition.childCoreIntoParent c v).2,
          G.childCoreIntoParent_terminal c v⟩⟩ ≤ d c s u v) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, f c = (Kc c).canonicalWholeParentMap) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ u v : G.transition.ChildCore c,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            ((Kc c).canonicalWholeParentMap (G.transition.childCoreIntoParent c u))
            ((Kc c).canonicalWholeParentMap (G.transition.childCoreIntoParent c v)) ≤
          ENNReal.ofReal (ell s) * d c s u v := by
  obtain ⟨f, hf, s₀, hs₀, ell, hell, htend, hdist⟩ :=
    G.rfs_child_comparison_metric_of_regionLengthComparison Kc hlocal
  refine ⟨f, hf, s₀, hs₀, ell, hell, htend, ?_⟩
  intro c s hs u v
  have h1 := hdist c s hs
    ⟨u.1.1, ⟨(G.transition.childCoreIntoParent c u).2,
      G.childCoreIntoParent_terminal c u⟩⟩
    ⟨v.1.1, ⟨(G.transition.childCoreIntoParent c v).2,
      G.childCoreIntoParent_terminal c v⟩⟩
  refine h1.trans (mul_le_mul_of_nonneg_left (hdom c s u v) (by positivity))

theorem localTerminalRegionEDistComparison_self_of_metric_eq
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ}
    (hmetric : ∀ s, (H.event i).terminal.metric =
      ((H.event i).incoming.flow.base.metric s).restrictOpen
        (H.event i).incoming.terminalRegularOpen) :
    G.LocalTerminalRegionEDistComparison Kc s₀ (fun _ => 1) := by
  intro c s hs x hx
  refine ⟨{y : (G.Parent c).Carrier |
      y.1 ∈ (H.event i).incoming.terminalRegularRegion},
    ((H.event i).incoming.terminalRegularRegion_isOpen.preimage
      continuous_subtype_val).mem_nhds ((Kc c).support_terminal x hx), fun y hy => hy, ?_⟩
  intro y _ z _ hy' hz'
  rw [hmetric s, ENNReal.ofReal_one, one_mul]

def CollapseDegreeRegionMetricHalfFrontier (G : GeometricCutoffRecord H i parameters) : Prop :=
  ∃ Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c,
    G.LocalTerminalEDistComparison Kc ∧
    ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      G.LocalTerminalRegionEDistComparison Kc s₀ ell

theorem collapseDegreeRegionMetricHalfFrontier_of_quadFormComparison
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hcollapse : G.LocalTerminalEDistComparison Kc)
    (hquad : G.TerminalParentQuadFormComparison s₀ ell)
    (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (hell : ∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1)) :
    G.CollapseDegreeRegionMetricHalfFrontier :=
  ⟨Kc, hcollapse, s₀, hs₀, ell, hell, htend,
    G.localTerminalRegionEDistComparison_of_quadFormComparison Kc hquad hell⟩

theorem collapseDegreeRegionMetricHalfFrontier_of_uniformConvergence
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} (hcollapse : G.LocalTerminalEDistComparison Kc)
    (huni : G.TerminalParentUniformConvergence s₀)
    (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ)) :
    G.CollapseDegreeRegionMetricHalfFrontier := by
  obtain ⟨s₁, hs₁, ell, hell, htend, hquad⟩ :=
    G.exists_quadFormComparison_of_uniformConvergence huni
  exact ⟨Kc, hcollapse, s₁, ⟨le_of_lt (lt_of_le_of_lt hs₀.1 hs₁.1), hs₁.2⟩, ell, hell, htend,
    G.localTerminalRegionEDistComparison_of_quadFormComparison Kc hquad hell⟩

theorem localLengthComparison_of_regionMetricHalfFrontier
    (G : GeometricCutoffRecord H i parameters)
    (h : G.CollapseDegreeRegionMetricHalfFrontier) :
    ∃ Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c,
      G.LocalRegionLengthComparison Kc := by
  obtain ⟨Kc, hcollapse, s₀, hs₀, ell, hell, htend, hregion⟩ := h
  exact ⟨Kc, G.localRegionLengthComparison_of_regionEDistComparison Kc hs₀
    (G.localRegionEDistComparison_of_terminalRegionComparison Kc hcollapse hregion) hell htend⟩

theorem collapseDegreeMetricHalfFrontier_of_regionMetricHalfFrontier_and_noShortcut
    (G : GeometricCutoffRecord H i parameters)
    (h : G.CollapseDegreeRegionMetricHalfFrontier)
    (hconv : ∀ (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        G.ComparisonSupport c) (s₀ : ℝ), G.TerminalParentRegionConvexity Kc s₀) :
    G.CollapseDegreeMetricHalfFrontier := by
  obtain ⟨Kc, hcollapse, s₀, hs₀, ell, hell, htend, hregion⟩ := h
  exact ⟨Kc, hcollapse, s₀, hs₀, ell, hell, htend,
    G.localTerminalParentEDistComparison_of_regionComparison Kc hregion (hconv Kc s₀)⟩

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
