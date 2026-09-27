import DifferentialGeometry.Analysis.Estimates.UniformScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegreeFrontierReduction
import DifferentialGeometry.Geometry.Metric.Restriction
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem scaleMetric_inner_self_le (g : SmoothRiemannianMetric I M) {c : ℝ} (hc : 0 < c)
    (x : M) (v : TangentSpace I x) :
    (scaleMetric c hc g).inner x v v ≤ c * g.inner x v v := by
  rw [scaleMetric_inner]

theorem not_scaleMetric_inner_self_le_standardEuclideanMetric :
    ¬ (∀ x : ℝ, ∀ v : TangentSpace 𝓘(ℝ, ℝ) x,
      (scaleMetric 4 (by norm_num) (standardEuclideanMetric ℝ)).inner x v v ≤
        (1 : ℝ) ^ 2 * (standardEuclideanMetric ℝ).inner x v v) := by
  intro h
  have hle := edistOf_le_of_quad (standardEuclideanMetric ℝ)
    (scaleMetric 4 (by norm_num) (standardEuclideanMetric ℝ)) one_pos
    (fun x v => by simpa using h x v) (0 : ℝ) (1 : ℝ)
  have hbase : riemannianEDistOf (standardEuclideanMetric ℝ) (0 : ℝ) 1 = 1 := by
    rw [riemannianEDistOf_standardEuclideanMetric, edist_dist, Real.dist_eq]
    norm_num
  have hsqrt : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hscaled : riemannianEDistOf (scaleMetric 4 (by norm_num) (standardEuclideanMetric ℝ))
      (0 : ℝ) 1 = 2 := by
    rw [edistOf_scale, hbase, mul_one, hsqrt, ENNReal.ofReal_ofNat]
  rw [hscaled, hbase, Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hle
  exact absurd hle (by norm_num)

section

variable [FiniteDimensional ℝ E] [T2Space M]

theorem riemannianEDistOf_restrictOpen_self_le (g : SmoothRiemannianMetric I M)
    {U V : TopologicalSpace.Opens M} (hUV : (U : Set M) ⊆ V) (x : U) :
    riemannianEDistOf (g.restrictOpen U) x x ≤
      riemannianEDistOf (g.restrictOpen V) ⟨x.1, hUV x.2⟩ ⟨x.1, hUV x.2⟩ := by
  rw [riemannianEDistOf_self]
  exact zero_le

end

theorem riemannianEDistOf_eq_top_of_isEmpty_path (g : SmoothRiemannianMetric I M)
    {x y : M} (h : IsEmpty (Path x y)) : riemannianEDistOf g x y = ⊤ := by
  rw [edistOf_iInf]
  exact le_antisymm le_top (le_iInf fun γ => (h.false γ).elim)

def puncturedLineOpen : TopologicalSpace.Opens ℝ :=
  ⟨{x : ℝ | x ≠ 0}, isOpen_compl_singleton⟩

def puncturedLineNeg : ↥puncturedLineOpen :=
  ⟨-1, by exact (by norm_num : (-1 : ℝ) ≠ 0)⟩

def puncturedLinePos : ↥puncturedLineOpen :=
  ⟨1, by exact (by norm_num : (1 : ℝ) ≠ 0)⟩

theorem puncturedLineOpen_isEmpty_path :
    IsEmpty (Path puncturedLineNeg puncturedLinePos) := by
  refine ⟨?_⟩
  rintro γ
  have hcont : Continuous fun t : unitInterval => ((γ t : ↥puncturedLineOpen) : ℝ) :=
    continuous_subtype_val.comp γ.continuous
  have h0 : ((γ (0 : unitInterval) : ↥puncturedLineOpen) : ℝ) = -1 := by
    rw [γ.source, puncturedLineNeg]
  have h1 : ((γ (1 : unitInterval) : ↥puncturedLineOpen) : ℝ) = 1 := by
    rw [γ.target, puncturedLinePos]
  have hmem : (0 : ℝ) ∈ Icc
      (((fun t : unitInterval => ((γ t : ↥puncturedLineOpen) : ℝ)) (0 : unitInterval)))
      (((fun t : unitInterval => ((γ t : ↥puncturedLineOpen) : ℝ)) 1)) := by
    simp only [h0, h1]
    norm_num
  obtain ⟨c, -, hcv⟩ := intermediate_value_Icc (show (0 : unitInterval) ≤ 1 from zero_le_one)
    hcont.continuousOn hmem
  exact (γ c).2 hcv

theorem not_riemannianEDistOf_restrictOpen_le_puncturedLine :
    ¬ (riemannianEDistOf ((standardEuclideanMetric ℝ).restrictOpen puncturedLineOpen)
        puncturedLineNeg puncturedLinePos ≤
      riemannianEDistOf (standardEuclideanMetric ℝ) (-1) 1) := by
  intro hbad
  have htop : riemannianEDistOf ((standardEuclideanMetric ℝ).restrictOpen puncturedLineOpen)
      puncturedLineNeg puncturedLinePos = ⊤ :=
    riemannianEDistOf_eq_top_of_isEmpty_path _ puncturedLineOpen_isEmpty_path
  have hbase : riemannianEDistOf (standardEuclideanMetric ℝ) (-1 : ℝ) 1 =
      ENNReal.ofReal 2 := by
    rw [riemannianEDistOf_standardEuclideanMetric, edist_dist, Real.dist_eq]
    norm_num
  rw [htop, hbase] at hbad
  exact absurd hbad (by simp)

theorem exists_scaling_of_uniform_quad_bound
    {α : Type*} {P Q : ℝ → α → ℝ} {s₀ T : ℝ}
    (hQ : ∀ s x, 0 ≤ Q s x)
    (h : ∀ ε : ℝ, 0 < ε → ∃ d ∈ Ioo s₀ T, ∀ s ∈ Ioo d T, ∀ x,
      |P s x - Q s x| ≤ ε * Q s x) :
    ∃ s₁ ∈ Ioo s₀ T, ∃ ell : ℝ → ℝ, (∀ s ∈ Ioo s₁ T, 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] T) (𝓝 1) ∧
      ∀ s ∈ Ioo s₁ T, ∀ x, P s x ≤ (ell s) ^ 2 * Q s x := by
  exact DifferentialGeometry.Analysis.exists_scaling_of_uniform_quad_bound hQ h

theorem exists_scaling_of_uniform_quad_bound_witness {α : Type*} {Q : ℝ → α → ℝ}
    {s₀ T : ℝ} (hT : s₀ < T) (hQ : ∀ s x, 0 ≤ Q s x) :
    ∃ s₁ ∈ Ioo s₀ T, ∃ ell : ℝ → ℝ, (∀ s ∈ Ioo s₁ T, 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] T) (𝓝 1) ∧
      ∀ s ∈ Ioo s₁ T, ∀ x, Q s x ≤ (ell s) ^ 2 * Q s x :=
  exists_scaling_of_uniform_quad_bound (P := Q) hQ fun ε hε =>
    ⟨(s₀ + T) / 2, ⟨by linarith, by linarith⟩, fun s hs x => by
      rw [sub_self, abs_zero]
      exact mul_nonneg hε.le (hQ s x)⟩

theorem not_quad_bound_shape_zero :
    ¬ (∃ ell : ℝ → ℝ, ∀ s ∈ Ioo (0 : ℝ) 1, (1 : ℝ) ≤ (ell s) ^ 2 * 0) := by
  rintro ⟨ell, h⟩
  have h1 := h (1 / 2) ⟨by norm_num, by norm_num⟩
  rw [mul_zero] at h1
  linarith

end DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

namespace GeometricCutoffRecord

def TerminalParentQuadFormComparison (_G : GeometricCutoffRecord H i parameters)
    (s₀ : ℝ) (ell : ℝ → ℝ) : Prop :=
  ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x : (H.event i).incoming.terminalRegularOpen,
    ∀ v : TangentSpace ThreeModel x,
      (H.event i).terminal.metric.inner x v v ≤ (ell s) ^ 2 *
        (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen).inner x v v

def TerminalParentRegionConvexity (G : GeometricCutoffRecord H i parameters)
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

def TerminalParentUniformConvergence (_G : GeometricCutoffRecord H i parameters)
    (s₀ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ d ∈ Ioo s₀ (H.time i.succ), ∀ s ∈ Ioo d (H.time i.succ),
    ∀ x : (H.event i).incoming.terminalRegularOpen, ∀ v : TangentSpace ThreeModel x,
      |(((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen).inner x v v -
        (H.event i).terminal.metric.inner x v v| ≤ ε *
        (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen).inner x v v

theorem TerminalParentRegionConvexity.mono (G : GeometricCutoffRecord H i parameters)
    {Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c}
    {s₀ s₁ : ℝ} (h : G.TerminalParentRegionConvexity Kc s₀) (hle : s₀ ≤ s₁) :
    G.TerminalParentRegionConvexity Kc s₁ := by
  intro c s hs x hx
  exact h c s ⟨lt_of_le_of_lt hle hs.1, hs.2⟩ x hx

theorem exists_quadFormComparison_of_uniformConvergence
    (G : GeometricCutoffRecord H i parameters) {s₀ : ℝ}
    (h : G.TerminalParentUniformConvergence s₀) :
    ∃ s₁ ∈ Ioo s₀ (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ s ∈ Ioo s₁ (H.time i.succ), 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      G.TerminalParentQuadFormComparison s₁ ell := by
  obtain ⟨s₁, hs₁, ell, hell, htend, hquad⟩ :=
    DifferentialGeometry.Geometry.Metric.exists_scaling_of_uniform_quad_bound
      (α := Σ x : (H.event i).incoming.terminalRegularOpen, TangentSpace ThreeModel x)
      (P := fun s a => (H.event i).terminal.metric.inner a.1 a.2 a.2)
      (Q := fun s a => (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen).inner a.1 a.2 a.2)
      (fun s a => DifferentialGeometry.metric_inner_self_nonneg _ a.1 a.2)
      (fun ε hε => by
        obtain ⟨d, hd, hbd⟩ := h ε hε
        exact ⟨d, hd, fun s hs a =>
          (abs_sub_comm _ _).trans_le (hbd s hs a.1 a.2)⟩)
  exact ⟨s₁, hs₁, ell, hell, htend, fun s hs x v => hquad s hs ⟨x, v⟩⟩

theorem localTerminalParentEDistComparison_of_quadFormComparison_of_regionConvexity
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hquad : G.TerminalParentQuadFormComparison s₀ ell)
    (hconv : G.TerminalParentRegionConvexity Kc s₀)
    (hell : ∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) :
    G.LocalTerminalParentEDistComparison Kc s₀ ell := by
  intro c s hs x hx
  obtain ⟨U, hU, hterm, hdist⟩ := hconv c s hs x hx
  refine ⟨U, hU, hterm, ?_⟩
  intro y hy z hz hy' hz'
  have hells : (0 : ℝ) < ell s := lt_of_lt_of_le zero_lt_one (hell s hs)
  have hmain : riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy'⟩ ⟨z.1, hz'⟩ ≤
      ENNReal.ofReal (ell s) *
        riemannianEDistOf (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen) ⟨y.1, hy'⟩ ⟨z.1, hz'⟩ := by
    have h := DifferentialGeometry.edistOf_le_of_quad
      (((H.event i).incoming.flow.base.metric s).restrictOpen
        (H.event i).incoming.terminalRegularOpen)
      (H.event i).terminal.metric (pow_pos hells 2)
      (fun x v => hquad s hs x v) ⟨y.1, hy'⟩ ⟨z.1, hz'⟩
    rwa [Real.sqrt_sq hells.le] at h
  exact hmain.trans (mul_le_mul_of_nonneg_left (hdist y hy z hz hy' hz') (by positivity))

theorem localLengthComparison_of_terminalParentInputs
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hcollapse : G.LocalTerminalEDistComparison Kc)
    (hquad : G.TerminalParentQuadFormComparison s₀ ell)
    (hconv : G.TerminalParentRegionConvexity Kc s₀)
    (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (hell : ∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1)) :
    G.LocalLengthComparison Kc :=
  G.localLengthComparison_of_terminal_comparisons Kc hs₀ hcollapse
    (G.localTerminalParentEDistComparison_of_quadFormComparison_of_regionConvexity
      Kc hquad hconv hell) hell htend

theorem collapseDegreeMetricHalfFrontier_of_terminalParentInputs
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} {ell : ℝ → ℝ}
    (hcollapse : G.LocalTerminalEDistComparison Kc)
    (hquad : G.TerminalParentQuadFormComparison s₀ ell)
    (hconv : G.TerminalParentRegionConvexity Kc s₀)
    (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (hell : ∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1)) :
    G.CollapseDegreeMetricHalfFrontier :=
  ⟨Kc, hcollapse, s₀, hs₀, ell, hell, htend,
    G.localTerminalParentEDistComparison_of_quadFormComparison_of_regionConvexity
      Kc hquad hconv hell⟩

theorem collapseDegreeMetricHalfFrontier_of_uniformConvergence
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    {s₀ : ℝ} (hcollapse : G.LocalTerminalEDistComparison Kc)
    (hconv : G.TerminalParentRegionConvexity Kc s₀)
    (huni : G.TerminalParentUniformConvergence s₀)
    (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ)) :
    G.CollapseDegreeMetricHalfFrontier := by
  obtain ⟨s₁, hs₁, ell, hell, htend, hquad⟩ :=
    G.exists_quadFormComparison_of_uniformConvergence huni
  exact G.collapseDegreeMetricHalfFrontier_of_terminalParentInputs Kc hcollapse hquad
    (TerminalParentRegionConvexity.mono G hconv (le_of_lt hs₁.1))
    ⟨le_of_lt (lt_of_le_of_lt hs₀.1 hs₁.1), hs₁.2⟩ hell htend

theorem rfs_child_comparison_of_uniformConvergence
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hdegree : ∀ c, ComparisonSupport.CollapseDegreeClassInput (Kc c))
    (hcollapse : G.LocalTerminalEDistComparison Kc)
    {s₀ : ℝ} (huni : G.TerminalParentUniformConvergence s₀)
    (hregion : G.TerminalParentRegionConvexity Kc s₀)
    (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ)) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      C((G.Parent c).Carrier, (G.Child c).Carrier),
    (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
    (∀ c, integralHomologyMap 3 (f c) (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation) ∧
    ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
        riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
          (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨s₁, hs₁, ell, hell, htend, hquad⟩ :=
    G.exists_quadFormComparison_of_uniformConvergence huni
  exact G.rfs_child_comparison_of_terminalFrontiers Kc hdegree hcollapse s₁
    ⟨le_of_lt (lt_of_le_of_lt hs₀.1 hs₁.1), hs₁.2⟩ ell hell htend
    (G.localTerminalParentEDistComparison_of_quadFormComparison_of_regionConvexity Kc hquad
      (TerminalParentRegionConvexity.mono G hregion (le_of_lt hs₁.1)) hell)

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
