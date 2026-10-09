import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ComparisonClassDegreeData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonLocalLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWitnessDistance
import DifferentialGeometry.Geometry.Metric.Restriction
import DifferentialGeometry.Geometry.Measure.Area.ManifoldEuclidean

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem edistOf_le_of_pointwise_le {g h : SmoothRiemannianMetric I M}
    (hle : ∀ x v, h.inner x v v ≤ g.inner x v v) (x y : M) :
    riemannianEDistOf h x y ≤ riemannianEDistOf g x y := by
  simpa using DifferentialGeometry.edistOf_le_of_quad g h one_pos
    (fun x v => by simpa using hle x v) x y

theorem edistOf_eq_of_pointwise_eq {g h : SmoothRiemannianMetric I M}
    (heq : ∀ x v, h.inner x v v = g.inner x v v) (x y : M) :
    riemannianEDistOf h x y = riemannianEDistOf g x y :=
  le_antisymm (edistOf_le_of_pointwise_le (fun x v => (heq x v).le) x y)
    (edistOf_le_of_pointwise_le (fun x v => (heq x v).ge) x y)

variable [FiniteDimensional ℝ E]

def RestrictedEDistLe (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] (h : SmoothRiemannianMetric I U) : Prop :=
  ∀ x y : U, riemannianEDistOf (g.restrictOpen U) x y ≤ riemannianEDistOf h x y

theorem restrictedEDistLe_of_pointwise_le {g : SmoothRiemannianMetric I M}
    {U : TopologicalSpace.Opens M} [T2Space U] {h : SmoothRiemannianMetric I U}
    (hle : ∀ x v, (g.restrictOpen U).inner x v v ≤ h.inner x v v) :
    RestrictedEDistLe g U h :=
  fun x y => edistOf_le_of_pointwise_le hle x y

theorem restrictedEDistLe_refl (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [T2Space U] :
    RestrictedEDistLe g U (g.restrictOpen U) :=
  fun _ _ => le_rfl

theorem not_restrictedEDistLe_standardEuclideanMetric_scaleMetric :
    ¬ RestrictedEDistLe (Geometry.standardEuclideanMetric ℝ) ⊤
      (scaleMetric (1 / 2) (by norm_num)
        ((Geometry.standardEuclideanMetric ℝ).restrictOpen (⊤ : TopologicalSpace.Opens ℝ))) := by
  intro h
  have hbase : riemannianEDistOf
      ((Geometry.standardEuclideanMetric ℝ).restrictOpen (⊤ : TopologicalSpace.Opens ℝ))
      (⟨0, trivial⟩ : ↥(⊤ : TopologicalSpace.Opens ℝ)) ⟨1, trivial⟩ = 1 := by
    rw [DifferentialGeometry.riemannianEDistOf_restrictOpen_of_isClosed _ _
      (show IsClosed (↑(⊤ : TopologicalSpace.Opens ℝ) : Set ℝ) from isClosed_univ)]
    rw [Geometry.riemannianEDistOf_standardEuclideanMetric, edist_dist]
    norm_num
  have hle := h (⟨0, trivial⟩ : ↥(⊤ : TopologicalSpace.Opens ℝ)) ⟨1, trivial⟩
  rw [DifferentialGeometry.edistOf_scale (1 / 2) (by norm_num)
      ((Geometry.standardEuclideanMetric ℝ).restrictOpen (⊤ : TopologicalSpace.Opens ℝ)) _ _,
    hbase, mul_one] at hle
  have hlt : ENNReal.ofReal (Real.sqrt (1 / 2)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact (Real.sqrt_lt' one_pos).mpr (by norm_num)
  exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl 1)

end DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def MapDistanceFactorOne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → N) : Prop :=
  ∀ x y : M, riemannianEDistOf h (f x) (f y) ≤ riemannianEDistOf g x y

theorem mapDistanceFactorOne_id {g : SmoothRiemannianMetric I M} :
    MapDistanceFactorOne g g id :=
  fun _ _ => le_rfl

theorem not_mapDistanceFactorOne_standardEuclideanMetric_scaleMetric :
    ¬ MapDistanceFactorOne (Geometry.standardEuclideanMetric ℝ)
      (scaleMetric 2 (by norm_num) (Geometry.standardEuclideanMetric ℝ)) id := by
  have hbase : riemannianEDistOf (Geometry.standardEuclideanMetric ℝ) (0 : ℝ) 1 = 1 := by
    rw [Geometry.riemannianEDistOf_standardEuclideanMetric, edist_dist, Real.dist_eq]
    norm_num
  have hscaled : riemannianEDistOf
      (scaleMetric 2 (by norm_num) (Geometry.standardEuclideanMetric ℝ)) (0 : ℝ) 1 =
      ENNReal.ofReal (Real.sqrt 2) := by
    rw [DifferentialGeometry.edistOf_scale, hbase, mul_one]
  intro h
  have h01 : riemannianEDistOf
      (scaleMetric 2 (by norm_num) (Geometry.standardEuclideanMetric ℝ)) (0 : ℝ) 1 ≤
      riemannianEDistOf (Geometry.standardEuclideanMetric ℝ) (0 : ℝ) 1 := h 0 1
  rw [hscaled, hbase] at h01
  have hgt : (1 : ENNReal) < ENNReal.ofReal (Real.sqrt 2) := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (Real.sqrt_pos.mpr (by norm_num))]
    exact (Real.lt_sqrt zero_le_one).mpr (by norm_num)
  exact absurd (lt_of_lt_of_le hgt h01) (lt_irrefl 1)

end DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem canonicalStaticInsertionWitness_collapse_mapDistanceFactorOne
    {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
    {d : DifferentialGeometry.Geometry.Neck.normalizedDatum g x₀ δ k}
    {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}
    (w : CanonicalStaticInsertionWitness d A hA D m ε) :
    letI := DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentChartedSpace
      DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd_pos
      (inv_pos.mpr d.precision_pos)
    letI := DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachment_isManifold
      DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd_pos
      (inv_pos.mpr d.precision_pos)
    DifferentialGeometry.Geometry.Metric.MapDistanceFactorOne
      (g.restrictOpen d.oriented.controlledImage) w.data.outMetric w.data.collapse :=
  fun p q => canonicalStaticInsertionWitness_collapse_riemannianEDistOf_le w p q

end DifferentialGeometry.PDE.RicciFlow.StandardCap

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]
  {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

def StaticCapWitness.CollapseDistanceFactorOne (neck : NormalizedNeck h δ k)
    (fixed : StaticCapScaffold) (D : ℝ) (m : ℕ) (ε : ℝ)
    (w : StaticCapWitness neck fixed D m ε) : Prop :=
  ∀ x y : neckCentralDomain δ,
    riemannianEDistOf w.metric (w.collapse x) (w.collapse y) ≤
      riemannianEDistOf h (neck.chart x.1) (neck.chart y.1)

theorem StaticCapWitness.collapse_locallyLipschitz_of_collapseDistanceFactorOne
    (neck : NormalizedNeck h δ k) (fixed : StaticCapScaffold) (D : ℝ) (m : ℕ) (ε : ℝ)
    (w : StaticCapWitness neck fixed D m ε)
    (h1 : CollapseDistanceFactorOne neck fixed D m ε w) :
    ∀ x : neckCentralDomain δ, ∃ U ∈ 𝓝 x, ∃ L : ℝ≥0, ∀ y ∈ U, ∀ z ∈ U,
      riemannianEDistOf w.metric (w.collapse y) (w.collapse z) ≤
        L * riemannianEDistOf h (neck.chart y.1) (neck.chart z.1) := by
  intro x
  refine ⟨univ, Filter.univ_mem, 1, fun y _ z _ => ?_⟩
  simpa using h1 y z

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

namespace GeometricCutoffRecord.ComparisonSupport

variable {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier}

theorem localTerminalDistanceControl_of_localTerminalLengthControl
    {K : G.ComparisonSupport c}
    {f : C((G.Parent c).Carrier, (G.Child c).Carrier)}
    (h : K.LocalTerminalLengthControl f) :
    K.LocalTerminalDistanceControl f := by
  intro x hx
  obtain ⟨U, hU, hterm, hdist, _hlen⟩ := h x hx
  exact ⟨U, hU, hterm, hdist⟩

theorem rfs_collapse_degree_of_localDistanceFrontier
    {K : G.ComparisonSupport c}
    (hlip : K.LocalTerminalDistanceControl K.canonicalWholeParentMap)
    (hclass : CollapseDegreeClassInput K) :
    K.LocalTerminalLengthControl K.canonicalWholeParentMap ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.canonicalWholeParentMap y = K.canonicalWholeParentMap x) ∧
    (∀ x : G.transition.ChildCore c,
      K.canonicalWholeParentMap (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 K.canonicalWholeParentMap (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation ∧
    Function.Surjective K.canonicalWholeParentMap :=
  ⟨K.rfs_whole_parent_map_localTerminalLengthControl_of_localTerminalDistanceControl hlip,
    fun _ hx => K.rfs_whole_parent_map_locallyConstant_of_notMem hx,
    fun x => K.rfs_whole_parent_map_childCore x, hclass,
    K.rfs_whole_parent_map_surjective_of_cover K.rfs_collapse_cover⟩

theorem localTerminalLengthControl_iff_localTerminalDistanceControl
    {K : G.ComparisonSupport c} :
    K.LocalTerminalLengthControl K.canonicalWholeParentMap ↔
      K.LocalTerminalDistanceControl K.canonicalWholeParentMap :=
  ⟨localTerminalDistanceControl_of_localTerminalLengthControl,
    K.rfs_whole_parent_map_localTerminalLengthControl_of_localTerminalDistanceControl⟩

end GeometricCutoffRecord.ComparisonSupport

namespace GeometricCutoffRecord

def CollapseDegreeMetricHalfFrontier (G : GeometricCutoffRecord H i parameters) : Prop :=
  ∃ Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c,
    G.LocalTerminalEDistComparison Kc ∧
    ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      G.LocalTerminalParentEDistComparison Kc s₀ ell

theorem localLengthComparison_of_metricHalfFrontier (G : GeometricCutoffRecord H i parameters)
    (h : G.CollapseDegreeMetricHalfFrontier) :
    ∃ Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c,
      G.LocalLengthComparison Kc := by
  obtain ⟨Kc, hcollapse, s₀, hs₀, ell, hell, htend, hconv⟩ := h
  exact ⟨Kc, G.localLengthComparison_of_terminal_comparisons Kc hs₀ hcollapse hconv hell
    htend⟩

theorem rfs_child_comparison_metric_of_metricHalfFrontier
    (G : GeometricCutoffRecord H i parameters)
    (h : G.CollapseDegreeMetricHalfFrontier) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.canonicalWholeParentMap) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  G.rfs_child_comparison_metric_of_exists_local_length_comparison
    (G.localLengthComparison_of_metricHalfFrontier h)

theorem rfs_child_comparison_of_terminalFrontiers
    (G : GeometricCutoffRecord H i parameters)
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hdegree : ∀ c, ComparisonSupport.CollapseDegreeClassInput (Kc c))
    (hcollapse : G.LocalTerminalEDistComparison Kc)
    (s₀ : ℝ) (hs₀ : s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ)) (ell : ℝ → ℝ)
    (hell : ∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s)
    (htend : Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hconv : G.LocalTerminalParentEDistComparison Kc s₀ ell) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.canonicalWholeParentMap) ∧
      (∀ c, integralHomologyMap 3 (f c) (fundamentalClass (G.Parent c).orientation) =
        fundamentalClass (G.Child c).orientation) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  G.rfs_child_comparison_of_local_length_comparison Kc hdegree
    (G.localLengthComparison_of_terminal_comparisons Kc hs₀ hcollapse hconv hell htend)

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
