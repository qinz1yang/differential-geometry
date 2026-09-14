import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CollapseDegreeInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonMetric

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

theorem exists_eq_zsmul_pos_generator_eq :
    ∃ (k : ℤ) (x y : ℤ), x = k • y ∧ 0 < k ∧
      (∃ φ : ℤ →ₗ[ℤ] ℤ, φ x = 1) ∧ x = y :=
  ⟨1, 1, 1, by norm_num, by norm_num, ⟨LinearMap.id, rfl⟩, rfl⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

structure ChildComparisonInputs
    (a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3)
    (b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3) where
  Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c
  collapse : G.LocalTerminalEDistComparison Kc
  convergenceTime : ℝ
  convergenceTime_mem : convergenceTime ∈ Ico (H.time i.castSucc) (H.time i.succ)
  scale : ℝ → ℝ
  scale_one : ∀ s ∈ Ioo convergenceTime (H.time i.succ), 1 ≤ scale s
  scale_tendsto : Filter.Tendsto scale (𝓝[<] (H.time i.succ)) (𝓝 1)
  convergence : G.LocalTerminalParentEDistComparison Kc convergenceTime scale
  multiplier : (c : ConnectedComponents (H.stage i.succ).Carrier) → ℤ
  map_eq : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
    integralHomologyMap 3 (Kc c).rfs_whole_parent_map (a c) = multiplier c • b c
  generator : ∀ c : ConnectedComponents (H.stage i.succ).Carrier,
    ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (integralHomologyMap 3 (Kc c).rfs_whole_parent_map (a c)) = 1
  positive : ∀ c : ConnectedComponents (H.stage i.succ).Carrier, 0 < multiplier c

variable {G}

theorem ChildComparisonInputs.localLengthComparison
    {a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3}
    {b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3}
    (h : G.ChildComparisonInputs a b) :
    G.LocalLengthComparison h.Kc :=
  G.localLengthComparison_of_terminal_comparisons h.Kc h.convergenceTime_mem
    h.collapse h.convergence h.scale_one h.scale_tendsto

theorem ChildComparisonInputs.integralHomologyMap_eq
    {a : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Parent c).Carrier 3}
    {b : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      IntegralHomology (G.Child c).Carrier 3}
    (h : G.ChildComparisonInputs a b)
    (c : ConnectedComponents (H.stage i.succ).Carrier) :
    integralHomologyMap 3 (h.Kc c).rfs_whole_parent_map (a c) = b c :=
  (ComparisonSupport.rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator
    (K := h.Kc c) (a c) (b c)
    (ComparisonSupport.localTerminalDistanceControl_of_localTerminalEDistComparison
      (c := c) h.Kc h.collapse)
    (h.map_eq c) (h.generator c) (h.positive c)).2.2.2.1

theorem rfs_child_comparison_of_data
    (h : G.ChildComparisonInputs
      (fun c => fundamentalClass (G.Parent c).orientation)
      (fun c => fundamentalClass (G.Child c).orientation)) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c)
          (fundamentalClass (G.Parent c).orientation) =
        fundamentalClass (G.Child c).orientation) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  rfs_child_comparison_of_local_length_comparison G h.Kc
    (fun c => h.integralHomologyMap_eq c) h.localLengthComparison

theorem rfs_child_comparison_of_nonempty_data
    (h : Nonempty (G.ChildComparisonInputs
      (fun c => fundamentalClass (G.Parent c).orientation)
      (fun c => fundamentalClass (G.Child c).orientation))) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      (∀ c, integralHomologyMap 3 (f c)
          (fundamentalClass (G.Parent c).orientation) =
        fundamentalClass (G.Child c).orientation) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  rfs_child_comparison_of_data h.some

theorem nonempty_comparisonSupport_of_simplyConnected
    [∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier] :
    Nonempty ((c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :=
  ⟨fun c => Classical.choice (G.rfs_comparison_support c)⟩

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
