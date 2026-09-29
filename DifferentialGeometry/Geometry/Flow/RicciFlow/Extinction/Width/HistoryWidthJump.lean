import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildSimplyConnected
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.SurgeryWidthEvolution

noncomputable section

universe u v

open Bundle Manifold Set Filter MeasureTheory CategoryTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

theorem rfs_actual_width_jump_of_child_comparison {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {parameters : CutoffParameters} (G : GeometricCutoffRecord H i parameters)
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier)
    (c : ConnectedComponents (H.stage i.succ).Carrier)
    (hchild : ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
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
                ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y) :
    letI := hSC (G.transition.childParent c)
    ENNReal.ofReal (componentWidth (H.stage i.succ) (H.event i).outputMetric c
      (G.transition.child_simplyConnected c)) ≤
      liminf (fun s => ENNReal.ofReal
        (componentWidth (H.stage i.castSucc) ((H.event i).incoming.flow.base.metric s)
          (G.transition.childParent c) (hSC (G.transition.childParent c))))
        (𝓝[<] (H.time i.succ)) := by
  let := (H.stage i.castSucc).component_connected (G.transition.childParent c)
  let := (H.stage i.succ).component_connected c
  let := hSC (G.transition.childParent c)
  let := G.transition.child_simplyConnected c
  obtain ⟨f, _hsupport, hdegree, s₀, hs₀, ell, hell, hlim, hlip⟩ := hchild
  have hdeg : orientedDegree (G.Parent c).orientation (G.Child c).orientation (f c) = 1 := by
    apply (orientedDegree_eq_iff _ _ _ 1).mpr
    simpa only [one_smul] using hdegree c
  have hcomp : ∀ (g : (G.Parent c).Metric) (h : (G.Child c).Metric)
      (f : C((G.Parent c).Carrier, (G.Child c).Carrier)) (L : ℝ≥0),
      FreeHomotopyClass.map (contractibleLoopPostcompose f)
          (positiveFreeContractibleClass (G.Parent c).orientation) =
        positiveFreeContractibleClass (G.Child c).orientation →
      (∀ x y, riemannianEDistOf h (f x) (f y) ≤
        (L : ℝ≥0∞) * riemannianEDistOf g x y) →
      canonicalWidth h (G.Child c).orientation ≤
        (L : ℝ) ^ 2 * canonicalWidth g (G.Parent c).orientation := by
    intro g h f L hclass hf
    have hw := rfs_width_lipschitz g h f L hf
      (positiveFreeContractibleClass (G.Parent c).orientation)
    rw [hclass] at hw
    exact hw
  apply rfs_comparison_width_transition (G.Parent c).orientation (G.Child c).orientation
    hcomp _ _ (f c)
    (positiveFreeContractibleClass_natural _ _ (f c) hdeg) ell hlim
  filter_upwards [Ioo_mem_nhdsLT hs₀.2] with s hs
  exact ⟨le_trans zero_le_one (hell s hs), hlip c s hs⟩

theorem historyWidth_atZero_continuous (P : OrientedThreeStage.{u}) (g : P.Metric)
    (h0 : ∀ c : ConnectedComponents P.Carrier,
      SimplyConnectedSpace ((P.component c).Carrier))
    (terminal : ConnectedComponents P.Carrier) :
    Continuous (historyWidth (ObservedHistory.atZero P g) h0 terminal) := by
  have hsubsing : Subsingleton (Icc (0 : ℝ) 0) :=
    ⟨fun a b => Subtype.ext
      (le_antisymm (a.2.2.trans b.2.1) (b.2.2.trans a.2.1))⟩
  have hsub : (historyWidth (ObservedHistory.atZero P g) h0 terminal) =
      fun _ => historyWidth (ObservedHistory.atZero P g) h0 terminal
        (historyStageTime (ObservedHistory.atZero P g) 0) :=
    funext fun t => congrArg _ (hsubsing.elim t _)
  rw [hsub]
  exact continuous_const

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
