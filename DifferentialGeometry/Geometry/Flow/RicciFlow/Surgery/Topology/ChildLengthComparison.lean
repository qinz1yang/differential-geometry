import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonCompactSupport
import DifferentialGeometry.Geometry.Metric.CurveVariation.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildTerminalDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalRegionConvexity

noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

private theorem local_length_comparison_of_local_terminal_edist_comparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hcollapse : G.LocalTerminalEDistComparison Kc) :
    G.LocalLengthComparison Kc := by
  obtain ⟨K, hK, hsupport, d, hd, ell, hell, htend, hquad⟩ :=
    G.exists_compact_comparison_support_quad_modulus Kc
  refine ⟨d, hd, ell, hell, htend, ?_⟩
  intro c s hs x hx
  obtain ⟨V, hV, hterm, hcollapseV⟩ := hcollapse c x hx
  let U : Set (G.Parent c).Carrier :=
    Subtype.val ⁻¹' (Subtype.val '' interior K)
  have hU : IsOpen U :=
    ((H.event i).incoming.terminalRegularRegion_isOpen.isOpenMap_subtype_val
      (interior K) isOpen_interior).preimage continuous_subtype_val
  have hxU : x ∈ U := ⟨⟨x.1, (Kc c).support_terminal x hx⟩, hsupport c x hx, rfl⟩
  refine ⟨U ∩ V, Filter.inter_mem (hU.mem_nhds hxU) hV, ?_⟩
  intro a b γ hab hγ hmap hfin
  let γT : ℝ → (H.event i).incoming.terminalRegularOpen := fun t =>
    ⟨(γ (projIcc a b hab t)).1,
      hterm (γ (projIcc a b hab t)) (hmap (projIcc a b hab t).property).2⟩
  have hγT : Continuous γT := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp_continuousOn hγ).domRestrict).comp
      continuous_projIcc
  have hγeq (t : ℝ) (ht : t ∈ Icc a b) : (γT t).1 = (γ t).1 := by
    simp only [γT, projIcc_of_mem, ht]
  have hγK : MapsTo γT (Icc a b) (interior K) := by
    intro t ht
    obtain ⟨z, hz, heq⟩ := (hmap ht).1
    have heq' : γT t = z := Subtype.ext ((hγeq t ht).trans heq.symm)
    exact heq' ▸ hz
  have hlength : riemannianCurveLength
      ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
      (fun t => (Kc c).canonicalWholeParentMap (γ t)) a b ≤
        riemannianCurveLength (H.event i).terminal.metric γT a b := by
    unfold riemannianCurveLength
    apply iSup_le
    intro p
    refine (Finset.sum_le_sum fun j hj => ?_).trans
      (le_iSup (f := fun q : ℕ × {v : ℕ → ℝ // Monotone v ∧ ∀ j, v j ∈ Icc a b} =>
        ∑ j ∈ Finset.range q.1,
          riemannianEDistOf (H.event i).terminal.metric
            (γT (q.2.1 (j + 1))) (γT (q.2.1 j))) p)
    have ht₁ := p.2.2.2 (j + 1)
    have ht₀ := p.2.2.2 j
    have hb := hcollapseV (γ (p.2.1 (j + 1))) (hmap ht₁).2
      (γ (p.2.1 j)) (hmap ht₀).2
      (hterm _ (hmap ht₁).2) (hterm _ (hmap ht₀).2)
    convert hb using 1
    congr 1 <;> apply Subtype.ext <;>
      simp only [γT, projIcc_of_mem, ht₀, ht₁]
  have hmetric : riemannianCurveLength (H.event i).terminal.metric γT a b ≤
      ENNReal.ofReal (ell s) * riemannianCurveLength
        (((H.event i).incoming.flow.base.metric s).restrictOpen
          (H.event i).incoming.terminalRegularOpen) γT a b := by
    have hb := DifferentialGeometry.Geometry.riemannianCurveVariation_le_of_quad_on
      (((H.event i).incoming.flow.base.metric s).restrictOpen
        (H.event i).incoming.terminalRegularOpen) (H.event i).terminal.metric
      (⟨interior K, isOpen_interior⟩ : TopologicalSpace.Opens
        (H.event i).incoming.terminalRegularOpen)
      (c := (ell s) ^ 2) (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one (hell s hs)))
      (fun y hy v => hquad s hs y (interior_subset hy) v)
      hγT.continuousOn hγK
    simpa only [riemannianCurveLength, DifferentialGeometry.Geometry.riemannianCurveVariation,
      Real.sqrt_sq (zero_le_one.trans (hell s hs))] using hb
  have hincoming : riemannianCurveLength
      (((H.event i).incoming.flow.base.metric s).restrictOpen
        (H.event i).incoming.terminalRegularOpen) γT a b =
      riemannianCurveLength ((H.stage i.castSucc).componentMetric
        ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) γ a b := by
    change DifferentialGeometry.Geometry.riemannianCurveVariation
      (((H.event i).incoming.flow.base.metric s).restrictOpen
        (H.event i).incoming.terminalRegularOpen) γT a b =
      DifferentialGeometry.Geometry.riemannianCurveVariation ((H.stage i.castSucc).componentMetric
        ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) γ a b
    rw [DifferentialGeometry.Geometry.riemannianCurveVariation_restrictOpen _ _ _ _ _ hγT.continuousOn]
    have hcongr := DifferentialGeometry.Geometry.riemannianCurveVariation_congr ((H.event i).incoming.flow.base.metric s)
      (show EqOn (Subtype.val ∘ γT) (Subtype.val ∘ γ) (Icc a b) from hγeq)
    rw [hcongr]
    unfold DifferentialGeometry.Geometry.riemannianCurveVariation
    simp only [OrientedThreeStage.edistOf_componentMetric]
    rfl
  exact hlength.trans (by simpa only [hincoming] using hmetric)


theorem local_length_comparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :
    G.LocalLengthComparison Kc :=
  G.local_length_comparison_of_local_terminal_edist_comparison Kc
    (G.local_terminal_edist_comparison Kc)

theorem child_comparison_metric
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, f c = (Kc c).canonicalWholeParentMap) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  G.rfs_child_comparison_metric_of_local_length_comparison Kc (G.local_length_comparison Kc)

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
