import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ComponentDistance_CX11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TerminalPath_CX2

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Bundle TopologicalSpace DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Metric DifferentialGeometry.PDE.RicciFlow
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- The inverse-time distance estimate with a singular incoming terminal time.
Only the regular open set carries the terminal metric. CX2's smooth-path length
continuity supplies the limit; no metric is extended over the singular set. -/
theorem incoming_dist_le_terminal_of_ricci_CX11
    {P : OrientedThreeStage.{u}} {b e a c C ℓ : ℝ}
    (G : P.IncomingSlab b e) (L : G.TerminalLimitMetric)
    (hbc : b ≤ c) (hce : c < e) (hac : a ≤ c) (hC : 0 < C) (hℓ : 0 ≤ ℓ)
    (x y : G.terminalRegularOpen)
    (hterminal : riemannianEDistOf L.metric x y ≤ ENNReal.ofReal ℓ)
    (hRic : ∀ v ∈ Ioo c e, ∀ z : P.Carrier, ∀ w : TangentSpace ThreeModel z,
      (riemannianEDistOf (G.flow.base.metric v) x.val z <
          ENNReal.ofReal (Real.sqrt (3 * (v - a) / C)) ∨
        riemannianEDistOf (G.flow.base.metric v) y.val z <
          ENNReal.ofReal (Real.sqrt (3 * (v - a) / C))) →
      ricciTensor (G.flow.base.metric v) z w w ≤
        C / (v - a) * (G.flow.base.metric v).inner z w w) :
    riemannianEDistOf (G.flow.base.metric c) x.val y.val ≤
      ENNReal.ofReal (ℓ + 16 * Real.sqrt (C / 3) *
        (Real.sqrt (e - a) - Real.sqrt (c - a))) := by
  have happrox (ℓ' : ℝ) (hℓ' : ℓ < ℓ') :
      (riemannianEDistOf (G.flow.base.metric c) x.val y.val).toReal +
          16 * Real.sqrt (C / 3) * Real.sqrt (c - a) ≤
        ℓ' + 16 * Real.sqrt (C / 3) * Real.sqrt (e - a) ∧
      riemannianEDistOf (G.flow.base.metric c) x.val y.val ≠ ⊤ := by
    let : RiemannianBundle (TangentSpace ThreeModel : G.terminalRegularOpen → Type _) :=
      ⟨L.metric.toRiemannianMetric⟩
    have hlt : riemannianEDist ThreeModel x y < ENNReal.ofReal ℓ' :=
      hterminal.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hℓ.trans_lt hℓ')).mpr hℓ')
    obtain ⟨γ, hγ0, hγ1, hγ, hlen, _, _⟩ :=
      exists_lt_locally_constant_of_riemannianEDist_lt hlt zero_lt_one
    have hlen' : metricPathELength L.metric γ 0 1 < ENNReal.ofReal ℓ' := hlen
    let γ' : ℝ → P.Carrier := Subtype.val ∘ γ
    have hγ' : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ' :=
      (contMDiff_subtype_val (n := 1)).comp hγ
    have hdist (v : ℝ) : riemannianEDistOf (G.flow.base.metric v) x.val y.val ≤
        metricPathELength (G.flow.base.metric v) γ' 0 1 := by
      have hh := edistOf_le_metricPathELength (G.flow.base.metric v) zero_le_one hγ'.contMDiffOn
      simpa only [γ', Function.comp_apply, hγ0, hγ1] using hh
    have hlenfin (v : ℝ) : metricPathELength (G.flow.base.metric v) γ' 0 1 ≠ ⊤ := by
      rw [pathLength_eq_ofReal_arcLength_CX2 _ hγ']
      exact ENNReal.ofReal_ne_top
    have hfin (v : ℝ) : riemannianEDistOf (G.flow.base.metric v) x.val y.val ≠ ⊤ :=
      ne_top_of_le_ne_top (hlenfin v) (hdist v)
    have hyc : y.val ∈ connectedComponent x.val := by
      apply edistOf_ball_subset_connCompOpen (G.flow.base.metric c) x.val
        ((riemannianEDistOf (G.flow.base.metric c) x.val y.val).toReal + 1)
      exact (ENNReal.lt_ofReal_iff_toReal_lt (hfin c)).mpr (by linarith)
    let S := terminalPathSolution_CX2 L
    have hS := terminalPathSolution_isSolution_CX2 L
    have hcont := continuousOn_pathLength_CX2 S hS
      (a := c) (b := e) (fun _ hv => ⟨hbc.trans hv.1, hv.2⟩) hγ
    have hcR : ContinuousOn (fun v => (metricPathELength (S.base.metric v) γ 0 1).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt (v - a)) (Icc c e) := by
      apply ContinuousOn.add
      · intro v hv
        have hfin' : metricPathELength (S.base.metric v) γ 0 1 ≠ ⊤ := by
          rw [pathLength_eq_ofReal_arcLength_CX2 _ hγ]
          exact ENNReal.ofReal_ne_top
        exact (ENNReal.continuousAt_toReal hfin').comp_continuousWithinAt
          (f := fun z => metricPathELength (S.base.metric z) γ 0 1) (hcont v hv)
      · fun_prop
    have hbound : ∀ v ∈ Ioo c e,
        (riemannianEDistOf (G.flow.base.metric c) x.val y.val).toReal +
            16 * Real.sqrt (C / 3) * Real.sqrt (c - a) ≤
          (metricPathELength (S.base.metric v) γ 0 1).toReal +
            16 * Real.sqrt (C / 3) * Real.sqrt (v - a) := by
      intro v hv
      have hh := dist_le_of_ricci_inv_time_component_CX11 G.flow G.equation hC hac hv.1.le
        (fun z hz => ⟨hbc.trans hz.1, hz.2.trans_lt hv.2⟩)
        (fun z hz => ⟨hbc.trans_lt hz.1, hz.2.trans_lt hv.2⟩)
        (fun _ _ => RiemannianMetricComplete.of_compact _) x.val y.val hyc
        (fun z hz => hRic z ⟨hz.1, hz.2.trans_lt hv.2⟩)
      have hmetric : S.base.metric v = (G.flow.base.metric v).restrictOpen G.terminalRegularOpen :=
        L.extendedMetric_before hv.2
      rw [hmetric, pathLength_restrictOpen_CX2 _ _ _ hγ]
      exact hh.trans (add_le_add (ENNReal.toReal_mono (hlenfin v) (hdist v)) le_rfl)
    have hclosed := le_on_closure hbound continuousOn_const
      (by rw [closure_Ioo hce.ne]; exact hcR)
      (x := e) (by rw [closure_Ioo hce.ne]; exact ⟨hce.le, le_rfl⟩)
    have hterminalmetric : S.base.metric e = L.metric := L.extendedMetric_terminal
    rw [hterminalmetric] at hclosed
    exact ⟨hclosed.trans (add_le_add (ENNReal.toReal_lt_of_lt_ofReal hlen').le le_rfl), hfin c⟩
  have hfin := (happrox (ℓ + 1) (by linarith)).2
  have hreal : (riemannianEDistOf (G.flow.base.metric c) x.val y.val).toReal ≤
      ℓ + 16 * Real.sqrt (C / 3) * (Real.sqrt (e - a) - Real.sqrt (c - a)) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hh := (happrox (ℓ + ε) (by linarith)).1
    linarith
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hreal

end GC.LongTime.Ch12
