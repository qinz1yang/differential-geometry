import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82DistBootSlab_S68
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82TerminalDistance_CX11

/-!
# CH12-S68, Group G2: the terminal-time distance estimate with a Ricci bound on a fixed ball

`incoming_dist_le_terminal_of_ricci_CX11` with the Ricci hypothesis around both `x` and `y`
replaced by `Ric ≤ C/(v−a)` on `B_v(x, R0)` (`v ∈ (c, e)`) plus the margin
`ℓ + 16√(C/3)√(e−a) + √(3(e−a)/C) < R0`.  The proof is CX11's (terminal path solution; length of a
smooth path is continuous up to the terminal time), with the slab estimate `dist_boot_slab_S68`
applied on `[c, v]` for `v` close to `e`, where the margin holds for the length of the chosen
path (continuity at `e`).
-/

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
/-- **G2 (terminal, ball form).**  The inverse-time distance estimate with a singular incoming
terminal time, with the Ricci bound only on the `R0`-ball around `x`. -/
theorem incoming_dist_boot_terminal_S68
    {P : OrientedThreeStage.{u}} {b e a c C R0 ℓ : ℝ}
    (G : P.IncomingSlab b e) (L : G.TerminalLimitMetric)
    (hbc : b ≤ c) (hce : c < e) (hac : a ≤ c) (hC : 0 < C) (hℓ : 0 ≤ ℓ)
    (x y : G.terminalRegularOpen)
    (hterminal : riemannianEDistOf L.metric x y ≤ ENNReal.ofReal ℓ)
    (hmargin : ℓ + 16 * Real.sqrt (C / 3) * Real.sqrt (e - a) + Real.sqrt (3 * (e - a) / C) < R0)
    (hRic : ∀ v ∈ Ioo c e, ∀ z : P.Carrier, ∀ w : TangentSpace ThreeModel z,
      riemannianEDistOf (G.flow.base.metric v) x.val z < ENNReal.ofReal R0 →
      ricciTensor (G.flow.base.metric v) z w w ≤
        C / (v - a) * (G.flow.base.metric v).inner z w w) :
    riemannianEDistOf (G.flow.base.metric c) x.val y.val ≤
      ENNReal.ofReal (ℓ + 16 * Real.sqrt (C / 3) *
        (Real.sqrt (e - a) - Real.sqrt (c - a))) := by
  have happrox (ℓ' : ℝ) (hℓ' : ℓ < ℓ')
      (hℓR : ℓ' + 16 * Real.sqrt (C / 3) * Real.sqrt (e - a) + Real.sqrt (3 * (e - a) / C) ≤ R0) :
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
    have hterminalmetric : S.base.metric e = L.metric := L.extendedMetric_terminal
    -- the margin holds for the length of `γ` near the terminal time
    have hF : ContinuousOn (fun v => (metricPathELength (S.base.metric v) γ 0 1).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt (v - a) + Real.sqrt (3 * (v - a) / C)) (Icc c e) :=
      hcR.add (by fun_prop : Continuous fun v : ℝ => Real.sqrt (3 * (v - a) / C)).continuousOn
    have hFe : (metricPathELength (S.base.metric e) γ 0 1).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt (e - a) + Real.sqrt (3 * (e - a) / C) < R0 := by
      rw [hterminalmetric]
      have := ENNReal.toReal_lt_of_lt_ofReal hlen'
      linarith
    have hev : ∀ᶠ v in 𝓝[Icc c e] e, (metricPathELength (S.base.metric v) γ 0 1).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt (v - a) + Real.sqrt (3 * (v - a) / C) < R0 :=
      (hF e ⟨hce.le, le_rfl⟩).eventually (Iio_mem_nhds hFe)
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
    have hc'e : max c (e - ε) < e := max_lt hce (by linarith)
    have hbound : ∀ v ∈ Ioo (max c (e - ε)) e,
        (riemannianEDistOf (G.flow.base.metric c) x.val y.val).toReal +
            16 * Real.sqrt (C / 3) * Real.sqrt (c - a) ≤
          (metricPathELength (S.base.metric v) γ 0 1).toReal +
            16 * Real.sqrt (C / 3) * Real.sqrt (v - a) := by
      intro v hv
      have hvc : c < v := (le_max_left _ _).trans_lt hv.1
      have hve : e - ε < v := (le_max_right _ _).trans_lt hv.1
      have hFv := hsub (show v ∈ Metric.ball e ε ∩ Icc c e from
        ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hv.2],
          ⟨hvc.le, hv.2.le⟩⟩)
      have hmetric : S.base.metric v = (G.flow.base.metric v).restrictOpen G.terminalRegularOpen :=
        L.extendedMetric_before hv.2
      have hlenv : metricPathELength (S.base.metric v) γ 0 1 =
          metricPathELength (G.flow.base.metric v) γ' 0 1 := by
        rw [hmetric, pathLength_restrictOpen_CX2 _ _ _ hγ]
      have hdv : (riemannianEDistOf (G.flow.base.metric v) x.val y.val).toReal ≤
          (metricPathELength (S.base.metric v) γ 0 1).toReal := by
        rw [hlenv]
        exact ENNReal.toReal_mono (hlenv ▸ hlenfin v) (hdist v)
      have hmarg : (riemannianEDistOf (G.flow.base.metric v) x.val y.val).toReal +
          16 * Real.sqrt (C / 3) * Real.sqrt (v - a) + Real.sqrt (3 * (v - a) / C) < R0 := by
        have : (metricPathELength (S.base.metric v) γ 0 1).toReal +
          16 * Real.sqrt (C / 3) * Real.sqrt (v - a) + Real.sqrt (3 * (v - a) / C) < R0 := hFv
        linarith
      have hh := dist_boot_slab_S68 G.flow G.equation hC hac hvc.le
        (fun z hz => ⟨hbc.trans hz.1, hz.2.trans_lt hv.2⟩)
        (fun z hz => ⟨hbc.trans_lt hz.1, hz.2.trans_lt hv.2⟩)
        (fun _ _ => RiemannianMetricComplete.of_compact _) x.val y.val hyc hmarg
        (fun v' hv' z w hz => hRic v' ⟨hv'.1, hv'.2.trans_lt hv.2⟩ z w hz)
        c ⟨le_rfl, hvc.le⟩
      linarith
    have hclosed := le_on_closure hbound continuousOn_const
      (by rw [closure_Ioo hc'e.ne]; exact hcR.mono (Icc_subset_Icc_left (le_max_left _ _)))
      (x := e) (by rw [closure_Ioo hc'e.ne]; exact ⟨hc'e.le, le_rfl⟩)
    rw [hterminalmetric] at hclosed
    exact ⟨hclosed.trans (add_le_add (ENNReal.toReal_lt_of_lt_ofReal hlen').le le_rfl), hfin c⟩
  -- room: the margin is strict, so some `ℓ' > ℓ` fits
  set ε0 : ℝ := R0 - (ℓ + 16 * Real.sqrt (C / 3) * Real.sqrt (e - a) + Real.sqrt (3 * (e - a) / C))
    with hε0
  have hε0pos : 0 < ε0 := by rw [hε0]; linarith
  have hfin := (happrox (ℓ + ε0 / 2) (by linarith) (by rw [hε0]; linarith)).2
  have hreal : (riemannianEDistOf (G.flow.base.metric c) x.val y.val).toReal ≤
      ℓ + 16 * Real.sqrt (C / 3) * (Real.sqrt (e - a) - Real.sqrt (c - a)) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hh := (happrox (ℓ + min ε (ε0 / 2)) (by have := lt_min hε (by linarith : 0 < ε0 / 2); linarith)
      (by have := min_le_right ε (ε0 / 2); rw [hε0] at *; linarith)).1
    have := min_le_left ε (ε0 / 2)
    linarith
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hreal

end GC.LongTime.Ch12
