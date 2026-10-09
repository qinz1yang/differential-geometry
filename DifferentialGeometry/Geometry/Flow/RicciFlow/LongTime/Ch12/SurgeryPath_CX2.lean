import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OutgoingSurvivor_CX2
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal

set_option autoImplicit false

noncomputable section

open Set Filter Manifold MeasureTheory DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Lift an entire outgoing path through one surgery, preserving its anchor,
smoothness, crossings, and length in the incoming terminal metric. -/
theorem lift_outgoing_path_CX2
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {r Λ K : ℝ}
    (hr : 0 < r) (hΛ : 1 ≤ Λ) (hKΛ : 2 * K < Λ ^ 2)
    (hδ : ∀ j, R.delta j ≤ 1 / 8646)
    (hnom : ∀ h, Λ * R.nominalRadius h ≤ r)
    (γ : ℝ → (H.stage i.succ).Carrier)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 γ (Icc (0 : ℝ) 1))
    (hscalar : ∀ s ∈ Icc (0 : ℝ) 1,
      metricScalarAt (H.event i).outputMetric (γ s) ≤ K / r ^ 2)
    (x : (H.event i).incoming.terminalRegularOpen)
    (hcross : (H.event i).RegularCrossing x.val (γ 0)) :
    ∃ η : ℝ → (H.event i).incoming.terminalRegularOpen,
      ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 η (Icc (0 : ℝ) 1) ∧ η 0 = x ∧
      (∀ s ∈ Icc (0 : ℝ) 1, (H.event i).RegularCrossing (η s).val (γ s)) ∧
      metricPathELength (H.event i).terminal.metric η 0 1 =
        metricPathELength (H.event i).outputMetric γ 0 1 := by
  let U := γ '' Icc (0 : ℝ) 1
  have hU : IsPreconnected U := isPreconnected_Icc.image _ hγ.continuousOn
  have hscalarU : ∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ K / r ^ 2 := by
    rintro y ⟨s, hs, rfl⟩
    exact hscalar s hs
  obtain ⟨E, hUE, _, hEcross, _⟩ := outgoing_survivor_chart_of_nominal_threshold_CX2 R
    hr hΛ hKΛ hδ hnom hU hscalarU ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ hcross
  let η : ℝ → (H.event i).incoming.terminalRegularOpen := (E.symm : _ → _) ∘ γ
  have hmap : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ E.target := fun s hs => hUE ⟨s, hs, rfl⟩
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 η (Icc (0 : ℝ) 1) :=
    (E.symm.contMDiffOn_toFun.of_le (by simp)).comp hγ hmap
  have hc : ∀ s ∈ Icc (0 : ℝ) 1, (H.event i).RegularCrossing (η s).val (γ s) :=
    fun s hs => hEcross (γ s) ⟨s, hs, rfl⟩
  have hη0 : η 0 = x := Subtype.ext ((H.event i).regularCrossing_left_unique
    (hc 0 ⟨le_rfl, zero_le_one⟩) hcross)
  refine ⟨η, hη, hη0, hc, ?_⟩
  rw [metricPathELength_eq, metricPathELength_eq]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro s hs
  have hηd : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel η s :=
    (hη.contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt (by norm_num)
  have heventually : ∀ᶠ z in 𝓝 s, (H.event i).RegularCrossing (η z).val (γ z) := by
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with z hz
    exact hc z hz
  have hm := (H.event i).metric_inner_eq_of_eventually_regularCrossing η γ hηd heventually
    (1 : ℝ) (1 : ℝ)
  exact congrArg (fun z : ℝ => ENNReal.ofReal (Real.sqrt z)) hm.symm

end GC.LongTime.Ch12
