import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedPath_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RecentProtection_CX2

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- A short seed path can be chosen globally smooth and constant outside
its parameter interval; these properties survive every chart transport. -/
theorem exists_global_seed_path_CX2 (P : OrientedThreeStage.{u}) (g : P.Metric)
    {p y x : P.Carrier} {r : ℝ} (hr : 0 < r)
    (hy : y ∈ riemannianBallOf g p r) (hx : x ∈ riemannianBallOf g p (2 * r)) :
    ∃ γ : ℝ → P.Carrier, γ 0 = y ∧ γ 1 = x ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ ∧
      (∀ s, γ s = γ (projIcc (0 : ℝ) 1 zero_le_one s)) ∧
      metricPathELength g γ 0 1 < ENNReal.ofReal (3 * r) := by
  obtain ⟨β, hβ0, hβ1, hβ, hlen⟩ := exists_seed_to_ball_path_CX2 P g hr hy hx
  let γ := β ∘ Real.smoothTransition
  have hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ := by
    rw [← contMDiffOn_univ]
    apply hβ.comp
    · rw [contMDiffOn_univ, contMDiff_iff_contDiff]
      fun_prop
    · intro s _
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨γ, by simpa [γ] using hβ0, by simpa [γ] using hβ1, hγ, ?_, ?_⟩
  · intro s
    simp only [γ, Function.comp_apply, Real.smoothTransition.projIcc]
  · have heq : metricPathELength g γ 0 1 = metricPathELength g β 0 1 := by
      let : RiemannianBundle (TangentSpace ThreeModel : P.Carrier → Type _) := ⟨g.toRiemannianMetric⟩
      change pathELength ThreeModel (β ∘ Real.smoothTransition) 0 1 = pathELength ThreeModel β 0 1
      rw [pathELength_comp_of_monotoneOn zero_le_one (Real.smoothTransition.monotone.monotoneOn _)]
      · simp only [Real.smoothTransition.zero, Real.smoothTransition.one]
      · exact (Real.smoothTransition.contDiff : ContDiff ℝ 1 Real.smoothTransition).contDiffOn.differentiableOn (by norm_num)
      · simpa only [Real.smoothTransition.zero, Real.smoothTransition.one] using
          hβ.mdifferentiableOn (by norm_num)
    exact heq.trans_lt hlen

/-- One surgery step for the path induction, with global smoothness and a
compact parameter range, and with the incoming terminal curvature bound. -/
theorem lift_global_outgoing_path_CX2
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) {r Λ K : ℝ}
    (hr : 0 < r) (hΛ : 1 ≤ Λ) (hKΛ : 2 * (9 * K) < Λ ^ 2)
    (hδ : ∀ j, R.delta j ≤ 1 / 8646) (hnom : ∀ h, Λ * R.nominalRadius h ≤ r)
    (γ : ℝ → (H.stage i.succ).Carrier)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hclip : ∀ s, γ s = γ (projIcc (0 : ℝ) 1 zero_le_one s))
    (hRm : ∀ s ∈ Icc (0 : ℝ) 1,
      Real.sqrt (normSq0S (H.event i).outputMetric (γ s) 4
        (metricRm04At (H.event i).outputMetric (γ s))) ≤ K / r ^ 2)
    (x : (H.event i).incoming.terminalRegularOpen)
    (hcross : (H.event i).RegularCrossing x.val (γ 0)) :
    ∃ η : ℝ → (H.event i).incoming.terminalRegularOpen,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧
      (∀ s, η s = η (projIcc (0 : ℝ) 1 zero_le_one s)) ∧ η 0 = x ∧
      (∀ s ∈ Icc (0 : ℝ) 1, (H.event i).RegularCrossing (η s).val (γ s)) ∧
      metricPathELength (H.event i).terminal.metric η 0 1 =
        metricPathELength (H.event i).outputMetric γ 0 1 ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        Real.sqrt (normSq0S (H.event i).terminal.metric (η s) 4
          (metricRm04At (H.event i).terminal.metric (η s))) ≤ K / r ^ 2 := by
  let U := γ '' Icc (0 : ℝ) 1
  have hU : IsPreconnected U := isPreconnected_Icc.image _ hγ.continuous.continuousOn
  have hscalar : ∀ z ∈ U, metricScalarAt (H.event i).outputMetric z ≤ (9 * K) / r ^ 2 := by
    rintro z ⟨s, hs, rfl⟩
    exact scalar_le_nine_rm_bound_CX2 _ _ _ (hRm s hs)
  obtain ⟨E, hUE, _, hEcross, _⟩ := outgoing_survivor_chart_of_nominal_threshold_CX2 R
    hr hΛ hKΛ hδ hnom hU hscalar ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ hcross
  let η : ℝ → (H.event i).incoming.terminalRegularOpen := (E.symm : _ → _) ∘ γ
  have htarget (s : ℝ) : γ s ∈ E.target := by
    apply hUE
    exact ⟨projIcc 0 1 zero_le_one s, (projIcc 0 1 zero_le_one s).property, (hclip s).symm⟩
  have hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η := by
    rw [← contMDiffOn_univ]
    exact (E.symm.contMDiffOn_toFun.of_le (by simp)).comp hγ.contMDiffOn (fun s _ => htarget s)
  have hc : ∀ s ∈ Icc (0 : ℝ) 1, (H.event i).RegularCrossing (η s).val (γ s) :=
    fun s hs => hEcross (γ s) ⟨s, hs, rfl⟩
  refine ⟨η, hη, fun s => congrArg E.symm (hclip s),
    Subtype.ext ((H.event i).regularCrossing_left_unique (hc 0 ⟨le_rfl, zero_le_one⟩) hcross), hc, ?_, ?_⟩
  · rw [metricPathELength_eq, metricPathELength_eq]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro s hs
    have heventually : ∀ᶠ z in 𝓝 s, (H.event i).RegularCrossing (η z).val (γ z) := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with z hz
      exact hc z hz
    have hm := (H.event i).metric_inner_eq_of_eventually_regularCrossing η γ
      (hη.mdifferentiableAt (by norm_num)) heventually (1 : ℝ) (1 : ℝ)
    exact congrArg (fun z : ℝ => ENNReal.ofReal (Real.sqrt z)) hm.symm
  · intro s hs
    exact (congrArg Real.sqrt (MetricCutCapEvent.RegularCrossing.rmNormSq_eq
      (H.event i) (p := η s) (hc s hs))).trans_le (hRm s hs)

end GC.LongTime.Ch12
