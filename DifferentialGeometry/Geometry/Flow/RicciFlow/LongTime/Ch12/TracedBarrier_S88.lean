import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.GlobalSurgeryPath_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.G3bTracedRegion_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OutgoingSurvivor_CX2

/-!
# CH12-S88, group 1a: the event barrier as the explicit input (replacing the global `hnom`)

CX2's `outgoing_survivor_chart_of_nominal_threshold_CX2` / `lift_global_outgoing_path_CX2` /
`record_seed_tracedRegion_CX2` use the cutoff hypotheses `δ ≤ 1/8646`, `Λ · nominalRadius ≤ r` of an
event record ONLY to obtain the barrier
  `Barrier(i, L) : a preconnected outgoing set U with scalar ≤ L, anchored at a regular crossing,
                   lies in the interior of the retained image  range (oldOutput)`
(`outgoing_low_scalar_subset_oldInterior_CX2`).  At micro scale `r = aρ` the global `hnom` is false
whenever a recent cut neck has nominal radius `≳ ρ`; the barrier is still true for the buffer if no
point of the buffer lies in the (young) cap of that event (hBuf).  Here the chain is re-run with the
barrier of each crossed event as the hypothesis (same proofs, `hsub` replaces the `hnom` step).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

universe u

/-- The barrier gives a single survivor chart covering the whole outgoing set `U`
(`outgoing_survivor_chart_of_nominal_threshold_CX2` with its `hsub` step as the hypothesis). -/
theorem outgoing_survivor_chart_of_barrier_S88
    {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {U : Set (H.stage i.succ).Carrier}
    {x : (H.event i).incoming.terminalRegularOpen} {y : (H.stage i.succ).Carrier}
    (hsub : U ⊆ interior (range (H.event i).oldOutput))
    (hcross : (H.event i).RegularCrossing x.val y) :
    ∃ E : PartialDiffeomorph ThreeModel ThreeModel
        (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞,
      U ⊆ E.target ∧ E x = y ∧
      (∀ q ∈ U, (H.event i).RegularCrossing (E.symm q).val q) ∧
      ∀ z ∈ E.source, ∀ v w : TangentSpace ThreeModel z,
        (H.event i).outputMetric.inner (E z)
          (mfderiv ThreeModel ThreeModel E z v) (mfderiv ThreeModel ThreeModel E z w) =
          (H.event i).terminal.metric.inner z v w := by
  obtain ⟨E, hsource, _, hxy, _, hEcross, hmetric⟩ :=
    hcross.exists_survivor_partialDiffeomorph (H.event i)
  have htarget : U ⊆ E.target := by
    intro q hq
    obtain ⟨z, hz⟩ := (H.event i).exists_terminal_regularCrossing_of_mem_interior_oldOutput q (hsub hq)
    obtain ⟨E', hsource', hz', _, _, _, _⟩ :=
      hz.exists_survivor_partialDiffeomorph (H.event i)
    have hzE : z ∈ E.source := by rwa [hsource, ← hsource']
    have heq : E z = q := (H.event i).regularCrossing_right_unique (hEcross z hzE) hz
    exact heq ▸ E.map_source hzE
  refine ⟨E, htarget, hxy, ?_, hmetric⟩
  intro q hq
  have hqE := htarget hq
  have hc := hEcross (E.symm q) (E.map_target hqE)
  have heq : E (E.symm q) = q := E.right_inv hqE
  exact (congrArg (fun z => (H.event i).RegularCrossing (E.symm q).val z) heq).mp hc

/-- The barrier needs no scalar bound once the connected set `U` avoids the frontier of the retained
image: a connected set anchored at a regular crossing that never meets `frontier (range oldOutput)`
lies in `interior (range oldOutput)`.  This is the interface to the cap analysis: the frontier of the
retained image lies in the cap window of the event (clause `hFront` of the S88 freeze), so
"`U` contains no young-cap point" (hBuf / `¬ CAP`) gives `hfree`. -/
theorem barrier_of_no_frontier_S88
    {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {U : Set (H.stage i.succ).Carrier} (hU : IsPreconnected U)
    {x : (H.event i).incoming.terminalRegularOpen} {y : (H.stage i.succ).Carrier}
    (hy : y ∈ U) (hcross : (H.event i).RegularCrossing x.val y)
    (hfree : Disjoint U (frontier (range (H.event i).oldOutput))) :
    U ⊆ interior (range (H.event i).oldOutput) := by
  apply hU.subset_of_closure_inter_subset isOpen_interior
    ⟨y, hy, crossing_mem_interior_oldOutput_CX2 (H.event i) hcross⟩
  intro q hq
  have hclosed := (H.event i).oldOutput_isClosedEmbedding.isClosed_range
  have hqr : q ∈ range (H.event i).oldOutput := (closure_minimal interior_subset hclosed) hq.1
  by_contra hqi
  exact Set.disjoint_left.mp hfree hq.2 ⟨by rwa [hclosed.closure_eq], hqi⟩

/-- One surgery step for the path induction with the barrier of the event as the hypothesis,
restricted to a location set `T` of the outgoing stage (`lift_global_outgoing_path_CX2` with `hδ`,
`hnom` replaced by `hbar`; `T = univ` is the universal form `lift_outgoing_path_of_barrier_S88`).
The restricted form is the one the cap analysis can supply: `T` = the outgoing points that are traces
of buffer points. -/
theorem lift_outgoing_path_of_barrier_in_S88
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {r K : ℝ}
    (T : Set (H.stage i.succ).Carrier)
    (hbar : ∀ U : Set (H.stage i.succ).Carrier, U ⊆ T → IsPreconnected U →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      ∀ (x : (H.event i).incoming.terminalRegularOpen) (y : (H.stage i.succ).Carrier),
        y ∈ U → (H.event i).RegularCrossing x.val y → U ⊆ interior (range (H.event i).oldOutput))
    (γ : ℝ → (H.stage i.succ).Carrier)
    (hγT : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ T)
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
  have h0 : γ 0 ∈ U := ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  obtain ⟨E, hUE, _, hEcross, _⟩ := outgoing_survivor_chart_of_barrier_S88
    (hbar U (by rintro _ ⟨z, hz, rfl⟩; exact hγT z hz) hU hscalar x (γ 0) h0 hcross) hcross
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

/-- Universal form (`T = univ`): exactly the `hprotect` clause of `bounded_trace_of_seed_path_CX2`
for the event `i`. -/
theorem lift_outgoing_path_of_barrier_S88
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {r K : ℝ}
    (hbar : ∀ U : Set (H.stage i.succ).Carrier, IsPreconnected U →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      ∀ (x : (H.event i).incoming.terminalRegularOpen) (y : (H.stage i.succ).Carrier),
        y ∈ U → (H.event i).RegularCrossing x.val y → U ⊆ interior (range (H.event i).oldOutput))
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
          (metricRm04At (H.event i).terminal.metric (η s))) ≤ K / r ^ 2 :=
  lift_outgoing_path_of_barrier_in_S88 univ (fun U _ => hbar U) γ (fun _ _ => mem_univ _) hγ hclip
    hRm x hcross

/-- G3b on an actual history with the per-event barriers (the `hδ`, `hnom` of
`record_seed_tracedRegion_CX2` replaced by the barrier at `L = 9K/r²`, and `Λ` dropped). -/
theorem record_seed_tracedRegion_barrier_S88 (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} {τ r K : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) (hK : 0 < K)
    (hexp : Real.exp (9 * K * τ) < 2)
    (ha : a.val = t.val - τ * r ^ 2) (hat : a ≤ t)
    (hregular : H.time (H.activeStage t) < t.val)
    {p y : (H.stageAt t).Carrier}
    (hy : y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r)
    (Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ K / r ^ 2)
    (hbar : ∀ (i : Fin H.eventCount), H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage t →
      ∀ U : Set (H.stage i.succ).Carrier, IsPreconnected U →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      ∀ (x : (H.event i).incoming.terminalRegularOpen) (y : (H.stage i.succ).Carrier),
        y ∈ U → (H.event i).RegularCrossing x.val y → U ⊆ interior (range (H.event i).oldOutput)) :
    H.isTracedRegion t p (2 * r) (τ * r ^ 2) (K / r ^ 2) := by
  have hdepth : 0 < τ * r ^ 2 := by positivity
  have hat' : a < t := show a.val < t.val from by rw [ha]; linarith
  have hroom : pathBudget_CX2 (K / r ^ 2) r t a < 20 * r := by
    have he : 9 * (K / r ^ 2) * (t.val - a.val) = 9 * K * τ := by
      rw [ha]
      field_simp
      ring
    unfold pathBudget_CX2
    rw [he]
    exact (six_radius_length_CX2 hr hexp).1.trans (six_radius_length_CX2 hr hexp).2
  refine ⟨by positivity, hdepth, a, hat, ha, ?_⟩
  intro x hx
  apply bounded_trace_of_seed_path_CX2 H hat' hregular Y hr (by positivity) hy hroom hbound ?_ x hx
  intro i hf hl γ hγ hclip hRm q hcross
  exact lift_outgoing_path_of_barrier_S88 (hbar i hf hl) γ hγ hclip hRm q hcross

end GC.LongTime.Ch12
