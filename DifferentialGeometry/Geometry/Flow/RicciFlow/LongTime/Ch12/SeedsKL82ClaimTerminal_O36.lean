import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.TensorConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives

/-!
# CH12-O36, G3b-3: the event-terminal clause of `isRmBoundedBy`

* `terminal_rmNormSq_le_O36`: a bound on `|Rm|²` at a terminal-regular point along the incoming
  flow on a final time interval `(d, s)` passes to the terminal limit metric
  (`TerminalMetricConverges` on the compact set `{x}`, `C²` closeness, and continuity of
  `|Rm|²` under `C²` convergence).
* `isRmBoundedBy_of_stage_O36`: the event clause of `isRmBoundedBy` follows from its stage
  clause, since the crossing point at event `i` is the trace point on stage `i.castSucc`, which
  is the active stage on `(max a (time i.castSucc), time i.succ)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

/-- A final-time bound on `|Rm|²` along the incoming flow passes to the terminal metric. -/
theorem terminal_rmNormSq_le_O36 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    {B d : ℝ} (hd : d < s)
    (hb : ∀ v ∈ Ioo d s, normSq0S (G.flow.base.metric v) (x : P.Carrier) 4
        (metricRm04At (G.flow.base.metric v) (x : P.Carrier)) ≤ B) :
    normSq0S L.metric x 4 (metricRm04At L.metric x) ≤ B := by
  classical
  have hK : IsCompact ({x} : Set G.terminalRegularOpen) := isCompact_singleton
  have hex : ∀ k : ℕ, ∃ τ ∈ Ioo d s, ∀ j : ℕ, j ≤ 2 →
      CheegerGromovCompactness.metricDerivNorm j
        ((G.flow.base.metric τ).restrictOpen G.terminalRegularOpen) L.metric L.metric x <
        1 / ((k : ℝ) + 1) := by
    intro k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨d0, hd0, h0⟩ := L.converges {x} hK 0 _ hε
    obtain ⟨d1, hd1, h1⟩ := L.converges {x} hK 1 _ hε
    obtain ⟨d2, hd2, h2⟩ := L.converges {x} hK 2 _ hε
    have hDs : max (max d d0) (max d1 d2) < s :=
      max_lt (max_lt hd hd0.2) (max_lt hd1.2 hd2.2)
    have hle1 : d ≤ max (max d d0) (max d1 d2) := (le_max_left _ _).trans (le_max_left _ _)
    have hle2 : d0 ≤ max (max d d0) (max d1 d2) := (le_max_right _ _).trans (le_max_left _ _)
    have hle3 : d1 ≤ max (max d d0) (max d1 d2) := (le_max_left _ _).trans (le_max_right _ _)
    have hle4 : d2 ≤ max (max d d0) (max d1 d2) := (le_max_right _ _).trans (le_max_right _ _)
    refine ⟨(max (max d d0) (max d1 d2) + s) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    intro j hj
    interval_cases j
    · exact h0 _ ⟨by linarith, by linarith⟩ x rfl
    · exact h1 _ ⟨by linarith, by linarith⟩ x rfl
    · exact h2 _ ⟨by linarith, by linarith⟩ x rfl
  choose τ hτ hτb using hex
  have hconv : CheegerGromovCompactness.MetricCPConvergenceOn ({x} : Set G.terminalRegularOpen) 2
      (fun k => (G.flow.base.metric (τ k)).restrictOpen G.terminalRegularOpen)
      L.metric L.metric := by
    intro ε hε
    obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt hε
    refine ⟨k0, fun k hk => ?_⟩
    have hkk : 1 / ((k : ℝ) + 1) ≤ 1 / ((k0 : ℝ) + 1) := by
      have : (k0 : ℝ) ≤ k := by exact_mod_cast hk
      gcongr
    refine lt_of_le_of_lt
      (CheegerGromovCompactness.metricDerivNormSupOn_le_of_forall _ _ _ _ _ _ (by positivity)
        (fun j hj y hy => ?_)) (hkk.trans_lt hk0)
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hτb k j hj).le
  have ht := hconv.tendsto_normSq_metricRm04At hK (Set.mem_singleton x)
  refine le_of_tendsto' ht (fun k => ?_)
  rw [Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen]
  exact hb _ (hτ k)

/-- The event-terminal clause of `isRmBoundedBy` follows from its stage clause. -/
theorem isRmBoundedBy_of_stage_O36 (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon}
    {hat : a ≤ t} {p : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {K : ℝ}
    (hstage : ∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t),
      normSq0S (H.stageMetric (H.activeStage s) s)
        (A.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst)) 4
        (metricRm04At (H.stageMetric (H.activeStage s) s)
          (A.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst))) ≤
        K ^ 2) :
    A.isRmBoundedBy (hat := hat) K := by
  refine ⟨hstage, ?_⟩
  intro i hf hl
  -- the stage bound, transported along `activeStage s = j`
  have key : ∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t)
      (j : Fin (H.eventCount + 1)) (hj : H.activeStage s = j)
      (hf' : H.activeStage a ≤ j) (hl' : j ≤ H.activeStage t),
      normSq0S (H.stageMetric j s) (A.point j hf' hl') 4
        (metricRm04At (H.stageMetric j s) (A.point j hf' hl')) ≤ K ^ 2 := by
    intro s has hst j hj hf' hl'
    subst hj
    exact hstage s has hst
  have hmono := H.time_strictMono.monotone
  have hat_lt : (a : ℝ) < H.time i.succ := by
    by_contra hn
    have h1 := H.le_activeStage a i.succ (not_lt.mp hn)
    have h2 : i.castSucc < i.succ := i.castSucc_lt_succ
    exact absurd (h1.trans hf) (not_le.mpr h2)
  have htt : H.time i.succ ≤ (t : ℝ) :=
    (hmono hl).trans (H.activeStage_time_le t)
  have hd : max (a : ℝ) (H.time i.castSucc) < H.time i.succ :=
    max_lt hat_lt (H.time_strictMono (i.castSucc_lt_succ))
  apply terminal_rmNormSq_le_O36 (H.event i).incoming (H.event i).terminal _ hd
  intro v hv
  have hav : (a : ℝ) ≤ v := (le_max_left _ _).trans hv.1.le
  have hiv : H.time i.castSucc ≤ v := (le_max_right _ _).trans hv.1.le
  have hvt : v ≤ (t : ℝ) := hv.2.le.trans htt
  let vv : Icc (0 : ℝ) H.horizon := ⟨v, a.2.1.trans hav, hvt.trans t.2.2⟩
  have hact : H.activeStage vv = i.castSucc := by
    apply le_antisymm _ (H.le_activeStage vv i.castSucc hiv)
    by_contra hn
    have hsucc : i.succ ≤ H.activeStage vv := by
      rw [not_le] at hn
      exact Fin.castSucc_lt_iff_succ_le.mp hn
    have := (hmono hsucc).trans (H.activeStage_time_le vv)
    exact absurd hv.2 (not_lt.mpr this)
  have h := key vv hav hvt i.castSucc hact hf (i.castSucc_lt_succ.le.trans hl)
  simpa [ObservedHistory.stageMetric] using h

end GC.LongTime.Ch12
