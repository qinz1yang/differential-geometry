import DifferentialGeometry.Geometry.Metric.Comparison.ScalarGradient
import DifferentialGeometry.Topology.Sequences.UniformEventually
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapScalarBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceForwardScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapScalarLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTraceConstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Mathlib.Analysis.SpecificLimits.Basic

section
noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem exists_stage_time_le_and_lt_succ (H : ObservedHistory.{u})
    (last : Fin (H.eventCount + 1)) {c : ℝ} (hc : 0 ≤ c) :
    ∃ first : Fin (H.eventCount + 1), first ≤ last ∧ H.time first ≤ c ∧
      ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → c < H.time j.succ := by
  by_cases hlast : H.time last ≤ c
  · refine ⟨last, le_rfl, hlast, ?_⟩
    intro j hj hl
    exact False.elim ((not_lt_of_ge hl) (hj.trans_lt j.castSucc_lt_succ))
  · have hclast : c < H.time last := lt_of_not_ge hlast
    let t : Set.Icc (0 : ℝ) H.horizon :=
      ⟨c, hc, hclast.le.trans (H.time_le_horizon_at last)⟩
    refine ⟨H.activeStage t,
      H.time_strictMono.le_iff_le.mp ((H.activeStage_time_le t).trans hclast.le),
      H.activeStage_time_le t, ?_⟩
    intro j hj _
    by_contra h
    have hsucc := H.le_activeStage t j.succ (le_of_not_gt h)
    exact (not_lt_of_ge hsucc) (hj.trans_lt j.castSucc_lt_succ)

private theorem exists_backwardPointTrace_or_recent_presented_cap_of_nonnegative_window
    (H : ObservedHistory.{u}) (last : Fin (H.eventCount + 1))
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen)
    {q Q θ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hθsmall : θ ≤ 1 / 4) (hbudget : 6 * C * θ ≤ 1)
    (hroom : 0 ≤ s - θ / Q)
    (hscalar : metricScalarAt L.metric x ≤ (3 / 2 : ℝ) * Q)
    (hderiv : ∀ j : Fin H.eventCount, j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      s - θ / Q ≤ t → q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ t ∈ Ioo (H.time last) s, s - θ / Q ≤ t → q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2)
    (hOld : ∀ j : Fin H.eventCount, j.succ ≤ last →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ j : Fin H.eventCount, j.succ ≤ last →
      ∀ b : (H.event j).RetainedBoundaryIndex, (H.event j).PresentedStaticCap fixed D m ε b)
    (hcap : ∀ j : Fin H.eventCount, ∀ hl : j.succ ≤ last,
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        (S j hl b).neck.scale / 2 ≤
          metricScalarAt (S j hl b).witness.metric ((S j hl b).witness.cap z)) :
    ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ last),
      H.time first ≤ s - θ / Q ∧
      (Nonempty (BackwardPointTrace H first last hle x.val) ∨
      ∃ (j : Fin H.eventCount) (_ : first ≤ j.castSucc) (hl : j.succ ≤ last)
        (A : BackwardPointTrace H j.succ last hl x.val)
        (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) =
            Sum.inl (A.point j.succ le_rfl hl) ∧
        A.point j.succ le_rfl hl = (S j hl b).inclusion ((S j hl b).witness.cap z) ∧
        metricScalarAt (H.event j).outputMetric (A.point j.succ le_rfl hl) < 2 * Q ∧
        (S j hl b).neck.scale < 4 * Q ∧
        0 < (S j hl b).neck.scale * (s - H.time j.succ) ∧
        (S j hl b).neck.scale * (s - H.time j.succ) < 4 * θ ∧
        (S j hl b).neck.scale * (s - H.time j.succ) < 1 ∧
        s - θ / Q < H.time j.succ) := by
  obtain ⟨first, hle, hfirst, hcross⟩ := H.exists_stage_time_le_and_lt_succ last hroom
  refine ⟨first, hle, hfirst, ?_⟩
  rcases H.exists_backwardPointTrace_or_recent_presented_cap_on_time_window first last hle G L hinit x
    hq hqQ hθsmall hbudget hcross hscalar
    (fun j _ hl => hderiv j hl) hfinal
    (fun j _ hl => hOld j hl) (fun j _ hl => S j hl)
    (fun j _ hl => hcap j hl) with htrace | ⟨j, hf, hl, A, b, z, hrest⟩
  · exact Or.inl htrace
  · exact Or.inr ⟨j, hf, hl, A, b, z, hrest.1, hrest.2.1, hrest.2.2.1,
      hrest.2.2.2.1, hrest.2.2.2.2.1, hrest.2.2.2.2.2.1, hrest.2.2.2.2.2.2,
      hcross j hf hl⟩

theorem exists_fixed_window_trace_subsequence_or_presented_cap_sequence_with_vanishing_age
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric)
    (hinit : ∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
    (x : ∀ i, (G i).terminalRegularOpen)
    (q Q : ℕ → ℝ) (C : ℝ≥0) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hq : ∀ i, 0 < q i) (hqQ : ∀ i, q i ≤ Q i)
    (hθsmall : θ₀ ≤ 1 / 4) (hbudget : 6 * C * θ₀ ≤ 1)
    (hroom : ∀ i, 0 ≤ s i - θ₀ / Q i)
    (hscalar : ∀ i, metricScalarAt (L i).metric (x i) ≤ (3 / 2 : ℝ) * Q i)
    (hderiv : ∀ i j, j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      s i - θ₀ / Q i ≤ t → q i < ((H i).event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
      s i - θ₀ / Q i ≤ t → q i < (G i).flow.scalar t (x i).val →
      |derivWithin (fun v => (G i).flow.scalar v (x i).val) (Iic t) t| ≤
        C * (G i).flow.scalar t (x i).val ^ 2)
    (parameters : ℕ → CutoffParameters)
    (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i))
    (haccuracy : Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0))
    (hcap : ∀ i j, j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric
            (((records i j).static b).witness.cap z)) :
    (∃ (θ : ℝ), 0 < θ ∧ θ ≤ θ₀ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (first : ∀ i, Fin ((H (φ i)).eventCount + 1)) (hle : ∀ i, first i ≤ last (φ i)),
        (∀ i, (H (φ i)).time (first i) ≤ s (φ i) - θ / Q (φ i)) ∧
        ∀ i, Nonempty (BackwardPointTrace (H (φ i)) (first i) (last (φ i))
          (hle i) (x (φ i)).val)) ∨
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧
        ∃ (event : ∀ i, Fin (H (φ i)).eventCount)
          (hlast : ∀ i, (event i).succ ≤ last (φ i))
          (A : ∀ i, BackwardPointTrace (H (φ i)) (event i).succ (last (φ i))
            (hlast i) (x (φ i)).val)
          (boundary : ∀ i, ((H (φ i)).event (event i)).RetainedBoundaryIndex)
          (z : ℕ → ThreeBall),
          (∀ i, ((H (φ i)).event (event i)).transition.trace.presentation
            (((H (φ i)).event (event i)).transition.trace.capping.cap (boundary i).val (z i)) =
              Sum.inl ((A i).point (event i).succ le_rfl (hlast i))) ∧
          (∀ i, (A i).point (event i).succ le_rfl (hlast i) =
            ((records (φ i) (event i)).static (boundary i)).inclusion
              (((records (φ i) (event i)).static (boundary i)).witness.cap (z i))) ∧
          (∀ i, metricScalarAt ((H (φ i)).event (event i)).outputMetric
            ((A i).point (event i).succ le_rfl (hlast i)) < 2 * Q (φ i)) ∧
          (∀ i, ((records (φ i) (event i)).static (boundary i)).neck.scale < 4 * Q (φ i)) ∧
          (∀ i, 0 < ((records (φ i) (event i)).static (boundary i)).neck.scale *
            (s (φ i) - (H (φ i)).time (event i).succ)) ∧
          (∀ i, ((records (φ i) (event i)).static (boundary i)).neck.scale *
            (s (φ i) - (H (φ i)).time (event i).succ) < 4 * θ₀ / ((i : ℝ) + 1)) ∧
          (∀ i, Q (φ i) * (s (φ i) - (H (φ i)).time (event i).succ) < θ₀ / ((i : ℝ) + 1)) ∧
          Tendsto (fun i => ((records (φ i) (event i)).static (boundary i)).neck.scale *
            (s (φ i) - (H (φ i)).time (event i).succ)) atTop (𝓝 0) ∧
          Tendsto (fun i => (parameters (φ i)).modelAccuracy) atTop (𝓝 0) := by
  classical
  let θ (n : ℕ) : ℝ := θ₀ / ((n : ℝ) + 1)
  have hθpos (n : ℕ) : 0 < θ n := div_pos hθ₀ (by positivity)
  have hθle (n : ℕ) : θ n ≤ θ₀ := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hθlim : Tendsto θ atTop (𝓝 0) := by
    simpa only [θ, mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul θ₀
  have hpoint (n i : ℕ) := (H i).exists_backwardPointTrace_or_recent_presented_cap_of_nonnegative_window
    (last i) (G i) (L i) (hinit i) (x i) (hq i) (hqQ i) ((hθle n).trans hθsmall)
    ((mul_le_mul_of_nonneg_left (hθle n) (by positivity : 0 ≤ 6 * (C : ℝ))).trans hbudget)
    ((hroom i).trans (sub_le_sub_left (div_le_div_of_nonneg_right (hθle n)
      (hq i |>.trans_le (hqQ i) |>.le)) (s i)))
    (hscalar i)
    (fun j hj y t ht hwindow => hderiv i j hj y t ht
      ((sub_le_sub_left (div_le_div_of_nonneg_right (hθle n)
        ((hq i).trans_le (hqQ i)).le) (s i)).trans hwindow))
    (fun t ht hwindow => hfinal i t ht
      ((sub_le_sub_left (div_le_div_of_nonneg_right (hθle n)
        ((hq i).trans_le (hqQ i)).le) (s i)).trans hwindow))
    (fun j _ => (records i j).old_eq_retained) (fun j _ => (records i j).static)
    (fun j hj => hcap i j hj)
  choose first hle htime halternative using hpoint
  by_cases htrace : ∃ n : ℕ, ∃ᶠ i in atTop,
      Nonempty (BackwardPointTrace (H i) (first n i) (last i) (hle n i) (x i).val)
  · obtain ⟨n, hn⟩ := htrace
    obtain ⟨φ, hφ, hφtrace⟩ := extraction_of_frequently_atTop hn
    exact Or.inl ⟨θ n, hθpos n, hθle n, φ, hφ, fun i => first n (φ i),
      fun i => hle n (φ i), fun i => htime n (φ i), hφtrace⟩
  · right
    have hnot (n : ℕ) : ∀ᶠ i in atTop,
        ¬ Nonempty (BackwardPointTrace (H i) (first n i) (last i) (hle n i) (x i).val) :=
      not_frequently.mp (fun hn => htrace ⟨n, hn⟩)
    obtain ⟨φ, hφ, hφnot⟩ := extraction_forall_of_eventually hnot
    have hcap' (i : ℕ) := (halternative i (φ i)).resolve_left (hφnot i)
    choose event hfirst hlast A boundary z hpres hbirth hscalar' hscale hpos hage hone hbirthTime using hcap'
    refine ⟨φ, hφ, event, hlast, A, boundary, z,
      hpres, hbirth, hscalar', hscale, hpos, ?_, ?_, ?_, ?_⟩
    · intro i
      simpa only [θ, mul_div_assoc] using hage i
    · intro i
      have hQ := (hq (φ i)).trans_le (hqQ (φ i))
      have ht : s (φ i) - (H (φ i)).time (event i).succ < θ i / Q (φ i) := by
        linarith [hbirthTime i]
      simpa only [mul_comm] using (lt_div_iff₀ hQ).mp ht
    · have hupper : Tendsto (fun i => 4 * θ i) atTop (𝓝 0) := by
        simpa only [mul_zero] using hθlim.const_mul 4
      exact squeeze_zero (fun i => (hpos i).le) (fun i => (hage i).le) hupper
    · exact haccuracy.comp hφ.tendsto_atTop

theorem exists_trace_subsequence_or_presented_cap_sequence_of_scalar_tendsto_atTop
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric)
    (hinit : ∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
    (x : ∀ i, (G i).terminalRegularOpen)
    {a q : ℝ} (ha : 0 < a) (hq : 0 < q) (C : ℝ≥0)
    (htime : ∀ i, a ≤ s i)
    (hhigh : Tendsto (fun i => metricScalarAt (L i).metric (x i)) atTop atTop)
    (hderiv : ∀ i j, j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q < ((H i).event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
      q < (G i).flow.scalar t (x i).val →
      |derivWithin (fun v => (G i).flow.scalar v (x i).val) (Iic t) t| ≤
        C * (G i).flow.scalar t (x i).val ^ 2)
    (parameters : ℕ → CutoffParameters)
    (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i))
    (haccuracy : Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0))
    (hcap : ∀ i j, j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric
            (((records i j).static b).witness.cap z)) :
    (∃ (θ : ℝ), 0 < θ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (first : ∀ i, Fin ((H (φ i)).eventCount + 1)) (hle : ∀ i, first i ≤ last (φ i)),
        (∀ i, (H (φ i)).time (first i) ≤ s (φ i) - θ / metricScalarAt (L (φ i)).metric (x (φ i))) ∧
        ∀ i, Nonempty (BackwardPointTrace (H (φ i)) (first i) (last (φ i))
          (hle i) (x (φ i)).val)) ∨
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧
        ∃ (event : ∀ i, Fin (H (φ i)).eventCount)
          (hlast : ∀ i, (event i).succ ≤ last (φ i))
          (A : ∀ i, BackwardPointTrace (H (φ i)) (event i).succ (last (φ i))
            (hlast i) (x (φ i)).val)
          (boundary : ∀ i, ((H (φ i)).event (event i)).RetainedBoundaryIndex)
          (z : ℕ → ThreeBall),
          (∀ i, ((H (φ i)).event (event i)).transition.trace.presentation
            (((H (φ i)).event (event i)).transition.trace.capping.cap (boundary i).val (z i)) =
              Sum.inl ((A i).point (event i).succ le_rfl (hlast i))) ∧
          (∀ i, (A i).point (event i).succ le_rfl (hlast i) =
            ((records (φ i) (event i)).static (boundary i)).inclusion
              (((records (φ i) (event i)).static (boundary i)).witness.cap (z i))) ∧
          (∀ i, metricScalarAt ((H (φ i)).event (event i)).outputMetric
            ((A i).point (event i).succ le_rfl (hlast i)) < 2 * metricScalarAt (L (φ i)).metric (x (φ i))) ∧
          (∀ i, ((records (φ i) (event i)).static (boundary i)).neck.scale < 4 * metricScalarAt (L (φ i)).metric (x (φ i))) ∧
          (∀ i, 0 < ((records (φ i) (event i)).static (boundary i)).neck.scale *
            (s (φ i) - (H (φ i)).time (event i).succ)) ∧
          Tendsto (fun i => metricScalarAt (L (φ i)).metric (x (φ i)) *
            (s (φ i) - (H (φ i)).time (event i).succ)) atTop (𝓝 0) ∧
          Tendsto (fun i => ((records (φ i) (event i)).static (boundary i)).neck.scale *
            (s (φ i) - (H (φ i)).time (event i).succ)) atTop (𝓝 0) ∧
          Tendsto (fun i => (parameters (φ i)).modelAccuracy) atTop (𝓝 0) := by
  let θ₀ : ℝ := min (1 / 4) (6 * (C : ℝ) + 1)⁻¹
  have hθ₀ : 0 < θ₀ := lt_min (by norm_num) (by positivity)
  have hθsmall : θ₀ ≤ 1 / 4 := min_le_left _ _
  have hbudget : 6 * (C : ℝ) * θ₀ ≤ 1 := by
    have hb : θ₀ ≤ 1 / (6 * (C : ℝ) + 1) := by
      simpa only [θ₀, one_div] using (min_le_right (1 / 4 : ℝ) (6 * (C : ℝ) + 1)⁻¹)
    have hh := (le_div_iff₀ (by positivity : 0 < 6 * (C : ℝ) + 1)).mp hb
    nlinarith [hθ₀.le]
  let Q (i : ℕ) := metricScalarAt (L i).metric (x i)
  obtain ⟨ψ, hψ, hψhigh⟩ := extraction_of_eventually_atTop
    (hhigh.eventually_ge_atTop (max q (θ₀ / a)))
  have hqQ (i : ℕ) : q ≤ Q (ψ i) := (le_max_left _ _).trans (hψhigh i)
  have hQpos (i : ℕ) : 0 < Q (ψ i) := hq.trans_le (hqQ i)
  have hroom (i : ℕ) : 0 ≤ s (ψ i) - θ₀ / Q (ψ i) := by
    have hb : θ₀ / a ≤ Q (ψ i) := (le_max_right _ _).trans (hψhigh i)
    have ht : θ₀ ≤ a * Q (ψ i) := by
      have hh := (div_le_iff₀ ha).mp hb
      nlinarith
    exact sub_nonneg.mpr (((div_le_iff₀ (hQpos i)).mpr ht).trans (htime (ψ i)))
  have hscalar (i : ℕ) : metricScalarAt (L (ψ i)).metric (x (ψ i)) ≤ (3 / 2 : ℝ) * Q (ψ i) := by
    change Q (ψ i) ≤ (3 / 2 : ℝ) * Q (ψ i)
    nlinarith [hQpos i]
  have halternative := exists_fixed_window_trace_subsequence_or_presented_cap_sequence_with_vanishing_age
    (fun i => H (ψ i)) (fun i => last (ψ i)) (fun i => s (ψ i))
    (fun i => G (ψ i)) (fun i => L (ψ i)) (fun i => hinit (ψ i)) (fun i => x (ψ i))
    (fun _ => q) (fun i => Q (ψ i)) C hθ₀ (fun _ => hq) hqQ hθsmall hbudget hroom hscalar
    (fun i j hj y t ht _ => hderiv (ψ i) j hj y t ht)
    (fun i t ht _ => hfinal (ψ i) t ht)
    (fun i => parameters (ψ i)) (fun i j => records (ψ i) j)
    (haccuracy.comp hψ.tendsto_atTop) (fun i j hj => hcap (ψ i) j hj)
  rcases halternative with ⟨θ, hθ, _, φ, hφ, first, hle, hfirst, htrace⟩ |
      ⟨φ, hφ, event, hlast, A, boundary, z, hpres, hbirth, hscalar', hscale, hagepos,
        hagebound, htimebound, hagelim, haccuracylim⟩
  · exact Or.inl ⟨θ, hθ, ψ ∘ φ, hψ.comp hφ, first, hle, hfirst, htrace⟩
  · refine Or.inr ⟨ψ ∘ φ, hψ.comp hφ, event, hlast, A, boundary, z,
      hpres, hbirth, hscalar', hscale, hagepos, ?_, hagelim, haccuracylim⟩
    have hupper : Tendsto (fun i : ℕ => θ₀ / ((i : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [mul_one_div, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul θ₀
    apply squeeze_zero _ (fun i => (htimebound i).le) hupper
    intro i
    exact mul_nonneg (hQpos (φ i)).le
      (sub_nonneg.mpr (((H (ψ (φ i))).time_strictMono.monotone (hlast i)).trans (G (ψ (φ i))).lt.le))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
end
end

section
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private theorem exists_canonical_cap_scalar_first_failure_exclusion
    (N : ℕ) (hN : 2 ≤ N) (D r eps : ℝ)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ : ℝ, ∃ C : ℝ≥0, 0 < C₀ ∧ 0 < C ∧ ∃ (η ε₀ δ₀ : ℝ), 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      (∀ i, (parameters i).modelAccuracy ≤ ε₀) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ (q₀ a₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
      (∀ i, q₀ i ≤ C₀ * q i) → (∀ i, 1 ≤ a₀ i * q i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) (a₀ i) x) →
      (∀ i x, -3 / a₀ i ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ i < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ i < (A i).flow.scalar t x →
        |derivWithin (fun v => (A i).flow.scalar v x) (Iic t) t| ≤ C * (A i).flow.scalar t x ^ 2) →
      (∀ i, age i ≤ η) → Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, ((H i).stage (last i)).Carrier)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i)),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      (∀ i, 0 < (A i).flow.scalar (time i) (x i)) →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i), v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i) * Real.sqrt ((A i).flow.scalar (time i) (x i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i) v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i) v)|) ∨
        C * (A i).flow.scalar (time i) (x i) ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i)) (Iic (time i)) (time i)|) → False := by
  obtain ⟨C₀,Cphys,hC₀,hCphys,hbound⟩ :=
    exists_uniform_scalar_derivative_bounds_at_canonical_cap_points_of_vanishing_age
      N hN D r eps heps hepssmall hr hfit
  let C : ℝ≥0 := ⟨Cphys + 1, by positivity⟩
  have hC : 0 < C := by change 0 < Cphys + 1; positivity
  obtain ⟨η,ε₀,δ₀,hη,hε₀,hεhalf,hδ₀,hmain⟩ := hbound C
  refine ⟨C₀,C,hC₀,hC,η,ε₀,δ₀,hη,hε₀,hεhalf,hδ₀,?_⟩
  intro H event last hle time A hinit parameters records boundary cap q age
    hcanonical hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z x trace hbirth hpositive hfail
  have hevent := hmain H event last hle time A hinit parameters records boundary hcanonical
    hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z x trace hbirth
  obtain ⟨i,hi⟩ := hevent.exists
  have hc : Cphys < (C : ℝ) := by change Cphys < Cphys + 1; linarith
  rcases hfail i with ⟨v,hvzero,hv⟩ | ht
  · have hpos : 0 < (A i).flow.scalar (time i) (x i) *
        Real.sqrt ((A i).flow.scalar (time i) (x i)) *
          Real.sqrt (((A i).flow.base.metric (time i)).inner (x i) v v) := by
      exact mul_pos (mul_pos (hpositive i) (Real.sqrt_pos.mpr (hpositive i)))
        (Real.sqrt_pos.mpr (((A i).flow.base.metric (time i)).pos (x i) v hvzero))
    have hlt := mul_lt_mul_of_pos_right hc hpos
    have hh := hi.1 v
    nlinarith
  · have hlt := mul_lt_mul_of_pos_right hc (sq_pos_of_pos (hpositive i))
    exact (not_lt_of_ge ht) (hi.2.trans_lt hlt)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private theorem cap_scale_tendsto_atTop_of_terminal_scalar_tendsto
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ) (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric)
    (hinit : ∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
    (x : ∀ i, (G i).terminalRegularOpen) (Q : ℕ → ℝ)
    (hQ : ∀ i, Q i = metricScalarAt (L i).metric (x i)) (hQlim : Tendsto Q atTop atTop)
    {q₀ Cbirth θ : ℝ} {C : ℝ≥0} (hq₀ : 0 < q₀) (hCbirth : 0 < Cbirth)
    (hbudget : C * θ ≤ 1)
    (parameters : ℕ → CutoffParameters)
    (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i))
    (event : ∀ i, Fin (H i).eventCount) (hl : ∀ i, (event i).succ ≤ last i)
    (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex) (z : ℕ → ThreeBall)
    (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hl i) (x i).val)
    (hbirth : ∀ i, (trace i).point (event i).succ le_rfl (hl i) =
      ((records i (event i)).static (boundary i)).inclusion
        (((records i (event i)).static (boundary i)).witness.cap (z i)))
    (hupper : ∀ᶠ i in atTop, metricScalarAt ((records i (event i)).static (boundary i)).witness.metric
      (((records i (event i)).static (boundary i)).witness.cap (z i)) ≤
        Cbirth * ((records i (event i)).static (boundary i)).neck.scale)
    (htime : ∀ᶠ i in atTop, Q i * (s i - (H i).time (event i).succ) ≤ θ)
    (hderiv : ∀ i j, (event i).succ ≤ j.castSucc → j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q₀ < ((H i).event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
          C * ((H i).event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i, ∀ t ∈ Ioo ((H i).time (last i)) (s i),
      q₀ < (G i).flow.scalar t (x i).val →
        |derivWithin (fun v => (G i).flow.scalar v (x i).val) (Iic t) t| ≤
          C * (G i).flow.scalar t (x i).val ^ 2) :
    Tendsto (fun i => ((records i (event i)).static (boundary i)).neck.scale) atTop atTop := by
  have hlow : ∀ᶠ i in atTop, Q i / (2 * Cbirth) ≤
      ((records i (event i)).static (boundary i)).neck.scale := by
    filter_upwards [hQlim.eventually_gt_atTop (2 * q₀),hupper,htime] with i hi hupperi htimei
    have hb : metricScalarAt ((H i).initialMetric (event i).succ)
        ((trace i).point (event i).succ le_rfl (hl i)) ≤
          Cbirth * ((records i (event i)).static (boundary i)).neck.scale := by
      rw [hbirth i, ← (H i).event_output (event i),
        ← (((records i (event i)).static (boundary i)).scalar_eq ((H i).event (event i)))]
      exact hupperi
    have ht : C * (s i - (H i).time (event i).succ) * metricScalarAt (L i).metric (x i) ≤ 1 := by
      rw [← hQ i]
      have hh := mul_le_mul_of_nonneg_left htimei C.coe_nonneg
      nlinarith
    have hh := (trace i).terminal_scalar_div_le_birth_scale_of_time_sub_le
      (G i) (L i) (hinit i) (x i) hq₀
      (fun j hj hlast t ht => hderiv i j hj hlast _ t ht) (hfinal i)
      hCbirth hb (by rwa [← hQ i]) ht
    simpa only [← hQ i] using hh.1
  apply tendsto_atTop_mono' atTop hlow
  exact hQlim.atTop_div_const (by positivity : 0 < 2 * Cbirth)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


private theorem exists_canonical_cap_scalar_contact_exclusion_of_high_curvature
    (N : ℕ) (hN : 2 ≤ N) (D r eps : ℝ)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C : ℝ≥0, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ q₀ a₀ : ℝ, 0 < q₀ → 0 < a₀ →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ < (A i).flow.scalar t x →
        |derivWithin (fun v => (A i).flow.scalar v x) (Iic t) t| ≤ C * (A i).flow.scalar t x ^ 2) →
      Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, ((H i).stage (last i)).Carrier)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i)),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      Tendsto (fun i => (A i).flow.scalar (time i) (x i)) atTop atTop →
      Tendsto (fun i => (A i).flow.scalar (time i) (x i) *
        (time i - (H i).time (event i).succ)) atTop (𝓝 0) →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i), v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i) * Real.sqrt ((A i).flow.scalar (time i) (x i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i) v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i) v)|) ∨
        C * (A i).flow.scalar (time i) (x i) ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i)) (Iic (time i)) (time i)|) → False := by
  obtain ⟨C₀,C,hC₀,hC,η,ε₀,δ₀,hη,hε₀,hεhalf,hδ₀,hmain⟩ :=
    exists_canonical_cap_scalar_first_failure_exclusion N hN D r eps heps hepssmall hr hfit
  obtain ⟨Cbirth,hCbirth,hupperBirth⟩ := exists_uniform_presented_cap_scalar_abs_bound_of_canonical_window.{u}
  refine ⟨C,hC,δ₀,hδ₀,?_⟩
  intro H event last hle time A hinit parameters records boundary cap q age
    hcanonical hmargin hm herrorlim q₀ a₀ hq₀ ha₀ hfixed hlower hδ hderiv hfinal
    hagelim z x trace hbirth hhigh hnormalizedtime hfail
  let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (last i))
  let x' : ∀ i, (G i).terminalRegularOpen := fun i => ⟨x i,by
    change x i ∈ (G i).terminalRegularRegion
    rw [(A i).terminalRegularRegion_eq_univ ((H i).stage (last i))]
    trivial⟩
  let Q := fun i => (A i).flow.scalar (time i) (x i)
  have hQ (i : ℕ) : Q i = metricScalarAt (L i).metric (x' i) := by
    change metricScalarAt ((A i).flow.base.metric (time i)) (x i) =
      metricScalarAt (((A i).flow.base.metric (time i)).restrictOpen (G i).terminalRegularOpen) (x' i)
    rw [metricScalarAt_restrictOpen]
  have hcoreD : StandardCap.transitionEnd < D + 1 := by
    linarith [inv_pos.mpr heps,StandardCap.transitionEnd_pos]
  have hupper : ∀ᶠ i in atTop, metricScalarAt (cap i).witness.metric ((cap i).witness.cap (z i)) ≤
      Cbirth * (cap i).neck.scale := by
    filter_upwards [herrorlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with i hi
    exact (le_abs_self _).trans (hupperBirth ((H i).event (event i))
      (hcoreD.trans_le (hmargin i)) hi.le (by have := hm i; omega) (cap i) (hcanonical i) (z i))
  have htime : ∀ᶠ i in atTop, Q i * (time i - (H i).time (event i).succ) ≤ 1 / (C+1) :=
    (hnormalizedtime.eventually (Iio_mem_nhds (by positivity : (0:ℝ) < 1/(C+1)))).mono fun i hi => hi.le
  have hqcap : Tendsto q atTop atTop := cap_scale_tendsto_atTop_of_terminal_scalar_tendsto
    H last time G L hinit x' Q hQ hhigh hq₀ hCbirth
    (show (C:ℝ) * (1/(C+1)) ≤ 1 by rw [mul_one_div]; exact (div_le_one (by positivity)).mpr (by linarith))
    parameters records event hle boundary z trace hbirth hupper htime hderiv
    (fun i t ht hh => hfinal i (x i) t ht hh)
  have hevent : ∀ᶠ i in atTop,
      (parameters i).modelAccuracy ≤ ε₀ ∧ q₀ ≤ C₀ * q i ∧ 1 ≤ a₀ * q i ∧
        age i ≤ η ∧ 0 < Q i := by
    filter_upwards [herrorlim.eventually (Iio_mem_nhds hε₀),
      hqcap.eventually_ge_atTop (q₀ / C₀),hqcap.eventually_ge_atTop (1 / a₀),
      hagelim.eventually (Iio_mem_nhds hη),hhigh.eventually_gt_atTop 0] with i hε hq hqa hage hpos
    refine ⟨hε.le,?_,?_,hage.le,hpos⟩
    · have hh := (div_le_iff₀ hC₀).mp hq
      nlinarith
    · have hh := (div_le_iff₀ ha₀).mp hqa
      nlinarith
  obtain ⟨M,hM⟩ := eventually_atTop.mp hevent
  let f := fun i : ℕ => i + M
  have hf : Tendsto f atTop atTop := tendsto_add_atTop_nat M
  have hgood (i : ℕ) := hM (f i) (by dsimp [f]; omega)
  exact hmain (fun i => H (f i)) (fun i => event (f i)) (fun i => last (f i))
    (fun i => hle (f i)) (fun i => time (f i)) (fun i => A (f i)) (fun i => hinit (f i))
    (fun i => parameters (f i)) (fun i => records (f i)) (fun i => boundary (f i))
    (fun i => hcanonical (f i)) (fun i => hmargin (f i)) (fun i => hm (f i))
    (fun i => (hgood i).1) (herrorlim.comp hf) (fun _ => q₀) (fun _ => a₀)
    (fun _ => hq₀) (fun i => (hgood i).2.1) (fun i => (hgood i).2.2.1)
    (fun i => hfixed (f i)) (fun i => hlower (f i)) (fun i => hδ (f i))
    (fun i => hderiv (f i)) (fun i => hfinal (f i)) (fun i => (hgood i).2.2.2.1)
    (hagelim.comp hf) (fun i => z (f i)) (fun i => x (f i)) (fun i => trace (f i))
    (fun i => hbirth (f i)) (fun i => (hgood i).2.2.2.2) (fun i => hfail (f i))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


theorem exists_fixed_backward_window_at_scalar_derivative_contact
    (N : ℕ) (hN : 2 ≤ N) (D r eps : ℝ)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C : ℝ≥0, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i)),
      (∀ i j, j.succ ≤ last i → ∀ b, ((records i j).static b).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      (∀ i j, j.succ ≤ last i → ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric (((records i j).static b).witness.cap z)) →
      ∀ q₀ a₀ a : ℝ, 0 < q₀ → 0 < a₀ → 0 < a →
      (∀ i, a ≤ time i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i j, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
      (∀ i j, j.succ ≤ last i → ∀ y : ((H i).stage j.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          q₀ < ((H i).event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).event j).incoming.flow.scalar t y ^ 2) →
      (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ < (A i).flow.scalar t y →
        |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤ C * (A i).flow.scalar t y ^ 2) →
      ∀ x : ∀ i, ((H i).stage (last i)).Carrier,
      Tendsto (fun i => (A i).flow.scalar (time i) (x i)) atTop atTop →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i), v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i) * Real.sqrt ((A i).flow.scalar (time i) (x i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i) v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i) v)|) ∨
        C * (A i).flow.scalar (time i) (x i) ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i)) (Iic (time i)) (time i)|) →
      ∃ θ : ℝ, 0 < θ ∧ ∃ f : ℕ → ℕ, StrictMono f ∧
        ∃ (first : ∀ i, Fin ((H (f i)).eventCount + 1)) (hle : ∀ i, first i ≤ last (f i)),
          (∀ i, (H (f i)).time (first i) ≤ time (f i) - θ / (A (f i)).flow.scalar (time (f i)) (x (f i))) ∧
          ∀ i, Nonempty (BackwardPointTrace (H (f i)) (first i) (last (f i)) (hle i) (x (f i))) := by
  obtain ⟨C,hC,δ₀,hδ₀,hexclude⟩ :=
    exists_canonical_cap_scalar_contact_exclusion_of_high_curvature N hN D r eps heps hepssmall hr hfit
  refine ⟨C,hC,δ₀,hδ₀,?_⟩
  intro H last time A hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hfail
  let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (last i))
  let x' : ∀ i, (G i).terminalRegularOpen := fun i => ⟨x i,by
    change x i ∈ (G i).terminalRegularRegion
    rw [(A i).terminalRegularRegion_eq_univ ((H i).stage (last i))]
    trivial⟩
  have hscalar (i : ℕ) : metricScalarAt (L i).metric (x' i) = (A i).flow.scalar (time i) (x i) := by
    change metricScalarAt (((A i).flow.base.metric (time i)).restrictOpen (G i).terminalRegularOpen) (x' i) = _
    rw [metricScalarAt_restrictOpen]
    rfl
  have hhigh' : Tendsto (fun i => metricScalarAt (L i).metric (x' i)) atTop atTop := by
    simpa only [hscalar] using hhigh
  have halt := exists_trace_subsequence_or_presented_cap_sequence_of_scalar_tendsto_atTop
    H last time G L hinit x' ha hq₀ C htime hhigh' hderiv
    (fun i t ht hh => hfinal i (x i) t ht hh) parameters records herrorlim hcap
  rcases halt with ⟨θ,hθ,f,hf,first,hle,hstart,htrace⟩ |
    ⟨f,hf,event,hlast,trace,boundary,z,hpresentation,hbirth,hscalarBirth,hscale,hagepos,htimelim,hagelim,herrorlim'⟩
  · exact ⟨θ,hθ,f,hf,first,hle,by simpa only [hscalar] using hstart,htrace⟩
  · exfalso
    have htimelim' : Tendsto (fun i => (A (f i)).flow.scalar (time (f i)) (x (f i)) *
        (time (f i) - (H (f i)).time (event i).succ)) atTop (𝓝 0) := by
      simpa only [hscalar] using htimelim
    exact hexclude (fun i => H (f i)) event (fun i => last (f i)) hlast
      (fun i => time (f i)) (fun i => A (f i)) (fun i => hinit (f i))
      (fun i => parameters (f i)) (fun i => records (f i)) boundary
      (fun i => hcanonical (f i) (event i) (hlast i) (boundary i))
      (fun i => hmargin (f i)) (fun i => hm (f i)) herrorlim'
      q₀ a₀ hq₀ ha₀ (fun i => hfixed (f i)) (fun i => hlower (f i))
      (fun i j _ hj => hδ (f i) j hj) (fun i j _ hj => hderiv (f i) j hj)
      (fun i => hfinal (f i)) hagelim z (fun i => x (f i)) trace hbirth
      (hhigh.comp hf.tendsto_atTop) htimelim' (fun i => hfail (f i))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


private theorem exists_scalar_derivative_contact_exclusion_near_high_curvature_caps
    (N : ℕ) (hN : 2 ≤ N) (D r eps : ℝ)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D)
    (Cscale d b : ℝ) (hCscale : 0 < Cscale) (hd : 0 ≤ d) (hb : 0 < b)
    (hcapture : 2 * StandardCap.transitionEnd + (d + b) * Real.sqrt Cscale < r / 2) :
    ∃ C : ℝ≥0, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ q₀ a₀ : ℝ, 0 < q₀ → 0 < a₀ →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ < (A i).flow.scalar t x →
        |derivWithin (fun v => (A i).flow.scalar v x) (Iic t) t| ≤ C * (A i).flow.scalar t x ^ 2) →
      Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, ((H i).stage (last i)).Carrier)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i)),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      Tendsto (fun i => (A i).flow.scalar (time i) (x i)) atTop atTop →
      Tendsto (fun i => (A i).flow.scalar (time i) (x i) *
        (time i - (H i).time (event i).succ)) atTop (𝓝 0) →
      ∀ (Qsel : ℕ → ℝ), (∀ i, 0 < Qsel i) → (∀ i, q i ≤ Cscale * Qsel i) →
      ∀ y : ∀ i, ((H i).stage (last i)).Carrier,
      (∀ i, riemannianEDistOf ((A i).flow.base.metric (time i)) (x i) (y i) ≤
        ENNReal.ofReal (d / Real.sqrt (Qsel i))) →
      (∀ i, (∃ v : TangentSpace ThreeModel (y i), v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (y i) * Real.sqrt ((A i).flow.scalar (time i) (y i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (y i) v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (y i) v)|) ∨
        C * (A i).flow.scalar (time i) (y i) ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (y i)) (Iic (time i)) (time i)|) → False := by
  obtain ⟨C₀,C,hC₀,hC,η,ε₀,δ₀,hη,hε₀,hεhalf,hδ₀,hmain⟩ :=
    exists_scalar_derivative_contact_exclusion_near_canonical_caps_of_vanishing_age
      N hN D r eps heps hepssmall hr hfit Cscale d b hCscale hd hb hcapture
  obtain ⟨Cbirth,hCbirth,hupperBirth⟩ := exists_uniform_presented_cap_scalar_abs_bound_of_canonical_window.{u}
  refine ⟨C,hC,δ₀,hδ₀,?_⟩
  intro H event last hle time A hinit parameters records boundary cap q age
    hcanonical hmargin hm herrorlim q₀ a₀ hq₀ ha₀ hfixed hlower hδ hderiv hfinal
    hagelim z x trace hbirth hhigh hnormalizedtime Qsel hQsel hscale y hnear hfail
  let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (last i))
  let x' : ∀ i, (G i).terminalRegularOpen := fun i => ⟨x i,by
    change x i ∈ (G i).terminalRegularRegion
    rw [(A i).terminalRegularRegion_eq_univ ((H i).stage (last i))]
    trivial⟩
  let Q := fun i => (A i).flow.scalar (time i) (x i)
  have hQ (i : ℕ) : Q i = metricScalarAt (L i).metric (x' i) := by
    change metricScalarAt ((A i).flow.base.metric (time i)) (x i) =
      metricScalarAt (((A i).flow.base.metric (time i)).restrictOpen (G i).terminalRegularOpen) (x' i)
    rw [metricScalarAt_restrictOpen]
  have hcoreD : StandardCap.transitionEnd < D + 1 := by
    linarith [inv_pos.mpr heps,StandardCap.transitionEnd_pos]
  have hupper : ∀ᶠ i in atTop, metricScalarAt (cap i).witness.metric ((cap i).witness.cap (z i)) ≤
      Cbirth * (cap i).neck.scale := by
    filter_upwards [herrorlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with i hi
    exact (le_abs_self _).trans (hupperBirth ((H i).event (event i))
      (hcoreD.trans_le (hmargin i)) hi.le (by have := hm i; omega) (cap i) (hcanonical i) (z i))
  have htime : ∀ᶠ i in atTop, Q i * (time i - (H i).time (event i).succ) ≤ 1 / (C+1) :=
    (hnormalizedtime.eventually (Iio_mem_nhds (by positivity : (0:ℝ) < 1/(C+1)))).mono fun i hi => hi.le
  have hqcap : Tendsto q atTop atTop := cap_scale_tendsto_atTop_of_terminal_scalar_tendsto
    H last time G L hinit x' Q hQ hhigh hq₀ hCbirth
    (show (C:ℝ) * (1/(C+1)) ≤ 1 by rw [mul_one_div]; exact (div_le_one (by positivity)).mpr (by linarith))
    parameters records event hle boundary z trace hbirth hupper htime hderiv
    (fun i t ht hh => hfinal i (x i) t ht hh)
  have hevent : ∀ᶠ i in atTop,
      (parameters i).modelAccuracy ≤ ε₀ ∧ q₀ ≤ C₀ * q i ∧ 1 ≤ a₀ * q i ∧
        age i ≤ η := by
    filter_upwards [herrorlim.eventually (Iio_mem_nhds hε₀),
      hqcap.eventually_ge_atTop (q₀ / C₀),hqcap.eventually_ge_atTop (1 / a₀),
      hagelim.eventually (Iio_mem_nhds hη)] with i hε hq hqa hage
    refine ⟨hε.le,?_,?_,hage.le⟩
    · have hh := (div_le_iff₀ hC₀).mp hq
      nlinarith
    · have hh := (div_le_iff₀ ha₀).mp hqa
      nlinarith
  obtain ⟨M,hM⟩ := eventually_atTop.mp hevent
  let f := fun i : ℕ => i + M
  have hf : Tendsto f atTop atTop := tendsto_add_atTop_nat M
  have hgood (i : ℕ) := hM (f i) (by dsimp [f]; omega)
  exact hmain (fun i => H (f i)) (fun i => event (f i)) (fun i => last (f i))
    (fun i => hle (f i)) (fun i => time (f i)) (fun i => A (f i)) (fun i => hinit (f i))
    (fun i => parameters (f i)) (fun i => records (f i)) (fun i => boundary (f i))
    (fun i => hcanonical (f i)) (fun i => hmargin (f i)) (fun i => hm (f i))
    (fun i => (hgood i).1) (herrorlim.comp hf) (fun _ => q₀) (fun _ => a₀)
    (fun _ => hq₀) (fun i => (hgood i).2.1) (fun i => (hgood i).2.2.1)
    (fun i => hfixed (f i)) (fun i => hlower (f i)) (fun i => hδ (f i))
    (fun i => hderiv (f i)) (fun i => hfinal (f i)) (fun i => (hgood i).2.2.2)
    (hagelim.comp hf) (fun i => z (f i)) (fun i => x (f i)) (fun i => trace (f i))
    (fun i => hbirth (f i)) (fun i => Qsel (f i)) (fun i => hQsel (f i))
    (fun i => hscale (f i)) (fun i => y (f i)) (fun i => hnear (f i)) (fun i => hfail (f i))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem exists_backward_traces_on_set_or_recent_presented_cap_of_nonnegative_window
    (H : ObservedHistory.{u}) (last : Fin (H.eventCount + 1))
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (K : Set G.terminalRegularOpen)
    {q Q θ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hθsmall : θ ≤ 1 / 4) (hbudget : 6 * C * θ ≤ 1)
    (hroom : 0 ≤ s - θ / Q)
    (hscalar : ∀ x ∈ K, metricScalarAt L.metric x ≤ (3 / 2 : ℝ) * Q)
    (hderiv : ∀ j : Fin H.eventCount, j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      s - θ / Q ≤ t → q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ x ∈ K, ∀ t ∈ Ioo (H.time last) s, s - θ / Q ≤ t → q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2)
    (hOld : ∀ j : Fin H.eventCount, j.succ ≤ last →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ j : Fin H.eventCount, j.succ ≤ last →
      ∀ b : (H.event j).RetainedBoundaryIndex, (H.event j).PresentedStaticCap fixed D m ε b)
    (hcap : ∀ j : Fin H.eventCount, ∀ hl : j.succ ≤ last,
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        (S j hl b).neck.scale / 2 ≤
          metricScalarAt (S j hl b).witness.metric ((S j hl b).witness.cap z)) :
    ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ last),
      H.time first ≤ s - θ / Q ∧
      ((∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val)) ∨
      ∃ x : G.terminalRegularOpen, x ∈ K ∧ ∃ (j : Fin H.eventCount) (_ : first ≤ j.castSucc) (hl : j.succ ≤ last)
        (A : BackwardPointTrace H j.succ last hl x.val)
        (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) =
            Sum.inl (A.point j.succ le_rfl hl) ∧
        A.point j.succ le_rfl hl = (S j hl b).inclusion ((S j hl b).witness.cap z) ∧
        metricScalarAt (H.event j).outputMetric (A.point j.succ le_rfl hl) < 2 * Q ∧
        (S j hl b).neck.scale < 4 * Q ∧
        0 < (S j hl b).neck.scale * (s - H.time j.succ) ∧
        (S j hl b).neck.scale * (s - H.time j.succ) < 4 * θ ∧
        (S j hl b).neck.scale * (s - H.time j.succ) < 1 ∧
        s - θ / Q < H.time j.succ) := by
  classical
  obtain ⟨first, hle, hfirst, hcross⟩ := exists_stage_time_le_and_lt_succ H last hroom
  refine ⟨first, hle, hfirst, ?_⟩
  by_cases hall : ∀ x ∈ K, Nonempty (BackwardPointTrace H first last hle x.val)
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨x, hx, hnot⟩ := hall
    have hn : ¬ Nonempty (BackwardPointTrace H first last hle x.val) :=
      not_nonempty_iff.mpr hnot
    rcases H.exists_backwardPointTrace_or_recent_presented_cap_on_time_window first last hle G L hinit x
      hq hqQ hθsmall hbudget hcross (hscalar x hx)
      (fun j _ hl => hderiv j hl) (hfinal x hx)
      (fun j _ hl => hOld j hl) (fun j _ hl => S j hl)
      (fun j _ hl => hcap j hl) with htrace | ⟨j, hf, hl, A, b, z, hrest⟩
    · exact (hn htrace).elim
    · exact Or.inr ⟨x, hx, j, hf, hl, A, b, z, hrest.1, hrest.2.1, hrest.2.2.1,
        hrest.2.2.2.1, hrest.2.2.2.2.1, hrest.2.2.2.2.2.1, hrest.2.2.2.2.2.2,
        hcross j hf hl⟩

theorem exists_fixed_window_traces_on_sets_subsequence_or_presented_cap_sequence_with_vanishing_age
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric)
    (hinit : ∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
    (K : ∀ i, Set (G i).terminalRegularOpen)
    (q Q : ℕ → ℝ) (C : ℝ≥0) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hq : ∀ i, 0 < q i) (hqQ : ∀ i, q i ≤ Q i)
    (hθsmall : θ₀ ≤ 1 / 4) (hbudget : 6 * C * θ₀ ≤ 1)
    (hroom : ∀ i, 0 ≤ s i - θ₀ / Q i)
    (hscalar : ∀ i x, x ∈ K i → metricScalarAt (L i).metric x ≤ (3 / 2 : ℝ) * Q i)
    (hderiv : ∀ i j, j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      s i - θ₀ / Q i ≤ t → q i < ((H i).event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i x, x ∈ K i → ∀ t ∈ Ioo ((H i).time (last i)) (s i),
      s i - θ₀ / Q i ≤ t → q i < (G i).flow.scalar t x.val →
      |derivWithin (fun v => (G i).flow.scalar v x.val) (Iic t) t| ≤
        C * (G i).flow.scalar t x.val ^ 2)
    (parameters : ℕ → CutoffParameters)
    (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i))
    (haccuracy : Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0))
    (hcap : ∀ i j, j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric
            (((records i j).static b).witness.cap z)) :
    (∃ (θ : ℝ), 0 < θ ∧ θ ≤ θ₀ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (first : ∀ i, Fin ((H (φ i)).eventCount + 1)) (hle : ∀ i, first i ≤ last (φ i)),
        (∀ i, (H (φ i)).time (first i) ≤ s (φ i) - θ / Q (φ i)) ∧
        ∀ i x, x ∈ K (φ i) → Nonempty (BackwardPointTrace (H (φ i)) (first i) (last (φ i))
          (hle i) x.val)) ∨
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧
        ∃ (x : ∀ i, (G (φ i)).terminalRegularOpen), (∀ i, x i ∈ K (φ i)) ∧
        ∃ (event : ∀ i, Fin (H (φ i)).eventCount)
          (hlast : ∀ i, (event i).succ ≤ last (φ i))
          (A : ∀ i, BackwardPointTrace (H (φ i)) (event i).succ (last (φ i))
            (hlast i) (x i).val)
          (boundary : ∀ i, ((H (φ i)).event (event i)).RetainedBoundaryIndex)
          (z : ℕ → ThreeBall),
          (∀ i, ((H (φ i)).event (event i)).transition.trace.presentation
            (((H (φ i)).event (event i)).transition.trace.capping.cap (boundary i).val (z i)) =
              Sum.inl ((A i).point (event i).succ le_rfl (hlast i))) ∧
          (∀ i, (A i).point (event i).succ le_rfl (hlast i) =
            ((records (φ i) (event i)).static (boundary i)).inclusion
              (((records (φ i) (event i)).static (boundary i)).witness.cap (z i))) ∧
          (∀ i, metricScalarAt ((H (φ i)).event (event i)).outputMetric
            ((A i).point (event i).succ le_rfl (hlast i)) < 2 * Q (φ i)) ∧
          (∀ i, ((records (φ i) (event i)).static (boundary i)).neck.scale < 4 * Q (φ i)) ∧
          (∀ i, 0 < ((records (φ i) (event i)).static (boundary i)).neck.scale *
            (s (φ i) - (H (φ i)).time (event i).succ)) ∧
          (∀ i, ((records (φ i) (event i)).static (boundary i)).neck.scale *
            (s (φ i) - (H (φ i)).time (event i).succ) < 4 * θ₀ / ((i : ℝ) + 1)) ∧
          (∀ i, Q (φ i) * (s (φ i) - (H (φ i)).time (event i).succ) < θ₀ / ((i : ℝ) + 1)) ∧
          Tendsto (fun i => Q (φ i) * (s (φ i) - (H (φ i)).time (event i).succ))
            atTop (𝓝 0) ∧
          Tendsto (fun i => ((records (φ i) (event i)).static (boundary i)).neck.scale *
            (s (φ i) - (H (φ i)).time (event i).succ)) atTop (𝓝 0) ∧
          Tendsto (fun i => (parameters (φ i)).modelAccuracy) atTop (𝓝 0) := by
  classical
  let θ (n : ℕ) : ℝ := θ₀ / ((n : ℝ) + 1)
  have hθpos (n : ℕ) : 0 < θ n := div_pos hθ₀ (by positivity)
  have hθle (n : ℕ) : θ n ≤ θ₀ := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hθlim : Tendsto θ atTop (𝓝 0) := by
    simpa only [θ, mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul θ₀
  have hpoint (n i : ℕ) := (H i).exists_backward_traces_on_set_or_recent_presented_cap_of_nonnegative_window
    (last i) (G i) (L i) (hinit i) (K i) (hq i) (hqQ i) ((hθle n).trans hθsmall)
    ((mul_le_mul_of_nonneg_left (hθle n) (by positivity : 0 ≤ 6 * (C : ℝ))).trans hbudget)
    ((hroom i).trans (sub_le_sub_left (div_le_div_of_nonneg_right (hθle n)
      (hq i |>.trans_le (hqQ i) |>.le)) (s i)))
    (hscalar i)
    (fun j hj y t ht hwindow => hderiv i j hj y t ht
      ((sub_le_sub_left (div_le_div_of_nonneg_right (hθle n)
        ((hq i).trans_le (hqQ i)).le) (s i)).trans hwindow))
    (fun x hx t ht hwindow => hfinal i x hx t ht
      ((sub_le_sub_left (div_le_div_of_nonneg_right (hθle n)
        ((hq i).trans_le (hqQ i)).le) (s i)).trans hwindow))
    (fun j _ => (records i j).old_eq_retained) (fun j _ => (records i j).static)
    (fun j hj => hcap i j hj)
  choose first hle htime halternative using hpoint
  by_cases htrace : ∃ n : ℕ, ∃ᶠ i in atTop,
      (∀ x ∈ K i, Nonempty (BackwardPointTrace (H i) (first n i) (last i) (hle n i) x.val))
  · obtain ⟨n, hn⟩ := htrace
    obtain ⟨φ, hφ, hφtrace⟩ := extraction_of_frequently_atTop hn
    exact Or.inl ⟨θ n, hθpos n, hθle n, φ, hφ, fun i => first n (φ i),
      fun i => hle n (φ i), fun i => htime n (φ i), hφtrace⟩
  · right
    have hnot (n : ℕ) : ∀ᶠ i in atTop,
        ¬ (∀ x ∈ K i, Nonempty (BackwardPointTrace (H i) (first n i) (last i) (hle n i) x.val)) :=
      not_frequently.mp (fun hn => htrace ⟨n, hn⟩)
    obtain ⟨φ, hφ, hφnot⟩ := extraction_forall_of_eventually hnot
    have hcap' (i : ℕ) := (halternative i (φ i)).resolve_left (hφnot i)
    choose x hx event hfirst hlast A boundary z hpres hbirth hscalar' hscale hpos hage hone hbirthTime using hcap'
    have htimebound (i : ℕ) : Q (φ i) * (s (φ i) - (H (φ i)).time (event i).succ) < θ i := by
      have hQ := (hq (φ i)).trans_le (hqQ (φ i))
      have ht : s (φ i) - (H (φ i)).time (event i).succ < θ i / Q (φ i) := by
        linarith [hbirthTime i]
      simpa only [mul_comm] using (lt_div_iff₀ hQ).mp ht
    refine ⟨φ, hφ, x, hx, event, hlast, A, boundary, z,
      hpres, hbirth, hscalar', hscale, hpos, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simpa only [θ, mul_div_assoc] using hage i
    · exact htimebound
    · apply squeeze_zero _ (fun i => (htimebound i).le) hθlim
      intro i
      exact mul_nonneg ((hq (φ i)).trans_le (hqQ (φ i))).le
        (sub_nonneg.mpr (((H (φ i)).time_strictMono.monotone (hlast i)).trans (G (φ i)).lt.le))
    · have hupper : Tendsto (fun i => 4 * θ i) atTop (𝓝 0) := by
        simpa only [mul_zero] using hθlim.const_mul 4
      exact squeeze_zero (fun i => (hpos i).le) (fun i => (hage i).le) hupper
    · exact haccuracy.comp hφ.tendsto_atTop

theorem exists_traces_on_sets_subsequence_or_presented_cap_sequence_of_scale_tendsto_atTop
    (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
    (s : ℕ → ℝ)
    (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (s i))
    (L : ∀ i, (G i).TerminalLimitMetric)
    (hinit : ∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i))
    (K : ∀ i, Set (G i).terminalRegularOpen) (Q : ℕ → ℝ)
    {a q : ℝ} (ha : 0 < a) (hq : 0 < q) (C : ℝ≥0)
    (htime : ∀ i, a ≤ s i)
    (hhigh : Tendsto Q atTop atTop)
    (hscalar : ∀ i x, x ∈ K i → metricScalarAt (L i).metric x ≤ (3 / 2 : ℝ) * Q i)
    (hderiv : ∀ i j, j.succ ≤ last i →
      ∀ y : ((H i).stage j.castSucc).Carrier,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q < ((H i).event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H i).event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i x, x ∈ K i → ∀ t ∈ Ioo ((H i).time (last i)) (s i),
      q < (G i).flow.scalar t x.val →
      |derivWithin (fun v => (G i).flow.scalar v x.val) (Iic t) t| ≤
        C * (G i).flow.scalar t x.val ^ 2)
    (parameters : ℕ → CutoffParameters)
    (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i))
    (haccuracy : Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0))
    (hcap : ∀ i j, j.succ ≤ last i →
      ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric
            (((records i j).static b).witness.cap z)) :
    (∃ (θ : ℝ), 0 < θ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (first : ∀ i, Fin ((H (φ i)).eventCount + 1)) (hle : ∀ i, first i ≤ last (φ i)),
        (∀ i, (H (φ i)).time (first i) ≤ s (φ i) - θ / Q (φ i)) ∧
        ∀ i x, x ∈ K (φ i) → Nonempty (BackwardPointTrace (H (φ i)) (first i) (last (φ i))
          (hle i) x.val)) ∨
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧
        ∃ (x : ∀ i, (G (φ i)).terminalRegularOpen), (∀ i, x i ∈ K (φ i)) ∧
        ∃ (event : ∀ i, Fin (H (φ i)).eventCount)
          (hlast : ∀ i, (event i).succ ≤ last (φ i))
          (A : ∀ i, BackwardPointTrace (H (φ i)) (event i).succ (last (φ i))
            (hlast i) (x i).val)
          (boundary : ∀ i, ((H (φ i)).event (event i)).RetainedBoundaryIndex)
          (z : ℕ → ThreeBall),
          (∀ i, ((H (φ i)).event (event i)).transition.trace.presentation
            (((H (φ i)).event (event i)).transition.trace.capping.cap (boundary i).val (z i)) =
              Sum.inl ((A i).point (event i).succ le_rfl (hlast i))) ∧
          (∀ i, (A i).point (event i).succ le_rfl (hlast i) =
            ((records (φ i) (event i)).static (boundary i)).inclusion
              (((records (φ i) (event i)).static (boundary i)).witness.cap (z i))) ∧
          (∀ i, metricScalarAt ((H (φ i)).event (event i)).outputMetric
            ((A i).point (event i).succ le_rfl (hlast i)) < 2 * Q (φ i)) ∧
          (∀ i, ((records (φ i) (event i)).static (boundary i)).neck.scale < 4 * Q (φ i)) ∧
          (∀ i, 0 < ((records (φ i) (event i)).static (boundary i)).neck.scale *
            (s (φ i) - (H (φ i)).time (event i).succ)) ∧
          Tendsto (fun i => Q (φ i) *
            (s (φ i) - (H (φ i)).time (event i).succ)) atTop (𝓝 0) ∧
          Tendsto (fun i => ((records (φ i) (event i)).static (boundary i)).neck.scale *
            (s (φ i) - (H (φ i)).time (event i).succ)) atTop (𝓝 0) ∧
          Tendsto (fun i => (parameters (φ i)).modelAccuracy) atTop (𝓝 0) := by
  let θ₀ : ℝ := min (1 / 4) (6 * (C : ℝ) + 1)⁻¹
  have hθ₀ : 0 < θ₀ := lt_min (by norm_num) (by positivity)
  have hθsmall : θ₀ ≤ 1 / 4 := min_le_left _ _
  have hbudget : 6 * (C : ℝ) * θ₀ ≤ 1 := by
    have hb : θ₀ ≤ 1 / (6 * (C : ℝ) + 1) := by
      simpa only [θ₀, one_div] using (min_le_right (1 / 4 : ℝ) (6 * (C : ℝ) + 1)⁻¹)
    have hh := (le_div_iff₀ (by positivity : 0 < 6 * (C : ℝ) + 1)).mp hb
    nlinarith [hθ₀.le]
  obtain ⟨ψ, hψ, hψhigh⟩ := extraction_of_eventually_atTop
    (hhigh.eventually_ge_atTop (max q (θ₀ / a)))
  have hqQ (i : ℕ) : q ≤ Q (ψ i) := (le_max_left _ _).trans (hψhigh i)
  have hQpos (i : ℕ) : 0 < Q (ψ i) := hq.trans_le (hqQ i)
  have hroom (i : ℕ) : 0 ≤ s (ψ i) - θ₀ / Q (ψ i) := by
    have hb : θ₀ / a ≤ Q (ψ i) := (le_max_right _ _).trans (hψhigh i)
    have ht : θ₀ ≤ a * Q (ψ i) := by
      have hh := (div_le_iff₀ ha).mp hb
      nlinarith
    exact sub_nonneg.mpr (((div_le_iff₀ (hQpos i)).mpr ht).trans (htime (ψ i)))
  have halternative := exists_fixed_window_traces_on_sets_subsequence_or_presented_cap_sequence_with_vanishing_age
    (fun i => H (ψ i)) (fun i => last (ψ i)) (fun i => s (ψ i))
    (fun i => G (ψ i)) (fun i => L (ψ i)) (fun i => hinit (ψ i)) (fun i => K (ψ i))
    (fun _ => q) (fun i => Q (ψ i)) C hθ₀ (fun _ => hq) hqQ hθsmall hbudget hroom (fun i => hscalar (ψ i))
    (fun i j hj y t ht _ => hderiv (ψ i) j hj y t ht)
    (fun i x hx t ht _ => hfinal (ψ i) x hx t ht)
    (fun i => parameters (ψ i)) (fun i j => records (ψ i) j)
    (haccuracy.comp hψ.tendsto_atTop) (fun i j hj => hcap (ψ i) j hj)
  rcases halternative with ⟨θ, hθ, _, φ, hφ, first, hle, hfirst, htrace⟩ |
      ⟨φ, hφ, x, hx, event, hlast, A, boundary, z, hpres, hbirth, hscalar', hscale, hagepos,
        _hagebound, _htimebound, htimelim, hagelim, haccuracylim⟩
  · exact Or.inl ⟨θ, hθ, ψ ∘ φ, hψ.comp hφ, first, hle, hfirst, htrace⟩
  · exact Or.inr ⟨ψ ∘ φ, hψ.comp hφ, x, hx, event, hlast, A, boundary, z,
      hpres, hbirth, hscalar', hscale, hagepos, htimelim, hagelim, haccuracylim⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


theorem exists_fixed_backward_window_on_ball_at_scalar_derivative_contact
    (N : ℕ) (hN : 2 ≤ N) (D r eps : ℝ)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D)
    (hcapture : 2 * StandardCap.transitionEnd + 2 * Real.sqrt 8 < r / 2) :
    ∃ C : ℝ≥0, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i)),
      (∀ i j, j.succ ≤ last i → ∀ b, ((records i j).static b).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      (∀ i j, j.succ ≤ last i → ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric (((records i j).static b).witness.cap z)) →
      ∀ q₀ a₀ a : ℝ, 0 < q₀ → 0 < a₀ → 0 < a →
      (∀ i, a ≤ time i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i j, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
      (∀ i j, j.succ ≤ last i → ∀ y : ((H i).stage j.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          q₀ < ((H i).event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).event j).incoming.flow.scalar t y ^ 2) →
      (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ < (A i).flow.scalar t y →
        |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤ C * (A i).flow.scalar t y ^ 2) →
      ∀ x : ∀ i, ((H i).stage (last i)).Carrier,
      Tendsto (fun i => (A i).flow.scalar (time i) (x i)) atTop atTop →
      (∀ i y, q₀ < (A i).flow.scalar (time i) y → ∀ v : TangentSpace ThreeModel y,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) y v)| ≤
          C * (A i).flow.scalar (time i) y * Real.sqrt ((A i).flow.scalar (time i) y) *
            Real.sqrt (((A i).flow.base.metric (time i)).inner y v v)) →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i), v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i) * Real.sqrt ((A i).flow.scalar (time i) (x i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i) v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i) v)|) ∨
        C * (A i).flow.scalar (time i) (x i) ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i)) (Iic (time i)) (time i)|) →
      ∃ θ ρ : ℝ, 0 < θ ∧ 0 < ρ ∧ ∃ f : ℕ → ℕ, StrictMono f ∧
        ∃ (first : ∀ i, Fin ((H (f i)).eventCount + 1)) (hle : ∀ i, first i ≤ last (f i)),
          (∀ i, (H (f i)).time (first i) ≤ time (f i) - θ / (A (f i)).flow.scalar (time (f i)) (x (f i))) ∧
          ∀ i y, y ∈ riemannianClosedBallOf ((A (f i)).flow.base.metric (time (f i))) (x (f i))
            (ρ / Real.sqrt ((A (f i)).flow.scalar (time (f i)) (x (f i)))) →
            Nonempty (BackwardPointTrace (H (f i)) (first i) (last (f i)) (hle i) y) := by
  obtain ⟨C, hC, δ₀, hδ₀, hexclude⟩ :=
    exists_scalar_derivative_contact_exclusion_near_high_curvature_caps
      N hN D r eps heps hepssmall hr hfit 8 1 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num at hcapture ⊢; exact hcapture)
  refine ⟨C, hC, δ₀, hδ₀, ?_⟩
  intro H last time A hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hgradient hfail
  let Q : ℕ → ℝ := fun i => (A i).flow.scalar (time i) (x i)
  obtain ⟨ψ, hψ, hψhigh⟩ := extraction_of_eventually_atTop (hhigh.eventually_gt_atTop (2 * q₀))
  let ρ := Perelman.CanonicalNeighborhood.localPropagationRadius ((C : ℝ) / 2)
  have hρ : 0 < ρ := Perelman.CanonicalNeighborhood.localPropagationRadius_pos (by positivity)
  have hρ1 : ρ ≤ 1 :=
    (Perelman.CanonicalNeighborhood.localPropagationRadius_le (CStar := (C : ℝ) / 2) (by positivity)).trans (by norm_num)
  let G := fun i => (A (ψ i)).restrictIncoming le_rfl (A (ψ i)).lt le_rfl
  let L := fun i => (A (ψ i)).endpointTerminalLimitMetric ((H (ψ i)).stage (last (ψ i)))
  let K (i : ℕ) : Set (G i).terminalRegularOpen :=
    {y | y.val ∈ riemannianClosedBallOf ((A (ψ i)).flow.base.metric (time (ψ i))) (x (ψ i))
      (ρ / Real.sqrt (Q (ψ i)))}
  have hQpos (i : ℕ) : 0 < Q (ψ i) := (by positivity : 0 < 2 * q₀).trans (hψhigh i)
  have hscalar (i : ℕ) (y : (G i).terminalRegularOpen) :
      metricScalarAt (L i).metric y = (A (ψ i)).flow.scalar (time (ψ i)) y.val := by
    change metricScalarAt (((A (ψ i)).flow.base.metric (time (ψ i))).restrictOpen
      (G i).terminalRegularOpen) y = _
    rw [metricScalarAt_restrictOpen]
    rfl
  have hbounds (i : ℕ) (y : (G i).terminalRegularOpen) (hy : y ∈ K i) :
      Q (ψ i) / 4 ≤ (A (ψ i)).flow.scalar (time (ψ i)) y.val ∧
        (A (ψ i)).flow.scalar (time (ψ i)) y.val ≤ 3 * Q (ψ i) := by
    apply Perelman.CanonicalNeighborhood.scalar_bounds_on_ball_of_threshold_gradient_bound
      (A (ψ i)).flow C.property (hQpos i) (by have := hψhigh i; dsimp [Q] at *; linarith)
      (hgradient (ψ i)) rfl hy
  have hscalehigh : Tendsto (fun i => 2 * Q (ψ i)) atTop atTop :=
    (hhigh.comp hψ.tendsto_atTop).const_mul_atTop (by norm_num)
  have halt := exists_traces_on_sets_subsequence_or_presented_cap_sequence_of_scale_tendsto_atTop
    (fun i => H (ψ i)) (fun i => last (ψ i)) (fun i => time (ψ i)) G L
    (fun i => hinit (ψ i)) K (fun i => 2 * Q (ψ i)) ha hq₀ C
    (fun i => htime (ψ i)) hscalehigh
    (fun i y hy => by rw [hscalar]; have hb := (hbounds i y hy).2; nlinarith)
    (fun i => hderiv (ψ i)) (fun i y _ t ht hh => hfinal (ψ i) y.val t ht hh)
    (fun i => parameters (ψ i)) (fun i => records (ψ i))
    (herrorlim.comp hψ.tendsto_atTop) (fun i => hcap (ψ i))
  rcases halt with ⟨θ, hθ, φ, hφ, first, hle, hstart, htrace⟩ |
    ⟨φ, hφ, y, hy, event, hlast, trace, boundary, z, hpresentation, hbirth,
      hscalarBirth, hscale, hagepos, htimelim, hagelim, herrorlim'⟩
  · refine ⟨θ / 2, ρ, half_pos hθ, hρ, ψ ∘ φ, hψ.comp hφ, first, hle, ?_, ?_⟩
    · intro i
      simpa only [Function.comp_apply, div_div] using hstart i
    · intro i y hy
      let y' : (G (φ i)).terminalRegularOpen := ⟨y, by
        change y ∈ (G (φ i)).terminalRegularRegion
        rw [(A (ψ (φ i))).terminalRegularRegion_eq_univ ((H (ψ (φ i))).stage (last (ψ (φ i))))]
        trivial⟩
      exact htrace i y' hy
  · exfalso
    have hmarkhigh : Tendsto (fun i => (A (ψ (φ i))).flow.scalar (time (ψ (φ i))) (y i).val)
        atTop atTop := by
      apply tendsto_atTop_mono (fun i => (hbounds (φ i) (y i) (hy i)).1)
      exact ((hhigh.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop).atTop_div_const (by norm_num)
    have hmarktime : Tendsto (fun i => (A (ψ (φ i))).flow.scalar (time (ψ (φ i))) (y i).val *
        (time (ψ (φ i)) - (H (ψ (φ i))).time (event i).succ)) atTop (𝓝 0) := by
      have hupper : Tendsto (fun i => (3 / 2 : ℝ) *
          (2 * Q (ψ (φ i)) * (time (ψ (φ i)) - (H (ψ (φ i))).time (event i).succ))) atTop (𝓝 0) := by
        simpa only [mul_zero] using htimelim.const_mul (3 / 2 : ℝ)
      apply squeeze_zero _ _ hupper
      · intro i
        exact mul_nonneg ((div_pos (hQpos (φ i)) (by norm_num)).le.trans
          (hbounds (φ i) (y i) (hy i)).1)
          (sub_nonneg.mpr (((H (ψ (φ i))).time_strictMono.monotone (hlast i)).trans (A (ψ (φ i))).lt.le))
      · intro i
        have ht := sub_nonneg.mpr (((H (ψ (φ i))).time_strictMono.monotone (hlast i)).trans (A (ψ (φ i))).lt.le)
        have hh := mul_le_mul_of_nonneg_right (hbounds (φ i) (y i) (hy i)).2 ht
        nlinarith
    exact hexclude (fun i => H (ψ (φ i))) event (fun i => last (ψ (φ i))) hlast
      (fun i => time (ψ (φ i))) (fun i => A (ψ (φ i))) (fun i => hinit (ψ (φ i)))
      (fun i => parameters (ψ (φ i))) (fun i => records (ψ (φ i))) boundary
      (fun i => hcanonical (ψ (φ i)) (event i) (hlast i) (boundary i))
      (fun i => hmargin (ψ (φ i))) (fun i => hm (ψ (φ i))) herrorlim'
      q₀ a₀ hq₀ ha₀ (fun i => hfixed (ψ (φ i))) (fun i => hlower (ψ (φ i)))
      (fun i j _ hj => hδ (ψ (φ i)) j hj) (fun i j _ hj => hderiv (ψ (φ i)) j hj)
      (fun i => hfinal (ψ (φ i))) hagelim z (fun i => (y i).val) trace hbirth
      hmarkhigh hmarktime (fun i => Q (ψ (φ i))) (fun i => hQpos (φ i))
      (fun i => by have hh := hscale i; dsimp [Q] at *; linarith)
      (fun i => x (ψ (φ i)))
      (fun i => by
        have hh := hy i
        change riemannianEDistOf ((A (ψ (φ i))).flow.base.metric (time (ψ (φ i))))
          (x (ψ (φ i))) (y i).val ≤ ENNReal.ofReal (ρ / Real.sqrt (Q (ψ (φ i)))) at hh
        rw [riemannianEDistOf_comm]
        exact hh.trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right hρ1 (Real.sqrt_nonneg _))))
      (fun i => hfail (ψ (φ i)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


private theorem exists_uniform_scalar_derivative_contact_exclusion_near_high_curvature_caps :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (N : ℕ), 4 ≤ N → ∀ (D r eps : ℝ),
    0 < eps → eps ≤ 1 / 1000 → StandardCap.transitionEnd + eps⁻¹ + 1 < r →
    64 * (r + eps⁻¹) < D → ∀ (Cscale d b : ℝ), 0 < Cscale → 0 ≤ d → 0 < b →
    2 * StandardCap.transitionEnd + (d + b) * Real.sqrt Cscale < r / 2 →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ q₀ a₀ : ℝ, 0 < q₀ → 0 < a₀ →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ < (A i).flow.scalar t x →
        |derivWithin (fun v => (A i).flow.scalar v x) (Iic t) t| ≤ C * (A i).flow.scalar t x ^ 2) →
      Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, ((H i).stage (last i)).Carrier)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i)),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      Tendsto (fun i => (A i).flow.scalar (time i) (x i)) atTop atTop →
      Tendsto (fun i => (A i).flow.scalar (time i) (x i) *
        (time i - (H i).time (event i).succ)) atTop (𝓝 0) →
      ∀ (Qsel : ℕ → ℝ), (∀ i, 0 < Qsel i) → (∀ i, q i ≤ Cscale * Qsel i) →
      ∀ y : ∀ i, ((H i).stage (last i)).Carrier,
      (∀ i, riemannianEDistOf ((A i).flow.base.metric (time i)) (x i) (y i) ≤
        ENNReal.ofReal (d / Real.sqrt (Qsel i))) →
      (∀ i, (∃ v : TangentSpace ThreeModel (y i), v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (y i) * Real.sqrt ((A i).flow.scalar (time i) (y i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (y i) v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (y i) v)|) ∨
        C * (A i).flow.scalar (time i) (y i) ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (y i)) (Iic (time i)) (time i)|) → False := by
  obtain ⟨C, hC, hbase⟩ := exists_uniform_scalar_derivative_contact_exclusion_near_canonical_caps
  refine ⟨C, hC, ?_⟩
  intro N hN D r eps heps hepssmall hr hfit Cscale d b hCscale hd hb hcapture
  obtain ⟨C₀, hC₀, η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hmain⟩ :=
    hbase N hN D r eps heps hepssmall hr hfit Cscale d b hCscale hd hb hcapture
  obtain ⟨Cbirth, hCbirth, hupperBirth⟩ := exists_uniform_presented_cap_scalar_abs_bound_of_canonical_window.{u}
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H event last hle time A hinit parameters records boundary cap q age
    hcanonical hmargin hm herrorlim q₀ a₀ hq₀ ha₀ hfixed hlower hδ hderiv hfinal
    hagelim z x trace hbirth hhigh hnormalizedtime Qsel hQsel hscale y hnear hfail
  let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (last i))
  let x' : ∀ i, (G i).terminalRegularOpen := fun i => ⟨x i,by
    change x i ∈ (G i).terminalRegularRegion
    rw [(A i).terminalRegularRegion_eq_univ ((H i).stage (last i))]
    trivial⟩
  let Q := fun i => (A i).flow.scalar (time i) (x i)
  have hQ (i : ℕ) : Q i = metricScalarAt (L i).metric (x' i) := by
    change metricScalarAt ((A i).flow.base.metric (time i)) (x i) =
      metricScalarAt (((A i).flow.base.metric (time i)).restrictOpen (G i).terminalRegularOpen) (x' i)
    rw [metricScalarAt_restrictOpen]
  have hcoreD : StandardCap.transitionEnd < D + 1 := by
    linarith [inv_pos.mpr heps,StandardCap.transitionEnd_pos]
  have hupper : ∀ᶠ i in atTop, metricScalarAt (cap i).witness.metric ((cap i).witness.cap (z i)) ≤
      Cbirth * (cap i).neck.scale := by
    filter_upwards [herrorlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with i hi
    exact (le_abs_self _).trans (hupperBirth ((H i).event (event i))
      (hcoreD.trans_le (hmargin i)) hi.le (by have := hm i; omega) (cap i) (hcanonical i) (z i))
  have htime : ∀ᶠ i in atTop, Q i * (time i - (H i).time (event i).succ) ≤ 1 / (C+1) :=
    (hnormalizedtime.eventually (Iio_mem_nhds (by positivity : (0:ℝ) < 1/(C+1)))).mono fun i hi => hi.le
  have hqcap : Tendsto q atTop atTop := cap_scale_tendsto_atTop_of_terminal_scalar_tendsto
    H last time G L hinit x' Q hQ hhigh hq₀ hCbirth
    (show (C:ℝ) * (1/(C+1)) ≤ 1 by rw [mul_one_div]; exact (div_le_one (by positivity)).mpr (by linarith))
    parameters records event hle boundary z trace hbirth hupper htime hderiv
    (fun i t ht hh => hfinal i (x i) t ht hh)
  have hevent : ∀ᶠ i in atTop,
      (parameters i).modelAccuracy ≤ ε₀ ∧ q₀ ≤ C₀ * q i ∧ 1 ≤ a₀ * q i ∧
        age i ≤ η := by
    filter_upwards [herrorlim.eventually (Iio_mem_nhds hε₀),
      hqcap.eventually_ge_atTop (q₀ / C₀),hqcap.eventually_ge_atTop (1 / a₀),
      hagelim.eventually (Iio_mem_nhds hη)] with i hε hq hqa hage
    refine ⟨hε.le,?_,?_,hage.le⟩
    · have hh := (div_le_iff₀ hC₀).mp hq
      nlinarith
    · have hh := (div_le_iff₀ ha₀).mp hqa
      nlinarith
  obtain ⟨M,hM⟩ := eventually_atTop.mp hevent
  let f := fun i : ℕ => i + M
  have hf : Tendsto f atTop atTop := tendsto_add_atTop_nat M
  have hgood (i : ℕ) := hM (f i) (by dsimp [f]; omega)
  exact hmain (fun i => H (f i)) (fun i => event (f i)) (fun i => last (f i))
    (fun i => hle (f i)) (fun i => time (f i)) (fun i => A (f i)) (fun i => hinit (f i))
    (fun i => parameters (f i)) (fun i => records (f i)) (fun i => boundary (f i))
    (fun i => hcanonical (f i)) (fun i => hmargin (f i)) (fun i => hm (f i))
    (fun i => (hgood i).1) (herrorlim.comp hf) (fun _ => q₀) (fun _ => a₀)
    (fun _ => hq₀) (fun i => (hgood i).2.1) (fun i => (hgood i).2.2.1)
    (fun i => hfixed (f i)) (fun i => hlower (f i)) (fun i => hδ (f i))
    (fun i => hderiv (f i)) (fun i => hfinal (f i)) (fun i => (hgood i).2.2.2)
    (hagelim.comp hf) (fun i => z (f i)) (fun i => x (f i)) (fun i => trace (f i))
    (fun i => hbirth (f i)) (fun i => Qsel (f i)) (fun i => hQsel (f i))
    (fun i => hscale (f i)) (fun i => y (f i)) (fun i => hnear (f i)) (fun i => hfail (f i))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


private theorem exists_fixed_backward_window_on_bounded_scalar_ball_at_scalar_derivative_contact :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (R Amax : ℝ), 0 < R → 1 ≤ Amax →
    ∀ (N : ℕ), 4 ≤ N → ∀ (D r eps : ℝ),
    0 < eps → eps ≤ 1 / 1000 → StandardCap.transitionEnd + eps⁻¹ + 1 < r →
    64 * (r + eps⁻¹) < D →
    2 * StandardCap.transitionEnd + (R + 1) * Real.sqrt (8 * Amax) < r / 2 →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i)),
      (∀ i j, j.succ ≤ last i → ∀ b, ((records i j).static b).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      (∀ i j, j.succ ≤ last i → ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric (((records i j).static b).witness.cap z)) →
      ∀ q₀ a₀ a : ℝ, 0 < q₀ → 0 < a₀ → 0 < a →
      (∀ i, a ≤ time i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i j, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
      (∀ i j, j.succ ≤ last i → ∀ y : ((H i).stage j.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          q₀ < ((H i).event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).event j).incoming.flow.scalar t y ^ 2) →
      (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ < (A i).flow.scalar t y →
        |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤ C * (A i).flow.scalar t y ^ 2) →
      ∀ x : ∀ i, ((H i).stage (last i)).Carrier,
      Tendsto (fun i => (A i).flow.scalar (time i) (x i)) atTop atTop →
      (∀ i y, q₀ < (A i).flow.scalar (time i) y → ∀ v : TangentSpace ThreeModel y,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) y v)| ≤
          C * (A i).flow.scalar (time i) y * Real.sqrt ((A i).flow.scalar (time i) y) *
            Real.sqrt (((A i).flow.base.metric (time i)).inner y v v)) →
      (∀ i y, y ∈ riemannianClosedBallOf ((A i).flow.base.metric (time i)) (x i)
          (R / Real.sqrt ((A i).flow.scalar (time i) (x i))) →
        (A i).flow.scalar (time i) y ≤ 2 * Amax * (A i).flow.scalar (time i) (x i)) →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i), v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i) * Real.sqrt ((A i).flow.scalar (time i) (x i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i) v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i) v)|) ∨
        C * (A i).flow.scalar (time i) (x i) ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i)) (Iic (time i)) (time i)|) →
      ∃ θ : ℝ, 0 < θ ∧ ∃ f : ℕ → ℕ, StrictMono f ∧
        ∃ (first : ∀ i, Fin ((H (f i)).eventCount + 1)) (hle : ∀ i, first i ≤ last (f i)),
          (∀ i, (H (f i)).time (first i) ≤ time (f i) - θ / (A (f i)).flow.scalar (time (f i)) (x (f i))) ∧
          ∀ i y, y ∈ riemannianClosedBallOf ((A (f i)).flow.base.metric (time (f i))) (x (f i))
            (R / Real.sqrt ((A (f i)).flow.scalar (time (f i)) (x (f i)))) →
            Nonempty (BackwardPointTrace (H (f i)) (first i) (last (f i)) (hle i) y) := by
  obtain ⟨C, hC, hbase⟩ := exists_uniform_scalar_derivative_contact_exclusion_near_high_curvature_caps
  refine ⟨C, hC, ?_⟩
  intro R Amax hR hAmax N hN D r eps heps hepssmall hr hfit hcapture
  obtain ⟨δ₀, hδ₀, hexclude⟩ := hbase N hN D r eps heps hepssmall hr hfit
    (8 * Amax) R 1 (by positivity) hR.le (by norm_num) hcapture
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H last time A hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hgradient hupper
    hfail
  let Q : ℕ → ℝ := fun i => (A i).flow.scalar (time i) (x i)
  let den := (2 + (C : ℝ) * R) ^ 2
  have hden : 0 < den := by dsimp [den]; positivity
  obtain ⟨ψ, hψ, hψhigh⟩ := extraction_of_eventually_atTop (hhigh.eventually_gt_atTop (q₀ * den))
  let G := fun i => (A (ψ i)).restrictIncoming le_rfl (A (ψ i)).lt le_rfl
  let L := fun i => (A (ψ i)).endpointTerminalLimitMetric ((H (ψ i)).stage (last (ψ i)))
  let K (i : ℕ) : Set (G i).terminalRegularOpen :=
    {y | y.val ∈ riemannianClosedBallOf ((A (ψ i)).flow.base.metric (time (ψ i))) (x (ψ i))
      (R / Real.sqrt (Q (ψ i)))}
  have hQpos (i : ℕ) : 0 < Q (ψ i) := (mul_pos hq₀ hden).trans (hψhigh i)
  have hscalar (i : ℕ) (y : (G i).terminalRegularOpen) :
      metricScalarAt (L i).metric y = (A (ψ i)).flow.scalar (time (ψ i)) y.val := by
    change metricScalarAt (((A (ψ i)).flow.base.metric (time (ψ i))).restrictOpen
      (G i).terminalRegularOpen) y = _
    rw [metricScalarAt_restrictOpen]
    rfl
  have hbounds (i : ℕ) (y : (G i).terminalRegularOpen) (hy : y ∈ K i) :
      Q (ψ i) / den ≤ (A (ψ i)).flow.scalar (time (ψ i)) y.val ∧
        (A (ψ i)).flow.scalar (time (ψ i)) y.val ≤ 2 * Amax * Q (ψ i) := by
    refine ⟨?_, hupper (ψ i) y.val hy⟩
    have hf : ContMDiff ThreeModel 𝓘(ℝ, ℝ) 1 ((A (ψ i)).flow.scalar (time (ψ i))) :=
      (scalarSmoothOfSolution (A (ψ i)).flow (time (ψ i))).of_le (by simp)
    exact (DifferentialGeometry.Geometry.Metric.lower_bound_on_closed_ball_of_threshold_gradient_bound
      ((A (ψ i)).flow.base.metric (time (ψ i))) hf C.property (hQpos i) hR.le
      (by apply (le_div_iff₀ hden).mpr; exact (hψhigh i).le)
      (hgradient (ψ i)) rfl hy).le
  have hscalehigh : Tendsto (fun i => 2 * Amax * Q (ψ i)) atTop atTop :=
    (hhigh.comp hψ.tendsto_atTop).const_mul_atTop (by positivity)
  have halt := exists_traces_on_sets_subsequence_or_presented_cap_sequence_of_scale_tendsto_atTop
    (fun i => H (ψ i)) (fun i => last (ψ i)) (fun i => time (ψ i)) G L
    (fun i => hinit (ψ i)) K (fun i => 2 * Amax * Q (ψ i)) ha hq₀ C
    (fun i => htime (ψ i)) hscalehigh
    (fun i y hy => by
      rw [hscalar]
      exact (hbounds i y hy).2.trans (by nlinarith [mul_pos (by positivity : 0 < 2 * Amax) (hQpos i)]))
    (fun i => hderiv (ψ i)) (fun i y _ t ht hh => hfinal (ψ i) y.val t ht hh)
    (fun i => parameters (ψ i)) (fun i => records (ψ i))
    (herrorlim.comp hψ.tendsto_atTop) (fun i => hcap (ψ i))
  rcases halt with ⟨θ, hθ, φ, hφ, first, hle, hstart, htrace⟩ |
    ⟨φ, hφ, y, hy, event, hlast, trace, boundary, z, hpresentation, hbirth,
      hscalarBirth, hscale, hagepos, htimelim, hagelim, herrorlim'⟩
  · refine ⟨θ / (2 * Amax), div_pos hθ (by positivity), ψ ∘ φ, hψ.comp hφ, first, hle, ?_, ?_⟩
    · intro i
      simpa only [Function.comp_apply, div_div] using hstart i
    · intro i y hy
      let y' : (G (φ i)).terminalRegularOpen := ⟨y, by
        change y ∈ (G (φ i)).terminalRegularRegion
        rw [(A (ψ (φ i))).terminalRegularRegion_eq_univ ((H (ψ (φ i))).stage (last (ψ (φ i))))]
        trivial⟩
      exact htrace i y' hy
  · exfalso
    have hmarkhigh : Tendsto (fun i => (A (ψ (φ i))).flow.scalar (time (ψ (φ i))) (y i).val)
        atTop atTop := by
      apply tendsto_atTop_mono (fun i => (hbounds (φ i) (y i) (hy i)).1)
      exact ((hhigh.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop).atTop_div_const hden
    have hmarktime : Tendsto (fun i => (A (ψ (φ i))).flow.scalar (time (ψ (φ i))) (y i).val *
        (time (ψ (φ i)) - (H (ψ (φ i))).time (event i).succ)) atTop (𝓝 0) := by
      have hupperlim := htimelim
      apply squeeze_zero _ _ hupperlim
      · intro i
        exact mul_nonneg ((div_pos (hQpos (φ i)) hden).le.trans
          (hbounds (φ i) (y i) (hy i)).1)
          (sub_nonneg.mpr (((H (ψ (φ i))).time_strictMono.monotone (hlast i)).trans (A (ψ (φ i))).lt.le))
      · intro i
        have ht := sub_nonneg.mpr (((H (ψ (φ i))).time_strictMono.monotone (hlast i)).trans (A (ψ (φ i))).lt.le)
        exact mul_le_mul_of_nonneg_right (hbounds (φ i) (y i) (hy i)).2 ht
    exact hexclude (fun i => H (ψ (φ i))) event (fun i => last (ψ (φ i))) hlast
      (fun i => time (ψ (φ i))) (fun i => A (ψ (φ i))) (fun i => hinit (ψ (φ i)))
      (fun i => parameters (ψ (φ i))) (fun i => records (ψ (φ i))) boundary
      (fun i => hcanonical (ψ (φ i)) (event i) (hlast i) (boundary i))
      (fun i => hmargin (ψ (φ i))) (fun i => hm (ψ (φ i))) herrorlim'
      q₀ a₀ hq₀ ha₀ (fun i => hfixed (ψ (φ i))) (fun i => hlower (ψ (φ i)))
      (fun i j _ hj => hδ (ψ (φ i)) j hj) (fun i j _ hj => hderiv (ψ (φ i)) j hj)
      (fun i => hfinal (ψ (φ i))) hagelim z (fun i => (y i).val) trace hbirth
      hmarkhigh hmarktime (fun i => Q (ψ (φ i))) (fun i => hQpos (φ i))
      (fun i => by have hh := hscale i; dsimp [Q] at *; linarith)
      (fun i => x (ψ (φ i)))
      (fun i => by
        have hh := hy i
        change riemannianEDistOf ((A (ψ (φ i))).flow.base.metric (time (ψ (φ i))))
          (x (ψ (φ i))) (y i).val ≤ ENNReal.ofReal (R / Real.sqrt (Q (ψ (φ i)))) at hh
        rw [riemannianEDistOf_comm]
        exact hh)
      (fun i => hfail (ψ (φ i)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


private theorem exists_eventually_backward_window_on_bounded_scalar_ball_of_contact :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (R Amax : ℝ), 0 < R → 1 ≤ Amax →
    ∀ (N : ℕ), 4 ≤ N → ∀ (D r eps : ℝ),
    0 < eps → eps ≤ 1 / 1000 → StandardCap.transitionEnd + eps⁻¹ + 1 < r →
    64 * (r + eps⁻¹) < D →
    2 * StandardCap.transitionEnd + (R + 1) * Real.sqrt (8 * Amax) < r / 2 →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i)),
      (∀ i j, j.succ ≤ last i → ∀ b, ((records i j).static b).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      (∀ i j, j.succ ≤ last i → ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric (((records i j).static b).witness.cap z)) →
      ∀ q₀ a₀ a : ℝ, 0 < q₀ → 0 < a₀ → 0 < a →
      (∀ i, a ≤ time i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i j, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
      (∀ i j, j.succ ≤ last i → ∀ y : ((H i).stage j.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          q₀ < ((H i).event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).event j).incoming.flow.scalar t y ^ 2) →
      (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ < (A i).flow.scalar t y →
        |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤ C * (A i).flow.scalar t y ^ 2) →
      ∀ x : ∀ i, ((H i).stage (last i)).Carrier,
      Tendsto (fun i => (A i).flow.scalar (time i) (x i)) atTop atTop →
      (∀ i y, q₀ < (A i).flow.scalar (time i) y → ∀ v : TangentSpace ThreeModel y,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) y v)| ≤
          C * (A i).flow.scalar (time i) y * Real.sqrt ((A i).flow.scalar (time i) y) *
            Real.sqrt (((A i).flow.base.metric (time i)).inner y v v)) →
      (∀ i y, y ∈ riemannianClosedBallOf ((A i).flow.base.metric (time i)) (x i)
          (R / Real.sqrt ((A i).flow.scalar (time i) (x i))) →
        (A i).flow.scalar (time i) y ≤ 2 * Amax * (A i).flow.scalar (time i) (x i)) →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i), v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i) * Real.sqrt ((A i).flow.scalar (time i) (x i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i) v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i) v)|) ∨
        C * (A i).flow.scalar (time i) (x i) ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i)) (Iic (time i)) (time i)|) →
      ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ i in atTop,
        ∃ (first : Fin ((H i).eventCount + 1)) (hle : first ≤ last i),
          (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i) ∧
          ∀ y ∈ riemannianClosedBallOf ((A i).flow.base.metric (time i)) (x i)
            (R / Real.sqrt ((A i).flow.scalar (time i) (x i))),
            Nonempty (BackwardPointTrace (H i) first (last i) hle y) := by
  obtain ⟨C, hC, hbase⟩ := exists_fixed_backward_window_on_bounded_scalar_ball_at_scalar_derivative_contact
  refine ⟨C, hC, ?_⟩
  intro R Amax hR hAmax N hN D r eps heps hepssmall hr hfit hcapture
  obtain ⟨δ₀, hδ₀, htrace⟩ := hbase R Amax hR hAmax N hN D r eps
    heps hepssmall hr hfit hcapture
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H last time A hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hgradient hupper hfail
  let P (i : ℕ) (θ : ℝ) : Prop :=
    ∃ (first : Fin ((H i).eventCount + 1)) (hle : first ≤ last i),
      (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i) ∧
      ∀ y ∈ riemannianClosedBallOf ((A i).flow.base.metric (time i)) (x i)
        (R / Real.sqrt ((A i).flow.scalar (time i) (x i))),
        Nonempty (BackwardPointTrace (H i) first (last i) hle y)
  have hseq (f : ℕ → ℕ) (hf : StrictMono f) :
      ∃ θ : ℝ, 0 < θ ∧ ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ i, P (f (g i)) θ := by
    obtain ⟨θ, hθ, g, hg, first, hle, hstart, htraces⟩ :=
      htrace (fun i => H (f i)) (fun i => last (f i)) (fun i => time (f i))
        (fun i => A (f i)) (fun i => hinit (f i)) (fun i => parameters (f i))
        (fun i => records (f i)) (fun i => hcanonical (f i)) (fun i => hmargin (f i))
        (fun i => hm (f i)) (herrorlim.comp hf.tendsto_atTop) (fun i => hcap (f i))
        q₀ a₀ a hq₀ ha₀ ha (fun i => htime (f i)) (fun i => hfixed (f i))
        (fun i => hlower (f i)) (fun i => hδ (f i)) (fun i => hderiv (f i))
        (fun i => hfinal (f i)) (fun i => x (f i)) (hhigh.comp hf.tendsto_atTop)
        (fun i => hgradient (f i)) (fun i => hupper (f i)) (fun i => hfail (f i))
    exact ⟨θ, hθ, g, hg, fun i => ⟨first i, hle i, hstart i, htraces i⟩⟩
  have hQevent : ∀ᶠ i in atTop, 0 < (A i).flow.scalar (time i) (x i) := hhigh.eventually_gt_atTop 0
  let P' (i : ℕ) (θ : ℝ) : Prop :=
    0 < (A i).flow.scalar (time i) (x i) → P i θ
  have hmono (i : ℕ) {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (hi : P' i δ) : P' i ε := by
    intro hQ
    obtain ⟨first, hle, hstart, htraces⟩ := hi hQ
    exact ⟨first, hle, hstart.trans (sub_le_sub_left (div_le_div_of_nonneg_right hεδ hQ.le) (time i)), htraces⟩
  have hseq' (f : ℕ → ℕ) (hf : StrictMono f) :
      ∃ θ : ℝ, 0 < θ ∧ ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ i, P' (f (g i)) θ := by
    obtain ⟨θ, hθ, g, hg, hp⟩ := hseq f hf
    exact ⟨θ, hθ, g, hg, fun i _ => hp i⟩
  obtain ⟨θ, hθ, hevent⟩ := Filter.exists_pos_eventually_of_antitone_of_subsequence P' hmono hseq'
  exact ⟨θ, hθ, (hevent.and hQevent).mono (fun i hi => hi.1 hi.2)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end

section

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u


theorem exists_eventually_backward_window_on_bounded_scalar_ball_at_scalar_derivative_contact :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (R Amax : ℝ), 0 < R → 1 ≤ Amax →
    ∀ (N : ℕ), 4 ≤ N → ∀ (D r eps : ℝ),
    0 < eps → eps ≤ 1 / 1000 → StandardCap.transitionEnd + eps⁻¹ + 1 < r →
    64 * (r + eps⁻¹) < D →
    2 * StandardCap.transitionEnd + (R + 1) * Real.sqrt (8 * Amax) < r / 2 →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (last : ∀ i, Fin ((H i).eventCount + 1))
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i j, GeometricCutoffRecord (H i) j (parameters i)),
      (∀ i j, j.succ ≤ last i → ∀ b, ((records i j).static b).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      (∀ i j, j.succ ≤ last i → ∀ (b : ((H i).event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i j).static b).neck.scale / 2 ≤
          metricScalarAt ((records i j).static b).witness.metric (((records i j).static b).witness.cap z)) →
      ∀ q₀ a₀ a : ℝ, 0 < q₀ → 0 < a₀ → 0 < a →
      (∀ i, a ≤ time i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) a₀ x) →
      (∀ i x, -3 / a₀ ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i j, j.succ ≤ last i → ∀ b, (records i j).delta b ≤ δ₀) →
      (∀ i j, j.succ ≤ last i → ∀ y : ((H i).stage j.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
          q₀ < ((H i).event j).incoming.flow.scalar t y →
          |derivWithin (fun v => ((H i).event j).incoming.flow.scalar v y) (Iic t) t| ≤
            C * ((H i).event j).incoming.flow.scalar t y ^ 2) →
      (∀ i y, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ < (A i).flow.scalar t y →
        |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤ C * (A i).flow.scalar t y ^ 2) →
      ∀ x : ∀ i, ((H i).stage (last i)).Carrier,
      Tendsto (fun i => (A i).flow.scalar (time i) (x i)) atTop atTop →
      (∀ i y, q₀ < (A i).flow.scalar (time i) y → ∀ v : TangentSpace ThreeModel y,
        |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) y v)| ≤
          C * (A i).flow.scalar (time i) y * Real.sqrt ((A i).flow.scalar (time i) y) *
            Real.sqrt (((A i).flow.base.metric (time i)).inner y v v)) →
      (∀ i y, y ∈ riemannianClosedBallOf ((A i).flow.base.metric (time i)) (x i)
          (R / Real.sqrt ((A i).flow.scalar (time i) (x i))) →
        (A i).flow.scalar (time i) y ≤ 2 * Amax * (A i).flow.scalar (time i) (x i)) →
      (∀ i, (∃ v : TangentSpace ThreeModel (x i), v ≠ 0 ∧
          C * (A i).flow.scalar (time i) (x i) * Real.sqrt ((A i).flow.scalar (time i) (x i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i) v v) ≤
            |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i) v)|) ∨
        C * (A i).flow.scalar (time i) (x i) ^ 2 ≤
          |derivWithin (fun t => (A i).flow.scalar t (x i)) (Iic (time i)) (time i)|) →
      ∃ θ : ℝ, 0 < θ ∧ 6 * C * (Amax * θ) ≤ 1 ∧ ∀ᶠ i in atTop,
        ∃ (first : Fin ((H i).eventCount + 1)) (hle : first ≤ last i),
          (H i).time first ≤ time i - θ / (A i).flow.scalar (time i) (x i) ∧
          ∀ y ∈ riemannianClosedBallOf ((A i).flow.base.metric (time i)) (x i)
            (R / Real.sqrt ((A i).flow.scalar (time i) (x i))),
            Nonempty (BackwardPointTrace (H i) first (last i) hle y) := by
  obtain ⟨C, hC, hbase⟩ := exists_eventually_backward_window_on_bounded_scalar_ball_of_contact
  refine ⟨C, hC, ?_⟩
  intro R Amax hR hAmax N hN D r eps heps hepssmall hr hfit hcapture
  obtain ⟨δ₀, hδ₀, htrace⟩ := hbase R Amax hR hAmax N hN D r eps
    heps hepssmall hr hfit hcapture
  refine ⟨δ₀, hδ₀, ?_⟩
  intro H last time A hinit parameters records hcanonical hmargin hm herrorlim hcap
    q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hgradient hupper hfail
  obtain ⟨θ, hθ, htrace⟩ := htrace H last time A hinit parameters records hcanonical hmargin hm
    herrorlim hcap q₀ a₀ a hq₀ ha₀ ha htime hfixed hlower hδ hderiv hfinal x hhigh hgradient hupper hfail
  let θ' := min θ (1 / (6 * (C : ℝ) * Amax + 1))
  have hθ' : 0 < θ' := lt_min hθ (by positivity)
  have hsmall : θ' ≤ θ := min_le_left _ _
  have hbudget : 6 * (C : ℝ) * (Amax * θ') ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 6 * (C : ℝ) * Amax + 1)).mp
      (min_le_right θ (1 / (6 * (C : ℝ) * Amax + 1)))
    nlinarith [hθ'.le]
  refine ⟨θ', hθ', hbudget, ?_⟩
  filter_upwards [htrace, hhigh.eventually_gt_atTop 0] with i hi hQ
  obtain ⟨first, hle, hstart, htraces⟩ := hi
  exact ⟨first, hle, hstart.trans (sub_le_sub_left (div_le_div_of_nonneg_right hsmall hQ.le) (time i)), htraces⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
end
