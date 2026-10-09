import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70B12Slice_O47
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70B3Cone_O39
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueTracedLocal

/-!
# CH12-O53, group 1: KL70.2 C2 in cone-end form — slice cone exclusion on the escape limit

`[FROZEN v2] CH12-O53 hC2`.  On the escape limit `Pl` of the rescaled slice slabs
(the data of `slice_b12_of_escape_limit_O47`):

* `escape_ray_necks_O47` / `escape_sec_nonneg_O47` give the ray with spatial necks and `Rm ≥ 0` on
  `Pl` itself (not behind an `∃ LM`);
* `cone_end_of_ray_necks_O39` (B3 v2) gives the punctured-cone end `W, qW, delta, xW` in `Pl`;
* the tree theorem `final_slab_punctured_cone_end_exclusion_of_trace_chains_local_O3` (second
  blow-up at `xW`: local backward limit flow with `Rm ≥ 0` from the pinching, strong maximum
  principle through `rescaled_end_cone_exclusion`) closes the contradiction.  All its flow-side
  inputs on slice slabs are theorems (`slice_pinching_O3`, `sliceSlab_derivative_O3`,
  `sliceHistory_eventSlabsDerivative_O3`, `sliceSlab_canonical_O3`, `sliceSlabR_initial_O3`,
  `slice_precedingR_O3`), except the local volume test `(σ, κ, hloc)` and the backward traces at
  the second blow-up points (`htrace`), which are inline binders in the tree's shape.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- **KL70.2 C2 (cone-end form)**: no punctured-cone end on the slice escape limit. -/
theorem hC2_O53 {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
    {Fs : GC.Interface.RawSurgery P₀ g₀} {δ : ℝ → ℝ}
    (Hp : GC.LongTime.AnalyticSurgeryProfile Fs δ) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime)
    (sl : ℕ → RegularSlice Fs.observation)
    (x : ∀ i, ((sliceSlabR_O3 Fs (sl i)).restrictIncoming le_rfl (sliceSlabR_O3 Fs (sl i)).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (sliceSlabR_O3 Fs (sl i)).flow.scalar (sl i).time (x i).val)
    (hqQ : ∀ i, (Hp.parameters.neckRadius (sl i).time ^ 2)⁻¹ ≤ (sliceSlabR_O3 Fs (sl i)).flow.scalar (sl i).time (x i).val)
    (hqlim : Tendsto (fun i => (Hp.parameters.neckRadius (sl i).time ^ 2)⁻¹ / (sliceSlabR_O3 Fs (sl i)).flow.scalar (sl i).time (x i).val) atTop (𝓝 0))
    {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1 / 2000000)
    (heps : 13000 * (13000 * Hp.epsilon) ≤
      min (neckModelTolerance (alpha / 26000)) ((alpha / 26000) / 64))
    {rho : ℝ} (hrho : 0 < rho) (f : ℕ → ℕ) (hf : StrictMono f)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 rho))
    (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((sliceSlabR_O3 Fs (sl i)).restrictIncoming le_rfl (sliceSlabR_O3 Fs (sl i)).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((sliceSlabR_O3 Fs (sl i)).flow.scalar (sl i).time (x i).val)
              (zero_lt_one.trans_le (hQ i)) ((sliceSlabR_O3 Fs (sl i)).endpointTerminalLimitMetric ((sliceHistoryR_O3 Fs (sl i)).stage (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hradial : ∀ z : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R))
    (hcapture : ∀ n, riemannianClosedBallOf
      (scaleMetric ((sliceSlabR_O3 Fs (sl (f n))).flow.scalar (sl (f n)).time (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((sliceSlabR_O3 Fs (sl (f n))).endpointTerminalLimitMetric ((sliceHistoryR_O3 Fs (sl (f n))).stage (Fin.last (sliceHistoryR_O3 Fs (sl (f n))).eventCount))).metric)
      (x (f n)) (r n) ⊆ F.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y ∈ F.source n, ∀ v : TangentSpace ThreeModel y,
      (1 - ε) * Pl.metric.inner y v v ≤
        (scaleMetric ((sliceSlabR_O3 Fs (sl (f n))).flow.scalar (sl (f n)).time (x (f n)).val)
          (zero_lt_one.trans_le (hQ (f n)))
          ((sliceSlabR_O3 Fs (sl (f n))).endpointTerminalLimitMetric ((sliceHistoryR_O3 Fs (sl (f n))).stage (Fin.last (sliceHistoryR_O3 Fs (sl (f n))).eventCount))).metric).inner (F.map n y)
          (mfderiv ThreeModel ThreeModel (F.map n) y v)
          (mfderiv ThreeModel ThreeModel (F.map n) y v))
    (z : ∀ n, ((sliceSlabR_O3 Fs (sl (f n))).restrictIncoming le_rfl (sliceSlabR_O3 Fs (sl (f n))).lt le_rfl).terminalRegularOpen)
    (hfinite : ∀ n, riemannianEDistOf
      (scaleMetric ((sliceSlabR_O3 Fs (sl (f n))).flow.scalar (sl (f n)).time (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((sliceSlabR_O3 Fs (sl (f n))).endpointTerminalLimitMetric ((sliceHistoryR_O3 Fs (sl (f n))).stage (Fin.last (sliceHistoryR_O3 Fs (sl (f n))).eventCount))).metric)
      (x (f n)) (z n) ≠ ⊤)
    (hdist : Tendsto (fun n => (riemannianEDistOf
      (scaleMetric ((sliceSlabR_O3 Fs (sl (f n))).flow.scalar (sl (f n)).time (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((sliceSlabR_O3 Fs (sl (f n))).endpointTerminalLimitMetric ((sliceHistoryR_O3 Fs (sl (f n))).stage (Fin.last (sliceHistoryR_O3 Fs (sl (f n))).eventCount))).metric)
      (x (f n)) (z n)).toReal) atTop (𝓝 rho))
    (hhigh : Tendsto (fun n => metricScalarAt
      ((sliceSlabR_O3 Fs (sl (f n))).endpointTerminalLimitMetric ((sliceHistoryR_O3 Fs (sl (f n))).stage (Fin.last (sliceHistoryR_O3 Fs (sl (f n))).eventCount))).metric (z n) /
        (sliceSlabR_O3 Fs (sl (f n))).flow.scalar (sl (f n)).time (x (f n)).val) atTop atTop)
    (hQlim : Tendsto (fun n => (sliceSlabR_O3 Fs (sl (f n))).flow.scalar (sl (f n)).time (x (f n)).val) atTop atTop)
    {κ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ)
    (hσlim : Tendsto (fun i => σ i *
      Real.sqrt ((sliceSlabR_O3 Fs (sl i)).flow.scalar (sl i).time (x i).val)) atTop atTop)
    (hloc : ∀ i (w : ((sliceSlabR_O3 Fs (sl i)).restrictIncoming le_rfl
        (sliceSlabR_O3 Fs (sl i)).lt le_rfl).terminalRegularOpen),
      riemannianEDistOf ((sliceSlabR_O3 Fs (sl i)).endpointTerminalLimitMetric
        ((sliceHistoryR_O3 Fs (sl i)).stage
          (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))).metric (x i) w <
        ENNReal.ofReal (σ i) →
      ∀ b : ℝ, 0 < b → b ≤ σ i →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel
            ((sliceSlabR_O3 Fs (sl i)).restrictIncoming le_rfl
              (sliceSlabR_O3 Fs (sl i)).lt le_rfl).terminalRegularOpen
            ((sliceSlabR_O3 Fs (sl i)).endpointTerminalLimitMetric
              ((sliceHistoryR_O3 Fs (sl i)).stage
                (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))).metric
            (riemannianBallOf ((sliceSlabR_O3 Fs (sl i)).endpointTerminalLimitMetric
              ((sliceHistoryR_O3 Fs (sl i)).stage
                (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))).metric w b))
    (htrace : ∀ xW : ℕ → Pl.M, Tendsto (fun n => metricScalarAt Pl.metric (xW n)) atTop atTop →
      ∃ θ₂ : ℝ, 0 < θ₂ ∧ ∀ m, ∀ᶠ n in atTop,
        ∃ first : Fin ((sliceHistoryR_O3 Fs (sl (f n))).eventCount + 1),
          (sliceHistoryR_O3 Fs (sl (f n))).time first ≤ (sl (f n)).time - θ₂ /
            (sliceSlabR_O3 Fs (sl (f n))).flow.scalar (sl (f n)).time (F.map n (xW m)).val ∧
          ∀ w ∈ riemannianBallOf ((sliceSlabR_O3 Fs (sl (f n))).flow.base.metric (sl (f n)).time)
            (F.map n (xW m)).val
            (Real.sqrt ((sliceSlabR_O3 Fs (sl (f n))).flow.scalar (sl (f n)).time
              (F.map n (xW m)).val))⁻¹,
            Nonempty (BackwardPointTrace (sliceHistoryR_O3 Fs (sl (f n))).toHistory first
              (Fin.last (sliceHistoryR_O3 Fs (sl (f n))).eventCount) (Fin.le_last first) w)) :
    False := by
  obtain ⟨phi, hadm, hphi⟩ := slice_pinching_O3 Hp
  have h1 := escape_ray_necks_O47
    (fun i => (sliceHistoryR_O3 Fs (sl i)).stage (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))
    (fun i => (sliceHistoryR_O3 Fs (sl i)).time (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))
    (fun i => (sl i).time) (fun i => sliceSlabR_O3 Fs (sl i)) Ctime
    ⟨Hp.C2, by linarith [Hp.C2_ge_one]⟩ (fun i => (Hp.parameters.neckRadius (sl i).time ^ 2)⁻¹)
    (fun i y t ht hq => sliceSlab_derivative_O3 Hp (sl i) Ctime _ hP2 le_rfl y t ht hq)
    (fun i y t ht hq v => sliceSlab_gradient_O3 Hp (sl i) _ le_rfl y t ht hq v)
    x hQ hqQ hqlim halpha (by linarith) heps (fun i y hy => sliceSlab_canonical_O3 Hp (sl i) y hy)
    hrho f hf r hr hrlim Pl F M hcanonical hradial hcompact hcapture hlower z hfinite hdist hhigh
  dsimp only at h1
  obtain ⟨hfin, γ, -, hiso, hblow, t₀, -, ht₀ρ, hnk⟩ := h1
  have hsec := escape_sec_nonneg_O47
    (fun i => (sliceHistoryR_O3 Fs (sl i)).stage (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))
    (fun i => (sliceHistoryR_O3 Fs (sl i)).time (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))
    (fun i => (sl i).time) (fun i => sliceSlabR_O3 Fs (sl i)) x hQ hadm
    (fun i => (hphi (sl i)).2.2) Pl F M hcanonical hQlim
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  let _ : MetricSpace Pl.M := EMetricSpace.toMetricSpace hfin
  obtain ⟨_, -, _, -, W, hW, hrest⟩ :=
    cone_end_of_ray_necks_O39 Pl.metric (fun _ _ => rfl) hsec hrho γ hiso hblow halpha halpha1
      ht₀ρ hnk
  have key := final_slab_punctured_cone_end_exclusion_of_trace_chains_local_O3
    (fun i => sliceHistoryR_O3 Fs (sl i)) (fun i => (sl i).time) (fun i => sliceSlabR_O3 Fs (sl i))
    (fun i => sliceSlabR_initial_O3 Fs (sl i)) (fun i => slice_precedingR_O3 Fs (sl i)) Ctime
    (fun i => (Hp.parameters.neckRadius (sl i).time ^ 2)⁻¹)
    (fun i => inv_pos.mpr (pow_pos (Hp.parameters.neckRadius_pos _ (sl i).positive.le) 2))
    (fun i j y t ht hq => sliceHistory_eventSlabsDerivative_O3 Hp (sl i) Ctime _ hP2 le_rfl j
      (Fin.castSucc_lt_last j) y t ht hq)
    (fun i y t ht hq => sliceSlab_derivative_O3 Hp (sl i) Ctime _ hP2 le_rfl y t ht hq)
    x hQ hqQ hadm (fun i j => (hphi (sl i)).1 j) (fun i => (hphi (sl i)).2.2) σ hκ hσlim hloc
    (fun i y hy => sliceSlab_canonical_O3 Hp (sl i) y hy) hf Pl F M hcanonical hradial hcompact
    W hW
  dsimp only at hrest key
  obtain ⟨qW, delta, hdelta, _, _, hK, hcover, xW, times, _, _, hx, _, hQW, hclow,
    ⟨B, _, hB⟩, hcone, _⟩ := hrest
  obtain ⟨θ₂, hθ₂, htr⟩ := htrace (fun n => (xW n : Pl.M))
    (by simpa only [metricScalarAt_restrictOpen] using hQW)
  refine key qW delta hdelta hK hcover hcone xW hx
    (by simpa only [metricScalarAt_restrictOpen] using hQW) θ₂ hθ₂ htr
    (((2 * alpha)⁻¹) ^ 2 / 8) (by positivity)
    (Eventually.of_forall fun n => by simpa only [metricScalarAt_restrictOpen] using hclow n)
    ⟨B, hB.mono fun n hn => by simpa only [metricScalarAt_restrictOpen] using hn⟩

end GC.LongTime.Ch12
