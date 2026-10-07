import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70B12Cone_O47

/-!
# CH12-O47, group 4: B1 + B2 on the escape limit of slice slabs — flow side from the profile

`slice_b12_of_escape_limit_O47`: `b12_of_escape_limit_O47` on the slice slabs
`sliceSlabR_O3 Fs (sl i)` (MicroGlueSliceTransfer) with threshold `q i = neckRadius((sl i).time)⁻²`:
the derivative / gradient bounds (`sliceSlab_derivative_O3` under `P2_O2 Hp Ctime`,
`sliceSlab_gradient_O3`), the canonical neighbourhoods (`sliceSlab_canonical_O3`, ε = Hp.epsilon)
and the pinching (`slice_pinching_O3`) all come from the profile.  Remaining inputs: the escape
limit data (Pl, F, M, …), the neck tolerance `heps` for Hp.epsilon, and `hQlim`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
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

/-- **B1 + B2 on slice slabs** (cone-end input form), flow-side hypotheses from the profile. -/
theorem slice_b12_of_escape_limit_O47 {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
    {Fs : GC.Interface.RawSurgery P₀ g₀} {δ : ℝ → ℝ}
    (Hp : GC.LongTime.AnalyticSurgeryProfile Fs δ) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime)
    (sl : ℕ → RegularSlice Fs.observation)
    (x : ∀ i, ((sliceSlabR_O3 Fs (sl i)).restrictIncoming le_rfl (sliceSlabR_O3 Fs (sl i)).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (sliceSlabR_O3 Fs (sl i)).flow.scalar (sl i).time (x i).val)
    (hqQ : ∀ i, (Hp.parameters.neckRadius (sl i).time ^ 2)⁻¹ ≤ (sliceSlabR_O3 Fs (sl i)).flow.scalar (sl i).time (x i).val)
    (hqlim : Tendsto (fun i => (Hp.parameters.neckRadius (sl i).time ^ 2)⁻¹ / (sliceSlabR_O3 Fs (sl i)).flow.scalar (sl i).time (x i).val) atTop (𝓝 0))
    {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1 / 11)
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
    (hQlim : Tendsto (fun n => (sliceSlabR_O3 Fs (sl (f n))).flow.scalar (sl (f n)).time (x (f n)).val) atTop atTop) :
    ∃ (LM : Type u) (_ : MetricSpace LM) (_ : ChartedSpace ThreeSpace LM)
      (_ : IsManifold ThreeModel ∞ LM) (_ : SigmaCompactSpace LM)
      (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM),
      (∀ a b : LM, edist a b = riemannianEDistOf gL a b) ∧
      (∀ z : LM, SectionalBoundedBelowAt gL z 0) ∧
      ∃ γ : ℝ → LM, γ 0 = x₀ ∧
        (∀ t₁ ∈ Ico (0 : ℝ) rho, ∀ t₂ ∈ Ico (0 : ℝ) rho,
          riemannianEDistOf gL (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|) ∧
        Tendsto (fun t => metricScalarAt gL (γ t)) (𝓝[<] rho) atTop ∧
        ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < rho ∧ ∀ t ∈ Ico t₀ rho, Nonempty (SpatialNeck gL alpha (γ t)) := by
  obtain ⟨phi, hadm, hphi⟩ := slice_pinching_O3 Hp
  exact b12_of_escape_limit_O47
    (fun i => (sliceHistoryR_O3 Fs (sl i)).stage (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))
    (fun i => (sliceHistoryR_O3 Fs (sl i)).time (Fin.last (sliceHistoryR_O3 Fs (sl i)).eventCount))
    (fun i => (sl i).time) (fun i => sliceSlabR_O3 Fs (sl i)) Ctime
    ⟨Hp.C2, by linarith [Hp.C2_ge_one]⟩ (fun i => (Hp.parameters.neckRadius (sl i).time ^ 2)⁻¹)
    (fun i y t ht hq => sliceSlab_derivative_O3 Hp (sl i) Ctime _ hP2 le_rfl y t ht hq)
    (fun i y t ht hq v => sliceSlab_gradient_O3 Hp (sl i) _ le_rfl y t ht hq v)
    x hQ hqQ hqlim halpha halpha1 heps (fun i y hy => sliceSlab_canonical_O3 Hp (sl i) y hy)
    hrho f hf r hr hrlim Pl F M hcanonical hradial hcompact hcapture hlower z hfinite hdist hhigh
    hadm (fun i => (hphi (sl i)).2.2) hQlim

end GC.LongTime.Ch12
