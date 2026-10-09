import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueLocalCone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceBoundedThreshold
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Analysis.Calculus.Compactness.DiagonalSubsequence

/-!
# CH12-O3, group 1d: the backward limit at the cone end with a local terminal volume test

The second blow-up of the KL70.2 kernel (`ST/BoundedCurvatureAtDistanceBoundedThreshold.lean:324`,
`:515`) is centred at `y m = F_{k m}(xW m)`, the image of a point `xW m` of the first limit `Pl`.
A *local* volume test about the first centre `x` transfers to `y m` only if `y m` stays at bounded
normalized distance from `x`.  This is supplied here:

* `local_shift_O3`: a local test of radius `σ` about `x` gives one of radius `σ - D/√Q` about any
  `y` at normalized distance `≤ D` from `x`.
* `exists_reindex_near_O3`: since every point of `Pl` lies at distance `< rho` from its basepoint and
  closed balls of radius `< rho` are compact, after re-indexing the convergence maps every
  `F_k(w m)` with `k ≥ φ m` lies at normalized distance `≤ 2 rho` from `x (f k)`
  (`edistOf_map_le_of_metric_upper_on_ball`).
* `exists_local_backward_limit_local_O3` (`:324` with the extra input `hnear`) and
  `final_slab_punctured_cone_end_exclusion_local_O3` (`:515`, which re-indexes and supplies `hnear`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance pointedLimitRegular_O3b (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

/-- Transfer of a local test along a bounded normalized displacement of the centre. -/
theorem local_shift_O3 {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (g : SmoothRiemannianMetric ThreeModel M) (x y : M)
    {Q D σ : ℝ} (hQ : 0 < Q) (hD : 0 ≤ D) (P : M → ℝ → Prop)
    (hnear : riemannianEDistOf (scaleMetric Q hQ g) x y ≤ ENNReal.ofReal D)
    (hloc : ∀ z : M, riemannianEDistOf g x z < ENNReal.ofReal σ → ∀ b : ℝ, 0 < b → b ≤ σ →
      P z b) :
    ∀ z : M, riemannianEDistOf g y z < ENNReal.ofReal (σ - D / Real.sqrt Q) →
      ∀ b : ℝ, 0 < b → b ≤ σ - D / Real.sqrt Q → P z b := by
  intro z hz b hb hbσ
  have hsq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hDQ : 0 ≤ D / Real.sqrt Q := div_nonneg hD hsq.le
  have hσ' : 0 < σ - D / Real.sqrt Q := hb.trans_le hbσ
  have hxy : riemannianEDistOf g x y ≤ ENNReal.ofReal (D / Real.sqrt Q) := by
    rw [DifferentialGeometry.edistOf_scale] at hnear
    have hmul : ENNReal.ofReal (Real.sqrt Q) * riemannianEDistOf g x y ≤
        ENNReal.ofReal (Real.sqrt Q) * ENNReal.ofReal (D / Real.sqrt Q) := by
      rw [← ENNReal.ofReal_mul hsq.le, mul_div_cancel₀ _ hsq.ne']
      exact hnear
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hsq).ne'
      ENNReal.ofReal_ne_top).mp hmul
  apply hloc z _ b hb (by linarith)
  calc riemannianEDistOf g x z ≤ riemannianEDistOf g x y + riemannianEDistOf g y z :=
        riemannianEDistOf_triangle g x y z
    _ < ENNReal.ofReal (D / Real.sqrt Q) + ENNReal.ofReal (σ - D / Real.sqrt Q) :=
        ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxy) hxy hz
    _ = ENNReal.ofReal σ := by
        rw [← ENNReal.ofReal_add hDQ hσ'.le]
        congr 1
        ring

/-- Re-indexing a pointed convergence so that the images of prescribed points of the limit stay at
normalized distance `≤ 2 rho` from the basepoints. -/
theorem exists_reindex_near_O3 {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X Pl f) (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    {rho : ℝ} (hradial : ∀ z : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R))
    (w : ℕ → Pl.M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m k : ℕ, φ m ≤ k →
      riemannianEDistOf (X.obj (f k)).metric (X.obj (f k)).basepoint
        (F.partialDiffeomorph k (w m)) ≤ ENNReal.ofReal (2 * rho) := by
  have hN : ∀ m, ∃ N : ℕ, ∀ k, N ≤ k →
      riemannianEDistOf (X.obj (f k)).metric (X.obj (f k)).basepoint
        (F.partialDiffeomorph k (w m)) ≤ ENNReal.ofReal (2 * rho) := by
    intro m
    have hd := hradial (w m)
    have hfin : riemannianEDistOf Pl.metric Pl.basepoint (w m) ≠ ⊤ := ne_top_of_lt hd
    have hrho : 0 < rho := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hd)
    set d := (riemannianEDistOf Pl.metric Pl.basepoint (w m)).toReal with hdef
    have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
    have hdlt : d < rho := by
      have := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hd
      rwa [ENNReal.toReal_ofReal hrho.le] at this
    set R := (d + rho) / 2 with hR
    have hRpos : 0 < R := by rw [hR]; linarith
    have hRrho : R < rho := by rw [hR]; linarith
    have hdR : d < R := by rw [hR]; linarith
    have hK := hcompact R hRpos.le hRrho
    have hconv : metricSourceConvergesOn F (CanonicalMetricCompactness.canonicalSourceData F)
        (riemannianClosedBallOf Pl.metric Pl.basepoint R) 0 := by
      have heq : M.domain = CanonicalMetricCompactness.canonicalSourceData F := funext hcanonical
      rw [← heq]
      exact M.converges _ hK 0
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (pointed_metric_eventually_quadratic_bounds hK hconv (by norm_num : (0 : ℝ) < 3))
    refine ⟨N, fun k hk => ?_⟩
    obtain ⟨hsrc, hb⟩ := hN k hk
    have hy : riemannianEDistOf Pl.metric Pl.basepoint (w m) < ENNReal.ofReal R := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hdR
    have hmain := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
      Pl.metric (X.obj (f k)).metric (F.partialDiffeomorph k) Pl.basepoint (w m) hRpos
      (by norm_num : (0 : ℝ) < 2) hsrc (fun z hz v => by
        have h := (hb z hz v).2
        change (X.obj (f k)).metric.inner (F.partialDiffeomorph k z)
          (mfderiv ThreeModel ThreeModel (F.partialDiffeomorph k) z v)
          (mfderiv ThreeModel ThreeModel (F.partialDiffeomorph k) z v) ≤ (1 + 3) * _ at h
        norm_num
        linarith) hy
    rw [F.basepoint_map k] at hmain
    refine hmain.trans ?_
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  choose N hN using hN
  obtain ⟨φ, hφ, hφN⟩ := exists_strictMono_ge N
  exact ⟨φ, hφ, fun m k hk => hN m k ((hφN m).trans hk)⟩

private theorem scaleMetric_mul_eq {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (g : SmoothRiemannianMetric ThreeModel M) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : c = a * b) :
    scaleMetric c hc g = scaleMetric a ha (scaleMetric b hb g) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  simp only [scaleMetric_inner]
  rw [habc]
  ring

theorem exists_local_backward_limit_local_O3
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (hderiv : ∀ i (j : Fin (H i).eventCount) (y : ((H i).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q i < ((H i).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hwindow : ∀ i, (H i).time (Fin.last (H i).eventCount) ≤
      time i - θ₀ / (A i).flow.scalar (time i) (x i).val)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi)
    (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi)
    {κ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ)
    (hσlim : Tendsto (fun i => σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val)) atTop atTop)
    (hloc : ∀ i (z : ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen),
      riemannianEDistOf ((A i).endpointTerminalLimitMetric
        ((H i).stage (Fin.last (H i).eventCount))).metric (x i) z < ENNReal.ofReal (σ i) →
      ∀ b : ℝ, 0 < b → b ≤ σ i →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric
            (riemannianBallOf ((A i).endpointTerminalLimitMetric
              ((H i).stage (Fin.last (H i).eventCount))).metric z b))
    {eps C1 C2 : ℝ}
    (hW : ∀ i y, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {f : ℕ → ℕ} (hf : StrictMono f) (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (time i) (x i).val)
              (zero_lt_one.trans_le (hQ i))
              ((A i).endpointTerminalLimitMetric
                ((H i).stage (Fin.last (H i).eventCount))).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (W : TopologicalSpace.Opens Pl.M) (xW : ℕ → W) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hQW : ∀ n, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M))
    (hQWlim : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop)
    (hcompactW : ∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW n)
      (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M)))))
    {D : ℝ} (hD : 0 ≤ D)
    (hnear : ∀ m k : ℕ, m ≤ k →
      riemannianEDistOf (scaleMetric ((A (f k)).flow.scalar (time (f k)) (x (f k)).val)
          (zero_lt_one.trans_le (hQ (f k)))
          ((A (f k)).endpointTerminalLimitMetric
            ((H (f k)).stage (Fin.last (H (f k)).eventCount))).metric)
        (x (f k)) (F.partialDiffeomorph k (xW m : Pl.M)) ≤ ENNReal.ofReal D) :
    ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
      Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
      ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (V : TopologicalSpace.Opens P₂.M)
        (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
        (g : ℝ → SmoothRiemannianMetric ThreeModel V),
        g 0 = P₂.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
        (∀ t ∈ Icc (-tau) 0, ∀ y : V, metricAlgebraicCurvatureTensorAt (g t) y ∈
          algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        metricScalarAt P₂.metric P₂.basepoint = 1 ∧
        ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
          (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
          ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
          (∀ᶠ n in atTop, riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
            riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
              (xW (j n)) (r / 4) ⊆ (C n) '' riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ a ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
            ∀ b ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
              |(riemannianEDistOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                (C n a) (C n b)).toReal - (riemannianEDistOf (g 0) a b).toReal| < eta := by
  let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))
  let Q := fun i => (A i).flow.scalar (time i) (x i).val
  have hQpos : ∀ i, 0 < Q i := fun i => zero_lt_one.trans_le (hQ i)
  have hLscalar (i : ℕ) (y : (G i).terminalRegularOpen) :
      metricScalarAt (L i).metric y = (A i).flow.scalar (time i) y.val :=
    metricScalarAt_restrictOpen _ _ _
  obtain ⟨k, hk, hqk, hratio, hcmp⟩ :=
    CheegerGromovCompactness.exists_scalar_rescaled_source_comparison _ f Pl F M hcanonical W xW
      hR₀ hQW hcompactW
  let y : ∀ m, (G (f (k m))).terminalRegularOpen := fun m =>
    F.partialDiffeomorph (k m) (xW m : Pl.M)
  let qk : ℕ → ℝ := fun m => metricScalarAt
    (scaleMetric (Q (f (k m))) (hQpos _) (L (f (k m))).metric) (y m)
  let Q₂ : ℕ → ℝ := fun m => metricScalarAt (L (f (k m))).metric (y m)
  have hQ₂eq (m : ℕ) : Q₂ m = qk m * Q (f (k m)) := by
    change Q₂ m = metricScalarAt (scaleMetric (Q (f (k m))) (hQpos _) (L (f (k m))).metric)
      (y m) * Q (f (k m))
    rw [metricScalarAt_scaleMetric, mul_comm, ← mul_assoc, mul_inv_cancel₀ (hQpos _).ne',
      one_mul]
  have hqk1 (m : ℕ) : 1 ≤ qk m := hqk m
  have hQ₂ (m : ℕ) : 1 ≤ Q₂ m := by
    rw [hQ₂eq]
    nlinarith [hqk1 m, hQ (f (k m))]
  have hQQ₂ (m : ℕ) : Q (f (k m)) ≤ Q₂ m := by
    rw [hQ₂eq]
    nlinarith [hqk1 m, hQpos (f (k m))]
  have hqQ₂ (m : ℕ) : q (f (k m)) ≤ Q₂ m := (hqQ _).trans (hQQ₂ m)
  have hfk : StrictMono (fun m => f (k m)) := hf.comp hk
  have hqklim : Tendsto qk atTop atTop := by
    have hhalf : ∀ᶠ m in atTop, (1 / 2 : ℝ) < qk m / metricScalarAt Pl.metric (xW m : Pl.M) :=
      hratio.eventually (eventually_gt_nhds (by norm_num))
    apply tendsto_atTop_mono' atTop _ ((hQWlim.atTop_div_const (by norm_num : (0 : ℝ) < 2)))
    filter_upwards [hhalf] with m hm
    have hR := (by linarith [hQW m] : (0 : ℝ) < metricScalarAt Pl.metric (xW m : Pl.M))
    have := (lt_div_iff₀ hR).mp hm
    linarith
  have hQ₂lim : Tendsto Q₂ atTop atTop :=
    tendsto_atTop_mono (fun m =>
      (le_mul_of_one_le_right (by linarith [hqk1 m]) (hQ (f (k m)))).trans_eq
      (hQ₂eq m).symm) hqklim
  have hqy : ∀ᶠ m in atTop, q (f (k m)) < (A (f (k m))).flow.scalar (time (f (k m))) (y m).val := by
    filter_upwards [hqklim.eventually_gt_atTop 1] with m hm
    rw [← hLscalar]
    change q (f (k m)) < Q₂ m
    rw [hQ₂eq]
    nlinarith [hqQ (f (k m)), hQpos (f (k m))]
  obtain ⟨m₀, hm₀⟩ := hqy.exists
  obtain ⟨W₀, _⟩ := hW _ _ hm₀
  have hC2 : 1 ≤ C2 := W₀.one_le_comparison_constant
  have hbuffer₂ := RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness
    (fun m => H (f (k m))) (fun m => time (f (k m)))
    (fun m => A (f (k m))) Ctime (fun m => q (f (k m))) y Q₂ hQ₂ (fun m => hLscalar _ _) hC2
    (fun m => hW (f (k m))) hqy hθ₀ (fun m => (hwindow (f (k m))).trans
      (sub_le_sub_left (div_le_div_of_nonneg_left hθ₀.le (hQpos _) (hQQ₂ m)) _))
  -- the local test transported to the second centres `y m`
  let σ' : ℕ → ℝ := fun m => σ (f (k m)) - D / Real.sqrt (Q (f (k m)))
  have hσfk : Tendsto (fun m => σ (f (k m)) * Real.sqrt (Q (f (k m)))) atTop atTop :=
    hσlim.comp hfk.tendsto_atTop
  have hσ' : Tendsto (fun m => σ' m * Real.sqrt (Q₂ m)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-D) hσfk)
    filter_upwards [hσfk.eventually_ge_atTop D] with m hm
    have hsq : 0 < Real.sqrt (Q (f (k m))) := Real.sqrt_pos.mpr (hQpos _)
    have hid : σ' m * Real.sqrt (Q (f (k m))) =
        σ (f (k m)) * Real.sqrt (Q (f (k m))) - D := by
      change (σ (f (k m)) - D / Real.sqrt (Q (f (k m)))) * Real.sqrt (Q (f (k m))) = _
      field_simp
    have hσ'0 : 0 ≤ σ' m := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_neg_of_pos hneg hsq
      linarith
    have hsq₂ : Real.sqrt (Q (f (k m))) ≤ Real.sqrt (Q₂ m) := Real.sqrt_le_sqrt (hQQ₂ m)
    calc σ (f (k m)) * Real.sqrt (Q (f (k m))) + -D = σ' m * Real.sqrt (Q (f (k m))) := by
          rw [hid]; ring
      _ ≤ σ' m * Real.sqrt (Q₂ m) := mul_le_mul_of_nonneg_left hsq₂ hσ'0
  have hloc' : ∀ m (z : (G (f (k m))).terminalRegularOpen),
      riemannianEDistOf (L (f (k m))).metric (y m) z < ENNReal.ofReal (σ' m) →
      ∀ b : ℝ, 0 < b → b ≤ σ' m →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (G (f (k m))).terminalRegularOpen
            (L (f (k m))).metric (riemannianBallOf (L (f (k m))).metric z b) := by
    intro m
    exact local_shift_O3 (L (f (k m))).metric (x (f (k m))) (y m) (hQpos _) hD
      (fun z b => ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (G (f (k m))).terminalRegularOpen
            (L (f (k m))).metric (riemannianBallOf (L (f (k m))).metric z b))
      (hnear m (k m) (hk.id_le m)) (hloc (f (k m)))
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := ThreeModel) W ⟨xW 0⟩
  let Fcmp := fun m => inc.trans (F.partialDiffeomorph (k m))
  let Gcmp := fun m => scaleMetric (qk m) (lt_of_lt_of_le zero_lt_one (hqk1 m))
    (Pl.metric.restrictOpen W)
  have hHeq (m : ℕ) := scaleMetric_mul_eq (L (f (k m))).metric
    (lt_of_lt_of_le zero_lt_one (hqk1 m)) (hQpos (f (k m))) (zero_lt_one.trans_le (hQ₂ m))
    (hQ₂eq m)
  have hcapture (m : ℕ) : riemannianClosedBallOf
      (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m)) (L (f (k m))).metric) (y m) (R₀ / 4) ⊆
        (Fcmp m) '' riemannianClosedBallOf (Gcmp m) (xW m) R₀ := by
    rw [hHeq m]
    exact (hcmp m).2.2.2.1
  have hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ m in atTop,
      ∀ z ∈ riemannianClosedBallOf (Gcmp m) (xW m) R₀, ∀ v : TangentSpace ThreeModel z,
        (1 - eta) * (Gcmp m).inner z v v ≤
          (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m)) (L (f (k m))).metric).inner
            (Fcmp m z) (mfderiv ThreeModel ThreeModel (Fcmp m) z v)
            (mfderiv ThreeModel ThreeModel (Fcmp m) z v) ∧
        (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m)) (L (f (k m))).metric).inner
            (Fcmp m z) (mfderiv ThreeModel ThreeModel (Fcmp m) z v)
            (mfderiv ThreeModel ThreeModel (Fcmp m) z v) ≤ (1 + eta) * (Gcmp m).inner z v v := by
    intro eta heta
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    filter_upwards [hlim.eventually (eventually_lt_nhds heta)] with m hm
    intro z hz v
    rw [hHeq m]
    have hh := (hcmp m).2.2.1 z hz v
    have hg := metric_inner_self_nonneg (Gcmp m) z v
    exact ⟨(mul_le_mul_of_nonneg_right (by linarith : 1 - eta ≤ 1 - 1 / ((m : ℝ) + 2)) hg).trans
      hh.1, hh.2.trans (mul_le_mul_of_nonneg_right
        (by linarith : 1 + 1 / ((m : ℝ) + 2) ≤ 1 + eta) hg)⟩
  obtain ⟨j, hj, P₂, V, hp, hpath, tau, htau, g, hgb, hbase₂, hsol, hnonneg, C, hcenter, r, hr,
      hcpt, hcap, hdist⟩ :=
    exists_nonnegative_local_flow_with_comparison_local_O3
      (fun m => H (f (k m))) (fun m => time (f (k m)))
      (fun m => A (f (k m))) (fun m => hinit _) Ctime (fun m => q (f (k m))) (fun m => hq _)
      (fun m => hderiv _) (fun m => hfinal _) y Q₂ hQ₂ hqQ₂ hQ₂lim hPhi (fun m => hpinch _)
      (fun m => hpinchFinal _) hbuffer₂ (fun m => hs _) (fun m => rfl) σ' hκ hσ'
      (Eventually.of_forall hloc')
      Gcmp xW Fcmp hR₀ (fun m => (hcmp m).2.1) (fun m => rfl) hcapture hBconv
  exact ⟨j, hj, fun n => qk (j n), fun n => lt_of_lt_of_le zero_lt_one (hqk1 (j n)),
    hratio.comp hj.tendsto_atTop, P₂, V, hp, hpath, tau, htau, g, hgb, hsol, hnonneg, hbase₂, C,
    hcenter, r, hr, hcpt, hcap, hdist⟩


private theorem isCompact_closedBall_of_lt_dist_puncture {W : Type*} [MetricSpace W]
    {q : UniformSpace.Completion W} {d : ℝ} (hK : IsCompact (Metric.closedBall q d))
    (hcover : Metric.closedBall q d ⊆
      insert q (range (fun z : W => (z : UniformSpace.Completion W))))
    (x : W) {r : ℝ} (hr : r < dist (x : UniformSpace.Completion W) q)
    (hd : dist (x : UniformSpace.Completion W) q + r ≤ d) :
    IsCompact (Metric.closedBall x r) := by
  let K := Metric.closedBall (x : UniformSpace.Completion W) r
  have hKd : K ⊆ Metric.closedBall q d := by
    intro z hz
    have hz' : dist z (x : UniformSpace.Completion W) ≤ r := hz
    change dist z q ≤ d
    linarith [dist_triangle z (x : UniformSpace.Completion W) q]
  have hKc : IsCompact K := hK.of_isClosed_subset Metric.isClosed_closedBall hKd
  have hKr : K ⊆ range (fun z : W => (z : UniformSpace.Completion W)) := by
    intro z hz
    rcases hcover (hKd hz) with hzq | hzr
    · exfalso
      have hz' : dist z (x : UniformSpace.Completion W) ≤ r := hz
      rw [hzq, dist_comm] at hz'
      linarith
    · exact hzr
  have hpre : (fun z : W => (z : UniformSpace.Completion W)) ⁻¹' K = Metric.closedBall x r := by
    ext z
    simp only [K, mem_preimage, Metric.mem_closedBall, UniformSpace.Completion.dist_eq]
  rw [← hpre]
  exact ((UniformSpace.Completion.isUniformInducing_coe W).isInducing.isCompact_preimage_iff
    hKr).mpr hKc


theorem final_slab_punctured_cone_end_exclusion_local_O3
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (hderiv : ∀ i (j : Fin (H i).eventCount) (y : ((H i).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q i < ((H i).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hwindow : ∀ i, (H i).time (Fin.last (H i).eventCount) ≤
      time i - θ₀ / (A i).flow.scalar (time i) (x i).val)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi)
    (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi)
    {κ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ)
    (hσlim : Tendsto (fun i => σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val)) atTop atTop)
    (hloc : ∀ i (z : ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen),
      riemannianEDistOf ((A i).endpointTerminalLimitMetric
        ((H i).stage (Fin.last (H i).eventCount))).metric (x i) z < ENNReal.ofReal (σ i) →
      ∀ b : ℝ, 0 < b → b ≤ σ i →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric
            (riemannianBallOf ((A i).endpointTerminalLimitMetric
              ((H i).stage (Fin.last (H i).eventCount))).metric z b))
    {eps C1 C2 : ℝ}
    (hW : ∀ i y, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {f : ℕ → ℕ} (hf : StrictMono f) (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (time i) (x i).val)
              (zero_lt_one.trans_le (hQ i))
              ((A i).endpointTerminalLimitMetric
                ((H i).stage (Fin.last (H i).eventCount))).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    {rhoP : ℝ}
    (hradial : ∀ z : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rhoP)
    (hcompactP : ∀ R : ℝ, 0 ≤ R → R < rhoP →
      IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R))
    (W : TopologicalSpace.Opens Pl.M) (hWc : PathConnectedSpace W) :
    let _ : PathConnectedSpace W := hWc
    let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
    let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
    ∀ (qW : UniformSpace.Completion W) (delta : ℝ), 0 < delta →
      IsCompact (Metric.closedBall qW delta) →
      Metric.closedBall qW delta ⊆
        insert qW (range (fun z : W => (z : UniformSpace.Completion W))) →
      Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) →
      ∀ xW : ℕ → W, Tendsto (fun n => (xW n : UniformSpace.Completion W)) atTop (𝓝 qW) →
      Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop →
      ∀ c : ℝ, 0 < c →
      (∀ᶠ n in atTop, c ≤ metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2) →
      (∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B) → False := by
  intro instPath instPseudo instMetric
  let _ : PathConnectedSpace W := instPath
  let _ : PseudoMetricSpace W := instPseudo
  let _ : MetricSpace W := instMetric
  intro qW delta hdelta hK hcover hcone xW hx hQW c hc hlower hupper
  obtain ⟨B, hB⟩ := hupper
  have hd0 : Tendsto (fun n => dist (xW n : UniformSpace.Completion W) qW) atTop (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero).mp hx
  let R₀ := min 1 (Real.sqrt c / 8)
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hR₀ : 0 < R₀ := lt_min one_pos (by positivity)
  have hev : ∀ᶠ n in atTop, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M) ∧
      c ≤ metricScalarAt Pl.metric (xW n : Pl.M) * dist (xW n : UniformSpace.Completion W) qW ^ 2 ∧
      metricScalarAt Pl.metric (xW n : Pl.M) * dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B ∧
      dist (xW n : UniformSpace.Completion W) qW < delta / 2 := by
    filter_upwards [hQW.eventually_ge_atTop 2, hlower, hB,
      hd0.eventually (eventually_lt_nhds (half_pos hdelta))] with n h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let xW' : ℕ → W := fun n => xW (n + N)
  have hN' (n : ℕ) := hN (n + N) (Nat.le_add_left N n)
  have hcompactW : ∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW' n)
      (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M)))) := by
    intro n
    obtain ⟨h1, h2, _, h4⟩ := hN' n
    have hRn : 0 < metricScalarAt Pl.metric (xW' n : Pl.M) := by linarith
    have hsR := Real.sqrt_pos.mpr hRn
    have hdn : 0 < dist (xW' n : UniformSpace.Completion W) qW := by
      rcases (dist_nonneg (x := (xW' n : UniformSpace.Completion W)) (y := qW)).lt_or_eq
        with hlt | heq
      · exact hlt
      · exfalso
        change c ≤ metricScalarAt Pl.metric (xW' n : Pl.M) *
          dist (xW' n : UniformSpace.Completion W) qW ^ 2 at h2
        rw [← heq] at h2
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h2
        linarith
    have hcd : Real.sqrt c ≤ Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M)) *
        dist (xW' n : UniformSpace.Completion W) qW := by
      rw [← Real.sqrt_sq hdn.le, ← Real.sqrt_mul hRn.le]
      exact Real.sqrt_le_sqrt h2
    have hrad : 4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M)) ≤
        dist (xW' n : UniformSpace.Completion W) qW / 2 := by
      rw [div_le_iff₀ hsR]
      have hR8 : R₀ ≤ Real.sqrt c / 8 := min_le_right _ _
      nlinarith
    have hball : riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW' n)
        (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M))) =
          Metric.closedBall (xW' n)
            (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M))) := by
      ext z
      change edist (xW' n) z ≤ ENNReal.ofReal _ ↔ dist z (xW' n) ≤ _
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity), dist_comm]
    rw [hball]
    have h4' : dist (xW' n : UniformSpace.Completion W) qW < delta / 2 := h4
    exact isCompact_closedBall_of_lt_dist_puncture hK hcover (xW' n) (by linarith) (by linarith)
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW' n : Pl.M)) atTop atTop :=
    hQW.comp (tendsto_add_atTop_nat N)
  -- re-index the first convergence so that the second centres stay near the first ones
  obtain ⟨φ, hφ, hφnear⟩ := exists_reindex_near_O3 F M hcanonical hradial hcompactP
    (fun m => (xW' m : Pl.M))
  have hcan' (n : ℕ) : (M.compSubseq φ hφ).domain n =
      CanonicalMetricCompactness.canonicalSourceData (F.compSubseq φ hφ) n := by
    change (M.domain (φ n)).compSubseq φ hφ n = _
    rw [hcanonical (φ n)]
    rfl
  have hrhoP : 0 ≤ rhoP := by
    have h := hradial Pl.basepoint
    exact (ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le h)).le
  have hnear : ∀ m k : ℕ, m ≤ k →
      riemannianEDistOf (scaleMetric ((A (f (φ k))).flow.scalar (time (f (φ k)))
          (x (f (φ k))).val) (zero_lt_one.trans_le (hQ (f (φ k))))
          ((A (f (φ k))).endpointTerminalLimitMetric
            ((H (f (φ k))).stage (Fin.last (H (f (φ k))).eventCount))).metric)
        (x (f (φ k))) ((F.compSubseq φ hφ).partialDiffeomorph k (xW' m : Pl.M)) ≤
        ENNReal.ofReal (2 * rhoP) :=
    fun m k hmk => hφnear m (φ k) (hφ.monotone hmk)
  obtain ⟨j, hj, A₂, hA₂, hratio, P₂, V, hp, hpath, tau, htau, g, hgb, hsol, hnonneg, hbase₂,
      C, hcenter, r, hr, hcpt, hcap, hdist⟩ :=
    exists_local_backward_limit_local_O3
      H time A
      hinit hs Ctime q hq hderiv hfinal x hQ hqQ hθ₀ hwindow hPhi hpinch hpinchFinal σ hκ
      hσlim hloc hW (hf.comp hφ) Pl (F.compSubseq φ hφ) (M.compSubseq φ hφ) hcan' W xW' hR₀
      (fun n => (hN' n).1) hQW' hcompactW (by positivity : (0 : ℝ) ≤ 2 * rhoP) hnear
  let _ : PseudoMetricSpace V := (P₂.metric.restrictOpen V).toPseudoMetricSpace
  let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)
  let S : SolutionOn (I := ThreeModel) (M := V)
      (RealTimeInterval.closed (-tau) 0 (by linarith)) := { base.metric := g }
  have hsec : ∀ t ∈ Icc (-tau) 0, SecLower (S.base.metric t) 0 univ := by
    intro t ht z _ v w
    have h := (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
      (g t) z (by simp [ThreeSpace])).mp (hnonneg t ht z) v w
    have hslots : (fun i => ![v, w, w, v] i) = vec4 (I := ThreeModel) v w w v := by
      funext i
      fin_cases i <;> rfl
    simpa only [S, zero_mul, metricRm04StandardAt_apply, hslots] using h
  have hmetric0 : ∀ a b : V, edist a b = riemannianEDistOf (S.base.metric 0) a b := by
    intro a b
    change edist a b = riemannianEDistOf (g 0) a b
    rw [hgb]
    rfl
  let p : V := ⟨P₂.basepoint, hp⟩
  have hscalar0 : metricScalarAt (S.base.metric 0) p ≠ 0 := by
    change metricScalarAt (g 0) p ≠ 0
    rw [hgb, metricScalarAt_restrictOpen, hbase₂]
    norm_num
  have hRj : Tendsto (fun n => metricScalarAt Pl.metric (xW' (j n) : Pl.M)) atTop atTop :=
    hQW'.comp hj.tendsto_atTop
  have hcmp : ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW' (j n) : Pl.M) / 2 ≤ A₂ n ∧
      A₂ n ≤ 2 * metricScalarAt Pl.metric (xW' (j n) : Pl.M) := by
    filter_upwards [hratio.eventually (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2))] with n hn
    have hRpos : 0 < metricScalarAt Pl.metric (xW' (j n) : Pl.M) := by linarith [(hN' (j n)).1]
    have hl := (lt_div_iff₀ hRpos).mp hn.1
    have hu := (div_lt_iff₀ hRpos).mp hn.2
    exact ⟨by linarith, hu.le⟩
  have hAtop : Tendsto A₂ atTop atTop :=
    tendsto_atTop_mono' atTop (hcmp.mono fun _ h => h.1)
      (hRj.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  let rho := fun n => 1 / Real.sqrt (A₂ n)
  have hrho (n : ℕ) : 0 < rho n := one_div_pos.mpr (Real.sqrt_pos.mpr (hA₂ n))
  have hrho0 : Tendsto rho atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hAtop)
  have hballP : riemannianClosedBallOf (g 0) p r = Metric.closedBall p r := by
    rw [hgb]
    ext z
    change edist p z ≤ ENNReal.ofReal r ↔ dist z p ≤ r
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hr.le, dist_comm]
  have hballH (n : ℕ) : riemannianClosedBallOf
      (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W)) (xW' (j n)) (r / 4) =
        Metric.closedBall (xW' (j n)) (r / 4 * rho n) := by
    have hscale : r / 4 = Real.sqrt (A₂ n) * (r / 4 * rho n) := by
      dsimp only [rho]
      field_simp [(Real.sqrt_pos.mpr (hA₂ n)).ne']
    conv_lhs => rw [hscale]
    rw [riemannianClosedBallOf_scaleMetric]
    ext z
    change edist (xW' (j n)) z ≤ ENNReal.ofReal (r / 4 * rho n) ↔ dist z (xW' (j n)) ≤ _
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by have := hrho n; positivity), dist_comm]
  have hdistH (n : ℕ) (a b : W) : (riemannianEDistOf
      (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W)) a b).toReal = dist a b / rho n := by
    rw [edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    change Real.sqrt (A₂ n) * (edist a b).toReal = _
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    dsimp only [rho]
    rw [one_div, div_inv_eq_mul, mul_comm]
  have hdistP (a b : V) : (riemannianEDistOf (g 0) a b).toReal = dist a b := by
    rw [hgb]
    change (edist a b).toReal = _
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  apply solution_not_rescaled_cone_limit (M := V) htau S hsol hmetric0 hsec p hscalar0
    hcone.some (fun n => xW' (j n)) (fun n z => C n z) rho hrho hrho0 hcenter hr
    (lower := Real.sqrt (c / 2)) (B := Real.sqrt (max 1 (2 * B)) + 1)
    (Real.sqrt_pos.mpr (half_pos hc)) (hballP ▸ hcpt)
  · filter_upwards [hcmp] with n hn
    obtain ⟨_, h2, h3, _⟩ := hN' (j n)
    set d := dist ((xW' (j n) : W) : UniformSpace.Completion W) qW
    have hd0 : 0 ≤ d := dist_nonneg
    have hdiv : d / rho n = Real.sqrt (A₂ n) * d := by
      dsimp only [rho]
      rw [one_div, div_inv_eq_mul, mul_comm]
    have hsq : (Real.sqrt (A₂ n) * d) ^ 2 = A₂ n * d ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hA₂ n).le]
    have hz : 0 ≤ Real.sqrt (A₂ n) * d := mul_nonneg (Real.sqrt_nonneg _) hd0
    change c ≤ metricScalarAt Pl.metric (xW' (j n) : Pl.M) * d ^ 2 at h2
    change metricScalarAt Pl.metric (xW' (j n) : Pl.M) * d ^ 2 ≤ B at h3
    rw [hdiv]
    constructor
    · have hlow : c / 2 ≤ (Real.sqrt (A₂ n) * d) ^ 2 := by
        rw [hsq]
        have := mul_le_mul_of_nonneg_right hn.1 (sq_nonneg d)
        nlinarith
      calc Real.sqrt (c / 2) ≤ Real.sqrt ((Real.sqrt (A₂ n) * d) ^ 2) := Real.sqrt_le_sqrt hlow
        _ = Real.sqrt (A₂ n) * d := Real.sqrt_sq hz
    · have hup : (Real.sqrt (A₂ n) * d) ^ 2 ≤ max 1 (2 * B) := by
        rw [hsq]
        have := mul_le_mul_of_nonneg_right hn.2 (sq_nonneg d)
        exact (by nlinarith : A₂ n * d ^ 2 ≤ 2 * B).trans (le_max_right _ _)
      have := Real.le_sqrt_of_sq_le hup
      linarith
  · filter_upwards [hcap] with n hn
    rw [← hballH n, ← hballP]
    exact hn.2
  · intro eta heta
    filter_upwards [hdist eta heta] with n hn
    intro a ha b hb
    have h := hn a (hballP ▸ ha) b (hballP ▸ hb)
    rw [hdistH, hdistP] at h
    exact h


end GC.LongTime.Ch12
