import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcanBackward_O67

/-!
# CH12-O67, group 2: the K-can tree theorem (no local volume test `hloc`)

`final_slab_punctured_cone_end_exclusion_of_trace_chains_kcan_O67` and
`exists_normalized_scalar_bound_of_chain_traces_kcan_O67` are the O3 theorems of
`MicroGlueTracedLocal` (l.678, l.940) with `(σ, hσlim, hloc)` replaced by the centre volume `hvx`
(first blow-up, `exists_pointed_convergence_at_scalar_escape_of_traced_buffer_kcan_O23`) and the
K-can second-blow-up volume `hvw` (`KcanBackward_O67`).  Proofs otherwise verbatim.
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

private local instance pointedLimitRegular_O67b (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

private theorem isCompact_closedBall_of_lt_dist_puncture_O67 {W : Type*} [MetricSpace W]
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


theorem final_slab_punctured_cone_end_exclusion_of_trace_chains_kcan_O67
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
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi)
    (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi)
    {κ a₀ Kv : ℝ} (hκ : 0 < κ) (ha₀ : 0 < a₀) (hKv : 0 ≤ Kv)
    (hvw : ∀ i (w : ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen),
      riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
          (zero_lt_one.trans_le (hQ i))
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
        (x i) w < ⊤ →
      ∀ hw : Kv * (A i).flow.scalar (time i) (x i).val < metricScalarAt
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric w,
      ∀ b : ℝ, 0 < b → b ≤ a₀ →
        ENNReal.ofReal (κ * b ^ 3) ≤
          riemannianVolumeMeasure ThreeModel
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            (scaleMetric (metricScalarAt ((A i).endpointTerminalLimitMetric
                ((H i).stage (Fin.last (H i).eventCount))).metric w)
              ((mul_nonneg hKv (zero_le_one.trans (hQ i))).trans_lt hw)
              ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
            (riemannianBallOf (scaleMetric (metricScalarAt ((A i).endpointTerminalLimitMetric
                ((H i).stage (Fin.last (H i).eventCount))).metric w)
              ((mul_nonneg hKv (zero_le_one.trans (hQ i))).trans_lt hw)
              ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
              w b))
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
      ∀ θ₂ : ℝ, 0 < θ₂ → (∀ m, ∀ᶠ n in atTop, ∃ first : Fin ((H (f n)).eventCount + 1),
        (H (f n)).time first ≤ time (f n) - θ₂ /
          (A (f n)).flow.scalar (time (f n)) (F.map n (xW m : Pl.M)).val ∧
        ∀ z ∈ riemannianBallOf ((A (f n)).flow.base.metric (time (f n)))
          (F.map n (xW m : Pl.M)).val
          (Real.sqrt ((A (f n)).flow.scalar (time (f n))
            (F.map n (xW m : Pl.M)).val))⁻¹,
          Nonempty (BackwardPointTrace (H (f n)).toHistory first
            (Fin.last (H (f n)).eventCount) (Fin.le_last first) z)) →
      ∀ c : ℝ, 0 < c →
      (∀ᶠ n in atTop, c ≤ metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2) →
      (∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B) → False := by
  intro instPath instPseudo instMetric
  let _ : PathConnectedSpace W := instPath
  let _ : PseudoMetricSpace W := instPseudo
  let _ : MetricSpace W := instMetric
  intro qW delta hdelta hK hcover hcone xW hx hQW θ₂ hθ₂ htrace c hc hlower hupper
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
    exact isCompact_closedBall_of_lt_dist_puncture_O67 hK hcover (xW' n) (by linarith) (by linarith)
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW' n : Pl.M)) atTop atTop :=
    hQW.comp (tendsto_add_atTop_nat N)
  obtain ⟨φ, -, hφnear⟩ := exists_reindex_near_O3 F M hcanonical hradial hcompactP
    (fun m => (xW' m : Pl.M))
  have hrhoP : 0 ≤ rhoP :=
    (ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le (hradial Pl.basepoint))).le
  obtain ⟨j, hj, A₂, hA₂, hratio, P₂, V, hp, hpath, tau, htau, g, hgb, hsol, hnonneg, hbase₂,
      C, hcenter, r, hr, hcpt, hcap, hdist⟩ :=
    exists_local_backward_limit_at_final_slab_end_of_eventual_traces_kcan_O67
      H time A
      hinit hs Ctime q hq hderiv hfinal x hQ hqQ hPhi hpinch hpinchFinal hκ ha₀
      hKv hvw hW hf Pl F M hcanonical W xW' hR₀ (fun n => (hN' n).1) hQW' hcompactW
      hθ₂ (fun m => htrace (m + N)) (by positivity : (0 : ℝ) ≤ 2 * rhoP)
      (fun m => eventually_atTop.mpr ⟨φ m, fun n hn => hφnear m n hn⟩)
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



theorem exists_normalized_scalar_bound_of_chain_traces_kcan_O67
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime Cgrad : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (hderiv : ∀ i (j : Fin (H i).eventCount) (y : ((H i).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q i < ((H i).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (hgradient : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow t y v| ≤
          Cgrad * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
            Real.sqrt (((A i).flow.base.metric t).inner y v v))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    (hQlim : Tendsto (fun i => (A i).flow.scalar (time i) (x i).val) atTop atTop)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi)
    (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi)
    {κ a₀ Kv : ℝ} (hκ : 0 < κ) (ha₀ : 0 < a₀)
    (hvx : ∀ i, ∀ b : ℝ, 0 < b → b ≤ a₀ →
      ENNReal.ofReal (κ * b ^ 3) ≤
        riemannianVolumeMeasure ThreeModel
          ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
          (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
            ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
          (riemannianBallOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
            (zero_lt_one.trans_le (hQ i))
            ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
            (x i) b))
    (hKv : 0 ≤ Kv)
    (hvw : ∀ i (w : ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen),
      riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
          (zero_lt_one.trans_le (hQ i))
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
        (x i) w < ⊤ →
      ∀ hw : Kv * (A i).flow.scalar (time i) (x i).val < metricScalarAt
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric w,
      ∀ b : ℝ, 0 < b → b ≤ a₀ →
        ENNReal.ofReal (κ * b ^ 3) ≤
          riemannianVolumeMeasure ThreeModel
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            (scaleMetric (metricScalarAt ((A i).endpointTerminalLimitMetric
                ((H i).stage (Fin.last (H i).eventCount))).metric w)
              ((mul_nonneg hKv (zero_le_one.trans (hQ i))).trans_lt hw)
              ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
            (riemannianBallOf (scaleMetric (metricScalarAt ((A i).endpointTerminalLimitMetric
                ((H i).stage (Fin.last (H i).eventCount))).metric w)
              ((mul_nonneg hKv (zero_le_one.trans (hQ i))).trans_lt hw)
              ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
              w b))
    {eps C1 C2 : ℝ}
    (heps : 13000 * (13000 * eps) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64))
    (hW : ∀ i y, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    (htime : Tendsto (fun i => (A i).flow.scalar (time i) (x i).val * time i) atTop atTop)
    {Kc lam θ : ℝ} (hlam : 0 ≤ lam) (hθ : 0 < θ) (D : ℕ → ℝ) (hD : Tendsto D atTop atTop)
    (htrace : ∀ i (N : ℕ) (p : ℕ → ((H i).stage (Fin.last (H i).eventCount)).Carrier)
      (δ : ℕ → ℝ) (M τ : ℝ), p 0 = (x i).val → (∀ k ≤ N, 0 < δ k) →
      (∀ k < N, p (k + 1) ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k)) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k),
        (A i).flow.scalar (time i) z ≤ M) →
      Kc * (A i).flow.scalar (time i) (x i).val ≤ M → 1 ≤ M → 0 ≤ τ → τ ≤ time i →
      (Ctime : ℝ) * M * τ ≤ 1 / 2 → 4 * M * τ ≤ θ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0) * M) * τ) *
          (lam / Real.sqrt ((A i).flow.scalar (time i) (x i).val) +
            ∑ k ∈ Finset.range (N + 1), δ k) < D i →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf ((A i).flow.base.metric (time i)) (p k) (δ k),
        ∃ first : Fin ((H i).eventCount + 1), (H i).time first ≤ time i - τ ∧
          Nonempty (BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
            (Fin.le_last first) z)) :
    ∀ R : ℝ, 0 < R → ∃ B : ℝ, ∀ᶠ i in atTop,
      ∀ y : ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen,
        riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
          (zero_lt_one.trans_le (hQ i))
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
          (x i) y < ENNReal.ofReal R →
        metricScalarAt
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric y /
            (A i).flow.scalar (time i) (x i).val ≤ B := by
  intro R hR
  by_contra hB
  have hL1 := exists_pointed_convergence_at_scalar_escape_of_traced_buffer_kcan_O23
    H time A hinit hs Ctime Cgrad q hq hderiv hfinal hgradient x hQ hqQ
    (RetainedCoreHistory.traced_buffer_of_chain_traces H time A x hQ hθ D hD htime htrace)
    ⟨R, hR, hB⟩ Phi hPhi hpinch hpinchFinal κ a₀ hκ ha₀ hvx
  dsimp only at hL1
  obtain ⟨rho, hrho, ind, hind, z, f, hf, r, hr, hrlim, Pl, F₀, M, _, hcan, hradial, hcompact,
      hcapture, hmetric, hfinite, hdist, hescape⟩ := hL1
  let F := PointedRiemannianConvergenceMaps.liftTargetOpen
    (S := { obj := fun i =>
          { M := ((A (ind i)).restrictIncoming le_rfl (A (ind i)).lt le_rfl).terminalRegularOpen
            basepoint := x (ind i)
            metric := scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
              (zero_lt_one.trans_le (hQ (ind i)))
              ((A (ind i)).endpointTerminalLimitMetric
                ((H (ind i)).stage (Fin.last (H (ind i)).eventCount))).metric } })
    (fun i => connectedComponentOpen (I := ThreeModel) (x (ind i)))
    (fun i => (mem_connectedComponent : x (ind i) ∈
      connectedComponentOpen (I := ThreeModel) (x (ind i)))) F₀
  have halpha : (0 : ℝ) < 1 / 4000000 := by norm_num
  obtain ⟨g, hg, hg0, hblow, hnecks⟩ :=
    exists_isometric_ray_with_spatialNecks_of_bounded_threshold
    (fun i => (H (ind i)).stage (Fin.last (H (ind i)).eventCount))
    (fun i => (H (ind i)).time (Fin.last (H (ind i)).eventCount)) (fun i => time (ind i))
    (fun i => A (ind i)) Ctime Cgrad (fun i => q (ind i)) (fun i => hfinal (ind i))
    (fun i => hgradient (ind i)) (fun i => x (ind i)) (fun i => hQ (ind i))
    (fun i => hqQ (ind i)) halpha (by norm_num) heps
    (fun i => hW (ind i)) hrho f hf r (fun n => (hr n).1) hrlim Pl F M hcan hradial hcompact
    hcapture (fun ε hε => (hmetric ε hε).mono fun n hn y hy v => (hn y hy v).1)
    (fun n => z (f n)) hfinite hdist hescape
  have hsec := metricRm04StandardAt_nonneg_of_normalized_terminal_pinching
    (fun i => (H (ind i)).stage (Fin.last (H (ind i)).eventCount))
    (fun i => (H (ind i)).time (Fin.last (H (ind i)).eventCount)) (fun i => time (ind i))
    (fun i => A (ind i)) (fun i => x (ind i)) (fun i => hQ (ind i)) hPhi
    (fun i => hpinchFinal (ind i)) Pl F M hcan (hQlim.comp (hind.comp hf).tendsto_atTop)
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  have hfin : ∀ a b : Pl.M, edist a b ≠ ⊤ := by
    intro a b
    apply ne_top_of_le_ne_top _ (edist_triangle_left a b Pl.basepoint)
    exact ENNReal.add_ne_top.mpr ⟨(hradial a).ne_top, (hradial b).ne_top⟩
  let _ : MetricSpace Pl.M := EMetricSpace.toMetricSpace hfin
  obtain ⟨qc, hqc, _⟩ :=
    DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry hrho hg
  obtain ⟨W, hWc, hrest⟩ := exists_punctured_cone_end_of_spatial_necks_with_ray_scalar_bound
    Pl.metric (fun _ _ => rfl) hrho halpha (by norm_num) hsec g hg hblow qc hqc hnecks
  let _ : PathConnectedSpace W := hWc
  let mW : MetricSpace W :=
    let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
    MetricSpace.ofT0PseudoMetricSpace W
  let _ : MetricSpace W := mW
  let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
  let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
  let eW : PseudoEMetricSpace W :=
    @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
  let _ : WeakPseudoEMetricSpace W :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
  obtain ⟨qW, delta, hdelta, _, _, hK, hcover, xW, times, hux, _, hxW, _, hQW, hlowerW, hupperW,
    hcone, Kr, hKr1, hKr⟩ := hrest
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop := by
    simpa only [metricScalarAt_restrictOpen] using hQW
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (hKr.and (hQW'.eventually_ge_atTop 3))
  have hlower' : ∀ᶠ n in atTop, ((2 * (1 / 4000000 : ℝ))⁻¹) ^ 2 / 8 ≤
      metricScalarAt Pl.metric (xW (n + m₀) : Pl.M) *
        dist (xW (n + m₀) : UniformSpace.Completion W) qW ^ 2 :=
    Eventually.of_forall fun n => by
      simpa only [metricScalarAt_restrictOpen] using hlowerW (n + m₀)
  have hupper' : ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW (n + m₀) : Pl.M) *
      dist (xW (n + m₀) : UniformSpace.Completion W) qW ^ 2 ≤ B := by
    obtain ⟨B, _, hB⟩ := hupperW
    have hB' : ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
      simpa only [metricScalarAt_restrictOpen] using hB
    exact ⟨B, (tendsto_add_atTop_nat m₀).eventually hB'⟩
  have hux' (m : ℕ) : (xW (m + m₀) : Pl.M) = g (times (m + m₀)) := hux (m + m₀)
  obtain ⟨θ₂, hθ₂, htr₂⟩ := RetainedCoreHistory.eventually_second_level_traces_of_chain_traces
    (fun i => H (ind i)) (fun i => time (ind i)) (fun i => A (ind i))
    Cgrad (fun i => q (ind i)) (fun i => hgradient (ind i)) (fun i => x (ind i))
    (fun i => hQ (ind i)) (fun i => hqQ (ind i)) (fun i => hW (ind i)) hlam hθ hPhi
    (fun i => D (ind i)) (hD.comp hind.tendsto_atTop) (htime.comp hind.tendsto_atTop)
    (fun i => htrace (ind i)) hf Pl F M hcan g (fun s t => (hg.edist_eq s t : _))
    ⟨0, le_rfl, hrho⟩ rfl hg0 (fun m => times (m + m₀)) (fun m => (xW (m + m₀) : Pl.M)) hux'
    hKr1 (fun m => by
      have h := (hm₀ (m + m₀) (Nat.le_add_left _ _)).1
      intro s hs
      rw [← hux (m + m₀)] at h ⊢
      exact h s hs)
    (fun m => by
      rw [← hux (m + m₀)]
      exact (hm₀ (m + m₀) (Nat.le_add_left _ _)).2)
  exact final_slab_punctured_cone_end_exclusion_of_trace_chains_kcan_O67
    (fun i => H (ind i)) (fun i => time (ind i)) (fun i => A (ind i)) (fun i => hinit (ind i))
    (fun i => hs (ind i)) Ctime (fun i => q (ind i)) (fun i => hq _) (fun i => hderiv (ind i))
    (fun i => hfinal (ind i)) (fun i => x (ind i)) (fun i => hQ _) (fun i => hqQ _)
    hPhi (fun i => hpinch _)
    (fun i => hpinchFinal _) hκ ha₀ hKv
    (fun i => hvw (ind i)) (fun i => hW (ind i)) hf Pl F M hcan hradial hcompact W hWc qW delta
    hdelta hK
    hcover hcone (fun n => xW (n + m₀)) (hxW.comp (tendsto_add_atTop_nat m₀))
    (hQW'.comp (tendsto_add_atTop_nat m₀)) θ₂ hθ₂ htr₂ _ (by norm_num) hlower' hupper'


end GC.LongTime.Ch12
