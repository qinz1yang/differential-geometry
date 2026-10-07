import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceTracedSecondLevel_P6L

/-!
# L6-B：`BoundedCurvatureAtDistanceTracedSecondLevel:170` 的局部化（`_P6L`）

原 `RetainedCoreHistory.eventually_second_level_traces_of_chain_traces`
（`ST/BoundedCurvatureAtDistanceTracedSecondLevel.lean:170`，序列形）。改动（rev1a C2.1/C2.3）：
* 区域 `U : ∀ i, Set (last stage).Carrier` 放 `hgradient` 前；`hgradient`、`hW` 限于 `U i`。
* 先验半径 `Rad` 与 `hU : ∀ i, ∀ y ∈ B_{Q i·L i}(x i, Rad), y.val ∈ U i`（放 `hqQ` 后），
  余量 `hRad : rho + 2 ≤ Rad`（放 `hg` 后；`rho` = 极限 ray 的长度）。
* 新证（非机械）：链点 `F.map n (g (sk k))`（`k ≤ N`）eventually 满足
  `d_{Q·L}(x (f n), ·) < rho`（`eventually_riemannianEDistOf_map_lt_of_metric_convergence`，
  极限端 `d(g s0, g (sk k)) = sk k < rho`）；再由三角不等式与 `√Q·4·r₀/√(2(K+1)LQ) ≤ 4·r₀ ≤ 1/5`
  得 `hchainU`（链点小球 ⊆ `U`）、`hendU`（终点 ∈ `U`），喂给 TSL:67_P6L。
私有 TSL:42/53/150 复制为 `_P6L`；其余证明体照抄；结论逐字。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem exists_ray_chain_times_P6L {T ρ : ℝ} (hρ : 0 < ρ) :
    ∃ N : ℕ, 0 < N ∧ T / N < ρ := by
  refine ⟨⌈T / ρ⌉₊ + 1, Nat.succ_pos _, ?_⟩
  have hN : T / ρ < (⌈T / ρ⌉₊ + 1 : ℕ) := by
    push_cast
    exact (Nat.le_ceil _).trans_lt (lt_add_one _)
  have hNpos : (0 : ℝ) < (⌈T / ρ⌉₊ + 1 : ℕ) := by positivity
  rw [div_lt_iff₀ hNpos]
  rw [div_lt_iff₀ hρ] at hN
  linarith

private theorem isCompact_image_Iic_of_ray_P6L {X : Type*} [TopologicalSpace X] {rho : ℝ}
    (g : C(Ico 0 rho, X)) (T : Ico 0 rho) :
    IsCompact (g '' {s : Ico 0 rho | (s : ℝ) ≤ T}) := by
  refine IsCompact.image ?_ g.continuous
  have hcl : {s : Ico 0 rho | (s : ℝ) ≤ T} =
      (Subtype.val : Ico 0 rho → ℝ) ⁻¹' Icc 0 (T : ℝ) := by
    ext s
    simp only [mem_ofPred_eq, mem_preimage, mem_Icc]
    exact ⟨fun h => ⟨s.2.1, h⟩, fun h => h.2⟩
  rw [hcl]
  apply (Topology.IsInducing.subtypeVal).isCompact_preimage' isCompact_Icc
  intro r hr
  exact ⟨⟨r, hr.1, hr.2.trans_lt T.2.2⟩, rfl⟩

private theorem ray_chain_step_P6L {rho T : ℝ} {N : ℕ} (hN : 0 < N) (hT : 0 ≤ T)
    {ρ : ℝ} (hNT : T / N < ρ) (sk : ℕ → Ico 0 rho)
    (hsk : ∀ k, (sk k : ℝ) = min (k * T / N) T) (k : ℕ) (hk : k < N) :
    edist (sk k) (sk (k + 1)) < ENNReal.ofReal ρ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (k : ℝ) * T / N ≤ T := by
    rw [div_le_iff₀ hNr]
    have : (k : ℝ) ≤ N := by exact_mod_cast hk.le
    nlinarith
  have h2 : ((k + 1 : ℕ) : ℝ) * T / N ≤ T := by
    rw [div_le_iff₀ hNr]
    have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
    nlinarith
  rw [edist_dist, Subtype.dist_eq, Real.dist_eq, hsk, hsk, min_eq_left h1, min_eq_left h2]
  have heq : (k : ℝ) * T / N - ((k + 1 : ℕ) : ℝ) * T / N = -(T / N) := by
    push_cast
    ring
  rw [heq, abs_neg, abs_of_nonneg (by positivity)]
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) hNT)).mpr hNT

/-- 半径余量（rev1a C2.3）：链点小球半径 `4·c/√(2(K+1)LQ)` 乘 `√Q` 后 `≤ 4·c ≤ 2`。 -/
private theorem sqrt_mul_chain_radius_le_P6L {Q K L c : ℝ} (hQ : 0 < Q) (hK : 1 ≤ K)
    (hL : 3 ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 20) :
    Real.sqrt Q * (2 * (2 * (c / Real.sqrt (2 * ((K + 1) * L * Q))))) ≤ 2 := by
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have h1 : 1 ≤ 2 * ((K + 1) * L) := by nlinarith
  have hle : Real.sqrt Q ≤ Real.sqrt (2 * ((K + 1) * L * Q)) :=
    Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_right h1 hQ.le])
  have hpos : 0 < Real.sqrt (2 * ((K + 1) * L * Q)) := hsQ.trans_le hle
  have h2 : Real.sqrt Q * (c / Real.sqrt (2 * ((K + 1) * L * Q))) ≤ c := by
    rw [mul_div_assoc', div_le_iff₀ hpos]
    nlinarith
  nlinarith

/-- 成员关系桥（rev1a C2.1/C2.3）：中心 `c` 满足 `d_{Q·L}(x, c) < rho`、`rho + √Q·r ≤ Rad`，且
`B_{Q·L}(x, Rad)` 的点都在 `U` ⇒ 端点度量球 `B_s(c, r) ⊆ U`（`terminalRegularRegion = univ`）。 -/
private theorem terminal_ball_subset_of_scaled_dist_lt_P6L {P : OrientedThreeStage.{u}}
    {a s : ℝ} (A : P.ClosedSlab a s) {Q : ℝ} (hQ : 0 < Q)
    (x c : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) (U : Set P.Carrier)
    {rho Rad r : ℝ} (hrho : 0 ≤ rho) (hr0 : 0 ≤ r)
    (hc : riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x c <
      ENNReal.ofReal rho)
    (hr : rho + Real.sqrt Q * r ≤ Rad)
    (hU : ∀ y ∈ riemannianBallOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x
      Rad, y.val ∈ U) :
    riemannianBallOf (A.flow.base.metric s) c.val r ⊆ U := by
  intro w hw
  have hmem : w ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen := by
    change w ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
    rw [A.terminalRegularRegion_eq_univ _]
    trivial
  apply hU ⟨w, hmem⟩
  change riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x
    ⟨w, hmem⟩ < ENNReal.ofReal Rad
  have hw' : riemannianEDistOf (A.flow.base.metric s) c.val w < ENNReal.ofReal r := hw
  have hsq : ENNReal.ofReal (Real.sqrt Q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne'
  have hcw : riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) c
      ⟨w, hmem⟩ < ENNReal.ofReal (Real.sqrt Q * r) := by
    rw [DifferentialGeometry.edistOf_scale, A.riemannianEDistOf_endpointTerminalLimitMetric,
      ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
    have h := ENNReal.mul_lt_mul_left hsq ENNReal.ofReal_ne_top hw'
    rwa [mul_comm, mul_comm (ENNReal.ofReal r)] at h
  calc riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x ⟨w, hmem⟩
      ≤ riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x c +
          riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) c
            ⟨w, hmem⟩ := riemannianEDistOf_triangle _ _ _ _
    _ < ENNReal.ofReal rho + ENNReal.ofReal (Real.sqrt Q * r) := ENNReal.add_lt_add hc hcw
    _ = ENNReal.ofReal (rho + Real.sqrt Q * r) :=
        (ENNReal.ofReal_add hrho (mul_nonneg (Real.sqrt_nonneg Q) hr0)).symm
    _ ≤ ENNReal.ofReal Rad := ENNReal.ofReal_le_ofReal hr

/-- **`_P6L`（L6-B，供 TP:97_P6L）**：原
`RetainedCoreHistory.eventually_second_level_traces_of_chain_traces`（TSL:170）。
改动见文件头（`U`、`Rad`、`hU`、`hRad`；`hgradient`、`hW` 限于 `U i`）。结论逐字。 -/
theorem RetainedCoreHistory.eventually_second_level_traces_of_chain_traces_P6L
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (Cgrad : ℝ≥0) (q : ℕ → ℝ)
    (U : ∀ i, Set ((H i).stage (Fin.last (H i).eventCount)).Carrier)
    (hgradient : ∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |scalarDifferential ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow t y v| ≤
          Cgrad * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
            Real.sqrt (((A i).flow.base.metric t).inner y v v))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    (Rad : ℝ) (hU : ∀ i, ∀ y ∈ riemannianBallOf
      (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
        ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
      (x i) Rad, y.val ∈ U i)
    {eps C1 C2 : ℝ}
    (hW : ∀ i, ∀ y ∈ U i, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {Kc lam θ : ℝ} (hlam : 0 ≤ lam) (hθ : 0 < θ) {Ctime : ℝ≥0} {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi) (D : ℕ → ℝ) (hD : Tendsto D atTop atTop)
    (htime : Tendsto (fun i => (A i).flow.scalar (time i) (x i).val * time i) atTop atTop)
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
            (Fin.le_last first) z))
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
    {rho : ℝ} (g : C(Ico 0 rho, Pl.M))
    (hg : ∀ s t : Ico 0 rho, riemannianEDistOf Pl.metric (g s) (g t) = edist s t)
    (hRad : rho + 2 ≤ Rad)
    (s0 : Ico 0 rho) (hs0 : (s0 : ℝ) = 0) (hg0 : g s0 = Pl.basepoint)
    (times : ℕ → Ico 0 rho) (xs : ℕ → Pl.M) (hxs : ∀ m, xs m = g (times m)) {K : ℝ}
    (hK1 : 1 ≤ K)
    (hK : ∀ m, ∀ s : Ico 0 rho, (s : ℝ) ≤ times m →
      metricScalarAt Pl.metric (g s) ≤ K * metricScalarAt Pl.metric (g (times m)))
    (h3 : ∀ m, 3 ≤ metricScalarAt Pl.metric (g (times m))) :
    ∃ θ₂ : ℝ, 0 < θ₂ ∧ ∀ m, ∀ᶠ n in atTop, ∃ first : Fin ((H (f n)).eventCount + 1),
      (H (f n)).time first ≤ time (f n) - θ₂ /
        (A (f n)).flow.scalar (time (f n)) (F.map n (xs m)).val ∧
      ∀ z ∈ riemannianBallOf ((A (f n)).flow.base.metric (time (f n)))
        (F.map n (xs m)).val
        (Real.sqrt ((A (f n)).flow.scalar (time (f n)) (F.map n (xs m)).val))⁻¹,
        Nonempty (BackwardPointTrace (H (f n)).toHistory first
          (Fin.last (H (f n)).eventCount) (Fin.le_last first) z) := by
  refine ⟨secondLevelTraceDepth K C2 Kc θ Ctime, secondLevelTraceDepth_pos Ctime hθ, fun m => ?_⟩
  have hL3 := h3 m
  have hρ : 0 < localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * ((K + 1) * metricScalarAt Pl.metric (g (times m))))) :=
    div_pos (localPropagationRadius_pos Cgrad.coe_nonneg) (by positivity)
  have hT0 : (0 : ℝ) ≤ times m := (times m).2.1
  obtain ⟨N, hN0, hNT⟩ := exists_ray_chain_times_P6L (T := (times m : ℝ)) hρ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  obtain ⟨sk, hsk⟩ : ∃ sk : ℕ → Ico 0 rho,
      ∀ k, (sk k : ℝ) = min (k * (times m : ℝ) / N) (times m) :=
    ⟨fun k => ⟨min (k * (times m : ℝ) / N) (times m),
      le_min (by positivity) hT0, (min_le_right _ _).trans_lt (times m).2.2⟩, fun _ => rfl⟩
  have hsk0 : sk 0 = s0 := Subtype.ext (by
    rw [hsk, hs0, Nat.cast_zero, zero_mul, zero_div, min_eq_left hT0])
  have hskN : sk N = times m := Subtype.ext (by
    rw [hsk, mul_div_cancel_left₀ _ hNr.ne', min_self])
  have hskle (k : ℕ) : (sk k : ℝ) ≤ times m := by rw [hsk]; exact min_le_right _ _
  have hKset := isCompact_image_Iic_of_ray_P6L g (times m)
  have href : ∀ k, (M.domain k).referenceMetric = (M.domain k).limitMetric := fun k => by
    rw [hcanonical k]
    rfl
  obtain ⟨k0, hk0⟩ := Perelman.KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains
    M hcanonical _ hKset 1 one_pos
  have hE2 : ∀ᶠ n in atTop, ∀ k ∈ Finset.range N,
      riemannianEDistOf (scaleMetric ((A (f n)).flow.scalar (time (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n)))
        ((A (f n)).endpointTerminalLimitMetric
          ((H (f n)).stage (Fin.last (H (f n)).eventCount))).metric)
        (F.map n (g (sk k))) (F.map n (g (sk (k + 1)))) <
      ENNReal.ofReal (localPropagationRadius Cgrad /
        (2 * Real.sqrt (2 * ((K + 1) * metricScalarAt Pl.metric (g (times m)))))) := by
    refine (Filter.eventually_all_finset _).mpr fun k hk => ?_
    refine eventually_riemannianEDistOf_map_lt_of_metric_convergence M href _ _ ?_
    rw [hg]
    exact ray_chain_step_P6L hN0 hT0 hNT sk hsk k (Finset.mem_range.mp hk)
  have hrho0 : 0 < rho := by
    have h := s0.2.2
    rw [hs0] at h
    exact h
  have hE3 : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (N + 1),
      riemannianEDistOf (scaleMetric ((A (f n)).flow.scalar (time (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n)))
        ((A (f n)).endpointTerminalLimitMetric
          ((H (f n)).stage (Fin.last (H (f n)).eventCount))).metric)
        (F.map n (g s0)) (F.map n (g (sk k))) < ENNReal.ofReal rho := by
    refine (Filter.eventually_all_finset _).mpr fun k _ => ?_
    refine eventually_riemannianEDistOf_map_lt_of_metric_convergence M href _ _ ?_
    rw [hg, edist_dist, Subtype.dist_eq, Real.dist_eq, hs0, zero_sub, abs_neg,
      abs_of_nonneg (sk k).2.1]
    exact (ENNReal.ofReal_lt_ofReal_iff hrho0).mpr (sk k).2.2
  filter_upwards [eventually_ge_atTop k0, hE2, hE3,
    (hD.comp hf.tendsto_atTop).eventually_gt_atTop
      (2 * StandardCap.transitionEnd + Real.sqrt (8 * (secondLevelTraceConstant K C2 Kc *
        metricScalarAt Pl.metric (g (times m)))) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + Phi 1 + Phi 0)) *
          (3 / 2 * secondLevelTraceConstant K C2 Kc * secondLevelTraceDepth K C2 Kc θ Ctime)) *
        (lam + (N * (localPropagationRadius Cgrad /
          (2 * Real.sqrt (2 * ((K + 1) * metricScalarAt Pl.metric (g (times m)))))) + 1))),
    (htime.comp hf.tendsto_atTop).eventually_ge_atTop (secondLevelTraceDepth K C2 Kc θ Ctime)]
    with n hn hE hE3n hDn hTn
  obtain ⟨-, hscal⟩ := hk0 n hn
  have hx0 : F.map n (g s0) = x (f n) := by
    rw [hg0]
    simpa only [PointedRiemannianConvergenceMaps.map] using F.basepoint_map n
  have hd (k : ℕ) (hk : k ≤ N) :
      riemannianEDistOf (scaleMetric ((A (f n)).flow.scalar (time (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n)))
        ((A (f n)).endpointTerminalLimitMetric
          ((H (f n)).stage (Fin.last (H (f n)).eventCount))).metric)
        (x (f n)) (F.map n (g (sk k))) < ENNReal.ofReal rho := by
    have h := hE3n k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    rwa [hx0] at h
  have hQn : 0 < (A (f n)).flow.scalar (time (f n)) (x (f n)).val :=
    zero_lt_one.trans_le (hQ (f n))
  have hrad := sqrt_mul_chain_radius_le_P6L (c := localPropagationRadius Cgrad) hQn hK1 hL3
    (localPropagationRadius_pos Cgrad.coe_nonneg).le
    (localPropagationRadius_le Cgrad.coe_nonneg)
  have hr0 : 0 ≤ 2 * (2 * (localPropagationRadius Cgrad /
      Real.sqrt (2 * ((K + 1) * metricScalarAt Pl.metric (g (times m)) *
        (A (f n)).flow.scalar (time (f n)) (x (f n)).val)))) :=
    mul_nonneg zero_le_two (mul_nonneg zero_le_two
      (div_nonneg (localPropagationRadius_pos Cgrad.coe_nonneg).le (Real.sqrt_nonneg _)))
  have hmem (k : ℕ) : g (sk k) ∈ g '' {s : Ico 0 rho | (s : ℝ) ≤ times m} :=
    ⟨sk k, hskle k, rfl⟩
  have key := RetainedCoreHistory.exists_trace_first_on_witness_ball_of_scaled_ray_chain_P6L
    (H (f n)) (A (f n)) (x (f n)) (hQ (f n)) hPhi hlam hθ (htrace (f n)) (hqQ (f n))
    (U (f n)) (hgradient (f n)) (hW (f n)) hK1 hL3 (N := N) (fun k => F.map n (g (sk k)))
    (by
      change F.map n (g (sk 0)) = x (f n)
      rw [hsk0, hg0]
      simpa only [PointedRiemannianConvergenceMaps.map] using F.basepoint_map n)
    (fun k _ => by
      have h1 := hscal _ (hmem k)
      have h2 := hK m (sk k) (hskle k)
      have h3 := (abs_lt.mp h1).2
      change metricScalarAt (scaleMetric ((A (f n)).flow.scalar (time (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric
          ((H (f n)).stage (Fin.last (H (f n)).eventCount))).metric) (F.map n (g (sk k))) ≤ _
      change metricScalarAt (scaleMetric ((A (f n)).flow.scalar (time (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric
          ((H (f n)).stage (Fin.last (H (f n)).eventCount))).metric) (F.map n (g (sk k))) -
          metricScalarAt Pl.metric (g (sk k)) < 1 at h3
      linarith)
    (fun k hk => hE k (Finset.mem_range.mpr hk))
    (by
      have h1 := hscal _ (hmem N)
      have hL : metricScalarAt Pl.metric (g (sk N)) = metricScalarAt Pl.metric (g (times m)) := by
        rw [hskN]
      rw [hL] at h1
      exact h1)
    (fun k hk => terminal_ball_subset_of_scaled_dist_lt_P6L (A (f n)) hQn (x (f n))
      (F.map n (g (sk k))) (U (f n)) hrho0.le hr0 (hd k hk.le) (by linarith)
      (hU (f n)))
    (hU (f n) _ ((hd N le_rfl).trans_le (ENNReal.ofReal_le_ofReal (by linarith))))
    hTn hDn
  have hpN : F.map n (g (sk N)) = F.map n (xs m) := by rw [hskN, hxs m]
  obtain ⟨first, hfirst, hball⟩ := key
  refine ⟨first, ?_, fun z hz => hball z ?_⟩
  · change (H (f n)).time first ≤ time (f n) - secondLevelTraceDepth K C2 Kc θ Ctime /
      (A (f n)).flow.scalar (time (f n)) (F.map n (g (sk N))).val at hfirst
    rw [hpN] at hfirst
    exact hfirst
  · rw [hpN]
    exact hz

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Set

/-- consumer：原 TSL:170（全局 `hgradient`、`hW`）由 `_P6L` 版（`U i = univ`、`Rad = rho + 2`）推出。 -/
example :
    type_of% @RetainedCoreHistory.eventually_second_level_traces_of_chain_traces.{0} := by
  intro H time A Cgrad q hgradient x hQ hqQ eps C1 C2 hW Kc lam θ hlam hθ Ctime Phi hPhi D hD
    htime htrace f hf Pl F M hcanonical rho g hg s0 hs0 hg0 times xs hxs K hK1 hK h3
  exact RetainedCoreHistory.eventually_second_level_traces_of_chain_traces_P6L H time A Cgrad q
    (fun _ => univ) (fun i y _ => hgradient i y) x hQ hqQ (rho + 2) (fun _ _ _ => mem_univ _)
    (fun i y _ => hW i y) hlam hθ hPhi D hD htime htrace hf Pl F M hcanonical g hg le_rfl s0 hs0
    hg0 times xs hxs hK1 hK h3

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
