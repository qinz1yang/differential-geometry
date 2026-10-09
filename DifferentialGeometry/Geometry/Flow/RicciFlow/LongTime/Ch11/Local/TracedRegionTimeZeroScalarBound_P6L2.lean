import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingWindowAnchorBound_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedRegionLocalLimitDepthSchedule_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TracedRegionAncientLimitNeckAlternatives_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionTimeZeroScalarBound

/-!
# 基点时刻一致曲率界（深度 schedule）的 **block 形**（O-CH11-P6ANCH2 G2，后缀 `_P6L2`）

`exists_subseq_scalar_le_on_normalized_balls_of_depth_schedule_P6L` 的逐字副本，唯一改动：`hwit` 由
`∀ D T` 换成 block 形 `∀ k, ∀ᶠ n, …(k + 3, τ k)…`（证明体本来只在 schedule 的第 `k` 块
`(k + 3, τ k)` 取值，即 `htraced k` 的半径 / 深度）。private 引理照抄为 `_P6L2`。用途：条件形 driver
（`CrossingDepthExtension2_P6L2`）的初始正深度只在已有 traced region 的 `(k + 3, τ k)` 上要 witness。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.scaleMetric_restrictOpen
  ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
  ObservedHistory.riemannianBallOf_scaleMetric_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

universe u

private theorem closedBall_one_subset_of_ball_eq_P6L2 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) (b : M) (W : TopologicalSpace.Opens M) (k : ℕ)
    (hW : (W : Set M) = riemannianBallOf g b ((k + 3 : ℕ) : ℝ)) (z : M)
    (hz : z ∈ riemannianClosedBallOf g b ((k + 1 : ℕ) : ℝ)) :
    riemannianClosedBallOf g z 1 ⊆ W := by
  intro w hw
  rw [hW]
  have hz' : riemannianEDistOf g b z ≤ ENNReal.ofReal ((k + 1 : ℕ) : ℝ) := hz
  have hw' : riemannianEDistOf g z w ≤ ENNReal.ofReal 1 := hw
  change riemannianEDistOf g b w < ENNReal.ofReal ((k + 3 : ℕ) : ℝ)
  calc riemannianEDistOf g b w ≤ riemannianEDistOf g b z + riemannianEDistOf g z w :=
        riemannianEDistOf_triangle _ _ _ _
    _ ≤ ENNReal.ofReal ((k + 1 : ℕ) : ℝ) + ENNReal.ofReal 1 := add_le_add hz' hw'
    _ = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) + 1) :=
        (ENNReal.ofReal_add (by positivity) (by norm_num)).symm
    _ < ENNReal.ofReal ((k + 3 : ℕ) : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by push_cast; linarith)

section LimitPullback

open TopologicalSpace CheegerGromovCompactness

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private theorem eventually_scalar_le_on_ball_of_limit_scalar_le_P6L2
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P f) (Cd : MetricConvergenceData F)
    (hcan : ∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hPc : MetricComplete P) {C' : ℝ} (hC' : ∀ w : P.M, metricScalarAt P.metric w ≤ C')
    {A : ℝ} (hA : 0 < A) :
    ∀ᶠ i in atTop, ∀ x ∈ riemannianBallOf (X.obj (f i)).metric (X.obj (f i)).basepoint A,
      metricScalarAt (X.obj (f i)).metric x ≤ C' + 1 := by
  have href : ∀ i, (Cd.domain i).referenceMetric = (Cd.domain i).limitMetric := by
    intro i
    rw [hcan i]
    rfl
  have hcompl : RiemannianMetricComplete P.metric := ⟨MetricComplete.complete P hPc⟩
  have hKc : IsCompact (riemannianClosedBallOf P.metric P.basepoint (2 * A)) :=
    hcompl.closedEBall_isCompact P.basepoint (2 * A)
  have hballI := F.eventually_ball_subset_image_closed_ball Cd href hPc P.basepoint (A := A)
    (R := 2 * A) (L := 3 / 2) (by norm_num) (by linarith)
  obtain ⟨k0, hk0⟩ :=
    Perelman.KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains Cd hcan _ hKc 1
      one_pos
  filter_upwards [hballI, eventually_ge_atTop k0] with i hi hik
  intro x hx
  have hx' : x ∈ riemannianBallOf (X.obj (f i)).metric (F.map i P.basepoint) A := by
    convert hx using 2
    exact F.basepoint_map i
  obtain ⟨w, hw, hwx⟩ := hi.2 hx'
  have hsc := (hk0 i hik).2 w hw
  rw [hwx] at hsc
  linarith [(abs_lt.mp hsc).2, hC' w]

end LimitPullback

namespace ObservedHistory

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialNeck SpatialCanonicalWitness
  neckModelTolerance neckModelTolerance_le
  exists_scalar_bound_of_curvatureOperator_nonnegative_of_neck_alternatives
  neck_alternatives_of_local_flow_limit_at_shifted_times
  monotone_and_cover_of_riemannianBallOf_eq
  tendsto_metricDerivNormSupOn_localPull_shifted_to_zero_of_time_lipschitz)

attribute [local instance] CheegerGromovCompactness.PointedRiemannianManifold.topology
  CheegerGromovCompactness.PointedRiemannianManifold.charted
  CheegerGromovCompactness.PointedRiemannianManifold.smooth
  CheegerGromovCompactness.PointedRiemannianManifold.t2
  CheegerGromovCompactness.PointedRiemannianManifold.sigmaCompact

/-- **基点时刻一致曲率界（局部化）**：深度 schedule traced regions + 基点种子体积 + trace-local
κ / pinching / witness ⇒ 子列上 `B(y, A/√R)` 内 `R ≤ C₀ R`（`C₀` 与 `A` 无关）。 -/
theorem exists_subseq_scalar_le_on_normalized_balls_of_depth_schedule_P6L2
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop) (τ : ℕ → ℝ) (hτ : ∀ k, 0 < τ k) (hτ1 : ∀ k, τ k ≤ 1)
    (htraced : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) (τ k / R n)
        (K * R n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (H n).isParabolicallyRmControlledBall v
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v)
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
          (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))))
    {eps C1 C2 Cq : ℝ} (heps0 : 0 < eps) (heps : eps ≤ crossingNeckAccuracy.{u}) {qs : ℕ → ℝ}
    (hqs : ∀ n, qs n ≤ R n * Cq)
    (hwit : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - τ k / R n ≤ v →
      (v : ℝ) < t n → (H n).time ((H n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
        qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) →
        ∃ Wt : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) eps C1 C2
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)),
          Wt.capTubeHasNeckChart eps) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((H (ψ i)).stageMetric ((H (ψ i)).activeStage (t (ψ i)))
          (t (ψ i))) (y (ψ i)) (A / Real.sqrt (R (ψ i))),
        metricScalarAt ((H (ψ i)).stageMetric ((H (ψ i)).activeStage (t (ψ i))) (t (ψ i))) x ≤
          C₀ * R (ψ i) := by
  obtain ⟨W, h, hblock, hlip, -, hlow, hpinchW, -, f, hf, P, F, ⟨Cd, hcan⟩, hPc, hconn,
      -, V, N, hV, hVF, φ, hφ, hφF, Gloc, hG0, -, -, ψ₁, hψ₁, hconv⟩ :=
    exists_local_pointed_flow_limits_of_depth_schedule_P6L
      H t y R hR hRlim τ hτ htraced hr₀ hw hseed hκ ρnc hkappa hPhi hpinch
  let _ : ConnectedSpace P.M := hconn
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  have hβτ : ∀ k : ℕ, 0 < ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k := fun k =>
    mul_pos (by positivity) (hτ k)
  have hβτle : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k ≤ τ k := fun k => by
    have h1 : ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      push_cast
      linarith
    nlinarith [hτ k]
  have hconv0 := fun k (K' : Set (V k)) (hK' : IsCompact K') p η (hη : 0 < η) =>
    (hconv k K' hK' p η hη).imp fun _ hj i hi => (hj i hi).imp fun _ hb => by
      have h1 := hb 0 ⟨neg_nonpos.mpr (hβτ k).le, le_rfl⟩
      rw [hG0 k] at h1
      exact h1
  have hcone := curvatureOperator_nonnegative_of_local_pinching_limit
    (h := fun k n _ => h k n 0) (G := fun _ => P.metric) hf hVmono hVcover hψ₁
    (fun k K' hK' p η hη => (hconv0 k K' hK' p η hη).imp fun _ hj i hi =>
      (hj i hi).imp fun _ hb _ _ => hb) hRlim hPhi
    (fun k => (hpinchW k).mono fun n hn _ _ x => hn 0 ⟨neg_nonpos.mpr (hτ k).le, le_rfl⟩ x)
    0 le_rfl
  have hcompl : RiemannianMetricComplete P.metric :=
    ⟨CheegerGromovCompactness.MetricComplete.complete P hPc⟩
  let E' : ℕ → Set ℝ := fun m => Iic 0 ∩
    ({s | (t m : ℝ) ≤ t m + s / R m} ∪ {s | ∃ i, t m + s / R m = (H m).time i})
  have hEs : ∀ m s, s ≤ 0 → s ∉ E' m →
      t m + s / R m < t m ∧ ∀ i, t m + s / R m ≠ (H m).time i := by
    intro m s hs hsE
    simp only [E', mem_inter_iff, mem_Iic, mem_union, mem_ofPred_eq, not_and, not_or,
      not_exists] at hsE
    obtain ⟨h1, h2⟩ := hsE hs
    exact ⟨not_le.mp h1, h2⟩
  have hE' : ∀ m, (E' m \ Icc (-(0 : ℝ)) 0).Finite := by
    intro m
    refine (Set.finite_range fun i : Fin ((H m).eventCount + 1) =>
      R m * ((H m).time i - t m)).subset ?_
    rintro s ⟨⟨hs0, hs⟩, hsI⟩
    have hs0 : s ≤ 0 := hs0
    have hRm := hR m
    rcases hs with hs | ⟨i, hi⟩
    · refine absurd ⟨?_, hs0⟩ hsI
      have hs1 : (t m : ℝ) ≤ t m + s / R m := hs
      have hsR : 0 ≤ s / R m := by linarith
      have hsn : 0 ≤ s := by
        by_contra hneg
        have := div_neg_of_neg_of_pos (not_le.mp hneg) hRm
        linarith
      linarith
    · refine ⟨i, ?_⟩
      have : s / R m = (H m).time i - t m := by linarith
      change R m * ((H m).time i - t m) = s
      rw [← this, mul_div_assoc']
      exact mul_div_cancel_left₀ s hRm.ne'
  obtain ⟨σ₀, hσ₀, hσ₀E⟩ := exists_tendsto_forall_notMem_of_finite_diff_Icc (ζ := fun _ => (0 : ℝ))
    tendsto_const_nhds hE' le_rfl
  obtain ⟨D, hD, hB6⟩ := exists_neckAlternatives_of_survivor_maps_P6L.{u}
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max 1 (max (2 * |C1|) C2) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := hC ▸ le_max_left _ _
  have hC0 : max (2 * |C1|) C2 ≤ C := hC ▸ le_max_right _ _
  have hC00 : 0 ≤ max (2 * |C1|) C2 := le_max_of_le_left (by positivity)
  have hDe : 0 ≤ D + 2 * eps⁻¹ := by have := inv_pos.mpr heps0; linarith
  obtain ⟨qW, hqW⟩ : ∃ qW : ℝ,
      qW = max Cq ((Real.exp 1 * (C + (D + 2 * eps⁻¹) * Real.sqrt C)) ^ 2) := ⟨_, rfl⟩
  have hxnn : 0 ≤ Real.exp 1 * (C + (D + 2 * eps⁻¹) * Real.sqrt C) :=
    mul_nonneg (Real.exp_pos 1).le
      (add_nonneg (by linarith) (mul_nonneg hDe (Real.sqrt_nonneg _)))
  have hqWsq : (Real.exp 1 * (C + (D + 2 * eps⁻¹) * Real.sqrt C)) ^ 2 ≤ qW :=
    hqW ▸ le_max_right _ _
  have hqWs : Cq ≤ qW := hqW ▸ le_max_left _ _
  have hqW0 : 0 ≤ qW := (sq_nonneg _).trans hqWsq
  have he2 : Real.exp 1 ^ 2 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  obtain ⟨hη₀, hslice⟩ :=
    (exists_scalar_bound_of_curvatureOperator_nonnegative_of_neck_alternatives.{u}).choose_spec
  set η₀ := (exists_scalar_bound_of_curvatureOperator_nonnegative_of_neck_alternatives.{u}).choose
    with hη₀def
  set alpha := min (η₀ / 2) (1 / 44) with halpha_def
  have halpha : 0 < alpha := lt_min (by positivity) (by norm_num)
  have h2α : 2 * alpha ≤ η₀ := by
    have := min_le_left (η₀ / 2) (1 / 44 : ℝ)
    linarith
  have hsmall2 : 2 * alpha < 1 / 11 := by
    have := min_le_right (η₀ / 2) (1 / 44 : ℝ)
    linarith
  have hnmt : neckModelTolerance alpha < 1 / 11 :=
    (neckModelTolerance_le alpha).trans_lt (by linarith)
  have hεα : eps ≤ neckModelTolerance alpha := heps
  obtain ⟨C', hC'⟩ := hslice P.metric hcompl hcone h2α (by
    refine neck_alternatives_of_local_flow_limit_at_shifted_times halpha hsmall2 hf F Cd hcan
      hPc hconn hV hVF hφF (G := fun _ => P.metric) hψ₁ (σ := fun _ => σ₀)
      (fun _ _ k _ K' hK' p η hη =>
        (tendsto_metricDerivNormSupOn_localPull_shifted_to_zero_of_time_lipschitz hf F Cd hcan
          hPc hV hφF hψ₁ hconv0 hβτ hlip hσ₀ (fun m => (hσ₀E m).1) k K' hK' p hη).imp
          fun _ hj i hi => (hj i hi).imp fun _ hb =>
            ⟨⟨le_trans (neg_le_neg (le_trans (hβτle k) ((hτ1 k).trans (by
              push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])))) hb.1.1, hb.1.2⟩,
              hb.2⟩)
      (fun _ _ => hcompl) (E := fun m => {s | s ≠ σ₀ m})
      (fun _ _ => Eventually.of_forall fun m => by simp) (q := qW) hC1 ?_ 0 le_rfl
    intro k
    filter_upwards [hblock k, hlow k, hσ₀.eventually (Ioi_mem_nhds (neg_neg_of_pos (hβτ k))),
      hwit k]
      with m hn hlowm hσm hwm s hs hsE z hz hqz
    have hsσ : s = σ₀ m := by simpa using hsE
    subst hsσ
    obtain ⟨hWset, -, h0eq, ⟨a, hat, ha, fs, hfs, hinj, hcross, hlast, hp⟩, -⟩ := hn
    obtain ⟨hσ0, hσE'⟩ := hσ₀E m
    obtain ⟨hst₀, hne⟩ := hEs m (σ₀ m) hσ0 hσE'
    have hsτ : σ₀ m ∈ Icc (-τ k) 0 := ⟨(neg_le_neg (hβτle k)).trans hσm.le, hσ0⟩
    have hsIn : σ₀ m ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0 := ⟨hσm.le, hσ0⟩
    have hzpos : 0 < metricScalarAt (h k m (σ₀ m)) z := hqW0.trans_lt hqz
    have hcpt : IsCompact (riemannianClosedBallOf (h k m 0) z 1) := by
      have hdom : ((t m : ℝ) + 0 / R m) ∈ (H m).stageDomain ((H m).activeStage (t m)) := by
        simpa using (H m).activeStage_mem (t m)
      rw [h0eq 0 ⟨neg_nonpos.mpr (hτ k).le, le_rfl⟩ hdom, zero_div, add_zero,
        ObservedHistory.scaleMetric_restrictOpen]
      exact ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen _ _ _ _
        (closedBall_one_subset_of_ball_eq_P6L2 _ _ _ k hWset _ hz)
    have hsmall : Real.exp 1 * (max (2 * |C1|) C2 + (D + 2 * eps⁻¹) *
        Real.sqrt (max (2 * |C1|) C2)) < Real.sqrt (metricScalarAt (h k m (σ₀ m)) z) := by
      refine lt_of_le_of_lt ?_ ((Real.lt_sqrt hxnn).mpr (hqWsq.trans_lt hqz))
      gcongr
    have hqs' : qs m ≤ R m * qW :=
      (hqs m).trans (mul_le_mul_of_nonneg_left hqWs (hR m).le)
    -- 局部化：survivor 点形 witness 由 trace-local `hwit` 经 survivor maps 的 backward trace 给出
    have hWset' : (W k m : Set ((H m).stageAt (t m)).Carrier) =
        riemannianBallOf (scaleMetric (R m) (hR m)
          ((H m).stageMetric ((H m).activeStage (t m)) (t m))) (y m) ((k + 3 : ℕ) : ℝ) := hWset
    have hwitS : ∀ v : Icc (0 : ℝ) (H m).horizon, (v : ℝ) < t m →
        (H m).time ((H m).activeStage v) < v →
        ∀ (hav : a ≤ v) (hvt : v ≤ t m) (z' : W k m),
          qs m < metricScalarAt ((H m).stageMetric ((H m).activeStage v) v)
            (fs ⟨(H m).activeStage v, (H m).activeStage_mono hav,
              (H m).activeStage_mono hvt⟩ z') →
          ∃ Wt : SpatialCanonicalWitness ((H m).stageMetric ((H m).activeStage v) v) eps C1 C2
              (fs ⟨(H m).activeStage v, (H m).activeStage_mono hav,
                (H m).activeStage_mono hvt⟩ z'),
            Wt.capTubeHasNeckChart eps := by
      intro v hvlt hreg hav hvt z' hq'
      obtain ⟨tr, htr⟩ := exists_backwardPointTrace_of_survivor_maps_P6L (H m) (t m) a hat fs
        hcross hlast v hav hvt z'
      have hz'B : (z' : ((H m).stageAt (t m)).Carrier) ∈
          riemannianBallOf ((H m).stageMetric ((H m).activeStage (t m)) (t m)) (y m)
            (((k + 3 : ℕ) : ℝ) / Real.sqrt (R m)) := by
        rw [← ObservedHistory.riemannianBallOf_scaleMetric_eq _ (hR m), ← hWset']
        exact z'.property
      have hva : (t m : ℝ) - τ k / R m ≤ v := by rw [← ha]; exact hav
      have hw := hwm z' hz'B v hvt hva hvlt hreg tr (by rw [htr]; exact hq')
      rw [htr] at hw
      exact hw
    have key := hB6 _ _ (hR m) hqs' (Real.exp_pos 1) a ha fs hfs hinj hp hwitS hsτ hst₀
      (fun hv => lt_of_le_of_ne (ObservedHistory.activeStage_time_le _ _)
        fun heq => hne _ heq.symm) z hcpt
      (fun y' _ u => by rw [he2]; exact hlowm (σ₀ m) hsIn y' u) hqz hsmall
    rcases key with nk | ⟨w, nk, h2, h3, h4⟩ | h5
    · exact Or.inl (nk.map fun n => n.mono hεα hnmt)
    · have hw0 : 0 < metricScalarAt (h k m (σ₀ m)) w := by
        by_contra hneg
        have := mul_nonpos_of_nonneg_of_nonpos hC00 (not_lt.mp hneg)
        linarith
      refine Or.inr (Or.inl ⟨w, nk.map fun n => n.mono hεα hnmt,
        h2.trans (mul_le_mul_of_nonneg_right hC0 hw0.le),
        h3.trans (mul_le_mul_of_nonneg_right hC0 hzpos.le), h4.trans_le ?_⟩)
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hC0 (Real.sqrt_nonneg _))
    · exact Or.inr (Or.inr fun y' hy => (h5 y' hy).trans
        (mul_le_mul_of_nonneg_right hC0 hzpos.le)))
  refine ⟨f, hf, max (C' + 1) 1, le_max_right _ _, fun A hA => ?_⟩
  filter_upwards [eventually_scalar_le_on_ball_of_limit_scalar_le_P6L2 F Cd hcan hPc hC' hA]
    with i hi
  intro x hx
  have hR0 := hR (f i)
  have hsR : Real.sqrt (R (f i)) * (A / Real.sqrt (R (f i))) = A := by
    have := Real.sqrt_pos.mpr hR0
    field_simp
  have hxX := riemannianBallOf_scaleMetric (R (f i)) hR0
    ((H (f i)).stageMetric ((H (f i)).activeStage (t (f i))) (t (f i))) (y (f i))
    (A / Real.sqrt (R (f i)))
  rw [hsR] at hxX
  rw [← hxX] at hx
  have hle := hi x hx
  change metricScalarAt (scaleMetric (R (f i)) hR0
    ((H (f i)).stageMetric ((H (f i)).activeStage (t (f i))) (t (f i)))) x ≤ C' + 1 at hle
  rw [metricScalarAt_scaleMetric, inv_mul_le_iff₀ hR0] at hle
  have h1 : C' + 1 ≤ max (C' + 1) 1 := le_max_left _ _
  refine hle.trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right h1 hR0.le

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
