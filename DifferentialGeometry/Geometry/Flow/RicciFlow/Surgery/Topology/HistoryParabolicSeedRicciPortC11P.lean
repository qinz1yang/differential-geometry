import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Curvature.Bounds.RiemannTensorOperator
import DifferentialGeometry.Geometry.Metric.Comparison.BallCapture
import DifferentialGeometry.Geometry.Metric.Distance.LocalPullCompactness

/-!
# S-CH11-FIX5 port of astra `HistoryParabolicSeedRicci`（`PortC11P`）

来源：donor `HistoryParabolicSeedRicci.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树有 2 处 elaboration error；本 port 只做下面 2 处 elaboration 层面修补
（no statement / definition / proof idea altered）：
* `exists_past_seed_core_traces_of_metric_distortion` 里 `hcompare` 的 `hRic s ⟨ha0a.trans hs.1, …⟩`：
  `ha0a : a0 ≤ a` 是 `Icc 0 H.horizon` 子类型上的序，`.trans` 的目标是实数不等式 `↑a0 ≤ s`，
  改为 `(show (a0 : ℝ) ≤ (a : ℝ) from ha0a).trans hs.1`。
* `hcapture` 的最后一个参数：`simpa only [hΦ, localPullMetric_inner] using hcompare x z` 改为
  `have h := hcompare x z; simp only [localPullMetric_inner] at h; exact h`
  （目标里是 `↑Φ.toPartialEquiv x`，而 `hΦ` 的左端是 `⇑Φ`，simp 改写不到；两者只差
  `hΦ : … = f j := rfl` 的 defeq，`exact` 用默认透明度可以直接对上）。

原路径 `HistoryParabolicSeedRicci` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology BigOperators ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- Contract the Riemann tensor directly in an orthonormal basis, without the
second dimension factor of a component-to-quadratic-form estimate. -/
private theorem ricciTensor_abs_le_dim_mul_sqrt_rmNormSq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (x : M) (w : TangentSpace I x) :
    |ricciTensor g x w w| ≤
      (Module.finrank ℝ E : ℝ) *
        Real.sqrt (normSq0S g x 4 (metricRm04At g x)) * g.inner x w w := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g b hb
  let A := ricciEndo g x w w
  have htrace : ricciTensor g x w w = ∑ i, b.repr (A (b i)) i := by
    rw [ricciTensor_apply, LinearMap.trace_eq_matrix_trace ℝ b]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
    rfl
  rw [htrace]
  calc
    _ ≤ ∑ i, |b.repr (A (b i)) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)),
        Real.sqrt (normSq0S g x 4 (metricRm04At g x)) * g.inner x w w := by
      apply Finset.sum_le_sum
      intro i _
      have hu : g.inner x (b i) (b i) = 1 := by simpa only [ite_true] using hb i i
      have hrepr : b.repr (A (b i)) i = g.inner x (A (b i)) (b i) := by
        rw [basis_repr_eq_sum_inv_inner g x b _ hinv]
        simp [identityInvMetric, diagonalInvMetric]
      have heval : b.repr (A (b i)) i =
          metricRm04At g x (vec4 (b i) w w (b i)) := by
        rw [hrepr]
        change g.inner x (riemannOp (LeviCivita g) x (b i) w w) (b i) = _
        rw [g.symm, ← rm04_eq_inner, metricRm04StandardAt_apply]
      rw [heval]
      have h := abs_apply_le_norm0S g x 4 (metricRm04At g x) (vec4 (b i) w w (b i))
      have hprod : (∏ a : Fin 4,
          Real.sqrt (g.inner x ((vec4 (b i) w w (b i)) a)
            ((vec4 (b i) w w (b i)) a))) = g.inner x w w := by
        simp [vec4, Fin.prod_univ_succ, hu, ← pow_two,
          Real.sq_sqrt (metric_inner_self_nonneg g x w)]
      simpa only [hprod] using h
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl]
      ring

private theorem sqrt_le_inv_sq_of_scale_bound {r X : ℝ}
    (hr : 0 < r) (hX : 0 ≤ X) (h : r ^ 4 * X ≤ 1) :
    Real.sqrt X ≤ 1 / r ^ 2 := by
  have hs : (r ^ 2 * Real.sqrt X) ^ 2 ≤ 1 := by
    rw [mul_pow, ← pow_mul, Real.sq_sqrt hX]
    exact h
  have hp : r ^ 2 * Real.sqrt X ≤ 1 := by
    nlinarith [Real.sqrt_nonneg X]
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  simpa only [mul_comm] using hp

/-- Retain the actual controlled traces supplied by the same physical
ball capture, including its incoming terminal bounds and zero elapsed time. -/
private theorem exists_past_seed_core_traces_of_metric_distortion
    (H : ObservedHistory.{u}) (t a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
    (p : (H.stageAt t).Carrier) (r v : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r)
    (hv : 0 ≤ v) (hvr : v ≤ r)
    (hclock : (a : ℝ) = (t : ℝ) - v ^ 2)
    (trace : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) p)
    (core L : ℝ) (hL : 0 < L)
    (hdistortion : Real.exp (2 * (3 / r ^ 2) * v ^ 2) ≤ L ^ 2)
    (hmargin : core < (3 * r / 4) / L) :
    let first := H.activeStage a
    let O := trace.point first le_rfl (H.activeStage_mono hat)
    let g := H.stageMetric first ((t : ℝ) - v ^ 2)
    ∃ (b : Icc (0 : ℝ) H.horizon) (hba : b ≤ a),
      (b : ℝ) = (t : ℝ) - r ^ 2 ∧
      ∀ y : (H.stage first).Carrier,
        riemannianEDistOf g O y < ENNReal.ofReal core →
        ∃ A : BackwardPointTrace H (H.activeStage b) first
          (H.activeStage_mono hba) y,
          A.isRmControlled (hat := hba) r := by
  classical
  intro first O g
  have hr : 0 < r := hball.1
  have hvsq : v ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hv hvr 2
  obtain ⟨a0, ha0t, ha0, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm⟩ :=
    H.exists_common_flow_of_parabolicallyRmControlledBall t p r hball
  have ha0a : a0 ≤ a := by
    change (a0 : ℝ) ≤ (a : ℝ)
    rw [ha0, hclock]
    nlinarith
  let j : H.StageInterval (H.activeStage a0) (H.activeStage t) :=
    ⟨first, H.activeStage_mono ha0a, H.activeStage_mono hat⟩
  have hpU : p ∈ U := by
    change p ∈ (U : Set (H.stageAt t).Carrier)
    rw [hU]
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  let pU : U := ⟨p, hpU⟩
  let sourceTrace : BackwardPointTrace H (H.activeStage a0) (H.activeStage t)
      (H.activeStage_mono ha0t) p :=
    { point := fun k hk hl => f ⟨k, hk, hl⟩ pU
      endpoint_eq := hlast pU
      crossing := fun i hi hl => hcross i hi hl pU }
  have hcenter : f j pU = O := by
    have he : sourceTrace.restrictFirst (H.activeStage_mono ha0a)
        (H.activeStage_mono hat) = trace := Subsingleton.elim _ _
    exact congrArg (fun A => A.point first le_rfl (H.activeStage_mono hat)) he
  have hterminal : S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U := by
    have hh := hmetric ⟨H.activeStage t, H.activeStage_mono ha0t, le_rfl⟩ t
      ⟨ha0t, le_rfl⟩ (H.activeStage_mem t)
    have he : f ⟨H.activeStage t, H.activeStage_mono ha0t, le_rfl⟩ = Subtype.val :=
      funext hlast
    simpa only [he, localPullMetric_subtype_val] using hh
  have hpast : S.base.metric a = localPullMetric g (f j) (hf j) := by
    dsimp only [g]
    rw [← hclock]
    exact hmetric j a ⟨ha0a, hat⟩ (H.activeStage_mem a)
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hRic (s : ℝ) (hs : s ∈ Icc (a0 : ℝ) (t : ℝ)) (x : U)
      (z : TangentSpace ThreeModel x) :
      |ricciTensor (S.base.metric s) x z z| ≤
        (3 / r ^ 2) * (S.base.metric s).inner x z z := by
    have hnorm := sqrt_le_inv_sq_of_scale_bound hr
      (normSq0S_nonneg (S.base.metric s) x 4 (metricRm04At (S.base.metric s) x))
      (hRm s hs x)
    have hraw := ricciTensor_abs_le_dim_mul_sqrt_rmNormSq (S.base.metric s) x z
    have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [hdim, Nat.cast_ofNat] at hraw
    calc
      _ ≤ 3 * Real.sqrt (normSq0S (S.base.metric s) x 4
          (metricRm04At (S.base.metric s) x)) * (S.base.metric s).inner x z z := hraw
      _ ≤ (3 / r ^ 2) * (S.base.metric s).inner x z z := by
        apply mul_le_mul_of_nonneg_right _ (metric_inner_self_nonneg _ _ _)
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ) ≤ 3)
  have htime : (t : ℝ) - (a : ℝ) = v ^ 2 := by rw [hclock]; ring
  have hexp : Real.exp (2 * (3 / r ^ 2) * ((t : ℝ) - (a : ℝ))) ≤ L ^ 2 := by
    simpa only [htime] using hdistortion
  have hcompare (x : U) (z : TangentSpace ThreeModel x) :
      (S.base.metric t).inner x z z ≤
        L ^ 2 * (localPullMetric g (f j) (hf j)).inner x z z := by
    have hh := metricEquiv_Icc S.base.metric
      (metricPDE_Icc S hS (Icc_subset_Icc ha0a le_rfl) (Ioo_subset_Ioo ha0a le_rfl))
      (fun s hs x z => hRic s ⟨(show (a0 : ℝ) ≤ (a : ℝ) from ha0a).trans hs.1, hs.2⟩ x z)
      t ⟨hat, le_rfl⟩ x z
    have hupper := hh.2.trans
      (mul_le_mul_of_nonneg_right hexp (metric_inner_self_nonneg _ _ _))
    rwa [hpast] at hupper
  have hcompact : IsCompact (riemannianClosedBallOf (S.base.metric t) pU (3 * r / 4)) := by
    have hc := Geometry.Metric.isCompact_riemannianClosedBallOf_localPullMetric
      (H.stageMetric (H.activeStage t) t) (Subtype.val : U → (H.stageAt t).Carrier)
      (isLocalDiffeomorph_subtype_val U) Subtype.val_injective pU (3 * r / 4)
      (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _).isCompact
      (by
        rw [Subtype.range_coe, hU]
        intro z hz
        exact hz.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith)))
    simpa only [localPullMetric_subtype_val, ← hterminal] using hc
  let V := (hf j).image
  let e : U ≃ₘ⟮ThreeModel, ThreeModel⟯ V :=
    DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage (f j) (hf j) (hinj j)
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel V ⟨e pU⟩
  let Φ : PartialDiffeomorph ThreeModel ThreeModel U (H.stage first).Carrier ∞ :=
    e.toPartialDiffeomorph.trans iV
  have hΦ : (Φ : U → (H.stage first).Carrier) = f j := rfl
  have hsource : Φ.source = univ := by
    ext x
    change (x ∈ (univ : Set U) ∧ e x ∈ (univ : Set V)) ↔ x ∈ (univ : Set U)
    simp only [mem_univ, and_self]
  have hcapture := Perelman.CanonicalNeighborhood.closedBall_subset_image_of_metric_lower
    (S.base.metric t) g Φ pU (by positivity : 0 < 3 * r / 4) hL
    hmargin hcompact (by rw [hsource]; exact subset_univ _) (fun x _ z => by
      have h := hcompare x z
      simp only [localPullMetric_inner] at h
      exact h)
  obtain ⟨_hr, b, _hbt, hb, htraces⟩ := hball
  have hb0 : b = a0 := Subtype.ext (hb.trans ha0.symm)
  subst b
  refine ⟨a0, ha0a, ha0, ?_⟩
  intro y hy
  have hyClosed : y ∈ riemannianClosedBallOf g (Φ pU) core := by
    rw [hΦ, hcenter]
    exact hy.le
  obtain ⟨x, _hx, hxy⟩ := hcapture hyClosed
  have hfy : f j x = y := by simpa only [hΦ] using hxy
  obtain ⟨A, hA⟩ := htraces x.val (by
    change x.val ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r
    rw [← hU]
    exact x.property)
  let mapTrace : BackwardPointTrace H (H.activeStage a0) (H.activeStage t)
      (H.activeStage_mono ha0t) x.val :=
    { point := fun k hk hl => f ⟨k, hk, hl⟩ x
      endpoint_eq := hlast x
      crossing := fun i hi hl => hcross i hi hl x }
  have hEndpoint : A.point first (H.activeStage_mono ha0a)
      (H.activeStage_mono hat) = y :=
    (mapTrace.point_unique A first (H.activeStage_mono ha0a)
      (H.activeStage_mono hat)).symm.trans hfy
  rw [← hEndpoint]
  refine ⟨A.restrictLast (H.activeStage_mono ha0a) (H.activeStage_mono hat), ?_⟩
  constructor
  · intro u hbu hua
    exact hA.1 u hbu (hua.trans hat)
  · intro i hi hl
    exact hA.2 i hi (hl.trans (H.activeStage_mono hat))

/-- The original Ricci conclusion is an endpoint projection of the same
captured controlled traces. -/
private theorem ricci_le_on_past_seed_core_of_metric_distortion
    (H : ObservedHistory.{u}) (t a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
    (p : (H.stageAt t).Carrier) (r v : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r)
    (hv : 0 < v) (hvr : v ≤ r)
    (hclock : (a : ℝ) = (t : ℝ) - v ^ 2)
    (trace : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) p)
    (core L : ℝ) (hL : 0 < L)
    (hdistortion : Real.exp (2 * (3 / r ^ 2) * v ^ 2) ≤ L ^ 2)
    (hmargin : core < (3 * r / 4) / L) :
    let first := H.activeStage a
    let O := trace.point first le_rfl (H.activeStage_mono hat)
    let g := H.stageMetric first ((t : ℝ) - v ^ 2)
    ∀ y : (H.stage first).Carrier,
      riemannianEDistOf g O y < ENNReal.ofReal core →
      ∀ w : TangentSpace ThreeModel y,
        ricciTensor g y w w ≤ (3 / r ^ 2) * g.inner y w w := by
  classical
  intro first O g y hy w
  have hr : 0 < r := hball.1
  obtain ⟨b, hba, _hb, htraces⟩ :=
    exists_past_seed_core_traces_of_metric_distortion H t a hat p r v hball
      hv.le hvr hclock trace core L hL hdistortion hmargin
  obtain ⟨A, hA⟩ := htraces y hy
  have hRmY : r ^ 4 * normSq0S g y 4 (metricRm04At g y) ≤ 1 := by
    have hb := hA.1 a hba le_rfl
    rw [A.endpoint_eq] at hb
    dsimp only [g]
    rw [← hclock]
    exact hb
  have hnorm := sqrt_le_inv_sq_of_scale_bound hr (normSq0S_nonneg g y 4 _) hRmY
  have hraw := ricciTensor_abs_le_dim_mul_sqrt_rmNormSq g y w
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim, Nat.cast_ofNat] at hraw
  apply (le_abs_self _).trans (hraw.trans ?_)
  apply mul_le_mul_of_nonneg_right _ (metric_inner_self_nonneg _ _ _)
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ) ≤ 3)

/-- A controlled terminal ball contains a whole physical past r/4 ball around
the already selected trace center. The common flow and all its maps are supplied
by this same history, including when either slice is a surgery birth. -/
theorem isParabolicallyRmControlledBall.ricci_le_on_past_seed_ball
    (H : ObservedHistory.{u}) (t a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
    (p : (H.stageAt t).Carrier) (r v : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r)
    (hv : 0 < v) (hvr : v ≤ r / 2)
    (hclock : (a : ℝ) = (t : ℝ) - v ^ 2)
    (trace : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) p) :
    let first := H.activeStage a
    let O := trace.point first le_rfl (H.activeStage_mono hat)
    let g := H.stageMetric first ((t : ℝ) - v ^ 2)
    ∀ y : (H.stage first).Carrier,
      riemannianEDistOf g O y < ENNReal.ofReal (r / 4) →
      ∀ w : TangentSpace ThreeModel y,
        ricciTensor g y w w ≤ (3 / r ^ 2) * g.inner y w w := by
  have hr : 0 < r := hball.1
  have hvrFull : v ≤ r := hvr.trans (by linarith)
  have hvsq : v ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ hv.le hvr 2
  have hratio : v ^ 2 / r ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith
  have hdistortion : Real.exp (2 * (3 / r ^ 2) * v ^ 2) ≤ (Real.exp 1) ^ 2 := by
    have hcoef : 2 * (3 / r ^ 2) * v ^ 2 ≤ 2 := by
      calc
        _ = 6 * (v ^ 2 / r ^ 2) := by ring
        _ ≤ 6 * (1 / 4) := mul_le_mul_of_nonneg_left hratio (by norm_num)
        _ ≤ 2 := by norm_num
    calc
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr hcoef
      _ = (Real.exp 1) ^ 2 := by rw [pow_two, ← Real.exp_add]; norm_num
  have hmargin : r / 4 < (3 * r / 4) / Real.exp 1 := by
    apply (lt_div_iff₀ (Real.exp_pos 1)).mpr
    nlinarith [Real.exp_one_lt_three]
  exact ricci_le_on_past_seed_core_of_metric_distortion H t a hat p r v hball hv
    hvrFull hclock trace (r / 4) (Real.exp 1) (Real.exp_pos 1) hdistortion hmargin

/-- Ordinary radius-r parabolic control gives the Ricci bound on the whole
actual past r/40 ball through the half clock, around the already selected trace.
The same common flow and closed-time postmetrics supply the capture. -/
theorem isParabolicallyRmControlledBall.ricci_le_on_past_seed_core_on_half_clock
    (H : ObservedHistory.{u}) (t a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
    (p : (H.stageAt t).Carrier) (r v : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r)
    (hv : 0 < v) (hhalf : v ^ 2 ≤ r ^ 2 / 2)
    (hclock : (a : ℝ) = (t : ℝ) - v ^ 2)
    (trace : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) p) :
    let first := H.activeStage a
    let O := trace.point first le_rfl (H.activeStage_mono hat)
    let g := H.stageMetric first ((t : ℝ) - v ^ 2)
    ∀ y : (H.stage first).Carrier,
      riemannianEDistOf g O y < ENNReal.ofReal (r / 40) →
      ∀ w : TangentSpace ThreeModel y,
        ricciTensor g y w w ≤ (3 / r ^ 2) * g.inner y w w := by
  have hr : 0 < r := hball.1
  have hvrFull : v ≤ r := (sq_le_sq₀ hv.le hr.le).mp (by nlinarith [sq_nonneg r])
  have hratio : v ^ 2 / r ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith
  have hdistortion : Real.exp (2 * (3 / r ^ 2) * v ^ 2) ≤ (Real.exp 2) ^ 2 := by
    have hcoef : 2 * (3 / r ^ 2) * v ^ 2 ≤ 4 := by
      calc
        _ = 6 * (v ^ 2 / r ^ 2) := by ring
        _ ≤ 6 * (1 / 2) := mul_le_mul_of_nonneg_left hratio (by norm_num)
        _ ≤ 4 := by norm_num
    calc
      _ ≤ Real.exp 4 := Real.exp_le_exp.mpr hcoef
      _ = (Real.exp 2) ^ 2 := by rw [pow_two, ← Real.exp_add]; norm_num
  have hexpTwo : Real.exp 2 < 9 := by
    have heq : Real.exp 2 = (Real.exp 1) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    rw [heq]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hmargin : r / 40 < (3 * r / 4) / Real.exp 2 := by
    apply (lt_div_iff₀ (Real.exp_pos 2)).mpr
    nlinarith [mul_lt_mul_of_pos_right hexpTwo hr]
  exact ricci_le_on_past_seed_core_of_metric_distortion H t a hat p r v hball hv
    hvrFull hclock trace (r / 40) (Real.exp 2) (Real.exp_pos 2) hdistortion hmargin

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
