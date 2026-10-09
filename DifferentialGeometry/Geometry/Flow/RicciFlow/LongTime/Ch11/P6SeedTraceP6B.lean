import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.BallVolumeComparison
import DifferentialGeometry.Geometry.Curvature.Bounds.RiemannTensorOperator
import DifferentialGeometry.Geometry.Metric.Comparison.BallCapture
import DifferentialGeometry.Geometry.Metric.Distance.LocalPullCompactness
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Metric.RestrictionDistance

/-!
# P6 / L5 的 seed shift 底座（O-CH11-P6B G1，后缀 `_P6B`）

KL 84.1(a)（局部 κ(A)）在种子时刻 `t` 成立；P6 的反证（point selection 选出坏点 `(s, y)`，
`s ∈ [t − r²/2, t]`）需要它在**更早的时刻** `v ≤ s` 成立。这里给出把种子从 `t` 搬到 `v` 的两个
history 级引理（只用树内引理重证；证明思路参照 astra B1 FAIL 的 `ST/HistoryParabolicSeedRicci`
与 `ST/TracedRegionVolume`，它们在 W8 编不过，只当 reference）：

* `exists_past_seed_core_traces_P6B`：controlled 球 `P(p, t, r, −r²)` 的 common flow 在时刻
  `t − v²` 的像覆盖种子 trace 点 `O` 周围半径 `core < (3r/4)/L` 的整个物理球（ball capture +
  Ricci 下的度量畸变 `exp(2·(3/r²)·v²) ≤ L²`），且球内每点都有 Rm-controlled backward trace。
* `volume_ball_ge_along_trace_of_isTracedRegion_P6B`：traced region 内，终端时刻的体积比沿同一条
  trace 传到更早时刻，损失 `exp(−54 K τ)`。
-/

set_option autoImplicit false
noncomputable section

open Set Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology BigOperators ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- 在正交基里直接缩并 Riemann 张量：`|Ric(w,w)| ≤ n·|Rm|·g(w,w)`（只有一个维数因子）。 -/
private theorem ricciTensor_abs_le_dim_mul_sqrt_rmNormSq_P6B
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

private theorem sqrt_le_inv_sq_of_scale_bound_P6B {r X : ℝ}
    (hr : 0 < r) (hX : 0 ≤ X) (h : r ^ 4 * X ≤ 1) :
    Real.sqrt X ≤ 1 / r ^ 2 := by
  have hs : (r ^ 2 * Real.sqrt X) ^ 2 ≤ 1 := by
    rw [mul_pow, ← pow_mul, Real.sq_sqrt hX]
    exact h
  have hp : r ^ 2 * Real.sqrt X ≤ 1 := by
    nlinarith [Real.sqrt_nonneg X]
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  simpa only [mul_comm] using hp

/-- **seed 覆盖引理**：`P(p, t, r, −r²)` controlled 时，在时刻 `a = t − v²`（`0 ≤ v ≤ r`），
种子 trace 点 `O` 周围半径 `core` 的物理球（`core < (3r/4)/L`，`L²` 控制 Ricci 畸变）里每点都有
从 `b = t − r²` 起、Rm-controlled（半径 `r`）的 backward trace。common flow 的像用 ball capture 覆盖。 -/
theorem exists_past_seed_core_traces_P6B
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
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hRic (s : ℝ) (hs : s ∈ Icc (a0 : ℝ) (t : ℝ)) (x : U)
      (z : TangentSpace ThreeModel x) :
      |ricciTensor (S.base.metric s) x z z| ≤
        (3 / r ^ 2) * (S.base.metric s).inner x z z := by
    have hnorm := sqrt_le_inv_sq_of_scale_bound_P6B hr
      (normSq0S_nonneg (S.base.metric s) x 4 (metricRm04At (S.base.metric s) x))
      (hRm s hs x)
    have hraw := ricciTensor_abs_le_dim_mul_sqrt_rmNormSq_P6B (S.base.metric s) x z
    have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [hdim, Nat.cast_ofNat] at hraw
    calc
      _ ≤ 3 * Real.sqrt (normSq0S (S.base.metric s) x 4
          (metricRm04At (S.base.metric s) x)) * (S.base.metric s).inner x z z := hraw
      _ ≤ (3 / r ^ 2) * (S.base.metric s).inner x z z := by
        apply mul_le_mul_of_nonneg_right _ (metric_inner_self_nonneg _ _ _)
        have h3 := mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ) ≤ 3)
        calc 3 * Real.sqrt (normSq0S (S.base.metric s) x 4
              (metricRm04At (S.base.metric s) x)) ≤ 3 * (1 / r ^ 2) := h3
          _ = 3 / r ^ 2 := by ring
  have htime : (t : ℝ) - (a : ℝ) = v ^ 2 := by rw [hclock]; ring
  have hexp : Real.exp (2 * (3 / r ^ 2) * ((t : ℝ) - (a : ℝ))) ≤ L ^ 2 := by
    simpa only [htime] using hdistortion
  have hcompare (x : U) (z : TangentSpace ThreeModel x) :
      (S.base.metric t).inner x z z ≤
        L ^ 2 * (localPullMetric g (f j) (hf j)).inner x z z := by
    have hh := metricEquiv_Icc S.base.metric
      (metricPDE_Icc S hS (Icc_subset_Icc ha0a le_rfl) (Ioo_subset_Ioo ha0a le_rfl))
      (fun s hs x z => hRic s ⟨le_trans (show (a0 : ℝ) ≤ a from ha0a) hs.1, hs.2⟩ x z)
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
    rw [hterminal]
    simpa only [localPullMetric_subtype_val] using hc
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
      have hxz := hcompare x z
      rw [localPullMetric_inner] at hxz
      exact hxz)
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

private theorem volume_ball_restrictOpen_eq_of_subset_P6B
    {P : OrientedThreeStage.{u}} (g : P.Metric) (U : Opens P.Carrier)
    [SigmaCompactSpace U] (p : U) (r : ℝ)
    (hball : riemannianBallOf g p.val r ⊆ U) :
    riemannianVolumeMeasure ThreeModel U (g.restrictOpen U)
        (riemannianBallOf (g.restrictOpen U) p r) =
      riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p.val r) := by
  have hset : riemannianBallOf (g.restrictOpen U) p r =
      (Subtype.val : U → P.Carrier) ⁻¹' riemannianBallOf g p.val r := by
    ext x
    constructor
    · intro hx
      exact (riemannianEDistOf_le_restrictOpen g U p x).trans_lt hx
    · intro hx
      exact Geometry.Metric.riemannianEDistOf_restrictOpen_lt_of_riemannianBallOf_subset
        g U p x hball hx
  rw [hset]
  let _ : MeasurableSpace P.Carrier := borel P.Carrier
  have _ : BorelSpace P.Carrier := ⟨rfl⟩
  exact Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset g U
    (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist g p.val)
      continuous_const).measurableSet hball

/-- **沿 trace 的体积下界**：traced region（半径 `ρ`、深度 `τ`、`|Rm| ≤ K`）里，终端时刻 `t` 在
`p` 处尺度 `≤ R` 的体积比 `κ` 传到更早时刻 `v ≥ t − τ` 的同一条 trace 点上，系数损失 `exp(−54 K τ)`。 -/
theorem volume_ball_ge_along_trace_of_isTracedRegion_P6B
    (H : ObservedHistory.{u}) (t v : Icc (0 : ℝ) H.horizon) (hvt : v ≤ t)
    (p : (H.stageAt t).Carrier) {ρ τ K κ R r : ℝ} (hK : 0 ≤ K)
    (h : H.isTracedRegion t p ρ τ K) (hv : (t : ℝ) - τ ≤ v)
    (A : BackwardPointTrace H (H.activeStage v) (H.activeStage t)
      (H.activeStage_mono hvt) p)
    (hRρ : R ≤ ρ)
    (hvolume : ∀ s : ℝ, 0 < s → s ≤ R →
      ENNReal.ofReal κ * ENNReal.ofReal s ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t)
          (riemannianBallOf (H.stageMetric (H.activeStage t) t) p s))
    (hr : 0 < r) (hrR : r ≤ R) :
    ENNReal.ofReal (Real.exp (-54 * K * τ) * κ) * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
        (H.stageMetric (H.activeStage v) v)
        (riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) r) := by
  obtain ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm⟩ :=
    H.exists_common_flow_of_isTracedRegion t p h
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have hav : a ≤ v := by change a.val ≤ v.val; rwa [ha]
  have hpU : p ∈ U := by
    change p ∈ (U : Set (H.stageAt t).Carrier)
    rw [hU]
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) p p < ENNReal.ofReal ρ
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr h.radius_pos
  let x : U := ⟨p, hpU⟩
  let jt : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩
  let jv : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩
  have hflast : f jt = (Subtype.val : U → (H.stageAt t).Carrier) := funext hlast
  have hterminal : S.base.metric t =
      (H.stageMetric (H.activeStage t) t).restrictOpen U := by
    rw [hmetric jt t ⟨hat, le_rfl⟩ (H.activeStage_mem t)]
    apply SmoothRiemannianMetric.ext_inner
    intro y z w
    rw [localPullMetric_inner, hflast]
    simp only [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply]
    rfl
  have hearlier : S.base.metric v =
      localPullMetric (H.stageMetric (H.activeStage v) v) (f jv) (hf jv) :=
    hmetric jv v ⟨hav, hvt⟩ (H.activeStage_mem v)
  let B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) p :=
    { point := fun j hj hl => f ⟨j, hj, hl⟩ x
      endpoint_eq := hlast x
      crossing := fun i hi hl => hcross i hi hl x }
  have hcenter : f jv x = A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt) :=
    (B.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvt)).point_unique
      A (H.activeStage v) le_rfl (H.activeStage_mono hvt)
  let α : ℝ := Real.exp (-9 * K * τ)
  have hα : 0 < α := Real.exp_pos _
  have hα1 : α ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hK h.depth_pos.le]
  have hαr : 0 < α * r := mul_pos hα hr
  have hαrR : α * r ≤ R :=
    (mul_le_mul_of_nonneg_right hα1 hr.le).trans (by simpa only [one_mul] using hrR)
  have hsubset : riemannianBallOf (H.stageMetric (H.activeStage t) t) p (α * r) ⊆ U := by
    intro z hz
    change z ∈ (U : Set (H.stageAt t).Carrier)
    rw [hU]
    exact riemannianBallOf_mono _ _ (hαrR.trans hRρ) hz
  have hterminalVolume : ENNReal.ofReal κ * ENNReal.ofReal (α * r) ^ 3 ≤
      riemannianVolumeMeasure ThreeModel U (S.base.metric t)
        (riemannianBallOf (S.base.metric t) x (α * r)) := by
    rw [hterminal, volume_ball_restrictOpen_eq_of_subset_P6B
      (H.stageMetric (H.activeStage t) t) U x (α * r) hsubset]
    exact hvolume (α * r) hαr hαrR
  have hcomparison := riemannianVolumeMeasure_ball_le_exp_mul_of_curvature_bound S hS
    (a := a.val) (b := t.val) (C := K ^ 2) Subset.rfl Subset.rfl hRm
    (show t.val ∈ Icc a.val t.val from ⟨hat, le_rfl⟩)
    (show v.val ∈ Icc a.val t.val from ⟨hav, hvt⟩) x (α * r)
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  norm_num only [hdim, Nat.cast_ofNat, Real.sqrt_sq hK] at hcomparison
  have htime : |t.val - v.val| ≤ τ := by
    rw [abs_of_nonneg (sub_nonneg.mpr (show (v : ℝ) ≤ t from hvt))]
    linarith
  have hradius : Real.exp (9 * K * |t.val - v.val|) * (α * r) ≤ r := by
    dsimp only [α]
    rw [← mul_assoc, ← Real.exp_add]
    have he : Real.exp (9 * K * |t.val - v.val| + -9 * K * τ) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hh := mul_le_mul_of_nonneg_left htime (by positivity : 0 ≤ 9 * K)
      linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he hr.le
  have hfactor : Real.exp (27 * K * |t.val - v.val|) ≤ Real.exp (27 * K * τ) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime (by positivity))
  have hmap := Geometry.Measure.riemannianVolumeMeasure_ball_le_of_injective_local_isometry
    (S.base.metric v) (H.stageMetric (H.activeStage v) v) (f jv) (hf jv) (hinj jv)
    (fun y z w => by rw [hearlier, localPullMetric_inner]) x r
  rw [hcenter] at hmap
  have hupper : ENNReal.ofReal κ * ENNReal.ofReal (α * r) ^ 3 ≤
      ENNReal.ofReal (Real.exp (27 * K * τ)) *
        riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
          (H.stageMetric (H.activeStage v) v)
          (riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) r) := by
    refine hterminalVolume.trans (hcomparison.trans ?_)
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hfactor)
      ((MeasureTheory.measure_mono (riemannianBallOf_mono _ _ hradius)).trans hmap)
  have hcancel : ENNReal.ofReal (Real.exp (-27 * K * τ)) *
      ENNReal.ofReal (Real.exp (27 * K * τ)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    rw [show -27 * K * τ + 27 * K * τ = 0 by ring,
      Real.exp_zero, ENNReal.ofReal_one]
  have hlower := mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp (-27 * K * τ)))) hupper
  have hcancelVolume : ENNReal.ofReal (Real.exp (-27 * K * τ)) *
      (ENNReal.ofReal (Real.exp (27 * K * τ)) *
        riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
          (H.stageMetric (H.activeStage v) v)
          (riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) r)) =
      riemannianVolumeMeasure ThreeModel (H.stageAt v).Carrier
        (H.stageMetric (H.activeStage v) v)
        (riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) r) := by
    rw [← mul_assoc, hcancel, one_mul]
  rw [hcancelVolume] at hlower
  have hexp : Real.exp (-27 * K * τ) * α ^ 3 = Real.exp (-54 * K * τ) := by
    dsimp only [α]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hcoef : ENNReal.ofReal (Real.exp (-27 * K * τ)) *
      (ENNReal.ofReal κ * ENNReal.ofReal (α * r) ^ 3) =
      ENNReal.ofReal (Real.exp (-54 * K * τ) * κ) * ENNReal.ofReal r ^ 3 := by
    rw [ENNReal.ofReal_mul hα.le, mul_pow]
    calc
      _ = (ENNReal.ofReal (Real.exp (-27 * K * τ)) * ENNReal.ofReal α ^ 3) *
          ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 := by ring
      _ = _ := by
        rw [← ENNReal.ofReal_pow hα.le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          hexp, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rwa [hcoef] at hlower

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
