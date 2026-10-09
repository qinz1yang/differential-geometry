import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaBallVolumeC11Q
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedShiftP6B

/-!
# K0 `seed_patch_transport` 的证明（O-CH11-KAPPA G2，后缀 `_C11Q`）

审稿第一限定（R-C11-2 Q1.1）："K0 不是单纯改写定义"——`hasSmallParabolicCurvature` 给的是终端种子球
每点的 backward trace 与沿 trace 的曲率控制；要在较早切片用一个实际度量球，须证它**包含在 traced 区域
中**，且有统一的体积比较。本文件证 `SeedPatchTransport_C11Q`（深度 `3r²/4`）：

* **包含 + 度量比较**（`exists_terminal_preimage_of_past_seed_ball_C11Q`）：controlled 球
  `P(p, t, r, −r²)` 的 common flow `f_s : B_t(p, r) → stage(s)`；Ricci 畸变 `g_t ≤ L² f_s^* g_s`
  （`L² = e^{6v²/r²}`）+ ball capture ⇒ `B_s(O, core) ⊆ f_s(B̄_t(p, R))`（`core < R/L`，`R < r`）。
  与 P6B 的 `exists_past_seed_core_traces_P6B` 同一几何证明（拷贝其两个 private 辅助引理），区别是
  **输出终端原像** `x' ∈ B̄_t(p, R)` 与它的 trace（P6B 只输出早期点的回溯 trace）。取 `v² = 3r²/4`、
  `L = e^{9/4} < 10`、`core = r/20`、`R = r/2`：早期球 `B(O⋆, r/20)` ⊆ `B_t(p, 3r/5)` 的 traced 像；
  再由 trace 唯一性（`Subsingleton`）换成种子自己的 `√3 r`-受控 trace。
* **体积**：P6B 的 `volume_lower_along_nearby_trace_P6B`（`y = p`），系数 `w e⁻⁵⁷/512`。
* **内部余量**：P6B 的 `exists_past_seed_core_traces_P6B`（`core = 3r/40 < (3r/4)/e^{9/4}`）。
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
private theorem ricciTensor_abs_le_dim_mul_sqrt_rmNormSq_C11Q
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

private theorem sqrt_le_inv_sq_of_scale_bound_C11Q {r X : ℝ}
    (hr : 0 < r) (hX : 0 ≤ X) (h : r ^ 4 * X ≤ 1) :
    Real.sqrt X ≤ 1 / r ^ 2 := by
  have hs : (r ^ 2 * Real.sqrt X) ^ 2 ≤ 1 := by
    rw [mul_pow, ← pow_mul, Real.sq_sqrt hX]
    exact h
  have hp : r ^ 2 * Real.sqrt X ≤ 1 := by
    nlinarith [Real.sqrt_nonneg X]
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  simpa only [mul_comm] using hp

/-- **终端原像覆盖**：`P(p, t, r, −r²)` controlled 时，时刻 `a = t − v²`（`0 ≤ v ≤ r`）的种子 trace 点
`O` 周围半径 `core < R/L` 的物理球里每点 `y`，都是某个 `x' ∈ B̄_t(p, R)`（`R < r`）的 Rm-controlled
（半径 `r`，从 `b = t − r²` 起）backward trace 在 `a` 的点——终端球的 traced 像包含早期度量球。 -/
theorem exists_terminal_preimage_of_past_seed_ball_C11Q
    (H : ObservedHistory.{u}) (t a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
    (p : (H.stageAt t).Carrier) (r v : ℝ)
    (hball : H.isParabolicallyRmControlledBall t p r)
    (hv : 0 ≤ v) (hvr : v ≤ r)
    (hclock : (a : ℝ) = (t : ℝ) - v ^ 2)
    (trace : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) p)
    (core R L : ℝ) (hR : 0 < R) (hRr : R < r) (hL : 0 < L)
    (hdistortion : Real.exp (2 * (3 / r ^ 2) * v ^ 2) ≤ L ^ 2)
    (hmargin : core < R / L) :
    let first := H.activeStage a
    let O := trace.point first le_rfl (H.activeStage_mono hat)
    let g := H.stageMetric first ((t : ℝ) - v ^ 2)
    ∃ (b : Icc (0 : ℝ) H.horizon) (hba : b ≤ a),
      (b : ℝ) = (t : ℝ) - r ^ 2 ∧
      ∀ y : (H.stage first).Carrier,
        riemannianEDistOf g O y < ENNReal.ofReal core →
        ∃ x' : (H.stageAt t).Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x' ≤ ENNReal.ofReal R ∧
          ∃ A : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
              (H.activeStage_mono (hba.trans hat)) x',
            A.isRmControlled (hat := hba.trans hat) r ∧
            A.point first (H.activeStage_mono hba) (H.activeStage_mono hat) = y := by
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
    have hnorm := sqrt_le_inv_sq_of_scale_bound_C11Q hr
      (normSq0S_nonneg (S.base.metric s) x 4 (metricRm04At (S.base.metric s) x))
      (hRm s hs x)
    have hraw := ricciTensor_abs_le_dim_mul_sqrt_rmNormSq_C11Q (S.base.metric s) x z
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
  have hcompact : IsCompact (riemannianClosedBallOf (S.base.metric t) pU R) := by
    have hc := Geometry.Metric.isCompact_riemannianClosedBallOf_localPullMetric
      (H.stageMetric (H.activeStage t) t) (Subtype.val : U → (H.stageAt t).Carrier)
      (isLocalDiffeomorph_subtype_val U) Subtype.val_injective pU R
      (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _).isCompact
      (by
        rw [Subtype.range_coe, hU]
        intro z hz
        exact hz.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hRr))
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
    (S.base.metric t) g Φ pU hR hL
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
  obtain ⟨x, hx, hxy⟩ := hcapture hyClosed
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
  have hxS : riemannianEDistOf (S.base.metric t) pU x ≤ ENNReal.ofReal R := hx
  rw [hterminal] at hxS
  exact ⟨x.val, (riemannianEDistOf_le_restrictOpen _ U pU x).trans hxS, A, hA, hEndpoint⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace GC.LongTime.Ch11

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse

universe u

/-- 种子 ⇒ 半径 `r` 的 controlled 球（`√3 r`-控制强于 `r`-控制）。 -/
theorem isParabolicallyRmControlledBall_of_seed_C11Q {H : ObservedHistory.{u}}
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {r : ℝ}
    (hseed : hasSmallParabolicCurvature H t p r) : H.isParabolicallyRmControlledBall t p r := by
  have hr : 0 < r := hseed.1
  have hsqrt : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hrr : r ≤ Real.sqrt 3 * r := le_mul_of_one_le_left hr.le hsqrt
  obtain ⟨_hr, a, hat, ha, htraces⟩ := hseed
  refine ⟨hr, a, hat, ha, ?_⟩
  intro x hx
  obtain ⟨B, hB⟩ := htraces x hx
  have hpow : r ^ 4 ≤ (Real.sqrt 3 * r) ^ 4 := pow_le_pow_left₀ hr.le hrr 4
  refine ⟨B, ?_, ?_⟩
  · intro u hau hut
    exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans (hB.1 u hau hut)
  · intro i hi hl
    exact (mul_le_mul_of_nonneg_right hpow (normSq0S_nonneg _ _ _ _)).trans (hB.2 i hi hl)

/-- `e^{9/4} < 10`（`e^9 < 2.7182818286⁹ < 10⁴`）：深度 `3r²/4` 的 Ricci 畸变常数。 -/
theorem exp_nine_quarters_lt_ten_C11Q : Real.exp (9 / 4) < 10 := by
  have h1 : Real.exp (9 / 4) ^ 4 = Real.exp 1 ^ 9 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have h2 : Real.exp 1 ^ 9 < 10 ^ 4 :=
    calc Real.exp 1 ^ 9 < 2.7182818286 ^ 9 := by
          gcongr
          exact Real.exp_one_lt_d9
      _ < 10 ^ 4 := by norm_num
  rw [← h1] at h2
  exact lt_of_pow_lt_pow_left₀ 4 (by norm_num) h2

/-- **K0 `seed_patch_transport`（G2，已证）**：每个种子与种子 trace 在深度 `3r²/4` 的切片上给出
`IsSeedPatch_C11Q`（包含 + 度量比较、体积 `(w e⁻⁵⁷/512)ϱ³`、内部余量）。 -/
theorem seedPatchTransport_C11Q : SeedPatchTransport_C11Q.{u} := by
  intro H t p r w htime hseed hvolume b hbt hb seedTrace s hbs hst hs
  have hr : 0 < r := hseed.1
  have hball := isParabolicallyRmControlledBall_of_seed_C11Q hseed
  set v : ℝ := Real.sqrt (3 / 4) * r with hvdef
  have hv0 : 0 ≤ v := by positivity
  have hv2 : v ^ 2 = 3 / 4 * r ^ 2 := by
    rw [hvdef, mul_pow, Real.sq_sqrt (by norm_num)]
  have hvr : v ≤ r := by
    have h34 : Real.sqrt (3 / 4) ≤ 1 := by
      rw [Real.sqrt_le_one]
      norm_num
    exact mul_le_of_le_one_left hr.le h34
  have hclock : (s : ℝ) = (t : ℝ) - v ^ 2 := by
    rw [hv2, hs]
    ring
  have hexp := exp_nine_quarters_lt_ten_C11Q
  have hL : 0 < Real.exp (9 / 4) := Real.exp_pos _
  have hdist : Real.exp (2 * (3 / r ^ 2) * v ^ 2) ≤ Real.exp (9 / 4) ^ 2 := by
    have h92 : 2 * (3 / r ^ 2) * (3 / 4 * r ^ 2) = 9 / 2 := by
      field_simp
      ring
    rw [hv2, h92, ← Real.exp_nat_mul]
    norm_num
  let trace := seedTrace.restrictFirst (H.activeStage_mono hbs) (H.activeStage_mono hst)
  unfold IsSeedPatch_C11Q
  refine ⟨?_, ?_, ?_⟩
  · -- 包含 + 度量比较
    have hmargin : r / 20 < (r / 2) / Real.exp (9 / 4) := by
      rw [lt_div_iff₀ hL]
      nlinarith
    obtain ⟨b', hb's, hb', hcov⟩ := H.exists_terminal_preimage_of_past_seed_ball_C11Q t s hst p
      r v hball hv0 hvr hclock trace (r / 20) (r / 2) (Real.exp (9 / 4)) (by positivity)
      (by linarith) hL hdist hmargin
    obtain rfl : b' = b := Subtype.ext (hb'.trans hb.symm)
    obtain ⟨aS, haSt, haS, hTr⟩ := hseed.2
    obtain rfl : aS = b' := Subtype.ext (haS.trans hb'.symm)
    intro y hy
    have hy' : riemannianEDistOf (H.stageMetric (H.activeStage s) ((t : ℝ) - v ^ 2))
        (trace.point (H.activeStage s) le_rfl (H.activeStage_mono hst)) y <
          ENNReal.ofReal (r / 20) := by
      rw [← hclock]
      exact hy
    obtain ⟨x', hx'R, A, _hA, hApt⟩ := hcov y hy'
    have hx'lt : ∀ ρ : ℝ, r / 2 < ρ →
        x' ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ := fun ρ hρ =>
      hx'R.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hρ)
    obtain ⟨B', hB'⟩ := hTr x' (hx'lt r (by linarith))
    refine ⟨x', hx'lt (3 * r / 5) (by linarith), B', hB', ?_⟩
    have hBA : B' = A := Subsingleton.elim _ _
    rw [hBA]
    exact hApt
  · -- 体积
    intro ϱ hϱ hϱr
    have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4) := by
      change riemannianEDistOf _ p p < ENNReal.ofReal (r / 4)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by positivity)
    exact (volume_lower_along_nearby_trace_P6B hseed hvolume hp s hst
      (by rw [hs]; nlinarith)).2 trace ϱ hϱ hϱr
  · -- 内部余量
    have hmargin : 3 * r / 40 < (3 * r / 4) / Real.exp (9 / 4) := by
      rw [lt_div_iff₀ hL]
      nlinarith
    obtain ⟨b', hb's, hb', hcore⟩ := H.exists_past_seed_core_traces_P6B t s hst p r v hball hv0
      hvr hclock trace (3 * r / 40) (Real.exp (9 / 4)) hL hdist hmargin
    obtain rfl : b' = b := Subtype.ext (hb'.trans hb.symm)
    intro y hy
    have hy' : riemannianEDistOf (H.stageMetric (H.activeStage s) ((t : ℝ) - v ^ 2))
        (trace.point (H.activeStage s) le_rfl (H.activeStage_mono hst)) y <
          ENNReal.ofReal (3 * r / 40) := by
      rw [← hclock]
      exact hy
    exact hcore y hy'

/-- consumer（G2）：K0（本文件）与 K6（G3）都已证，局部 κ 只剩 K1–K5 前提（同一 `nr`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₂ Λ C₄ v : ℝ → ℝ}
    (hK1 : ∀ n, AdmissibleLCalculus_C11Q (F.tower.history n))
    (hK2 : (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      LocalizedLCutoffInequality_C11Q F nr C₂)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hK4 : LocalizedLCutoffInequality_C11Q F nr C₂ → SurgeryActionBarrier_C11Q F δ α nr Λ →
      BoundedReducedLengthNearSeed_C11Q F δ α nr C₄)
    (hK5 : SeedPatchTransport_C11Q.{u} → (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      BoundedReducedLengthNearSeed_C11Q F δ α nr C₄ → SeedReducedVolumeLower_C11Q F δ α nr v) :
    LocalKappaSupply_P6B F δ α nr :=
  (localKappa_of_K0_to_K5_C11Q seedPatchTransport_C11Q hK1 hK2 hK3 hK4 hK5).toP6B

end GC.LongTime.Ch11
