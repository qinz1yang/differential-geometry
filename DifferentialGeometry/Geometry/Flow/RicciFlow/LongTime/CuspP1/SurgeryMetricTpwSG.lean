import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryMetricWindowSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryTransportSG
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback

/-!
# hmetric：`P^* g_t ≤ e^ε g_s`（G4c，S-A14-SURGERY）

窗口里的 `P_{s→t} = ι_t ∘ Φ_{s,t} ∘ ι_s⁻¹`（G2）与 G4b 的 `windowQuad` 接近引理合成：

* `window_hmetric_left_D_SG`：`s ↑ τ₀`（τ₀ 可以是 event 时刻）时
  `G(τ₀)(dΦ_{s,τ₀} u) ≤ e^ε G(s)(u)`（`D` 的紧集 `KD` 上一致）；
* `window_hmetric_right_D_SG`：`t ↓ τ₀` 时 `G(t)(dΦ_{τ₀,t} u) ≤ e^ε G(τ₀)(u)`；
* `window_tpw_metric_left_SG` / `_right_SG`：翻译到 `postStage` 上的 `P`：
  `∀ p ∈ ι_s '' KD, ∀ w, g_{τ₀}(dP w, dP w) ≤ e^ε g_s(w, w)`。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold Bundle DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g) (N : ℕ)
    (Fs Ls : Fin ((T.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
      Fs ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧ (T.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)

/-- `D` 上的拉回度量 `G(t) = ι_t^* postMetric t`。 -/
def windowMetric_SG (t : ℝ) (ht : t ∈ J) :
    SmoothRiemannianMetric (𝓡 3) ((T.history N).backwardSurvivorDomain Fs Ls hFL) :=
  DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph
    (postMetric T t) (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht)
    (windowEmbed_isLocalDiffeomorph_SG T N Fs Ls hFL J hJh hst t ht)
    (windowEmbed_injective_SG T N Fs Ls hFL J hJh hst t ht)

theorem windowMetric_inner_SG (t : ℝ) (ht : t ∈ J)
    (x : (T.history N).backwardSurvivorDomain Fs Ls hFL) (u : TangentSpace (𝓡 3) x) :
    (windowMetric_SG T N Fs Ls hFL J hJh hst t ht).inner x u u =
      windowQuad_SG T N Fs Ls hFL J hJh hst t ht x u :=
  DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_inner _ _ _ _ x u u

/-- D 上、左侧：`G(τ₀)(dΦ_{s,τ₀} u) ≤ e^ε G(s)(u)`，`KD ⊆ D` 紧集上对 `s ↑ τ₀` 一致。 -/
theorem window_hmetric_left_D_SG {τ₀ : ℝ} (hτ0 : 0 < τ₀) (hτ : τ₀ ∈ J) (hJo : IsOpen J)
    (Φ : ℝ → ℝ → (T.history N).backwardSurvivorDomain Fs Ls hFL →
      (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (hself : ∀ s y, Φ s s y = y)
    (hsm : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : (ℝ × ℝ) × (T.history N).backwardSurvivorDomain Fs Ls hFL => Φ q.1.1 q.1.2 q.2))
    {KD : Set ((T.history N).backwardSurvivorDomain Fs Ls hFL)} (hKD : IsCompact KD)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ s (hs : s ∈ J), s < τ₀ → |s - τ₀| < η → ∀ x ∈ KD, ∀ u : TangentSpace (𝓡 3) x,
      windowQuad_SG T N Fs Ls hFL J hJh hst τ₀ hτ (Φ s τ₀ x)
          (mfderiv (𝓡 3) (𝓡 3) (Φ s τ₀) x u) ≤
        Real.exp ε * windowQuad_SG T N Fs Ls hFL J hJh hst s hs x u := by
  have hε2 : 0 < ε / 2 := by linarith
  have hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × (T.history N).backwardSurvivorDomain Fs Ls hFL => Φ q.1 τ₀ q.2) :=
    hsm.comp ((contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd)
  obtain ⟨δ1, hδ1, h1⟩ := exists_near_id_quadratic_SG
    (windowMetric_SG T N Fs Ls hFL J hJh hst τ₀ hτ) (fun q => Φ q.1 τ₀ q.2) hf τ₀
    (hself τ₀) hKD hε2
  obtain ⟨δ2, hδ2, h2⟩ := window_quad_close_SG T N Fs Ls hFL J hJh hst hτ0 hτ hJo hKD hε2
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun s hs hlt hd x hx u => ?_⟩
  have a := h1 s (lt_of_lt_of_le hd (min_le_left _ _)) x hx u
  rw [windowMetric_inner_SG, windowMetric_inner_SG] at a
  have b := (h2 s hs (lt_of_lt_of_le hd (min_le_right _ _)) x hx u).2
  have hexp : Real.exp ε = Real.exp (ε / 2) * Real.exp (ε / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  calc _ ≤ Real.exp (ε / 2) * windowQuad_SG T N Fs Ls hFL J hJh hst τ₀ hτ x u := a
    _ ≤ Real.exp (ε / 2) * (Real.exp (ε / 2) * windowQuad_SG T N Fs Ls hFL J hJh hst s hs x u) :=
      mul_le_mul_of_nonneg_left b (Real.exp_pos _).le
    _ = _ := by ring

/-- D 上、右侧：`G(t)(dΦ_{τ₀,t} u) ≤ e^ε G(τ₀)(u)`，`KD ⊆ D` 紧集上对 `t ↓ τ₀` 一致。 -/
theorem window_hmetric_right_D_SG {τ₀ : ℝ} (hτ : τ₀ ∈ J)
    (Φ : ℝ → ℝ → (T.history N).backwardSurvivorDomain Fs Ls hFL →
      (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (hself : ∀ s y, Φ s s y = y)
    (hsm : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : (ℝ × ℝ) × (T.history N).backwardSurvivorDomain Fs Ls hFL => Φ q.1.1 q.1.2 q.2))
    {KD : Set ((T.history N).backwardSurvivorDomain Fs Ls hFL)} (hKD : IsCompact KD)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ t (ht : t ∈ J), τ₀ ≤ t → |t - τ₀| < η → ∀ x ∈ KD, ∀ u : TangentSpace (𝓡 3) x,
      windowQuad_SG T N Fs Ls hFL J hJh hst t ht (Φ τ₀ t x)
          (mfderiv (𝓡 3) (𝓡 3) (Φ τ₀ t) x u) ≤
        Real.exp ε * windowQuad_SG T N Fs Ls hFL J hJh hst τ₀ hτ x u := by
  have hε2 : 0 < ε / 2 := by linarith
  have hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × (T.history N).backwardSurvivorDomain Fs Ls hFL => Φ τ₀ q.1 q.2) :=
    hsm.comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)
  have hKc : IsCompact ((fun q : ℝ × (T.history N).backwardSurvivorDomain Fs Ls hFL =>
      Φ τ₀ q.1 q.2) '' (Icc τ₀ (τ₀ + 1) ×ˢ KD)) :=
    (isCompact_Icc.prod hKD).image hf.continuous
  obtain ⟨δ1, hδ1, h1⟩ := exists_near_id_quadratic_SG
    (windowMetric_SG T N Fs Ls hFL J hJh hst τ₀ hτ) (fun q => Φ τ₀ q.1 q.2) hf τ₀
    (hself τ₀) hKD hε2
  obtain ⟨δ2, hδ2, h2⟩ := window_quad_right_close_SG T N Fs Ls hFL J hJh hst hτ hKc hε2
  refine ⟨min (min δ1 δ2) 1, lt_min (lt_min hδ1 hδ2) one_pos, fun t ht hle hd x hx u => ?_⟩
  have hd1 : |t - τ₀| < δ1 := lt_of_lt_of_le hd ((min_le_left _ _).trans (min_le_left _ _))
  have hd2 : |t - τ₀| < δ2 := lt_of_lt_of_le hd ((min_le_left _ _).trans (min_le_right _ _))
  have hd3 : t - τ₀ < 1 := lt_of_le_of_lt (le_abs_self _) (lt_of_lt_of_le hd (min_le_right _ _))
  have a := h1 t hd1 x hx u
  rw [windowMetric_inner_SG, windowMetric_inner_SG] at a
  have b := (h2 t ht hle hd2 _ ⟨(t, x), ⟨⟨hle, by linarith⟩, hx⟩, rfl⟩
    (mfderiv (𝓡 3) (𝓡 3) (Φ τ₀ t) x u)).1
  have hexp : Real.exp ε = Real.exp (ε / 2) * Real.exp (ε / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  calc _ ≤ Real.exp (ε / 2) * windowQuad_SG T N Fs Ls hFL J hJh hst τ₀ hτ (Φ τ₀ t x)
          (mfderiv (𝓡 3) (𝓡 3) (Φ τ₀ t) x u) := b
    _ ≤ Real.exp (ε / 2) * (Real.exp (ε / 2) * windowQuad_SG T N Fs Ls hFL J hJh hst τ₀ hτ x u) :=
      mul_le_mul_of_nonneg_left a (Real.exp_pos _).le
    _ = _ := by ring

/-- 沿点相等改基点（`TangentSpace` 与基点无关，`inner` 只依赖基点）。 -/
theorem inner_congr_point_SG {X : OrientedThreeStage.{u}} (m : X.Metric) {a b : X.Carrier}
    (h : a = b) (v : TangentSpace ThreeModel a) :
    m.inner a v v = m.inner b v v := by
  subst h
  rfl

/-- `P_{s→t}` 在 `ι_s x` 处的切映射：`dP (dι_s u) = dι_t (dΦ u)`（`E` 里的向量相等）。 -/
theorem window_transport_mfderiv_SG
    (Φ : ℝ → ℝ → (T.history N).backwardSurvivorDomain Fs Ls hFL →
      (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (hsm : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : (ℝ × ℝ) × (T.history N).backwardSurvivorDomain Fs Ls hFL => Φ q.1.1 q.1.2 q.2))
    (s t : ℝ) (hs : s ∈ J) (ht : t ∈ J)
    (w₀ : (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (x : (T.history N).backwardSurvivorDomain Fs Ls hFL) (u : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3) (windowTransport_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀)
        (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs x)
        (mfderiv (𝓡 3) (𝓡 3) (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs) x u) =
      mfderiv (𝓡 3) (𝓡 3) (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht) (Φ s t x)
        (mfderiv (𝓡 3) (𝓡 3) (Φ s t) x u) := by
  have hPs := windowTransport_contMDiffOn_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀ hsm
  have hP : MDifferentiableAt (𝓡 3) (𝓡 3)
      (windowTransport_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀)
      (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs x) :=
    (hPs.contMDiffAt
      ((windowEmbed_isOpenEmbedding_SG T N Fs Ls hFL J hJh hst s hs).isOpen_range.mem_nhds
        ⟨x, rfl⟩)).mdifferentiableAt (by simp)
  have hιs : MDifferentiableAt (𝓡 3) (𝓡 3) (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs) x :=
    ((windowEmbed_contMDiff_SG T N Fs Ls hFL J hJh hst s hs).contMDiffAt).mdifferentiableAt
      (by simp)
  have hιt : MDifferentiableAt (𝓡 3) (𝓡 3) (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht)
      (Φ s t x) :=
    ((windowEmbed_contMDiff_SG T N Fs Ls hFL J hJh hst t ht).contMDiffAt).mdifferentiableAt
      (by simp)
  have hΦx : MDifferentiableAt (𝓡 3) (𝓡 3) (Φ s t) x :=
    ((isotopy_slice_contMDiff_SG T N Fs Ls hFL Φ s t hsm).contMDiffAt).mdifferentiableAt
      (by simp)
  have hfun : (windowTransport_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀) ∘
      (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs) =
      (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht) ∘ (Φ s t) :=
    funext fun y => windowTransport_apply_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀ y
  have h1 := mfderiv_comp x hP hιs
  have h2 : mfderiv (𝓡 3) (𝓡 3) ((windowEmbed_SG T N Fs Ls hFL J hJh hst t ht) ∘ (Φ s t)) x =
      (mfderiv (𝓡 3) (𝓡 3) (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht) (Φ s t x)).comp
        (mfderiv (𝓡 3) (𝓡 3) (Φ s t) x) := mfderiv_comp x hιt hΦx
  rw [hfun] at h1
  have h3 := congrArg (fun L => L u) (h1.symm.trans h2)
  exact h3

/-- `P_{s→t}` 下的二次型：`g_t(dP (dι_s u)) = G(t)(dΦ_{s,t} u)`（`windowQuad` 的形式）。 -/
theorem window_transport_quad_SG
    (Φ : ℝ → ℝ → (T.history N).backwardSurvivorDomain Fs Ls hFL →
      (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (hsm : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : (ℝ × ℝ) × (T.history N).backwardSurvivorDomain Fs Ls hFL => Φ q.1.1 q.1.2 q.2))
    (s t : ℝ) (hs : s ∈ J) (ht : t ∈ J)
    (w₀ : (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (x : (T.history N).backwardSurvivorDomain Fs Ls hFL) (u : TangentSpace (𝓡 3) x) :
    (postMetric T t).inner
        (windowTransport_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀
          (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs x))
        (mfderiv (𝓡 3) (𝓡 3) (windowTransport_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀)
          (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs x)
          (mfderiv (𝓡 3) (𝓡 3) (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs) x u))
        (mfderiv (𝓡 3) (𝓡 3) (windowTransport_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀)
          (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs x)
          (mfderiv (𝓡 3) (𝓡 3) (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs) x u)) =
      windowQuad_SG T N Fs Ls hFL J hJh hst t ht (Φ s t x) (mfderiv (𝓡 3) (𝓡 3) (Φ s t) x u) := by
  rw [window_transport_mfderiv_SG T N Fs Ls hFL J hJh hst Φ hsm s t hs ht w₀ x u]
  exact inner_congr_point_SG (postMetric T t)
    (windowTransport_apply_SG T N Fs Ls hFL J hJh hst Φ s t hs ht w₀ x) _

/-- 每个切向量都是 `dι_s u`（`ι_s` 是 local diffeo）。 -/
theorem window_mfderiv_surj_SG (s : ℝ) (hs : s ∈ J)
    (x : (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (w : TangentSpace (𝓡 3) (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs x)) :
    ∃ u : TangentSpace (𝓡 3) x,
      mfderiv (𝓡 3) (𝓡 3) (windowEmbed_SG T N Fs Ls hFL J hJh hst s hs) x u = w := by
  have hl := windowEmbed_isLocalDiffeomorph_SG T N Fs Ls hFL J hJh hst s hs
  let e := hl.mfderivToContinuousLinearEquiv (by decide) x
  exact ⟨e.symm w, e.apply_symm_apply w⟩

/-- **hmetric（左）**：`s ↑ τ₀` 时，`P := P_{s→τ₀}` 在 `ι_s '' KD`（`KD ⊆ D` 紧）上
`g_{τ₀}(dP w, dP w) ≤ e^ε g_s(w, w)`，`η` 对 `KD`、`ε` 一致（与 `w₀`、`s` 无关）。 -/
theorem window_tpw_metric_left_SG {τ₀ : ℝ} (hτ0 : 0 < τ₀) (hτ : τ₀ ∈ J) (hJo : IsOpen J)
    (Φ : ℝ → ℝ → (T.history N).backwardSurvivorDomain Fs Ls hFL →
      (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (hself : ∀ s y, Φ s s y = y)
    (hsm : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : (ℝ × ℝ) × (T.history N).backwardSurvivorDomain Fs Ls hFL => Φ q.1.1 q.1.2 q.2))
    {KD : Set ((T.history N).backwardSurvivorDomain Fs Ls hFL)} (hKD : IsCompact KD)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ s (hs : s ∈ J), s < τ₀ → |s - τ₀| < η →
      ∀ w₀ : (T.history N).backwardSurvivorDomain Fs Ls hFL,
      ∀ p ∈ windowEmbed_SG T N Fs Ls hFL J hJh hst s hs '' KD, ∀ w : TangentSpace (𝓡 3) p,
        (postMetric T τ₀).inner (windowTransport_SG T N Fs Ls hFL J hJh hst Φ s τ₀ hs hτ w₀ p)
            (mfderiv (𝓡 3) (𝓡 3) (windowTransport_SG T N Fs Ls hFL J hJh hst Φ s τ₀ hs hτ w₀) p w)
            (mfderiv (𝓡 3) (𝓡 3) (windowTransport_SG T N Fs Ls hFL J hJh hst Φ s τ₀ hs hτ w₀) p
              w) ≤
          Real.exp ε * (postMetric T s).inner p w w := by
  obtain ⟨η, hη, h⟩ := window_hmetric_left_D_SG T N Fs Ls hFL J hJh hst hτ0 hτ hJo Φ hself hsm
    hKD hε
  refine ⟨η, hη, fun s hs hlt hd w₀ p hp w => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨u, rfl⟩ := window_mfderiv_surj_SG T N Fs Ls hFL J hJh hst s hs x w
  rw [window_transport_quad_SG T N Fs Ls hFL J hJh hst Φ hsm s τ₀ hs hτ w₀ x u]
  exact h s hs hlt hd x hx u

/-- **hmetric（右）**：`t ↓ τ₀` 时，`P := P_{τ₀→t}` 在 `ι_{τ₀} '' KD` 上
`g_t(dP w, dP w) ≤ e^ε g_{τ₀}(w, w)`。 -/
theorem window_tpw_metric_right_SG {τ₀ : ℝ} (hτ : τ₀ ∈ J)
    (Φ : ℝ → ℝ → (T.history N).backwardSurvivorDomain Fs Ls hFL →
      (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (hself : ∀ s y, Φ s s y = y)
    (hsm : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : (ℝ × ℝ) × (T.history N).backwardSurvivorDomain Fs Ls hFL => Φ q.1.1 q.1.2 q.2))
    {KD : Set ((T.history N).backwardSurvivorDomain Fs Ls hFL)} (hKD : IsCompact KD)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ t (ht : t ∈ J), τ₀ ≤ t → |t - τ₀| < η →
      ∀ w₀ : (T.history N).backwardSurvivorDomain Fs Ls hFL,
      ∀ p ∈ windowEmbed_SG T N Fs Ls hFL J hJh hst τ₀ hτ '' KD, ∀ w : TangentSpace (𝓡 3) p,
        (postMetric T t).inner (windowTransport_SG T N Fs Ls hFL J hJh hst Φ τ₀ t hτ ht w₀ p)
            (mfderiv (𝓡 3) (𝓡 3) (windowTransport_SG T N Fs Ls hFL J hJh hst Φ τ₀ t hτ ht w₀) p w)
            (mfderiv (𝓡 3) (𝓡 3) (windowTransport_SG T N Fs Ls hFL J hJh hst Φ τ₀ t hτ ht w₀) p
              w) ≤
          Real.exp ε * (postMetric T τ₀).inner p w w := by
  obtain ⟨η, hη, h⟩ := window_hmetric_right_D_SG T N Fs Ls hFL J hJh hst hτ Φ hself hsm hKD hε
  refine ⟨η, hη, fun t ht hle hd w₀ p hp w => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨u, rfl⟩ := window_mfderiv_surj_SG T N Fs Ls hFL J hJh hst τ₀ hτ x w
  rw [window_transport_quad_SG T N Fs Ls hFL J hJh hst Φ hsm τ₀ t hτ ht w₀ x u]
  exact h t ht hle hd x hx u

end GC.LongTime.CuspP1
