import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingDepthExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingTracedLate_P6LL

/-!
# `hextend`（`CrossingDepthExtension:16`）的 late-records + hybrid 形（O-CH11-P6LATE G1 (2)，`_P6LL`）

`depthExtendable_add_of_windowAnchorBound` 的局部化副本：数据前提只经 (1)
`exists_eventually_isTracedRegion_extendAt_of_scalar_le_along_traces` 被消费，换成 (1) 的 `_late_P6LL`
版；数据前提块同 (1)（late records / `hcan` / `hscale` / `hnot` 展开形 / `hT₀`，full family
`recordsF` + `hδF`，时刻 0 HI `a₀` 代替 `hinit`，`p₀` 去掉）。证明其余逐字。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **`_P6LL`（(2)：`hextend`，late records + hybrid）**：`CrossingDepthExtension:16` 的副本。 -/
theorem depthExtendable_add_of_windowAnchorBound_late_P6LL
    {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (H n).toHistory i (pF n))
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hHI : ∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((H n).initialMetric 0) x)
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      (pF n).delta ((H n).time i.succ) ≤ δb n)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - (H n).time j.succ ≤ θcap n * (((records n j hj).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ t n - B / (G n).flow.scalar (t n) (y n))
    (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t n) atTop atTop)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {Tstar M : ℝ} (hT : 0 < Tstar) (hM : 0 ≤ M) :
    let K : ℕ → RetainedCoreHistory.{u} := fun n =>
      (H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)
    let τ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon := fun n =>
      (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)
    ∀ ŷ : ∀ n, ((K n).toHistory.stageAt (τ n)).Carrier, (∀ n, HEq (ŷ n) (y n)) →
    (∀ T : ℝ, 0 < T → T < Tstar → ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
      (fun n => (G n).flow.scalar (t n) (y n)) σ T) →
    (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((K (σ i)).toHistory.stageMetric
          ((K (σ i)).toHistory.activeStage (τ (σ i))) (τ (σ i))) (ŷ (σ i))
          (A / Real.sqrt ((G (σ i)).flow.scalar (t (σ i)) (y (σ i)))),
      ∀ (w : Icc (0 : ℝ) (K (σ i)).toHistory.horizon),
        (w : ℝ) = t (σ i) - T' / (G (σ i)).flow.scalar (t (σ i)) (y (σ i)) →
      ∀ (hwt : w ≤ τ (σ i))
        (Bt : BackwardPointTrace (K (σ i)).toHistory
          ((K (σ i)).toHistory.activeStage w)
          ((K (σ i)).toHistory.activeStage (τ (σ i)))
          ((K (σ i)).toHistory.activeStage_mono hwt) x),
        metricScalarAt ((K (σ i)).toHistory.stageMetric
            ((K (σ i)).toHistory.activeStage w) w)
          (Bt.point ((K (σ i)).toHistory.activeStage w) le_rfl
            ((K (σ i)).toHistory.activeStage_mono hwt)) ≤
          M * (G (σ i)).flow.scalar (t (σ i)) (y (σ i))) →
    ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
      (fun n => (G n).flow.scalar (t n) (y n)) σ
      (Tstar + 1 / (32 * ((Ctime : ℝ) + 1) * (M + 1))) := by
  intro K τ ŷ hŷ hext hanc A hA
  have hRpos : ∀ n, 0 < (G n).flow.scalar (t n) (y n) := fun n =>
    (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  have hC0 : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
  set Tg : ℝ := Tstar + 1 / (32 * ((Ctime : ℝ) + 1) * (M + 1)) with hTg
  set Δ : ℝ := 1 / (8 * ((Ctime : ℝ) + 1) * (M + 1)) with hΔ
  have hΔ0 : 0 < Δ := by positivity
  set T' : ℝ := max (Tstar - Δ / 2) (Tstar / 2) with hT'
  have hT'0 : 0 < T' := lt_max_of_lt_right (half_pos hT)
  have hT'lt : T' < Tstar := max_lt (by linarith) (by linarith)
  have hTgΔ : Tg = Tstar + Δ / 4 := by
    rw [hTg, hΔ]
    field_simp
    ring
  have hgap : Tg - T' ≤ 3 * Δ / 4 := by
    have := le_max_left (Tstar - Δ / 2) (Tstar / 2)
    linarith
  have hTg0 : 0 < Tg := by positivity
  have hCΔ : 4 * (Ctime : ℝ) * (M + 1) * Δ ≤ 1 / 2 := by
    rw [hΔ]
    rw [show 4 * (Ctime : ℝ) * (M + 1) * (1 / (8 * ((Ctime : ℝ) + 1) * (M + 1))) =
      (Ctime : ℝ) / (2 * ((Ctime : ℝ) + 1)) by field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨K₁, hK₁, hev1⟩ := hext T' hT'0 hT'lt A hA
  have hev2 := hanc T' hT'0 hT'lt A hA
  obtain ⟨K₀, hK₀, hev3⟩ :=
    RetainedCoreHistory.exists_eventually_isTracedRegion_extendAt_late_P6LL
      hphi recordsF ha₀ hHI hend hGi hcan hδF hqcan hpar hscale hθcap hpinch hslab hat hts hderG hqR
      hnot hT₀
      (A := A) (T := Tg) (Q := 9 * K₁ + 4 * (M + 1)) hA hTg0 (by linarith)
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [hev1, hev2, hσ.tendsto_atTop.eventually hev3,
    hσ.tendsto_atTop.eventually (hRt.eventually_gt_atTop Tg)] with i h1 h2 h3 h4
  generalize σ i = n at h1 h2 h3 h4 ⊢
  have hR := hRpos n
  have hut0 : 0 ≤ t n - Tg / (G n).flow.scalar (t n) (y n) := by
    rw [sub_nonneg, div_le_iff₀ hR]
    linarith
  let uu : Icc (0 : ℝ) (K n).toHistory.horizon :=
    ⟨t n - Tg / (G n).flow.scalar (t n) (y n), hut0,
      show t n - Tg / (G n).flow.scalar (t n) (y n) ≤ t n from
        sub_le_self _ (div_pos hTg0 hR).le⟩
  refine h3 (ŷ n) (hŷ n) uu rfl ?_
  intro x hx w huw hwt B v hwv hvt
  obtain ⟨-, -, a, hat', ha, htr⟩ := h1
  by_cases hva : a ≤ v
  · obtain ⟨A₁, hA₁⟩ := htr x hx
    have hpt := BackwardPointTrace.point_unique
      (B.restrictFirst ((K n).toHistory.activeStage_mono hwv)
        ((K n).toHistory.activeStage_mono hvt))
      (A₁.restrictFirst ((K n).toHistory.activeStage_mono hva)
        ((K n).toHistory.activeStage_mono hvt))
      ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt)
    have hnorm := hA₁.1 v hva hvt
    have hsc := scalar_abs_le_rm ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
      (A₁.point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono hva)
        ((K n).toHistory.activeStage_mono hvt))
    have hfin : (Module.finrank ℝ (TangentSpace ThreeModel
        (A₁.point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono hva)
          ((K n).toHistory.activeStage_mono hvt))) : ℝ) = 3 := by
      change ((Module.finrank ℝ ThreeSpace : ℕ) : ℝ) = 3
      simp [ThreeSpace]
    have hsq : Real.sqrt (normSq0S ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
        (A₁.point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono hva)
          ((K n).toHistory.activeStage_mono hvt)) 4
        (metricRm04At ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          (A₁.point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono hva)
            ((K n).toHistory.activeStage_mono hvt)))) ≤
        K₁ * (G n).flow.scalar (t n) (y n) :=
      (Real.sqrt_le_sqrt hnorm).trans (Real.sqrt_sq (by positivity)).le
    rw [hfin] at hsc
    refine (le_of_eq (congrArg _ hpt)).trans ((le_abs_self _).trans (hsc.trans ?_))
    nlinarith
  · have hva' : v < a := lt_of_not_ge hva
    have hwa : w ≤ a := hwv.trans hva'.le
    have hanchor := h2 x hx a ha hat'
      (B.restrictFirst ((K n).toHistory.activeStage_mono hwa)
        ((K n).toHistory.activeStage_mono hat'))
    have hdin := (H n).derivativeBound_inputs_extendAt (hend n) (G n) (hGi n) (hat n) (hts n)
      (by linarith [hqcan n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (hslab n) (hderG n)
    have haw : (a : ℝ) - w ≤ (Tg - T') / (G n).flow.scalar (t n) (y n) := by
      have hw : t n - Tg / (G n).flow.scalar (t n) (y n) ≤ (w : ℝ) := huw
      have ha' : (a : ℝ) = t n - T' / (G n).flow.scalar (t n) (y n) := ha
      calc (a : ℝ) - w ≤ (t n - T' / (G n).flow.scalar (t n) (y n)) -
            (t n - Tg / (G n).flow.scalar (t n) (y n)) := by rw [ha']; linarith
        _ = (Tg - T') / (G n).flow.scalar (t n) (y n) := by ring
    have haw0 : 0 ≤ (a : ℝ) - w := sub_nonneg.mpr hwa
    have htime : ((2 * Ctime : ℝ≥0) : ℝ) * (2 * (M + 1) * (G n).flow.scalar (t n) (y n)) *
        ((a : ℝ) - w) ≤ 1 / 2 := by
      push_cast
      have e1 : 2 * (Ctime : ℝ) * (2 * (M + 1) * (G n).flow.scalar (t n) (y n)) *
          ((Tg - T') / (G n).flow.scalar (t n) (y n)) = 4 * (Ctime : ℝ) * (M + 1) * (Tg - T') := by
        field_simp
        ring
      have e2 : 2 * (Ctime : ℝ) * (2 * (M + 1) * (G n).flow.scalar (t n) (y n)) *
          ((a : ℝ) - w) ≤ 2 * (Ctime : ℝ) * (2 * (M + 1) * (G n).flow.scalar (t n) (y n)) *
          ((Tg - T') / (G n).flow.scalar (t n) (y n)) :=
        mul_le_mul_of_nonneg_left haw (by positivity)
      have e3 : 4 * (Ctime : ℝ) * (M + 1) * (Tg - T') ≤ 4 * (Ctime : ℝ) * (M + 1) * Δ := by
        have : 0 ≤ 4 * (Ctime : ℝ) * (M + 1) := by positivity
        nlinarith
      linarith
    have hstep := (K n).scalar_le_two_mul_of_backwardPointTrace_of_scalar_le_at
      (Ctime := 2 * Ctime) (qcan := 2 * qcan n) (M := 2 * (M + 1) * (G n).flow.scalar (t n) (y n))
      hwa hat' B hdin.1 hdin.2.1 hdin.2.2 (by positivity) (by nlinarith [hqR n])
      (hanchor.trans (by nlinarith)) htime v hwv hva'.le
    exact hstep.trans (by nlinarith)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
