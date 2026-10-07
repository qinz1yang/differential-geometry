import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingWindowAnchorBound_P6L

/-!
# survivor-block 两引理的 **block 形**（O-CH11-P6ANCH2 G2，后缀 `_P6L2`）

`CrossingWindowAnchorBound_P6L` 的
`exists_eventually_neckAlternatives_or_isCompact_of_survivor_blocks_P6L`
（`hwit`）与 `eventually_abs_derivWithin_scalar_le_of_survivor_blocks_P6L`（`hstage`）的证明体只在
block `(Dw, Tw) = (k + 3, τ k)` 取 trace-local 前提。这里把 `∀ Dw Tw` 前提换成 block 形
`∀ k, ∀ᶠ n, …(k + 3, τ k)…`，证明体逐字（删去只服务于该处的 `hk3` / `hτ`）。用途：条件形 driver
（`CrossingDepthExtension2_P6L2`）只在已控深度 `τ k < Tstar` 上提供 witness / 导数（深度自举）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.scaleMetric_restrictOpen
  ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen
  ObservedHistory.riemannianBallOf_scaleMetric_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

universe u

/-- 照抄 `CrossingWindowAnchorBound_P6L` 的 private `closedBall_one_subset_of_ball_eq_window_P6L`。 -/
private theorem closedBall_one_subset_of_ball_eq_window_P6L2 {M : Type*} [TopologicalSpace M]
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


open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace ObservedHistory

/-- `exists_eventually_neckAlternatives_or_isCompact_of_survivor_blocks_P6L` 的 **block 形**（`_P6L2`）：
`hwit` 只在 block `(k + 3, τ k)` 取值（证明体本来只用这一处），其余逐字。 -/
theorem exists_eventually_neckAlternatives_or_isCompact_of_survivor_blocks_P6L2 :
    ∃ D : ℝ, 0 < D ∧ ∀ {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
      {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n} {τ c : ℕ → ℝ}
      {W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens ((Hs n).stageAt (ts n)).Carrier}
      {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)},
      (∀ k, 0 < τ k) → (∀ k, c k ≤ τ k) →
      (∀ k : ℕ, ∀ᶠ n in atTop, (W k n : Set ((Hs n).stageAt (ts n)).Carrier) =
        riemannianBallOf (scaleMetric (R n) (hR n)
          ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))) (ys n) ((k + 3 : ℕ) : ℝ)) →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-τ k) 0,
        (ts n : ℝ) + s / R n ∈ (Hs n).stageDomain ((Hs n).activeStage (ts n)) →
        h k n s = scaleMetric (R n) (hR n)
          (((Hs n).stageMetric ((Hs n).activeStage (ts n)) ((ts n : ℝ) + s / R n)).restrictOpen
            (W k n))) →
      (∀ k : ℕ, ∀ᶠ n in atTop,
        ∃ (a : Icc (0 : ℝ) (Hs n).horizon) (hat : a ≤ ts n), (a : ℝ) = ts n - τ k / R n ∧
          ∃ f : (j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n))) →
              W k n → ((Hs n).stage j.val).Carrier,
            ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
              (∀ j, Function.Injective (f j)) ∧
              (∀ (i : Fin (Hs n).eventCount) (hi : (Hs n).activeStage a ≤ i.castSucc)
                  (hl : i.succ ≤ (Hs n).activeStage (ts n)), ∀ x : W k n,
                ((Hs n).event i).RegularCrossing
                  (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                  (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
              (∀ x : W k n,
                f ⟨(Hs n).activeStage (ts n), (Hs n).activeStage_mono hat, le_rfl⟩ x = x.val) ∧
              ∀ s ∈ Icc (-τ k) 0,
                ∀ j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n)),
                  (ts n : ℝ) + s / R n ∈ (Hs n).stageDomain j.val →
                    h k n s = scaleMetric (R n) (hR n)
                      (localPullMetric ((Hs n).stageMetric j.val ((ts n : ℝ) + s / R n)) (f j)
                        (hf j))) →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, ∀ (x : W k n)
        (u : TangentSpace ThreeModel x),
        (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u) →
      ∀ {qs : ℕ → ℝ} {E : ℕ → Set ℝ} {eps C1 C2 C qW : ℝ}, 0 < eps → 1 ≤ C →
      max (2 * |C1|) C2 ≤ C → (∀ n, qs n ≤ R n * qW) →
      (Real.exp 1 * (C + (D + 2 * eps⁻¹) * Real.sqrt C)) ^ 2 ≤ qW →
      (∀ k : ℕ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - τ k / R n ≤ v →
        (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) eps C1 C2
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart eps) →
      (∀ n s, s ≤ 0 → s ∉ E n → (ts n : ℝ) + s / R n < ts n ∧
        ∀ i, (ts n : ℝ) + s / R n ≠ (Hs n).time i) →
      ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, s ∉ E n → ∀ z : W k n,
        (z : ((Hs n).stageAt (ts n)).Carrier) ∈ riemannianClosedBallOf (scaleMetric (R n) (hR n)
          ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))) (ys n) ((k + 1 : ℕ) : ℝ) →
        qW < metricScalarAt (h k n s) z →
        Nonempty (SpatialNeck (h k n s) eps z) ∨
          (∃ w : W k n, Nonempty (SpatialNeck (h k n s) eps w) ∧
            metricScalarAt (h k n s) z ≤ C * metricScalarAt (h k n s) w ∧
            metricScalarAt (h k n s) w ≤ C * metricScalarAt (h k n s) z ∧
            riemannianEDistOf (h k n s) z w <
              ENNReal.ofReal (C / Real.sqrt (metricScalarAt (h k n s) z))) ∨
          IsCompact (connectedComponent z) := by
  obtain ⟨D, hD, hB6⟩ := exists_neckAlternatives_or_isCompact_of_survivor_maps_P6L.{u}
  refine ⟨D, hD, ?_⟩
  intro Hs ts ys R hR τ c W h hτ hcτ hWset hcur hsurv hlow qs E eps C1 C2 C qW heps hC1 hC0
    hqs hqWsq hwit hE k
  have hC00 : 0 ≤ max (2 * |C1|) C2 := le_max_of_le_left (by positivity)
  have hDe : 0 ≤ D + 2 * eps⁻¹ := by have := inv_pos.mpr heps; linarith
  have hxnn : 0 ≤ Real.exp 1 * (C + (D + 2 * eps⁻¹) * Real.sqrt C) :=
    mul_nonneg (Real.exp_pos 1).le
      (add_nonneg (by linarith) (mul_nonneg hDe (Real.sqrt_nonneg _)))
  have hqW0 : 0 ≤ qW := (sq_nonneg _).trans hqWsq
  have he2 : Real.exp 1 ^ 2 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  filter_upwards [hWset k, hcur k, hsurv k, hlow k, hwit k] with n hWn hcn hsn hlown
    hwn s hs hsE z hz hqz
  obtain ⟨a, hat, ha, fs, hfs, hinj, hcross, hlast, hp⟩ := hsn
  obtain ⟨hst₀, hne⟩ := hE n s hs.2 hsE
  have hsτ : s ∈ Icc (-τ k) 0 := ⟨by linarith [hs.1, hcτ k], hs.2⟩
  have hzpos : 0 < metricScalarAt (h k n s) z := hqW0.trans_lt hqz
  have hcpt : IsCompact (riemannianClosedBallOf (h k n 0) z 1) := by
    have hdom : ((ts n : ℝ) + 0 / R n) ∈ (Hs n).stageDomain ((Hs n).activeStage (ts n)) := by
      simpa using (Hs n).activeStage_mem (ts n)
    rw [hcn 0 ⟨neg_nonpos.mpr (hτ k).le, le_rfl⟩ hdom, zero_div, add_zero,
      ObservedHistory.scaleMetric_restrictOpen]
    exact ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen _ _ _ _
      (closedBall_one_subset_of_ball_eq_window_P6L2 _ _ _ k hWn _ hz)
  have hsmall : Real.exp 1 * (max (2 * |C1|) C2 + (D + 2 * eps⁻¹) *
      Real.sqrt (max (2 * |C1|) C2)) < Real.sqrt (metricScalarAt (h k n s) z) := by
    refine lt_of_le_of_lt ?_ ((Real.lt_sqrt hxnn).mpr (hqWsq.trans_lt hqz))
    gcongr
  -- 局部化：survivor 点形 witness 由 trace-local `hwit` 经 survivor maps 的 backward trace 给出
  have hwitS : ∀ v : Icc (0 : ℝ) (Hs n).horizon, (v : ℝ) < ts n →
      (Hs n).time ((Hs n).activeStage v) < v →
      ∀ (hav : a ≤ v) (hvt : v ≤ ts n) (z' : W k n),
        qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (fs ⟨(Hs n).activeStage v, (Hs n).activeStage_mono hav,
            (Hs n).activeStage_mono hvt⟩ z') →
        ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) eps C1 C2
            (fs ⟨(Hs n).activeStage v, (Hs n).activeStage_mono hav,
              (Hs n).activeStage_mono hvt⟩ z'),
          Wt.capTubeHasNeckChart eps := by
    intro v hvlt hreg hav hvt z' hq'
    obtain ⟨tr, htr⟩ := exists_backwardPointTrace_of_survivor_maps_P6L (Hs n) (ts n) a hat fs
      hcross hlast v hav hvt z'
    have hz'B : (z' : ((Hs n).stageAt (ts n)).Carrier) ∈
        riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
      rw [← ObservedHistory.riemannianBallOf_scaleMetric_eq _ (hR n), ← hWn]
      exact z'.property
    have hva : (ts n : ℝ) - τ k / R n ≤ v := by rw [← ha]; exact hav
    have hw := hwn z' hz'B v hvt hva hvlt hreg tr (by rw [htr]; exact hq')
    rw [htr] at hw
    exact hw
  have key := hB6 (Hs n) (ts n) (hR n) (θ := τ k) (t₀ := ts n) (eps := eps) (C1 := C1)
    (C2 := C2) (W := W k n) (h := h k n) (hqs n) (Real.exp_pos 1) a ha fs hfs hinj hp
    hwitS hsτ hst₀
    (fun hv => lt_of_le_of_ne (ObservedHistory.activeStage_time_le _ _)
      fun heq => hne _ heq.symm) z hcpt
    (fun y' _ u => by rw [he2]; exact hlown s hs y' u) hqz hsmall
  rcases key with h1 | ⟨w, hw, h2, h3, h4⟩ | h5
  · exact Or.inl h1
  · have hw0 : 0 < metricScalarAt (h k n s) w := by
      by_contra hneg
      have := mul_nonpos_of_nonneg_of_nonpos hC00 (not_lt.mp hneg)
      linarith
    refine Or.inr (Or.inl ⟨w, hw, h2.trans (mul_le_mul_of_nonneg_right hC0 hw0.le),
      h3.trans (mul_le_mul_of_nonneg_right hC0 hzpos.le), h4.trans_le ?_⟩)
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hC0 (Real.sqrt_nonneg _))
  · exact Or.inr (Or.inr h5)

variable {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
  {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n} {τ : ℕ → ℝ}
  {W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens ((Hs n).stageAt (ts n)).Carrier}
  {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)}

/-- `eventually_abs_derivWithin_scalar_le_of_survivor_blocks_P6L` 的 **block 形**（`_P6L2`）：
`hstage` 只在 block `(k + 3, τ k)` 取值（证明体本来只用这一处；`hτ` 随之不再需要）。 -/
theorem eventually_abs_derivWithin_scalar_le_of_survivor_blocks_P6L2
    (hWset : ∀ k : ℕ, ∀ᶠ n in atTop, (W k n : Set ((Hs n).stageAt (ts n)).Carrier) =
      riemannianBallOf (scaleMetric (R n) (hR n)
        ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))) (ys n) ((k + 3 : ℕ) : ℝ))
    (hsurv : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∃ (a : Icc (0 : ℝ) (Hs n).horizon) (hat : a ≤ ts n), (a : ℝ) = ts n - τ k / R n ∧
        ∃ f : (j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n))) →
            W k n → ((Hs n).stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin (Hs n).eventCount) (hi : (Hs n).activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ (Hs n).activeStage (ts n)), ∀ x : W k n,
              ((Hs n).event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : W k n,
              f ⟨(Hs n).activeStage (ts n), (Hs n).activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∀ s ∈ Icc (-τ k) 0,
              ∀ j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n)),
                (ts n : ℝ) + s / R n ∈ (Hs n).stageDomain j.val →
                  h k n s = scaleMetric (R n) (hR n)
                    (localPullMetric ((Hs n).stageMetric j.val ((ts n : ℝ) + s / R n)) (f j)
                      (hf j)))
    {E : ℕ → Set ℝ} {Ct qD : ℝ} (hCt : 0 ≤ Ct) {qst : ℕ → ℝ} (hqD : ∀ n, qst n ≤ R n * qD)
    (hstage : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - τ k / R n ≤ v →
      (v : ℝ) < ts n → (Hs n).time ((Hs n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
        ((Hs n).activeStage_mono hvt) x,
        qst n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
        |derivWithin (fun v' => metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v')
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)))
          (Iic (v : ℝ)) v| ≤
          Ct * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ^ 2)
    (hE : ∀ n s, s ≤ 0 → s ∉ E n → ∀ i, (ts n : ℝ) + s / R n ≠ (Hs n).time i) :
    ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-τ k) 0, s ∉ E n →
      ∀ z : W k n, qD < metricScalarAt (h k n s) z →
        |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
          Ct * metricScalarAt (h k n s) z ^ 2 := by
  intro k
  filter_upwards [hWset k, hsurv k, hstage k] with n hWn hn hsn s hs hsE z hz
  obtain ⟨a, hat, ha, fs, hfs, -, hcross, hlast, hp⟩ := hn
  have hne := hE n s hs.2.le hsE
  have hst : (ts n : ℝ) + s / R n < ts n := by
    have := div_neg_of_neg_of_pos hs.2 (hR n)
    linarith
  refine abs_derivWithin_scalar_le_of_survivor_maps_of_lt_P6L (Hs n) (ts n) (t₀ := ts n) (hR n)
    hCt (hqD n) a ha fs hfs hp ?_ ⟨hs.1, hs.2.le⟩ hst
    (fun hv => lt_of_le_of_ne (ObservedHistory.activeStage_time_le _ _)
      fun heq => hne _ heq.symm) z hz
  -- 局部化：survivor 点形导数界由 trace-local `hstage` 经 survivor maps 的 backward trace 给出
  intro v hvlt hreg hav hvt z' hq'
  obtain ⟨tr, htr⟩ := exists_backwardPointTrace_of_survivor_maps_P6L (Hs n) (ts n) a hat fs
    hcross hlast v hav hvt z'
  have hz'B : (z' : ((Hs n).stageAt (ts n)).Carrier) ∈
      riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
        (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
    rw [← ObservedHistory.riemannianBallOf_scaleMetric_eq _ (hR n), ← hWn]
    exact z'.property
  have hva : (ts n : ℝ) - τ k / R n ≤ v := by rw [← ha]; exact hav
  have hw := hsn z' hz'B v hvt hva hvlt hreg tr (by rw [htr]; exact hq')
  rw [htr] at hw
  exact hw

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
