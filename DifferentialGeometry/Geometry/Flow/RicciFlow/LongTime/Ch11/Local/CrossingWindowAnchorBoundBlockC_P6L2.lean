import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingWindowAnchorBound_P6L

/-!
# survivor-block BCAD 引理的 **block 形**（O-CH11-P6ANCH2 G4′，后缀 `_P6L2`）

`survivor_blocks_scalar_le_at_distance_P6L`（O-CH11-P6D2 G2）的证明体只在 block `(s, Dw) = (s, k + 3)`、
`s ∈ [−c k, 0)` 上取 `hbound`（BCAD 双 trace 形）；常数 `C` 只依赖 `(A, Dd)`。这里把 `∀ σ' Dw` 前提换成
block 形 `∀ k, ∀ s ∈ Icc (−c k) 0, s < 0 → ∀ᶠ n, …(s, k + 3)…`，证明体逐字（删去只服务于该处的 `hk3`）。
用途：条件形 `hbcadC` 的 window anchor（`CrossingWindowAnchorBound2C_P6L2`）只在已控深度 `c k < τ k < Tstar`
的 block 上提供 BCAD。private `lt_ofReal_div_of_ofReal_mul_lt_P6L` 照抄为 `_bC_P6L2`。
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

/-- 照抄 `CrossingWindowAnchorBound` 的 private `lt_ofReal_div_of_ofReal_mul_lt`。 -/
private theorem lt_ofReal_div_of_ofReal_mul_lt_bC_P6L2 {a b : ℝ} (ha : 0 < a) {d : ENNReal}
    (h : ENNReal.ofReal a * d < ENNReal.ofReal b) : d < ENNReal.ofReal (b / a) := by
  have hd : d ≠ ⊤ := by
    rintro rfl
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr ha).ne'] at h
    exact (not_top_lt h)
  rw [← ENNReal.ofReal_toReal hd, ← ENNReal.ofReal_mul ha.le] at h
  obtain ⟨h1, hb⟩ := (ENNReal.ofReal_lt_ofReal_iff').mp h
  rw [← ENNReal.ofReal_toReal hd]
  refine (ENNReal.ofReal_lt_ofReal_iff' ).mpr ⟨?_, div_pos hb ha⟩
  rw [lt_div_iff₀ ha]
  linarith

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace ObservedHistory

variable {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
  {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n} {τ : ℕ → ℝ}
  {W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens ((Hs n).stageAt (ts n)).Carrier}
  {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)}

/-- `:264` 的局部化：`hbound`（bounded curvature at bounded distance，`∀ z x : stage`）换成
trace 形（两条从 `B(y n, Dw/√R n)` 出发的 backward trace 的点，`C` 不依赖 `Dw`）。 -/
theorem survivor_blocks_scalar_le_at_distance_block_P6L2
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
    {c : ℕ → ℝ} (hcτ : ∀ k, c k ≤ τ k)
    (hbound : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ k : ℕ, ∀ s ∈ Icc (-c k) 0, s < 0 →
      ∀ᶠ n in atTop,
      ∀ x₁ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)),
      ∀ x₂ ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
          (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (v : ℝ) = ts n + s / R n →
      ∀ (tr₁ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x₂),
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤
          A * R n →
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr₁.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt))
            (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr₂.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) ≤
          C * R n) :
    ∀ A Dd : ℝ, ∃ C : ℝ, ∀ k : ℕ, ∀ s ∈ Icc (-c k) 0, s < 0 → ∀ᶠ n in atTop,
      ∀ z x : W k n, metricScalarAt (h k n s) z ≤ A →
        riemannianEDistOf (h k n s) z x < ENNReal.ofReal Dd →
        metricScalarAt (h k n s) x ≤ C := by
  intro A Dd
  obtain ⟨C₁, hC₁⟩ := hbound (max A 1) (max Dd 1) (by positivity) (by positivity)
  refine ⟨C₁, fun k s hs hs0 => ?_⟩
  filter_upwards [hWset k, hsurv k, hC₁ k s hs hs0] with n hWn hn hCm z x hz hzx
  obtain ⟨a, hat, ha, fs, hfs, -, hcross, hlast, hp⟩ := hn
  have hR0 := hR n
  have hsτ : s ∈ Icc (-τ k) 0 := ⟨by linarith [hs.1, hcτ k], hs.2⟩
  have hsR : s / R n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hR0.le
  have hθR : -τ k / R n ≤ s / R n := div_le_div_of_nonneg_right hsτ.1 hR0.le
  have hlo : (a : ℝ) ≤ (ts n : ℝ) + s / R n := by
    rw [ha, sub_eq_add_neg, ← neg_div]
    linarith
  let v : Icc (0 : ℝ) (Hs n).horizon :=
    ⟨(ts n : ℝ) + s / R n, a.2.1.trans hlo,
      (by linarith : (ts n : ℝ) + s / R n ≤ ts n).trans (ts n).2.2⟩
  have hav : a ≤ v := hlo
  have hvt : v ≤ ts n := show (ts n : ℝ) + s / R n ≤ ts n by linarith
  let j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n)) :=
    ⟨(Hs n).activeStage v, (Hs n).activeStage_mono hav, (Hs n).activeStage_mono hvt⟩
  have hs1 := hp s hsτ j ((Hs n).activeStage_mem v)
  have hscz : ∀ w, metricScalarAt (h k n s) w =
      (R n)⁻¹ * metricScalarAt ((Hs n).stageMetric j.val v) (fs j w) := by
    intro w
    rw [hs1, metricScalarAt_scaleMetric, metricScalarAt_localPull]
  have hz' : metricScalarAt ((Hs n).stageMetric j.val v) (fs j z) ≤ max A 1 * R n := by
    rw [hscz z, inv_mul_le_iff₀ hR0] at hz
    nlinarith [le_max_left A 1]
  have hd : riemannianEDistOf ((Hs n).stageMetric j.val v) (fs j z) (fs j x) <
      ENNReal.ofReal (max Dd 1 / Real.sqrt (R n)) := by
    rw [hs1, edistOf_scale] at hzx
    have h1 := lt_ofReal_div_of_ofReal_mul_lt_bC_P6L2 (Real.sqrt_pos.mpr hR0) hzx
    have h2 := edistOf_le_of_quad_of_localDiffeomorph
      (localPullMetric ((Hs n).stageMetric j.val v) (fs j) (hfs j))
      ((Hs n).stageMetric j.val v) (fs j) (hfs j) one_pos
      (fun x' u => by rw [localPullMetric_inner, one_mul]) z x
    rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at h2
    exact h2.trans_lt (h1.trans_le (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))))
  -- 局部化：`hbound` 只在 survivor maps 给出的两条 backward trace 的点上用
  obtain ⟨tr₁, htr₁⟩ := exists_backwardPointTrace_of_survivor_maps_P6L (Hs n) (ts n) a hat fs
    hcross hlast v hav hvt z
  obtain ⟨tr₂, htr₂⟩ := exists_backwardPointTrace_of_survivor_maps_P6L (Hs n) (ts n) a hat fs
    hcross hlast v hav hvt x
  have hzB : (z : ((Hs n).stageAt (ts n)).Carrier) ∈
      riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
        (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
    rw [← ObservedHistory.riemannianBallOf_scaleMetric_eq _ hR0, ← hWn]
    exact z.property
  have hxB : (x : ((Hs n).stageAt (ts n)).Carrier) ∈
      riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
        (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n)) := by
    rw [← ObservedHistory.riemannianBallOf_scaleMetric_eq _ hR0, ← hWn]
    exact x.property
  have hx' := hCm z hzB x hxB v hvt rfl tr₁ tr₂ (by rw [htr₁]; exact hz')
    (by rw [htr₁, htr₂]; exact hd)
  rw [htr₂] at hx'
  rw [hscz x, inv_mul_le_iff₀ hR0]
  linarith

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
