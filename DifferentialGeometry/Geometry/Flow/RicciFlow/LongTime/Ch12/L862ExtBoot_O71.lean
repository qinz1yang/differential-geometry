import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862UnscathedRegion_S111
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedFamily_S130

/-!
# CH12-O71 G1: traces to a common bottom + distance bootstrap inside the 84.1 ball

Pieces of `hU_of_parts_O71` (`[FROZEN] CH12-O71 inputs-v2b`), on a general observed history:
* `traces_to_bottom_O71`: an S130 family (`|Rm| ≤ K/r²` on `B_v(Y v, 20 r)` + event barrier) on
  `[ae, t]` with `t - ae ≤ τ r²` gives, at EVERY `v ∈ [ae, t]`, backward traces down to the common
  bottom `ae` of all points of `B_v(Y v, 2 r)` (S130 applied with the variable depth `v - ae`;
  `v = ae` is the singleton trace).
* `boot_O71`: the distance bootstrap `dist_trace_boot_S68` in the window `[ae, t]` (length
  `≤ c r²`, `16 max(B,1) c ≤ 1`) with the Ricci bound from `|Rm| ≤ B/r²` on `B_v(Y v, ρ)`: a point
  at distance `< d` from `Y t` (with `d + r < ρ/2`) stays at distance `< d + r` along its trace.
* `ball_subset_O71`: triangle-inequality ball inclusion.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Backward traces of every point of `B_v(Y v, 2r)`, `v ∈ [ae, t]`, down to the common bottom
`ae`, from the S130 family invariant on `[ae, t]` (variable depth `v - ae ≤ τ r²`). -/
theorem traces_to_bottom_O71 (H : ObservedHistory.{u}) {ae t : Icc (0 : ℝ) H.horizon}
    (het : ae ≤ t) {τ r K : ℝ} (hr : 0 < r) (hK : 0 < K)
    (hexp : Real.exp (9 * K * τ) < 2) (hwin : (t : ℝ) - ae ≤ τ * r ^ 2)
    {y : (H.stageAt t).Carrier}
    (Y : BackwardPointTrace H (H.activeStage ae) (H.activeStage t) (H.activeStage_mono het) y)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : ae ≤ v) (hvt : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ K / r ^ 2)
    (hbar : ∀ (i : Fin H.eventCount) (hf : H.activeStage ae ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t) (U : Set (H.stage i.succ).Carrier),
      U ⊆ riemannianBallOf (H.event i).outputMetric
        (Y.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) → IsPreconnected U →
      (∀ y ∈ U, metricScalarAt (H.event i).outputMetric y ≤ (9 * K) / r ^ 2) →
      ∀ (x : (H.event i).incoming.terminalRegularOpen) (y : (H.stage i.succ).Carrier),
        y ∈ U → (H.event i).RegularCrossing x.val y → U ⊆ interior (range (H.event i).oldOutput)) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hev : ae ≤ v) (hvt : v ≤ t),
      ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (Y.point (H.activeStage v) (H.activeStage_mono hev) (H.activeStage_mono hvt)) (2 * r),
        Nonempty (BackwardPointTrace H (H.activeStage ae) (H.activeStage v)
          (H.activeStage_mono hev) z) := by
  intro v hev hvt z hz
  by_cases hlt : ae < v
  · have hpos : 0 < (v : ℝ) - ae := sub_pos.mpr hlt
    have hr2 : 0 < r ^ 2 := by positivity
    set τv : ℝ := ((v : ℝ) - ae) / r ^ 2 with hτv
    have hτv0 : 0 < τv := div_pos hpos hr2
    have hτvr : τv * r ^ 2 = (v : ℝ) - ae := by rw [hτv]; field_simp
    have hτvle : τv ≤ τ := by
      rw [hτv, div_le_iff₀ hr2]
      have : (v : ℝ) ≤ t := hvt
      linarith
    have hexpv : Real.exp (9 * K * τv) < 2 := by
      have h9 := mul_le_mul_of_nonneg_left hτvle (by positivity : (0 : ℝ) ≤ 9 * K)
      exact lt_of_le_of_lt (Real.exp_le_exp.mpr h9) hexp
    let Yv := Y.restrictLast (H.activeStage_mono hev) (H.activeStage_mono hvt)
    have hTR := traced_family_of_trace_S130 H hev hτv0 hr hK hexpv Yv
      (fun w haw hwv q hq => hbound w haw (hwv.trans hvt) q hq)
      (fun i hf hl U hU => hbar i hf (hl.trans (H.activeStage_mono hvt)) U hU)
      v (by rw [hτvr]; linarith) le_rfl
    obtain ⟨-, -, a, hav, ha, hball⟩ := hTR
    have hae : a = ae := Subtype.ext (by rw [ha, hτvr]; ring)
    subst hae
    obtain ⟨A, -⟩ := hball z hz
    exact ⟨A⟩
  · have hve : v = ae := le_antisymm (not_lt.mp hlt) hev
    subst hve
    exact ⟨BackwardPointTrace.singleton H (H.activeStage v) z⟩

/-- Distance bootstrap inside the `84.1` ball: in a window `[ae, t]` of length `≤ c r²` with
`16 max(B,1) c ≤ 1`, `|Rm| ≤ B/r²` on `B_v(Y v, ρ)` and traces to `ae` on these balls, a point
`q` at distance `< d` from `Y t` (`d + r < ρ/2`) stays at distance `< d + r` from `Y v`. -/
theorem boot_O71 (H : ObservedHistory.{u}) {a' ae t a : Icc (0 : ℝ) H.horizon}
    (ha'e : a' ≤ ae) (het : ae ≤ t) (hta : t ≤ a) (ha' : a' ≤ a)
    {y : (H.stageAt a).Carrier}
    (Y : BackwardPointTrace H (H.activeStage a') (H.activeStage a) (H.activeStage_mono ha') y)
    {ρ B c r d : ℝ} (hr : 0 < r) (hc : 0 < c) (hcB : 16 * max B 1 * c ≤ 1)
    (hwin : (t : ℝ) - ae ≤ c * r ^ 2)
    (hRm : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a' ≤ v) (hva : v ≤ a),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hva)) ρ,
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ B / r ^ 2)
    (hTr : ∀ (v : Icc (0 : ℝ) H.horizon) (hev : ae ≤ v) (hvt : v ≤ t),
      ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (Y.point (H.activeStage v) (H.activeStage_mono (ha'e.trans hev))
            (H.activeStage_mono (hvt.trans hta))) ρ,
        Nonempty (BackwardPointTrace H (H.activeStage ae) (H.activeStage v)
          (H.activeStage_mono hev) z))
    {q : (H.stageAt t).Carrier}
    (Q : BackwardPointTrace H (H.activeStage ae) (H.activeStage t) (H.activeStage_mono het) q)
    (hq : riemannianEDistOf (H.stageMetric (H.activeStage t) t)
      (Y.point (H.activeStage t) (H.activeStage_mono (ha'e.trans het))
        (H.activeStage_mono hta)) q < ENNReal.ofReal d)
    (hd : d + r < ρ / 2) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hev : ae ≤ v) (hvt : v ≤ t),
      riemannianEDistOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono (ha'e.trans hev))
          (H.activeStage_mono (hvt.trans hta)))
        (Q.point (H.activeStage v) (H.activeStage_mono hev) (H.activeStage_mono hvt)) <
        ENNReal.ofReal (d + r) := by
  intro v hev hvt
  set B' : ℝ := max B 1 with hB'
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hBB' : B ≤ B' := le_max_left _ _
  have hB'0 : 0 < B' := lt_of_lt_of_le one_pos hB'1
  set C : ℝ := 3 * B' * c with hCdef
  have hC : 0 < C := by positivity
  let Yt := traceRestrict_O30 (Y.restrictLast (H.activeStage_mono (ha'e.trans het))
    (H.activeStage_mono hta)) (H.activeStage_mono ha'e) (H.activeStage_mono het)
  set dt := (riemannianEDistOf (H.stageMetric (H.activeStage t) t)
    (Y.point (H.activeStage t) (H.activeStage_mono (ha'e.trans het))
      (H.activeStage_mono hta)) q).toReal with hdt_def
  have hdt : dt < d := ENNReal.toReal_lt_of_lt_ofReal hq
  have hdt0 : 0 ≤ dt := ENNReal.toReal_nonneg
  have htae0 : 0 ≤ (t : ℝ) - ae := sub_nonneg.mpr het
  have h16 : 16 * c ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hB'1 (by positivity : (0 : ℝ) ≤ 16 * c)
    linarith
  have hE : 16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - ae) ≤ r := by
    have h1 : Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - ae) =
        Real.sqrt (C / 3 * ((t : ℝ) - ae)) := (Real.sqrt_mul (by positivity) _).symm
    have h2 : C / 3 * ((t : ℝ) - ae) ≤ (r / 16) ^ 2 := by
      have e : C / 3 = B' * c := by rw [hCdef]; ring
      rw [e]
      have h3 : B' * c * ((t : ℝ) - ae) ≤ B' * c * (c * r ^ 2) :=
        mul_le_mul_of_nonneg_left hwin (by positivity)
      have h4 : (16 * B' * c) * (16 * c) ≤ 1 * 1 :=
        mul_le_mul hcB h16 (by positivity) (by norm_num)
      have h5 := mul_le_mul_of_nonneg_right h4 (sq_nonneg r)
      nlinarith
    have h3 : Real.sqrt (C / 3 * ((t : ℝ) - ae)) ≤ r / 16 :=
      calc _ ≤ Real.sqrt ((r / 16) ^ 2) := Real.sqrt_le_sqrt h2
        _ = r / 16 := Real.sqrt_sq (by positivity)
    rw [mul_assoc, h1]
    linarith
  have hS : Real.sqrt (3 * ((t : ℝ) - ae) / C) ≤ r := by
    have h1 : 3 * ((t : ℝ) - ae) / C ≤ r ^ 2 := by
      rw [div_le_iff₀ hC, hCdef]
      have : c * r ^ 2 ≤ B' * (c * r ^ 2) := by
        have := mul_le_mul_of_nonneg_right hB'1 (by positivity : (0 : ℝ) ≤ c * r ^ 2)
        linarith
      nlinarith
    calc _ ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt h1
      _ = r := Real.sqrt_sq hr.le
  have hq' : riemannianEDistOf (H.stageMetric (H.activeStage t) t)
      (Y.point (H.activeStage t) (H.activeStage_mono (ha'e.trans het))
        (H.activeStage_mono hta)) q < ENNReal.ofReal ρ :=
    lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal (by linarith))
  have hroom : dt + 16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - ae) < ρ / 2 := by linarith
  have hR0 : dt + 16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - ae) +
      Real.sqrt (3 * ((t : ℝ) - ae) / C) < ρ := by linarith
  have hRic : ∀ (w : Icc (0 : ℝ) H.horizon) (haw : ae ≤ w) (hwt : w ≤ t), (ae : ℝ) < w →
      ∀ z : (H.stageAt w).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage w) w)
          (Yt.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) z <
          ENNReal.ofReal ρ →
      ∀ x : TangentSpace ThreeModel z,
      ricciTensor (H.stageMetric (H.activeStage w) w) z x x ≤
        C / ((w : ℝ) - ae) * (H.stageMetric (H.activeStage w) w).inner z x x := by
    intro w haw hwt hlt z hz x
    have hb := hRm w (ha'e.trans haw) (hwt.trans hta) z hz
    obtain ⟨hB0, hB2⟩ := Real.sqrt_le_iff.mp hb
    have hR := ricci_le_of_rm_S111 (H.stageMetric (H.activeStage w) w) z hB0 hB2 x
    have hg := metric_inner_self_nonneg (H.stageMetric (H.activeStage w) w) z x
    have hsub : 0 < (w : ℝ) - ae := sub_pos.mpr hlt
    have hcoef : 3 * (B / r ^ 2) ≤ C / ((w : ℝ) - ae) := by
      rw [le_div_iff₀ hsub, hCdef]
      have hwle : (w : ℝ) - ae ≤ c * r ^ 2 := by
        have : (w : ℝ) ≤ t := hwt
        linarith
      have h1 : 3 * (B / r ^ 2) * ((w : ℝ) - ae) ≤ 3 * (B / r ^ 2) * (c * r ^ 2) :=
        mul_le_mul_of_nonneg_left hwle (by linarith)
      have h2 : 3 * (B / r ^ 2) * (c * r ^ 2) = 3 * B * c := by field_simp
      have h3 : 3 * B * c ≤ 3 * B' * c := by nlinarith
      linarith
    exact hR.trans (mul_le_mul_of_nonneg_right hcoef hg)
  have hboot := dist_trace_boot_S68 H het Yt Q hC (by linarith) hq' hroom hR0
    (fun w haw hwt z hz => hTr w haw hwt z hz) hRic v hev hvt
  have hsv := Real.sqrt_nonneg ((v : ℝ) - ae)
  have hsC : 0 ≤ 16 * Real.sqrt (C / 3) := by positivity
  refine lt_of_le_of_lt hboot ?_
  rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
  have := mul_nonneg hsC hsv
  rw [mul_sub]
  linarith

/-- Ball inclusion by the triangle inequality. -/
theorem ball_subset_O71 (H : ObservedHistory.{u}) (v : Icc (0 : ℝ) H.horizon)
    {p z : (H.stageAt v).Carrier} {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h : riemannianEDistOf (H.stageMetric (H.activeStage v) v) p z < ENNReal.ofReal α)
    (hγ : α + β ≤ γ) :
    riemannianBallOf (H.stageMetric (H.activeStage v) v) z β ⊆
      riemannianBallOf (H.stageMetric (H.activeStage v) v) p γ := by
  intro q hq
  change riemannianEDistOf (H.stageMetric (H.activeStage v) v) p q < ENNReal.ofReal γ
  calc riemannianEDistOf (H.stageMetric (H.activeStage v) v) p q
      ≤ riemannianEDistOf (H.stageMetric (H.activeStage v) v) p z +
          riemannianEDistOf (H.stageMetric (H.activeStage v) v) z q :=
        riemannianEDistOf_triangle _ _ _ _
    _ < ENNReal.ofReal α + ENNReal.ofReal β := ENNReal.add_lt_add h hq
    _ = ENNReal.ofReal (α + β) := (ENNReal.ofReal_add hα hβ).symm
    _ ≤ ENNReal.ofReal γ := ENNReal.ofReal_le_ofReal hγ

end GC.LongTime.Ch12
