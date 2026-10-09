import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HUParts_O71

/-!
# CH12-O79 G1a: `strip_R_O79` — the `Reg`-free new strip of `(U-R)` (`[FROZEN] CH12-O79 G1a`)

Statement = binder type of `frozen_strip_R_O79` (`build-logs/ch12/scratch/FrozenO79.lean`).
Inputs = the three binders of `hU_of_parts_O71` (`hBig`, `hscale`, `hrc`), verbatim.
This is the new-strip half of `hU_of_parts_O71` with the old family removed (R6 D-R6-2/D-R6-4:
the `(U-R)` input is the region `Reg`, which carries no curvature bound on the old part):
constants `A := 50`, `(B, T₁, b₁) := hBig σ ℓ wst 50`, `C₀ := 2B + 2`, `K_Y := 25B/4`,
`τ := log 2/(18 K_Y)`, `c := min ℓ (min (min (25τ/4) (1/(16 max(B,1)))) 1)`, `b₀ := min b₁ ½`,
`T₀ := max (max T₁ 1) (2 Trc)` — all chosen from `(σ, ℓ, w_*)` before `a, r`.
Route: the seed trace `Y` on `[ae, a]` is an S130 family (hBig, O70 barrier) ⇒
`traces_to_bottom_O71` gives `Z` := trace of the old centre point `p`; `boot_O71` keeps
`d_v(Y v, Z v) < 3r/2` ⇒ `B_v(Z v, 20r) ⊆ B_v(Y v, 50r)`: hBig gives `|Rm|, R ≤ B/r²`,
`sec ≥ -r⁻²` there, and `strip_barrier_slice_O70` gives the outgoing inclusion at every event.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- **G1a** (`[FROZEN] CH12-O79 G1a`): the new strip of `(U-R)` from hBig, the O70 barrier and the
O71 extension, with no old-family input. -/
theorem strip_R_O79 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hBig : ∀ σ ℓ wst A : ℝ, 0 < σ → σ ≤ 1 → 0 < ℓ → 0 < wst → 0 < A →
      ∃ B T₁ b₁ : ℝ, 0 < B ∧ 0 < T₁ ∧ 0 < b₁ ∧
      ∀ s : RegularSlice F.observation, let N := sliceTowerHistory_CX2 s;
      ∀ (u : Icc (0 : ℝ) N.horizon), T₁ ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
      ∀ (r : ℝ), 0 < r → r ≤ b₁ * Real.sqrt u →
      ∀ (a : Icc (0 : ℝ) N.horizon), a ≤ u → (u : ℝ) - r ^ 2 ≤ a →
      ∀ (y : (N.stageAt a).Carrier) (a' : Icc (0 : ℝ) N.horizon) (ha' : a' ≤ a)
        (Y : BackwardPointTrace N (N.activeStage a') (N.activeStage a) (N.activeStage_mono ha') y),
        (a' : ℝ) = a - ℓ * r ^ 2 →
        (∀ (w : Icc (0 : ℝ) N.horizon) (haw : a' ≤ w) (hwa : w ≤ a),
          hasSmallParabolicCurvature N w
            (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
            (σ * r) ∧
          ENNReal.ofReal (wst * (σ * r) ^ 3) ≤
            ballVolume (N.stageMetric (N.activeStage w) w)
              (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
              (σ * r)) →
        ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a' ≤ w) (hwa : w ≤ a),
          ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage w) w)
              (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa)) (A * r),
            Real.sqrt (normSq0S (N.stageMetric (N.activeStage w) w) q 4
              (metricRm04At (N.stageMetric (N.activeStage w) w) q)) ≤ B / r ^ 2 ∧
            metricScalarAt (N.stageMetric (N.activeStage w) w) q ≤ B / r ^ 2 ∧
            SectionalBoundedBelowAt (N.stageMetric (N.activeStage w) w) q (-(r ^ 2)⁻¹))
    (hscale : ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
      ((Hp.records n i).static b).neck.scale / 2 ≤
        metricScalarAt ((Hp.records n i).static b).witness.metric
          (((Hp.records n i).static b).witness.cap z))
    (hrc : ∃ Trc : ℝ, ∀ n (i : Fin (F.tower.history n).eventCount),
      Trc ≤ (F.tower.history n).toHistory.time i.succ →
      Hp.parameters.recenterConstant *
        Hp.parameters.delta ((F.tower.history n).toHistory.time i.succ) ≤ 1 / 2) :
    ∀ σ ℓ wst : ℝ, 0 < σ → σ ≤ 1 → 0 < ℓ → 0 < wst →
      ∃ B c C₀ b₀ T₀ : ℝ, 0 < B ∧ 0 < c ∧ c ≤ ℓ ∧ 1 ≤ C₀ ∧ 0 < b₀ ∧ 0 < T₀ ∧
      ∀ s : RegularSlice F.observation, let N := sliceTowerHistory_CX2 s;
      ∀ (u : Icc (0 : ℝ) N.horizon), T₀ ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
      ∀ (r : ℝ), 0 < r → r ≤ b₀ * Real.sqrt u →
      ∀ (a : Icc (0 : ℝ) N.horizon), a ≤ u → (u : ℝ) - r ^ 2 ≤ a →
      ∀ (p : (N.stageAt a).Carrier),
        (∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc ((a : ℝ) - c * r ^ 2) a →
          ∀ h, C₀ * (Hp.records m i).nominalRadius h ≤ r) →
        ∀ y : (N.stageAt a).Carrier,
        y ∈ riemannianBallOf (N.stageMetric (N.activeStage a) a) p (r / 2) →
        (∃ (a' : Icc (0 : ℝ) N.horizon) (ha' : a' ≤ a)
          (Y : BackwardPointTrace N (N.activeStage a') (N.activeStage a) (N.activeStage_mono ha') y),
          (a' : ℝ) = a - ℓ * r ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a' ≤ w) (hwa : w ≤ a),
            hasSmallParabolicCurvature N w
              (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
              (σ * r) ∧
            ENNReal.ofReal (wst * (σ * r) ^ 3) ≤
              ballVolume (N.stageMetric (N.activeStage w) w)
                (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
                (σ * r)) →
        ∃ (ae : Icc (0 : ℝ) N.horizon) (haa : ae ≤ a)
          (Z : BackwardPointTrace N (N.activeStage ae) (N.activeStage a) (N.activeStage_mono haa) p),
          (ae : ℝ) = a - c * r ^ 2 ∧
          (∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hva : v ≤ a),
            ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
                (Z.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hva)) (20 * r),
              Real.sqrt (normSq0S (N.stageMetric (N.activeStage v) v) q 4
                (metricRm04At (N.stageMetric (N.activeStage v) v) q)) ≤ B / r ^ 2 ∧
              metricScalarAt (N.stageMetric (N.activeStage v) v) q ≤ B / r ^ 2 ∧
              SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r ^ 2)⁻¹)) ∧
          (∀ (i : Fin N.eventCount) (hf : N.activeStage ae ≤ i.castSucc)
              (hl : i.succ ≤ N.activeStage a),
            riemannianBallOf (N.event i).outputMetric
                (Z.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) ⊆
              interior (range (N.event i).oldOutput)) := by
  obtain ⟨Trc, hrcT⟩ := hrc
  intro σ ℓ wst hσ hσ1 hℓ hwst
  obtain ⟨B, T₁, b₁, hB, hT₁, hb₁, hBigI⟩ := hBig σ ℓ wst 50 hσ hσ1 hℓ hwst (by norm_num)
  set KY : ℝ := 25 * B / 4 with hKY
  have hKY0 : 0 < KY := by positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set τ : ℝ := Real.log 2 / (18 * KY) with hτdef
  have hτ0 : 0 < τ := by positivity
  have hexp : Real.exp (9 * KY * τ) < 2 := by
    have e : 9 * KY * τ = Real.log 2 / 2 := by rw [hτdef]; field_simp; ring
    rw [e]
    calc Real.exp (Real.log 2 / 2) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have hM : 0 < 16 * max B 1 := by positivity
  set c : ℝ := min ℓ (min (min (25 * τ / 4) (1 / (16 * max B 1))) 1) with hcdef
  have hc0 : 0 < c := lt_min hℓ (lt_min (lt_min (by positivity) (by positivity)) one_pos)
  have hcℓ : c ≤ ℓ := min_le_left _ _
  have hcτ : c ≤ 25 * τ / 4 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hcM : c ≤ 1 / (16 * max B 1) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hcB : 16 * max B 1 * c ≤ 1 := by
    calc 16 * max B 1 * c ≤ 16 * max B 1 * (1 / (16 * max B 1)) :=
          mul_le_mul_of_nonneg_left hcM hM.le
      _ = 1 := by field_simp
  refine ⟨B, c, 2 * B + 2, min b₁ (1 / 2), max (max T₁ 1) (2 * Trc), hB, hc0, hcℓ,
    (by linarith), lt_min hb₁ (by norm_num),
    lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  intro s N u hTu hus r hr hrb a hau hua p hbud y hy hseed
  obtain ⟨a', ha', Y, ha'eq, hstrip⟩ := hseed
  have hu0 : 0 ≤ (u : ℝ) := u.2.1
  have hsq : Real.sqrt (u : ℝ) ^ 2 = u := Real.sq_sqrt hu0
  have hrb1 : r ≤ b₁ * Real.sqrt u := le_trans hrb (mul_le_mul_of_nonneg_right
    (min_le_left _ _) (Real.sqrt_nonneg _))
  have hr2 : 0 < r ^ 2 := by positivity
  have hr2u : r ^ 2 ≤ (u : ℝ) / 4 := by
    have h1 : r ≤ 1 / 2 * Real.sqrt u :=
      le_trans hrb (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _))
    have h2 := pow_le_pow_left₀ hr.le h1 2
    nlinarith [hsq]
  have hcr : c * r ^ 2 ≤ r ^ 2 := by
    have := mul_le_mul_of_nonneg_right hc1 hr2.le
    linarith
  have hae0 : 0 ≤ (a : ℝ) - c * r ^ 2 := by
    have : (u : ℝ) - r ^ 2 ≤ a := hua
    linarith
  let ae : Icc (0 : ℝ) N.horizon :=
    ⟨(a : ℝ) - c * r ^ 2, hae0, (sub_le_self _ (by positivity)).trans a.2.2⟩
  have haeval : (ae : ℝ) = a - c * r ^ 2 := rfl
  have haa : ae ≤ a := show (a : ℝ) - c * r ^ 2 ≤ a from sub_le_self _ (by positivity)
  have ha'e : a' ≤ ae := by
    change (a' : ℝ) ≤ (a : ℝ) - c * r ^ 2
    rw [ha'eq]
    have := mul_le_mul_of_nonneg_right hcℓ hr2.le
    linarith
  -- the 84.1 big-ball bound on the seed strip
  have hBigY := hBigI s u (((le_max_left T₁ 1).trans (le_max_left _ _)).trans hTu) hus r hr
    hrb1 a hau hua y a' ha' Y ha'eq hstrip
  -- the O70 barrier on the extension window (ball B_out(Y, 50 r))
  have hTrc : Trc ≤ (ae : ℝ) := by
    change Trc ≤ (a : ℝ) - c * r ^ 2
    have h1 : 2 * Trc ≤ (u : ℝ) := (le_max_right _ _).trans hTu
    have : (u : ℝ) - r ^ 2 ≤ a := hua
    linarith
  have hbarY := strip_barrier_slice_O70 Hp hscale hrcT s (B := B) (C₀ := 2 * B + 2) (r := r)
    (ρ := 50 * r) (by positivity) hr (by nlinarith) ha'e haa hTrc
    (fun m i hi h => hbud m i hi h) Y (fun w haw hwa q hq => (hBigY w haw hwa q hq).2.1)
  -- the seed family on [ae, a] is an S130 family at radius 5r/2
  let Yae := traceRestrict_O30 Y (N.activeStage_mono ha'e) (N.activeStage_mono haa)
  have e20 : (20 : ℝ) * (5 * r / 2) = 50 * r := by ring
  have eK : KY / (5 * r / 2) ^ 2 = B / r ^ 2 := by rw [hKY]; field_simp; ring
  have hwin : (a : ℝ) - ae ≤ τ * (5 * r / 2) ^ 2 := by
    rw [haeval]
    have h1 := mul_le_mul_of_nonneg_right hcτ hr2.le
    have e : τ * (5 * r / 2) ^ 2 = 25 * τ / 4 * r ^ 2 := by ring
    rw [e]
    linarith
  have htb := traces_to_bottom_O71 N haa (by positivity) hKY0 hexp hwin Yae
    (fun v hav hvt q hq => by
      rw [e20] at hq
      rw [eK]
      exact (hBigY v (ha'e.trans hav) hvt q hq).1)
    (fun i hf hl U hU _ _ _ _ _ _ => hbarY i hf hl U (by rw [e20] at hU; exact hU))
  -- the new centre line
  have hYa : Y.point (N.activeStage a) (N.activeStage_mono (ha'e.trans haa))
      (N.activeStage_mono (le_refl a)) = y := Y.endpoint_eq
  have hxa : p ∈
      riemannianBallOf (N.stageMetric (N.activeStage a) a)
        (Yae.point (N.activeStage a) (N.activeStage_mono haa) (N.activeStage_mono (le_refl a)))
        (2 * (5 * r / 2)) := by
    change riemannianEDistOf (N.stageMetric (N.activeStage a) a)
      (Y.point (N.activeStage a) (N.activeStage_mono (ha'e.trans haa))
        (N.activeStage_mono (le_refl a))) _ < _
    rw [hYa, riemannianEDistOf_comm]
    exact lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal (by linarith))
  let Z := Classical.choice (htb a haa (le_refl a) _ hxa)
  -- distance bootstrap: d_v(Y v, Z v) < 3r/2 on [ae, a]
  have hdist := boot_O71 N ha'e haa (le_refl a) ha' Y (ρ := 5 * r) (d := r / 2) hr hc0 hcB
    (by rw [haeval]; linarith)
    (fun v hav hva q hq => (hBigY v hav hva q
      (lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal (by linarith)))).1)
    (fun v hev hvt z hz => htb v hev hvt z (by rw [show (2 : ℝ) * (5 * r / 2) = 5 * r by ring]; exact hz))
    Z
    (by
      rw [hYa, riemannianEDistOf_comm]
      exact hy)
    (by linarith)
  have hin : ∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hva : v ≤ a) {β : ℝ}, 0 ≤ β →
      β ≤ 20 * r →
      riemannianBallOf (N.stageMetric (N.activeStage v) v)
        (Z.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hva)) β ⊆
      riemannianBallOf (N.stageMetric (N.activeStage v) v)
        (Y.point (N.activeStage v) (N.activeStage_mono (ha'e.trans hav))
          (N.activeStage_mono hva)) (50 * r) := by
    intro v hav hva β hβ0 hβ
    exact ball_subset_O71 N v (by positivity) hβ0 (hdist v hav hva) (by linarith)
  -- output-metric inclusion at the events of the new strip (output metric = stage metric at the
  -- event time, `activeStage (time i.succ) = i.succ`)
  have hout : ∀ (i : Fin N.eventCount) (hf : N.activeStage ae ≤ i.castSucc)
      (hl : i.succ ≤ N.activeStage a),
      riemannianBallOf (N.event i).outputMetric
          (Z.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) ⊆
        riemannianBallOf (N.event i).outputMetric
          (Y.point i.succ ((N.activeStage_mono ha'e).trans (hf.trans i.castSucc_lt_succ.le)) hl)
          (50 * r) := by
    intro i hf hl
    let e : Icc (0 : ℝ) N.horizon := ⟨N.time i.succ, N.time_nonneg _, N.time_le_horizon_at _⟩
    have hae : ae ≤ e :=
      (time_lt_of_activeStage_lt_CX2 N ae i.succ (hf.trans_lt i.castSucc_lt_succ)).le
    have hea : e ≤ a := (N.time_strictMono.monotone hl).trans (N.activeStage_time_le a)
    have hej : N.activeStage e = i.succ := N.activeStage_at_time i.succ
    have key : ∀ (j : Fin (N.eventCount + 1)) (hj : N.activeStage e = j)
        (h1 : N.activeStage ae ≤ j) (h1' : N.activeStage a' ≤ j) (h2 : j ≤ N.activeStage a),
        riemannianBallOf (N.stageMetric j e) (Z.point j h1 h2) (20 * r) ⊆
          riemannianBallOf (N.stageMetric j e) (Y.point j h1' h2) (50 * r) := by
      intro j hj h1 h1' h2
      subst hj
      exact hin e hae hea (by positivity) le_rfl
    have hb := key i.succ hej (hf.trans i.castSucc_lt_succ.le)
      ((N.activeStage_mono ha'e).trans (hf.trans i.castSucc_lt_succ.le)) hl
    have hmetricE : N.stageMetric i.succ e = (N.event i).outputMetric :=
      (N.stageMetric_initial i.succ).trans (N.event_output i).symm
    rw [hmetricE] at hb
    exact hb
  refine ⟨ae, haa, Z, haeval, ?_, ?_⟩
  · intro v hav hva q hq
    exact hBigY v (ha'e.trans hav) hva q (hin v hav hva (by positivity) le_rfl hq)
  · intro i hf hl
    exact hbarY i hf hl _ (hout i hf hl)

end GC.LongTime.Ch12
