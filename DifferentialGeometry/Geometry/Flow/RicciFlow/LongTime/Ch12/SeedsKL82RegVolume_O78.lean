import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82RegStart_O78
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimSelVol_O30
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimTerminal_O36
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimRmBound_O30

/-!
# CH12-O78, G2: regional volume transport

* `volume_transfer_R_O78`: CX11's quarter-ball volume transfer with the trace hypothesis only on
  the top `r/4`-ball (`traced_set_volume_of_sec_CX11` is applied with `ρ = r/4`).
* `kl82_window_volume_R_O78`: Reg-input + claim (C) on `(a, top]` ⇒ bottom volume
  `w (r0/4)³/10 ≤ vol B_a(X a, r0/4)` (the tree's `w`-form; not PDF 82.1(2)).  Traces of the top
  `r0/4`-ball come from `trace_start_R_O78` (Ricci bound from claim (C) + `sec ≥ −r0⁻²` on the
  `3r0/8`-balls), their distance from `dist_trace_boot_R_O78`, and `|Rm|` along them from
  (Reg-fin K) + (Reg-sec) (`rm_normSq_le_of_sec_O30`, `isRmBoundedBy_of_stage_O36`).
* `kl82_selected_volume_R_O78`: the regional `kl82_selected_volume_O30`.
Proof bodies follow O30/CX11 line by line apart from these inputs.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- **G2a.** `volume_transfer_of_distance_CX11` with the trace hypothesis only on the top
`r/4`-ball (the regional trace start produces traces there, not on the whole `r`-ball). -/
theorem volume_transfer_R_O78 (C : ℝ) :
    ∃ τ₁ : ℝ, 0 < τ₁ ∧ τ₁ ≤ 1 ∧
    ∀ (H : ObservedHistory.{u}) (a t : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
      (p : (H.stageAt t).Carrier)
      (X : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) p) (w r τ K : ℝ),
      0 < w → 0 < r → 0 < τ → τ ≤ τ₁ → (a : ℝ) = t - τ * r ^ 2 →
      (∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4),
        ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) q, A.isRmBoundedBy (hat := hat) K) →
      (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r,
          SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r ^ 2)⁻¹)) →
      (∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4),
        ∀ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) q,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q +
            ENNReal.ofReal (16 * Real.sqrt (C / 3) * Real.sqrt τ * r)) →
      ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
      ENNReal.ofReal (w * (r / 4) ^ 3 / 10) ≤
        ballVolume (H.stageMetric (H.activeStage a) a)
          (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r / 4) := by
  obtain ⟨τ₁, hτ₁, hτ₁1, hmargin⟩ := exists_volume_transfer_margin_CX11 C
  refine ⟨τ₁, hτ₁, hτ₁1, ?_⟩
  intro H a t hat p X w r τ K hw hr hτ hτle ha htr hsec hshift hvol
  have hatlt : a < t := by
    change (a : ℝ) < t
    rw [ha]
    exact sub_lt_self _ (mul_pos hτ (sq_pos_of_pos hr))
  let α : ℝ := 1 / 4 - 16 * Real.sqrt (C / 3) * Real.sqrt τ
  obtain ⟨hα, hmargin'⟩ := hmargin τ hτ.le hτle
  change 0 < α at hα
  have hα4 : α ≤ 1 / 4 := by
    dsimp [α]
    have hh : 0 ≤ 16 * Real.sqrt (C / 3) * Real.sqrt τ := by positivity
    linarith
  have hαr : 0 < α * r := mul_pos hα hr
  have hαrr : α * r ≤ r := by
    have hh := mul_le_mul_of_nonneg_right hα4 hr.le
    linarith
  have hαr4 : α * r ≤ r / 4 := by
    have hh := mul_le_mul_of_nonneg_right hα4 hr.le
    linarith
  let : MeasurableSpace (H.stageAt t).Carrier := borel _
  let : BorelSpace (H.stageAt t).Carrier := ⟨rfl⟩
  let B := riemannianBallOf (H.stageMetric (H.activeStage t) t) p (α * r)
  have hBsmall : B ⊆ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4) :=
    riemannianBallOf_mono _ _ hαr4
  have hcapture (q : (H.stageAt t).Carrier) (hq : q ∈ B)
      (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) q)
      (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) :
      A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt) ∈
        riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (r / 4) := by
    have hh := (hshift q (hBsmall hq) A v hav hvt).trans_lt
      (ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hq)
    rw [← ENNReal.ofReal_add hαr.le (by positivity)] at hh
    have he : α * r + 16 * Real.sqrt (C / 3) * Real.sqrt τ * r = r / 4 := by
      dsimp [α]
      ring
    rwa [he] at hh
  have hsetvol := traced_set_volume_of_sec_CX11 H hatlt p (by positivity : (0 : ℝ) < r / 4) htr B
    (isOpen_riemannianBallOf _ _ _).measurableSet hBsmall
    (fun q hq A v hav hvt => hsec v hav hvt _
      (riemannianBallOf_mono _ _ (by linarith : r / 4 ≤ r) (hcapture q hq A v hav hvt)))
  have hsmallvol := ballVolume_small_of_sec_component_CX11
    (H.stageMetric (H.activeStage t) t) (RiemannianMetricComplete.of_compact _) p
    (q := r⁻¹) (inv_nonneg.mpr hr.le) hαr hαrr
    (fun z hz => by
      have hh := hsec t hat le_rfl z
      rw [X.endpoint_eq] at hh
      simpa only [inv_pow] using hh hz) hvol
  have hexp : 2 * r⁻¹ * r = (2 : ℝ) := by field_simp
  rw [hexp] at hsmallvol
  have htime : (t : ℝ) - a = τ * r ^ 2 := by rw [ha]; ring
  rw [htime] at hsetvol
  have he : -6 * (τ * r ^ 2) / r ^ 2 = -6 * τ := by field_simp
  rw [he] at hsetvol
  have hnum : w * (r / 4) ^ 3 / 10 ≤
      Real.exp (-6 * τ) * (w * (α * r) ^ 3 / Real.exp 2) := by
    have hh := mul_le_mul_of_nonneg_left hmargin' (mul_pos hw (pow_pos hr 3)).le
    have he : Real.exp (-6 * τ) / Real.exp 2 = Real.exp (-(2 + 6 * τ)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    calc
      w * (r / 4) ^ 3 / 10 = (w * r ^ 3) * ((1 / 4 : ℝ) ^ 3 / 10) := by ring
      _ ≤ (w * r ^ 3) * (Real.exp (-(2 + 6 * τ)) * α ^ 3) := hh
      _ = Real.exp (-6 * τ) * (w * (α * r) ^ 3 / Real.exp 2) := by
        rw [← he]
        ring
  have hcomparison : ENNReal.ofReal (w * (r / 4) ^ 3 / 10) ≤
      ENNReal.ofReal (Real.exp (-6 * τ)) *
        riemannianVolumeMeasure ThreeModel (H.stageAt t).Carrier
          (H.stageMetric (H.activeStage t) t) B := by
    apply (ENNReal.ofReal_le_ofReal hnum).trans
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_le_mul' le_rfl hsmallvol
  apply (hcomparison.trans hsetvol).trans
  apply measure_mono
  rintro z ⟨q, hq, A, rfl⟩
  exact hcapture q hq A a le_rfl hat


/-- **G2b.** Sub-window volume transport from the Reg-input and claim (C) on the window
(regional `kl82_window_volume_O30`): bottom quarter-ball volume in the tree's `w`-form. -/
theorem kl82_window_volume_R_O78 (C₀ B₀ : ℝ) (hC₀ : 0 ≤ C₀) (hB₀ : 0 ≤ B₀) :
    ∃ τw : ℝ, 0 < τw ∧ τw ≤ 1 ∧
      ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
        (r0 τ K w : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
        (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
          (H.activeStage_mono hat) x0),
        0 < w → 0 < r0 → 0 < τ → τ ≤ τw → (a : ℝ) = top - τ * r0 ^ 2 →
            (∀ (i : Fin H.eventCount) (hai : H.activeStage a ≤ i.castSucc)
                (hit : i.succ ≤ H.activeStage top),
              riemannianBallOf (H.initialMetric i.succ)
                  (X.point i.succ (hai.trans i.castSucc_lt_succ.le) hit) r0 ⊆
                H.backwardSurvivorDomain i.castSucc i.succ i.castSucc_lt_succ.le) →
            (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
              ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                  (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
                metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤ K) →
            (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
              ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                  (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
                SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r0 ^ 2)⁻¹)) →
            ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top), (a : ℝ) < v →
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (3 * r0 / 8),
            metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤
              C₀ * (r0 ^ 2)⁻¹ + B₀ * ((v : ℝ) - a)⁻¹) →
        ENNReal.ofReal (w * (r0 / 4) ^ 3 / 10) ≤
          ballVolume (H.stageMetric (H.activeStage a) a)
            (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 4) := by
  set C' : ℝ := C₀ / 2 + B₀ / 2 + 1 with hC'
  have hC'pos : 0 < C' := by positivity
  obtain ⟨τ₁, hτ₁, -, hVT⟩ := volume_transfer_R_O78.{u} C'
  set τ₂ : ℝ := min (C' / 768) (3 / (65536 * C')) with hτ₂
  have hτ₂pos : 0 < τ₂ := lt_min (by positivity) (by positivity)
  refine ⟨min (min τ₁ 1) τ₂, lt_min (lt_min hτ₁ one_pos) hτ₂pos,
    (min_le_left _ _).trans (min_le_right _ _), ?_⟩
  intro H top x0 r0 τ K w a hat X hw hr0 hτ hτ0 ha hEvt hRfin hsec hvol hclv
  have hτ₁' : τ ≤ τ₁ := hτ0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτ1 : τ ≤ 1 := hτ0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτ₂' : τ ≤ τ₂ := hτ0.trans (min_le_right _ _)
  have hsqrt_ta : Real.sqrt ((top : ℝ) - a) = Real.sqrt τ * r0 := by
    rw [ha, show (top : ℝ) - (top - τ * r0 ^ 2) = τ * r0 ^ 2 by ring,
      Real.sqrt_mul hτ.le, Real.sqrt_sq hr0.le]
  have hsqrt_3 : Real.sqrt (3 * ((top : ℝ) - a) / C') = Real.sqrt (3 * τ / C') * r0 := by
    rw [ha, show 3 * ((top : ℝ) - (top - τ * r0 ^ 2)) / C' = (3 * τ / C') * r0 ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hr0.le]
  have hδ : 16 * Real.sqrt (C' / 3) * Real.sqrt τ ≤ 1 / 16 := by
    have hτa : τ ≤ 3 / (65536 * C') := hτ₂'.trans (min_le_right _ _)
    have hm : C' / 3 * τ ≤ (1 / 256) ^ 2 := by
      calc C' / 3 * τ ≤ C' / 3 * (3 / (65536 * C')) :=
            mul_le_mul_of_nonneg_left hτa (by positivity)
        _ = (1 / 256) ^ 2 := by field_simp; norm_num
    have hs : Real.sqrt (C' / 3) * Real.sqrt τ ≤ 1 / 256 := by
      rw [← Real.sqrt_mul (by positivity)]
      calc Real.sqrt (C' / 3 * τ) ≤ Real.sqrt ((1 / 256) ^ 2) := Real.sqrt_le_sqrt hm
        _ = 1 / 256 := Real.sqrt_sq (by norm_num)
    linarith
  have hε : Real.sqrt (3 * τ / C') ≤ 1 / 16 := by
    have hτb : τ ≤ C' / 768 := hτ₂'.trans (min_le_left _ _)
    have hm : 3 * τ / C' ≤ (1 / 16) ^ 2 := by
      rw [div_le_iff₀ hC'pos]
      linarith
    calc Real.sqrt (3 * τ / C') ≤ Real.sqrt ((1 / 16) ^ 2) := Real.sqrt_le_sqrt hm
      _ = 1 / 16 := Real.sqrt_sq (by norm_num)
  have hδr : 16 * Real.sqrt (C' / 3) * Real.sqrt ((top : ℝ) - a) ≤ r0 / 16 := by
    rw [hsqrt_ta]
    calc 16 * Real.sqrt (C' / 3) * (Real.sqrt τ * r0)
        = (16 * Real.sqrt (C' / 3) * Real.sqrt τ) * r0 := by ring
      _ ≤ 1 / 16 * r0 := mul_le_mul_of_nonneg_right hδ hr0.le
      _ = r0 / 16 := by ring
  have hεr : Real.sqrt (3 * ((top : ℝ) - a) / C') ≤ r0 / 16 := by
    rw [hsqrt_3]
    calc Real.sqrt (3 * τ / C') * r0 ≤ 1 / 16 * r0 := mul_le_mul_of_nonneg_right hε hr0.le
      _ = r0 / 16 := by ring
  have hRic : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top), (a : ℝ) < v →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) z <
          ENNReal.ofReal (3 * r0 / 8) →
        ∀ w : TangentSpace ThreeModel z,
          ricciTensor (H.stageMetric (H.activeStage v) v) z w w ≤
            C' / ((v : ℝ) - a) * (H.stageMetric (H.activeStage v) v).inner z w w := by
    intro v hav hvt hav' z hz w'
    have hs : 0 < (v : ℝ) - a := by linarith
    have hvt' : (v : ℝ) ≤ top := hvt
    have hsr : (v : ℝ) - a ≤ r0 ^ 2 := by
      rw [ha]
      have : τ * r0 ^ 2 ≤ r0 ^ 2 := by nlinarith [sq_nonneg r0]
      linarith
    have hzr0 : z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0 :=
      lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal (by linarith))
    exact ricci_le_inv_time_of_claim_O25 _ z hs hsr hC₀ (hsec v hav hvt z hzr0)
      (hclv v hav hvt hav' z hz) w'
  refine hVT H a top hat x0 X w r0 τ (2 * Real.sqrt 3 * (max K 0 / 2 + 2 * (r0 ^ 2)⁻¹))
    hw hr0 hτ hτ₁' ha ?_ hsec ?_ hvol
  · intro q hq
    have hd : riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q <
        ENNReal.ofReal (r0 / 4) := hq
    have hdlt : (riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q).toReal <
        r0 / 4 := ENNReal.toReal_lt_of_lt_ofReal hd
    have hdr0 : riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q <
        ENNReal.ofReal r0 := lt_of_lt_of_le hd (ENNReal.ofReal_le_ofReal (by linarith))
    obtain ⟨A⟩ := trace_start_R_O78 H hat X (C := C') (ρ := r0) (R0 := 3 * r0 / 8) hC'pos hr0
      hdr0 (by linarith) (by linarith) hEvt hRic
    refine ⟨A, isRmBoundedBy_of_stage_O36 H A ?_⟩
    intro s has hst
    have hb := dist_trace_boot_R_O78 H hat X A (C := C') (ρ := r0) (R0 := 3 * r0 / 8) hC'pos
      hr0 hdr0 (by linarith) (by linarith) hEvt hRic s has hst
    rw [traceEDist_at_stage_CX11 H X A s has hst (H.activeStage s) rfl
      (H.activeStage_mono has) (H.activeStage_mono hst)] at hb
    have hin : A.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst) ∈
        riemannianBallOf (H.stageMetric (H.activeStage s) s)
          (X.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst)) r0 := by
      refine lt_of_le_of_lt hb ((ENNReal.ofReal_lt_ofReal_iff hr0).mpr ?_)
      have h1 : 0 ≤ Real.sqrt ((s : ℝ) - a) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt (C' / 3) := Real.sqrt_nonneg _
      nlinarith [mul_nonneg h2 h1]
    exact rm_normSq_le_of_sec_O30 _ _ (by positivity) (le_max_right K 0) (hsec s has hst _ hin)
      ((hRfin s has hst _ hin).trans (le_max_left K 0))
  · intro q hq A v hav hvt
    have hd : riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q <
        ENNReal.ofReal (r0 / 4) := hq
    have hne := ne_top_of_lt hd
    have hdlt : (riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q).toReal <
        r0 / 4 := ENNReal.toReal_lt_of_lt_ofReal hd
    have hdr0 : riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q <
        ENNReal.ofReal r0 := lt_of_lt_of_le hd (ENNReal.ofReal_le_ofReal (by linarith))
    have hb := dist_trace_boot_R_O78 H hat X A (C := C') (ρ := r0) (R0 := 3 * r0 / 8) hC'pos
      hr0 hdr0 (by linarith) (by linarith) hEvt hRic v hav hvt
    rw [traceEDist_at_stage_CX11 H X A v hav hvt (H.activeStage v) rfl
      (H.activeStage_mono hav) (H.activeStage_mono hvt)] at hb
    have hδv : 16 * Real.sqrt (C' / 3) * (Real.sqrt ((top : ℝ) - a) -
        Real.sqrt ((v : ℝ) - a)) ≤ 16 * Real.sqrt (C' / 3) * Real.sqrt τ * r0 := by
      rw [hsqrt_ta]
      have h1 : 0 ≤ Real.sqrt ((v : ℝ) - a) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt (C' / 3) := Real.sqrt_nonneg _
      nlinarith
    refine hb.trans ?_
    calc ENNReal.ofReal
          ((riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q).toReal +
            16 * Real.sqrt (C' / 3) * (Real.sqrt ((top : ℝ) - a) - Real.sqrt ((v : ℝ) - a)))
        ≤ ENNReal.ofReal
          ((riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q).toReal +
            16 * Real.sqrt (C' / 3) * Real.sqrt τ * r0) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q +
            ENNReal.ofReal (16 * Real.sqrt (C' / 3) * Real.sqrt τ * r0) := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
            ENNReal.ofReal_toReal hne]


/-- **G2c.** Regional `kl82_selected_volume_O30`. -/
theorem kl82_selected_volume_R_O78
    (C₀ B₀ : ℝ) (hC₀ : 0 ≤ C₀) (hB₀ : 0 ≤ B₀) :
    ∃ τw : ℝ, 0 < τw ∧ τw ≤ 1 ∧
      ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
        (r0 τ K w : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
        (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
          (H.activeStage_mono hat) x0),
        0 < w → 0 < r0 → 0 < τ → τ ≤ τw → (a : ℝ) = top - τ * r0 ^ 2 →
            (∀ (i : Fin H.eventCount) (hai : H.activeStage a ≤ i.castSucc)
                (hit : i.succ ≤ H.activeStage top),
              riemannianBallOf (H.initialMetric i.succ)
                  (X.point i.succ (hai.trans i.castSucc_lt_succ.le) hit) r0 ⊆
                H.backwardSurvivorDomain i.castSucc i.succ i.castSucc_lt_succ.le) →
            (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
              ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                  (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
                metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤ K) →
            (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
              ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                  (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
                SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r0 ^ 2)⁻¹)) →
            ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
        ∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ top),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top), (s : ℝ) < v →
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (3 * r0 / 8),
            metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤
              C₀ * (r0 ^ 2)⁻¹ + B₀ * ((v : ℝ) - s)⁻¹) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s)
            (X.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst))
            (15 * r0 / 32),
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ 17 * r0 / 32 →
          ENNReal.ofReal (w / 10 * (2 / 17) ^ 3 * ρ ^ 3 / Real.exp (25 / 16)) ≤
            ballVolume (H.stageMetric (H.activeStage s) s) x ρ := by
  obtain ⟨τw, hτw, hτw1, hW⟩ := kl82_window_volume_R_O78 C₀ B₀ hC₀ hB₀
  refine ⟨τw, hτw, hτw1, ?_⟩
  intro H top x0 r0 τ K w a hat X hw hr0 hτ hτ0 ha hEvt hRfin hsec hvol s has hst hgood x hx ρ hρ hρr
  have hsecs := hsec s has hst
  have hquarter : ENNReal.ofReal (w * (r0 / 4) ^ 3 / 10) ≤
      ballVolume (H.stageMetric (H.activeStage s) s)
        (X.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst))
        (r0 / 4) := by
    rcases lt_or_eq_of_le hst with hlt | heq
    · have hlt' : (s : ℝ) < top := hlt
      have has' : (a : ℝ) ≤ s := has
      set τ' : ℝ := ((top : ℝ) - s) / r0 ^ 2 with hτ'
      have hr2 : 0 < r0 ^ 2 := by positivity
      have hτ'pos : 0 < τ' := div_pos (sub_pos.mpr hlt') hr2
      have hτ'le : τ' ≤ τ := by
        rw [hτ', div_le_iff₀ hr2]
        linarith
      have hs' : (s : ℝ) = top - τ' * r0 ^ 2 := by
        rw [hτ', div_mul_cancel₀ _ hr2.ne']
        ring
      refine hW H top x0 r0 τ' K w s hst
        (traceRestrict_O30 X (H.activeStage_mono has) (H.activeStage_mono hst))
        hw hr0 hτ'pos (hτ'le.trans hτ0) hs'
        (fun i hai hit => hEvt i ((H.activeStage_mono has).trans hai) hit)
        (fun v hsv hvt q hq => hRfin v (has.trans hsv) hvt q hq)
        (fun v hsv hvt q hq => hsec v (has.trans hsv) hvt q hq) hvol
        (fun v hsv hvt hv q hq => hgood v (has.trans hsv) hvt hv q hq)
    · subst heq
      have hXtop : X.point (H.activeStage s) (H.activeStage_mono has)
          (H.activeStage_mono hst) = x0 := X.endpoint_eq
      rw [hXtop]
      have hsec0 : ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) x0 r0,
          SectionalBoundedBelowAt (H.stageMetric (H.activeStage s) s) z (-(r0⁻¹ ^ 2)) := by
        intro z hz
        have hz' : z ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s)
            (X.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst)) r0 := by
          rw [hXtop]; exact hz
        simpa only [inv_pow] using hsecs z hz'
      have hc := ballVolume_small_of_sec_component_CX11 (H.stageMetric (H.activeStage s) s)
        (RiemannianMetricComplete.of_compact _) x0 (q := r0⁻¹) (s := r0 / 4) (R := r0)
        (inv_nonneg.mpr hr0.le) (by positivity) (by linarith) hsec0 hvol
      have he : 2 * r0⁻¹ * r0 = (2 : ℝ) := by field_simp
      rw [he] at hc
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hc
      have hexp : Real.exp 2 ≤ 10 := by
        have h1 := Real.exp_one_lt_d9
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        rw [h2]
        nlinarith [Real.exp_pos 1]
      have hnum : 0 ≤ w * r0 ^ 3 := by positivity
      rw [div_le_div_iff₀ (by norm_num) (Real.exp_pos 2)]
      have h3 : 0 ≤ w * (r0 / 4) ^ 3 := by positivity
      nlinarith
  exact ballVolume_recentre_far_O30 (H.stageMetric (H.activeStage s) s)
    (RiemannianMetricComplete.of_compact _) _ x hr0 hρ hρr hx hsecs hquarter

end GC.LongTime.Ch12
