import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82RegDatum_O78
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimMain_O36

/-!
# CH12-O78, G3c: regional KL82 — claim (C), KL82.1 and the improved-region `|Rm|` bound

Regional entry of the `kl82_claim_O36` chain (review CH12-R6 Q1.4; dispositions D-R6-1/D-R6-3):
the input is the Reg-input frozen in "[FROZEN] CH12-O78 Reg-input" (centre trace, (Reg-ev r0),
(Reg-fin K), (Reg-sec)) — no clause "every point of `B_v(X v, r0)` traces back to `a`";
`isTracedRegion` is unchanged.
* `kl82_claim_R_O78`: claim (C) (`kl82_claim_O36`'s contradiction argument, with
  `kl82_blowup_datum_R_O78`; `blowup_core_local_O25` unchanged).
* `kl82_1_R_O78`: conclusion of `kl82_1_O36` verbatim; Part 1 = `kl82_1_part1_of_claim_O11`,
  Part 2 = `kl82_window_volume_R_O78` (the tree's `w`-form of the bottom volume, not the
  `w`-independent number of PDF 82.1(2): flat-torus counterexample, review R6 Q1.4).
* `kl82_improved_rm_R_O78`: `τ₈₂ = τ₀`, `K₈₂ = K₀`, `D = τ₈₂/2`, improved region
  `[top − D r0²/2, top] × B(X v, r0/4)`, `|Rm| ≤ M_ε r0⁻²`, `M_ε = 2√3 (K₈₂/τ₈₂ + 2)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

universe u

/-- **G3c-1. Claim (C) from the Reg-input** (`kl82_claim_O36`'s proof with
`kl82_blowup_datum_R_O78`). -/
theorem kl82_claim_R_O78 :
    ∀ w : ℝ, 0 < w → ∃ τc C₀ B₀ : ℝ, 0 < τc ∧ 0 ≤ C₀ ∧ 0 ≤ B₀ ∧
          ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
            (r0 τ K : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
            (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
              (H.activeStage_mono hat) x0),
            0 < r0 → 0 < τ → τ ≤ τc → (a : ℝ) = top - τ * r0 ^ 2 →
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
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top), (a : ℝ) < v →
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (3 * r0 / 8),
            metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤
              C₀ * (r0 ^ 2)⁻¹ + B₀ * ((v : ℝ) - a)⁻¹ := by
  intro w hw
  by_contra hcon
  have hD := fun n : ℕ => kl82_blowup_datum_R_O78.{u} ((n : ℝ) + 1)
    (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  choose τw hτw _hτw1 hdat using hD
  have hneg : ∀ n : ℕ, ∃ (H : ObservedHistory.{u}) (ts : Icc (0 : ℝ) H.horizon)
      (y : (H.stageAt ts).Carrier) (Q r0 : ℝ),
      0 < Q ∧ metricScalarAt (H.stageMetric (H.activeStage ts) ts) y = Q ∧
      (n : ℝ) + 1 ≤ Q * r0 ^ 2 ∧ 0 < r0 ∧
      (∀ Aa T : ℝ, 0 < Aa → 0 < T → 8192 * (Aa + 16 * T + 1) ^ 2 < (n : ℝ) + 1 →
        2 * T ≤ (n : ℝ) + 1 →
        H.isTracedRegion ts y (Aa / Real.sqrt Q) (T / Q) (8 * Real.sqrt 3 * Q) ∧
        ∀ (a'' : Icc (0 : ℝ) H.horizon) (ha'' : a'' ≤ ts), (a'' : ℝ) = ts - T / Q →
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage ts) ts) y (Aa / Real.sqrt Q),
          ∀ Y : BackwardPointTrace H (H.activeStage a'') (H.activeStage ts)
              (H.activeStage_mono ha'') q,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a'' ≤ v) (hvt : v ≤ ts),
            SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v)
              (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (-(r0 ^ 2)⁻¹)) ∧
      ∀ (D : ℝ) (hQ : 0 < Q), 0 < D → 1024 * D ^ 2 ≤ (n : ℝ) + 1 →
        ∀ x ∈ riemannianClosedBallOf
            (scaleMetric Q hQ (H.stageMetric (H.activeStage ts) ts)) y D,
        ∀ s : ℝ, 0 < s → s ≤ D →
          ENNReal.ofReal (w / 10 * (2 / 17) ^ 3 / Real.exp (25 / 16) * s ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel (H.stageAt ts).Carrier
              (scaleMetric Q hQ (H.stageMetric (H.activeStage ts) ts))
              (riemannianBallOf (scaleMetric Q hQ (H.stageMetric (H.activeStage ts) ts)) x s) := by
    intro n
    by_contra hno
    apply hcon
    refine ⟨τw n, (n : ℝ) + 1, (n : ℝ) + 1, hτw n, by positivity, by positivity, ?_⟩
    intro H top x0 r0 τ K a hat X hr0 hτ hττ ha hEvt hRfin hsec hvol v hav hvt hav' q hq
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨ts, y, Q, hQ, hRy, hNQ, htr, hvl⟩ :=
      hdat n w H top x0 r0 τ K a hat X hw hr0 hτ hττ ha hEvt hRfin hsec hvol
        ⟨v, hav, hvt, hav', q, hq, hlt⟩
    exact hno ⟨H, ts, y, Q, r0, hQ, hRy, hNQ, hr0, htr, hvl⟩
  choose H ts y Q r0 hQ hRy hNQ hr0 htr hvl using hneg
  have hn1 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hlarge : ∀ M : ℝ, ∀ᶠ n : ℕ in atTop, M < (n : ℝ) + 1 := by
    intro M
    refine eventually_atTop.2 ⟨⌈M⌉₊, fun n hn => ?_⟩
    have h1 : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
    have h2 : ((⌈M⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let ε : ℕ → ℝ := fun n => (Q n * r0 n ^ 2)⁻¹
  have hε : ∀ n, 0 < ε n := fun n => inv_pos.mpr (mul_pos (hQ n) (pow_pos (hr0 n) 2))
  have hεle : ∀ n, ε n ≤ 1 / ((n : ℝ) + 1) := fun n => by
    rw [one_div]; exact inv_anti₀ (hn1 n) (hNQ n)
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hε n).le) hεle
  have hεQ : ∀ n, ε n * Q n = (r0 n ^ 2)⁻¹ := fun n => by
    have h1 := (hQ n).ne'
    have h2 := (hr0 n).ne'
    simp only [ε]
    field_simp
  refine blowup_core_local_O25 H ts y Q hQ hRy (K := 8 * Real.sqrt 3) ?_ ε hε hεlim ?_
    (v := w / 10 * (2 / 17) ^ 3 / Real.exp (25 / 16))
    (div_pos (mul_pos (div_pos hw (by norm_num)) (by norm_num)) (Real.exp_pos _)) ?_
  · intro A T hA hT
    filter_upwards [hlarge (8192 * (A + 16 * T + 1) ^ 2), hlarge (2 * T)] with n h1 h2
    exact (htr n A T hA hT h1 h2.le).1
  · intro A T hA hT
    filter_upwards [hlarge (8192 * (A + 16 * T + 1) ^ 2), hlarge (2 * T)] with n h1 h2
    intro a hat ha q hq X v hav hvt
    rw [hεQ n]
    exact (htr n A T hA hT h1 h2.le).2 a hat ha q hq X v hav hvt
  · intro D hD
    filter_upwards [hlarge (1024 * D ^ 2)] with n h1
    exact hvl n D (hQ n) hD h1.le

/-- **G3c-2. Regional KL82.1**: Reg-input ⇒ the conclusion of `kl82_1_O36` verbatim (upper 3/4
window, `r0/4`-ball scalar bound, and the tree's `w`-dependent bottom volume). -/
theorem kl82_1_R_O78 :
  ∀ w : ℝ, 0 < w → ∃ τ₀ K₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ 1 ∧ 0 < K₀ ∧
    ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
      (r0 τ K : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
      (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
        (H.activeStage_mono hat) x0),
      0 < r0 → 0 < τ → τ ≤ τ₀ → (a : ℝ) = top - τ * r0 ^ 2 →
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
      (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
        (top : ℝ) - 3 / 4 * τ * r0 ^ 2 ≤ v →
        ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (r0 / 4),
          metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤ K₀ * τ⁻¹ * (r0 ^ 2)⁻¹) ∧
      ENNReal.ofReal (w * (r0 / 4) ^ 3 / 10) ≤
        ballVolume (H.stageMetric (H.activeStage a) a)
          (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 4) := by
  intro w hw
  obtain ⟨τc, C₀, B₀, hτc, hC₀, hB₀, hcl⟩ := kl82_claim_R_O78.{u} w hw
  obtain ⟨τw, hτw, -, hW⟩ := kl82_window_volume_R_O78.{u} C₀ B₀ hC₀ hB₀
  refine ⟨min (min τc τw) 1, C₀ + 4 * B₀ + 1, lt_min (lt_min hτc hτw) one_pos,
    min_le_right _ _, by positivity, ?_⟩
  intro H top x0 r0 τ K a hat X hr0 hτ hτ0 ha hEvt hRfin hsec hvol
  have hτc' : τ ≤ τc := hτ0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτw' : τ ≤ τw := hτ0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτ1 : τ ≤ 1 := hτ0.trans (min_le_right _ _)
  have hclv := hcl H top x0 r0 τ K a hat X hr0 hτ hτc' ha hEvt hRfin hsec hvol
  refine ⟨?_, hW H top x0 r0 τ K w a hat X hw hr0 hτ hτw' ha hEvt hRfin hsec hvol hclv⟩
  intro v hav hvt hv q hq
  have h1 := kl82_1_part1_of_claim_O11 H hat X hr0 hτ hτ1 hC₀ hB₀ ha hclv v hav hvt hv q hq
  have h2 : 0 ≤ τ⁻¹ * (r0 ^ 2)⁻¹ := by positivity
  calc metricScalarAt (H.stageMetric (H.activeStage v) v) q
      ≤ (C₀ + 4 * B₀) * τ⁻¹ * (r0 ^ 2)⁻¹ := h1
    _ ≤ (C₀ + 4 * B₀ + 1) * τ⁻¹ * (r0 ^ 2)⁻¹ := by nlinarith

/-- **G3c-3. Improved region** (for O79): with `D = τ₈₂/2` and `a = top − D r0²`, on
`[top − D r0²/2, top] × B(X v, r0/4)` the bound `R ≤ K₈₂ D⁻¹ r0⁻²` and `sec ≥ −r0⁻²` give
`|Rm| ≤ M_ε r0⁻²`, `M_ε = 2√3 (K₈₂/τ₈₂ + 2)` (`rm_normSq_le_of_sec_O30`); bottom volume kept. -/
theorem kl82_improved_rm_R_O78 :
  ∀ w : ℝ, 0 < w → ∃ τ₈₂ K₈₂ M : ℝ, 0 < τ₈₂ ∧ τ₈₂ ≤ 1 ∧ 0 < K₈₂ ∧
    M = 2 * Real.sqrt 3 * (K₈₂ / τ₈₂ + 2) ∧
    ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
      (r0 K : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
      (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
        (H.activeStage_mono hat) x0),
      0 < r0 → (a : ℝ) = top - τ₈₂ / 2 * r0 ^ 2 →
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
      (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
        (top : ℝ) - τ₈₂ / 2 * r0 ^ 2 / 2 ≤ v →
        ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (r0 / 4),
          Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
              (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ M / r0 ^ 2) ∧
      ENNReal.ofReal (w * (r0 / 4) ^ 3 / 10) ≤
        ballVolume (H.stageMetric (H.activeStage a) a)
          (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 4) := by
  intro w hw
  obtain ⟨τ₀, K₀, hτ₀, hτ₀1, hK₀, hmain⟩ := kl82_1_R_O78.{u} w hw
  refine ⟨τ₀, K₀, 2 * Real.sqrt 3 * (K₀ / τ₀ + 2), hτ₀, hτ₀1, hK₀, rfl, ?_⟩
  intro H top x0 r0 K a hat X hr0 ha hEvt hRfin hsec hvol
  have hD : 0 < τ₀ / 2 := by positivity
  obtain ⟨h1, h2⟩ := hmain H top x0 r0 (τ₀ / 2) K a hat X hr0 hD (by linarith) ha hEvt hRfin
    hsec hvol
  refine ⟨?_, h2⟩
  intro v hav hvt hv q hq
  have hp : 0 ≤ τ₀ * r0 ^ 2 := by positivity
  have hv' : (top : ℝ) - 3 / 4 * (τ₀ / 2) * r0 ^ 2 ≤ v := by nlinarith
  have hR := h1 v hav hvt hv' q hq
  have hqr0 : q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
      (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0 :=
    riemannianBallOf_mono _ _ (by linarith) hq
  have hRm := rm_normSq_le_of_sec_O30 _ q (κ := (r0 ^ 2)⁻¹)
    (Λ := K₀ * (τ₀ / 2)⁻¹ * (r0 ^ 2)⁻¹) (by positivity) (by positivity) (hsec v hav hvt q hqr0) hR
  have hc : 0 ≤ 2 * Real.sqrt 3 * (K₀ * (τ₀ / 2)⁻¹ * (r0 ^ 2)⁻¹ / 2 + 2 * (r0 ^ 2)⁻¹) := by
    positivity
  refine (Real.sqrt_le_sqrt hRm).trans (le_of_eq ?_)
  rw [Real.sqrt_sq hc]
  have hτ₀' : τ₀ ≠ 0 := hτ₀.ne'
  have hr0' : r0 ≠ 0 := hr0.ne'
  field_simp

end GC.LongTime.Ch12
