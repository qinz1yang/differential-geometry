import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ClaimAssembly_O25

/-!
# CH12-O30, G2: the window-start device and the sub-window volume transfer for claim (C)

Source: corrected w-dependent local variant of KL 82.1 / Perelman II.6.5; not a verbatim
transcription.  The reference PDFs named in AGENTS.md are not on this machine; locators follow
the CX11 report and the DELIVERIES records.

* `exists_late_bad_start_O30`: for a monotone family of window claims that fails at `a` and
  holds at `top`, a failing window start `a'` after which every start `≥ a' + η` is good
  (infimum of the good starts).  This replaces the "latest bad time" step of the O25 plan
  (see "[FROZEN v2] CH12-O30").
* `kl82_window_volume_O30`: O25's Part-2 argument with claim (C) as a hypothesis on the given
  window: the claim on `(a, top]` and the distance bootstrap give the quarter-ball volume at `a`.
* `traceRestrict_O30`, `isRmBoundedBy_restrict_O30`: restricting a backward trace to a later
  first stage.
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

/-- **Window-start device**: the infimum of the good window starts. -/
theorem exists_late_bad_start_O30 (good : ℝ → Prop) {a top η : ℝ} (hη : 0 < η)
    (hat : a ≤ top) (hmono : ∀ s s', s ≤ s' → good s → good s') (htop : good top)
    (ha : ¬ good a) :
    ∃ a', a ≤ a' ∧ a' < top ∧ ¬ good a' ∧ ∀ s, a' + η ≤ s → good s := by
  classical
  set G : Set ℝ := {s | a ≤ s ∧ good s} with hG
  have hGne : G.Nonempty := ⟨top, hat, htop⟩
  have hGbdd : BddBelow G := ⟨a, fun s hs => hs.1⟩
  set st : ℝ := sInf G with hst
  have hast : a ≤ st := le_csInf hGne fun s hs => hs.1
  have hgood_above : ∀ s, st < s → good s := by
    intro s hs
    obtain ⟨s₀, hs₀, hs₀s⟩ := exists_lt_of_csInf_lt hGne hs
    exact hmono s₀ s hs₀s.le hs₀.2
  set a' : ℝ := max a (st - η / 2) with ha'
  have hbad : ¬ good a' := by
    rcases le_total (st - η / 2) a with h | h
    · rw [ha', max_eq_left h]; exact ha
    · rw [ha', max_eq_right h]
      intro hg
      have : st ≤ st - η / 2 := csInf_le hGbdd ⟨h, hg⟩
      linarith
  refine ⟨a', le_max_left _ _, ?_, hbad, ?_⟩
  · by_contra hle
    exact hbad (hmono top a' (le_of_not_gt hle) htop)
  · intro s hs
    exact hgood_above s (by have := le_max_right a (st - η / 2); linarith)

/-- A backward trace restricted to a later first stage. -/
def traceRestrict_O30 {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {e : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle e)
    {first' : Fin (H.eventCount + 1)} (h : first ≤ first') (hle' : first' ≤ last) :
    BackwardPointTrace H first' last hle' e where
  point j hf hl := A.point j (h.trans hf) hl
  endpoint_eq := A.endpoint_eq
  crossing i hf hl := A.crossing i (h.trans hf) hl

theorem isRmBoundedBy_restrict_O30 {H : ObservedHistory.{u}} {a s t : Icc (0 : ℝ) H.horizon}
    {hat : a ≤ t} (has : a ≤ s) (hst : s ≤ t) {p : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {K : ℝ} (hA : A.isRmBoundedBy (hat := hat) K) :
    (traceRestrict_O30 A (H.activeStage_mono has) (H.activeStage_mono hst)).isRmBoundedBy
      (hat := hst) K :=
  ⟨fun u hsu hut => hA.1 u (has.trans hsu) hut,
    fun i hf hl => hA.2 i ((H.activeStage_mono has).trans hf) hl⟩

/-- **Sub-window volume transfer** (O25 Part 2 with claim (C) as a hypothesis). -/
theorem kl82_window_volume_O30
    (hboot : ∀ (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
      {p q : (H.stageAt t).Carrier}
      (X : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
      (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
      {C ρ R0 : ℝ}, 0 < C → 0 < ρ →
      riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q < ENNReal.ofReal ρ →
      (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) < ρ / 2 →
      (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) +
          Real.sqrt (3 * ((t : ℝ) - a) / C) < R0 →
      (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ρ,
          Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage v)
            (H.activeStage_mono hav) z)) →
      (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (a : ℝ) < v →
        ∀ z : (H.stageAt v).Carrier,
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) z <
            ENNReal.ofReal R0 →
          ∀ w : TangentSpace ThreeModel z,
            ricciTensor (H.stageMetric (H.activeStage v) v) z w w ≤
              C / ((v : ℝ) - a) * (H.stageMetric (H.activeStage v) v).inner z w w) →
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        traceEDist_CX11 H (hat := hat) X A v hav hvt ≤
          ENNReal.ofReal ((riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
            16 * Real.sqrt (C / 3) * (Real.sqrt ((t : ℝ) - a) - Real.sqrt ((v : ℝ) - a))))
    (C₀ B₀ : ℝ) (hC₀ : 0 ≤ C₀) (hB₀ : 0 ≤ B₀) :
    ∃ τw : ℝ, 0 < τw ∧ τw ≤ 1 ∧
      ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
        (r0 τ K w : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
        (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
          (H.activeStage_mono hat) x0),
        0 < w → 0 < r0 → 0 < τ → τ ≤ τw → (a : ℝ) = top - τ * r0 ^ 2 →
            (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
              ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                  (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
                ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
                    (H.activeStage_mono hav) q, A.isRmBoundedBy (hat := hav) K) →
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
  obtain ⟨τ₁, hτ₁, -, hVT⟩ := volume_transfer_of_distance_CX11.{u} C'
  set τ₂ : ℝ := min (C' / 768) (3 / (65536 * C')) with hτ₂
  have hτ₂pos : 0 < τ₂ := lt_min (by positivity) (by positivity)
  refine ⟨min (min τ₁ 1) τ₂, lt_min (lt_min hτ₁ one_pos) hτ₂pos,
    (min_le_left _ _).trans (min_le_right _ _), ?_⟩
  intro H top x0 r0 τ K w a hat X hw hr0 hτ hτ0 ha hSF hsec hvol hclv
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
  have hXtop : X.point (H.activeStage top) (H.activeStage_mono hat)
      (H.activeStage_mono (le_refl top)) = x0 := X.endpoint_eq
  have hSF' : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
      ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
        Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage v)
          (H.activeStage_mono hav) z) := by
    intro v hav hvt z hz
    obtain ⟨A, -⟩ := hSF v hav hvt z hz
    exact ⟨A⟩
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
  refine hVT H a top hat x0 X w r0 τ K hw hr0 hτ hτ₁' ha ?_ hsec ?_ hvol
  · intro q hq
    have hq' : q ∈ riemannianBallOf (H.stageMetric (H.activeStage top) top)
        (X.point (H.activeStage top) (H.activeStage_mono hat)
          (H.activeStage_mono (le_refl top))) r0 := by
      rw [hXtop]
      exact hq
    exact hSF top hat (le_refl top) q hq'
  · intro q hq A v hav hvt
    have hd : riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q <
        ENNReal.ofReal (r0 / 4) := hq
    have hne := ne_top_of_lt hd
    have hdlt : (riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q).toReal <
        r0 / 4 := ENNReal.toReal_lt_of_lt_ofReal hd
    have hdr0 : riemannianEDistOf (H.stageMetric (H.activeStage top) top) x0 q <
        ENNReal.ofReal r0 := lt_of_lt_of_le hd (ENNReal.ofReal_le_ofReal (by linarith))
    have hb := hboot H hat X A (C := C') (ρ := r0) (R0 := 3 * r0 / 8) hC'pos hr0 hdr0
      (by linarith) (by linarith) hSF' hRic v hav hvt
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

end GC.LongTime.Ch12
