import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MetricCompare_S107
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrQuad_S70
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutoffThreshold_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WeakBootstrap_S93
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility

set_option autoImplicit false

/-!
# CH12-S117 / G2: sharp comparison along the lift, and `hevS` at the F level

* `metric_compare_sharp_S117` : the chain factor `(s/t)^η ≤ 1 + η` (`s ≤ 2t`, `η ≤ 1`) and the order-0 closeness
  `ckErr_S45 H g_t t⁻¹ J 0 < δ` give `ckErr_S45 H g_s s⁻¹ (ψ_last ∘ φ) 0 < ε` whenever `10 η ≤ ε`, `10 δ ≤ ε ≤ 1`.
* `hevS_S117` : the `hevS` binder of `himprove_of_regular_S107` (closed step at an event time) for the tower
  history `(F.tower.history n).toHistory`: `weak_closed_event_S93` with `η/2`, `Λ = 100`, the cutoff data from
  `Hp.recent_cutoff_smallness` (nominal radius `≤ 1/100`) and `eventually_recent_cutoff_accuracy_CX2`.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Hyperbolic GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u v

theorem mfderiv_val_lift_S117 (K : ObservedHistory.{u}) (j0 last : Fin (K.eventCount + 1))
    (hle : j0 ≤ last) {X : Type v} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (φ : X → K.backwardSurvivorDomain j0 last hle) {B : Set X} (hB : IsOpen B)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ B) {p : X} (hp : p ∈ B) (w : TangentSpace (𝓡 3) p) :
    mfderiv (𝓡 3) (𝓡 3) (fun q => (φ q).val) p w = mfderiv (𝓡 3) (𝓡 3) φ p w := by
  have hφd : MDifferentiableAt (𝓡 3) (𝓡 3) φ p :=
    (hφ.contMDiffAt (hB.mem_nhds hp)).mdifferentiableAt (by decide)
  have hval := (hasMFDerivAt_subtype_val (I := 𝓡 3) (K.backwardSurvivorDomain j0 last hle)
    (φ p)).mdifferentiableAt
  have hc : mfderiv (𝓡 3) (𝓡 3) (fun q => (φ q).val) p =
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : K.backwardSurvivorDomain j0 last hle → _)
        (φ p)).comp (mfderiv (𝓡 3) (𝓡 3) φ p) := mfderiv_comp p hval hφd
  rw [hc]
  simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
  rfl

theorem metric_compare_sharp_S117 (H : FiniteVolumeHyperbolicModel.{u}) (K : ObservedHistory.{u})
    (j0 : Fin (K.eventCount + 1)) (J : H.Carrier → (K.stage j0).Carrier) {t s η δ ε : ℝ}
    (ht0 : 0 < t) (hts : t ≤ s) (hs2 : s ≤ 2 * t) (hs : s ≤ K.horizon) (hη0 : 0 ≤ η)
    (hδ0 : 0 ≤ δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 10 * η ≤ ε) (hδ : 10 * δ ≤ ε)
    (hj0 : actS_S70 K t = j0) {last : Fin (K.eventCount + 1)} (hlast : actS_S70 K s = last)
    (hle : j0 ≤ last) {B : Set H.Carrier} (hB : IsOpen B)
    (hW : ∀ r ∈ Icc t s, DefectAllAt_S85 K j0 J B η r)
    (φ : H.Carrier → K.backwardSurvivorDomain j0 last hle)
    (hφ : ContMDiffOn ThreeModel ThreeModel ∞ φ B)
    (hφJ : ∀ p ∈ B, K.backwardSurvivorMap j0 last hle j0 le_rfl hle (φ p) = J p)
    (hck : ∀ p ∈ B, ckErr_S45 H (K.stageMetric j0 t) t⁻¹ J 0 p < δ) :
    ∀ p ∈ B, ckErr_S45 H (K.stageMetric last s) s⁻¹ (fun q => (φ q).val) 0 p < ε := by
  intro p hp
  have hs0 : 0 < s := ht0.trans_le hts
  have hη1 : η ≤ 1 / 10 := by linarith
  have hδ1 : δ ≤ 1 / 10 := by linarith
  have hν : (s / t) ^ η ≤ 1 + η := by
    have h2 : s / t ≤ 2 := by rw [div_le_iff₀ ht0]; linarith
    have h0 : 0 ≤ s / t := (div_pos hs0 ht0).le
    calc (s / t) ^ η ≤ (2 : ℝ) ^ η := Real.rpow_le_rpow h0 h2 hη0
      _ = (1 + 1) ^ η := by norm_num
      _ ≤ 1 + η * 1 := rpow_one_add_le_one_add_mul_self (by norm_num) hη0 (by linarith)
      _ = 1 + η := by ring
  have hνpos : 0 < (s / t) ^ η := Real.rpow_pos_of_pos (div_pos hs0 ht0) _
  have hch := fun w => metric_chain_S107 K j0 J B ht0 hts hs hj0 hW hlast hle p hp (φ p)
    (hφJ p hp) w
  refine lt_of_le_of_lt (ckErr_zero_le_of_quad_S70 H (K.stageMetric last s) s⁻¹ (fun q => (φ q).val) p
    (e := 3 * ε / 10) (by linarith) (fun w => ?_)) (by linarith)
  rw [mfderiv_val_lift_S117 K j0 last hle φ hB hφ hp w]
  have hch' := hch (mfderiv ThreeModel ThreeModel φ p w)
  rw [pushInner_eq_pullback_S107 H K j0 last hle J hB φ hφ hφJ t hp w] at hch'
  have hlo := pullback_inner_ge_of_ckErr_S90 H (K.stageMetric j0 t) t⁻¹ J p (hck p hp) w
  have hup := pullback_inner_le_of_ckErr_S49 H (K.stageMetric j0 t) t⁻¹ J p (hck p hp) w
  set a := t⁻¹ * (K.stageMetric j0 t).inner (J p) (mfderiv ThreeModel ThreeModel J p w)
    (mfderiv ThreeModel ThreeModel J p w) with ha
  set b := s⁻¹ * (K.stageMetric last s).inner (φ p).val (mfderiv ThreeModel ThreeModel φ p w)
    (mfderiv ThreeModel ThreeModel φ p w) with hb
  have hch1 : a ≤ (s / t) ^ η * b := by simpa only [ha, hb, div_eq_inv_mul] using hch'.1
  have hch2 : b ≤ (s / t) ^ η * a := by simpa only [ha, hb, div_eq_inv_mul] using hch'.2
  have hhh : 0 ≤ H.metric.inner p w w := metric_inner_self_nonneg _ _ _
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact mul_nonneg (inv_nonneg.mpr ht0.le) (metric_inner_self_nonneg _ _ _)
  have hb0 : 0 ≤ b := by
    rw [hb]
    exact mul_nonneg (inv_nonneg.mpr hs0.le) (metric_inner_self_nonneg _ _ _)
  -- upper: `b ≤ (1 + η) a ≤ (1 + η)(1 + δ) h ≤ (1 + e) h`
  have hbup : b ≤ (1 + 3 * ε / 10) * H.metric.inner p w w := by
    have h1 : b ≤ (1 + η) * a := hch2.trans (mul_le_mul_of_nonneg_right hν ha0)
    have h2 : (1 + η) * a ≤ (1 + η) * ((1 + δ) * H.metric.inner p w w) :=
      mul_le_mul_of_nonneg_left hup (by linarith)
    have hηδ : 0 ≤ η * δ := mul_nonneg hη0 hδ0
    have h3 : (1 + η) * (1 + δ) ≤ 1 + 3 * ε / 10 := by nlinarith [hηδ]
    calc b ≤ (1 + η) * ((1 + δ) * H.metric.inner p w w) := h1.trans h2
      _ = ((1 + η) * (1 + δ)) * H.metric.inner p w w := by ring
      _ ≤ (1 + 3 * ε / 10) * H.metric.inner p w w := mul_le_mul_of_nonneg_right h3 hhh
  -- lower: `(1 - δ) h ≤ a ≤ (1 + η) b`
  have hblo : H.metric.inner p w w - b ≤ (3 * ε / 10) * H.metric.inner p w w := by
    have h1 : (1 - δ) * H.metric.inner p w w ≤ (1 + η) * b :=
      hlo.trans (hch1.trans (mul_le_mul_of_nonneg_right hν hb0))
    have h2 : η * b ≤ η * ((1 + 3 * ε / 10) * H.metric.inner p w w) :=
      mul_le_mul_of_nonneg_left hbup hη0
    have h3 : δ + η * (1 + 3 * ε / 10) ≤ 3 * ε / 10 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h3 hhh]
  rw [abs_le]
  constructor <;> nlinarith

/-- `hevS` at the F level: closed step at an event time for the tower history `n` (cutoff records of `Hp`). -/
theorem hevS_S117 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) :
    ∃ T₁ : ℝ, 0 < T₁ ∧ ∀ (n : ℕ) (j0 : Fin ((F.tower.history n).eventCount + 1)) {X : Type v}
      (J : X → ((F.tower.history n).toHistory.stage j0).Carrier) (B : Set X)
      (_hJo : IsOpen (J '' B)) (_hJp : IsPreconnected (J '' B)) (_hBne : B.Nonempty) {η t : ℝ}
      (_hη : η ≤ 2) (_ht : T₁ ≤ t) (i : Fin (F.tower.history n).eventCount),
      j0 ≤ i.castSucc → ∀ t'' : ℝ, t < t'' → t'' < (F.tower.history n).toHistory.time i.succ →
      (F.tower.history n).toHistory.time i.succ ≤ 2 * t →
      (∀ r ∈ Ico t'' ((F.tower.history n).toHistory.time i.succ),
        WeakAt_S85 (F.tower.history n).toHistory j0 J B (η / 2) r) →
      WeakAt_S85 (F.tower.history n).toHistory j0 J B (η / 2)
        ((F.tower.history n).toHistory.time i.succ) := by
  obtain ⟨Ta, hTa, hacc⟩ := eventually_recent_cutoff_accuracy_CX2 Hp hdec
  have hrbar : 0 < Hp.parameters.neckRadius 0 := Hp.parameters.neckRadius_pos 0 le_rfl
  obtain ⟨Tb, hTb, hrecent⟩ :=
    Hp.recent_cutoff_smallness (1 / (100 * Hp.parameters.neckRadius 0)) (by positivity)
  refine ⟨max (max Ta Tb) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro n j0 X J B hJo hJp hBne η t hη ht i hj0 t'' htt'' ht''τ hτ2t hW
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
  have htTa : Ta ≤ t := ((le_max_left _ _).trans (le_max_left _ _)).trans ht
  have htTb : Tb ≤ t := ((le_max_right _ _).trans (le_max_left _ _)).trans ht
  have hτ0 : 0 < (F.tower.history n).toHistory.time i.succ := by linarith
  have hτI : (F.tower.history n).toHistory.time i.succ ∈
      Icc ((F.tower.history n).toHistory.time i.succ / 2) ((F.tower.history n).toHistory.time i.succ) :=
    ⟨by linarith, le_rfl⟩
  refine weak_closed_event_S93 (F.tower.history n).toHistory (Hp.records n i) (Λ := 100) (η := η / 2)
    (by norm_num) (by norm_num) (hacc _ (by linarith) n i hτI) (by linarith) (by linarith) ht''τ
    ?_ hj0 J B hJo hJp hBne hW
  intro h
  have h1 := hrecent _ (by linarith) n i hτI h
  have h2 : Hp.parameters.neckRadius ((F.tower.history n).toHistory.time i.succ) ≤
      Hp.parameters.neckRadius 0 :=
    Hp.radius_antitone (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hτ0.le) hτ0.le
  have h3 : (Hp.records n i).nominalRadius h ≤ 1 / 100 := by
    calc (Hp.records n i).nominalRadius h
        ≤ 1 / (100 * Hp.parameters.neckRadius 0) *
          Hp.parameters.neckRadius ((F.tower.history n).toHistory.time i.succ) := h1
      _ ≤ 1 / (100 * Hp.parameters.neckRadius 0) * Hp.parameters.neckRadius 0 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 / 100 := by field_simp
  have h4 : (1 : ℝ) ≤ Real.sqrt (max t'' ((F.tower.history n).toHistory.time i.castSucc)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by
      exact le_trans (by linarith) (le_max_left _ _))
  linarith

end GC.LongTime.Ch12
