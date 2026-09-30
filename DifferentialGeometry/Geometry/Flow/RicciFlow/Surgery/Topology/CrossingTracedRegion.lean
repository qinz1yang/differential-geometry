import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionOrCapWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAt
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingPersistenceInputs

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

private theorem capWindowPoint_of_stage_eq
    {H : RetainedCoreHistory.{u}} {p : CutoffParameters}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    {k k' : Fin (H.eventCount + 1)} (hk : k = k') {y : (H.stage k).Carrier}
    {y' : (H.stage k').Carrier} (hy : HEq y y') {t D θ : ℝ}
    (h : H.CapWindowPoint records k y t D θ) : H.CapWindowPoint records k' y' t D θ := by
  subst hk
  cases hy
  exact h

private theorem derivativeBoundBefore_double {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} {Ctime : ℝ≥0} {q t₀ : ℝ} (hq : 0 ≤ q)
    (h : G.DerivativeBoundBefore Ctime q t₀) :
    G.DerivativeBoundBefore (2 * Ctime) (2 * q) t₀ := by
  intro y t ht hqy
  refine (h y t ht (by linarith)).trans ?_
  push_cast
  nlinarith [Ctime.coe_nonneg, sq_nonneg (G.flow.scalar t y)]

theorem derivativeBound_inputs_extendAt (H : RetainedCoreHistory.{u})
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s) {Ctime : ℝ≥0} {q : ℝ}
    (hq : 0 ≤ q) (hslab : H.EventSlabsDerivative Ctime q (Fin.last H.eventCount))
    (hder : G.DerivativeBoundBefore (2 * Ctime) (2 * q) t) :
    (H.extendAt hend G hG hat hts).EventSlabsDerivative (2 * Ctime) (2 * q)
        ((H.extendAt hend G hG hat hts).toHistory.activeStage (H.extendAtTime hend G hG hat hts)) ∧
      (∀ j : Fin (H.extendAt hend G hG hat hts).eventCount,
        j.castSucc = (H.extendAt hend G hG hat hts).toHistory.activeStage
          (H.extendAtTime hend G hG hat hts) →
        ((H.extendAt hend G hG hat hts).toHistory.event j).incoming.DerivativeBoundBefore
          (2 * Ctime) (2 * q) (H.extendAtTime hend G hG hat hts)) ∧
      ∀ h : (H.extendAt hend G hG hat hts).time
          (Fin.last (H.extendAt hend G hG hat hts).eventCount) <
          (H.extendAt hend G hG hat hts).horizon,
        (H.extendAt hend G hG hat hts).toHistory.activeStage (H.extendAtTime hend G hG hat hts) =
          Fin.last (H.extendAt hend G hG hat hts).eventCount →
        (((H.extendAt hend G hG hat hts).finalSlab h).restrictIncoming le_rfl h
          le_rfl).DerivativeBoundBefore (2 * Ctime) (2 * q) (H.extendAtTime hend G hG hat hts) := by
  have hlast : (H.extendAt hend G hG hat hts).toHistory.activeStage
      (H.extendAtTime hend G hG hat hts) = Fin.last H.eventCount :=
    H.activeStage_extendHorizon_eq_last (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
      (H.extendAtTime hend G hG hat hts) hat.le
  refine ⟨?_, fun j hj => absurd (hj.trans hlast) (Fin.castSucc_lt_last j).ne,
    fun h _ => extendHorizon_finalSlab_derivativeBoundBefore (H := H) (hHT := hend ▸ hat.le)
      hder le_rfl h⟩
  rw [hlast]
  exact fun j hj => derivativeBoundBefore_double hq (hslab j hj)

theorem exists_eventually_isTracedRegion_extendAt_of_scalar_le_along_traces
    {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric} {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {D θcap qcan s t : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
    (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory))
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
      Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hslab : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t n))
    (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (y n))
    (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n)
      (D n) (θcap n))
    {A T Q : ℝ} (hA : 0 < A) (hT : 0 < T) (hQ : 1 ≤ Q) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ n in atTop,
      ∀ ŷ : (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.stageAt
          ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))).Carrier,
      HEq ŷ (y n) →
      ∀ uu : Icc (0 : ℝ) ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.horizon,
        (uu : ℝ) = t n - T / (G n).flow.scalar (t n) (y n) →
      (∀ x ∈ riemannianBallOf
          (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.stageMetric
            (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
            ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))) ŷ
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        ∀ (w : Icc (0 : ℝ)
            ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.horizon)
          (_ : uu ≤ w) (hwt : w ≤ (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n))
          (B : BackwardPointTrace ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory
            (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage w)
            (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage
              ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)))
            (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage_mono
              hwt) x)
          (v : Icc (0 : ℝ)
            ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.horizon)
          (hwv : w ≤ v) (hvt : v ≤ (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)),
          metricScalarAt
              (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.stageMetric
                (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage v)
                v)
            (B.point
              (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage v)
              (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage_mono
                hwv)
              (((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage_mono
                hvt)) ≤
            2 * (Q * (G n).flow.scalar (t n) (y n))) →
      ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.isTracedRegion
        ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) ŷ
        (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))
        (T / (G n).flow.scalar (t n) (y n)) (K₀ * (G n).flow.scalar (t n) (y n)) := by
  obtain ⟨c, hc, hB5⟩ := exists_isTracedRegion_or_capWindowPoint_at_scale.{u}
  have hφ0 := hphi.pos 0
  have hφ1 := hphi.pos 1
  have hTQ : 0 < 8 * T * Q := by positivity
  set θ₁ : ℝ := max (1 / 4) (1 - c / (8 * T * Q)) with hθ₁def
  have hθ₁ : θ₁ < 1 := max_lt (by norm_num) (by have := div_pos hc hTQ; linarith)
  have hΘ0 : 0 < (θ₁ + 1) / 2 := by
    have := le_max_left (1 / 4 : ℝ) (1 - c / (8 * T * Q))
    linarith
  obtain ⟨Cbirth, hCb, hB5⟩ := hB5 ((θ₁ + 1) / 2) hΘ0 (by linarith) (2 * Ctime)
  set Dcap : ℝ := 2 * StandardCap.transitionEnd + Real.sqrt (8 * Q) *
    Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Q * T) * A + 1 with hDcap
  have hDs : StandardCap.transitionEnd < Dcap := by
    have := StandardCap.transitionEnd_pos
    have : 0 ≤ Real.sqrt (8 * Q) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Q * T) * A := by positivity
    linarith
  obtain ⟨Rrad, -, m₀, -, ζ₀, δ₀, hζ₀, -, hδ₀, hB5⟩ := hB5 Dcap hDs
  obtain ⟨a₀, -, hHI, hev⟩ := exists_capWindow_persistence_inputs_eventually
    (t₀ := fun n => (H n).time (Fin.last (H n).eventCount)) hinit hrec hGi hslab
    (fun n => ⟨⟨le_rfl, (hat n).trans (hts n)⟩,
      fun _ _ hv _ => absurd (hv.1.trans hv.2) (lt_irrefl _)⟩) hqcan hpar hscale
  have hDev : ∀ᶠ n : ℕ in atTop, Dcap ≤ D n := by
    obtain ⟨N, hN⟩ := exists_nat_ge Dcap
    filter_upwards [eventually_ge_atTop N] with n hn
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith [(hpar n).2.1]
  have hθev : ∀ᶠ n : ℕ in atTop, θ₁ ≤ θcap n := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - θ₁))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 0 < 1 - θ₁ := by linarith
    have h2 : 1 / ((n : ℝ) + 2) ≤ 1 - θ₁ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ h1] at hN
      nlinarith
    linarith [hθcap n]
  refine ⟨8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Q, by positivity, ?_⟩
  filter_upwards [hev Rrad ζ₀ δ₀ (Cbirth / 2) m₀ hζ₀ hδ₀ (half_pos hCb), hDev, hθev]
    with n hn hDn hθn
  obtain ⟨hδn, hRn, hmn, hζn, hbirth, hq0, -, -, -, -⟩ := hn
  intro ŷ hŷ uu huu hscal
  obtain ⟨records', hfam', hsc', hiff⟩ := (H n).capWindowPoint_extendHorizon_iff (records n)
    ((hend n) ▸ (hat n).le) ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n)
  have hR0 : 0 < (G n).flow.scalar (t n) (y n) := hq0.trans (hqR n)
  have hq1 : 1 ≤ qcan n := le_trans (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (hqcan n)
  have hlast : ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory.activeStage
      ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) =
        Fin.last (H n).eventCount :=
    (H n).activeStage_extendHorizon_eq_last ((hend n) ▸ (hat n).le)
      ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n)
      ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) (hat n).le
  have hut : uu ≤ (H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n) := by
    change (uu : ℝ) ≤ t n
    rw [huu]
    linarith [div_pos hT hR0]
  have hdin := (H n).derivativeBound_inputs_extendAt (hend n) (G n) (hGi n) (hat n) (hts n)
    (by linarith) (hslab n) (hderG n)
  rcases hB5 ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)) (p₀ n) (δb n) (ρb n)
      records' (hfam' _ _ _ (hrec n)) hδn hRn hmn hζn (2 * qcan n) a₀ (by linarith)
      (fun x => (hHI n x).1) (fun x => (hHI n x).2)
      (fun i b => le_of_le_of_eq (by linarith [(hbirth i b).1])
        (congrArg (Cbirth * ·) (hsc' i b).symm))
      (fun i b => le_of_le_of_eq (hbirth i b).2 (congrArg (a₀ * ·) (hsc' i b).symm)) phi hphi
      (hpinch n).1 uu
      ((H n).extendAtTime (hend n) (G n) (hGi n) (hat n) (hts n)) hut
      (fun _ => extendHorizon_finalSlab_phiAlmostNonnegative (H := H n)
        (hHT := (hend n) ▸ (hat n).le) (hpinch n).2)
      hdin.1 hdin.2.1 hdin.2.2 ŷ
      ((G n).flow.scalar (t n) (y n)) A T Q Dcap θ₁ hR0 hA hT
      (by nlinarith [hqR n]) huu
      (le_max_left _ _) (le_max_right _ _) (by linarith) le_rfl hscal
      (by rw [hDcap]; linarith) with htr | hcw
  · rw [mul_assoc]
    exact htr
  · obtain ⟨j, hl, B, b, x, hx, hxn, hage⟩ :=
      (hiff (y n) (t n) Dcap θ₁).mp (capWindowPoint_of_stage_eq hlast hŷ hcw)
    exact absurd ⟨j, hl, B, b, x, hx, by linarith, hage.trans (mul_le_mul_of_nonneg_right hθn
      (inv_nonneg.mpr ((records n j).static b).neck.scale_pos.le))⟩ (hnot n)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
