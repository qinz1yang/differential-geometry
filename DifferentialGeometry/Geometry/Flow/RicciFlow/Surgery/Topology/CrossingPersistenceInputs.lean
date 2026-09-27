import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped NNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_capWindow_persistence_inputs_eventually {P₀ : OrientedThreeStage.{u}}
    {g₀ : P₀.Metric} {Ctime : ℝ≥0} {D qcan t₀ s : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters}
    {δb ρb : ℕ → ℝ} {H : ℕ → RetainedCoreHistory P₀}
    {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
    {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n)}
    (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory))
    (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
    (hGinit : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hslabs : ∀ n, (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount))
    (hbefore : ∀ n, t₀ n ∈ Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∧
      (G n).DerivativeBoundBefore Ctime (qcan n) (t₀ n))
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((H n).initialMetric 0) x) ∧
      ∀ (Rw ζ₀ δ₀ Cbirth : ℝ) (m₀ : ℕ), 0 < ζ₀ → 0 < δ₀ → 0 < Cbirth → ∀ᶠ n in atTop,
        δb n ≤ δ₀ ∧ Rw ≤ (p₀ n).modelRadius ∧ m₀ ≤ (p₀ n).modelOrder ∧
        (p₀ n).modelAccuracy ≤ ζ₀ ∧
        (∀ i b, qcan n ≤ Cbirth * ((records n i).static b).neck.scale ∧
          1 ≤ a₀ * ((records n i).static b).neck.scale) ∧
        0 < qcan n ∧ (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n) ∧
        (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
          (H n).initialMetric (Fin.last (H n).eventCount) ∧
        (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount) ∧
        ∀ v : ℝ, (H n).time (Fin.last (H n).eventCount) < v → v ≤ t₀ n →
          v < s n ∧ (G n).DerivativeBoundBefore Ctime (qcan n) v := by
  obtain ⟨a₀, ha₀, hHI⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  refine ⟨a₀, ha₀, fun n x => ?_, ?_⟩
  · obtain ⟨A⟩ := hinit n
    exact ⟨(hHI _ A).1 x, (hHI _ A).2 x⟩
  intro Rw ζ₀ δ₀ Cbirth m₀ hζ₀ hδ₀ hC
  have hinv : ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ c := by
    intro c hc
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / c)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_iff₀ (by positivity)]
    have := (div_lt_iff₀ hc).mp hN
    nlinarith
  have hbig : ∀ c : ℝ, ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) + 1 := by
    intro c
    obtain ⟨N, hN⟩ := exists_nat_gt c
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  filter_upwards [hinv δ₀ hδ₀, hinv ζ₀ hζ₀, hbig Rw, eventually_ge_atTop m₀, hbig (1 / Cbirth),
    hbig (1 / a₀)] with n hδ hζ hR hm hCb ha
  obtain ⟨hacc, hD, hrad, hord, hdel⟩ := hpar n
  have hq := hqcan n
  have hq0 : 0 < qcan n := lt_of_lt_of_le (by positivity) hq
  refine ⟨hdel.trans hδ, hR.trans (hD.trans hrad), le_trans hm (by omega), hacc.trans hζ,
    fun i b => ?_, hq0, hrec n, hGinit n, hslabs n, fun v _ hv =>
      ⟨hv.trans_lt (hbefore n).1.2, (G n).derivativeBoundBefore_mono hv (hbefore n).2⟩⟩
  have hs := hscale n i b
  have hCb' : 1 ≤ Cbirth * ((n : ℝ) + 1) := by
    rw [div_le_iff₀ hC] at hCb
    linarith
  have ha' : 1 ≤ a₀ * ((n : ℝ) + 1) := by
    rw [div_le_iff₀ ha₀] at ha
    linarith
  constructor
  · calc qcan n ≤ Cbirth * ((n : ℝ) + 1) * qcan n := le_mul_of_one_le_left hq0.le hCb'
      _ = Cbirth * (((n : ℝ) + 1) * qcan n) := by ring
      _ ≤ Cbirth * ((records n i).static b).neck.scale := mul_le_mul_of_nonneg_left hs hC.le
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hsq : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) * qcan n := by nlinarith
    calc (1 : ℝ) ≤ a₀ * ((n : ℝ) + 1) := ha'
      _ ≤ a₀ * (((n : ℝ) + 1) * qcan n) := mul_le_mul_of_nonneg_left hsq ha₀.le
      _ ≤ a₀ * ((records n i).static b).neck.scale := mul_le_mul_of_nonneg_left hs ha₀.le

theorem RetainedCoreHistory.CapWindowPoint.exists_standard_comparison_anchor
    {P₀ : OrientedThreeStage.{u}} {H : RetainedCoreHistory P₀} {p : CutoffParameters}
    {records : ∀ i, GeometricCutoffRecord H.toHistory i p} {k : Fin (H.eventCount + 1)}
    {y : (H.stage k).Carrier} {t Dcap D θ Θ : ℝ} (hD : Dcap ≤ D) (hθ : θ ≤ Θ)
    (hy : H.CapWindowPoint records k y t Dcap θ) :
    ∃ (j : Fin H.eventCount) (hl : j.succ ≤ k) (A : BackwardPointTrace H.toHistory j.succ k hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j).static b).window x ∧
      t - H.time j.succ ≤ Θ * (((records j).static b).neck.scale)⁻¹ ∧ ‖x.val‖ < D + 1 := by
  obtain ⟨j, hl, A, b, x, hA, hx, hage⟩ := hy
  exact ⟨j, hl, A, b, x, hA, hage.trans (mul_le_mul_of_nonneg_right hθ
    (inv_nonneg.mpr ((records j).static b).neck.scale_pos.le)), by linarith⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
