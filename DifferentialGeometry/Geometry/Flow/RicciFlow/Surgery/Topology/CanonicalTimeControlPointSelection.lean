import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Backward
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

private theorem floor_div_lt_floor_div_of_two_mul_le {K R R' : Real}
    (hR : 0 < R) (hRR : 2 * R ≤ R') (hRK : R' ≤ K) :
    ⌊K / R'⌋₊ < ⌊K / R⌋₊ := by
  have hR2 : (0 : Real) < 2 * R := by linarith
  have hR' : (0 : Real) < R' := lt_of_lt_of_le hR2 hRR
  have hK : (0 : Real) ≤ K := le_trans hR'.le hRK
  have hKR : (2 : Real) ≤ K / R := by
    rw [le_div_iff₀ hR]
    linarith
  have hstep : K / R' ≤ K / R / 2 := by
    have h1 : K / R' ≤ K / (2 * R) := div_le_div_of_nonneg_left hK hR2 hRR
    have h2 : K / R / 2 = K / (2 * R) := by
      rw [div_div, mul_comm]
    rw [h2]
    exact h1
  have hhalf : (0 : Real) ≤ K / R / 2 := by linarith
  have hfloor1 : ⌊K / R'⌋₊ ≤ ⌊K / R / 2⌋₊ := Nat.floor_le_floor hstep
  have hfloor2 : ⌊K / R / 2⌋₊ + 1 ≤ ⌊K / R⌋₊ := by
    refine Nat.le_floor ?_
    have hle : ((⌊K / R / 2⌋₊ : ℕ) : Real) ≤ K / R / 2 := Nat.floor_le hhalf
    push_cast
    linarith
  omega

/-- The spatial canonical witness and the actual one-sided scalar time bound.
The time bound is required only at positive stage age below the observation horizon. -/
def HasSpatialCanonicalTimeControl
    (H : ObservedHistory.{u}) (eps C1 C2 : ℝ) (Ctime : ℝ≥0)
    (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier) : Prop :=
  (∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) eps C1 C2 z,
    W.capTubeHasNeckChart eps) ∧
  (H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
    |derivWithin (fun t => metricScalarAt (H.stageMetric (H.activeStage v) t) z)
      (Iic (v : ℝ)) v| ≤
      Ctime * metricScalarAt (H.stageMetric (H.activeStage v) v) z ^ 2)

/-- Finite moving-seed selection for the full produced spatial and time predicate. -/
theorem exists_localized_canonical_time_control_point_selection
    (H : ObservedHistory.{u}) (q : CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcanonical : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt (H.stageMetric (H.activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.stageMetric (H.activeStage v) v) z ^ 2)
    (T : Icc (0 : ℝ) H.horizon) (p : (H.stageAt T).Carrier)
    (r A L : ℝ) (hr : 0 < r) (hA : 0 < A) (hL : 0 < L)
    (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ T)
    (haSeed : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) p)
    (x : (H.stageAt T).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage T) T) p (A * r))
    (hR : 0 < metricScalarAt (H.stageMetric (H.activeStage T) T) x)
    (hbad : ¬ H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' T x)
    (htime : 2 * L ^ 2 / metricScalarAt (H.stageMetric (H.activeStage T) T) x ≤
      r ^ 2 / 2)
    (hspace : 2 * L / Real.sqrt (metricScalarAt (H.stageMetric (H.activeStage T) T) x) ≤
      r / 2) :
    ∃ (s : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ s) (hsT : s ≤ T)
      (y : (H.stageAt s).Carrier),
    let Q := metricScalarAt (H.stageMetric (H.activeStage s) s) y
    let R0 := metricScalarAt (H.stageMetric (H.activeStage T) T) x
    let O := seedTrace.point (H.activeStage s) (H.activeStage_mono has)
      (H.activeStage_mono hsT)
    (¬ H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' s y) ∧
    0 < Q ∧ R0 ≤ Q ∧ Q ≤ (q.neckRadius T ^ 2)⁻¹ ∧
    (T : ℝ) - 2 * L ^ 2 / R0 ≤ (s : ℝ) - 2 * L ^ 2 / Q ∧
    (T : ℝ) - r ^ 2 / 2 ≤ (s : ℝ) - L ^ 2 / Q ∧
    riemannianEDistOf (H.stageMetric (H.activeStage s) s) O y +
        ENNReal.ofReal (2 * L / Real.sqrt Q) ≤
      riemannianEDistOf (H.stageMetric (H.activeStage T) T) p x +
        ENNReal.ofReal (2 * L / Real.sqrt R0) ∧
    y ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) O ((A + 1) * r) ∧
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ s),
      (s : ℝ) - L ^ 2 / Q ≤ (v : ℝ) →
    ∀ z : (H.stageAt v).Carrier,
      riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono (hvs.trans hsT))) z ≤
        riemannianEDistOf (H.stageMetric (H.activeStage s) s) O y +
          ENNReal.ofReal (L / Real.sqrt Q) →
      4 * Q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z := by
  classical
  let R (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier) : ℝ :=
    metricScalarAt (H.stageMetric (H.activeStage v) v) z
  let Good (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier) : Prop :=
    H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z
  let K : ℝ := (q.neckRadius T ^ 2)⁻¹
  let d (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvT : v ≤ T)
      (z : (H.stageAt v).Carrier) : ℝ≥0∞ :=
    riemannianEDistOf (H.stageMetric (H.activeStage v) v)
      (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
        (H.activeStage_mono hvT)) z
  -- Only bad points need the global ceiling. It is used solely for termination.
  have hceiling (v : Icc (0 : ℝ) H.horizon) (hvT : v ≤ T)
      (z : (H.stageAt v).Carrier) (hb : ¬ Good v z) : R v z ≤ K := by
    have hlocal : R v z ≤ (q.neckRadius v ^ 2)⁻¹ := by
      by_contra hnot
      have hhigh : (q.neckRadius v ^ 2)⁻¹ < R v z := lt_of_not_ge hnot
      obtain ⟨W, hW⟩ := hcanonical v z hhigh
      apply hb
      refine ⟨⟨W.enlargeConstants hC1 hC2, hW.enlarge_constants hC1 hC2⟩, ?_⟩
      intro hage htop
      exact (hderivative v z hage htop hhigh).trans
        (mul_le_mul_of_nonneg_right (show (Ctime : ℝ) ≤ Ctime' from hCtime)
          (sq_nonneg _))
    have hrT := q.neckRadius_pos T T.2.1
    have hrv := q.neckRadius_pos v v.2.1
    have hrad : q.neckRadius T ≤ q.neckRadius v := hanti v.2.1 T.2.1 hvT
    have hsq : q.neckRadius T ^ 2 ≤ q.neckRadius v ^ 2 := by nlinarith
    exact hlocal.trans ((inv_le_inv₀ (sq_pos_of_pos hrv) (sq_pos_of_pos hrT)).mpr hsq)
  -- Strong induction is the existing floor-descent proof, with the same trace
  -- and both quantitative debts retained at every recursive choice.
  have hselect : ∀ n : ℕ,
      ∀ (s : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ s) (hsT : s ≤ T)
        (y : (H.stageAt s).Carrier),
      ⌊K / R s y⌋₊ = n → ¬ Good s y → 0 < R s y →
      ∃ (s' : Icc (0 : ℝ) H.horizon) (has' : aSeed ≤ s') (hs'T : s' ≤ T)
        (y' : (H.stageAt s').Carrier),
        (¬ Good s' y') ∧ 0 < R s' y' ∧ R s y ≤ R s' y' ∧ s' ≤ s ∧
        (s : ℝ) - 2 * L ^ 2 / R s y ≤ (s' : ℝ) - 2 * L ^ 2 / R s' y' ∧
        d s' has' hs'T y' + ENNReal.ofReal (2 * L / Real.sqrt (R s' y')) ≤
          d s has hsT y + ENNReal.ofReal (2 * L / Real.sqrt (R s y)) ∧
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs' : v ≤ s'),
          (s' : ℝ) - L ^ 2 / R s' y' ≤ (v : ℝ) →
        ∀ z : (H.stageAt v).Carrier,
          d v hav (hvs'.trans hs'T) z ≤
            d s' has' hs'T y' + ENNReal.ofReal (L / Real.sqrt (R s' y')) →
          4 * R s' y' ≤ R v z → Good v z := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s has hsT y hn hb hQ
      by_cases hex : ∃ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v)
          (hvs : v ≤ s) (z : (H.stageAt v).Carrier),
          (s : ℝ) - L ^ 2 / R s y ≤ (v : ℝ) ∧
          d v hav (hvs.trans hsT) z ≤
            d s has hsT y + ENNReal.ofReal (L / Real.sqrt (R s y)) ∧
          4 * R s y ≤ R v z ∧ ¬ Good v z
      · obtain ⟨v, hav, hvs, z, htimeStep, hdistStep, hfour, hbadStep⟩ := hex
        have hQ' : 0 < R v z := by linarith
        have htwo : 2 * R s y ≤ R v z := by linarith
        have htimeHalf : 2 * L ^ 2 / R v z ≤ L ^ 2 / R s y := by
          calc
            2 * L ^ 2 / R v z ≤ 2 * L ^ 2 / (2 * R s y) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) htwo
            _ = L ^ 2 / R s y :=
              mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)
        have htimeDebt : (s : ℝ) - 2 * L ^ 2 / R s y ≤
            (v : ℝ) - 2 * L ^ 2 / R v z := by
          have hdouble : 2 * L ^ 2 / R s y = 2 * (L ^ 2 / R s y) := by ring
          linarith
        have hroot : 2 * Real.sqrt (R s y) ≤ Real.sqrt (R v z) := by
          apply Real.le_sqrt_of_sq_le
          nlinarith [Real.sq_sqrt hQ.le]
        have hspaceHalf : 2 * L / Real.sqrt (R v z) ≤ L / Real.sqrt (R s y) := by
          calc
            2 * L / Real.sqrt (R v z) ≤ 2 * L / (2 * Real.sqrt (R s y)) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hroot
            _ = L / Real.sqrt (R s y) :=
              mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)
        have hdistDebt : d v hav (hvs.trans hsT) z +
            ENNReal.ofReal (2 * L / Real.sqrt (R v z)) ≤
            d s has hsT y + ENNReal.ofReal (2 * L / Real.sqrt (R s y)) := by
          calc
            _ ≤ (d s has hsT y + ENNReal.ofReal (L / Real.sqrt (R s y))) +
                ENNReal.ofReal (L / Real.sqrt (R s y)) :=
              add_le_add hdistStep (ENNReal.ofReal_le_ofReal hspaceHalf)
            _ = _ := by
              rw [add_assoc, ← ENNReal.ofReal_add (by positivity : 0 ≤ L / Real.sqrt (R s y))
                (by positivity : 0 ≤ L / Real.sqrt (R s y)),
                show L / Real.sqrt (R s y) + L / Real.sqrt (R s y) =
                  2 * L / Real.sqrt (R s y) by ring]
        have hlt : ⌊K / R v z⌋₊ < ⌊K / R s y⌋₊ :=
          floor_div_lt_floor_div_of_two_mul_le hQ htwo
            (hceiling v (hvs.trans hsT) z hbadStep)
        rw [hn] at hlt
        obtain ⟨s', has', hs'T, y', hb', hQ'', hRle, hs'v, htime', hdist', hgood⟩ :=
          ih _ hlt v hav (hvs.trans hsT) z rfl hbadStep hQ'
        exact ⟨s', has', hs'T, y', hb', hQ'', by linarith,
          hs'v.trans hvs, htimeDebt.trans htime', hdist'.trans hdistDebt, hgood⟩
      · refine ⟨s, has, hsT, y, hb, hQ, le_rfl, le_rfl, le_rfl, le_rfl, ?_⟩
        intro v hav hvs htime' z hdist' hfour
        by_contra hnot
        exact hex ⟨v, hav, hvs, z, htime', hdist', hfour, hnot⟩
  have hseedStart : (aSeed : ℝ) ≤ (T : ℝ) - 2 * L ^ 2 / R T x := by
    rw [haSeed]
    change 2 * L ^ 2 / R T x ≤ r ^ 2 / 2 at htime
    nlinarith [sq_nonneg r]
  have hstart : aSeed ≤ T :=
    hseedStart.trans (sub_le_self _ (by positivity))
  obtain ⟨s, has, hsT, y, hb, hQ, hRle, _, htimeDebt, hdistDebt, hgood⟩ :=
    hselect _ T hstart le_rfl x rfl hbad hR
  refine ⟨s, has, hsT, y, hb, hQ, hRle, hceiling s hsT y hb, htimeDebt, ?_, ?_, ?_, ?_⟩
  · have hnonneg : 0 ≤ L ^ 2 / R s y := div_nonneg (sq_nonneg _) hQ.le
    change (T : ℝ) - r ^ 2 / 2 ≤ (s : ℝ) - L ^ 2 / R s y
    change 2 * L ^ 2 / R T x ≤ r ^ 2 / 2 at htime
    have hdouble : 2 * L ^ 2 / R s y = 2 * (L ^ 2 / R s y) := by ring
    linarith
  · simpa only [d, R, seedTrace.endpoint_eq] using hdistDebt
  · change d s has hsT y < ENNReal.ofReal ((A + 1) * r)
    have hx' : d T haT le_rfl x < ENNReal.ofReal (A * r) := by
      simpa only [d, seedTrace.endpoint_eq, riemannianBallOf, mem_ofPred_eq] using hx
    have hdist : d s has hsT y ≤ ENNReal.ofReal (A * r + r / 2) := by
      calc
        d s has hsT y ≤ d s has hsT y + ENNReal.ofReal (2 * L / Real.sqrt (R s y)) :=
          le_add_of_nonneg_right zero_le
        _ ≤ d T haT le_rfl x + ENNReal.ofReal (2 * L / Real.sqrt (R T x)) := hdistDebt
        _ ≤ ENNReal.ofReal (A * r) + ENNReal.ofReal (r / 2) :=
          add_le_add hx'.le (ENNReal.ofReal_le_ofReal hspace)
        _ = ENNReal.ofReal (A * r + r / 2) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    exact hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith))
  · simpa only [R, Good, d] using hgood

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
