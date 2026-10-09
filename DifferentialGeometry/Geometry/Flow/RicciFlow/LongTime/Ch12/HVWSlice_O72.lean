import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcoreA1Seq_O45
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KcanCentreVolume_O14
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70B1SlicePt_O51
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroWholeBallShi_O13
import DifferentialGeometry.Analysis.Integration.Measure.OpenSubtypeBall
import DifferentialGeometry.Geometry.Collapse.SublevelCore.BufferedMapsAtScale
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Metric.Restriction
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Curvature.RicciRestriction

/-!
# CH12-O72, group G3a: slice volume inputs of the K-can tree (HVW on slices, hvc)

`[FROZEN] CH12-O72 G3a/G3b`.
* `slice_witness_O72` / `hStrongTrue_O72`: canonical witnesses on the slice metric (from
  `sliceSlab_canonical_O3`); the `hStrong` binder of `hA1_O45` with the free neck clause `True`.
* `hA1_unif_O72`: `hA1_O45` with the quantifier order `∀ ℓ, ∀ᶠ n` replaced by `∀ᶠ n, ∀ ℓ`
  (the eventual set of that proof does not depend on `ℓ`; `A1_slice_O45` is the Bishop–Gromov
  chain at each `n`, valid for every `ℓ ≤ 1` at once).
* `hvc_O72`: the centre volume at `y n` at the normalized scale, eventually, for every
  `b ≤ a₀` (`[FROZEN] CH12-O67 hvc` conclusion), from `hA1_unif_O72` at `p := y n`.
* `hvw_slice_O72`: the `hvw` input of `exists_normalized_scalar_bound_of_chain_traces_kcan_O67`
  on slices with `Kv := Hp.C2`, `a₀ := (√C2)⁻¹` (canonical witness at `w` +
  `centre_volume_of_witness_O14`; the round alternative is excluded by `scalar_bounds`, since
  `y` lies in the component of `w` and `C2 · R(y) < R(w)`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter Topology
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

section Slice

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- Canonical witnesses on the slice metric above the neck threshold. -/
theorem slice_witness_O72 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (x : s.stage.Carrier)
    (hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x) :
    ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
      W.capTubeHasNeckChart Hp.epsilon := by
  have h := sliceSlab_canonical_O3 Hp s x (by rw [slice_flow_scalar_O51]; exact hR)
  rw [sliceSlabR_metric_time_O3] at h
  exact h

/-- The `hStrong` binder of `hA1_O45` / `exists_buffered_rcw_O31` with `NK := True`. -/
theorem hStrongTrue_O72 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier,
      ∀ _hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon ∧ True := by
  refine ⟨0, fun s _ x hR => ?_⟩
  obtain ⟨W, hW⟩ := slice_witness_O72 Hp s x hR
  exact ⟨W, hW, trivial⟩

/-- **hA1, uniform in `ℓ`**: `hA1_O45` (with `hStrong := hStrongTrue_O72`) with `∀ ℓ, ∀ᶠ n`
replaced by `∀ᶠ n, ∀ ℓ`. -/
theorem hA1_unif_O72 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    ∀ (s : ℕ → RegularSlice F.observation) (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      1 / 4 ≤ ρ →
      (∀ r : ℝ, 0 < r → r < ρ - (Real.sqrt 2)⁻¹ / 4 → ∃ v : ℝ, 0 < v ∧ ∀ᶠ n in atTop,
        ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ min 1 (ρ - (Real.sqrt 2)⁻¹ / 4 - r) →
          ∀ p ∈ riemannianBallOf (s n).metric (y n) (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
            ENNReal.ofReal (v * (ℓ / Real.sqrt (metricScalarAt (s n).metric (y n))) ^ 3) ≤
              riemannianVolumeMeasure ThreeModel (s n).stage.Carrier (s n).metric
                (riemannianBallOf (s n).metric p (ℓ / Real.sqrt (metricScalarAt (s n).metric (y n))))) := by
  obtain ⟨κ, hκ, hbuf⟩ := exists_buffered_rcw_O31 Hp (fun _ _ _ _ => True) (hStrongTrue_O72 Hp)
  obtain ⟨Phi, hPhi, hpin⟩ := slice_pinch_O45 Hp
  intro s y z ρ htime hneck hRy hratio hbdd hesc hρ r hr hrs
  have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs2n := Real.sqrt_nonneg 2
  have hs2a : 1 < Real.sqrt 2 := by nlinarith
  have hs2b : Real.sqrt 2 ≤ 2 := by nlinarith
  have hs2 : (Real.sqrt 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs2a
  have hs2p : 0 < (Real.sqrt 2)⁻¹ / 4 := by positivity
  have hβpos : 0 < (Real.sqrt Hp.C2)⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos Hp.C2_ge_one))
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max r (ρ - 19 / 50) := ⟨_, rfl⟩
  have hmr : r ≤ m := hm ▸ le_max_left _ _
  have hm19 : ρ - 19 / 50 ≤ m := hm ▸ le_max_right _ _
  have hmpos : 0 < m := lt_of_lt_of_le hr hmr
  have hmrs : m < ρ - (Real.sqrt 2)⁻¹ / 4 := hm ▸ max_lt hrs (by linarith)
  obtain ⟨h0, hh0⟩ : ∃ h0 : ℝ,
      h0 = min (min (1 / 4) ((Real.sqrt Hp.C2)⁻¹ / 2)) ((ρ - (Real.sqrt 2)⁻¹ / 4 - m) / 5) :=
    ⟨_, rfl⟩
  have hh0pos : 0 < h0 := hh0 ▸ lt_min (lt_min (by norm_num) (by positivity)) (by linarith)
  have hh01 : h0 ≤ 1 := hh0 ▸ (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hh0β : h0 ≤ (Real.sqrt Hp.C2)⁻¹ / 2 := hh0 ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hh05 : 5 * h0 ≤ ρ - (Real.sqrt 2)⁻¹ / 4 - m := by
    have := min_le_right (min (1 / 4) ((Real.sqrt Hp.C2)⁻¹ / 2))
      ((ρ - (Real.sqrt 2)⁻¹ / 4 - m) / 5)
    rw [← hh0] at this; linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈m / h0⌉₊ := ⟨_, rfl⟩
  have hN1 : m ≤ N * h0 := by
    have := Nat.le_ceil (m / h0); rw [← hN, div_le_iff₀ hh0pos] at this; exact this
  have hN2 : (N : ℝ) * h0 < m + h0 := by
    have h1 := Nat.ceil_lt_add_one (div_pos hmpos hh0pos).le
    rw [← hN] at h1
    have h2 := mul_lt_mul_of_pos_right h1 hh0pos
    rw [add_mul, div_mul_cancel₀ _ hh0pos.ne', one_mul] at h2
    exact h2
  have hr'ρ : ((N : ℝ) + 4) * h0 < ρ := by linarith only [hN2, hh05, hs2p]
  obtain ⟨C, hC⟩ := hbdd (((N : ℝ) + 4) * h0) hr'ρ
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = max C 1 := ⟨_, rfl⟩
  have hC'1 : 1 ≤ C' := hC' ▸ le_max_right _ _
  have hCC' : C ≤ C' := hC' ▸ le_max_left _ _
  have hPhi1 := hPhi.pos 1
  obtain ⟨Q0, hQ0⟩ : ∃ Q0 : ℝ, Q0 = Real.sqrt (3 * C' * Phi 1 / 2) := ⟨_, rfl⟩
  have hQ0n : 0 ≤ Q0 := hQ0 ▸ Real.sqrt_nonneg _
  have hQ0sq : 2 * Q0 ^ 2 = 3 * C' * Phi 1 := by
    rw [hQ0, Real.sq_sqrt (by positivity)]; ring
  refine ⟨Real.exp (-(Q0 * 2 * h0)) * chainConst_O14 3 Q0 h0 ^ (2 * (N + 1)) * κ / 8 * h0 ^ 3,
    by have := chainConst_pos_O14 3 Q0 h0; positivity, ?_⟩
  filter_upwards [hbuf s y z ρ htime hneck hRy hratio hesc, hC,
    hRy.eventually (eventually_ge_atTop 1)] with n hn hCn hRy1
  intro ℓ hℓ hℓle
  have hℓ1 : ℓ ≤ 1 := hℓle.trans (min_le_left _ _)
  obtain ⟨w, hwB, -, hRw, -, W, -, -, hvolW, -⟩ := hn
  intro p hp
  have hRypos : 0 < metricScalarAt (s n).metric (y n) := lt_of_lt_of_le one_pos hRy1
  have hlam : 0 < Real.sqrt (metricScalarAt (s n).metric (y n)) := Real.sqrt_pos.mpr hRypos
  refine A1_slice_O45 (s n).metric (y n) w p (Q0 := Q0) (h0 := h0)
    (lam := Real.sqrt (metricScalarAt (s n).metric (y n))) (κ := κ) hQ0n hh0pos hh01 hlam
    hκ.le N (isCompact_univ.of_isClosed_subset (isClosed_riemannianClosedBallOf_O14 _ _ _)
      (subset_univ _)) ?_ ?_ ?_ ?_ hℓ hℓ1
  · intro x hx v
    have hx' : x ∈ riemannianBallOf (s n).metric (y n)
        (((N : ℝ) + 4) * h0 / Real.sqrt (metricScalarAt (s n).metric (y n))) := by
      rw [mul_div_assoc]; exact hx
    have hRx := hCn x hx'
    have hric := ricci_lower_of_curvatureOperatorLowerBound_O45 (s n).metric x
      (hPhi.pos _).le (hpin (s n) x) v
    rw [finrank_euclideanSpace_fin] at hric
    have hinner : 0 ≤ (s n).metric.inner x v v := by
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · exact ((s n).metric.pos x v hv).le
    have hCR : C * metricScalarAt (s n).metric (y n) ≤ C' * metricScalarAt (s n).metric (y n) :=
      mul_le_mul_of_nonneg_right hCC' hRypos.le
    have hmono : Phi (metricScalarAt (s n).metric x) ≤
        Phi (C' * metricScalarAt (s n).metric (y n)) := hPhi.mono (hRx.trans hCR)
    have h1CR : 1 ≤ C' * metricScalarAt (s n).metric (y n) := one_le_mul_of_one_le_of_one_le hC'1 hRy1
    have hanti : Phi (C' * metricScalarAt (s n).metric (y n)) /
        (C' * metricScalarAt (s n).metric (y n)) ≤ Phi 1 / 1 :=
      hPhi.quotientAntitoneOn (mem_Ioi.mpr one_pos) (mem_Ioi.mpr (by linarith)) h1CR
    rw [div_one, div_le_iff₀ (by linarith)] at hanti
    have hsq : (Q0 * Real.sqrt (metricScalarAt (s n).metric (y n))) ^ 2 =
        Q0 ^ 2 * metricScalarAt (s n).metric (y n) := by
      rw [mul_pow, Real.sq_sqrt hRypos.le]
    have hQR : 2 * Q0 ^ 2 * metricScalarAt (s n).metric (y n) =
        3 * C' * Phi 1 * metricScalarAt (s n).metric (y n) := by rw [hQ0sq]
    have h3 : 3 * Phi (metricScalarAt (s n).metric x) ≤
        2 * (Q0 * Real.sqrt (metricScalarAt (s n).metric (y n))) ^ 2 := by
      rw [hsq]; linarith only [hmono, hanti, hQR]
    have h4 := mul_le_mul_of_nonneg_right h3 hinner
    push_cast at hric
    linarith only [hric, h4]
  · have hwB' : riemannianEDistOf (s n).metric (y n) w < ENNReal.ofReal
        ((ρ - 19 / 50) / Real.sqrt (metricScalarAt (s n).metric (y n))) := hwB
    refine lt_of_lt_of_le hwB' (ENNReal.ofReal_le_ofReal ?_)
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith only [hm19, hN1, hh0pos]) hlam.le
  · have hp' : riemannianEDistOf (s n).metric (y n) p < ENNReal.ofReal
        (r / Real.sqrt (metricScalarAt (s n).metric (y n))) := hp
    refine lt_of_lt_of_le hp' (ENNReal.ofReal_le_ofReal ?_)
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith only [hmr, hN1, hh0pos]) hlam.le
  · refine unscaled_centre_volume_O31 (s n).metric w W.Q_pos hvolW
      (h0 / Real.sqrt (metricScalarAt (s n).metric (y n))) (div_pos hh0pos hlam) ?_
    rw [hRw, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have e : h0 / Real.sqrt (metricScalarAt (s n).metric (y n)) *
        (Real.sqrt 2 * Real.sqrt (metricScalarAt (s n).metric (y n))) = Real.sqrt 2 * h0 := by
      field_simp
    rw [e]
    linarith only [mul_le_mul_of_nonneg_right hs2b hh0pos.le, hh0β]

/-- **hvc** (`[FROZEN] CH12-O67 hvc` conclusion; premises ⊂ the 12 U-form premises): eventually
along `y n`, the normalized centre balls of radius `b ≤ a₀` have volume `≥ κ b³`. -/
theorem hvc_O72 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    ∀ (s : ℕ → RegularSlice F.observation) (y z : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      Tendsto (fun n => metricScalarAt (s n).metric (z n) /
        metricScalarAt (s n).metric (y n)) atTop atTop →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      (∀ r : ℝ, ρ < r → ∀ᶠ n in atTop, z n ∈ riemannianBallOf (s n).metric (y n)
        (r / Real.sqrt (metricScalarAt (s n).metric (y n)))) →
      1 / 4 ≤ ρ →
      ∃ κ a₀ : ℝ, 0 < κ ∧ 0 < a₀ ∧ ∀ᶠ n in atTop,
        ∀ hy : 0 < metricScalarAt (s n).metric (y n), ∀ b : ℝ, 0 < b → b ≤ a₀ →
          ENNReal.ofReal (κ * b ^ 3) ≤
            riemannianVolumeMeasure ThreeModel (s n).stage.Carrier
              (scaleMetric (metricScalarAt (s n).metric (y n)) hy (s n).metric)
              (riemannianBallOf (scaleMetric (metricScalarAt (s n).metric (y n)) hy (s n).metric)
                (y n) b) := by
  intro s y z ρ h1 h2 h3 h8 h9 h10 h11
  have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs2a : 1 < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hs2 : (Real.sqrt 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs2a
  have hgap : 0 < ρ - (Real.sqrt 2)⁻¹ / 4 := by linarith
  obtain ⟨v, hv, hev⟩ := hA1_unif_O72 Hp s y z ρ h1 h2 h3 h8 h9 h10 h11
    ((ρ - (Real.sqrt 2)⁻¹ / 4) / 2) (by linarith) (by linarith)
  refine ⟨v, min 1 (ρ - (Real.sqrt 2)⁻¹ / 4 - (ρ - (Real.sqrt 2)⁻¹ / 4) / 2), hv,
    lt_min one_pos (by linarith), ?_⟩
  filter_upwards [hev] with n hn hy b hb hba
  have hlam : 0 < Real.sqrt (metricScalarAt (s n).metric (y n)) := Real.sqrt_pos.mpr hy
  have h := hn b hb hba (y n) (mem_riemannianBallOf_self_O13 _ _ (div_pos (by linarith) hlam))
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hscaled :=
    (DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff
      (s n).metric (metricScalarAt (s n).metric (y n)) hy (y n)
      (b / Real.sqrt (metricScalarAt (s n).metric (y n))) (ENNReal.ofReal v)).mpr (by
        rw [hdim, ← ENNReal.ofReal_pow (div_pos hb hlam).le, ← ENNReal.ofReal_mul hv.le]
        exact h)
  have hscale : Real.sqrt (metricScalarAt (s n).metric (y n)) *
      (b / Real.sqrt (metricScalarAt (s n).metric (y n))) = b := mul_div_cancel₀ _ hlam.ne'
  rw [hscale, hdim] at hscaled
  simpa only [ENNReal.ofReal_mul hv.le, ENNReal.ofReal_pow hb.le] using hscaled

/-- **HVW on slices** (`[FROZEN] CH12-O67 G1/G2` HVW with `Kv := Hp.C2`, `a₀ := (√C2)⁻¹`). -/
theorem hvw_slice_O72 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (s : RegularSlice F.observation) (y : s.stage.Carrier)
      (hQ : 1 ≤ (sliceSlabR_O3 F s).flow.scalar s.time y),
      (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ (sliceSlabR_O3 F s).flow.scalar s.time y →
      ∀ (w : ((sliceSlabR_O3 F s).restrictIncoming le_rfl
          (sliceSlabR_O3 F s).lt le_rfl).terminalRegularOpen),
      riemannianEDistOf (scaleMetric ((sliceSlabR_O3 F s).flow.scalar s.time y)
          (zero_lt_one.trans_le hQ)
          ((sliceSlabR_O3 F s).endpointTerminalLimitMetric
            ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount))).metric)
        ⟨y, mem_slice_terminalRegularOpen_O51 F s y⟩ w < ⊤ →
      ∀ hw : Hp.C2 * (sliceSlabR_O3 F s).flow.scalar s.time y < metricScalarAt
          ((sliceSlabR_O3 F s).endpointTerminalLimitMetric
            ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount))).metric w,
      ∀ b : ℝ, 0 < b → b ≤ (Real.sqrt Hp.C2)⁻¹ →
        ENNReal.ofReal (κ * b ^ 3) ≤
          riemannianVolumeMeasure ThreeModel
            ((sliceSlabR_O3 F s).restrictIncoming le_rfl
              (sliceSlabR_O3 F s).lt le_rfl).terminalRegularOpen
            (scaleMetric (metricScalarAt ((sliceSlabR_O3 F s).endpointTerminalLimitMetric
                ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount))).metric w)
              ((mul_nonneg (zero_le_one.trans Hp.C2_ge_one) (zero_le_one.trans hQ)).trans_lt hw)
              ((sliceSlabR_O3 F s).endpointTerminalLimitMetric
                ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount))).metric)
            (riemannianBallOf
              (scaleMetric (metricScalarAt ((sliceSlabR_O3 F s).endpointTerminalLimitMetric
                ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount))).metric w)
              ((mul_nonneg (zero_le_one.trans Hp.C2_ge_one) (zero_le_one.trans hQ)).trans_lt hw)
              ((sliceSlabR_O3 F s).endpointTerminalLimitMetric
                ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount))).metric)
              w b) := by
  have hC2 : 1 ≤ Hp.C2 := Hp.C2_ge_one
  obtain ⟨κ, hκ, hcv⟩ := centre_volume_of_witness_O14.{u} Hp.epsilon Hp.C1 Hp.C2
    (zero_lt_one.trans_le hC2)
  refine ⟨κ, hκ, fun s y hQ hq w hd hw b hb hbC => ?_⟩
  let U : TopologicalSpace.Opens s.stage.Carrier :=
    ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl).terminalRegularOpen
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have : IsManifold ThreeModel 1 U := IsManifold.of_le (I := ThreeModel) (n := ∞) (by decide)
  have hUc : IsClosed (SetLike.coe U) := by
    have hU : (SetLike.coe U) = univ :=
      eq_univ_of_forall (mem_slice_terminalRegularOpen_O51 F s)
    rw [hU]
    exact isClosed_univ
  have hRy : (sliceSlabR_O3 F s).flow.scalar s.time y = metricScalarAt s.metric y :=
    slice_flow_scalar_O51 F s y
  have hRw : metricScalarAt ((sliceSlabR_O3 F s).endpointTerminalLimitMetric
      ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount))).metric w =
      metricScalarAt s.metric w.val := by
    rw [slice_endpoint_metric_O51]
    exact metricScalarAt_restrictOpen (I := ThreeModel) s.metric U w
  have hw' : Hp.C2 * metricScalarAt s.metric y < metricScalarAt s.metric w.val := by
    rw [← hRy, ← hRw]; exact hw
  have hy1 : 1 ≤ metricScalarAt s.metric y := hRy ▸ hQ
  -- `y` lies in the connected component of `w`
  have hfin : riemannianEDistOf s.metric y w.val < ⊤ := by
    have h := hd
    rw [edistOf_scale, slice_endpoint_metric_O51] at h
    have h' := ENNReal.lt_top_of_mul_ne_top_right h.ne
      (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le hQ))).ne'
    exact (riemannianEDistOf_restrictOpen_of_isClosed s.metric U hUc _ w).symm.trans_lt h'
  have hcc : w.val ∈ connectedComponent y := by
    have hr : 0 < (riemannianEDistOf s.metric y w.val).toReal + 1 := by positivity
    have hmem : w.val ∈ riemannianBallOf s.metric y
        ((riemannianEDistOf s.metric y w.val).toReal + 1) := by
      change riemannianEDistOf s.metric y w.val < ENNReal.ofReal _
      exact (ENNReal.lt_ofReal_iff_toReal_lt hfin.ne).mpr (by linarith)
    exact (isPathConnected_riemannianBallOf s.metric y hr).isConnected.isPreconnected.subset_connectedComponent
      (mem_riemannianBallOf_self_O13 s.metric y hr) hmem
  -- the canonical witness at `w`
  have hRwn : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric w.val := by
    have h1 : metricScalarAt s.metric y ≤ Hp.C2 * metricScalarAt s.metric y :=
      le_mul_of_one_le_left (by linarith) hC2
    rw [hRy] at hq
    linarith
  obtain ⟨W, hWc⟩ := slice_witness_O72 Hp s w.val hRwn
  have hreq : W.alternative.requiresVolume := by
    cases hA : W.alternative with
    | neck _ => trivial
    | cap _ _ => trivial
    | positive _ _ _ => trivial
    | round whole _ =>
      exfalso
      have hyc : y ∈ connectedComponent (w.val : s.stage.Carrier) :=
        (connectedComponent_eq hcc).subset mem_connectedComponent
      have hyD : y ∈ W.domain.carrier := by
        rw [whole]
        exact hyc
      have hb1 := (W.scalar_bounds y hyD).1
      have hC2pos : 0 < Hp.C2 := zero_lt_one.trans_le hC2
      rw [inv_mul_le_iff₀ hC2pos] at hb1
      linarith
  have hvol := hcv W hWc hreq b hb hbC
  have key : ∀ m : SmoothRiemannianMetric ThreeModel U, m = s.metric.restrictOpen U →
      ∀ (c : ℝ) (hc : 0 < c), c = metricScalarAt m w →
      ENNReal.ofReal (κ * b ^ 3) ≤ riemannianVolumeMeasure ThreeModel U (scaleMetric c hc m)
        (riemannianBallOf (scaleMetric c hc m) w b) := by
    intro m hm c hc hcw
    subst hm
    rw [metricScalarAt_restrictOpen (I := ThreeModel) s.metric U w] at hcw
    subst hcw
    rw [← restrictOpen_scaleMetric]
    exact hvol.trans_eq (riemannianVolumeMeasure_ball_restrictOpen_of_isClosed _ U hUc w b).symm
  exact key _ (slice_endpoint_metric_O51 F s) _ _ rfl

end Slice

end GC.LongTime.Ch12
