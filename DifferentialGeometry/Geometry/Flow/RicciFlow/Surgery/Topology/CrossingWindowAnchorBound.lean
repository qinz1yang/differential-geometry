import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingMaximalWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingBaseSliceBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingTracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAtBefore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionLocalLimitDepthSchedule
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionNeckAlternativesCompact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitDerivativeCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionMaximalDepth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceAnchor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorTraceScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalPointedFlowLimitNoncollapsing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.OpenClosedGluing

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.scaleMetric_restrictOpen
  ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

universe u

private theorem closedBall_one_subset_of_ball_eq_window {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) (b : M) (W : TopologicalSpace.Opens M) (k : ℕ)
    (hW : (W : Set M) = riemannianBallOf g b ((k + 3 : ℕ) : ℝ)) (z : M)
    (hz : z ∈ riemannianClosedBallOf g b ((k + 1 : ℕ) : ℝ)) :
    riemannianClosedBallOf g z 1 ⊆ W := by
  intro w hw
  rw [hW]
  have hz' : riemannianEDistOf g b z ≤ ENNReal.ofReal ((k + 1 : ℕ) : ℝ) := hz
  have hw' : riemannianEDistOf g z w ≤ ENNReal.ofReal 1 := hw
  change riemannianEDistOf g b w < ENNReal.ofReal ((k + 3 : ℕ) : ℝ)
  calc riemannianEDistOf g b w ≤ riemannianEDistOf g b z + riemannianEDistOf g z w :=
        riemannianEDistOf_triangle _ _ _ _
    _ ≤ ENNReal.ofReal ((k + 1 : ℕ) : ℝ) + ENNReal.ofReal 1 := add_le_add hz' hw'
    _ = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) + 1) :=
        (ENNReal.ofReal_add (by positivity) (by norm_num)).symm
    _ < ENNReal.ofReal ((k + 3 : ℕ) : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by push_cast; linarith)

private theorem lt_ofReal_div_of_ofReal_mul_lt {a b : ℝ} (ha : 0 < a) {d : ENNReal}
    (h : ENNReal.ofReal a * d < ENNReal.ofReal b) : d < ENNReal.ofReal (b / a) := by
  have hd : d ≠ ⊤ := by
    rintro rfl
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr ha).ne'] at h
    exact (not_top_lt h)
  rw [← ENNReal.ofReal_toReal hd, ← ENNReal.ofReal_mul ha.le] at h
  obtain ⟨h1, hb⟩ := (ENNReal.ofReal_lt_ofReal_iff').mp h
  rw [← ENNReal.ofReal_toReal hd]
  refine (ENNReal.ofReal_lt_ofReal_iff' ).mpr ⟨?_, div_pos hb ha⟩
  rw [lt_div_iff₀ ha]
  linarith

private theorem depth_schedule_facts {T : ℝ} (hT : 0 < T) :
    (∀ k : ℕ, 0 < T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ∧
    (∀ k : ℕ, T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) < T) ∧
    (∀ k : ℕ, 0 < ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) ∧
    (∀ k : ℕ, ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) < T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ∧
    Monotone (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) ∧
    (∀ s < T, ∃ k : ℕ, s < ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (T * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) := by
  have hβ (n : ℕ) : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) = 1 - 1 / ((n + 2 : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    field_simp
    push_cast
    ring
  have hβ1 (n : ℕ) : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    push_cast
    linarith
  have hβ0 (n : ℕ) : 0 < ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by positivity
  have hτ (n : ℕ) : 0 < T * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by positivity
  have hτT (n : ℕ) : T * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) < T := by
    rw [mul_div_assoc]
    nlinarith [hβ1 n]
  refine ⟨hτ, hτT, fun n => mul_pos (hβ0 n) (hτ n), fun n => ?_, fun n m hnm => ?_,
    fun s hs => ?_⟩
  · nlinarith [hβ1 n, hτ n]
  · have h1 : 1 / ((m + 2 : ℕ) : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 2)
    have h3 : 0 ≤ 1 - 1 / ((n + 2 : ℕ) : ℝ) := by
      rw [← hβ]
      positivity
    have h4 : 1 - 1 / ((n + 2 : ℕ) : ℝ) ≤ 1 - 1 / ((m + 2 : ℕ) : ℝ) := by linarith
    change ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) * (T * ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) ≤
      ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) * (T * ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ))
    rw [mul_div_assoc, mul_div_assoc, hβ, hβ]
    exact mul_le_mul h4 (mul_le_mul_of_nonneg_left h4 hT.le) (mul_nonneg hT.le h3) (h3.trans h4)
  · by_cases hs0 : s < 0
    · exact ⟨0, hs0.trans (mul_pos (hβ0 0) (hτ 0))⟩
    push Not at hs0
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * T / (T - s))
    refine ⟨n, ?_⟩
    have hTs : 0 < T - s := by linarith
    have hn2 : 2 * T / (T - s) < ((n + 2 : ℕ) : ℝ) := by push_cast; linarith
    have hx : 2 * T * (1 / ((n + 2 : ℕ) : ℝ)) < T - s := by
      rw [div_lt_iff₀ hTs] at hn2
      rw [mul_one_div, div_lt_iff₀ (by positivity)]
      linarith
    have hx0 : 0 ≤ 1 / ((n + 2 : ℕ) : ℝ) := by positivity
    rw [mul_div_assoc, hβ]
    nlinarith [mul_nonneg hT.le (sq_nonneg (1 / ((n + 2 : ℕ) : ℝ)))]

open Perelman.CanonicalNeighborhood.FiniteHorn

private local instance opensSigmaCompactAnchor {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace ThreeSpace Y] [SigmaCompactSpace Y] (U : TopologicalSpace.Opens Y) :
    SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

namespace ObservedHistory

variable {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
  {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n} {τ : ℕ → ℝ}
  {W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens ((Hs n).stageAt (ts n)).Carrier}
  {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)}

theorem exists_eventually_neckAlternatives_or_isCompact_of_survivor_blocks :
    ∃ D : ℝ, 0 < D ∧ ∀ {Hs : ℕ → ObservedHistory.{u}} {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon}
      {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n} {τ c : ℕ → ℝ}
      {W : ∀ (_ : ℕ) (n : ℕ), TopologicalSpace.Opens ((Hs n).stageAt (ts n)).Carrier}
      {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)},
      (∀ k, 0 < τ k) → (∀ k, c k ≤ τ k) →
      (∀ k : ℕ, ∀ᶠ n in atTop, (W k n : Set ((Hs n).stageAt (ts n)).Carrier) =
        riemannianBallOf (scaleMetric (R n) (hR n)
          ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))) (ys n) ((k + 3 : ℕ) : ℝ)) →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-τ k) 0,
        (ts n : ℝ) + s / R n ∈ (Hs n).stageDomain ((Hs n).activeStage (ts n)) →
        h k n s = scaleMetric (R n) (hR n)
          (((Hs n).stageMetric ((Hs n).activeStage (ts n)) ((ts n : ℝ) + s / R n)).restrictOpen
            (W k n))) →
      (∀ k : ℕ, ∀ᶠ n in atTop,
        ∃ (a : Icc (0 : ℝ) (Hs n).horizon) (_ : a ≤ ts n), (a : ℝ) = ts n - τ k / R n ∧
          ∃ f : (j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n))) →
              W k n → ((Hs n).stage j.val).Carrier,
            ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
              (∀ j, Function.Injective (f j)) ∧
              ∀ s ∈ Icc (-τ k) 0,
                ∀ j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n)),
                  (ts n : ℝ) + s / R n ∈ (Hs n).stageDomain j.val →
                    h k n s = scaleMetric (R n) (hR n)
                      (localPullMetric ((Hs n).stageMetric j.val ((ts n : ℝ) + s / R n)) (f j)
                        (hf j))) →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, ∀ (x : W k n)
        (u : TangentSpace ThreeModel x),
        (h k n 0).inner x u u ≤ Real.exp 2 * (h k n s).inner x u u) →
      ∀ {t₀ qs : ℕ → ℝ} {E : ℕ → Set ℝ} {eps C1 C2 C qW : ℝ}, 0 < eps → 1 ≤ C →
      max (2 * |C1|) C2 ≤ C → (∀ n, qs n ≤ R n * qW) →
      (Real.exp 1 * (C + (D + 2 * eps⁻¹) * Real.sqrt C)) ^ 2 ≤ qW →
      (∀ n (v : Icc (0 : ℝ) (Hs n).horizon), (v : ℝ) < t₀ n →
        (Hs n).time ((Hs n).activeStage v) < v →
        ∀ p : ((Hs n).stageAt v).Carrier,
          qs n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) p →
          ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) eps C1 C2 p,
            Wt.capTubeHasNeckChart eps) →
      (∀ n s, s ≤ 0 → s ∉ E n → (ts n : ℝ) + s / R n < t₀ n ∧
        ∀ i, (ts n : ℝ) + s / R n ≠ (Hs n).time i) →
      ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, s ∉ E n → ∀ z : W k n,
        (z : ((Hs n).stageAt (ts n)).Carrier) ∈ riemannianClosedBallOf (scaleMetric (R n) (hR n)
          ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))) (ys n) ((k + 1 : ℕ) : ℝ) →
        qW < metricScalarAt (h k n s) z →
        Nonempty (SpatialNeck (h k n s) eps z) ∨
          (∃ w : W k n, Nonempty (SpatialNeck (h k n s) eps w) ∧
            metricScalarAt (h k n s) z ≤ C * metricScalarAt (h k n s) w ∧
            metricScalarAt (h k n s) w ≤ C * metricScalarAt (h k n s) z ∧
            riemannianEDistOf (h k n s) z w <
              ENNReal.ofReal (C / Real.sqrt (metricScalarAt (h k n s) z))) ∨
          IsCompact (connectedComponent z) := by
  obtain ⟨D, hD, hB6⟩ := exists_neckAlternatives_or_isCompact_of_survivor_maps.{u}
  refine ⟨D, hD, ?_⟩
  intro Hs ts ys R hR τ c W h hτ hcτ hWset hcur hsurv hlow t₀ qs E eps C1 C2 C qW heps hC1 hC0
    hqs hqWsq hwit hE k
  have hC00 : 0 ≤ max (2 * |C1|) C2 := le_max_of_le_left (by positivity)
  have hDe : 0 ≤ D + 2 * eps⁻¹ := by have := inv_pos.mpr heps; linarith
  have hxnn : 0 ≤ Real.exp 1 * (C + (D + 2 * eps⁻¹) * Real.sqrt C) :=
    mul_nonneg (Real.exp_pos 1).le
      (add_nonneg (by linarith) (mul_nonneg hDe (Real.sqrt_nonneg _)))
  have hqW0 : 0 ≤ qW := (sq_nonneg _).trans hqWsq
  have he2 : Real.exp 1 ^ 2 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  filter_upwards [hWset k, hcur k, hsurv k, hlow k] with n hWn hcn hsn hlown s hs hsE z hz hqz
  obtain ⟨a, -, ha, fs, hfs, hinj, hp⟩ := hsn
  obtain ⟨hst₀, hne⟩ := hE n s hs.2 hsE
  have hsτ : s ∈ Icc (-τ k) 0 := ⟨by linarith [hs.1, hcτ k], hs.2⟩
  have hzpos : 0 < metricScalarAt (h k n s) z := hqW0.trans_lt hqz
  have hcpt : IsCompact (riemannianClosedBallOf (h k n 0) z 1) := by
    have hdom : ((ts n : ℝ) + 0 / R n) ∈ (Hs n).stageDomain ((Hs n).activeStage (ts n)) := by
      simpa using (Hs n).activeStage_mem (ts n)
    rw [hcn 0 ⟨neg_nonpos.mpr (hτ k).le, le_rfl⟩ hdom, zero_div, add_zero,
      ObservedHistory.scaleMetric_restrictOpen]
    exact ObservedHistory.isCompact_riemannianClosedBallOf_restrictOpen _ _ _ _
      (closedBall_one_subset_of_ball_eq_window _ _ _ k hWn _ hz)
  have hsmall : Real.exp 1 * (max (2 * |C1|) C2 + (D + 2 * eps⁻¹) *
      Real.sqrt (max (2 * |C1|) C2)) < Real.sqrt (metricScalarAt (h k n s) z) := by
    refine lt_of_le_of_lt ?_ ((Real.lt_sqrt hxnn).mpr (hqWsq.trans_lt hqz))
    gcongr
  have key := hB6 (Hs n) (ts n) (hR n) (θ := τ k) (t₀ := t₀ n) (eps := eps) (C1 := C1)
    (C2 := C2) (W := W k n) (h := h k n) (hqs n) (Real.exp_pos 1) a ha fs hfs hinj hp
    (hwit n) hsτ hst₀
    (fun hv => lt_of_le_of_ne (ObservedHistory.activeStage_time_le _ _)
      fun heq => hne _ heq.symm) z hcpt
    (fun y' _ u => by rw [he2]; exact hlown s hs y' u) hqz hsmall
  rcases key with h1 | ⟨w, hw, h2, h3, h4⟩ | h5
  · exact Or.inl h1
  · have hw0 : 0 < metricScalarAt (h k n s) w := by
      by_contra hneg
      have := mul_nonpos_of_nonneg_of_nonpos hC00 (not_lt.mp hneg)
      linarith
    refine Or.inr (Or.inl ⟨w, hw, h2.trans (mul_le_mul_of_nonneg_right hC0 hw0.le),
      h3.trans (mul_le_mul_of_nonneg_right hC0 hzpos.le), h4.trans_le ?_⟩)
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hC0 (Real.sqrt_nonneg _))
  · exact Or.inr (Or.inr h5)

theorem eventually_abs_derivWithin_scalar_le_of_survivor_blocks
    (hsurv : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∃ (a : Icc (0 : ℝ) (Hs n).horizon) (_ : a ≤ ts n), (a : ℝ) = ts n - τ k / R n ∧
        ∃ f : (j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n))) →
            W k n → ((Hs n).stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            ∀ s ∈ Icc (-τ k) 0,
              ∀ j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n)),
                (ts n : ℝ) + s / R n ∈ (Hs n).stageDomain j.val →
                  h k n s = scaleMetric (R n) (hR n)
                    (localPullMetric ((Hs n).stageMetric j.val ((ts n : ℝ) + s / R n)) (f j)
                      (hf j)))
    {E : ℕ → Set ℝ} {Ct qD : ℝ} (hCt : 0 ≤ Ct) {qst : ℕ → ℝ} (hqD : ∀ n, qst n ≤ R n * qD)
    (hstage : ∀ n (v : Icc (0 : ℝ) (Hs n).horizon), (v : ℝ) < ts n →
      (Hs n).time ((Hs n).activeStage v) < v →
      ∀ p : ((Hs n).stageAt v).Carrier,
        qst n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) p →
        |derivWithin (fun v' => metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v') p)
          (Iic (v : ℝ)) v| ≤
          Ct * metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) p ^ 2)
    (hE : ∀ n s, s ≤ 0 → s ∉ E n → ∀ i, (ts n : ℝ) + s / R n ≠ (Hs n).time i) :
    ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Ioo (-τ k) 0, s ∉ E n →
      ∀ z : W k n, qD < metricScalarAt (h k n s) z →
        |derivWithin (fun v => metricScalarAt (h k n v) z) (Iic s) s| ≤
          Ct * metricScalarAt (h k n s) z ^ 2 := by
  intro k
  filter_upwards [hsurv k] with n hn s hs hsE z hz
  obtain ⟨a, -, ha, fs, hfs, hp⟩ := hn
  have hne := hE n s hs.2.le hsE
  have hst : (ts n : ℝ) + s / R n < ts n := by
    have := div_neg_of_neg_of_pos hs.2 (hR n)
    linarith
  exact abs_derivWithin_scalar_le_of_survivor_maps_of_lt (Hs n) (ts n) (hR n) hCt (hqD n) a ha fs
    hfs hp (hstage n) ⟨hs.1, hs.2.le⟩ hst
    (fun hv => lt_of_le_of_ne (ObservedHistory.activeStage_time_le _ _)
      fun heq => hne _ heq.symm) z hz

theorem survivor_blocks_scalar_le_at_distance
    (hsurv : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∃ (a : Icc (0 : ℝ) (Hs n).horizon) (_ : a ≤ ts n), (a : ℝ) = ts n - τ k / R n ∧
        ∃ f : (j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n))) →
            W k n → ((Hs n).stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            ∀ s ∈ Icc (-τ k) 0,
              ∀ j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n)),
                (ts n : ℝ) + s / R n ∈ (Hs n).stageDomain j.val →
                  h k n s = scaleMetric (R n) (hR n)
                    (localPullMetric ((Hs n).stageMetric j.val ((ts n : ℝ) + s / R n)) (f j)
                      (hf j)))
    {c : ℕ → ℝ} (hcτ : ∀ k, c k ≤ τ k)
    (hbound : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ᶠ n in atTop,
      ∀ v : Icc (0 : ℝ) (Hs n).horizon, (v : ℝ) = ts n + σ' / R n →
      ∀ z x : ((Hs n).stageAt v).Carrier,
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) z ≤ A * R n →
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v) z x <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) x ≤ C * R n) :
    ∀ A Dd : ℝ, ∃ C : ℝ, ∀ k : ℕ, ∀ s ∈ Icc (-c k) 0, s < 0 → ∀ᶠ n in atTop,
      ∀ z x : W k n, metricScalarAt (h k n s) z ≤ A →
        riemannianEDistOf (h k n s) z x < ENNReal.ofReal Dd →
        metricScalarAt (h k n s) x ≤ C := by
  intro A Dd
  obtain ⟨C₁, hC₁⟩ := hbound (max A 1) (max Dd 1) (by positivity) (by positivity)
  refine ⟨C₁, fun k s hs hs0 => ?_⟩
  filter_upwards [hsurv k, hC₁ s hs0] with n hn hCm z x hz hzx
  obtain ⟨a, -, ha, fs, hfs, hp⟩ := hn
  have hR0 := hR n
  have hsτ : s ∈ Icc (-τ k) 0 := ⟨by linarith [hs.1, hcτ k], hs.2⟩
  have hsR : s / R n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hR0.le
  have hθR : -τ k / R n ≤ s / R n := div_le_div_of_nonneg_right hsτ.1 hR0.le
  have hlo : (a : ℝ) ≤ (ts n : ℝ) + s / R n := by
    rw [ha, sub_eq_add_neg, ← neg_div]
    linarith
  let v : Icc (0 : ℝ) (Hs n).horizon :=
    ⟨(ts n : ℝ) + s / R n, a.2.1.trans hlo,
      (by linarith : (ts n : ℝ) + s / R n ≤ ts n).trans (ts n).2.2⟩
  have hav : a ≤ v := hlo
  have hvt : v ≤ ts n := show (ts n : ℝ) + s / R n ≤ ts n by linarith
  let j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n)) :=
    ⟨(Hs n).activeStage v, (Hs n).activeStage_mono hav, (Hs n).activeStage_mono hvt⟩
  have hs1 := hp s hsτ j ((Hs n).activeStage_mem v)
  have hscz : ∀ w, metricScalarAt (h k n s) w =
      (R n)⁻¹ * metricScalarAt ((Hs n).stageMetric j.val v) (fs j w) := by
    intro w
    rw [hs1, metricScalarAt_scaleMetric, metricScalarAt_localPull]
  have hz' : metricScalarAt ((Hs n).stageMetric j.val v) (fs j z) ≤ max A 1 * R n := by
    rw [hscz z, inv_mul_le_iff₀ hR0] at hz
    nlinarith [le_max_left A 1]
  have hd : riemannianEDistOf ((Hs n).stageMetric j.val v) (fs j z) (fs j x) <
      ENNReal.ofReal (max Dd 1 / Real.sqrt (R n)) := by
    rw [hs1, edistOf_scale] at hzx
    have h1 := lt_ofReal_div_of_ofReal_mul_lt (Real.sqrt_pos.mpr hR0) hzx
    have h2 := edistOf_le_of_quad_of_localDiffeomorph
      (localPullMetric ((Hs n).stageMetric j.val v) (fs j) (hfs j))
      ((Hs n).stageMetric j.val v) (fs j) (hfs j) one_pos
      (fun x' u => by rw [localPullMetric_inner, one_mul]) z x
    rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at h2
    exact h2.trans_lt (h1.trans_le (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))))
  have hx' := hCm v rfl (fs j z) (fs j x) hz' hd
  rw [hscz x, inv_mul_le_iff₀ hR0]
  linarith

attribute [local instance] CheegerGromovCompactness.PointedRiemannianManifold.topology
  CheegerGromovCompactness.PointedRiemannianManifold.charted
  CheegerGromovCompactness.PointedRiemannianManifold.smooth
  CheegerGromovCompactness.PointedRiemannianManifold.t2
  CheegerGromovCompactness.PointedRiemannianManifold.sigmaCompact in
theorem eventually_scalar_backwardPointTrace_le_of_window_limit
    (hsurv : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∃ (a : Icc (0 : ℝ) (Hs n).horizon) (hat : a ≤ ts n), (a : ℝ) = ts n - τ k / R n ∧
        ∃ f : (j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n))) →
            W k n → ((Hs n).stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin (Hs n).eventCount) (hi : (Hs n).activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ (Hs n).activeStage (ts n)), ∀ x : W k n,
              ((Hs n).event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : W k n,
              f ⟨(Hs n).activeStage (ts n), (Hs n).activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∀ s ∈ Icc (-τ k) 0,
              ∀ j : (Hs n).StageInterval ((Hs n).activeStage a) ((Hs n).activeStage (ts n)),
                (ts n : ℝ) + s / R n ∈ (Hs n).stageDomain j.val →
                  h k n s = scaleMetric (R n) (hR n)
                    (localPullMetric ((Hs n).stageMetric j.val ((ts n : ℝ) + s / R n)) (f j)
                      (hf j)))
    {f : ℕ → ℕ} (hfm : StrictMono f)
    {P : CheegerGromovCompactness.PointedRiemannianManifold.{u, 0, 0} ThreeModel}
    (F : CheegerGromovCompactness.PointedRiemannianConvergenceMaps
      ({ obj := fun n =>
          { M := ((Hs n).stageAt (ts n)).Carrier
            basepoint := ys n
            metric := scaleMetric (R n) (hR n)
              ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) } } :
        CheegerGromovCompactness.PointedRiemannianSeq.{u, 0, 0} ThreeModel) P f)
    (Cd : CheegerGromovCompactness.MetricConvergenceData F)
    (hcan : ∀ n, Cd.domain n =
      CheegerGromovCompactness.CanonicalMetricCompactness.canonicalSourceData F n)
    (hPc : CheegerGromovCompactness.MetricComplete P) {V : ℕ → TopologicalSpace.Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)}
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : ((Hs (f j)).stageAt (ts (f j))).Carrier) = F.map j z)
    {T : ℝ} {c : ℕ → ℝ} (hcτ : ∀ k, c k ≤ τ k) (hcmono : Monotone c)
    (hcT : ∀ s ∈ Ioc (-T) 0, ∃ k, -c k < s) {Gl : ℝ → SmoothRiemannianMetric ThreeModel P.M}
    {ψ₁ : ℕ → ℕ} (hψ₁ : StrictMono ψ₁)
    (hconvG : ∀ k (K' : Set (V k)), IsCompact K' → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ₁ i, ∀ s ∈ Icc (-c k) 0,
        metricDerivNormSupOn K' p
          (localPullMetric (h k (f (ψ₁ i)) s) (φ k (ψ₁ i) hi) (hφ k (ψ₁ i) hi))
          ((Gl s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    {C₀ : ℝ} (hC₀ : ∀ t ∈ Ioc (-T) 0, ∀ x : P.M, metricScalarAt (Gl t) x ≤ C₀)
    {T' : ℝ} (hT' : 0 < T') (hT'T : T' < T) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Hs (f (ψ₁ i))).stageMetric
          ((Hs (f (ψ₁ i))).activeStage (ts (f (ψ₁ i)))) (ts (f (ψ₁ i)))) (ys (f (ψ₁ i)))
          (A / Real.sqrt (R (f (ψ₁ i)))),
      ∀ (w : Icc (0 : ℝ) (Hs (f (ψ₁ i))).horizon),
        (w : ℝ) = ts (f (ψ₁ i)) - T' / R (f (ψ₁ i)) →
      ∀ (hwt : w ≤ ts (f (ψ₁ i)))
        (Bt : BackwardPointTrace (Hs (f (ψ₁ i))) ((Hs (f (ψ₁ i))).activeStage w)
          ((Hs (f (ψ₁ i))).activeStage (ts (f (ψ₁ i))))
          ((Hs (f (ψ₁ i))).activeStage_mono hwt) x),
        metricScalarAt ((Hs (f (ψ₁ i))).stageMetric ((Hs (f (ψ₁ i))).activeStage w) w)
          (Bt.point ((Hs (f (ψ₁ i))).activeStage w) le_rfl
            ((Hs (f (ψ₁ i))).activeStage_mono hwt)) ≤
          (max C₀ 0 + 1) * R (f (ψ₁ i)) := by
  have hcompl : RiemannianMetricComplete P.metric :=
    ⟨CheegerGromovCompactness.MetricComplete.complete P hPc⟩
  have href : ∀ i, (Cd.domain i).referenceMetric = (Cd.domain i).limitMetric := by
    intro i
    rw [hcan i]
    rfl
  obtain ⟨k₁, hk₁⟩ := hcT (-T') ⟨by linarith, by linarith⟩
  obtain ⟨k₂, hk₂⟩ := exists_nat_gt (4 * A)
  set k := max k₁ k₂ with hkdef
  have hTk : -T' ∈ Icc (-c k) 0 :=
    ⟨(neg_le_neg (hcmono (le_max_left k₁ k₂))).trans hk₁.le, by linarith⟩
  have hk2 : (k₂ : ℝ) ≤ k := by exact_mod_cast le_max_right k₁ k₂
  have hball2A : riemannianClosedBallOf P.metric P.basepoint (2 * A) ⊆ (V k : Set P.M) := by
    intro p hp
    rw [hV k]
    refine lt_of_le_of_lt hp ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
    push_cast
    linarith
  have hKc : IsCompact (riemannianClosedBallOf P.metric P.basepoint (2 * A)) :=
    hcompl.closedEBall_isCompact P.basepoint (2 * A)
  let Kbig : Set (V k) := Subtype.val ⁻¹' riemannianClosedBallOf P.metric P.basepoint (2 * A)
  have hKbig : IsCompact Kbig := by
    rw [Subtype.isCompact_iff]
    have himg : Subtype.val '' Kbig = riemannianClosedBallOf P.metric P.basepoint (2 * A) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, hball2A hz⟩, hz, rfl⟩
    rw [himg]
    exact hKc
  let seq : ℕ → SmoothRiemannianMetric ThreeModel (V k) := fun i =>
    if hi : N k ≤ ψ₁ i then
      localPullMetric (h k (f (ψ₁ i)) (-T')) (φ k (ψ₁ i) hi) (hφ k (ψ₁ i) hi)
    else (Gl (-T')).restrictOpen (V k)
  have hseq_eq : ∀ i (hi : N k ≤ ψ₁ i),
      seq i = localPullMetric (h k (f (ψ₁ i)) (-T')) (φ k (ψ₁ i) hi) (hφ k (ψ₁ i) hi) :=
    fun i hi => dite_eq_left hi
  have hconvk : MetricCInfConvergenceOnCompacts seq
      ((Gl (-T')).restrictOpen (V k)) (P.metric.restrictOpen (V k)) := by
    intro K' hK' p η hη
    obtain ⟨j₀, hj₀⟩ := hconvG k K' hK' p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', hb⟩ := hj₀ i hi
    rw [hseq_eq i hi']
    exact hb (-T') hTk
  have hunif := (hconvk Kbig hKbig 2).tendstoUniformlyOn_metricScalarAt hKbig
  have hballI := F.eventually_ball_subset_image_closed_ball Cd href hPc P.basepoint (A := A)
    (R := 2 * A) (L := 3 / 2) (by norm_num) (by linarith)
  have hfψ : Tendsto (fun i => f (ψ₁ i)) atTop atTop := (hfm.comp hψ₁).tendsto_atTop
  filter_upwards [hψ₁.tendsto_atTop.eventually (eventually_ge_atTop (N k)),
    Metric.tendstoUniformlyOn_iff.mp hunif 1 one_pos, hψ₁.tendsto_atTop.eventually hballI,
    hfψ.eventually (hsurv k)] with i hNi hsc hbi hn
  intro x hx w hw hwt Bt
  have hR0 := hR (f (ψ₁ i))
  have hsR : Real.sqrt (R (f (ψ₁ i))) * (A / Real.sqrt (R (f (ψ₁ i)))) = A := by
    have := Real.sqrt_pos.mpr hR0
    field_simp
  have hxX := riemannianBallOf_scaleMetric _ hR0
    ((Hs (f (ψ₁ i))).stageMetric ((Hs (f (ψ₁ i))).activeStage (ts (f (ψ₁ i)))) (ts (f (ψ₁ i))))
    (ys (f (ψ₁ i))) (A / Real.sqrt (R (f (ψ₁ i))))
  rw [hsR] at hxX
  rw [← hxX] at hx
  have hbase : F.map (ψ₁ i) P.basepoint = ys (f (ψ₁ i)) := F.basepoint_map (ψ₁ i)
  obtain ⟨p, hp, hpx⟩ := hbi.2 (by rw [hbase]; exact hx)
  let pk : V k := ⟨p, hball2A hp⟩
  have hxW : ((φ k (ψ₁ i) hNi pk : W k (f (ψ₁ i))) : ((Hs (f (ψ₁ i))).stageAt
      (ts (f (ψ₁ i)))).Carrier) = x := (hφF k (ψ₁ i) hNi pk).trans hpx
  subst hxW
  obtain ⟨a, hat, ha, fs, hfs, -, hcross, hlast, hp'⟩ := hn
  have hck := hcτ k
  have haw : a ≤ w := by
    change (a : ℝ) ≤ (w : ℝ)
    rw [ha, hw]
    have h1 : T' ≤ τ k := by linarith [hTk.1]
    have h2 : T' / R (f (ψ₁ i)) ≤ τ k / R (f (ψ₁ i)) := div_le_div_of_nonneg_right h1 hR0.le
    linarith
  have hσw : (w : ℝ) = (ts (f (ψ₁ i)) : ℝ) + -T' / R (f (ψ₁ i)) := by
    rw [hw, neg_div]
    ring
  have hev := scalar_backwardPointTrace_eq_of_survivor_identity
    (Hs (f (ψ₁ i))) (ts (f (ψ₁ i))) a w haw hwt hR0 (h k (f (ψ₁ i))) fs hfs
    hcross hlast hσw (fun j hj => hp' (-T') ⟨by linarith [hTk.1], by linarith⟩ j hj)
    (φ k (ψ₁ i) hNi pk) Bt
  rw [hev]
  have hscal : metricScalarAt (h k (f (ψ₁ i)) (-T')) (φ k (ψ₁ i) hNi pk) ≤ C₀ + 1 := by
    have h1 := hsc pk hp
    rw [Real.dist_eq, hseq_eq i hNi, metricScalarAt_localPull, metricScalarAt_restrictOpen] at h1
    have h2 := hC₀ (-T') ⟨by linarith, by linarith⟩ p
    have h3 := abs_lt.mp h1
    linarith [h3.1, h3.2]
  have hC₀' : C₀ + 1 ≤ max C₀ 0 + 1 := by linarith [le_max_left C₀ 0]
  calc R (f (ψ₁ i)) * metricScalarAt (h k (f (ψ₁ i)) (-T')) (φ k (ψ₁ i) hNi pk)
      ≤ R (f (ψ₁ i)) * (max C₀ 0 + 1) := mul_le_mul_of_nonneg_left (hscal.trans hC₀') hR0.le
    _ = (max C₀ 0 + 1) * R (f (ψ₁ i)) := mul_comm _ _

end ObservedHistory

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
  {B ε C1 C2 τmin θ κ C1s C2s Cs : ℝ} {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ}
  {D θcap qcan qs η t₀ t s : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
  {H : ℕ → RetainedCoreHistory.{u}}
  {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
  {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
    ((H n).time (Fin.last (H n).eventCount)) (s n)}
  {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
  (hε : 0 < ε) (hεcone : ε ≤ coneAccuracy)
  (hκ : 0 < κ) (hphi : Perelman.AdmissiblePinchingFunction phi) (hθ : 0 < θ)
  (hCs : 1 ≤ Cs) (hCt : 0 < Ctime)
  (hH : ∀ n, (H n).InCutoffClass (P₀ := P₀) g₀ B (p₀ n) (δb n) (ρb n))
  (hG : ∀ n, (H n).IsContinuationSlab B (Fin.last (H n).eventCount) (G n))
  (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
  (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n ∧ qcan n ≤ qs n ∧ qs n ≤ Cs * qcan n)
  (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
    D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
  (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale)
  (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
  (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
    Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
  (hslabs : ∀ n,
    (H n).EventSlabsCanonical ε C1 C2 (qcan n) τmin (Fin.last (H n).eventCount) ∧
    (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount) ∧
    (H n).EventSlabsGradient Cgrad (qcan n) (Fin.last (H n).eventCount) ∧
    (H n).EventSlabsSpatiallyCanonical ε C1s C2s (qs n) (Fin.last (H n).eventCount) ∧
    (H n).NoncollapsedBefore κ ε ((H n).time (Fin.last (H n).eventCount)))
  (hbefore : ∀ n, t₀ n ∈ Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∧
    (G n).CanonicalBefore ε C1 C2 (qcan n) τmin (t₀ n) ∧
    (G n).DerivativeBoundBefore Ctime (qcan n) (t₀ n) ∧
    (G n).GradientBoundBefore Cgrad (qcan n) (t₀ n) ∧
    (G n).SpatiallyCanonicalBefore ε C1s C2s (qs n) (t₀ n) ∧
    (H n).TerminalNoncollapsedBefore (hH n).2.1 (G n) (hG n).2 κ ε (t₀ n))
  (hsliver : ∀ n, 0 < η n ∧ t₀ n + η n < s n ∧
    (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t₀ n + η n) ∧
    (∀ t' ∈ Icc (t₀ n) (t₀ n + η n), ∀ x, (G n).flow.scalar t' x * η n ≤ 1 / ((n : ℝ) + 1) ∧
      |(G n).flow.scalar t' x - (G n).flow.scalar (t₀ n) x| ≤ qcan n / 4 ∧
      ∀ v : TangentSpace ThreeModel x,
        ((G n).flow.base.metric t').inner x v v ≤
          Real.exp 1 * ((G n).flow.base.metric (t₀ n)).inner x v v ∧
        ((G n).flow.base.metric (t₀ n)).inner x v v ≤
          Real.exp 1 * ((G n).flow.base.metric t').inner x v v) ∧
    ∀ i b, ((records n i).static b).neck.scale * η n ≤ 1 / ((n : ℝ) + 2))
  (hbad : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n ∧ t₀ n ≤ t n ∧
    t n < t₀ n + η n ∧ qcan n < (G n).flow.scalar (t n) (y n) ∧
    (G n).flow.scalar (t n) (y n) * (t n - (H n).time (Fin.last (H n).eventCount)) < θ ∧
    ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n) (D n) (θcap n))

open ObservedHistory
  (exists_local_pointed_flow_limits_with_time_lipschitz_survivor_maps_of_depth_schedule) in
attribute [local instance] CheegerGromovCompactness.PointedRiemannianManifold.topology
  CheegerGromovCompactness.PointedRiemannianManifold.charted
  CheegerGromovCompactness.PointedRiemannianManifold.smooth
  CheegerGromovCompactness.PointedRiemannianManifold.t2
  CheegerGromovCompactness.PointedRiemannianManifold.sigmaCompact in
include hε hεcone hκ hphi hCs hH hG hrec hq hpar hscale hpinch hslabs hbefore hsliver hbad in
theorem exists_subseq_windowAnchorBound_of_depthExtendable
    (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) {σ : ℕ → ℕ} (hσ : StrictMono σ) {Tstar : ℝ}
    (hT : 0 < Tstar) :
    let K : ℕ → RetainedCoreHistory.{u} := fun n => (H n).extendAt (hH n).2.1 (G n) (hG n).2
      (hbad n).1 ((hbad n).2.2.1.trans (hsliver n).2.1)
    let τ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon := fun n =>
      (H n).extendAtTime (hH n).2.1 (G n) (hG n).2 (hbad n).1
        ((hbad n).2.2.1.trans (hsliver n).2.1)
    ∀ ŷ : ∀ n, ((K n).toHistory.stageAt (τ n)).Carrier, (∀ n, HEq (ŷ n) (y n)) →
    (∀ T : ℝ, 0 < T → T < Tstar → ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
      (fun n => (G n).flow.scalar (t n) (y n)) σ T) →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((K (σ (ψ i))).toHistory.stageMetric
          ((K (σ (ψ i))).toHistory.activeStage (τ (σ (ψ i)))) (τ (σ (ψ i)))) (ŷ (σ (ψ i)))
          (A / Real.sqrt ((G (σ (ψ i))).flow.scalar (t (σ (ψ i))) (y (σ (ψ i))))),
      ∀ (w : Icc (0 : ℝ) (K (σ (ψ i))).toHistory.horizon),
        (w : ℝ) = t (σ (ψ i)) - T' / (G (σ (ψ i))).flow.scalar (t (σ (ψ i))) (y (σ (ψ i))) →
      ∀ (hwt : w ≤ τ (σ (ψ i)))
        (Bt : BackwardPointTrace (K (σ (ψ i))).toHistory
          ((K (σ (ψ i))).toHistory.activeStage w)
          ((K (σ (ψ i))).toHistory.activeStage (τ (σ (ψ i))))
          ((K (σ (ψ i))).toHistory.activeStage_mono hwt) x),
        metricScalarAt ((K (σ (ψ i))).toHistory.stageMetric
            ((K (σ (ψ i))).toHistory.activeStage w) w)
          (Bt.point ((K (σ (ψ i))).toHistory.activeStage w) le_rfl
            ((K (σ (ψ i))).toHistory.activeStage_mono hwt)) ≤
          M * (G (σ (ψ i))).flow.scalar (t (σ (ψ i))) (y (σ (ψ i))) := by
  intro K τ ŷ hŷ hext
  have hts : ∀ n, t n < s n := fun n => (hbad n).2.2.1.trans (hsliver n).2.1
  have hRpos : ∀ n, 0 < (G n).flow.scalar (t n) (y n) := fun n =>
    (lt_of_lt_of_le (by positivity) (hq n).1).trans (hbad n).2.2.2.1
  obtain ⟨hτs0, hτsT, hc0, hcτ, hcmono, hcex⟩ := depth_schedule_facts hT
  have hcT' : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) < Tstar := fun k => (hcτ k).trans (hτsT k)
  have hcT : ∀ s ∈ Ioc (-Tstar) 0, ∃ k : ℕ, -(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) < s := fun s hs =>
    (hcex (-s) (by linarith [hs.1])).imp fun _ hk => by linarith
  have hR := tendsto_scalar_at_bad_point_atTop hq hbad
  have hRσ : Tendsto (fun m => (G (σ m)).flow.scalar (t (σ m)) (y (σ m))) atTop atTop :=
    hR.comp hσ.tendsto_atTop
  have hgap : Tendsto (fun n => (G n).flow.scalar (t n) (y n) * (t n - t₀ n)) atTop (𝓝 0) := by
    have hup : ∀ n, (G n).flow.scalar (t n) (y n) * (t n - t₀ n) ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have h1 := ((hsliver n).2.2.2.1 (t n) ⟨(hbad n).2.1, (hbad n).2.2.1.le⟩ (y n)).1
      have hgap : t n - t₀ n ≤ η n := by linarith [(hbad n).2.2.1]
      exact (mul_le_mul_of_nonneg_left hgap (hRpos n).le).trans h1
    have hlow : ∀ n, 0 ≤ (G n).flow.scalar (t n) (y n) * (t n - t₀ n) := fun n =>
      mul_nonneg (hRpos n).le (sub_nonneg.mpr (hbad n).2.1)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat hlow hup
  have hgapσ : Tendsto (fun m => (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) *
      (t (σ m) - t₀ (σ m))) atTop (𝓝 0) := hgap.comp hσ.tendsto_atTop
  obtain ⟨W, h, hblock, hlip, -, hlow, hpinchW, hncW, f, hf, P, F, ⟨Cd, hcan⟩, hPc, hconn,
      hballF, V, N, hV, hVF, φ, hφ, hφF, Gloc, hG0, hGsol, hGcompat, ψ₁, hψ₁, hconv⟩ :=
    exists_local_pointed_flow_limits_with_time_lipschitz_survivor_maps_of_depth_schedule
      (fun m => (K (σ m)).toHistory) (fun m => τ (σ m)) (fun m => ŷ (σ m))
      (fun m => (G (σ m)).flow.scalar (t (σ m)) (y (σ m))) (fun m => hRpos (σ m)) hRσ
      (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) hτs0
      (fun k => hext _ (hτs0 k) (hτsT k) _ (by positivity))
      hκ hε (t₀ := fun m => t₀ (σ m)) hgapσ
      (fun m v p r hv hr hball => (H (σ m)).volume_ge_extendAt_of_terminalNoncollapsedBefore
        (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2 (hbad (σ m)).1 (hts (σ m))
        (hslabs (σ m)).2.2.2.2 (hbefore (σ m)).2.2.2.2.2 v p r hv hr hball) hphi
      (fun m v _ x => (H (σ m)).curvatureOperatorLowerBoundAt_extendAt_of_pinched
        (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2 (hbad (σ m)).1 (hts (σ m)) (hpinch (σ m)).1
        (hpinch (σ m)).2 v x)
  let _ : ConnectedSpace P.M := hconn
  obtain ⟨hVmono, hVcover⟩ := monotone_and_cover_of_riemannianBallOf_eq hconn hV
  obtain ⟨Gl, hGlsol, hGlres⟩ :=
    exists_openClosed_solution_of_compatible_open_cover_of_depth_schedule hT V hVmono hVcover
      Gloc hGsol hGcompat
  have hGl0 : Gl 0 = P.metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    obtain ⟨k, hk⟩ := hVcover x
    have heq := (hGlres k 0 ⟨by linarith [hc0 k], le_rfl⟩).trans (hG0 k)
    exact congrArg (fun q : SmoothRiemannianMetric ThreeModel (V k) => q.inner ⟨x, hk⟩ v w) heq
  have hconvG : ∀ k (K' : Set (V k)), IsCompact K' → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ₁ i,
        ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
          (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)))) 0,
        metricDerivNormSupOn K' p
          (localPullMetric (h k (f (ψ₁ i)) s) (φ k (ψ₁ i) hi) (hφ k (ψ₁ i) hi))
          ((Gl s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η := by
    intro k K' hK' p η hη
    obtain ⟨j₀, hj₀⟩ := hconv k K' hK' p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨hi', hb⟩ := hj₀ i hi
    refine ⟨hi', fun s hs => ?_⟩
    rw [hGlres k s hs]
    exact hb s hs
  have hsol : ∀ k : ℕ, ∀ᶠ n in atTop, IsSolutionOn ({ base.metric := h k n } :
      SolutionOn (I := ThreeModel) (M := W k n)
        (RealTimeInterval.closed (-(Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) 0
          (neg_nonpos.mpr (hτs0 k).le))) := fun k => (hblock k).mono fun _ hn => hn.2.1
  let E' : ℕ → Set ℝ := fun m => Iic 0 ∩
    ({s | t₀ (σ m) ≤ (τ (σ m) : ℝ) + s / (G (σ m)).flow.scalar (t (σ m)) (y (σ m))} ∪
      {s | ∃ i, (τ (σ m) : ℝ) + s / (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) =
        (K (σ m)).toHistory.time i})
  have hEs : ∀ m s, s ≤ 0 → s ∉ E' m →
      (τ (σ m) : ℝ) + s / (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) < t₀ (σ m) ∧
        ∀ i, (τ (σ m) : ℝ) + s / (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) ≠
          (K (σ m)).toHistory.time i := by
    intro m s hs hsE
    simp only [E', mem_inter_iff, mem_Iic, mem_union, mem_ofPred_eq, not_and, not_or,
      not_exists] at hsE
    obtain ⟨h1, h2⟩ := hsE hs
    exact ⟨not_le.mp h1, h2⟩
  have hE' : ∀ m, (E' m \ Icc (-((G (σ m)).flow.scalar (t (σ m)) (y (σ m)) *
      (t (σ m) - t₀ (σ m)))) 0).Finite := by
    intro m
    refine (Set.finite_range fun i : Fin ((K (σ m)).toHistory.eventCount + 1) =>
      (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) *
        ((K (σ m)).toHistory.time i - t (σ m))).subset ?_
    rintro s ⟨⟨hs0, hs⟩, hsI⟩
    have hs0 : s ≤ 0 := hs0
    have hRm := hRpos (σ m)
    rcases hs with hs | ⟨i, hi⟩
    · refine absurd ⟨?_, hs0⟩ hsI
      have hs' : (t₀ (σ m) - t (σ m)) * (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) ≤ s :=
        (le_div_iff₀ hRm).mp (show t₀ (σ m) - t (σ m) ≤
            s / (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) by
          have : t₀ (σ m) ≤ t (σ m) + s / (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) := hs
          linarith)
      linarith
    · refine ⟨i, ?_⟩
      have hi' : t (σ m) + s / (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) =
          (K (σ m)).toHistory.time i := hi
      have : s / (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) =
          (K (σ m)).toHistory.time i - t (σ m) := by
        linarith
      change (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) *
        ((K (σ m)).toHistory.time i - t (σ m)) = s
      rw [← this, mul_div_assoc']
      exact mul_div_cancel_left₀ s hRm.ne'
  obtain ⟨D, hD, hL1⟩ :=
    ObservedHistory.exists_eventually_neckAlternatives_or_isCompact_of_survivor_blocks.{u}
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max 1 (max (2 * |C1s|) C2s) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := hC ▸ le_max_left _ _
  have hC0 : max (2 * |C1s|) C2s ≤ C := hC ▸ le_max_right _ _
  obtain ⟨qW, hqW⟩ : ∃ qW : ℝ,
      qW = max Cs ((Real.exp 1 * (C + (D + 2 * ε⁻¹) * Real.sqrt C)) ^ 2) := ⟨_, rfl⟩
  have hqWsq : (Real.exp 1 * (C + (D + 2 * ε⁻¹) * Real.sqrt C)) ^ 2 ≤ qW :=
    hqW ▸ le_max_right _ _
  have hqWs : Cs ≤ qW := hqW ▸ le_max_left _ _
  have hqs' : ∀ m, qs (σ m) ≤ (G (σ m)).flow.scalar (t (σ m)) (y (σ m)) * qW := fun m =>
    ((hq (σ m)).2.2.trans (mul_le_mul_of_nonneg_left (hbad (σ m)).2.2.2.1.le
      (by linarith))).trans
      (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hqWs (hRpos (σ m)).le)
  have hW := hL1 (Hs := fun m => (K (σ m)).toHistory) (ts := fun m => τ (σ m))
    (ys := fun m => ŷ (σ m)) (hR := fun m => hRpos (σ m)) (W := W) (h := h)
    (c := fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) hτs0 (fun k => (hcτ k).le)
    (fun k => (hblock k).mono fun _ hn => hn.1) (fun k => (hblock k).mono fun _ hn => hn.2.2.1)
    (fun k => (hblock k).mono fun _ hn => by
      obtain ⟨a, hat, ha, fs, hfs, hinj, -, -, hp⟩ := hn.2.2.2.1
      exact ⟨a, hat, ha, fs, hfs, hinj, hp⟩) hlow (t₀ := fun m => t₀ (σ m)) (E := E')
    (qs := fun m => qs (σ m)) hε hC1 hC0 hqs' hqWsq
    (fun m v hv hvk p hpq => (H (σ m)).exists_spatialCanonicalWitness_extendAt_of_before
      (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2 (hbad (σ m)).1 (hts (σ m))
      (hslabs (σ m)).2.2.2.1 (hbefore (σ m)).2.2.2.2.1 v hv hvk p hpq) hEs
  have hderiv := ObservedHistory.eventually_abs_derivWithin_scalar_le_of_survivor_blocks
    (Hs := fun m => (K (σ m)).toHistory) (ts := fun m => τ (σ m))
    (hR := fun m => hRpos (σ m)) (W := W) (h := h)
    (τ := fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))
    (fun k => (hblock k).mono fun _ hn => by
      obtain ⟨a, hat, ha, fs, hfs, -, -, -, hp⟩ := hn.2.2.2.1
      exact ⟨a, hat, ha, fs, hfs, hp⟩) (E := E')
    (Ct := ((2 * Ctime : ℝ≥0) : ℝ)) (qD := 2) (NNReal.coe_nonneg _)
    (qst := fun m => 2 * qcan (σ m)) (fun m => by nlinarith [(hbad (σ m)).2.2.2.1])
    (fun m v hv hvk p hpq =>
      (K (σ m)).abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt
        (t := τ (σ m)) (t₀ := (τ (σ m) : ℝ)) le_rfl
        ((H (σ m)).derivativeBound_inputs_extendAt (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2
          (hbad (σ m)).1 (hts (σ m)) (by linarith [(hq (σ m)).1,
            (Nat.cast_nonneg (σ m) : (0 : ℝ) ≤ σ m)]) (hslabs (σ m)).2.1
          ((G (σ m)).derivativeBoundBefore_mono (hbad (σ m)).2.2.1.le
            (hsliver (σ m)).2.2.1)).1
        ((H (σ m)).derivativeBound_inputs_extendAt (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2
          (hbad (σ m)).1 (hts (σ m)) (by linarith [(hq (σ m)).1,
            (Nat.cast_nonneg (σ m) : (0 : ℝ) ≤ σ m)]) (hslabs (σ m)).2.1
          ((G (σ m)).derivativeBoundBefore_mono (hbad (σ m)).2.2.1.le
            (hsliver (σ m)).2.2.1)).2.1
        ((H (σ m)).derivativeBound_inputs_extendAt (hH (σ m)).2.1 (G (σ m)) (hG (σ m)).2
          (hbad (σ m)).1 (hts (σ m)) (by linarith [(hq (σ m)).1,
            (Nat.cast_nonneg (σ m) : (0 : ℝ) ≤ σ m)]) (hslabs (σ m)).2.1
          ((G (σ m)).derivativeBoundBefore_mono (hbad (σ m)).2.2.1.le
            (hsliver (σ m)).2.2.1)).2.2 v hv hvk p hpq)
    (fun m s hs hsE => (hEs m s hs hsE).2)
  have hX4d := eventually_scalar_le_at_normalized_distance_of_anchor hε hεcone hκ hphi hH hG
    hrec hq hpar hscale hpinch hslabs hbefore hsliver hbad
  have happrox := ObservedHistory.survivor_blocks_scalar_le_at_distance
    (Hs := fun m => (K (σ m)).toHistory) (ts := fun m => τ (σ m))
    (hR := fun m => hRpos (σ m)) (W := W) (h := h)
    (τ := fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))
    (fun k => (hblock k).mono fun _ hn => by
      obtain ⟨a, hat, ha, fs, hfs, -, -, -, hp⟩ := hn.2.2.2.1
      exact ⟨a, hat, ha, fs, hfs, hp⟩)
    (c := fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
      (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) (fun k => (hcτ k).le)
    (fun A Dd hA hD => (hX4d A Dd hA hD).imp fun _ hC' σ' hσ' =>
      hσ.tendsto_atTop.eventually (hC'.2 σ' hσ'))
  have hradii : Tendsto (fun m => ε * Real.sqrt ((G (σ m)).flow.scalar (t (σ m)) (y (σ m))))
      atTop atTop := (Real.tendsto_sqrt_atTop.comp hRσ).const_mul_atTop hε
  obtain ⟨C₀, hC₀⟩ := exists_uniform_scalar_bound_of_local_flow_limit_on_window hf F Cd hcan hPc
    hconn hV hVF hφF
    (fun k => by
      filter_upwards [hf.tendsto_atTop.eventually (hblock k),
        hballF ((k + 3 : ℕ) : ℝ) (by positivity)] with j hj hb x hx
      have hx' : x ∈ (W k (f j) : Set _) := hx
      rw [hj.1] at hx'
      exact hb (show riemannianEDistOf _ _ _ ≤ _ from le_of_lt hx'))
    hT hτs0 hcτ hcmono hcT hGl0 hGlsol hψ₁ hconvG hsol hRσ hphi
    (fun k => (hpinchW k).mono fun _ hn s hs x => hn s ⟨by linarith [hs.1, hcτ k], hs.2⟩ x)
    hlip hgapσ hE' hεX hC1 (by positivity : (0 : ℝ) < κ / 250) hW hderiv
    (fun hcomplete =>
      parabolicallyKappaNoncollapsedBelowScale_of_local_flow_limit_on_openClosed
        hT (fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))
        (fun k => ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) *
          (Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))) hc0 hcτ hcT' hcmono hcex hsol hκ
        hradii hncW hf F hVmono hVcover hVF φ hφ hφF hGlsol hcomplete hψ₁ hconvG 1 one_pos)
    happrox
  refine ⟨fun i => f (ψ₁ i), hf.comp hψ₁, max C₀ 0 + 1, by positivity,
    fun T' hT' hT'T A hA => ?_⟩
  exact ObservedHistory.eventually_scalar_backwardPointTrace_le_of_window_limit
    (Hs := fun m => (K (σ m)).toHistory) (ts := fun m => τ (σ m)) (ys := fun m => ŷ (σ m))
    (hR := fun m => hRpos (σ m)) (W := W) (h := h)
    (τ := fun k => Tstar * ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))
    (fun k => (hblock k).mono fun _ hn => hn.2.2.2.1) hf F Cd hcan hPc hV hφF
    (fun k => (hcτ k).le) hcmono hcT hψ₁ hconvG hC₀ hT' hT'T hA

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
