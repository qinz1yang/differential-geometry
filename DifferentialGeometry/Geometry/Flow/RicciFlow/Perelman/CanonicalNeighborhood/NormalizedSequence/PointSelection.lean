import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Metric.RiemannianPointPicking
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem NormalizedSequence.exists_terminal_scalar_point_selection
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (h : ¬ BoundedAtDistance X) :
    ∃ D : ℝ, 0 < D ∧ ∃ f : ℕ → ℕ, StrictMono f ∧
      ∃ (x : ∀ i, (X.term (f i)).M) (r : ℕ → ℝ),
        (∀ i, 0 < r i ∧ r i < D + 1 ∧
          metricDistance ((X.term (f i)).S.base.metric 0) (X.term (f i)).basepoint (x i) <
            D + 1 ∧ 0 < (X.term (f i)).S.scalar 0 (x i)) ∧
        Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i)) atTop atTop ∧
        Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i) * r i ^ 2) atTop atTop ∧
        ∀ i y, metricDistance ((X.term (f i)).S.base.metric 0) (x i) y ≤ r i →
          metricDistance ((X.term (f i)).S.base.metric 0) (X.term (f i)).basepoint y < D + 1 ∧
            (X.term (f i)).S.scalar 0 y ≤ 2 * (X.term (f i)).S.scalar 0 (x i) := by
  classical
  simp only [BoundedAtDistance] at h
  push Not at h
  obtain ⟨D, hD, hfail⟩ := h
  choose C hC using X.source_bound
  let B : ℕ → ℝ := fun i => (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (max (C i) 0)
  have hB0 (i : ℕ) : 0 ≤ B i := by dsimp only [B]; positivity
  have hzero (i : ℕ) : (0 : ℝ) ∈ (X.interval i).carrier := by
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hB (i : ℕ) (p : (X.term i).M) : (X.term i).S.scalar 0 p ≤ B i := by
    have hrm := (hC i 0 (hzero i) p).trans (le_max_left (C i) 0)
    have hscal := scalar_abs_le_rm (I := I3) ((X.term i).S.base.metric 0) p
    exact (le_abs_self _).trans (hscal.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrm) (by positivity)))
  have hex (n : ℕ) : ∃ i : ℕ, n ≤ i ∧ ∃ y : (X.term i).M,
      metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ D ∧
        16 * ((n : ℝ) + 1) < (X.term i).S.scalar 0 y := by
    obtain ⟨i, y, hdist, hlarge⟩ := hfail
      (max (16 * ((n : ℝ) + 1)) (∑ j ∈ Finset.range n, B j))
    have hni : n ≤ i := by
      by_contra hn
      have hsum : B i ≤ ∑ j ∈ Finset.range n, B j :=
        Finset.single_le_sum (fun j _ => hB0 j) (Finset.mem_range.mpr (lt_of_not_ge hn))
      exact (not_lt_of_ge ((hB i y).trans (hsum.trans (le_max_right _ _)))) hlarge
    exact ⟨i, hni, y, hdist, (le_max_left _ _).trans_lt hlarge⟩
  choose ind hind y hdist hlarge using hex
  have hselect (n : ℕ) : ∃ p : (X.term (ind n)).M,
      metricDistance ((X.term (ind n)).S.base.metric 0) (X.term (ind n)).basepoint p < D + 1 ∧
      0 < (X.term (ind n)).S.scalar 0 p ∧
      (X.term (ind n)).S.scalar 0 (y n) *
          (D + 1 - metricDistance ((X.term (ind n)).S.base.metric 0)
            (X.term (ind n)).basepoint (y n)) ^ 2 ≤
        (X.term (ind n)).S.scalar 0 p *
          (D + 1 - metricDistance ((X.term (ind n)).S.base.metric 0)
            (X.term (ind n)).basepoint p) ^ 2 ∧
      ∀ z, metricDistance ((X.term (ind n)).S.base.metric 0) p z ≤
          (D + 1 - metricDistance ((X.term (ind n)).S.base.metric 0)
            (X.term (ind n)).basepoint p) / 4 →
        metricDistance ((X.term (ind n)).S.base.metric 0) (X.term (ind n)).basepoint z < D + 1 ∧
          (X.term (ind n)).S.scalar 0 z ≤ 2 * (X.term (ind n)).S.scalar 0 p := by
    let _ : ConnectedSpace (X.term (ind n)).M := X.connected (ind n)
    let _ : IsManifold I3 1 (X.term (ind n)).M := IsManifold.of_le (n := ∞) (by decide)
    let _ : TopologicalSpace.MetrizableSpace (X.term (ind n)).M := Manifold.metrizableSpace I3 _
    have hc : RiemannianMetricComplete ((X.term (ind n)).S.base.metric 0) :=
      ⟨X.complete (ind n) 0 (hzero (ind n))⟩
    have hfy : 0 < (X.term (ind n)).S.scalar 0 (y n) := by
      linarith [hlarge n, Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨p, hp, hfp, hw, hb⟩ :=
      (((X.term (ind n)).S.base.metric 0).exists_weighted_point_selection
        (f := (X.term (ind n)).S.scalar 0) (eta := 1 / 4)
        (hc.closedEBall_isCompact (X.term (ind n)).basepoint (D + 1))
        (metricScalar_smooth (I := I3) ((X.term (ind n)).S.base.metric 0)).continuous.continuousOn
        (by change metricDistance _ _ _ < D + 1; linarith [hdist n]) hfy (by norm_num))
    refine ⟨p, hp, hfp, hw, fun z hz => ?_⟩
    have hh := hb z (by simpa only [metricDistance, div_eq_mul_inv, one_mul, mul_comm] using hz)
    refine ⟨hh.1, hh.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ hfp.le
    norm_num
  choose x hx hpos hweight hcontrol using hselect
  let r : ℕ → ℝ := fun n =>
    (D + 1 - metricDistance ((X.term (ind n)).S.base.metric 0) (X.term (ind n)).basepoint (x n)) / 4
  have hrpos (n : ℕ) : 0 < r n := div_pos (sub_pos.mpr (hx n)) (by norm_num)
  have hrle (n : ℕ) : r n < D + 1 := by
    dsimp only [r]
    linarith [show 0 ≤ metricDistance ((X.term (ind n)).S.base.metric 0)
      (X.term (ind n)).basepoint (x n) from ENNReal.toReal_nonneg]
  have hprod : Tendsto (fun n => (X.term (ind n)).S.scalar 0 (x n) * r n ^ 2) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    have hmargin : 1 ≤ D + 1 - metricDistance ((X.term (ind n)).S.base.metric 0)
        (X.term (ind n)).basepoint (y n) := by linarith [hdist n]
    have hsquare := (sq_le_sq₀ zero_le_one (zero_le_one.trans hmargin)).mpr hmargin
    have hmul := mul_le_mul_of_nonneg_left hsquare
      (by linarith [hlarge n, Nat.cast_nonneg (α := ℝ) n] : 0 ≤ (X.term (ind n)).S.scalar 0 (y n))
    dsimp only [r]
    nlinarith [hweight n, hlarge n]
  have hvalue : Tendsto (fun n => (X.term (ind n)).S.scalar 0 (x n)) atTop atTop := by
    apply Tendsto.atTop_of_const_mul₀ (sq_pos_of_pos (by linarith : 0 < D + 1))
    apply tendsto_atTop_mono (fun n => ?_) hprod
    have hsquare := (sq_le_sq₀ (hrpos n).le (by linarith : 0 ≤ D + 1)).mpr (hrle n).le
    nlinarith [mul_le_mul_of_nonneg_left hsquare (hpos n).le]
  obtain ⟨phi, hphi, hmono⟩ := strictMono_subseq_of_id_le hind
  exact ⟨D, hD, ind ∘ phi, hmono, (fun n => x (phi n)), r ∘ phi,
    (fun n => ⟨hrpos (phi n), hrle (phi n), hx (phi n), hpos (phi n)⟩),
    hvalue.comp hphi.tendsto_atTop, hprod.comp hphi.tendsto_atTop,
    fun n z hz => hcontrol (phi n) z hz⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
