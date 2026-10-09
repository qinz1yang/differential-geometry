import DifferentialGeometry.Geometry.Metric.Approximation.BasepointCompactness
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistortion
import DifferentialGeometry.Topology.MetricSpace.ProperApproximation
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open Filter Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem metric_bounds_of_approximation
    {g : SmoothRiemannianMetric I M} {Φ : PartialDiffeomorph I I M M ∞}
    {K : Set M} {p : ℕ} {ε : ℝ} (hΦ : isMetricApproximationOn Φ K p ε g g)
    (hε : ε ≤ 1 / 2) {x : M} (hx : x ∈ K) (v : TangentSpace I x) :
    g.inner x v v ≤ (1 + 2 * ε) ^ 2 *
      g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x v) ∧
    g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x v) ≤
      (1 + 2 * ε) ^ 2 * g.inner x v v := by
  have hε0 : 0 ≤ ε := hΦ.epsilon_pos.le
  have hgnonneg : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hpnonneg : 0 ≤ g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x v) := by
    by_cases hv : mfderiv I I Φ x v = 0
    · simp [hv]
    · exact (g.pos (Φ x) _ hv).le
  obtain ⟨hl, hu⟩ := hΦ.quadratic_bounds hx v
  have hc : 1 ≤ (1 + 2 * ε) * (1 - ε) := by
    nlinarith [mul_nonneg hε0 (show 0 ≤ 1 - 2 * ε by linarith)]
  have hL : 0 ≤ 1 + 2 * ε := by linarith
  have hLL : 1 + 2 * ε ≤ (1 + 2 * ε) ^ 2 := by nlinarith
  constructor
  · calc
      g.inner x v v ≤ ((1 + 2 * ε) * (1 - ε)) * g.inner x v v := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hgnonneg
      _ = (1 + 2 * ε) * ((1 - ε) * g.inner x v v) := by ring
      _ ≤ (1 + 2 * ε) * g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x v) :=
        mul_le_mul_of_nonneg_left hl hL
      _ ≤ _ := mul_le_mul_of_nonneg_right hLL hpnonneg
  · exact hu.trans (mul_le_mul_of_nonneg_right (by nlinarith) hgnonneg)

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [PreconnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_isometry_close_of_metric_approximation
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (hvol : Integral.Measure.riemannianVolumeMeasure I M g Set.univ < ⊤)
    (o : M) {ζ : ℝ} (hζ : 0 < ζ) :
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : PseudoMetricSpace M := g.toPseudoMetricSpace
    letI : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
    ∃ N : ℕ, 1 ≤ N ∧ ζ⁻¹ < (N : ℝ) + 1 ∧
      ∀ Φ : PartialDiffeomorph I I M M ∞,
      isMetricApproximationOn Φ (riemannianClosedBallOf g o (N + 1 : ℝ))
        (N + 1) (1 / (N + 1 : ℝ)) g g →
      ∃ e : M ≃ᵢ M,
        sSup ((fun p => dist (e p) (Φ p)) '' Metric.closedBall o ζ⁻¹) < ζ := by
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : PseudoMetricSpace M := g.toPseudoMetricSpace
  let _ : MetricSpace M := MetricSpace.ofT0PseudoMetricSpace M
  have hcore : ∃ N : ℕ, 1 ≤ N ∧ ∀ Φ : PartialDiffeomorph I I M M ∞,
    isMetricApproximationOn Φ (riemannianClosedBallOf g o (N + 1 : ℝ))
      (N + 1) (1 / (N + 1 : ℝ)) g g →
    ∃ e : M ≃ᵢ M,
      sSup ((fun p => dist (e p) (Φ p)) '' Metric.closedBall o ζ⁻¹) < ζ := by
    have hclosed (x : M) {r : ℝ} (hr : 0 ≤ r) :
        riemannianClosedBallOf g x r = Metric.closedBall x r := by
      ext y
      change edist x y ≤ ENNReal.ofReal r ↔ dist y x ≤ r
      rw [edist_dist, dist_comm, ENNReal.ofReal_le_ofReal_iff hr]
    let _ : ProperSpace M := ⟨fun x r => by
      by_cases hr : 0 ≤ r
      · rw [← hclosed x hr]
        exact hg.closedEBall_isCompact x r
      · rw [Metric.closedBall_eq_empty.mpr (lt_of_not_ge hr)]
        exact isCompact_empty⟩
    by_contra hnot
    push Not at hnot
    have hcounter (n : ℕ) : ∃ Φ : PartialDiffeomorph I I M M ∞,
        isMetricApproximationOn Φ (riemannianClosedBallOf g o (n + 2 : ℝ))
          (n + 2) (1 / (n + 2 : ℝ)) g g ∧
        ∀ e : M ≃ᵢ M,
          ζ ≤ sSup ((fun p => dist (e p) (Φ p)) '' Metric.closedBall o ζ⁻¹) := by
      obtain ⟨Φ, hΦ, hbad⟩ := hnot (n + 1) (by omega)
      refine ⟨Φ, ?_, hbad⟩
      norm_num [Nat.cast_add, add_assoc] at hΦ
      simpa only [one_div] using hΦ
    choose Φ hΦ hbad using hcounter
    let ε : ℕ → ℝ := fun n => 1 / (n + 2 : ℝ)
    let L : ℕ → ℝ := fun n => 1 + 2 * ε n
    have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
    have hεsmall (n : ℕ) : ε n ≤ 1 / 2 := by
      dsimp [ε]
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < n + 2) (by norm_num : (0 : ℝ) < 2)).mpr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hLone (n : ℕ) : 1 ≤ L n := by dsimp [L]; linarith [hεpos n]
    have hLtwo (n : ℕ) : L n ≤ 2 := by dsimp [L]; linarith [hεsmall n]
    have hεlim : Tendsto ε atTop (𝓝 0) := by
      simpa only [ε, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
    have hquad (n : ℕ) : ∀ x ∈ riemannianClosedBallOf g o (n + 2 : ℝ),
        ∀ v : TangentSpace I x,
          g.inner x v v ≤ L n ^ 2 * g.inner (Φ n x)
            (mfderiv I I (Φ n) x v) (mfderiv I I (Φ n) x v) ∧
          g.inner (Φ n x) (mfderiv I I (Φ n) x v) (mfderiv I I (Φ n) x v) ≤
            L n ^ 2 * g.inner x v v := by
      intro x hx v
      exact metric_bounds_of_approximation (hΦ n) (hεsmall n) hx v
    have hreal {a b c d : M} {C : ℝ} (hC : 0 ≤ C)
        (h : riemannianEDistOf g a b ≤ ENNReal.ofReal C * riemannianEDistOf g c d) :
        dist a b ≤ C * dist c d := by
      change edist a b ≤ ENNReal.ofReal C * edist c d at h
      rw [edist_dist, edist_dist, ← ENNReal.ofReal_mul hC] at h
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC dist_nonneg)).mp h
    have hdist_bounds (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
        (hbuf : 3 * L n ^ 2 * r < (n : ℝ) + 2) {x y : M}
        (hx : x ∈ Metric.closedBall o r) (hy : y ∈ Metric.closedBall o r) :
        dist (Φ n x) (Φ n y) ≤ L n * dist x y ∧
        dist x y ≤ L n * dist (Φ n x) (Φ n y) := by
      have hb := edist_bounds_of_metric_bounds_on_buffered_ball g g (Φ n) o (x := x) (y := y) hr (hLone n) hbuf
        (hg.closedEBall_isCompact o (n + 2 : ℝ)) (hΦ n).1 (hquad n)
        (by rwa [hclosed o hr]) (by rwa [hclosed o hr])
      exact ⟨hreal (zero_le_one.trans (hLone n)) hb.1,
        hreal (zero_le_one.trans (hLone n)) hb.2⟩
    have hbase : ∃ K : Set M, IsCompact K ∧ ∃ᶠ n in atTop, Φ n o ∈ K := by
      obtain ⟨K, hK, hmaps⟩ := exists_isCompact_basepoint_images_of_metric_approximation
        g hg hvol o (r := 1) zero_lt_one
      refine ⟨K, hK, Filter.Frequently.of_forall fun n => ?_⟩
      have hr : (1 : ℝ) ≤ n + 2 := by
        have hn := Nat.cast_nonneg (α := ℝ) n
        linarith
      exact hmaps (Φ n) ((hΦ n).mono (riemannianClosedBallOf_mono g o hr) le_rfl le_rfl)
        (hεsmall n)
    have hdist : ∀ R δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        ∀ x ∈ Metric.closedBall o R, ∀ y ∈ Metric.closedBall o R,
          |dist (Φ n x) (Φ n y) - dist x y| < δ := by
      intro R δ hδ
      let r : ℝ := max R 0
      have hr : 0 ≤ r := le_max_right _ _
      obtain ⟨N, hN⟩ := exists_nat_gt (12 * r)
      have herr : ∀ᶠ n in atTop, 8 * r * ε n < δ := by
        have ht : Tendsto (fun n => 8 * r * ε n) atTop (𝓝 0) := by
          simpa only [mul_zero] using tendsto_const_nhds.mul hεlim
        exact ht.eventually_lt_const hδ
      filter_upwards [eventually_ge_atTop N, herr] with n hn hnerr x hx y hy
      have hnR : 12 * r < (n : ℝ) + 2 := by
        have hNn : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
        linarith
      have hLs : L n ^ 2 ≤ 4 := by nlinarith [hLone n, hLtwo n]
      have hbuf : 3 * L n ^ 2 * r < (n : ℝ) + 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hLs hr]
      have hx' : x ∈ Metric.closedBall o r := Metric.closedBall_subset_closedBall (le_max_left _ _) hx
      have hy' : y ∈ Metric.closedBall o r := Metric.closedBall_subset_closedBall (le_max_left _ _) hy
      obtain ⟨hu, hl⟩ := hdist_bounds n hr hbuf hx' hy'
      have hxy : dist x y ≤ 2 * r := by
        have htri := dist_triangle x o y
        have hxo : dist x o ≤ r := hx'
        have hyo : dist y o ≤ r := hy'
        rw [dist_comm o y] at htri
        linarith
      have hmap : dist (Φ n x) (Φ n y) ≤ 4 * r := by
        have hmul := mul_le_mul_of_nonneg_left hxy (zero_le_one.trans (hLone n))
        have hmul' := mul_le_mul_of_nonneg_right (hLtwo n) (by positivity : 0 ≤ 2 * r)
        linarith
      have hlmul := mul_le_mul_of_nonneg_left hmap (sub_nonneg.mpr (hLone n))
      have humul := mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr (hLone n))
      have herr0 : 0 ≤ r * ε n := mul_nonneg hr (hεpos n).le
      dsimp only [L] at hu hl hlmul humul
      apply abs_lt.mpr
      constructor <;> nlinarith only [hu, hl, hlmul, humul, hnerr, herr0]
    have hcapture : ∀ R : ℝ, 0 < R → ∃ S : ℝ, ∀ᶠ n in atTop,
        Metric.ball (Φ n o) R ⊆ (Φ n) '' Metric.closedBall o S := by
      intro R hR
      let S : ℝ := 2 * R + 1
      have hS : 0 < S := by dsimp [S]; linarith
      obtain ⟨N, hN⟩ := exists_nat_gt S
      refine ⟨S, ?_⟩
      filter_upwards [eventually_ge_atTop N] with n hn
      have hSN : S ≤ (n : ℝ) + 2 := by
        have hNn : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
        linarith
      have hsub := riemannianClosedBallOf_mono g o hSN
      have hlower : ∀ x ∈ riemannianClosedBallOf g o S, ∀ v : TangentSpace I x,
          g.inner x v v ≤ (2 : ℝ) ^ 2 * g.inner (Φ n x)
            (mfderiv I I (Φ n) x v) (mfderiv I I (Φ n) x v) := by
        intro x hx v
        have hp : 0 ≤ g.inner (Φ n x) (mfderiv I I (Φ n) x v) (mfderiv I I (Φ n) x v) := by
          by_cases hv : mfderiv I I (Φ n) x v = 0
          · simp [hv]
          · exact (g.pos (Φ n x) _ hv).le
        exact (hquad n x (hsub hx) v).1.trans
          (mul_le_mul_of_nonneg_right (by nlinarith [hLone n, hLtwo n]) hp)
      have hc := PDE.RicciFlow.Perelman.CanonicalNeighborhood.closedBall_subset_image_of_metric_lower
        g g (Φ n) o hS (by norm_num : (0 : ℝ) < 2) (by dsimp [S]; linarith : R < S / 2)
        (hg.closedEBall_isCompact o S) (hsub.trans (hΦ n).1) hlower
      rw [hclosed (Φ n o) hR.le, hclosed o hS.le] at hc
      exact Metric.ball_subset_closedBall.trans hc
    obtain ⟨k, e, _, hconv⟩ := Metric.exists_isometryEquiv_subsequence_of_distortion
      (fun n x => Φ n x) o hbase hdist hcapture
    have hnear : ∀ᶠ n in atTop, ∀ p ∈ Metric.closedBall o ζ⁻¹,
        dist (e p) (Φ (k n) p) < ζ / 2 :=
      Metric.tendstoUniformlyOn_iff.mp
        (hconv (Metric.closedBall o ζ⁻¹) (isCompact_closedBall o ζ⁻¹)) (ζ / 2) (half_pos hζ)
    obtain ⟨n, hn⟩ := hnear.exists
    have hnonempty : ((fun p => dist (e p) (Φ (k n) p)) '' Metric.closedBall o ζ⁻¹).Nonempty :=
      ⟨dist (e o) (Φ (k n) o), o, Metric.mem_closedBall_self (inv_nonneg.mpr hζ.le), rfl⟩
    have hbound : ∀ t ∈ ((fun p => dist (e p) (Φ (k n) p)) '' Metric.closedBall o ζ⁻¹),
        t ≤ ζ / 2 := by
      rintro t ⟨p, hp, rfl⟩
      exact (hn p hp).le
    have hbdd : BddAbove ((fun p => dist (e p) (Φ (k n) p)) '' Metric.closedBall o ζ⁻¹) :=
      ⟨ζ / 2, hbound⟩
    have hsup : sSup ((fun p => dist (e p) (Φ (k n) p)) '' Metric.closedBall o ζ⁻¹) ≤ ζ / 2 :=
      (isLUB_csSup hnonempty hbdd).2 hbound
    have hlt : ζ / 2 < ζ := by linarith
    exact (not_lt_of_ge (hbad (k n) e)) (hsup.trans_lt hlt)
  obtain ⟨N, hN, hmaps⟩ := hcore
  obtain ⟨B, hB⟩ := exists_nat_gt ζ⁻¹
  have hNM : (N : ℝ) + 1 ≤ (max N B : ℕ) + 1 := by
    exact_mod_cast Nat.add_le_add_right (le_max_left N B) 1
  refine ⟨max N B, hN.trans (le_max_left N B), ?_, ?_⟩
  · have hBM : (B : ℝ) ≤ (max N B : ℕ) := Nat.cast_le.mpr (le_max_right N B)
    linarith
  · intro Φ hΦ
    apply hmaps Φ
    apply hΦ.mono (riemannianClosedBallOf_mono g o hNM)
      (Nat.add_le_add_right (le_max_left N B) 1)
    exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < N + 1) hNM

end DifferentialGeometry.PartialDiffeomorph
