import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarEscape
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarBlowup
import DifferentialGeometry.Geometry.Geodesic.Ray
import DifferentialGeometry.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_standard_high_scalar_geodesic_tail
    {tau : ℝ} (htau : 0 < tau) (B : ℝ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ (S : PartialStandardSolution) (t : ℝ),
      t ∈ S.domain → tau ≤ t → t < 1 → ∀ p y : E3,
        metricScalarAt (S.metric t) p ≤ B → C < metricScalarAt (S.metric t) y →
        let L := (riemannianEDistOf (S.metric t) p y).toReal
        ∃ (gamma : ℝ → E3) (s : ℝ), s ∈ Ico 0 L ∧
          gamma 0 = p ∧ gamma L = y ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ gamma ∧
          (∀ u, DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicAt
            (S.metric t) gamma u) ∧
          (∀ u, (S.metric t).inner (gamma u)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma u 1)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma u 1) = 1) ∧
          (∀ u ∈ Icc 0 L, ∀ v ∈ Icc 0 L,
            (riemannianEDistOf (S.metric t) (gamma u) (gamma v)).toReal = |u - v|) ∧
          metricScalarAt (S.metric t) (gamma s) = B ∧
          (∀ u ∈ Ioc s L, B < metricScalarAt (S.metric t) (gamma u)) ∧
          r < L - s := by
  obtain ⟨r, C, hr, hC, hball⟩ := exists_standard_scalar_bound_on_ball_of_scalar_le htau B
  refine ⟨max B C, r, hC.trans_le (le_max_right _ _), hr, ?_⟩
  intro S t ht htaut ht1 p y hp hy L
  have hpne : p ≠ y := by
    intro heq
    have hh := (le_max_left B C).trans_lt hy
    rw [← heq] at hh
    exact (not_lt_of_ge hp) hh
  obtain ⟨gamma, hstart, hend, hsmooth, hgeo, hunit, hdist⟩ :=
    DifferentialGeometry.Geometry.exists_unitSpeed_minimizing_geodesic_of_complete
      (S.metric t) (S.complete t ht) p y hpne
  change gamma L = y at hend
  change ∀ u ∈ Icc 0 L, ∀ v ∈ Icc 0 L,
    (riemannianEDistOf (S.metric t) (gamma u) (gamma v)).toReal = |u - v| at hdist
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hcont : Continuous (fun u => metricScalarAt (S.metric t) (gamma u)) :=
    (metricScalar_smooth (S.metric t)).continuous.comp hsmooth.continuous
  obtain ⟨s, hs, hscalar, htail⟩ := hcont.continuousOn.exists_eq_and_forall_gt hL
    (show metricScalarAt (S.metric t) (gamma 0) ≤ B by simpa only [hstart] using hp)
    (show B < metricScalarAt (S.metric t) (gamma L) by rw [hend]; exact (le_max_left B C).trans_lt hy)
  refine ⟨gamma, s, hs, hstart, hend, hsmooth, hgeo, hunit, hdist, hscalar, htail, ?_⟩
  by_contra hnot
  have hd : (riemannianEDistOf (S.metric t) (gamma s) y).toReal ≤ r := by
    rw [← hend, hdist s ⟨hs.1, hs.2.le⟩ L ⟨hL, le_rfl⟩,
      abs_of_nonpos (sub_nonpos.mpr hs.2.le)]
    linarith
  have hmem : y ∈ riemannianClosedBallOf (S.metric t) (gamma s) r :=
    (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top _ _ _) hr.le).mpr hd
  have hb := hball S t ht htaut ht1 (gamma s) hscalar.le y hmem
  exact (not_lt_of_ge hb) ((le_max_right B C).trans_lt hy)

theorem exists_standard_scalar_level_sequence_of_bounded_anchor
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point target : ℕ → E3)
    {tau A B : ℝ} (htau : 0 < tau) (hAB : A ≤ B)
    (htime : ∀ i, time i ∈ (S i).domain ∧ tau ≤ time i ∧ time i < 1)
    (hbase : ∀ i, metricScalarAt ((S i).metric (time i)) (point i) ≤ A)
    (hblow : Tendsto (fun i => metricScalarAt ((S i).metric (time i)) (target i)) atTop atTop) :
    ∃ (k : ℕ → ℕ) (q : ℕ → E3) (r : ℝ), StrictMono k ∧ 0 < r ∧
      (∀ i, metricScalarAt ((S (k i)).metric (time (k i))) (q i) = B) ∧
      (∀ i, r < (riemannianEDistOf ((S (k i)).metric (time (k i))) (q i) (target (k i))).toReal ∧
        (riemannianEDistOf ((S (k i)).metric (time (k i))) (q i) (target (k i))).toReal ≤
          (riemannianEDistOf ((S (k i)).metric (time (k i))) (point (k i)) (target (k i))).toReal) ∧
      Tendsto (fun i => metricScalarAt ((S (k i)).metric (time (k i))) (target (k i))) atTop atTop := by
  obtain ⟨C, r, _hC, hr, hgeo⟩ := exists_standard_high_scalar_geodesic_tail htau B
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hblow.eventually_gt_atTop C)
  let k : ℕ → ℕ := fun i => i + N
  have hk : StrictMono k := strictMono_id.add_const N
  have hchoose (i : ℕ) := hgeo (S (k i)) (time (k i)) (htime (k i)).1
    (htime (k i)).2.1 (htime (k i)).2.2 (point (k i)) (target (k i))
    ((hbase (k i)).trans hAB) (hN (k i) (by dsimp [k]; omega))
  choose gamma s hs hstart hend hsmooth hgeodesic hunit hdist hscalar htail hremain using hchoose
  refine ⟨k, fun i => gamma i (s i), r, hk, hr, hscalar, ?_, hblow.comp hk.tendsto_atTop⟩
  intro i
  let L := (riemannianEDistOf ((S (k i)).metric (time (k i))) (point (k i)) (target (k i))).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hd : (riemannianEDistOf ((S (k i)).metric (time (k i)))
      (gamma i (s i)) (target (k i))).toReal = L - s i := by
    rw [← hend i, hdist i (s i) ⟨(hs i).1, (hs i).2.le⟩ L ⟨hL, le_rfl⟩,
      abs_of_nonpos (sub_nonpos.mpr (hs i).2.le)]
    ring
  rw [hd]
  exact ⟨hremain i, by linarith [(hs i).1]⟩

theorem exists_standard_scalar_level_radius_escape
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point target : ℕ → E3)
    {tau A B D : ℝ} (htau : 0 < tau) (hAB : A ≤ B) (hD : 0 ≤ D)
    (htime : ∀ i, time i ∈ (S i).domain ∧ tau ≤ time i ∧ time i < 1)
    (hbase : ∀ i, metricScalarAt ((S i).metric (time i)) (point i) ≤ A)
    (hdist : ∀ i, (riemannianEDistOf ((S i).metric (time i)) (point i) (target i)).toReal ≤ D)
    (hblow : Tendsto (fun i => metricScalarAt ((S i).metric (time i)) (target i)) atTop atTop) :
    ∃ (ind : ℕ → ℕ) (q y : ℕ → E3) (R : ℝ), StrictMono ind ∧ 0 < R ∧
      (∀ i, metricScalarAt ((S (ind i)).metric (time (ind i))) (q i) = B) ∧
      (∀ r : ℝ, 0 < r → r < R → ∃ C : ℝ,
        ∀ᶠ i in atTop, ∀ z ∈ riemannianClosedBallOf ((S (ind i)).metric (time (ind i))) (q i) r,
          metricScalarAt ((S (ind i)).metric (time (ind i))) z ≤ C) ∧
      Tendsto (fun i => (riemannianEDistOf ((S (ind i)).metric (time (ind i))) (q i) (y i)).toReal)
        atTop (𝓝 R) ∧
      Tendsto (fun i => metricScalarAt ((S (ind i)).metric (time (ind i))) (y i)) atTop atTop := by
  obtain ⟨k, q, r, hk, _hr, hq, htail, hblowk⟩ :=
    exists_standard_scalar_level_sequence_of_bounded_anchor S time point target htau hAB htime hbase hblow
  have hfail : ∃ rho : ℝ, 0 < rho ∧ ¬ ∃ C : ℝ,
      ∀ᶠ i in atTop, ∀ z ∈ riemannianBallOf ((S (k i)).metric (time (k i))) (q i) rho,
        metricScalarAt ((S (k i)).metric (time (k i))) z ≤ C := by
    refine ⟨D + 1, by linarith, ?_⟩
    rintro ⟨C, hC⟩
    obtain ⟨i, hi, hiC⟩ := (hC.and (hblowk.eventually_gt_atTop C)).exists
    have hclose : target (k i) ∈ riemannianBallOf ((S (k i)).metric (time (k i))) (q i) (D + 1) := by
      apply (ENNReal.lt_ofReal_iff_toReal_lt (riemannianEDistOf_ne_top _ _ _)).mpr
      exact ((htail i).2.trans (hdist (k i))).trans_lt (lt_add_one D)
    exact (not_lt_of_ge (hi _ hclose)) hiC
  obtain ⟨R, j, hR, hj, hinner, y, hdisty, hblowy⟩ :=
    exists_standard_terminal_radius_escape (S ∘ k) (time ∘ k) q htau
      (fun i => htime (k i)) (fun i => (hq i).le) hfail
  refine ⟨k ∘ j, q ∘ j, y, R, hk.comp hj, hR, fun i => hq (j i), ?_, hdisty, hblowy⟩
  intro rho hrho hrhoR
  obtain ⟨C, hC⟩ := hinner rho hrho hrhoR
  exact ⟨C, hj.tendsto_atTop.eventually hC⟩

end DifferentialGeometry.PDE.RicciFlow
