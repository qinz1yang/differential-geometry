import DifferentialGeometry.Topology.MetricSpace.DistanceMatrixLimit
import DifferentialGeometry.Topology.MetricSpace.CountableNetLabels
import DifferentialGeometry.Geometry.Metric.Approximation.PairedNets
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence

set_option autoImplicit false
open Filter Set
open scoped Topology

namespace GC.MetricGeometry

private theorem exists_level (R η : ℝ) (hη : 0 < η) :
    ∃ m : ℕ, R < (m : ℝ) + 1 ∧ ((m : ℝ) + 1)⁻¹ < η := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max R η⁻¹)
  refine ⟨m, by linarith [le_max_left R η⁻¹], ?_⟩
  have hmη : η⁻¹ < (m : ℝ) := lt_of_le_of_lt (le_max_right R η⁻¹) hm
  rw [← one_div]
  apply (one_div_lt (by positivity : (0 : ℝ) < (m : ℝ) + 1) hη).mpr
  rw [one_div]
  linarith

universe u v
variable {L : Type u} [Countable L]
variable {X : ℕ → Type v} [∀ n, MetricSpace (X n)]

theorem exists_pointedGHConverges_of_countable_nets
    (x : ∀ n, L → X n) (o : L) (C : L → ℝ)
    (hrad : ∀ n a, dist (x n a) (x n o) ≤ C a)
    (F : ℕ → Finset L)
    (hnet : ∀ m : ℕ, ∀ᶠ n in atTop, ∀ u : X n,
      dist u (x n o) ≤ (m : ℝ) + 1 →
        ∃ a ∈ F m, dist u (x n a) ≤ ((m : ℝ) + 1)⁻¹) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ d : PseudoMetricSpace L,
      letI := d
      ProperSpace (UniformSpace.Completion L) ∧
      PointedGHConverges (fun n => x (φ n) o) (o : UniformSpace.Completion L) := by
  classical
  have hB (n : ℕ) (a b : L) : dist (x n a) (x n b) ≤ C a + C b := by
    have h := dist_triangle_right (x n a) (x n b) (x n o)
    linarith [hrad n a, hrad n b]
  obtain ⟨φ, hφ, d, hdense, hdist⟩ :=
    Metric.exists_completion_subseq_tendsto_dist x (fun a b => C a + C b) hB
  refine ⟨φ, hφ, d, ?_⟩
  let := d
  let Y := UniformSpace.Completion L
  let z : L → Y := fun a => (a : UniformSpace.Completion L)
  have htarget (m : ℕ) (y : Y) (hy : dist y (z o) < (m : ℝ) + 1) :
      ∃ a ∈ F m, dist y (z a) ≤ ((m : ℝ) + 1)⁻¹ := by
    apply Metric.exists_mem_finset_dist_le_of_denseRange z hdense (F m) (z o)
      ((m : ℝ) + 1) (((m : ℝ) + 1)⁻¹) ?_ y hy
    intro b hb
    have hball : ∀ᶠ n in atTop,
        dist (x (φ n) b) (x (φ n) o) < (m : ℝ) + 1 :=
      (hdist b o).eventually (Iio_mem_nhds hb)
    have hcover : ∀ᶠ n in atTop,
        ∃ a ∈ F m, dist (x (φ n) b) (x (φ n) a) ≤ ((m : ℝ) + 1)⁻¹ := by
      filter_upwards [hφ.tendsto_atTop.eventually (hnet m), hball] with n hn hbn
      exact hn (x (φ n) b) hbn.le
    exact Metric.exists_mem_finset_dist_le_of_tendsto (fun n => x (φ n)) z
      (F m) b (((m : ℝ) + 1)⁻¹) (fun a _ => hdist b a) hcover
  have hproper : ProperSpace Y := by
    apply Metric.properSpace_of_finite_nets_at_basepoint z (z o)
    intro R hR η hη
    obtain ⟨m, hmR, hmη⟩ := exists_level R η hη
    refine ⟨F m, fun y hy => ?_⟩
    obtain ⟨a, ha, hya⟩ := htarget m y (hy.trans hmR)
    exact ⟨a, ha, hya.trans hmη.le⟩
  refine ⟨hproper, inferInstance, ?_⟩
  intro R ε hε hεR
  obtain ⟨m, hmR, hmη⟩ := exists_level R (ε / 4) (by linarith)
  let η : ℝ := ((m : ℝ) + 1)⁻¹
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : 3 * η < ε := by dsimp [η]; linarith
  let E : Finset L := insert o (F m)
  have hmatrix : ∀ᶠ n in atTop, ∀ a ∈ E, ∀ b ∈ E,
      |dist (z a) (z b) - dist (x (φ n) a) (x (φ n) b)| < η := by
    rw [Filter.eventually_all_finset]
    intro a ha
    rw [Filter.eventually_all_finset]
    intro b hb
    have h := (hdist a b).eventually (Metric.ball_mem_nhds _ hη)
    simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using h
  filter_upwards [hφ.tendsto_atTop.eventually (hnet m), hmatrix] with n hn hmat
  refine ⟨PointedBallApprox.ofPairedNets
    (fun a : E => x (φ n) a.val) (fun a : E => z a.val)
    ⟨o, Finset.mem_insert_self o (F m)⟩ rfl rfl hη hεR hηε ?_ ?_ ?_⟩
  · intro u
    obtain ⟨a, ha, hua⟩ := hn u.val (le_trans u.property hmR.le)
    exact ⟨⟨a, Finset.mem_insert_of_mem ha⟩, hua⟩
  · intro y hy
    obtain ⟨a, ha, hya⟩ := htarget m y (by linarith)
    exact ⟨⟨a, Finset.mem_insert_of_mem ha⟩, hya⟩
  · intro a b
    exact hmat a.val a.property b.val b.property

theorem exists_pointedGHConverges_of_eventual_finite_nets (p : ∀ n, X n)
    (hnets : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N I : ℕ, ∀ n : ℕ, I ≤ n →
      ∃ S : Finset (X n), S.card ≤ N ∧
        (∀ y ∈ S, dist y (p n) ≤ R) ∧
        ∀ x : X n, dist x (p n) ≤ R → ∃ y ∈ S, dist x y ≤ η) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace Y ∧
        PointedGHConverges (fun n => p (φ n)) q := by
  obtain ⟨N, x, C, F, hbase, hrad, _, hnet⟩ :=
    Metric.exists_countable_ball_net_labels_of_eventual_nets p hnets
  let Labels := Option (Σ m : ℕ, Fin (N m + 1))
  obtain ⟨φ, hφ, d, hproper, hconv⟩ :=
    exists_pointedGHConverges_of_countable_nets x (none : Labels) C hrad F hnet
  let := d
  refine ⟨UniformSpace.Completion Labels, inferInstance,
    ((none : Labels) : UniformSpace.Completion Labels), φ, hφ, hproper, ?_⟩
  simpa only [hbase] using hconv

theorem exists_pointedGHConverges_of_uniform_finite_nets (p : ∀ n, X n)
    (hnets : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ,
      ∃ S : Finset (X n), S.card ≤ N ∧
        (∀ y ∈ S, dist y (p n) ≤ R) ∧
        ∀ x : X n, dist x (p n) ≤ R → ∃ y ∈ S, dist x y ≤ η) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace Y ∧
        PointedGHConverges (fun n => p (φ n)) q := by
  apply exists_pointedGHConverges_of_eventual_finite_nets p
  intro R hR η hη
  obtain ⟨N, hN⟩ := hnets R hR η hη
  exact ⟨N, 0, fun n _ => hN n⟩

end GC.MetricGeometry
