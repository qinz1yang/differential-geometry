import DifferentialGeometry.Geometry.Comparison.PairedPacketPerturbation
import DifferentialGeometry.Geometry.Comparison.FourPoint
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteConfiguration

set_option autoImplicit false

open Set Metric Filter
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v

variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, CompleteSpace (X i)]
  {Y : Type v} [MetricSpace Y] {ι : Type*} [Finite ι]

theorem PointedGHConverges.exists_uniform_lifted_packet
    {p : ∀ i, X i} {x : Y} (hconv : PointedGHConverges p x)
    (hcompare : ∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, fourPointComparison 1 (ball (p i) R))
    (c : Option (ι × Bool) → Y) (hc : Function.Injective c)
    (hq : dist (c none) x < 1 / 4) {δ : ℝ} (hδ : 0 < δ)
    (hpacket : PairedComparisonPacket (δ / 2) {c none}
      (fun j => c (some (j, true))) (fun j => c (some (j, false)))) :
    ∃ a A r R : ℝ, 0 < a ∧ a ≤ A ∧ 0 < r ∧ r < 1 / 4 ∧ 2 < R ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
        ∃ ε : ℝ, 0 < ε ∧ ε < η ∧
        ∃ f : PointedBallApprox (p i) x R ε,
        ∃ z : Option (ι × Bool) → BallCarrier (p i) R,
          Function.Injective z ∧
          (∀ j, dist (f.toFun (z j)) (c j) < η) ∧
          (∀ j k, |dist (z j).val (z k).val - dist (c j) (c k)| < η) ∧
          dist (z none).val (p i) < 1 / 2 ∧
          (∀ j, (z j).val ∈ ball (p i) R) ∧
          ball (z none).val (2 * r) ⊆ ball (p i) R ∧
          fourPointComparison 1 (ball (p i) R) ∧
          PairedComparisonPacket δ (ball (z none).val (2 * r))
            (fun j => (z (some (j, true))).val) (fun j => (z (some (j, false))).val) ∧
          (∀ w ∈ ball (z none).val (2 * r), ∀ j,
            dist w (z (some j)).val ∈ Icc a A) ∧
          IsComplete (closedBall (z none).val r) := by
  classical
  have hne (j : ι × Bool) : c none ≠ c (some j) := by
    intro hj
    have hh := hc hj
    cases hh
  obtain ⟨a, A, ξ, ha, haA, hξ, hstable⟩ :=
    hpacket.exists_metric_perturbation_bounds (fun j => c (some j)) hδ hne
  obtain ⟨M₀, hM₀⟩ := ((finite_range c).image (fun y => dist y x)).bddAbove
  let M := max 1 M₀
  let R := M + 2
  have hM : 1 ≤ M := le_max_left _ _
  have hR : 2 < R := by dsimp [R]; linarith
  have hbound (j) : dist (c j) x ≤ M :=
    (hM₀ ⟨c j, ⟨j, rfl⟩, rfl⟩).trans (le_max_right _ _)
  let r := min (1 / 8) (ξ / 8)
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hrquarter : r < 1 / 4 := (min_le_left _ _).trans_lt (by norm_num)
  have hrξ : r ≤ ξ / 8 := min_le_right _ _
  refine ⟨a, A, r, R, ha, haA, hr, hrquarter, hR, ?_⟩
  intro η hη
  have hsep : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ j k, j ≠ k → 3 * ε < dist (c j) (c k) := by
    apply eventually_all.mpr
    intro j
    apply eventually_all.mpr
    intro k
    by_cases hjk : j = k
    · exact Eventually.of_forall (fun _ hh => (hh hjk).elim)
    have hpos : 0 < dist (c j) (c k) := dist_pos.mpr (fun hh => hjk (hc hh))
    have ht : Tendsto (fun ε : ℝ => 3 * ε) (𝓝[>] 0) (𝓝 0) := by
      have hh : Continuous (fun ε : ℝ => 3 * ε) := by fun_prop
      simpa using hh.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    exact (ht.eventually (gt_mem_nhds hpos)).mono (fun _ hh _ => hh)
  have hcap : 0 < min (1 / 16) (min (ξ / 16) (η / 4)) :=
    lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (min (1 / 16) (min (ξ / 16) (η / 4))) :=
    Ioo_mem_nhdsGT hcap
  obtain ⟨ε, hε, hεsep⟩ := (hsmall.and hsep).exists
  have hεsixteen : ε < 1 / 16 := hε.2.trans_le (min_le_left _ _)
  have hεξ : ε < ξ / 16 :=
    hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεη : ε < η / 4 :=
    hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  filter_upwards [hconv.eventually_approx hε.1 (show ε < R by linarith),
    hcompare R (by linarith)] with i hi hcomp
  obtain ⟨f⟩ := hi
  obtain ⟨z, hz, hzf, hzr, hzR, hzd⟩ :=
    f.exists_injective_lift_configuration hM (by linarith) c hbound hεsep
  have hqnear : dist (z none).val (p i) < 1 / 2 := by linarith [hzr none]
  have hball : ball (z none).val (2 * r) ⊆ ball (p i) R := by
    intro w hw
    change dist w (p i) < R
    have hw' : dist w (z none).val < 2 * r := hw
    linarith [dist_triangle w (z none).val (p i)]
  have hlocal (w : X i) (hw : w ∈ ball (z none).val (2 * r)) :
      PairedComparisonPacket δ {w}
        (fun j => (z (some (j, true))).val) (fun j => (z (some (j, false))).val) ∧
        ∀ j, dist w (z (some j)).val ∈ Icc a A := by
    apply hstable w (fun j => (z (some j)).val)
    · intro j
      have ht := abs_sub_le (dist w (z (some j)).val)
        (dist (z none).val (z (some j)).val) (dist (c none) (c (some j)))
      have hd := abs_dist_sub_le w (z none).val (z (some j)).val
      have hw' : dist w (z none).val < 2 * r := hw
      linarith [hzd none (some j)]
    · intro j k
      exact (hzd (some j) (some k)).trans (by linarith)
  refine ⟨ε, hε.1, by linarith, f, z, hz,
    (fun j => (hzf j).trans (by linarith)),
    (fun j k => (hzd j k).trans (by linarith)), hqnear,
    (fun j => (hzr j).trans (hzR j)), hball, hcomp, ?_,
    (fun w hw => (hlocal w hw).2), isClosed_closedBall.isComplete⟩
  constructor
  · intro w hw j
    exact (hlocal w hw).1.opposite w (by simp) j
  · intro w hw j k hjk u hu v hv
    exact (hlocal w hw).1.cross w (by simp) j k hjk u hu v hv

end GC.MetricGeometry
