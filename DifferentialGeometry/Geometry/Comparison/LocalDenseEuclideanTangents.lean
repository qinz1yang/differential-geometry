import DifferentialGeometry.Geometry.Comparison.LocalPairedQualities
import DifferentialGeometry.Geometry.Comparison.IntrinsicPacketDirections
import DifferentialGeometry.Geometry.Comparison.EuclideanTangentFrame
import DifferentialGeometry.Geometry.Comparison.DirectionAngleSum
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalTangentGeometry
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalLocalCompactness
import DifferentialGeometry.Geometry.Metric.CompactAngularFrame
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false

open Set Metric Real
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_dense_euclidean_tangents_of_intrinsic_eight_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hdim : dimH (ball p (8 * R)) ≤ n)
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω) :
    ∃ m : ℕ, m ≤ n ∧ dimH (closedBall p R) = m ∧
      (∀ V : Set X, IsOpen V → V.Nonempty → V ⊆ ball p (R / 2) → dimH V = m) ∧
      (∀ (q : X) (hq : q ∈ ball p (R / 2)),
        letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
          (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
          (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
        dimH (univ : Set (TangentCone q)) = m) ∧
      ∃ S : Set (ball p (R / 2)), IsGδ S ∧ Dense S ∧
        ∀ q ∈ S,
          letI : HasAnglesAt q.val := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
            (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
            (by change dist q.val p < 8 * R; have hh : dist q.val p < R / 2 := q.property; linarith)
          ∃ e : TangentCone q.val ≃ᵢ EuclideanSpace ℝ (Fin m),
            e EuclideanCone.tip = 0 := by
  classical
  obtain ⟨m, hmn, hclosed, hopen, htangent, S, hGS, hDS, hpackets⟩ :=
    exists_local_rank_dense_paired_qualities_of_intrinsic_eight_comparison_and_dimH
      hcurves p hR hdim hlocal
  refine ⟨m, hmn, hclosed, hopen, htangent, S, hGS, hDS, ?_⟩
  intro q hqS
  have hq8 : q.val ∈ ball p (8 * R) := by
    change dist q.val p < 8 * R
    have hh : dist q.val p < R / 2 := q.property
    linarith
  let : HasAnglesAt q.val := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq8
  let : LocallyCompactSpace (ball p (8 * R)) :=
    locallyCompactSpace_ball_of_intrinsic_local_comparison_and_dimH hcurves p
      (by positivity : 0 < 8 * R) hdim hlocal
  have hdim' : dimH (ball p (8 * R)) ≤ (n + 1 : ℕ) :=
    hdim.trans (by exact_mod_cast Nat.le_succ n)
  obtain ⟨hcpt, hproper, hcompT, hsegments, _⟩ :=
    tangent_geometry_and_blowup_of_intrinsic_eight_comparison_and_dimH
      hcurves p hR (by omega : 1 ≤ n + 1) hdim' hlocal hq8
  let : CompactSpace (SpaceOfDirections q.val) := hcpt
  let : ProperSpace (TangentCone q.val) := hproper
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hεsmall (k : ℕ) : ε k < Real.pi / 2 := by
    have hle : ε k ≤ 1 := by
      dsimp [ε]
      exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hpi : 1 < Real.pi / 2 := by
      simpa only [Real.sin_pi_div_two] using Real.sin_lt Real.pi_div_two_pos
    exact hle.trans_lt hpi
  have harrays (k : ℕ) : ∃ A : (Fin m × Bool) → SpaceOfDirections q.val,
      (∀ i, Real.pi - ε k < dist (A (i, true)) (A (i, false))) ∧
      ∀ i j, i ≠ j → ∀ s t : Bool,
        Real.pi / 2 - ε k < dist (A (i, s)) (A (j, t)) := by
    obtain ⟨a, b, hab⟩ := hpackets q hqS (ε k) (hεpos k)
    have habX : PairedComparisonPacket (ε k) {q.val}
        (fun i => (a i).val) (fun i => (b i).val) := by
      constructor
      · intro z hz i
        obtain rfl := mem_singleton_iff.mp hz
        exact hab.opposite q (mem_singleton q) i
      · intro z hz i j hij u hu v hv
        obtain rfl := mem_singleton_iff.mp hz
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact hab.cross q (mem_singleton q) i j hij (a i) (by simp) (a j) (by simp)
        · exact hab.cross q (mem_singleton q) i j hij (a i) (by simp) (b j) (by simp)
        · exact hab.cross q (mem_singleton q) i j hij (b i) (by simp) (a j) (by simp)
        · exact hab.cross q (mem_singleton q) i j hij (b i) (by simp) (b j) (by simp)
    have haR (i : Fin m) : (a i).val ∈ ball p R :=
      (ball_subset_ball (by linarith : R / 2 ≤ R)) (a i).property
    have hbR (i : Fin m) : (b i).val ∈ ball p R :=
      (ball_subset_ball (by linarith : R / 2 ≤ R)) (b i).property
    obtain ⟨σ, _, _, hopp, hcross⟩ :=
      habX.exists_directions_of_intrinsic_eight_comparison hcurves p hR hlocal
        q.property haR hbR (hεsmall k)
    exact ⟨fun v => (σ v).direction, hopp, hcross⟩
  choose A hopp hcross using harrays
  obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ :=
    (exists_local_fourPointComparison_intrinsicBall_iff hcurves p
      (by positivity : 0 < 8 * R) ⟨q.val, hq8⟩).mp (hlocal ⟨q.val, hq8⟩)
  have hthree := SpaceOfDirections.dist_add_dist_add_dist_le_two_pi_of_local_fourPointComparison
    (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  obtain ⟨φ, _, v, _, hvopp, hvcross⟩ := exists_subsequence_antipodal_orthogonal_frame
    SpaceOfDirections.dist_le_pi hthree A tendsto_one_div_add_atTop_nhds_zero_nat
    (Filter.Eventually.of_forall (fun k i => (hopp k i).le))
    (Filter.Eventually.of_forall (fun k i j hij s t => (hcross k i j hij s t).le))
  exact exists_pointed_euclidean_tangent_of_orthogonal_frame q.val hcompT hsegments
    (htangent q.val q.property).le v hvopp (fun i j hij => hvcross i j hij true true)

end DifferentialGeometry.Geometry.Comparison.Toponogov
