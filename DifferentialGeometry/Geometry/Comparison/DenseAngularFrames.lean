import DifferentialGeometry.Geometry.Comparison.ArbitraryQualityPairedPackets
import DifferentialGeometry.Geometry.Comparison.BairePairedPacket
import DifferentialGeometry.Geometry.Comparison.PairedPacketDirections
import DifferentialGeometry.Geometry.Comparison.DirectionAngleSum
import DifferentialGeometry.Geometry.Metric.CompactAngularFrame
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalProperness
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalTangentGeometry
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_dense_isGδ_orthogonal_direction_frames_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nontrivial X]
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {n : ℕ} (hdim : dimH (univ : Set X) ≤ n)
    (hlocal : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω) :
    ∃ m : ℕ, m ≤ n ∧ dimH (univ : Set X) = m ∧
      (∀ V : Set X, IsOpen V → V.Nonempty → dimH V = m) ∧
      ∃ S : Set X, IsGδ S ∧ Dense S ∧ ∀ q ∈ S,
        letI : HasAnglesAt q := by
          obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
          exact hasAnglesAt_of_local_fourPointComparison
            (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
        ∃ v : (Fin m × Bool) → SpaceOfDirections q,
          (∀ i, dist (v (i, true)) (v (i, false)) = Real.pi) ∧
          ∀ i j, i ≠ j → ∀ s t : Bool,
            dist (v (i, s)) (v (j, t)) = Real.pi / 2 := by
  classical
  obtain ⟨m, hmn, hglobal, hopen, hpackets⟩ :=
    exists_global_rank_paired_packets_of_local_comparison_and_dimH hcurves hdim hlocal
  obtain ⟨S, hS, hSdense, hSframes⟩ := exists_dense_isGδ_all_paired_qualities
    (m := m) (by
      intro ε hε O hO hOne
      obtain ⟨q, hq, Ω, _, _, _, a, b, _, hab⟩ := hpackets ε hε O hO hOne
      exact ⟨q, hq, a, b, hab⟩)
  let : ProperSpace X := properSpace_of_local_comparison_and_dimH hcurves
    (by norm_num : (0 : ℝ) ≤ 1) hdim hlocal
  have hsegments : ∀ x y : X, ∃ σ : Icc (0 : ℝ) (dist x y) → X,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
    intro x y
    obtain ⟨f, _, hf0, hf1, hfd⟩ :=
      exists_metric_segment_of_locallyCompact_of_arbitrarily_short_curves hcurves x y
    exact exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
  refine ⟨m, hmn, hglobal, hopen, S, hS, hSdense, ?_⟩
  intro q hq
  let : HasAnglesAt q := by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
    exact hasAnglesAt_of_local_fourPointComparison
      (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  have hdim' : dimH (univ : Set X) ≤ (n + 1 : ℕ) :=
    hdim.trans (by exact_mod_cast Nat.le_succ n)
  have hgeometry := tangent_geometry_and_blowup_of_local_comparison_and_dimH
    hcurves isOpen_univ (by omega : 1 ≤ n + 1) hdim'
    (fun z _ => hlocal z) (mem_univ q)
  let : CompactSpace (SpaceOfDirections q) := hgeometry.1
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hεsmall (k : ℕ) : ε k < Real.pi / 2 := by
    have hle : ε k ≤ 1 := by
      dsimp [ε]
      exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hpi : 1 < Real.pi / 2 := by
      simpa only [Real.sin_pi_div_two] using Real.sin_lt Real.pi_div_two_pos
    exact hle.trans_lt hpi
  have harrays (k : ℕ) : ∃ A : (Fin m × Bool) → SpaceOfDirections q,
      (∀ i, Real.pi - ε k < dist (A (i, true)) (A (i, false))) ∧
      ∀ i j, i ≠ j → ∀ s t : Bool,
        Real.pi / 2 - ε k < dist (A (i, s)) (A (j, t)) := by
    obtain ⟨a, b, hab⟩ := hSframes q hq (ε k) (hεpos k)
    obtain ⟨σ, _, _, hopp, hcross⟩ :=
      hab.exists_directions_of_complete_local_comparison hsegments hlocal (hεsmall k)
    exact ⟨fun v => (σ v).direction, hopp, hcross⟩
  choose A hopp hcross using harrays
  obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
  have hthree := SpaceOfDirections.dist_add_dist_add_dist_le_two_pi_of_local_fourPointComparison
    (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  obtain ⟨φ, _, v, _, hvopp, hvcross⟩ := exists_subsequence_antipodal_orthogonal_frame
    SpaceOfDirections.dist_le_pi hthree A tendsto_one_div_add_atTop_nhds_zero_nat
    (Eventually.of_forall (fun k i => (hopp k i).le))
    (Eventually.of_forall (fun k i j hij s t => (hcross k i j hij s t).le))
  exact ⟨v, hvopp, hvcross⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
