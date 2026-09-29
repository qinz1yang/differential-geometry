import DifferentialGeometry.Geometry.Flow.RicciFlow.Stability.Local
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry (SmoothRiemannianMetric euclideanMetric)
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry (euclideanMetric_ricciTensor
  euclideanMetric_metricRm04At_eq_zero)
open DifferentialGeometry.Geometry.Metric (metricDerivNorm_scaleMetric_self)
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

def flatBallRadius (i : ℕ) : ℝ := (i : ℝ) + 1

theorem flatBallRadius_pos (i : ℕ) : 0 < flatBallRadius i := by
  simp only [flatBallRadius]
  positivity

theorem tendsto_flatBallRadius_atTop : Tendsto flatBallRadius atTop atTop :=
  tendsto_atTop_mono (fun i => by simp only [flatBallRadius]; simp)
    tendsto_natCast_atTop_atTop

def flatBallTime (_ : ℕ) : ℝ := 1 / 2

theorem flatBallTime_pos (i : ℕ) : 0 < flatBallTime i := by
  norm_num [flatBallTime]

theorem flatBallTime_le_half (i : ℕ) : flatBallTime i ≤ 1 / 2 := le_rfl

def flatBallInterval (i : ℕ) : RealTimeInterval :=
  RealTimeInterval.closed (0 : ℝ) (flatBallTime i) (le_of_lt (flatBallTime_pos i))

noncomputable def flatEuclideanSolution (D : RealTimeInterval) :
    SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := (EuclideanSpace ℝ (Fin 3))) D :=
  SolutionOn.const (euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))) D

theorem isSolutionOn_flatEuclideanSolution (D : RealTimeInterval) :
    IsSolutionOn (flatEuclideanSolution D) :=
  isSolutionOn_const_of_ricciTensor_eq_zero (euclideanMetric (E := (EuclideanSpace ℝ (Fin 3))))
    (fun x v w => euclideanMetric_ricciTensor x v w) D

noncomputable def flatBallMetric (L : ℝ) : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ↥(ModelBall L) :=
  (euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall L)

noncomputable def flatBallSolution (i : ℕ) :
    SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i))) (flatBallInterval i) :=
  SolutionOn.const (flatBallMetric (flatBallRadius i)) (flatBallInterval i)

@[simp] theorem flatBallSolution_base_metric (i : ℕ) (u : ℝ) :
    (flatBallSolution i).base.metric u = flatBallMetric (flatBallRadius i) :=
  rfl

theorem ricciTensor_flatBallMetric_eq_zero (L : ℝ) (x : ↥(ModelBall L))
    (v w : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) x) :
    ricciTensor (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall L)) (flatBallMetric L) x v w = 0 := by
  rw [flatBallMetric, DifferentialGeometry.CheegerGromovCompactness.ricciTensor_restrictOpen]
  exact euclideanMetric_ricciTensor (x : (EuclideanSpace ℝ (Fin 3)))
    (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (Subtype.val : ↥(ModelBall L) → (EuclideanSpace ℝ (Fin 3))) x v)
    (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (Subtype.val : ↥(ModelBall L) → (EuclideanSpace ℝ (Fin 3))) x w)

theorem isSolutionOn_flatBallSolution (i : ℕ) : IsSolutionOn (flatBallSolution i) :=
  isSolutionOn_const_of_ricciTensor_eq_zero (flatBallMetric (flatBallRadius i))
    (fun x v w => ricciTensor_flatBallMetric_eq_zero (flatBallRadius i) x v w)
    (flatBallInterval i)

theorem metricRm04At_flatBallMetric_eq_zero (L : ℝ) (x : ↥(ModelBall L)) :
    metricRm04At (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall L)) (flatBallMetric L) x = 0 := by
  rw [flatBallMetric]
  ext v
  have hv : v = vec4 (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (v 0) (v 1) (v 2) (v 3) := by
    ext i
    fin_cases i <;> rfl
  rw [hv, ← metricRm04StandardAt_apply, metricRm04StandardAt_restrictOpen,
    metricRm04StandardAt_apply, euclideanMetric_metricRm04At_eq_zero]
  simp

theorem curvatureNormSq_flatBallSolution_le (i : ℕ) (x : ↥(ModelBall (flatBallRadius i))) :
    curvatureNormSq ((flatBallSolution i).base.metric (flatBallTime i)) x
      (metricRm04At (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i)))
        ((flatBallSolution i).base.metric (flatBallTime i)) x) ≤ (1 : ℝ) ^ 2 := by
  have hz : Tensor0SBundle.normSq0S (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))))
      (M := ↥(ModelBall (flatBallRadius i))) (flatBallMetric (flatBallRadius i)) x 4
      (0 : Tensor0SBundle.Tensor0SSpace 4 (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) x) = 0 :=
    (Tensor0SBundle.normSq0S_eq_zero_iff _ _ _ _).mpr rfl
  rw [flatBallSolution_base_metric, metricRm04At_flatBallMetric_eq_zero, curvatureNormSq, hz]
  norm_num

theorem metricDerivNormSupOn_flatBallSolution_eq_zero (i : ℕ) (A : Set (EuclideanSpace ℝ (Fin 3))) (m : ℕ)
    (u : ℝ) :
    metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i)))
      (Subtype.val ⁻¹' A) m ((flatBallSolution i).base.metric u)
      (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i)) = 0 := by
  rw [flatBallSolution_base_metric]
  exact metricDerivNormSupOn_self (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i)))
    (Subtype.val ⁻¹' A) m _ _

theorem nonempty_flatBall_localStability_supSet (i : ℕ) (A : Set (EuclideanSpace ℝ (Fin 3))) (m : ℕ) :
    ({r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (flatBallTime i),
      metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i)))
        (Subtype.val ⁻¹' A) m ((flatBallSolution i).base.metric u)
        (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i)) = r}).Nonempty :=
  ⟨0, 0, ⟨le_rfl, (flatBallTime_pos i).le⟩,
    metricDerivNormSupOn_flatBallSolution_eq_zero i A m 0⟩

theorem flatBall_metricDerivNormSupOn_tendsto_zero :
    ∀ A : Set (EuclideanSpace ℝ (Fin 3)), IsCompact A → ∀ p : ℕ,
      Tendsto (fun i : ℕ => metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))))
          (M := ↥(ModelBall (flatBallRadius i))) (Subtype.val ⁻¹' A) p
          ((flatBallSolution i).base.metric 0)
          ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i)))
          ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i))))
        atTop (𝓝 0) := by
  intro A _ p
  have h : (fun i : ℕ => metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))))
        (M := ↥(ModelBall (flatBallRadius i))) (Subtype.val ⁻¹' A) p
        ((flatBallSolution i).base.metric 0)
        ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i)))
        ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i))))
      = fun _ => (0 : ℝ) := by
    funext i
    simpa only [flatBallMetric] using metricDerivNormSupOn_flatBallSolution_eq_zero i A p 0
  rw [h]
  exact tendsto_const_nhds

theorem flatBall_localStability_tendsto :
    ∀ A : Set (EuclideanSpace ℝ (Fin 3)), IsCompact A → ∀ m : ℕ, 4 ≤ m →
      Tendsto (fun i : ℕ => sSup {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (flatBallTime i),
          metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i)))
            (Subtype.val ⁻¹' A) m ((flatBallSolution i).base.metric u)
            ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i)))
            ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i))) = r})
        atTop (𝓝 0) := by
  intro A _ m _
  have h : (fun i : ℕ => sSup {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (flatBallTime i),
        metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i)))
          (Subtype.val ⁻¹' A) m ((flatBallSolution i).base.metric u)
          ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i)))
          ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i))) = r})
      = fun _ => (0 : ℝ) := by
    funext i
    have hset : {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (flatBallTime i),
        metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i)))
          (Subtype.val ⁻¹' A) m ((flatBallSolution i).base.metric u)
          ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i)))
          ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i))) = r}
        = {0} := by
      ext r
      constructor
      · rintro ⟨u, _hu, hr⟩
        rw [← hr, Set.mem_singleton_iff]
        simpa only [flatBallMetric] using metricDerivNormSupOn_flatBallSolution_eq_zero i A m u
      · intro hr
        rw [Set.mem_singleton_iff] at hr
        subst hr
        exact ⟨0, ⟨le_rfl, (flatBallTime_pos i).le⟩,
          by simpa only [flatBallMetric] using
            metricDerivNormSupOn_flatBallSolution_eq_zero i A m 0⟩
    rw [hset, csSup_singleton]
  rw [h]
  exact tendsto_const_nhds

def flatBallRescale (i : ℕ) : ℝ := 1 + 1 / ((i : ℝ) + 1)

theorem flatBallRescale_pos (i : ℕ) : 0 < flatBallRescale i := by
  simp only [flatBallRescale]
  positivity

theorem flatBallRescale_sub_one (i : ℕ) : flatBallRescale i - 1 = 1 / ((i : ℝ) + 1) := by
  simp only [flatBallRescale]
  ring

theorem flatBallRescale_ne_one (i : ℕ) : flatBallRescale i ≠ 1 := by
  have hpos : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
  intro h
  simp only [flatBallRescale] at h
  linarith

theorem finrank_threeSpace : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
  rw [finrank_euclideanSpace_fin]

theorem finrank_threeSpace_pos : 0 < (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) := by
  rw [finrank_threeSpace]
  norm_num

theorem tendsto_flatBallRescale_abs_sub_one :
    Tendsto (fun i : ℕ => |flatBallRescale i - 1|) atTop (𝓝 0) := by
  have h : (fun i : ℕ => |flatBallRescale i - 1|)
      = fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1) := by
    funext i
    have hp : 0 < (1 : ℝ) / ((i : ℝ) + 1) := by positivity
    rw [flatBallRescale_sub_one, abs_of_pos hp]
  rw [h]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_flatBallScaledFactor :
    Tendsto (fun i : ℕ => |flatBallRescale i - 1| * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))
      atTop (𝓝 0) := by
  have h : Tendsto (fun _ : ℕ => Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) atTop
      (𝓝 (Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))) := tendsto_const_nhds
  simpa using tendsto_flatBallRescale_abs_sub_one.mul h

noncomputable def flatBallScaledMetric (L : ℝ) (c : ℝ) (hc : 0 < c) :
    SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ↥(ModelBall L) :=
  scaleMetric c hc (flatBallMetric L)

theorem ricciTensor_flatBallScaledMetric_eq_zero (L : ℝ) (c : ℝ) (hc : 0 < c)
    (x : ↥(ModelBall L)) (v w : TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) x) :
    ricciTensor (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall L)) (flatBallScaledMetric L c hc) x v w
      = 0 := by
  rw [flatBallScaledMetric, ricciTensor_scaleMetric]
  exact ricciTensor_flatBallMetric_eq_zero L x v w

noncomputable def flatBallScaledSolution (i : ℕ) :
    SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i))) (flatBallInterval i) :=
  SolutionOn.const (flatBallScaledMetric (flatBallRadius i) (flatBallRescale i)
    (flatBallRescale_pos i)) (flatBallInterval i)

@[simp] theorem flatBallScaledSolution_base_metric (i : ℕ) (u : ℝ) :
    (flatBallScaledSolution i).base.metric u
      = flatBallScaledMetric (flatBallRadius i) (flatBallRescale i) (flatBallRescale_pos i) :=
  rfl

theorem isSolutionOn_flatBallScaledSolution (i : ℕ) : IsSolutionOn (flatBallScaledSolution i) :=
  isSolutionOn_const_of_ricciTensor_eq_zero
    (flatBallScaledMetric (flatBallRadius i) (flatBallRescale i) (flatBallRescale_pos i))
    (fun x v w => ricciTensor_flatBallScaledMetric_eq_zero (flatBallRadius i) (flatBallRescale i)
      (flatBallRescale_pos i) x v w) (flatBallInterval i)

theorem metricRm04At_flatBallScaledMetric_eq_zero (L : ℝ) (c : ℝ) (hc : 0 < c)
    (x : ↥(ModelBall L)) :
    metricRm04At (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall L)) (flatBallScaledMetric L c hc) x = 0 := by
  rw [flatBallScaledMetric, ← metricRm04_apply, metricRm_scale, metricRm04_apply,
    metricRm04At_flatBallMetric_eq_zero, smul_zero]

theorem curvatureNormSq_flatBallScaledSolution_le (i : ℕ)
    (x : ↥(ModelBall (flatBallRadius i))) :
    curvatureNormSq ((flatBallScaledSolution i).base.metric (flatBallTime i)) x
      (metricRm04At (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i)))
        ((flatBallScaledSolution i).base.metric (flatBallTime i)) x) ≤ (1 : ℝ) ^ 2 := by
  have hz : Tensor0SBundle.normSq0S (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))))
      (M := ↥(ModelBall (flatBallRadius i)))
      (flatBallScaledMetric (flatBallRadius i) (flatBallRescale i) (flatBallRescale_pos i)) x 4
      (0 : Tensor0SBundle.Tensor0SSpace 4 (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) x) = 0 :=
    (Tensor0SBundle.normSq0S_eq_zero_iff _ _ _ _).mpr rfl
  rw [flatBallScaledSolution_base_metric, metricRm04At_flatBallScaledMetric_eq_zero,
    curvatureNormSq, hz]
  norm_num

theorem metricDerivNorm_flatBallScaledMetric_le (L : ℝ) (c : ℝ) (hc : 0 < c) (a : ℕ)
    (x : ↥(ModelBall L)) :
    metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall L)) a
        (flatBallScaledMetric L c hc) (flatBallMetric L) (flatBallMetric L) x
      ≤ |c - 1| * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := by
  rw [flatBallScaledMetric, metricDerivNorm_scaleMetric_self]
  split_ifs with h
  · exact le_rfl
  · positivity

theorem metricDerivNormSupOn_flatBallScaledMetric_le (L : ℝ) (c : ℝ) (hc : 0 < c)
    (K : Set ↥(ModelBall L)) (m : ℕ) :
    metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall L)) K m
      (flatBallScaledMetric L c hc) (flatBallMetric L) (flatBallMetric L)
      ≤ |c - 1| * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := by
  refine Real.sSup_le (fun r hr => ?_) (by positivity)
  obtain ⟨a, _ha, x, _hx, rfl⟩ := hr
  exact metricDerivNorm_flatBallScaledMetric_le L c hc a x

theorem metricDerivNormSupOn_flatBallScaledMetric_eq (L : ℝ) (c : ℝ) (hc : 0 < c)
    (K : Set ↥(ModelBall L)) (hK : K.Nonempty) (m : ℕ) :
    metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall L)) K m
      (flatBallScaledMetric L c hc) (flatBallMetric L) (flatBallMetric L)
      = |c - 1| * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := by
  refine le_antisymm (metricDerivNormSupOn_flatBallScaledMetric_le L c hc K m) ?_
  obtain ⟨x, hx⟩ := hK
  have hbdd : BddAbove {r : ℝ | ∃ a : ℕ, a ≤ m ∧ ∃ y : ↥(ModelBall L), y ∈ K ∧
      metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall L)) a
        (flatBallScaledMetric L c hc) (flatBallMetric L) (flatBallMetric L) y = r} :=
    ⟨|c - 1| * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))), fun r hr => by
      obtain ⟨a, _ha, y, _hy, rfl⟩ := hr
      exact metricDerivNorm_flatBallScaledMetric_le L c hc a y⟩
  have hmem : metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall L)) 0
      (flatBallScaledMetric L c hc) (flatBallMetric L) (flatBallMetric L) x
      ≤ metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall L)) K m
        (flatBallScaledMetric L c hc) (flatBallMetric L) (flatBallMetric L) :=
    le_csSup hbdd ⟨0, Nat.zero_le m, x, hx, rfl⟩
  have hzero : metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall L)) 0
      (flatBallScaledMetric L c hc) (flatBallMetric L) (flatBallMetric L) x
      = |c - 1| * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := by
    rw [flatBallScaledMetric, metricDerivNorm_scaleMetric_self]
    simp
  rw [hzero] at hmem
  exact hmem

theorem metricDerivNormSupOn_flatBallScaledMetric_pos (i m : ℕ)
    {K : Set ↥(ModelBall (flatBallRadius i))} (hK : K.Nonempty) :
    0 < metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i))) K m
      (flatBallScaledMetric (flatBallRadius i) (flatBallRescale i) (flatBallRescale_pos i))
      (flatBallMetric (flatBallRadius i)) (flatBallMetric (flatBallRadius i)) := by
  rw [metricDerivNormSupOn_flatBallScaledMetric_eq (flatBallRadius i) (flatBallRescale i)
    (flatBallRescale_pos i) K hK m]
  exact mul_pos (abs_pos.mpr (sub_ne_zero.mpr (flatBallRescale_ne_one i)))
    (Real.sqrt_pos.mpr finrank_threeSpace_pos)

theorem flatBallScaled_metricDerivNormSupOn_tendsto_zero :
    ∀ A : Set (EuclideanSpace ℝ (Fin 3)), IsCompact A → ∀ p : ℕ,
      Tendsto (fun i : ℕ => metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))))
          (M := ↥(ModelBall (flatBallRadius i))) (Subtype.val ⁻¹' A) p
          ((flatBallScaledSolution i).base.metric 0)
          ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i)))
          ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i))))
        atTop (𝓝 0) := by
  intro A _ p
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (h := fun i : ℕ => |flatBallRescale i - 1| * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))
    tendsto_const_nhds ?_ ?_ ?_
  · exact tendsto_flatBallScaledFactor
  · intro i
    refine Real.sSup_nonneg (fun r hr => ?_)
    obtain ⟨a, _ha, x, _hx, rfl⟩ := hr
    rw [flatBallScaledSolution_base_metric, metricDerivNorm]
    exact Real.sqrt_nonneg _
  · intro i
    simpa only [flatBallScaledSolution_base_metric, flatBallMetric] using
      metricDerivNormSupOn_flatBallScaledMetric_le (flatBallRadius i) (flatBallRescale i)
        (flatBallRescale_pos i) (Subtype.val ⁻¹' A) p

theorem flatBallScaled_localStability_tendsto :
    ∀ A : Set (EuclideanSpace ℝ (Fin 3)), IsCompact A → ∀ m : ℕ, 4 ≤ m →
      Tendsto (fun i : ℕ => sSup {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (flatBallTime i),
          metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i)))
            (Subtype.val ⁻¹' A) m ((flatBallScaledSolution i).base.metric u)
            ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i)))
            ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i))) = r})
        atTop (𝓝 0) := by
  intro A _ m _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (h := fun i : ℕ => |flatBallRescale i - 1| * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))
    tendsto_const_nhds ?_ ?_ ?_
  · exact tendsto_flatBallScaledFactor
  · intro i
    refine Real.sSup_nonneg (fun r hr => ?_)
    obtain ⟨u, _hu, rfl⟩ := hr
    refine Real.sSup_nonneg (fun s hs => ?_)
    obtain ⟨a, _ha, x, _hx, rfl⟩ := hs
    rw [flatBallScaledSolution_base_metric, metricDerivNorm]
    exact Real.sqrt_nonneg _
  · intro i
    refine Real.sSup_le (fun r hr => ?_) (by positivity)
    obtain ⟨u, _hu, rfl⟩ := hr
    simpa only [flatBallScaledSolution_base_metric, flatBallMetric] using
      metricDerivNormSupOn_flatBallScaledMetric_le (flatBallRadius i) (flatBallRescale i)
        (flatBallRescale_pos i) (Subtype.val ⁻¹' A) m

theorem flatBallScaled_localStability_sup_pos (i m : ℕ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (hA : (Subtype.val ⁻¹' A : Set ↥(ModelBall (flatBallRadius i))).Nonempty) :
    0 < sSup {r : ℝ | ∃ u ∈ Set.Icc (0 : ℝ) (flatBallTime i),
      metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (flatBallRadius i)))
        (Subtype.val ⁻¹' A) m ((flatBallScaledSolution i).base.metric u)
        ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i)))
        ((euclideanMetric (E := (EuclideanSpace ℝ (Fin 3)))).restrictOpen (ModelBall (flatBallRadius i))) = r} := by
  refine lt_of_lt_of_le (metricDerivNormSupOn_flatBallScaledMetric_pos i m hA) (le_csSup ?_ ?_)
  · refine ⟨|flatBallRescale i - 1| * Real.sqrt (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
      fun r hr => ?_⟩
    obtain ⟨u, _hu, rfl⟩ := hr
    simpa only [flatBallScaledSolution_base_metric, flatBallMetric] using
      metricDerivNormSupOn_flatBallScaledMetric_le (flatBallRadius i) (flatBallRescale i)
        (flatBallRescale_pos i) (Subtype.val ⁻¹' A) m
  · exact ⟨0, ⟨le_rfl, (flatBallTime_pos i).le⟩, by
      simp only [flatBallScaledSolution_base_metric, flatBallMetric]⟩

theorem exists_flatBall_localStability_hypotheses :
    ∃ (θ K : ℝ), 0 < θ ∧ θ < 1 ∧ 0 < K ∧
      ∃ (L : ℕ → ℝ), (∀ i, 0 < L i) ∧ Tendsto L atTop atTop ∧
        ∃ (v : ℕ → ℝ) (hv : ∀ i, 0 < v i), (∀ i, v i ≤ θ) ∧
          ∃ γ : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3)),
            ∃ ℓ : (i : ℕ) → SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
              (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i))),
              (∀ i, IsSolutionOn (ℓ i)) ∧
              (∀ i, ∀ x : ↥(ModelBall (L i)),
                curvatureNormSq ((ℓ i).base.metric (v i)) x
                  (metricRm04At (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
                    ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) ∧
              (∀ A : Set (EuclideanSpace ℝ (Fin 3)), IsCompact A → ∀ p : ℕ,
                Tendsto (fun i : ℕ => metricDerivNormSupOn (Subtype.val ⁻¹' A) p
                    ((ℓ i).base.metric 0) (γ.restrictOpen (ModelBall (L i)))
                    (γ.restrictOpen (ModelBall (L i)))) atTop (𝓝 0)) := by
  refine ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num,
    flatBallRadius, flatBallRadius_pos, tendsto_flatBallRadius_atTop,
    flatBallTime, flatBallTime_pos, flatBallTime_le_half,
    euclideanMetric (E := (EuclideanSpace ℝ (Fin 3))), flatBallSolution, ?_, ?_, ?_⟩
  · exact isSolutionOn_flatBallSolution
  · exact curvatureNormSq_flatBallSolution_le
  · exact flatBall_metricDerivNormSupOn_tendsto_zero

theorem exists_flatBallScaled_localStability_hypotheses :
    ∃ (θ K : ℝ), 0 < θ ∧ θ < 1 ∧ 0 < K ∧
      ∃ (L : ℕ → ℝ), (∀ i, 0 < L i) ∧ Tendsto L atTop atTop ∧
        ∃ (v : ℕ → ℝ) (hv : ∀ i, 0 < v i), (∀ i, v i ≤ θ) ∧
          ∃ γ : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3)),
            ∃ ℓ : (i : ℕ) → SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
              (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i))),
              (∀ i, IsSolutionOn (ℓ i)) ∧
              (∀ i, ∀ x : ↥(ModelBall (L i)),
                curvatureNormSq ((ℓ i).base.metric (v i)) x
                  (metricRm04At (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
                    ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) ∧
              (∀ A : Set (EuclideanSpace ℝ (Fin 3)), IsCompact A → ∀ p : ℕ,
                Tendsto (fun i : ℕ => metricDerivNormSupOn (Subtype.val ⁻¹' A) p
                    ((ℓ i).base.metric 0) (γ.restrictOpen (ModelBall (L i)))
                    (γ.restrictOpen (ModelBall (L i)))) atTop (𝓝 0)) := by
  refine ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num,
    flatBallRadius, flatBallRadius_pos, tendsto_flatBallRadius_atTop,
    flatBallTime, flatBallTime_pos, flatBallTime_le_half,
    euclideanMetric (E := (EuclideanSpace ℝ (Fin 3))), flatBallScaledSolution, ?_, ?_, ?_⟩
  · exact isSolutionOn_flatBallScaledSolution
  · exact curvatureNormSq_flatBallScaledSolution_le
  · exact flatBallScaled_metricDerivNormSupOn_tendsto_zero

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
