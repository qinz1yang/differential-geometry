/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.Axis

noncomputable section

namespace DifferentialGeometry.AxialThinCompactness

open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH)
open HyperbolicConvexity (geodFromTo geodFromTo_zero dist_geodFromTo)
open AxisGeometry (axisFoot axisFoot_mem eq_axisFoot_of_dist_le cosh_dist_normal_geod)

variable {n : ℕ}

theorem axisFoot_normal_geod (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (y : HUpper n) (hy : axisFoot ξ η hne y ≠ y) (t : ℝ) :
    axisFoot ξ η hne (geodFromTo (axisFoot ξ η hne y) y hy t) = axisFoot ξ η hne y := by
  apply Eq.symm
  apply eq_axisFoot_of_dist_le ξ η hne _ _ (axisFoot_mem ξ η hne y)
  apply (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp
  rw [cosh_dist_normal_geod ξ η hne y hy _ (axisFoot_mem ξ η hne y),
    cosh_dist_normal_geod ξ η hne y hy _ (axisFoot_mem ξ η hne _),
    dist_self, Real.cosh_zero, mul_one]
  exact le_mul_of_one_le_right (Real.cosh_pos _).le (Real.one_le_cosh _)

theorem dist_normal_axisFoot (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (y : HUpper n) (hy : axisFoot ξ η hne y ≠ y) (t : ℝ) :
    dist (geodFromTo (axisFoot ξ η hne y) y hy t)
      (axisFoot ξ η hne (geodFromTo (axisFoot ξ η hne y) y hy t)) = |t| := by
  rw [axisFoot_normal_geod]
  simpa only [geodFromTo_zero, sub_zero] using dist_geodFromTo hy t 0

end DifferentialGeometry.AxialThinCompactness

namespace DifferentialGeometry.AxisGeometry

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open HyperbolicBoundary (BoundaryH poBoundaryMulAction)
open HyperbolicAction (poMulAction po_dist_smul)
open HyperbolicConvexity (geodFromTo geodFromTo_zero dist_geodFromTo)

variable {n : ℕ}

theorem lipschitzWith_dist_axisFoot (ξ η : BoundaryH n) (hne : ξ ≠ η) :
    LipschitzWith 1 (fun x : HUpper n => dist x (axisFoot ξ η hne x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  have hx := (dist_axisFoot_le ξ η hne x _ (axisFoot_mem ξ η hne y)).trans
    (dist_triangle x y (axisFoot ξ η hne y))
  have hy := (dist_axisFoot_le ξ η hne y _ (axisFoot_mem ξ η hne x)).trans
    (dist_triangle y x (axisFoot ξ η hne x))
  rw [dist_comm y x] at hy
  exact abs_le.mpr ⟨by linarith only [hy], by linarith only [hx]⟩

theorem dist_axisFoot_smul (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n))) (x : HUpper n) :
    dist ((poMulAction hn).smul g x) (axisFoot ξ η hne ((poMulAction hn).smul g x)) =
      dist x (axisFoot ξ η hne x) := by
  rw [axisFoot_smul hn g ξ η hne hpair x]
  exact po_dist_smul hn g x (axisFoot ξ η hne x)

theorem dist_normal_geod_le_dist_smul (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n)))
    (y : HUpper n) (hy : axisFoot ξ η hne y ≠ y) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    dist (geodFromTo (axisFoot ξ η hne y) y hy s) (geodFromTo (axisFoot ξ η hne y) y hy t) ≤
      dist (geodFromTo (axisFoot ξ η hne y) y hy s)
        ((poMulAction hn).smul g (geodFromTo (axisFoot ξ η hne y) y hy t)) := by
  have hd := (lipschitzWith_dist_axisFoot ξ η hne).dist_le_mul
    (geodFromTo (axisFoot ξ η hne y) y hy s)
    ((poMulAction hn).smul g (geodFromTo (axisFoot ξ η hne y) y hy t))
  rw [NNReal.coe_one, one_mul, Real.dist_eq,
    dist_axisFoot_smul hn g ξ η hne hpair,
    AxialThinCompactness.dist_normal_axisFoot, AxialThinCompactness.dist_normal_axisFoot,
    abs_of_nonneg hs, abs_of_nonneg ht] at hd
  simpa only [dist_geodFromTo] using hd

theorem dist_smul_axisFoot_eq_abs_log_poConfFactor (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hη : (poBoundaryMulAction hn).smul g η = η) (x : HUpper n) :
    dist ((poMulAction hn).smul g (axisFoot ξ η hne x)) (axisFoot ξ η hne x) =
      |Real.log (BusemannCocycle.poConfFactor hn g ξ)| := by
  have hmem := axisFoot_mem ξ η hne x
  rw [axis_eq_range_rayTo ξ η hne] at hmem
  obtain ⟨t, ht⟩ := hmem
  rw [← ht, BoundaryStabilizer.smul_axis_ray hn g ξ η hne hξ hη,
    AsymptoticRays.dist_rayTo, add_sub_cancel_left]

end DifferentialGeometry.AxisGeometry
