/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.InjectiveDeterminantSign

open Metric Set Filter
open scoped Topology

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

theorem isLocallyConstant_euclideanLocalDegree_sub_of_injOn
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hinj : InjOn f U) :
    IsLocallyConstant (fun z : U =>
      euclideanLocalDegree (fun w => f w - f z) z
        (isolatedZero_sub_of_injOn hU hf hinj z.2)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds z.2)
  have hR2 : 0 < R / 2 := half_pos hR
  have hsub : closedBall (z : EuclideanSpace ℝ (Fin (d + 1))) (2 * (R / 2)) ⊆ U := by
    rw [mul_div_cancel₀ R two_ne_zero]
    exact hRU
  have hball : ∀ᶠ w : U in 𝓝 z,
      (w : EuclideanSpace ℝ (Fin (d + 1))) ∈
        ball (z : EuclideanSpace ℝ (Fin (d + 1))) (R / 2) :=
    (continuous_subtype_val.tendsto z).eventually (ball_mem_nhds _ hR2)
  filter_upwards [hball] with w hw
  exact (euclideanLocalDegree_sub_eq_of_mem_ball hf hinj hR2 hsub hw _ _).symm

theorem euclideanLocalDegree_sub_eq_of_injOn
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : ContinuousOn f U) (hinj : InjOn f U)
    {x y : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ U) (hy : y ∈ U) :
    euclideanLocalDegree (fun z => f z - f x) x
        (isolatedZero_sub_of_injOn hU hf hinj hx) =
      euclideanLocalDegree (fun z => f z - f y) y
        (isolatedZero_sub_of_injOn hU hf hinj hy) := by
  have hpre : PreconnectedSpace U := Subtype.preconnectedSpace hUc
  have hD := isLocallyConstant_euclideanLocalDegree_sub_of_injOn hU hf hinj
  exact hD.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

end DifferentialGeometry.LocalDegree
