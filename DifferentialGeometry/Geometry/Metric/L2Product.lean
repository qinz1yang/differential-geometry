import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Set

namespace WithLp

variable {E Y : Type*} [MetricSpace E] [MetricSpace Y]

theorem prod_dist_sq_eq_add_sq (a b : WithLp 2 (E × Y)) :
    dist a b ^ 2 = dist a.fst b.fst ^ 2 + dist a.snd b.snd ^ 2 := by
  have h : dist a b = Real.sqrt (dist a.fst b.fst ^ 2 + dist a.snd b.snd ^ 2) := by
    rw [prod_dist_eq_add (by norm_num : 0 < (2 : ENNReal).toReal)]
    norm_num [Real.sqrt_eq_rpow, Real.rpow_two]
  rw [h, Real.sq_sqrt (by positivity)]

theorem isometry_prodMk_left (u : E) : Isometry (fun y : Y => toLp 2 (u, y)) := by
  apply Isometry.of_dist_eq
  intro a b
  have h := prod_dist_sq_eq_add_sq (toLp 2 (u, a)) (toLp 2 (u, b))
  simp only [toLp_fst, toLp_snd, dist_self, zero_pow (by decide : 2 ≠ 0), zero_add] at h
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h

theorem isometry_prodMk_right (y : Y) : Isometry (fun u : E => toLp 2 (u, y)) := by
  apply Isometry.of_dist_eq
  intro a b
  have h := prod_dist_sq_eq_add_sq (toLp 2 (a, y)) (toLp 2 (b, y))
  simp only [toLp_fst, toLp_snd, dist_self, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h

theorem fst_eq_of_dist_add_eq (u : E) (a b : Y) (z : WithLp 2 (E × Y))
    (hz : dist (toLp 2 (u, a)) z + dist z (toLp 2 (u, b)) = dist a b) : z.fst = u := by
  have h₁ := dist_snd_le (toLp 2 (u, a)) z
  have h₂ := dist_snd_le z (toLp 2 (u, b))
  have htri := dist_triangle a z.snd b
  have heq : dist (toLp 2 (u, a)) z = dist a z.snd := by
    change dist a z.snd ≤ _ at h₁
    change dist z.snd b ≤ _ at h₂
    linarith
  have hs := prod_dist_sq_eq_add_sq (toLp 2 (u, a)) z
  simp only [toLp_fst, toLp_snd, heq] at hs
  have hzero : dist u z.fst = 0 := by nlinarith [dist_nonneg (x := u) (y := z.fst)]
  exact (dist_eq_zero.mp hzero).symm

end WithLp

namespace IsometryEquiv

variable {X E Y : Type*} [MetricSpace X] [MetricSpace E] [MetricSpace Y]

noncomputable def l2ProductSlice (e : X ≃ᵢ WithLp 2 (E × Y)) (u : E) :
    Y ≃ᵢ {x : X // (e x).fst = u} where
  toFun y := ⟨e.symm (WithLp.toLp 2 (u, y)), by simp⟩
  invFun x := (e x.val).snd
  left_inv y := by simp
  right_inv x := by
    apply Subtype.ext
    apply e.injective
    simp only [apply_symm_apply]
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext x.property.symm rfl
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro a b
    exact e.symm.dist_eq _ _ |>.trans ((WithLp.isometry_prodMk_left u).dist_eq a b)

theorem isClosed_l2ProductSlice (e : X ≃ᵢ WithLp 2 (E × Y)) (u : E) :
    IsClosed {x : X | (e x).fst = u} :=
  isClosed_eq ((WithLp.continuous_fst 2 E Y).comp e.continuous) continuous_const

theorem completeSpace_l2_product_factor [CompleteSpace X]
    (e : X ≃ᵢ WithLp 2 (E × Y)) (u : E) : CompleteSpace Y := by
  let : CompleteSpace {x : X // (e x).fst = u} :=
    (isClosed_l2ProductSlice e u).completeSpace_coe
  exact (e.l2ProductSlice u).completeSpace

theorem properSpace_l2_product_factor [ProperSpace X]
    (e : X ≃ᵢ WithLp 2 (E × Y)) (u : E) : ProperSpace Y := by
  let : ProperSpace {x : X // (e x).fst = u} :=
    ProperSpace.of_isClosed (isClosed_l2ProductSlice e u)
  refine ⟨fun y r => ?_⟩
  have he := e.l2ProductSlice u
  have h : Metric.closedBall y r = he ⁻¹' Metric.closedBall (he y) r := by
    ext z
    simp only [mem_preimage, Metric.mem_closedBall, he.dist_eq]
  rw [h]
  exact he.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)

end IsometryEquiv
