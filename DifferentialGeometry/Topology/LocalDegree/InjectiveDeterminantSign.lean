/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.BoundaryHomotopy
import DifferentialGeometry.Topology.LocalDegree.Determinant

open Metric Set Filter
open scoped Topology unitInterval

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

theorem isolatingRadius_sub_of_injOn
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hf : ContinuousOn f U) (hinj : InjOn f U)
    {x : EuclideanSpace ℝ (Fin (d + 1))} {R : ℝ} (hR : 0 < R) (hxU : closedBall x R ⊆ U) :
    IsolatingRadius (fun y => f y - f x) x R where
  pos := hR
  continuousOn := (hf.mono hxU).sub continuousOn_const
  zero_iff y hy := by
    rw [sub_eq_zero]
    exact ⟨fun h => hinj (hxU hy) (hxU (mem_closedBall_self hR.le)) h, fun h => h ▸ rfl⟩

theorem isolatedZero_sub_of_injOn
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ U) :
    isolatedZero (fun y => f y - f x) x := by
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  exact ⟨R, isolatingRadius_sub_of_injOn hf hinj hR hRU⟩

theorem euclideanLocalDegree_sub_eq_of_mem_ball
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hf : ContinuousOn f U) (hinj : InjOn f U)
    {x x' : EuclideanSpace ℝ (Fin (d + 1))} {R : ℝ} (hR : 0 < R)
    (hxU : closedBall x (2 * R) ⊆ U) (hx' : x' ∈ ball x R)
    (h : isolatedZero (fun y => f y - f x) x) (h' : isolatedZero (fun y => f y - f x') x') :
    euclideanLocalDegree (fun y => f y - f x) x h =
      euclideanLocalDegree (fun y => f y - f x') x' h' := by
  set v := x' - x with hvdef
  have hvR : ‖v‖ < R := by rw [hvdef, ← dist_eq_norm]; exact mem_ball.mp hx'
  have hsub : closedBall x R ⊆ closedBall x (2 * R) :=
    closedBall_subset_closedBall (by linarith)
  have hball' : closedBall x' R ⊆ closedBall x (2 * R) := by
    intro y hy
    rw [mem_closedBall] at hy ⊢
    have := dist_triangle y x' x
    rw [dist_comm x' x] at this
    have hx'x : dist x x' < R := by rw [dist_comm]; exact mem_ball.mp hx'
    linarith
  have hshift : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ y ∈ closedBall x R,
      y + t • v ∈ closedBall x (2 * R) := by
    intro t ht0 ht1 y hy
    rw [mem_closedBall] at hy ⊢
    have htv : ‖t • v‖ ≤ R := by
      rw [norm_smul, Real.norm_of_nonneg ht0]
      nlinarith [norm_nonneg v]
    calc dist (y + t • v) x ≤ dist (y + t • v) y + dist y x := dist_triangle _ _ _
      _ = ‖t • v‖ + dist y x := by rw [dist_eq_norm, add_sub_cancel_left]
      _ ≤ 2 * R := by linarith
  have hfx := isolatingRadius_sub_of_injOn hf hinj hR (hsub.trans hxU)
  have hfx' := isolatingRadius_sub_of_injOn hf hinj hR (hball'.trans hxU)
  let g : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) :=
    fun y => f (y + v) - f x'
  have hg : IsolatingRadius g x R := by
    refine ⟨hR, ?_, ?_⟩
    · refine ((hf.comp (continuous_id.add continuous_const).continuousOn ?_)).sub
        continuousOn_const
      intro y hy
      have := hshift 1 zero_le_one le_rfl y hy
      rw [one_smul] at this
      exact hxU this
    · intro y hy
      have hy1 := hshift 1 zero_le_one le_rfl y hy
      rw [one_smul] at hy1
      have hx'1 : x' ∈ closedBall x (2 * R) := by
        have := hshift 1 zero_le_one le_rfl x (mem_closedBall_self hR.le)
        rwa [one_smul, hvdef, add_sub_cancel] at this
      change f (y + v) - f x' = 0 ↔ y = x
      rw [sub_eq_zero]
      constructor
      · intro hyx
        have := hinj (hxU hy1) (hxU hx'1) hyx
        rw [hvdef] at this
        have h2 : y = x' - (x' - x) := eq_sub_of_add_eq this
        rw [h2, sub_sub_cancel]
      · intro hyx
        rw [hyx, hvdef, add_sub_cancel]
  have hstep1 : euclideanLocalDegree (fun y => f y - f x) x ⟨R, hfx⟩ =
      euclideanLocalDegree g x ⟨R, hg⟩ := by
    apply euclideanLocalDegree_eq_of_boundaryHomotopy hfx hg
      (fun p => f (p.2 + (p.1 : ℝ) • v) - f (x + (p.1 : ℝ) • v))
    · refine ContinuousOn.sub ?_ ?_
      · refine hf.comp (continuous_snd.add
          ((continuous_subtype_val.comp continuous_fst).smul continuous_const)).continuousOn ?_
        rintro ⟨t, y⟩ ⟨-, hy⟩
        exact hxU (hshift t t.2.1 t.2.2 y (sphere_subset_closedBall hy))
      · refine hf.comp (continuous_const.add
          ((continuous_subtype_val.comp continuous_fst).smul continuous_const)).continuousOn ?_
        rintro ⟨t, y⟩ -
        exact hxU (hshift t t.2.1 t.2.2 x (mem_closedBall_self hR.le))
    · intro t y hy hzero
      rw [sub_eq_zero] at hzero
      have hyx := hinj (hxU (hshift t t.2.1 t.2.2 y (sphere_subset_closedBall hy)))
        (hxU (hshift t t.2.1 t.2.2 x (mem_closedBall_self hR.le))) hzero
      have hyx' : y = x := add_right_cancel hyx
      rw [hyx', mem_sphere, dist_self] at hy
      exact hR.ne' hy.symm
    · intro y _
      simp
    · intro y _
      change f (y + (1 : ℝ) • v) - f (x + (1 : ℝ) • v) = f (y + v) - f x'
      rw [one_smul, hvdef, add_sub_cancel]
  have hstep2 : euclideanLocalDegree g x ⟨R, hg⟩ =
      euclideanLocalDegree (fun y => f y - f x') x' ⟨R, hfx'⟩ := by
    rw [euclideanLocalDegree_eq_sphereDegree ⟨R, hg⟩ hg ⟨R, hR, le_rfl⟩,
      euclideanLocalDegree_eq_sphereDegree ⟨R, hfx'⟩ hfx' ⟨R, hR, le_rfl⟩]
    congr 1
    apply ContinuousMap.ext
    intro w
    apply Subtype.ext
    simp only [sphereMap_apply]
    have hpt : x + R • (w : EuclideanSpace ℝ (Fin (d + 1))) + v =
        x' + R • (w : EuclideanSpace ℝ (Fin (d + 1))) := by
      rw [hvdef]
      abel
    change ‖f (x + R • (w : EuclideanSpace ℝ (Fin (d + 1))) + v) - f x'‖⁻¹ •
        (f (x + R • (w : EuclideanSpace ℝ (Fin (d + 1))) + v) - f x') = _
    rw [hpt]
  exact hstep1.trans hstep2

theorem sign_det_fderiv_eq_of_injOn
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) {x y : EuclideanSpace ℝ (Fin (d + 1))}
    (hx : x ∈ U) (hy : y ∈ U) (hdx : DifferentiableAt ℝ f x) (hdy : DifferentiableAt ℝ f y)
    (hx0 : LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0)
    (hy0 : LinearMap.det (fderiv ℝ f y).toLinearMap ≠ 0) :
    SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) =
      SignType.sign (LinearMap.det (fderiv ℝ f y).toLinearMap) := by
  let D : U → ℤ := fun z =>
    euclideanLocalDegree (fun w => f w - f z) z (isolatedZero_sub_of_injOn hU hf hinj z.2)
  have hD : IsLocallyConstant D := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds z.2)
    have hR2 : 0 < R / 2 := half_pos hR
    have hsub : closedBall (z : EuclideanSpace ℝ (Fin (d + 1))) (2 * (R / 2)) ⊆ U := by
      rw [mul_div_cancel₀ R two_ne_zero]
      exact hRU
    have hball : ∀ᶠ w : U in 𝓝 z, (w : EuclideanSpace ℝ (Fin (d + 1))) ∈
        ball (z : EuclideanSpace ℝ (Fin (d + 1))) (R / 2) :=
      (continuous_subtype_val.tendsto z).eventually (ball_mem_nhds _ hR2)
    filter_upwards [hball] with w hw
    exact (euclideanLocalDegree_sub_eq_of_mem_ball hf hinj hR2 hsub hw _ _).symm
  have hpre : PreconnectedSpace U := Subtype.preconnectedSpace hUc
  have hxy : D ⟨x, hx⟩ = D ⟨y, hy⟩ := hD.apply_eq_of_preconnectedSpace _ _
  have hsign : ∀ z (hz : z ∈ U), DifferentiableAt ℝ f z →
      LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0 →
      D ⟨z, hz⟩ = (SignType.sign (LinearMap.det (fderiv ℝ f z).toLinearMap) : ℤ) := by
    intro z hz hdz hz0
    have hfd : fderiv ℝ (fun w => f w - f z) z = fderiv ℝ f z := fderiv_sub_const _
    change euclideanLocalDegree (fun w => f w - f z) z _ = _
    rw [euclideanLocalDegree_eq_sign_det_fderiv _ (hdz.sub_const _) (by rwa [hfd]), hfd]
  have hcast : ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ) =
      ((SignType.sign (LinearMap.det (fderiv ℝ f y).toLinearMap) : SignType) : ℤ) := by
    rw [← hsign x hx hdx hx0, ← hsign y hy hdy hy0, hxy]
  generalize SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) = s at hcast
  generalize SignType.sign (LinearMap.det (fderiv ℝ f y).toLinearMap) = t at hcast
  cases s <;> cases t <;> first | rfl | (norm_num at hcast)

end DifferentialGeometry.LocalDegree
