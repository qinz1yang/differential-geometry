/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Metric
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Transitivity

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.HyperbolicGeodesic

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.Hyperbolic.HUpper
open DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.HyperbolicBoundary
open DifferentialGeometry.BoundaryTopology
open DifferentialGeometry.HyperbolicGeometry
open Matrix
open scoped unitInterval

variable {n : ℕ}

theorem eq_basepoint_of_sdot_eq_zero {x : HUpper n} (h : sdot x.val x.val = 0) :
    x = basepointH := by
  have hcoord : ∀ i : Fin n, x.val (Sum.inl i) = 0 :=
    fun i => inl_eq_zero_of_sdot_self_eq_zero h i
  have htc : tc x.val = 1 := by
    have h2 : tc x.val ^ 2 = 1 := by
      have h3 := tc_sq x
      rw [h] at h3
      linarith
    have hpos : 0 < tc x.val := x.future
    nlinarith
  apply HUpper.ext
  funext a
  rcases a with i | k
  · rw [hcoord i]
    exact (eTime_apply_inl i).symm
  · have hk0 : k = 0 := Subsingleton.elim k 0
    subst hk0
    change x.val (Sum.inr 0) = (eTime : LorVec n) (Sum.inr 0)
    rw [eTime_apply_inr]
    exact htc

theorem neg_lorB_eTime (x : HUpper n) : - lorB (eTime : LorVec n) x.val = tc x.val := by
  have hsd0 : sdot (eTime : LorVec n) x.val = 0 := by
    change (∑ i : Fin n, (eTime : LorVec n) (Sum.inl i) * x.val (Sum.inl i)) = 0
    simp [eTime_apply_inl]
  change -(sdot (eTime : LorVec n) x.val - tc (eTime : LorVec n) * tc x.val) = tc x.val
  rw [hsd0, tc_eTime]
  ring

theorem dist_basepoint (x : HUpper n) : dist basepointH x = Real.arcosh (tc x.val) := by
  change HUpper.hdist basepointH x = _
  unfold HUpper.hdist
  change Real.arcosh (- lorB (eTime : LorVec n) x.val) = _
  rw [neg_lorB_eTime]

theorem geodesicRay_reaches_point {x : HUpper n} (hx : x ≠ basepointH) :
    ∃ ξ : BoundaryH n, geodesicRay ξ (dist basepointH x) = x := by
  have hs : sdot x.val x.val ≠ 0 := by
    intro h
    exact hx (eq_basepoint_of_sdot_eq_zero h)
  have hspos : 0 < sdot x.val x.val := lt_of_le_of_ne (sdot_self_nonneg _) (Ne.symm hs)
  set s : ℝ := sdot x.val x.val with hsdef
  set sq : ℝ := Real.sqrt s with hsqdef
  have hsqpos : 0 < sq := Real.sqrt_pos.mpr hspos
  refine ⟨⟨Sum.elim (fun i => sq⁻¹ * x.val (Sum.inl i)) (fun _ => 1), ?_, rfl⟩, ?_⟩
  · show lorB (Sum.elim (fun i => sq⁻¹ * x.val (Sum.inl i)) (fun _ => 1))
        (Sum.elim (fun i => sq⁻¹ * x.val (Sum.inl i)) (fun _ => 1)) = 0
    have hsd : sdot (Sum.elim (fun i => sq⁻¹ * x.val (Sum.inl i)) (fun _ => 1))
        (Sum.elim (fun i => sq⁻¹ * x.val (Sum.inl i)) (fun _ => 1)) = 1 := by
      change (∑ i : Fin n, sq⁻¹ * x.val (Sum.inl i) * (sq⁻¹ * x.val (Sum.inl i))) = 1
      have h1 : ∀ i : Fin n, sq⁻¹ * x.val (Sum.inl i) * (sq⁻¹ * x.val (Sum.inl i))
          = (sq⁻¹ * sq⁻¹) * (x.val (Sum.inl i) * x.val (Sum.inl i)) := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum]
      have hsum : (∑ i : Fin n, x.val (Sum.inl i) * x.val (Sum.inl i)) = s := rfl
      have h2 : sq⁻¹ * sq⁻¹ = s⁻¹ := by
        rw [hsqdef, ← _root_.mul_inv_rev, Real.mul_self_sqrt hspos.le]
      rw [hsum, h2, inv_mul_cancel₀ (ne_of_gt hspos)]
    change sdot _ _ - tc _ * tc _ = 0
    rw [hsd]
    change (1 : ℝ) - 1 * 1 = 0
    norm_num
  · have hd : dist basepointH x = Real.arcosh (tc x.val) := dist_basepoint x
    have hcosh : Real.cosh (dist basepointH x) = tc x.val := by
      rw [hd]
      exact Real.cosh_arcosh (one_le_tc x)
    have hsinh : Real.sinh (dist basepointH x) = sq := by
      rw [hd, Real.sinh_arcosh (one_le_tc x)]
      have h1 : tc x.val ^ 2 - 1 = s := by
        have h2 := tc_sq x
        rw [hsdef]
        linarith [h2]
      rw [h1, hsqdef]
    set ξ : BoundaryH n := ⟨Sum.elim (fun i => sq⁻¹ * x.val (Sum.inl i)) (fun _ => 1), _, rfl⟩
    apply HUpper.ext
    funext a
    rcases a with i | k
    · change (Real.cosh (dist basepointH x) • (eTime : LorVec n)
          + Real.sinh (dist basepointH x) • spatialEmbed (spatial ξ)) (Sum.inl i)
          = x.val (Sum.inl i)
      have hspξ : spatial ξ i = sq⁻¹ * x.val (Sum.inl i) := rfl
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        eTime_apply_inl, spatialEmbed_inl, hspξ, hcosh, hsinh]
      change tc x.val * 0 + sq * (sq⁻¹ * x.val (Sum.inl i)) = x.val (Sum.inl i)
      rw [mul_zero, zero_add, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsqpos), one_mul]
    · have hk0 : k = 0 := Subsingleton.elim k 0
      subst hk0
      change (Real.cosh (dist basepointH x) • (eTime : LorVec n)
          + Real.sinh (dist basepointH x) • spatialEmbed (spatial ξ)) (Sum.inr 0)
          = x.val (Sum.inr 0)
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        eTime_apply_inr, spatialEmbed_inr, hcosh, hsinh]
      change tc x.val * 1 + sq * 0 = tc x.val
      rw [mul_one, mul_zero, add_zero]

theorem exists_isometric_segment (hn : 1 ≤ n) (x y : HUpper n) :
    ∃ γ : ℝ → HUpper n, Continuous γ ∧ γ 0 = x ∧ γ (dist x y) = y ∧
      (∀ s t : ℝ, s ∈ Set.Icc 0 (dist x y) → t ∈ Set.Icc 0 (dist x y) →
        dist (γ s) (γ t) = |s - t|) := by
  by_cases hxy : x = y
  · subst hxy
    refine ⟨fun _ => x, continuous_const, rfl, rfl, fun s t hs ht => ?_⟩
    have h0 : dist x x = 0 := dist_self x
    rw [h0, Set.mem_Icc] at hs ht
    have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    rw [hs0, ht0]
    simp
  · obtain ⟨g, hg⟩ := HyperbolicTransitive.exists_po_smul_basepoint hn x
    let := poMulAction hn
    have hg' : g • basepointH = x := hg
    set y' : HUpper n := g⁻¹ • y with hy'def
    have hgy : g • y' = y := by rw [hy'def, smul_smul, mul_inv_cancel, one_smul]
    have hy' : y' ≠ basepointH := by
      intro h
      apply hxy
      rw [← hgy, h]
      exact hg'.symm
    obtain ⟨ξ, hξ⟩ := geodesicRay_reaches_point hy'
    have hd : dist basepointH y' = dist x y := by
      have e1 : dist (g⁻¹ • x) (g⁻¹ • y) = dist x y := po_dist_smul hn g⁻¹ x y
      have e2 : g⁻¹ • x = basepointH := by rw [← hg', smul_smul, inv_mul_cancel, one_smul]
      rw [e2] at e1
      rw [← hy'def] at e1
      exact e1
    have hLip : LipschitzWith 1 (fun p : HUpper n => g • p) := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro a b
      rw [NNReal.coe_one, one_mul]
      exact (po_dist_smul hn g a b).le
    refine ⟨fun s => g • geodesicRay ξ s, (hLip.continuous).comp (continuous_geodesicRay ξ),
      ?_, ?_, ?_⟩
    · change g • geodesicRay ξ 0 = x
      rw [geodesicRay_zero]
      exact hg'
    · change g • geodesicRay ξ (dist x y) = y
      rw [← hd, hξ]
      exact hgy
    · intro s t _ _
      change dist (g • geodesicRay ξ s) (g • geodesicRay ξ t) = |s - t|
      rw [po_dist_smul hn g]
      exact dist_geodesicRay ξ s t

theorem pathConnectedSpace (hn : 1 ≤ n) : PathConnectedSpace (HUpper n) := by
  have : Nonempty (HUpper n) := ⟨basepointH⟩
  refine ⟨‹Nonempty (HUpper n)›, fun x y => ?_⟩
  obtain ⟨γ, hcont, h0, hd, _⟩ := exists_isometric_segment hn x y
  refine ⟨Path.mk ⟨fun t : I => γ ((t : ℝ) * dist x y), ?_⟩ ?_ ?_⟩
  · exact hcont.comp (continuous_subtype_val.mul continuous_const)
  · change γ ((0 : ℝ) * dist x y) = x
    rw [zero_mul]
    exact h0
  · change γ ((1 : ℝ) * dist x y) = y
    rw [one_mul]
    exact hd

end DifferentialGeometry.HyperbolicGeodesic
