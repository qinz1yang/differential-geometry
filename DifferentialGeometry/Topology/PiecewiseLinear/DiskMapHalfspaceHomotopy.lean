/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import Mathlib.Topology.Piecewise
import Mathlib.Topology.UnitInterval

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem exists_diskMap_halfspace_homotopy {P : Set Plane} (hP : IsPLBall 2 P)
    {Φ : Plane × ℝ → Plane × ℝ} (hΦ : Continuous Φ)
    (hfix : EqOn Φ id (P ×ˢ Icc (-1 : ℝ) 1)ᶜ)
    (hbox : MapsTo Φ (P ×ˢ Icc (-1 : ℝ) 1) (P ×ˢ Icc (-1 : ℝ) 1))
    (hside : ∀ z, 0 ≤ z.2 → 0 ≤ (Φ z).2) :
    ∃ H : (Plane × ℝ) × unitInterval → Plane × ℝ, Continuous H ∧
      (∀ z, H (z, 0) = z) ∧ (∀ z, H (z, 1) = Φ z) ∧
      (∀ t, EqOn (fun z => H (z, t)) id (P ×ˢ Icc (-1 : ℝ) 1)ᶜ) ∧
      (∀ t, MapsTo (fun z => H (z, t)) (P ×ˢ Icc (-1 : ℝ) 1)
        (P ×ˢ Icc (-1 : ℝ) 1)) ∧
      (∀ z t, 0 ≤ z.2 → 0 ≤ (H (z, t)).2) ∧
      ((∀ z, z.2 = 0 → (Φ z).2 = 0) → ∀ z t, z.2 = 0 → (H (z, t)).2 = 0) := by
  classical
  obtain ⟨q, hq⟩ := id hP
  let Δ := Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
  let r := Function.invFunOn q Δ
  let B := P ×ˢ Icc (-1 : ℝ) 1
  let S : Set ((Plane × ℝ) × unitInterval) := {w | w.1 ∈ B}
  have hrmem : ∀ x ∈ P, r x ∈ Δ := hq.bijOn.surjOn.mapsTo_invFunOn
  have hqr : ∀ x ∈ P, q (r x) = x := hq.bijOn.invOn_invFunOn.2
  let a : (Plane × ℝ) × unitInterval → Fin 3 → ℝ := fun w =>
    (1 - (w.2 : ℝ)) • r w.1.1 + (w.2 : ℝ) • r (Φ w.1).1
  let F : (Plane × ℝ) × unitInterval → Plane × ℝ := fun w =>
    (q (a w), (1 - (w.2 : ℝ)) * w.1.2 + (w.2 : ℝ) * (Φ w.1).2)
  have hamem : MapsTo a S Δ := by
    intro w hw
    exact (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin 3)) (hrmem _ hw.1)
      (hrmem _ (hbox hw).1) (sub_nonneg.mpr w.2.2.2) w.2.2.1 (sub_add_cancel _ _)
  have ht : Continuous (fun w : (Plane × ℝ) × unitInterval => (w.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hrx : ContinuousOn (fun w : (Plane × ℝ) × unitInterval => r w.1.1) S :=
    hq.isPiecewiseAffineOn_invFunOn.continuousOn.comp continuous_fst.fst.continuousOn
      (fun _ hw => hw.1)
  have hry : ContinuousOn (fun w : (Plane × ℝ) × unitInterval => r (Φ w.1).1) S :=
    hq.isPiecewiseAffineOn_invFunOn.continuousOn.comp
      (hΦ.fst.comp continuous_fst).continuousOn (fun _ hw => (hbox hw).1)
  have hac : ContinuousOn a S :=
    ((continuous_const.sub ht).continuousOn.smul hrx).add (ht.continuousOn.smul hry)
  have hFc : ContinuousOn F S :=
    (hq.isPiecewiseAffineOn.continuousOn.comp hac hamem).prodMk
      (((continuous_const.sub ht).mul continuous_fst.snd).add
        (ht.mul (hΦ.snd.comp continuous_fst))).continuousOn
  have hBclosed : IsClosed B := hP.isPolyhedron.isClosed.prod isClosed_Icc
  have hSclosed : IsClosed S := hBclosed.preimage continuous_fst
  have hfront : EqOn Φ id (frontier B) := (hfix.closure hΦ continuous_id).mono (by
    rw [← frontier_compl]
    exact frontier_subset_closure)
  have hFfix : ∀ w ∈ S, Φ w.1 = w.1 → F w = w.1 := by
    intro w hw heq
    dsimp only [F, a]
    rw [heq, ← add_smul, sub_add_cancel, one_smul, hqr _ hw.1]
    congr 1
    ring
  let H : (Plane × ℝ) × unitInterval → Plane × ℝ := S.piecewise F Prod.fst
  have hHc : Continuous H := by
    apply continuous_piecewise
    · intro w hw
      exact hFfix w (hSclosed.frontier_subset hw)
        (hfront (continuous_fst.frontier_preimage_subset B hw))
    · rwa [hSclosed.closure_eq]
    · exact continuous_fst.continuousOn
  refine ⟨H, hHc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    by_cases hz : z ∈ B
    · rw [show H (z, 0) = F (z, 0) from ite_eq_left hz]
      change (q ((1 - (0 : ℝ)) • r z.1 + (0 : ℝ) • r (Φ z).1),
        (1 - (0 : ℝ)) * z.2 + (0 : ℝ) * (Φ z).2) = z
      simp only [sub_zero, one_smul, zero_smul, add_zero, one_mul, zero_mul, hqr _ hz.1]
    · exact ite_eq_right hz
  · intro z
    by_cases hz : z ∈ B
    · rw [show H (z, 1) = F (z, 1) from ite_eq_left hz]
      change (q ((1 - (1 : ℝ)) • r z.1 + (1 : ℝ) • r (Φ z).1),
        (1 - (1 : ℝ)) * z.2 + (1 : ℝ) * (Φ z).2) = Φ z
      simp only [sub_self, zero_smul, one_smul, zero_add, zero_mul, one_mul,
        hqr _ (hbox hz).1]
    · exact (ite_eq_right hz).trans (hfix hz).symm
  · intro t z hz
    exact ite_eq_right hz
  · intro t z hz
    change H (z, t) ∈ B
    rw [show H (z, t) = F (z, t) from ite_eq_left hz]
    refine ⟨hq.bijOn.mapsTo (hamem hz), ?_⟩
    exact (convex_Icc (-1 : ℝ) 1) hz.2 (hbox hz).2
      (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel _ _)
  · intro z t hz
    by_cases hzB : z ∈ B
    · rw [show H (z, t) = F (z, t) from ite_eq_left hzB]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) hz)
        (mul_nonneg t.2.1 (hside z hz))
    · rw [show H (z, t) = z from ite_eq_right hzB]
      exact hz
  · intro hplane z t hz
    by_cases hzB : z ∈ B
    · rw [show H (z, t) = F (z, t) from ite_eq_left hzB]
      change (1 - (t : ℝ)) * z.2 + (t : ℝ) * (Φ z).2 = 0
      rw [hz, hplane z hz, mul_zero, mul_zero, zero_add]
    · rw [show H (z, t) = z from ite_eq_right hzB]
      exact hz

end DifferentialGeometry.Topology.PiecewiseLinear
