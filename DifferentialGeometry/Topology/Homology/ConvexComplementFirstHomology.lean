/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.EuclideanThreePunctureFirstHomology
import Mathlib.Analysis.Convex.Star

open Set Metric

namespace DifferentialGeometry.Topology

theorem subsingleton_integralFirstHomology_complement_of_bounded_starConvex
    {C : Set (EuclideanSpace ℝ (Fin 3))} {p : EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ C) (hC : StarConvex ℝ p C) (hb : Bornology.IsBounded C) :
    Subsingleton (integralSingularHomology 1 (Cᶜ : Set (EuclideanSpace ℝ (Fin 3)))) := by
  obtain ⟨R, hR, hCR⟩ := hb.subset_ball_lt 0 p
  have hnorm (x : ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))) : ‖(x : _) - p‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr x.property)
  have hout (x : (Cᶜ : Set (EuclideanSpace ℝ (Fin 3)))) {a : ℝ} (ha : 1 ≤ a) :
      p + a • ((x : _) - p) ∈ Cᶜ := by
    intro hx
    have ha0 : 0 < a := zero_lt_one.trans_le ha
    have h := hC.add_smul_sub_mem hx (inv_nonneg.mpr ha0.le) (inv_le_one_of_one_le₀ ha)
    apply x.property
    simpa only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha0.ne', one_smul,
      add_sub_cancel] using h
  let i : C((Cᶜ : Set (EuclideanSpace ℝ (Fin 3))),
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))) :=
    ⟨fun x => ⟨x, fun hx => x.property (hx.symm ▸ hp)⟩, continuous_subtype_val.subtype_mk _⟩
  let r : C(({p}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
      (Cᶜ : Set (EuclideanSpace ℝ (Fin 3)))) :=
    ⟨fun x => ⟨p + (1 + R / ‖(x : _) - p‖) • ((x : _) - p), by
      intro hx
      have hlt := mem_ball.mp (hCR hx)
      have ha : 0 ≤ 1 + R / ‖(x : _) - p‖ := by positivity
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ha] at hlt
      have heq : (1 + R / ‖(x : _) - p‖) * ‖(x : _) - p‖ = ‖(x : _) - p‖ + R := by
        field_simp [hnorm x]
      rw [heq] at hlt
      linarith [norm_nonneg ((x : _) - p)]⟩,
      by
        apply Continuous.subtype_mk
        exact continuous_const.add ((continuous_const.add
          (continuous_const.div (continuous_subtype_val.sub continuous_const).norm hnorm)).smul
            (continuous_subtype_val.sub continuous_const))⟩
  have hhom : (ContinuousMap.id (Cᶜ : Set (EuclideanSpace ℝ (Fin 3)))).Homotopic
      (r.comp i) := by
    refine ⟨{
      toFun := fun q => ⟨p + (1 + (q.1 : ℝ) * R / ‖(q.2 : _) - p‖) • ((q.2 : _) - p),
        hout q.2 (le_add_of_nonneg_right
          (div_nonneg (mul_nonneg q.1.2.1 hR.le) (norm_nonneg _)))⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · have hx : Continuous (fun q : unitInterval × (Cᶜ : Set (EuclideanSpace ℝ (Fin 3))) =>
          (q.2 : EuclideanSpace ℝ (Fin 3)) - p) :=
        (continuous_subtype_val.comp continuous_snd).sub continuous_const
      have ht : Continuous (fun q : unitInterval × (Cᶜ : Set (EuclideanSpace ℝ (Fin 3))) =>
          (q.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
      exact (continuous_const.add ((continuous_const.add
        ((ht.mul continuous_const).div hx.norm (fun q => hnorm (i q.2)))).smul hx)).subtype_mk _
    · intro x
      apply Subtype.ext
      simp
    · intro x
      apply Subtype.ext
      simp [r, i]
  have hz : ∀ a : integralSingularHomology 1 (Cᶜ : Set (EuclideanSpace ℝ (Fin 3))),
      a = 0 := by
    intro a
    have hi : integralSingularHomologyMap 1 i a = 0 :=
      (subsingleton_integralFirstHomology_complement_point p).elim _ _
    have h := LinearMap.congr_fun (integralSingularHomologyMap_homotopic 1 hhom) a
    rw [integralSingularHomologyMap_id, integralSingularHomologyMap_comp,
      LinearMap.id_apply, LinearMap.comp_apply, hi, map_zero] at h
    exact h
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end DifferentialGeometry.Topology
