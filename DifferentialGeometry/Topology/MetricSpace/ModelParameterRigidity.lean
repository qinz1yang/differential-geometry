import DifferentialGeometry.Topology.MetricSpace.MetricEndpoint
import DifferentialGeometry.Topology.MetricSpace.CircleDistance

set_option autoImplicit false

open Set Metric

namespace IsometryEquiv

theorem apply_Ici_zero (e : Ici (0 : ℝ) ≃ᵢ Ici (0 : ℝ)) (t : Ici (0 : ℝ)) : e t = t := by
  let z : Ici (0 : ℝ) := ⟨0, by simp⟩
  have hz : IsEndpoint z := (isEndpoint_Ici_iff z).mpr rfl
  have hez : e z = z := Subtype.ext ((isEndpoint_Ici_iff (e z)).mp
    ((isEndpoint_isometryEquiv_iff e z).mpr hz))
  have hd := e.dist_eq t z
  rw [hez] at hd
  apply Subtype.ext
  simpa only [Subtype.dist_eq, Real.dist_eq, z, sub_zero,
    abs_of_nonneg (show 0 ≤ (e t : ℝ) from (e t).property),
    abs_of_nonneg (show 0 ≤ (t : ℝ) from t.property)] using hd

theorem Icc_length_and_coordinates {L M : ℝ} (hL : 0 < L) (hM : 0 < M)
    (e : Icc (0 : ℝ) L ≃ᵢ Icc (0 : ℝ) M) :
    L = M ∧ ((∀ t, (e t : ℝ) = t) ∨ (∀ t, (e t : ℝ) = L - t)) := by
  let z : Icc (0 : ℝ) L := ⟨0, le_rfl, hL.le⟩
  let w : Icc (0 : ℝ) L := ⟨L, hL.le, le_rfl⟩
  have hz : IsEndpoint z := (isEndpoint_Icc_iff hL.le z).mpr (Or.inl rfl)
  have hw : IsEndpoint w := (isEndpoint_Icc_iff hL.le w).mpr (Or.inr rfl)
  have hez := (isEndpoint_Icc_iff hM.le (e z)).mp ((isEndpoint_isometryEquiv_iff e z).mpr hz)
  have hew := (isEndpoint_Icc_iff hM.le (e w)).mp ((isEndpoint_isometryEquiv_iff e w).mpr hw)
  have hne : (e z : ℝ) ≠ (e w : ℝ) := by
    intro h
    have hh := congrArg (fun t : Icc (0 : ℝ) L => (t : ℝ)) (e.injective (Subtype.ext h))
    change 0 = L at hh
    linarith
  have hd := e.dist_eq w z
  change |(e w : ℝ) - e z| = |L - 0| at hd
  rw [sub_zero, abs_of_pos hL] at hd
  rcases hez with hez | hez
  · have hew : (e w : ℝ) = M := hew.resolve_left (fun h => hne (hez.trans h.symm))
    have hLM : L = M := by rw [hew, hez, sub_zero, abs_of_pos hM] at hd; exact hd.symm
    refine ⟨hLM, Or.inl (fun t => ?_)⟩
    have h := e.dist_eq t z
    change |(e t : ℝ) - e z| = |(t : ℝ) - 0| at h
    simpa only [hez, sub_zero, abs_of_nonneg (e t).property.1,
      abs_of_nonneg t.property.1] using h
  · have hew : (e w : ℝ) = 0 := hew.resolve_right (fun h => hne (hez.trans h.symm))
    have hLM : L = M := by rw [hew, hez, zero_sub, abs_neg, abs_of_pos hM] at hd; exact hd.symm
    refine ⟨hLM, Or.inr (fun t => ?_)⟩
    have h := e.dist_eq t z
    change |(e t : ℝ) - e z| = |(t : ℝ) - 0| at h
    rw [hez, abs_of_nonpos (sub_nonpos.mpr (e t).property.2), sub_zero,
      abs_of_nonneg t.property.1] at h
    linarith

theorem addCircle_period_eq {L M : ℝ} (hL : 0 < L) (hM : 0 < M)
    (e : AddCircle L ≃ᵢ AddCircle M) : L = M := by
  have hle {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
      (f : AddCircle A ≃ᵢ AddCircle B) : A ≤ B := by
    have hd := f.dist_eq ((A / 2 : ℝ) : AddCircle A) 0
    have hb := AddCircle.norm_le_half_period B (x := f ((A / 2 : ℝ) : AddCircle A) - f 0) hB.ne'
    rw [← dist_eq_norm, hd, dist_zero_right, AddCircle.norm_half_period_eq,
      abs_of_pos hA, abs_of_pos hB] at hb
    linarith
  exact le_antisymm (hle hL hM e) (hle hM hL e.symm)

theorem Ici_pointed_height_eq {X : Type*} [MetricSpace X]
    (e f : X ≃ᵢ Ici (0 : ℝ)) (p : X) : (e p : ℝ) = (f p : ℝ) := by
  have h := congrArg (fun t : Ici (0 : ℝ) => (t : ℝ))
    ((e.symm.trans f).apply_Ici_zero (e p))
  simpa using h.symm

theorem Icc_pointed_coordinates {X : Type*} [MetricSpace X] {L M : ℝ}
    (hL : 0 < L) (hM : 0 < M) (e : X ≃ᵢ Icc (0 : ℝ) L)
    (f : X ≃ᵢ Icc (0 : ℝ) M) (p : X) :
    L = M ∧ ((f p : ℝ) = (e p : ℝ) ∨ (f p : ℝ) = L - (e p : ℝ)) := by
  obtain ⟨hLM, hc⟩ := (e.symm.trans f).Icc_length_and_coordinates hL hM
  refine ⟨hLM, ?_⟩
  rcases hc with hc | hc
  · exact Or.inl (by simpa using hc (e p))
  · exact Or.inr (by simpa using hc (e p))

end IsometryEquiv
