import DifferentialGeometry.Topology.MetricSpace.CircleEndpoint
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem not_nonempty_isometryEquiv_of_endpoint (p : X) (hp : IsEndpoint p)
    (hY : ∀ y : Y, ¬ IsEndpoint y) : ¬ Nonempty (X ≃ᵢ Y) := by
  rintro ⟨e⟩
  exact hY (e p) ((isEndpoint_isometryEquiv_iff e p).mpr hp)

theorem not_isometry_real_of_dist_bounded {D : ℝ} (hD : ∀ x y : X, dist x y ≤ D)
    (f : ℝ → X) : ¬ Isometry f := by
  intro hf
  have h := hD (f (|D| + 1)) (f 0)
  rw [hf.dist_eq, Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at h
  linarith [le_abs_self D]

theorem not_isometry_Ici_of_dist_bounded {D : ℝ} (hD : ∀ x y : X, dist x y ≤ D)
    (f : Ici (0 : ℝ) → X) : ¬ Isometry f := by
  intro hf
  let t : Ici (0 : ℝ) := ⟨|D| + 1, by change 0 ≤ |D| + 1; positivity⟩
  let z : Ici (0 : ℝ) := ⟨0, by simp⟩
  have h := hD (f t) (f z)
  rw [hf.dist_eq] at h
  change |(|D| + 1) - 0| ≤ D at h
  rw [sub_zero, abs_of_pos (by positivity)] at h
  linarith [le_abs_self D]

theorem not_nonempty_real_Ici : ¬ Nonempty (ℝ ≃ᵢ Ici (0 : ℝ)) := by
  rintro ⟨e⟩
  exact not_nonempty_isometryEquiv_of_endpoint (⟨0, by simp⟩ : Ici (0 : ℝ))
    ((isEndpoint_Ici_iff _).mpr rfl) not_isEndpoint_real ⟨e.symm⟩

theorem not_nonempty_real_Icc {L : ℝ} (hL : 0 < L) :
    ¬ Nonempty (ℝ ≃ᵢ Icc (0 : ℝ) L) := by
  rintro ⟨e⟩
  exact not_nonempty_isometryEquiv_of_endpoint (⟨0, le_rfl, hL.le⟩ : Icc (0 : ℝ) L)
    ((isEndpoint_Icc_iff hL.le _).mpr (Or.inl rfl)) not_isEndpoint_real ⟨e.symm⟩

theorem not_nonempty_real_addCircle {L : ℝ} (hL : 0 < L) :
    ¬ Nonempty (ℝ ≃ᵢ AddCircle L) := by
  rintro ⟨e⟩
  apply not_isometry_real_of_dist_bounded (D := L / 2) (fun x y => ?_) e e.isometry
  rw [dist_eq_norm]
  simpa only [abs_of_pos hL] using AddCircle.norm_le_half_period L (x := x - y) hL.ne'

theorem not_nonempty_Ici_Icc {L : ℝ} :
    ¬ Nonempty (Ici (0 : ℝ) ≃ᵢ Icc (0 : ℝ) L) := by
  rintro ⟨e⟩
  apply not_isometry_Ici_of_dist_bounded (D := L) (fun x y => ?_) e e.isometry
  change |(x : ℝ) - y| ≤ L
  rw [abs_le]
  constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]

theorem not_nonempty_Ici_addCircle {L : ℝ} (hL : 0 < L) :
    ¬ Nonempty (Ici (0 : ℝ) ≃ᵢ AddCircle L) :=
  not_nonempty_isometryEquiv_of_endpoint (⟨0, by simp⟩ : Ici (0 : ℝ))
    ((isEndpoint_Ici_iff _).mpr rfl) (not_isEndpoint_addCircle hL)

theorem not_nonempty_Icc_addCircle {L M : ℝ} (hL : 0 < L) (hM : 0 < M) :
    ¬ Nonempty (Icc (0 : ℝ) L ≃ᵢ AddCircle M) :=
  not_nonempty_isometryEquiv_of_endpoint (⟨0, le_rfl, hL.le⟩ : Icc (0 : ℝ) L)
    ((isEndpoint_Icc_iff hL.le _).mpr (Or.inl rfl)) (not_isEndpoint_addCircle hM)

theorem not_nonempty_subsingleton_models [Subsingleton X] :
    ¬ Nonempty (X ≃ᵢ ℝ) ∧ ¬ Nonempty (X ≃ᵢ Ici (0 : ℝ)) ∧
    (∀ L : ℝ, 0 < L → ¬ Nonempty (X ≃ᵢ Icc (0 : ℝ) L)) ∧
    (∀ L : ℝ, 0 < L → ¬ Nonempty (X ≃ᵢ AddCircle L)) := by
  have hdist {T : Type} [MetricSpace T] (e : X ≃ᵢ T) (a b : T) : dist a b = 0 := by
    rw [← e.symm.dist_eq, Subsingleton.elim (e.symm a) (e.symm b), dist_self]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨e⟩
    have h := hdist e 0 1
    norm_num at h
  · rintro ⟨e⟩
    have h := hdist e ⟨0, by simp⟩ ⟨1, by norm_num⟩
    norm_num [Subtype.dist_eq, Real.dist_eq] at h
  · intro L hL he
    obtain ⟨e⟩ := he
    have h := hdist e ⟨0, le_rfl, hL.le⟩ ⟨L, hL.le, le_rfl⟩
    simp only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hL] at h
    linarith
  · intro L hL he
    obtain ⟨e⟩ := he
    have h := hdist e ((L / 2 : ℝ) : AddCircle L) 0
    rw [dist_zero_right, AddCircle.norm_half_period_eq, abs_of_pos hL] at h
    linarith

end Metric
