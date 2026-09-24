import DifferentialGeometry.Topology.Homotopy.BallPrism
import DifferentialGeometry.Topology.ClosedCover

noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

theorem exists_continuous_ball_homotopy_extension
    (f : C(closedBall (0 : E) 1, X))
    (H : C(unitInterval × sphere (0 : E) 1, X))
    (hH : ∀ x : sphere (0 : E) 1, H (0, x) = f ⟨x.val, sphere_subset_closedBall x.property⟩) :
    ∃ F : C(unitInterval × closedBall (0 : E) 1, X),
      (∀ x, F (0, x) = f x) ∧
      ∀ t (x : sphere (0 : E) 1), F (t, ⟨x.val, sphere_subset_closedBall x.property⟩) = H (t, x) := by
  let P := unitInterval × closedBall (0 : E) 1
  let S : Bool → Set P := fun b => if b then {z | 1 - z.1.val / 2 ≤ ‖(z.2 : E)‖}
    else {z | ‖(z.2 : E)‖ ≤ 1 - z.1.val / 2}
  let φ : ∀ b, C(S b, X) := fun b => by
    cases b
    · exact ⟨fun z => f (ballPrismRetract z.val).2,
        f.continuous.comp ((continuous_ballPrismRetract (E := E)).snd.comp continuous_subtype_val)⟩
    · exact ⟨fun z => H ((ballPrismRetract z.val).1,
        ⟨((ballPrismRetract z.val).2 : E), ballPrismRetract_position_sphere z.val z.property⟩), by
        apply H.continuous.comp
        exact (((continuous_ballPrismRetract (E := E)).fst.comp continuous_subtype_val).prodMk
          (Continuous.subtype_mk
            (continuous_subtype_val.comp
              ((continuous_ballPrismRetract (E := E)).snd.comp continuous_subtype_val)) _))⟩
  have hφ : ∀ (i j : Bool) (z : P) (hi : z ∈ S i) (hj : z ∈ S j),
      φ i ⟨z, hi⟩ = φ j ⟨z, hj⟩ := by
    intro i j z hi hj
    cases i <;> cases j
    · rfl
    · change f (ballPrismRetract z).2 = H ((ballPrismRetract z).1, _)
      rw [ballPrismRetract_time_zero z hi]
      exact (hH ⟨((ballPrismRetract z).2 : E), ballPrismRetract_position_sphere z hj⟩).symm
    · change H ((ballPrismRetract z).1, _) = f (ballPrismRetract z).2
      rw [ballPrismRetract_time_zero z hj]
      exact hH ⟨((ballPrismRetract z).2 : E), ballPrismRetract_position_sphere z hi⟩
    · rfl
  have hcov : ⋃ b, S b = univ := by
    apply eq_univ_of_forall
    intro z
    rcases le_total ‖(z.2 : E)‖ (1 - z.1.val / 2) with h | h
    · exact mem_iUnion.mpr ⟨false, h⟩
    · exact mem_iUnion.mpr ⟨true, h⟩
  have hclosed : ∀ b, IsClosed (S b) := by
    intro b
    cases b <;> apply isClosed_le
    · exact continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
    · exact continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)
    · exact continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)
    · exact continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
  let F := ContinuousMap.liftClosedCover S φ hφ hcov hclosed (locallyFinite_of_finite _)
  refine ⟨F, ?_, ?_⟩
  · intro x
    have hx : (0, x) ∈ S false := by
      change ‖(x : E)‖ ≤ 1 - (0 : ℝ) / 2
      simpa only [zero_div, sub_zero, mem_closedBall, dist_zero_right] using x.property
    have hf := ContinuousMap.liftClosedCover_coe (S := S) (φ := φ)
      (hφ := hφ) (hcov := hcov) (hclosed := hclosed)
      (hfinite := locallyFinite_of_finite _) (i := false) ⟨(0, x), hx⟩
    change F (0, x) = f (ballPrismRetract (0, x)).2 at hf
    simpa only [ballPrismRetract_bottom] using hf
  · intro t x
    have hx : (t, (⟨x.val, sphere_subset_closedBall x.property⟩ : closedBall (0 : E) 1)) ∈ S true := by
      change 1 - t.val / 2 ≤ ‖x.val‖
      rw [mem_sphere_zero_iff_norm.mp x.property]
      linarith [t.property.1]
    have hf := ContinuousMap.liftClosedCover_coe (S := S) (φ := φ)
      (hφ := hφ) (hcov := hcov) (hclosed := hclosed)
      (hfinite := locallyFinite_of_finite _) (i := true) ⟨_, hx⟩
    change F (t, _) = H ((ballPrismRetract (t, _)).1, _) at hf
    have hr := ballPrismRetract_side t
      (⟨x.val, sphere_subset_closedBall x.property⟩ : closedBall (0 : E) 1) x.property
    apply hf.trans
    apply congrArg H
    apply Prod.ext
    · exact congrArg (fun z : unitInterval × closedBall (0 : E) 1 => z.1) hr
    · apply Subtype.ext
      exact congrArg (fun z : unitInterval × closedBall (0 : E) 1 => (z.2 : E)) hr

end DifferentialGeometry.Topology
