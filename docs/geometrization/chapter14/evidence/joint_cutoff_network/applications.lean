import DifferentialGeometry.Analysis.Calculus.JointCutoffNetwork
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.FinCases

set_option autoImplicit false
open DifferentialGeometry.Analysis Set Metric

namespace JointCutoffRegression

private abbrev Space := EuclideanSpace ℝ (Option (Fin 2))
private def edgeProfile : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
private noncomputable def heightProfile : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
private noncomputable def smallProfile : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
private noncomputable def χ (x : ℝ) := 1 - smallProfile x
private noncomputable def u (i : Fin 2) : Space →L[ℝ] ℝ := EuclideanSpace.proj (some i)
private noncomputable def v : Space →L[ℝ] ℝ := EuclideanSpace.proj none
private noncomputable def point (t : ℝ) : Space := WithLp.toLp 2
  (fun i => i.elim 1 (fun j => if j = 0 then t else 10000))
private def weights (_ : Fin 2) : ℝ := 2
private noncomputable def W := jointCutoffNetwork 1 weights edgeProfile (fun _ => 1) heightProfile χ u v

private theorem profile_values : edgeProfile 0 = 1 ∧ edgeProfile 10000 = 0 ∧
    heightProfile 1 = 1 ∧ χ 0 = 0 ∧ χ 1 = 1 := by
  have h0 : smallProfile 0 = 1 := smallProfile.one_of_mem_closedBall (by norm_num [smallProfile])
  have h1 : smallProfile 1 = 0 := smallProfile.zero_of_le_dist (by norm_num [smallProfile])
  exact ⟨edgeProfile.one_of_mem_closedBall (by norm_num [edgeProfile]),
    edgeProfile.zero_of_le_dist (by norm_num [edgeProfile]),
    heightProfile.one_of_mem_closedBall (by norm_num [heightProfile]),
    by simp [χ, h0], by simp [χ, h1]⟩

theorem joint_block_changes_with_edge_coordinates :
    v (point 0) = v (point 10000) ∧
      W (point 0) none = WithLp.toLp 2 ((1 : ℝ), (1 : ℝ)) ∧
      W (point 10000) none = 0 := by
  obtain ⟨hf0, hf1, hh1, hc0, hc1⟩ := profile_values
  constructor
  · rfl
  constructor
  · rw [W, jointCutoffNetwork_none]
    simp [jointEdgeCutoff, edgeCutoff, point, u, v, Fin.sum_univ_two, hf0, hf1, hh1, hc1]
  · rw [W, jointCutoffNetwork_none]
    simp [jointEdgeCutoff, edgeCutoff, point, u, v, hf1, hh1, hc0]

theorem inactive_unbounded_coordinate_does_not_kill_active_block :
    u 1 (point 0) = 10000 ∧
      W (point 0) (some 0) = WithLp.toLp 2 ((0 : ℝ), (2 : ℝ)) ∧
      W (point 0) (some 1) = 0 := by
  obtain ⟨hf0, hf1, _, _, _⟩ := profile_values
  constructor
  · norm_num [u, point]
  constructor
  · rw [W, jointCutoffNetwork_some]
    simp [edgeCutoff, point, u, weights, hf0]
  · rw [W, jointCutoffNetwork_some]
    simp [edgeCutoff, point, u, weights, hf1]

theorem empty_edge_family_joint_cutoff_is_zero (x : ℝ) :
    jointEdgeCutoff (ι := Fin 0) 1 edgeProfile (fun _ => 1) heightProfile χ
      (fun i => Fin.elim0 i) (ContinuousLinearMap.id ℝ ℝ) x = 0 := by
  exact jointEdgeCutoff_eq_zero_of_all_edgeCutoff_zero profile_values.2.2.2.1 _ _
    (fun i => Fin.elim0 i)

private theorem bump_bounds {c : ℝ} (b : ContDiffBump c) :
    ∃ P : ℝ, 1 ≤ P ∧ (∀ x, ‖fderiv ℝ b x‖ ≤ P) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ b) x‖ ≤ P) := by
  have hD : ContDiff ℝ 2 (fderiv ℝ b) :=
    (b.contDiff : ContDiff ℝ 3 b).fderiv_right (by norm_num)
  have hDD : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ b)) := hD.fderiv_right (by norm_num)
  obtain ⟨A, hA⟩ := hD.continuous.norm.bddAbove_range_of_hasCompactSupport
    (b.hasCompactSupport.fderiv ℝ |>.comp_left norm_zero)
  obtain ⟨B, hB⟩ := hDD.continuous.norm.bddAbove_range_of_hasCompactSupport
    ((b.hasCompactSupport.fderiv ℝ).fderiv ℝ |>.comp_left norm_zero)
  refine ⟨max 1 (max A B), le_max_left _ _, ?_, ?_⟩
  · exact fun x => (hA (mem_range_self x)).trans ((le_max_left A B).trans (le_max_right _ _))
  · exact fun x => (hB (mem_range_self x)).trans ((le_max_right A B).trans (le_max_right _ _))

theorem actual_nonzero_network_has_global_bounds :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ x : Space,
      ‖W x‖ ≤ 20 * Real.sqrt 3 ∧
      ‖fderiv ℝ W x‖ ≤ Real.sqrt 3 * (2 + 1800 * P ^ 3) ∧
      ‖fderiv ℝ (fderiv ℝ W) x‖ ≤ 2160 * Real.sqrt 3 * P ^ 3 := by
  obtain ⟨Pf, hPf, hDf, hDDf⟩ := bump_bounds edgeProfile
  obtain ⟨Ph, hPh, hDh, hDDh⟩ := bump_bounds heightProfile
  obtain ⟨Pc, hPc, hDc, hDDc⟩ := bump_bounds smallProfile
  let P := max Pf (max Ph Pc)
  have hP : 1 ≤ P := hPf.trans (le_max_left _ _)
  have hfP : Pf ≤ P := le_max_left _ _
  have hhP : Ph ≤ P := (le_max_left _ _).trans (le_max_right _ _)
  have hcP : Pc ≤ P := (le_max_right _ _).trans (le_max_right _ _)
  have hχ : ContDiff ℝ 2 χ := contDiff_const.sub smallProfile.contDiff
  have hdχ : fderiv ℝ χ = fun x => -fderiv ℝ smallProfile x := by
    funext x
    exact fderiv_const_sub 1
  have hDχ (x : ℝ) : ‖fderiv ℝ χ x‖ ≤ P := by
    rw [hdχ, norm_neg]
    exact (hDc x).trans hcP
  have hDDχ (x : ℝ) : ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ P := by
    rw [hdχ, fderiv_fun_neg, norm_neg]
    exact (hDDc x).trans hcP
  have hu (i : Fin 2) : ‖u i‖ ≤ 1 := by
    apply (u i).opNorm_le_bound (by norm_num)
    intro x
    change ‖x (some i)‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using PiLp.norm_apply_le x (some i)
  have hv : ‖v‖ ≤ 1 := by
    apply v.opNorm_le_bound (by norm_num)
    intro x
    change ‖x none‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using PiLp.norm_apply_le x none
  have hfs : tsupport edgeProfile ⊆ Icc (-9) 9 := by
    rw [edgeProfile.tsupport_eq]
    intro x hx
    have hh : |x| ≤ 2 := by simpa [edgeProfile, mem_closedBall, Real.dist_eq] using hx
    exact ⟨by linarith [(abs_le.mp hh).1], by linarith [(abs_le.mp hh).2]⟩
  have hhs : tsupport heightProfile ⊆ Icc (1 / 5) 9 := by
    rw [heightProfile.tsupport_eq]
    intro x hx
    have hh : |x - 1| ≤ 1 / 2 := by simpa [heightProfile, mem_closedBall, Real.dist_eq] using hx
    exact ⟨by linarith [(abs_le.mp hh).1], by linarith [(abs_le.mp hh).2]⟩
  refine ⟨P, hP, fun x => ?_⟩
  have hb := jointCutoffNetwork_bounds (g := fun _ => (1 : ℝ)) edgeProfile.contDiff contDiff_const heightProfile.contDiff hχ
    (Δ := 1) (by norm_num) hP (fun _ => ⟨edgeProfile.nonneg, edgeProfile.le_one⟩)
    (fun _ => by norm_num) (fun _ => ⟨heightProfile.nonneg, heightProfile.le_one⟩)
    (fun y => by dsimp [χ]; constructor <;> linarith [smallProfile.nonneg' y, smallProfile.le_one (x := y)])
    (fun y => (hDf y).trans hfP) (fun _ => by simp; linarith)
    (fun y => (hDh y).trans hhP) hDχ
    (fun y => (hDDf y).trans hfP) (fun _ => by simp; linarith)
    (fun y => (hDDh y).trans hhP) hDDχ hfs hhs weights (fun _ => by norm_num [weights]) u v hu hv x
  dsimp only at hb
  norm_num [Fintype.card_fin, W] at hb ⊢
  exact ⟨hb.1, hb.2.1.trans_eq (by ring), hb.2.2.trans_eq (by ring)⟩

end JointCutoffRegression

#print axioms JointCutoffRegression.joint_block_changes_with_edge_coordinates
#print axioms JointCutoffRegression.inactive_unbounded_coordinate_does_not_kill_active_block
#print axioms JointCutoffRegression.empty_edge_family_joint_cutoff_is_zero
#print axioms JointCutoffRegression.actual_nonzero_network_has_global_bounds
