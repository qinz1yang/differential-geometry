import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Affine.AddTorsor

noncomputable section

open ContinuousMap Metric
open scoped unitInterval

namespace DifferentialGeometry.Topology

variable {E : Type*} [normE : NormedAddCommGroup E] [NormedSpace ℝ E]

private def sphereDirection (a : sphere (0 : E) 1) (z : E) : sphere (0 : E) 1 := by
  classical
  exact if hz : z = 0 then a else
    ⟨‖z‖⁻¹ • z, by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩

private theorem sphereDirection_continuousOn (a : sphere (0 : E) 1) :
    ContinuousOn (sphereDirection a) {z | z ≠ 0} := by
  rw [_root_.Topology.IsInducing.subtypeVal.continuousOn_iff]
  apply ((continuous_norm.continuousOn.inv₀ fun z hz => norm_ne_zero_iff.mpr hz).smul
    continuousOn_id).congr
  intro z hz
  change z ≠ 0 at hz
  simp [sphereDirection, hz]

private def radialTime (z : E) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (2 * ‖z‖ - 1)

omit [NormedSpace ℝ E] in
private theorem radialTime_continuous : Continuous (radialTime (E := E)) := by
  unfold radialTime
  fun_prop

private theorem exists_continuous_closedBall_of_nullhomotopic_unit
    {X : Type*} [TopologicalSpace X] {f : C(sphere (0 : E) 1, X)} (hf : f.Nullhomotopic) :
    ∃ u : C(closedBall (0 : E) 1, X), u.comp (ContinuousMap.inclusion sphere_subset_closedBall) = f := by
  classical
  obtain ⟨x, ⟨H⟩⟩ := hf
  rcases isEmpty_or_nonempty (sphere (0 : E) 1) with hE | hE
  · let := hE
    refine ⟨ContinuousMap.const _ x, ?_⟩
    ext z
    exact isEmptyElim z
  let a : sphere (0 : E) 1 := Classical.choice hE
  let F := H.symm
  let g : E → X := fun z =>
    if ‖z‖ ≤ 1 / 2 then x else F (radialTime z, sphereDirection a z)
  have hg : Continuous g := by
    apply continuous_if_le continuous_norm continuous_const continuousOn_const
    · apply F.continuous.comp_continuousOn
      apply radialTime_continuous.continuousOn.prodMk
      apply sphereDirection_continuousOn a |>.mono
      intro z hz
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by norm_num) hz))
    · intro z hz
      have ht : radialTime z = 0 := by
        change Set.projIcc 0 1 zero_le_one (2 * ‖z‖ - 1) = 0
        apply (Set.projIcc_eq_left (by norm_num : (0 : ℝ) < 1)).mpr
        linarith
      simp only [ht, F.apply_zero, const_apply]
  let u : C(closedBall (0 : E) 1, X) := ⟨fun z => g z, hg.comp continuous_subtype_val⟩
  refine ⟨u, ?_⟩
  ext z
  have hz : ‖(z : E)‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
  have hzne : (z : E) ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have ht : radialTime (z : E) = 1 := by
    change Set.projIcc 0 1 zero_le_one (2 * ‖(z : E)‖ - 1) = 1
    apply (Set.projIcc_eq_right (by norm_num : (0 : ℝ) < 1)).mpr
    rw [hz]
    norm_num
  have hd : sphereDirection a (z : E) = z := by
    apply Subtype.ext
    simp [sphereDirection, hzne, hz]
  change g (z : E) = f z
  dsimp [g]
  rw [hz, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2), ht, hd]
  exact F.apply_one z

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

variable {E : Type*} [normE : NormedAddCommGroup E]
variable [spaceE : NormedSpace ℝ E]
variable {P : Type*} [metricP : MetricSpace P] [torsorEP : NormedAddTorsor E P]

private def sphereDilation (c : P) {r : ℝ} (hr : 0 < r) :
    sphere (0 : E) 1 ≃ₜ sphere c r :=
  (DilationEquiv.smulTorsor c (k := r) hr.ne').toHomeomorph.sets (by
    ext x
    simp only [mem_sphere, dist_zero_right, DilationEquiv.coe_toHomeomorph,
      Set.mem_preimage, DilationEquiv.smulTorsor_apply, dist_vadd_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_eq_left₀ hr.ne').symm)

private def closedBallDilation (c : P) {r : ℝ} (hr : 0 < r) :
    closedBall (0 : E) 1 ≃ₜ closedBall c r :=
  (DilationEquiv.smulTorsor c (k := r) hr.ne').toHomeomorph.sets (by
    ext x
    simp only [mem_closedBall, dist_zero_right, DilationEquiv.coe_toHomeomorph,
      Set.mem_preimage, DilationEquiv.smulTorsor_apply, dist_vadd_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_iff_le_one_right hr).symm)

include E spaceE torsorEP

private theorem exists_continuous_closedBall_of_nullhomotopic_pos
    {c : P} {r : ℝ} (hr : 0 < r) {X : Type*} [TopologicalSpace X]
    {f : C(sphere c r, X)} (hf : f.Nullhomotopic) :
    ∃ u : C(closedBall c r, X), u.comp (ContinuousMap.inclusion sphere_subset_closedBall) = f := by
  let es := sphereDilation c hr
  let eb := closedBallDilation c hr
  obtain ⟨u, hu⟩ := exists_continuous_closedBall_of_nullhomotopic_unit
    (hf.comp_left (es : C(sphere (0 : E) 1, sphere c r)))
  refine ⟨u.comp (eb.symm : C(closedBall c r, closedBall (0 : E) 1)), ?_⟩
  ext z
  have hz := congrArg (fun g : C(sphere (0 : E) 1, X) => g (es.symm z)) hu
  change u (eb.symm ((ContinuousMap.inclusion sphere_subset_closedBall) z)) = f z
  change u ((ContinuousMap.inclusion sphere_subset_closedBall) (es.symm z)) =
    f (es (es.symm z)) at hz
  rw [es.apply_symm_apply] at hz
  exact hz

private theorem exists_continuous_closedBall_of_nullhomotopic_nonneg
    {c : P} {r : ℝ} (hr : 0 ≤ r) {X : Type*} [TopologicalSpace X]
    {f : C(sphere c r, X)} (hf : f.Nullhomotopic) :
    ∃ u : C(closedBall c r, X), u.comp (ContinuousMap.inclusion sphere_subset_closedBall) = f := by
  rcases eq_or_lt_of_le hr with hr | hr
  · subst r
    have hs : closedBall c 0 ⊆ sphere c 0 := by simp
    exact ⟨f.comp (ContinuousMap.inclusion hs), by ext; rfl⟩
  · exact exists_continuous_closedBall_of_nullhomotopic_pos hr hf

theorem exists_continuous_closedBall_of_nullhomotopic
    {c : P} {r : ℝ} {X : Type*} [TopologicalSpace X]
    {f : C(sphere c r, X)} (hf : f.Nullhomotopic) :
    ∃ u : C(closedBall c r, X), u.comp (ContinuousMap.inclusion sphere_subset_closedBall) = f := by
  by_cases hr : 0 ≤ r
  · exact exists_continuous_closedBall_of_nullhomotopic_nonneg hr hf
  · obtain ⟨x, _⟩ := hf
    refine ⟨ContinuousMap.const _ x, ?_⟩
    ext z
    have hz : (z : P) ∈ (∅ : Set P) := by
      simpa only [sphere_eq_empty_of_neg (lt_of_not_ge hr)] using z.property
    exact hz.elim

theorem nullhomotopic_of_exists_continuous_closedBall
    {c : P} {r : ℝ} (hr : 0 ≤ r) {X : Type*} [TopologicalSpace X]
    {f : C(sphere c r, X)}
    (hf : ∃ u : C(closedBall c r, X),
      u.comp (ContinuousMap.inclusion sphere_subset_closedBall) = f) : f.Nullhomotopic := by
  have hcontract : ContractibleSpace (closedBall c r) := by
    rcases eq_or_lt_of_le hr with hr | hr
    · subst r
      rw [closedBall_zero]
      infer_instance
    · let : ContractibleSpace (closedBall (0 : E) 1) := contractibleSpace_closedBall (by norm_num)
      exact (closedBallDilation c hr).symm.contractibleSpace
  let := hcontract
  obtain ⟨u, hu⟩ := hf
  rw [← hu]
  exact ((id_nullhomotopic (closedBall c r)).comp_left
    (ContinuousMap.inclusion sphere_subset_closedBall)).comp_right u

theorem nullhomotopic_iff_exists_continuous_closedBall
    {c : P} {r : ℝ} (hr : 0 ≤ r) {X : Type*} [TopologicalSpace X]
    (f : C(sphere c r, X)) :
    f.Nullhomotopic ↔ ∃ u : C(closedBall c r, X),
      u.comp (ContinuousMap.inclusion sphere_subset_closedBall) = f :=
  ⟨exists_continuous_closedBall_of_nullhomotopic,
    nullhomotopic_of_exists_continuous_closedBall hr⟩

end DifferentialGeometry.Topology
