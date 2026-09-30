# Full AC87 independent acceptance

Two public theorems and one private helper in two leaves add three owned declarations. The357-module gate checks1627 declarations in3192 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import regression lint is silent; eight reports cover both public production theorems, the new actual uniform application and both-direction incomplete-source transfer, plus four retained cone-regression assertions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

Root and same_lines independently read the full frozen proofs and source contracts. The actual uniform test was independently implemented, read by root and the authoring agent, and compiled against canonical production leaves. The metric transfer test was independently read by root. Targeted production imports avoid the tactic umbrella.

The uniform theorem chooses epsilon(n,delta) before every input space, point, model and map. It extracts only the first cone model, transfers convergence through the ORIGINAL first KL maps, and moves the ORIGINAL second basepoints on the SAME proper limit via AC81. Distinctness follows from retained separation1. The ORIGINAL second KL maps transfer convergence directly to this same newly pointed target, and85 supplies its second radial cone. The same two-apex line yields an exact product normalized at the second point. The accepted exact-limit theorem's explicit ULift moves the small factor to the source universe before contradicting original delta-splitting failure. No hidden regularity of either KL map or completeness of the source/second model is used. Independent input universes remain explicit.

The generic stability iff is tested in BOTH directions using actual inclusion KL maps from the genuinely incomplete dense union of planar rays to the SAME Euclidean plane. The maps equal the original inclusion on all controlled source points, their errors1/(i+2) tend to0, and their own coverage is proved. The uniform theorem is applied at its actual unknown returned epsilon for n1/delta1/2: original real source points5,4, first cone apex-2 and map x-7, second apex10 and reversed map14-x. Global comparison, length curves and both cone laws are proved. Whole-map formulas retain remote points outside the tested approximation balls. The final production map is an actual normalized whole-source splitting at the original point4.

The source theorem's additional completeness/length hypotheses on Z and geometry on D are unnecessary for this documented one-model proof. The original written AC87 is a direct specialization of the stronger proved statement. No explicit modulus, monotonicity, equality of pointed-GH closeness conventions, strainer theorem or compatibility theorem is asserted. Full87 is proved;83 convention equivalence and the separate sharp-margin/tangent-route tasks remain. Blueprint207 and migration interfaces are unchanged.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.OverlappingConeSplitting
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import DifferentialGeometry.Geometry.Comparison.OppositeAngleExcess
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import Mathlib.Tactic

set_option autoImplicit false

namespace GCAC85Review

open GC.MetricGeometry Set Metric Filter
open scoped NNReal Topology

private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private noncomputable def v (a b : ℝ) : Plane := WithLp.toLp 2 ![a, b]
private def rays : Set Plane := {x | x 0 ≠ 0 ∨ x 1 = 0}
private abbrev Source := rays
private noncomputable def apex : Source := ⟨0, Or.inr rfl⟩

private theorem vector_eta (x : Plane) : v (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> rfl

private theorem horizontal_dist (a b c : ℝ) : dist (v a c) (v b c) = |a - b| := by
  apply (sq_eq_sq₀ dist_nonneg (abs_nonneg _)).mp
  simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, v,
    Real.dist_eq, sq_abs]
  simp

private noncomputable def sourceCone : RadialConeData apex where
  map t x := ⟨(t : ℝ) • x.val, by
    by_cases ht : t = 0
    · subst t
      right
      simp
    · rcases x.property with hx | hx
      · left
        change (t : ℝ) * x.val 0 ≠ 0
        exact mul_ne_zero (by exact_mod_cast ht) hx
      · right
        change (t : ℝ) * x.val 1 = 0
        rw [hx, mul_zero]⟩
  map_zero x := by apply Subtype.ext; simp [apex]
  map_one x := by apply Subtype.ext; simp
  dist_sq s t x y := by
    simp only [Subtype.dist_eq, radialConeKernel, apex, EuclideanSpace.dist_sq_eq,
      Fin.sum_univ_two, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, Real.dist_eq, sq_abs]
    ring

private noncomputable def inclusionApprox {R ε : ℝ} (hε : 0 < ε) (hR : ε < R) :
    PointedBallApprox apex (0 : Plane) R ε where
  error_pos := hε
  error_lt_radius := hR
  toFun x := x.val.val
  basepoint := rfl
  distortion x y := by
    change |dist x.val.val y.val.val - dist x.val.val y.val.val| < ε
    simpa only [sub_self, abs_zero] using hε
  coverage y hy := by
    by_cases hy0 : y 0 = 0
    · let z : Source := ⟨v (ε / 2) (y 1), Or.inl (by change ε / 2 ≠ 0; positivity)⟩
      have hdist : dist y z.val = ε / 2 := by
        have he : y = v 0 (y 1) := by rw [← hy0]; exact (vector_eta y).symm
        rw [he]
        change dist (v 0 (y 1)) (v (ε / 2) (y 1)) = ε / 2
        rw [horizontal_dist]
        rw [zero_sub, abs_neg, abs_of_pos (by positivity : 0 < ε / 2)]
      have hz : dist z apex ≤ R := by
        have hh := dist_triangle z.val y (0 : Plane)
        rw [dist_comm z.val y, hdist] at hh
        change dist z.val (0 : Plane) ≤ R
        linarith
      exact ⟨⟨z, hz⟩, by simpa only [hdist] using (by linarith : ε / 2 < ε)⟩
    · let z : Source := ⟨y, Or.inl hy0⟩
      refine ⟨⟨z, ?_⟩, ?_⟩
      · change dist y (0 : Plane) ≤ R
        linarith
      · change dist y y < ε
        simpa only [dist_self] using hε

private theorem source_not_complete : ¬ CompleteSpace Source := by
  intro h
  let := h
  have hc : IsClosed rays := by
    simpa only [Subtype.range_val] using
      (isometry_subtype_coe (s := rays)).isUniformInducing.isComplete_range.isClosed
  have hcl : v 0 1 ∈ closure rays := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨v (ε / 2) 1, Or.inl (by change ε / 2 ≠ 0; positivity), ?_⟩
    rw [horizontal_dist]
    rw [zero_sub, abs_neg, abs_of_pos (by positivity : 0 < ε / 2)]
    linarith
  have hm := hc.closure_subset hcl
  change (0 : ℝ) ≠ 0 ∨ (1 : ℝ) = 0 at hm
  norm_num at hm

private theorem original_pointed_convergence :
    PointedGHConverges (fun _ : ℕ => apex) (0 : Plane) :=
  ⟨inferInstance, fun R ε hε hR => Eventually.of_forall (fun _ => ⟨inclusionApprox (R := R) (ε := ε) hε hR⟩)⟩

private theorem incomplete_cones_converge_to_same_plane_cone :
    Nonempty (RadialConeData (0 : Plane)) :=
  original_pointed_convergence.nonempty_radialConeData (fun _ => sourceCone)

private theorem same_limit_has_full_two_parameter_radial_identity :
    ∃ H : RadialConeData (0 : Plane),
      ∀ (s t : ℝ≥0) (x y : Plane),
        dist (H.map s x) (H.map t y) ^ 2 =
          (s : ℝ) ^ 2 * dist 0 x ^ 2 + (t : ℝ) ^ 2 * dist 0 y ^ 2 -
            2 * (s : ℝ) * (t : ℝ) * radialConeKernel 0 x y := by
  obtain ⟨H⟩ := incomplete_cones_converge_to_same_plane_cone
  exact ⟨H, H.dist_sq⟩

#print axioms source_not_complete
#print axioms original_pointed_convergence
#print axioms incomplete_cones_converge_to_same_plane_cone
#print axioms same_limit_has_full_two_parameter_radial_identity

end GCAC85Review

#lint- only unusedArguments simpNF synTaut

namespace GCAC85Review

open GC.MetricGeometry Set Metric Filter
open scoped Topology

private theorem varying_kl_preserves_same_limit_both_directions :
    ¬ CompleteSpace Source ∧
    ∃ (ε : ℕ → ℝ) (F : ∀ i, KleinerLottApprox apex (0 : Plane) (ε i)),
      Tendsto ε atTop (𝓝 0) ∧
      (∀ i (x : Source), dist x apex < (ε i)⁻¹ → (F i).toFun x = x.val) ∧
      PointedGHConverges (fun _ : ℕ => apex) (0 : Plane) ∧
      PointedGHConverges (fun _ : ℕ => (0 : Plane)) (0 : Plane) := by
  classical
  let ε : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 2)
  have hepos (i : ℕ) : 0 < ε i := by dsimp [ε]; positivity
  have heone (i : ℕ) : ε i < 1 := by
    dsimp [ε]
    exact (div_lt_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i])
  have hezero : Tendsto ε atTop (𝓝 0) := by
    have hh : Tendsto (fun i : ℕ => (i : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [ε, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hh
  let f (i : ℕ) : PointedBallApprox apex (0 : Plane) ((ε i)⁻¹ + ε i) (ε i / 4) :=
    inclusionApprox (by linarith [hepos i]) (by linarith [hepos i, inv_pos.mpr (hepos i)])
  let F (i : ℕ) : KleinerLottApprox apex (0 : Plane) (ε i) :=
    (f i).toKleinerLott (hepos i) (heone i)
  have hequiv := pointedGHConverges_iff_of_kleinerLott_sequence (z := (0 : Plane)) F hezero
  have hsource := hequiv.mpr (PointedGHConverges.const (0 : Plane))
  have htarget := hequiv.mp hsource
  refine ⟨source_not_complete, ε, F, hezero, ?_, hsource, htarget⟩
  intro i x hx
  simp only [F, PointedBallApprox.toKleinerLott, dite_eq_left hx]
  rfl

#print axioms varying_kl_preserves_same_limit_both_directions

end GCAC85Review

#lint- only unusedArguments simpNF synTaut

open Set Metric Filter GC.MetricGeometry
open scoped Topology NNReal
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GCOverlappingConeReview

private theorem same_side_zero {κ : ℝ} (hκ : 0 ≤ κ) (x a b : ℝ) (ha : a ≠ x) (hb : b ≠ x)
    (hs : (x ≤ a ∧ x ≤ b) ∨ (a ≤ x ∧ b ≤ x)) :
    comparisonAngleNegCurvature κ (dist x a) (dist x b) (dist a b) = 0 := by
  have heq : dist a b = |dist x a - dist x b| := by
    rcases hs with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonpos (sub_nonpos.mpr ha'), abs_of_nonpos (sub_nonpos.mpr hb')]
      have h : -(x - a) - -(x - b) = a - b := by ring
      rw [h]
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonneg (sub_nonneg.mpr ha'), abs_of_nonneg (sub_nonneg.mpr hb')]
      have h : (x - a) - (x - b) = b - a := by ring
      rw [h, abs_sub_comm]
  rw [heq]
  exact comparisonAngleNegCurvature_abs_sub hκ (dist_pos.mpr ha.symm) (dist_pos.mpr hb.symm)

private theorem real_comparison {κ : ℝ} (hκ : 0 ≤ κ) : fourPointComparison κ (univ : Set ℝ) := by
  intro x _ a _ b _ c _ ha hb hc
  have hab := (comparisonAngleNegCurvature_mem_Icc κ (dist x a) (dist x b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc κ (dist x b) (dist x c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc κ (dist x c) (dist x a) (dist c a)).2
  rcases le_total x a with hxa | hax <;> rcases le_total x b with hxb | hbx <;>
    rcases le_total x c with hxc | hcx
  all_goals first
    | have hz := same_side_zero hκ x a b ha hb (Or.inl ⟨hxa, hxb⟩); linarith
    | have hz := same_side_zero hκ x a b ha hb (Or.inr ⟨hax, hbx⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inl ⟨hxb, hxc⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inr ⟨hbx, hcx⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inl ⟨hxc, hxa⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inr ⟨hcx, hax⟩); linarith


private theorem real_segments (x y : ℝ) :
    ∃ f : unitInterval → ℝ, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ℝ := fun t => (1 - (t : ℝ)) * x + (t : ℝ) * y
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  change |(1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y)| =
    |x - y| * |(s : ℝ) - t|
  rw [show (1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y) =
    (y - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm y x]

private noncomputable def realCone (p : ℝ) : RadialConeData p where
  map t x := p + (t : ℝ) * (x - p)
  map_zero x := by simp
  map_one x := by simp
  dist_sq s t x y := by
    simp only [radialConeKernel, Real.dist_eq, sq_abs]
    ring


private def shift : ℝ ≃ᵢ ℝ where
  toFun x := x - 7
  invFun x := x + 7
  left_inv x := by ring
  right_inv x := by ring
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    simp only [Real.dist_eq]
    congr 1
    ring

private def reverseShift : ℝ ≃ᵢ ℝ where
  toFun x := 14 - x
  invFun x := 14 - x
  left_inv x := by ring
  right_inv x := by ring
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    simp only [Real.dist_eq]
    rw [show 14 - x - (14 - y) = y - x by ring, abs_sub_comm]

theorem original_real_overlapping_cones :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∃ (φ : KleinerLottApprox (5 : ℝ) (-2 : ℝ) ε)
        (ψ : KleinerLottApprox (4 : ℝ) (10 : ℝ) ε),
      (∀ x, φ.toFun x = x - 7) ∧ (∀ x, ψ.toFun x = 14 - x) ∧
      φ.toFun (5 + 2 * ε⁻¹) = -2 + 2 * ε⁻¹ ∧
      ψ.toFun (4 + 2 * ε⁻¹) = 10 - 2 * ε⁻¹ ∧
      ∃ (W : Type) (m : MetricSpace W), letI := m
        ∃ (w : W) (F : KleinerLottApprox (4 : ℝ)
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), w)) (1 / 2)),
        F.toFun 4 = WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), w) := by
  obtain ⟨ε, hε, hεone, h⟩ := exists_overlapping_cone_splitting_parameter
    (n := 1) (by norm_num) (δ := 1 / 2) (by norm_num) (by norm_num)
  let φ : KleinerLottApprox (5 : ℝ) (-2 : ℝ) ε :=
    shift.toKleinerLottApprox (by norm_num [shift]) hε hεone
  let ψ : KleinerLottApprox (4 : ℝ) (10 : ℝ) ε :=
    reverseShift.toKleinerLottApprox (by norm_num [reverseShift]) hε hεone
  obtain ⟨W, m, w, F⟩ := h ℝ ℝ ℝ 5 4 (-2) 10 (by norm_num [Real.dist_eq])
    (arbitrarily_short_curves_of_metric_segments real_segments)
    (by rw [Real.dimH_univ]; norm_num) (real_comparison le_rfl)
    (realCone (-2)) (realCone 10) φ ψ
  let := m
  obtain ⟨F⟩ := F
  refine ⟨ε, hε, hεone, φ, ψ, (fun _ => rfl), (fun _ => rfl), ?_, ?_,
    W, m, w, F, F.basepoint⟩
  · change 5 + 2 * ε⁻¹ - 7 = -2 + 2 * ε⁻¹
    ring
  · change 14 - (4 + 2 * ε⁻¹) = 10 - 2 * ε⁻¹
    ring

end GCOverlappingConeReview

#print axioms GC.MetricGeometry.pointedGHConverges_iff_of_kleinerLott_sequence
#print axioms GC.MetricGeometry.exists_overlapping_cone_splitting_parameter
#print axioms GCOverlappingConeReview.original_real_overlapping_cones
#lint- only unusedArguments simpNF synTaut
```
