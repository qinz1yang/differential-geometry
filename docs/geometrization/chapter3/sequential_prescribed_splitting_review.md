# Fixed-rank sequential splitting review

Three public theorems in two leaves add three owned declarations. The 320-module gate checks 1405 declarations in 3155 jobs. All transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and review-driver unusedArguments/simpNF/synTaut lint is silent. The accepted-import driver emits ten requested standard axiom reports. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning lies outside these closures. Static audit passes; no full migrated root, PDF/Overleaf build or human approval is claimed.

An agent implemented the scalar/vector bridge and original sequential producer. A second agent independently checked both proofs and the source hypotheses. Root read both complete statements and proofs, checked the composition of the actual extraction maps, and constructed the original-input sequential test. The same subsequence and factor precede the quantifier over every fixed delta. Original endpoints retain the composed indices. Scalar convergence is simultaneous over all finite coordinates, vector tolerance uses eta/(k+1), and max(S,1) supplies the older bridge on every requested radius. Rank zero requires no special unproved bound. Exact first-coordinate equality is a whole-source assertion, while distortion and coverage remain on the KL balls.

The independent generic bridge test uses the actual identity approximation on Euclidean(Fin k) times the real line. Its prescribed map equals (1+alpha_i) times the Euclidean coordinate inside the growing domain and twice that coordinate outside. The fixed-ball component errors tend to zero. An explicit outside point has coordinate error tending to infinity, yet the produced KL map has the exact prescribed first coordinate there. The empty-rank application is also compiled. This verifies the scope without assuming global approximation of the original identity map.

The original sequential tests start from complete real sources with sigma_i=1/(i+1), actual opposite endpoints, proved short curves, local comparison and dimension. They invoke the new producer with NO supplied limit, at ranks one and zero, retaining its entire factor geometry and all-delta map conclusion. A further rank-one application uses the SAME returned subsequence and factor: at the original point twice the endpoint radius, outside the fixed KL control ball, the first coordinate is exactly zero, and the whole-source distance-coordinate formula is retained. This exercises the accepted compactness, AC66 and distance-coordinate bridge together.

This closes the fixed-rank sequential input for AC55. The uniform parameter contradiction is separate. Chapters 3–4 remain unfinished; blueprint 207 and migration interfaces are unchanged.

```lean
import Mathlib.Tactic
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import DifferentialGeometry.Geometry.Metric.Approximation.ScalarPrescribedCoordinates
import DifferentialGeometry.Geometry.Metric.Approximation.SequentialPrescribedSplitting


open Set Filter Metric
open scoped Topology

namespace GCScalarPrescribedCoordinatesReview

open GC.MetricGeometry

private abbrev Space (k : ℕ) := WithLp 2 (EuclideanSpace ℝ (Fin k) × ℝ)
private def base (k : ℕ) : Space k := WithLp.toLp 2 (0, 0)
private def radius (i : ℕ) : ℝ := (i : ℝ) + 1
private theorem radius_one (i : ℕ) : 1 ≤ radius i := by
  dsimp [radius]
  linarith [Nat.cast_nonneg (α := ℝ) i]
private theorem radius_pos (i : ℕ) : 0 < radius i := lt_of_lt_of_le (by norm_num) (radius_one i)
private theorem radius_top : Tendsto radius atTop atTop :=
  tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
private noncomputable def alpha (i : ℕ) : ℝ := 1 / radius i
private theorem alpha_pos (i : ℕ) : 0 < alpha i := div_pos zero_lt_one (radius_pos i)
private theorem alpha_le_one (i : ℕ) : alpha i ≤ 1 :=
  (div_le_one (radius_pos i)).mpr (radius_one i)
private theorem alpha_zero : Tendsto alpha atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat
private noncomputable def errors (i : ℕ) : ℝ := alpha i / 100
private theorem errors_pos (i : ℕ) : 0 < errors i := div_pos (alpha_pos i) (by norm_num)
private theorem errors_lt (i : ℕ) : errors i < radius i := by
  dsimp [errors]
  linarith [alpha_le_one i, radius_one i]
private theorem errors_zero : Tendsto errors atTop (𝓝 0) := by
  change Tendsto (fun i => alpha i / 100) atTop (𝓝 0)
  simpa only [zero_div] using alpha_zero.div_const 100
private def approx (k i : ℕ) : PointedBallApprox (base k) (base k) (radius i) (errors i) where
  error_pos := errors_pos i
  error_lt_radius := errors_lt i
  toFun := Subtype.val
  basepoint := rfl
  distortion x y := by simpa only [sub_self, abs_zero] using errors_pos i
  coverage y hy := ⟨⟨y, by linarith [errors_pos i]⟩, by simpa only [dist_self] using errors_pos i⟩
private noncomputable def prescribed (k i : ℕ) (x : Space k) : EuclideanSpace ℝ (Fin k) := by
  classical
  exact if dist x (base k) ≤ radius i then (1 + alpha i) • x.fst else (2 : ℝ) • x.fst
private theorem prescribed_base (k i : ℕ) : prescribed k i (base k) = (base k).fst := by
  simp only [prescribed, dist_self, ite_eq_left (radius_pos i).le, base,
    WithLp.toLp_fst, smul_zero]
private theorem component_bound (k : ℕ) (x : Space k) (j : Fin k) :
    |x.fst j| ≤ dist x (base k) := by
  have hh := (PiLp.dist_apply_le x.fst (0 : EuclideanSpace ℝ (Fin k)) j).trans
    (WithLp.dist_fst_le x (base k))
  simpa only [base, WithLp.toLp_fst, PiLp.zero_apply, Real.dist_eq, sub_zero] using hh
private theorem prescribed_close (k : ℕ) : ∀ S : ℝ, 0 < S → ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
    ∀ j, ∀ x : BallCarrier (base k) (radius i), dist x.val (base k) ≤ S →
      |prescribed k i x.val j - ((IsometryEquiv.refl (Space k)) ((approx k i).toFun x)).fst j| < η := by
  intro S hS η hη
  have ht : Tendsto (fun i => alpha i * S) atTop (𝓝 0) := by
    simpa only [zero_mul] using alpha_zero.mul_const S
  filter_upwards [ht.eventually (gt_mem_nhds hη)] with i hi
  intro j x hx
  simp only [prescribed, ite_eq_left x.property, PiLp.smul_apply, smul_eq_mul,
    approx]
  change |(1 + alpha i) * x.val.fst j - x.val.fst j| < η
  rw [show (1 + alpha i) * x.val.fst j - x.val.fst j = alpha i * x.val.fst j by ring,
    abs_mul, abs_of_pos (alpha_pos i)]
  exact (mul_le_mul_of_nonneg_left ((component_bound k x.val j).trans hx) (alpha_pos i).le).trans_lt hi

theorem prescribed_whole_space (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∀ᶠ i in atTop, ∃ ψ : KleinerLottApprox (base k) (base k) δ,
      ∀ x : Space k, (ψ.toFun x).fst = prescribed k i x :=
  eventually_prescribed_kleinerLott_approximation_of_component_convergence
    (IsometryEquiv.refl (Space k)) (approx k) radius_top errors_zero (prescribed k)
    (prescribed_base k) (prescribed_close k) hδ hδone

private def outside (i : ℕ) : Space 1 := WithLp.toLp 2 (PiLp.single 2 0 (2 * radius i), 0)
private theorem outside_distance (i : ℕ) : dist (outside i) (base 1) = 2 * radius i := by
  change dist (WithLp.toLp 2 (PiLp.single 2 0 (2 * radius i), (0 : ℝ)))
    (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), (0 : ℝ))) = 2 * radius i
  rw [(WithLp.isometry_prodMk_right (0 : ℝ)).dist_eq
    (PiLp.single 2 (0 : Fin 1) (2 * radius i)) (0 : EuclideanSpace ℝ (Fin 1)),
    dist_zero_right, PiLp.norm_single]
  simp only [Real.norm_eq_abs, abs_of_pos (show 0 < 2 * radius i by linarith [radius_pos i])]
private theorem outside_not_in_map_domain (i : ℕ) : ¬ dist (outside i) (base 1) ≤ radius i := by
  rw [outside_distance]
  linarith [radius_pos i]
private theorem prescribed_outside (i : ℕ) : prescribed 1 i (outside i) 0 = 4 * radius i := by
  rw [prescribed, ite_eq_right (outside_not_in_map_domain i)]
  simp only [outside, WithLp.toLp_fst, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  norm_num
  ring

theorem outside_coordinate_exact {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∀ᶠ i in atTop, ∃ ψ : KleinerLottApprox (base 1) (base 1) δ,
      (∀ x : Space 1, (ψ.toFun x).fst = prescribed 1 i x) ∧
      ¬ dist (outside i) (base 1) ≤ radius i ∧
      (ψ.toFun (outside i)).fst 0 = 4 * radius i := by
  filter_upwards [prescribed_whole_space 1 hδ hδone] with i hi
  obtain ⟨ψ, hψ⟩ := hi
  refine ⟨ψ, hψ, outside_not_in_map_domain i, ?_⟩
  rw [hψ]
  exact prescribed_outside i

theorem outside_error_diverges :
    Tendsto (fun i => |prescribed 1 i (outside i) 0 - (outside i).fst 0|) atTop atTop := by
  have he (i : ℕ) : |prescribed 1 i (outside i) 0 - (outside i).fst 0| = 2 * radius i := by
    rw [prescribed_outside]
    simp only [outside, WithLp.toLp_fst, PiLp.single_apply]
    norm_num
    rw [show 4 * radius i - 2 * radius i = 2 * radius i by ring,
      abs_of_pos (show 0 < 2 * radius i by linarith [radius_pos i])]
  simpa only [he] using radius_top.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)

theorem rank_zero_whole_space {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∀ᶠ i in atTop, ∃ ψ : KleinerLottApprox (base 0) (base 0) δ,
      ∀ x : Space 0, (ψ.toFun x).fst = prescribed 0 i x := prescribed_whole_space 0 hδ hδone

#print axioms prescribed_whole_space
#print axioms outside_coordinate_exact
#print axioms outside_error_diverges
#print axioms rank_zero_whole_space

end GCScalarPrescribedCoordinatesReview

open Set Filter Metric
open scoped Topology

namespace GCSequentialSplittingReview

open DifferentialGeometry.Geometry.Comparison.Toponogov GC.MetricGeometry

private def radius (i : ℕ) : ℝ := (i : ℝ) + 1
private theorem radius_one (i : ℕ) : 1 ≤ radius i := by dsimp [radius]; linarith [Nat.cast_nonneg (α := ℝ) i]
private theorem radius_pos (i : ℕ) : 0 < radius i := lt_of_lt_of_le (by norm_num) (radius_one i)
private theorem radius_top : Tendsto radius atTop atTop :=
  tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
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

private noncomputable def sig (i : ℕ) : ℝ := 1 / radius i
private theorem sig_pos (i : ℕ) : 0 < sig i := div_pos (by norm_num) (radius_pos i)
private theorem sig_zero : Tendsto sig atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
private theorem sig_inv (i : ℕ) : (sig i)⁻¹ = radius i := by simp [sig]


private def RealSequentialData (k : ℕ) : Prop :=
    ∃ χ : ℕ → ℕ, StrictMono χ ∧
      ∃ (Z : Type) (m : MetricSpace Z), letI := m
        ∃ z : Z, ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) ∧
          (∀ a b : Z, ∃ c : Icc (0 : ℝ) 1 → Z,
            Continuous c ∧ c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
              ∀ s t, dist (c s) (c t) = dist a b * dist s t) ∧
          ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ᶠ i in atTop,
            ∃ F : KleinerLottApprox (0 : ℝ) (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), z)) δ,
              ∀ x : ℝ, (F.toFun x).fst =
                WithLp.toLp 2 (fun _ : Fin k => dist (0 : ℝ) (radius (χ i)) - dist x (radius (χ i)))

private theorem real_sequential_family (k : ℕ) [Subsingleton (Fin k)] : RealSequentialData k := by
  exact exists_subsequence_prescribed_kleinerLott_approximations_of_reciprocal_local_geometry
    (fun _ => (0 : ℝ)) (n := 1) (by norm_num)
    (fun _ => arbitrarily_short_curves_of_metric_segments real_segments)
    (fun i => by simpa only [Nat.cast_one] using
      (dimH_mono (subset_univ (ball (0 : ℝ) ((sig i)⁻¹)))).trans_eq Real.dimH_univ)
    (fun i z _ => ⟨univ, isOpen_univ, real_comparison (sig_pos i).le, mem_univ z⟩)
    (fun i (_ : Fin k) => radius i) (fun i _ => -radius i) sig_pos sig_zero
    (fun i _ => by rw [sig_inv, Real.dist_eq, zero_sub, abs_neg, abs_of_pos (radius_pos i)])
    (fun i _ => by rw [sig_inv, Real.dist_eq, zero_sub, neg_neg, abs_of_pos (radius_pos i)]) (by
      intro j
      exact Eventually.of_forall fun i => by
        have hh := comparisonAngleNegCurvature_add (sig_pos i).le (radius_pos i) (radius_pos i)
        rw [Real.dist_eq (0 : ℝ) (radius i), Real.dist_eq (0 : ℝ) (-radius i),
          Real.dist_eq (radius i) (-radius i), zero_sub, abs_neg, abs_of_pos (radius_pos i),
          zero_sub, neg_neg, abs_of_pos (radius_pos i), sub_neg_eq_add,
          abs_of_pos (show 0 < radius i + radius i by linarith [radius_pos i]), hh]
        linarith [sig_pos i])
    (fun j l hjl => (hjl (Subsingleton.elim j l)).elim)
    (fun j l hjl => (hjl (Subsingleton.elim j l)).elim)

private theorem actual_sequence_one_axis : RealSequentialData 1 := real_sequential_family 1
private theorem actual_sequence_no_axes : RealSequentialData 0 := real_sequential_family 0

private theorem whole_source_folded_coordinate :
    ∃ χ : ℕ → ℕ, StrictMono χ ∧
      ∃ (Z : Type) (m : MetricSpace Z), letI := m
        ∃ z : Z, ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ᶠ i in atTop,
          ∃ F : KleinerLottApprox (0 : ℝ) (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), z)) δ,
            dist (2 * radius (χ i)) (0 : ℝ) > δ⁻¹ ∧
            (F.toFun (2 * radius (χ i))).fst 0 = 0 ∧
            ∀ x : ℝ, (F.toFun x).fst =
              WithLp.toLp 2 (fun _ : Fin 1 => dist (0 : ℝ) (radius (χ i)) - dist x (radius (χ i))) := by
  obtain ⟨χ, hχ, Z, m, z, _hp, _hc, _hs, _hseg, hmaps⟩ := actual_sequence_one_axis
  let := m
  refine ⟨χ, hχ, Z, m, z, ?_⟩
  intro δ hδ hδone
  filter_upwards [hmaps δ hδ hδone,
    (radius_top.comp hχ.tendsto_atTop).eventually_gt_atTop δ⁻¹] with i hi hrad
  change δ⁻¹ < radius (χ i) at hrad
  obtain ⟨F, hF⟩ := hi
  refine ⟨F, ?_, ?_, hF⟩
  · rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith [radius_pos (χ i)])]
    linarith [radius_pos (χ i)]
  · rw [hF]
    change dist (0 : ℝ) (radius (χ i)) - dist (2 * radius (χ i)) (radius (χ i)) = 0
    rw [Real.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_pos (radius_pos (χ i)),
      show 2 * radius (χ i) - radius (χ i) = radius (χ i) by ring,
      abs_of_pos (radius_pos (χ i)), sub_self]

#print axioms actual_sequence_one_axis
#print axioms actual_sequence_no_axes
#print axioms whole_source_folded_coordinate

end GCSequentialSplittingReview


#print axioms GC.MetricGeometry.eventually_prescribed_kleinerLott_approximation_of_component_convergence
#print axioms GC.MetricGeometry.eventually_distance_coordinates_kleinerLott_approximation
#print axioms GC.MetricGeometry.exists_subsequence_prescribed_kleinerLott_approximations_of_reciprocal_local_geometry
#lint- only unusedArguments simpNF synTaut
```
