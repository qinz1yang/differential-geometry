# Full uniform AC55 review

One public theorem in one leaf adds one owned declaration. The 321-module gate checks 1406 declarations in 3156 jobs. All transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import review lint is silent. The review emits two requested standard axiom reports. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. Static audit passes. No full migrated root, new PDF/Overleaf build or human approval is claimed.

One agent implemented the uniform contradiction. A different agent independently reviewed the full statement, proof and original sources and constructed the concrete application. Root reread the complete proof and application, the blueprint AC55 body and Mathlib's finite-fiber proof. The existential sigma precedes every rank and source-space quantifier. The counterexample proposition negates exactly the actual normalized approximation with the whole-source original distance vector. Ranks are fixed by an infinite fiber before any dependent metric spaces or endpoint families are chosen; no unchecked Fin cast is used. Both strict subsequences preserve the actual curvature parameter and reciprocal radius. The accepted sequential producer supplies the actual factor in the Type universe required by the negated conclusion. No monotonicity, explicit modulus, stronger source geometry or independently supplied limit is assumed.

The nonvacuous application obtains the ACTUAL unknown sigma from the uniform theorem at dimension bound two and delta=1/2. At that same sigma it supplies complete real sources, actual endpoints plus/minus sigma inverse, proved opposite comparison angle pi, actual short curves, global comparison and dimension bound. The returned normalized KL map has the original first coordinate sigma inverse minus |x-sigma inverse| at EVERY real point. At x=3/sigma, proved outside the control ball, that coordinate is exactly -1/sigma. The test retains 0<sigma<1 and the actual factor/map, without choosing an explicit value for sigma or assuming the map is the identity.

Full AC55 is complete through accepted original-input dependencies. Reverse strainers and compatibility remain. Chapters 3-4 are unfinished; blueprint 207 and migration interfaces remain unchanged.

```lean
import Mathlib.Tactic
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import DifferentialGeometry.Geometry.Metric.Approximation.UniformLongStrainerSplitting

open Set Filter Metric
open scoped Topology

namespace GCUniformLongStrainerReview

open DifferentialGeometry.Geometry.Comparison.Toponogov GC.MetricGeometry

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

theorem actual_uniform_parameter_real_application :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧
      ∃ (Z : Type) (m : MetricSpace Z), letI := m
        ∃ (z : Z) (F : KleinerLottApprox (0 : ℝ)
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), z)) (1 / 2)),
          (∀ x : ℝ, (F.toFun x).fst =
            WithLp.toLp 2 (fun _ : Fin 1 => σ⁻¹ - dist x σ⁻¹)) ∧
          F.toFun 0 = WithLp.toLp 2 (0, z) ∧
          ¬ dist (3 * σ⁻¹) (0 : ℝ) < 2 ∧
          (F.toFun (3 * σ⁻¹)).fst 0 = -σ⁻¹ := by
  obtain ⟨σ, hσpos, hσone, hparameter⟩ :=
    exists_prescribed_splitting_parameter (n := 2) (δ := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  have hLpos : 0 < σ⁻¹ := inv_pos.mpr hσpos
  have hLone : 1 < σ⁻¹ := (one_lt_inv₀ hσpos).mpr hσone
  have hd : dimH (ball (0 : ℝ) σ⁻¹) ≤ (2 : ENNReal) :=
    (dimH_mono (subset_univ _)).trans (by rw [Real.dimH_univ]; norm_num)
  have hp (j : Fin 1) : dist (0 : ℝ) σ⁻¹ = σ⁻¹ := by
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hLpos]
  have hm (j : Fin 1) : dist (0 : ℝ) (-σ⁻¹) = σ⁻¹ := by
    rw [Real.dist_eq, zero_sub, neg_neg, abs_of_pos hLpos]
  have hopp (j : Fin 1) : Real.pi - σ ≤ comparisonAngleNegCurvature σ
      (dist (0 : ℝ) σ⁻¹) (dist (0 : ℝ) (-σ⁻¹)) (dist σ⁻¹ (-σ⁻¹)) := by
    rw [hp j, hm j, Real.dist_eq, sub_neg_eq_add,
      abs_of_pos (show 0 < σ⁻¹ + σ⁻¹ by linarith),
      comparisonAngleNegCurvature_add hσpos.le hLpos hLpos]
    linarith
  obtain ⟨Z, m, z, F, hF⟩ := hparameter 1 (by norm_num) (by norm_num)
    ℝ (0 : ℝ) (fun _ : Fin 1 => σ⁻¹) (fun _ : Fin 1 => -σ⁻¹)
    (arbitrarily_short_curves_of_metric_segments real_segments) hd
    (fun z _ => ⟨univ, isOpen_univ, real_comparison hσpos.le, mem_univ z⟩)
    hp hm hopp
    (fun j l hjl => (hjl (Subsingleton.elim j l)).elim)
    (fun j l hjl => (hjl (Subsingleton.elim j l)).elim)
  let := m
  have hF' (x : ℝ) : (F.toFun x).fst =
      WithLp.toLp 2 (fun _ : Fin 1 => σ⁻¹ - dist x σ⁻¹) := by
    simpa only [hp (0 : Fin 1)] using hF x
  refine ⟨σ, hσpos, hσone, Z, m, z, F, hF', F.basepoint, ?_, ?_⟩
  · rw [Real.dist_eq, sub_zero, abs_of_pos (show 0 < 3 * σ⁻¹ by linarith)]
    linarith
  · rw [hF']
    change σ⁻¹ - dist (3 * σ⁻¹) σ⁻¹ = -σ⁻¹
    rw [Real.dist_eq, abs_of_nonneg (show 0 ≤ 3 * σ⁻¹ - σ⁻¹ by linarith)]
    ring

#print axioms actual_uniform_parameter_real_application

end GCUniformLongStrainerReview

#print axioms GC.MetricGeometry.exists_prescribed_splitting_parameter
#lint- only unusedArguments simpNF synTaut
```
