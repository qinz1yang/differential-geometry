# Radial cones and full AC84 acceptance

Twenty-nine public theorems, three definitions and one structure in five leaves add58 owned declarations, including25 generated declarations. The353-module gate checks1621 declarations in3188 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import regression lint is silent;37 reports cover all public production declarations and four concrete regressions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

Root and two independent agents read the full baseline proof and source passages. Root implemented the exact aligned splitting consumer; an independent agent read its proof and implemented its concrete original-input regression. Root read all regression bodies. Final tests import the canonical production leaves, rather than copied theorem bodies. Production imports are targeted, without the Mathlib.Tactic umbrella.

The actual translated Euclidean-plane example has apices(2,-3),(-1,1) at distance5. The SAME named line is checked at parameters0,5,-5,10, including signed points(5,-7),(-4,5) and cross-distance15. A separate actual singleton cone confirms that the radial interface admits the degenerate point. The actual real example with reversed apices5,2 proves the constructed line is gamma(t)=5-t. The production consumer yields one onto product isometry with global first coordinate2-x, old-apex coordinate-3, coordinate-5 atx7, and entire-axis coordinate t-3; its factor is proved singleton/dimension0 using that same onto map. Properness, completeness and CBB0 facts are retained.

Full AC82 and AC84 are proved. AC83 algebra and unique rays are proved, while its full independently stated two-ray-convention equivalence remains open. No angular quotient construction, angular-link curvature, residual-factor cone or rescaling-only cone claim is made. Blueprint207 and migration interfaces remain unchanged.

```lean
import DifferentialGeometry.Geometry.Comparison.TwoConeSplitting
import Mathlib.Tactic

set_option autoImplicit false

open GC.MetricGeometry
open scoped NNReal

namespace GCRadialConeReview

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private noncomputable def planeCone (p : Plane) : RadialConeData p where
  map t x := p + (t : ℝ) • (x - p)
  map_zero x := by simp
  map_one x := by simp
  dist_sq s t x y := by
    simp only [radialConeKernel, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two,
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Real.dist_eq, sq_abs]
    ring

private noncomputable def p : Plane := WithLp.toLp 2 ![2, -3]
private noncomputable def q : Plane := WithLp.toLp 2 ![-1, 1]

private theorem dist_pq : dist p q = 5 := by
  apply (sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 5)).mp
  norm_num [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, p, q, Real.dist_eq]

theorem translated_plane_actual_cones :
    ∃ (H : RadialConeData p) (K : RadialConeData q),
      (∀ t x, H.map t x = p + (t : ℝ) • (x - p)) ∧
      (∀ t x, K.map t x = q + (t : ℝ) • (x - q)) ∧ dist p q = 5 :=
  ⟨planeCone p, planeCone q, fun _ _ => rfl, fun _ _ => rfl, dist_pq⟩

theorem translated_plane_two_apices :
    let γ := (planeCone p).twoApexLine (planeCone q)
    Isometry γ ∧ γ 0 = p ∧ γ 5 = q ∧
      γ (-5) = WithLp.toLp 2 ![5, -7] ∧
      γ 10 = WithLp.toLp 2 ![-4, 5] ∧ dist (γ (-5)) (γ 10) = 15 := by
  let γ := (planeCone p).twoApexLine (planeCone q)
  have hpq : p ≠ q := by
    intro h
    have hh := dist_pq
    rw [h, dist_self] at hh
    norm_num at hh
  have hn : nndist p q = (5 : ℝ≥0) := by
    apply NNReal.coe_injective
    exact dist_pq
  have hn' : nndist q p = (5 : ℝ≥0) := by rw [nndist_comm, hn]
  have hγ := (planeCone p).twoApexLine_isometry (planeCone q) hpq
  refine ⟨hγ, (planeCone p).twoApexLine_zero (planeCone q), ?_, ?_, ?_, ?_⟩
  · simpa only [dist_pq] using (planeCone p).twoApexLine_through (planeCone q) hpq
  · rw [(planeCone p).twoApexLine_nonpos (planeCone q) hpq (by norm_num)]
    simp only [RadialConeData.unitRay, hn']
    norm_num only [neg_neg, Real.toNNReal_ofNat, Nat.cast_ofNat, NNReal.coe_ofNat]
    change q + (2 : ℝ) • (p - q) = _
    ext j
    fin_cases j <;> norm_num [p, q, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]
  · rw [(planeCone p).twoApexLine_nonneg (planeCone q) (by norm_num)]
    simp only [RadialConeData.unitRay, hn]
    norm_num only [Real.toNNReal_ofNat, Nat.cast_ofNat, NNReal.coe_ofNat]
    change p + (2 : ℝ) • (q - p) = _
    ext j
    fin_cases j <;> norm_num [p, q, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]
  · rw [hγ.dist_eq]
    norm_num [Real.dist_eq]

private abbrev Point := PUnit.{1}

private noncomputable def pointCone : RadialConeData (PUnit.unit : Point) where
  map _ _ := PUnit.unit
  map_zero _ := rfl
  map_one _ := Subsingleton.elim _ _
  dist_sq _ _ _ _ := by simp [radialConeKernel, Subsingleton.elim _ (PUnit.unit : Point)]

theorem singleton_actual_cone : Nonempty (RadialConeData (PUnit.unit : Point)) := ⟨pointCone⟩

end GCRadialConeReview

open Set Metric GC.MetricGeometry
open scoped NNReal
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GCTwoConeSplittingReview

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

private theorem reversed_line (t : ℝ) :
    (realCone (5 : ℝ)).twoApexLine (realCone 2) t = 5 - t := by
  have hn : nndist (5 : ℝ) 2 = (3 : ℝ≥0) := by
    apply NNReal.coe_injective
    norm_num [Real.dist_eq]
  have hn' : nndist (2 : ℝ) 5 = (3 : ℝ≥0) := by rw [nndist_comm, hn]
  by_cases ht : 0 ≤ t
  · rw [(realCone (5 : ℝ)).twoApexLine_nonneg (realCone 2) ht]
    simp only [RadialConeData.unitRay, hn, realCone, NNReal.coe_div,
      Real.coe_toNNReal _ ht, NNReal.coe_ofNat]
    ring
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [(realCone (5 : ℝ)).twoApexLine_nonpos (realCone 2) (by norm_num) ht']
    simp only [RadialConeData.unitRay, hn', realCone, NNReal.coe_div, NNReal.coe_add,
      Real.coe_toNNReal _ (neg_nonneg.mpr ht'), NNReal.coe_ofNat]
    ring

theorem translated_reversed_real_apices_product :
    ∃ (Y : Type) (m : MetricSpace Y), letI := m
      ∃ (w : Y) (e : ℝ ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × Y)),
        e 2 = WithLp.toLp 2 (0, w) ∧
        e 5 = WithLp.toLp 2 (PiLp.single 2 0 (-3 : ℝ), w) ∧
        (∀ x : ℝ, e x = WithLp.toLp 2 (PiLp.single 2 0 (2 - x), w)) ∧
        (∀ t : ℝ, e ((realCone 5).twoApexLine (realCone 2) t) =
          WithLp.toLp 2 (PiLp.single 2 0 (t - 3), w)) ∧
        e 7 = WithLp.toLp 2 (PiLp.single 2 0 (-5 : ℝ), w) ∧
        ProperSpace Y ∧ CompleteSpace Y ∧ fourPointComparison 0 (univ : Set Y) ∧
        Subsingleton Y ∧ dimH (univ : Set Y) = 0 := by
  obtain ⟨Y, m, w, e, hq, hp, haxis, hproper, hcomplete, hcomp, _hsegments, _hdim⟩ :=
    (realCone (5 : ℝ)).exists_pointed_product_at_second_apex (realCone 2) (by norm_num)
      (real_comparison le_rfl) real_segments
  let := m
  have hd : dist (5 : ℝ) 2 = 3 := by norm_num [Real.dist_eq]
  have hall (x : ℝ) : e x = WithLp.toLp 2 (PiLp.single 2 0 (2 - x), w) := by
    have hh := haxis (5 - x)
    rw [reversed_line, hd, show (5 : ℝ) - (5 - x) = x by ring,
      show (5 - x) - 3 = 2 - x by ring] at hh
    exact hh
  have hsub : Subsingleton Y := by
    refine ⟨fun a b => ?_⟩
    have hz (a : Y) : a = w := by
      obtain ⟨x, hx⟩ := e.surjective (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), a))
      rw [hall x] at hx
      exact (congrArg (fun v : WithLp 2 (EuclideanSpace ℝ (Fin 1) × Y) => v.snd) hx).symm
    exact (hz a).trans (hz b).symm
  let := hsub
  refine ⟨Y, m, w, e, hq, ?_, hall, ?_, ?_, hproper, hcomplete, hcomp, hsub, ?_⟩
  · simpa only [hd] using hp
  · intro t
    simpa only [hd] using haxis t
  · simpa only [show (2 : ℝ) - 7 = -5 by norm_num] using hall 7
  · exact dimH_subsingleton (fun _ _ _ _ => Subsingleton.elim _ _)

end GCTwoConeSplittingReview

#print axioms GC.MetricGeometry.radialConeKernel
#print axioms GC.MetricGeometry.RadialConeData
#print axioms GC.MetricGeometry.radialConeKernel_self
#print axioms GC.MetricGeometry.radialConeKernel_comm
#print axioms GC.MetricGeometry.radialConeKernel_bounds
#print axioms GC.MetricGeometry.RadialConeData.dist_apex
#print axioms GC.MetricGeometry.RadialConeData.map_apex
#print axioms GC.MetricGeometry.RadialConeData.same_ray_dist
#print axioms GC.MetricGeometry.RadialConeData.similarity
#print axioms GC.MetricGeometry.RadialConeData.kernel_map_left
#print axioms GC.MetricGeometry.RadialConeData.kernel_map_right
#print axioms GC.MetricGeometry.RadialConeData.map_mul
#print axioms GC.MetricGeometry.RadialConeData.map_inv_map
#print axioms GC.MetricGeometry.RadialConeData.map_map_inv
#print axioms GC.MetricGeometry.RadialConeData.map_surjective
#print axioms GC.MetricGeometry.RadialConeData.map_injective
#print axioms GC.MetricGeometry.RadialConeData.unitRay
#print axioms GC.MetricGeometry.RadialConeData.unitRay_zero
#print axioms GC.MetricGeometry.RadialConeData.unitRay_through
#print axioms GC.MetricGeometry.RadialConeData.unitRay_isometry
#print axioms GC.MetricGeometry.RadialConeData.eq_map_of_radial_distances
#print axioms GC.MetricGeometry.RadialConeData.eq_map_of_radial_distances_abs
#print axioms GC.MetricGeometry.RadialConeData.unitRay_dist_apex
#print axioms GC.MetricGeometry.RadialConeData.unitRay_unique
#print axioms GC.MetricGeometry.RadialConeData.two_apex_cross_dist
#print axioms GC.MetricGeometry.RadialConeData.twoApexLine
#print axioms GC.MetricGeometry.RadialConeData.twoApexLine_nonneg
#print axioms GC.MetricGeometry.RadialConeData.twoApexLine_nonpos
#print axioms GC.MetricGeometry.RadialConeData.twoApexLine_zero
#print axioms GC.MetricGeometry.RadialConeData.twoApexLine_through
#print axioms GC.MetricGeometry.RadialConeData.twoApexLine_isometry
#print axioms GC.MetricGeometry.RadialConeData.exists_line_through_two_apices
#print axioms GC.MetricGeometry.RadialConeData.exists_pointed_product_at_second_apex
#print axioms GCRadialConeReview.translated_plane_actual_cones
#print axioms GCRadialConeReview.translated_plane_two_apices
#print axioms GCRadialConeReview.singleton_actual_cone
#print axioms GCTwoConeSplittingReview.translated_reversed_real_apices_product
#lint- only unusedArguments simpNF synTaut
```
