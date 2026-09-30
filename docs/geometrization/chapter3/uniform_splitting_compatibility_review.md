# Full AC76 independent acceptance

Four public theorems in two leaves add four owned declarations. The341-module gate checks1477 declarations in3176 jobs. Every new transitive closure uses only propext, Classical.choice and Quot.sound. Source-copy and accepted-import review lint is silent; the driver emits nine standard reports. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning lies outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

One agent implemented the original uniform theorem and its exact-limit exclusion dependencies; another independently read their full statements/proofs, checked source locators and universe quantifiers, and separately recompiled the declarations and both original-input drivers. Root read all production proofs and both full regression bodies. The final driver imports the accepted leaves rather than copying their theorem bodies.

The uniform quantifier selects sigma before every source, original factor and BOTH supplied maps. Counterexamples retain those actual maps and their failure, and are chosen at sigma_i=1/(i+2), with exact original OPEN sigma inverse geometry. The growing-limit producer derives all needed target geometry. No target-map convergence rate or source properness is assumed. The final failure and success are compared at exactly alpha(chi(i)). The whole proof uses the original actual point and both products of the same Y.

The exclusion proof constructs source splittings from a hypothetical exact limit isometry. It intersects the eventual construction with frequent absence. The explicit Type0-to-Typeu adapter uses ULift of the factor with its induced metric and a proved pointed product isometry. Thus the resulting forbidden map lies inside the ORIGINAL exclusion universe, without changing the underlying Y. The full theorem needs this because the compactness/exact-compatibility targets and their factors are Type0.

The first regression constructs pointed convergence of actual rational sources to R and proves those sources incomplete and nonproper. It obtains source approximations to the exact rank1 real product at EVERY normalized quality. A second regression constructs actual lifted-universe singleton sources and their convergence. It proves the fixed-quality no-line-product hypothesis from coverage at a unit Euclidean target, then exercises both the same-universe and explicit lifted-universe exclusion adapters. These hypotheses are not supplied as opaque test assumptions.

The uniform regression obtains the ACTUAL unknown sigma for j=k=n=1, tau1/2 and nu1/1000. It constructs original whole-space real product maps with coordinates+x and-x, proves their pointedness, actual local comparison at sigma, Hausdorff ball dimension and short curves, and invokes the uniform theorem. Its fixed-quality rank2 exclusion is PROVED for every metric factor: AC67 would give two exact radius1 real points with distance close to sqrt2, whereas both points belong to{-1,1} and their distance is0 or2. This test-only AC67 dependency is absent from the production uniform theorem.

Source review checks KL4.17 statement/proof and the full frozen AC76 body. The shrinking-ball proof typo is explicitly treated as an inferred correction, with growing balls read directly from the source statement; the retained author sheet does not list it. The strict/equal-rank definition mismatch is preserved as a source qualification and resolved through the accepted equal-rank compatibility interface. No automatic passage of absence to limits, hidden modulus or parameter monotonicity is claimed.

Full AC76 is complete. Basepoint transport, overlapping cones and later Chapters3-4 work remain. Blueprint207 and PC migration interfaces remain unchanged.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.UniformSplittingCompatibility
import DifferentialGeometry.Geometry.Metric.Approximation.ExactRadiusLifts
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.Rat
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Filter GC.MetricGeometry

namespace GCExactLimitApproximationReview

private theorem rat_incomplete : ¬ CompleteSpace ℚ := by
  intro hc
  let := hc
  have hi : Isometry (fun r : ℚ => (r : ℝ)) := Isometry.of_dist_eq (fun _ _ => rfl)
  have hclosed := hi.antilipschitzWith.isClosed_range hi.uniformContinuous
  have hdense : DenseRange (fun r : ℚ => (r : ℝ)) := Rat.denseRange_cast
  have heq : range (fun r : ℚ => (r : ℝ)) = univ := hclosed.closure_eq.symm.trans hdense.closure_range
  exact irrational_sqrt_two (by rw [heq]; exact mem_univ _)
private theorem rat_not_proper : ¬ ProperSpace ℚ := by
  intro hp
  let := hp
  exact rat_incomplete inferInstance

private def ratApprox {R ε : ℝ} (hε : 0 < ε) (hR : ε < R) :
    PointedBallApprox (0 : ℚ) (0 : ℝ) R ε where
  error_pos := hε
  error_lt_radius := hR
  toFun x := (x.val : ℝ)
  basepoint := Rat.cast_zero
  distortion x y := by
    simp only [Rat.dist_cast, sub_self, abs_zero]
    exact hε
  coverage y hy := by
    obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn (by linarith : y - ε / 2 < y + ε / 2)
    have hry : dist (r : ℝ) y < ε / 2 := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hrad : dist r (0 : ℚ) ≤ R := by
      rw [← Rat.dist_cast, Rat.cast_zero]
      have ht := dist_triangle (r : ℝ) y 0
      linarith
    refine ⟨⟨r, hrad⟩, ?_⟩
    change dist y (r : ℝ) < ε
    rw [dist_comm]
    linarith

private theorem ratConverges : PointedGHConverges (fun _ : ℕ => (0 : ℚ)) (0 : ℝ) :=
  ⟨inferInstance, fun _ _ hε hR => Eventually.of_forall (fun _ => ⟨ratApprox hε hR⟩)⟩

private abbrev E1 := EuclideanSpace ℝ (Fin 1)
private abbrev Unit := PUnit.{1}

private noncomputable def realProduct : ℝ ≃ᵢ WithLp 2 (E1 × Unit) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toIsometryEquiv.trans
    (IsometryEquiv.withLpProdUnique 2 E1 Unit).symm

private theorem realProduct_base : realProduct 0 = WithLp.toLp 2 (0, PUnit.unit) := by
  change (IsometryEquiv.withLpProdUnique 2 E1 Unit).symm
    ((OrthonormalBasis.singleton (Fin 1) ℝ).repr 0) = _
  rw [(OrthonormalBasis.singleton (Fin 1) ℝ).repr.map_zero]
  rfl

theorem incomplete_rational_source_product_transfer :
    ¬ CompleteSpace ℚ ∧ ¬ ProperSpace ℚ ∧
      ∀ ν : ℝ, 0 < ν → ν < 1 →
        ∀ᶠ _ : ℕ in atTop,
          Nonempty (KleinerLottApprox (0 : ℚ) (WithLp.toLp 2 ((0 : E1), (PUnit.unit : Unit))) ν) := by
  refine ⟨rat_incomplete, rat_not_proper, ?_⟩
  intro ν hν hνone
  have h := ratConverges.eventually_kleinerLott_approx_isometric_target realProduct hν hνone
  rwa [realProduct_base] at h

universe u
private abbrev LargePoint := ULift.{u} Unit
private def largeBase : LargePoint.{u} := ULift.up PUnit.unit

private theorem large_point_converges :
    PointedGHConverges (fun _ : ℕ => largeBase.{u}) (PUnit.unit : Unit) := by
  refine ⟨inferInstance, fun R ε hε hR => Eventually.of_forall (fun _ => ?_)⟩
  refine ⟨⟨hε, hR, fun _ => PUnit.unit, rfl, ?_, ?_⟩⟩
  · intro x y
    have hxy : x.val = y.val := Subsingleton.elim _ _
    simpa only [hxy, dist_self, sub_self, abs_zero] using hε
  · intro y hy
    refine ⟨⟨largeBase, by simpa using (hε.trans hR).le⟩, ?_⟩
    have hy0 : y = PUnit.unit := Subsingleton.elim _ _
    simpa only [hy0, dist_self] using hε

private theorem point_has_no_fixed_quality_splitting :
    ¬ ∃ (W : Type u) (m : MetricSpace W), letI := m
      ∃ w : W, Nonempty (KleinerLottApprox largeBase.{u}
        (WithLp.toLp 2 ((0 : E1), w)) (1 / 4 : ℝ)) := by
  rintro ⟨W, m, w, F⟩
  let := m
  obtain ⟨F⟩ := F
  let y : WithLp 2 (E1 × W) := WithLp.toLp 2 (PiLp.single 2 0 (1 : ℝ), w)
  have hy : dist y (WithLp.toLp 2 ((0 : E1), w)) = 1 := by
    change dist (WithLp.toLp 2 (PiLp.single 2 (0 : Fin 1) (1 : ℝ), w))
      (WithLp.toLp 2 ((0 : E1), w)) = 1
    rw [(WithLp.isometry_prodMk_right (E := E1) w).dist_eq]
    simp only [dist_zero_right, PiLp.norm_single, norm_one]
  obtain ⟨x, _, hx⟩ := F.coverage_witness y (by rw [hy]; norm_num)
  have hxp : x = largeBase := Subsingleton.elim _ _
  rw [hxp, F.basepoint, hy] at hx
  norm_num at hx

theorem lifted_universe_point_excludes_exact_line_factor :
    PointedGHConverges (fun _ : ℕ => largeBase.{u}) (PUnit.unit : Unit) ∧
    ¬ ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (e : Unit ≃ᵢ WithLp 2 (E1 × W)),
        e PUnit.unit = WithLp.toLp 2 (0, w) := by
  refine ⟨large_point_converges.{u}, ?_⟩
  exact large_point_converges.{u}.not_exists_small_product_isometry_of_frequently_no_kleinerLott
    (0 : E1) (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    (Frequently.of_forall (fun _ => point_has_no_fixed_quality_splitting.{u}))

theorem same_universe_point_excludes_exact_line_factor :
    ¬ ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (e : Unit ≃ᵢ WithLp 2 (E1 × W)),
        e PUnit.unit = WithLp.toLp 2 (0, w) := by
  exact large_point_converges.{0}.not_exists_product_isometry_of_frequently_no_kleinerLott
    (0 : E1) (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    (Frequently.of_forall (fun _ => point_has_no_fixed_quality_splitting.{0}))

#print axioms incomplete_rational_source_product_transfer
#print axioms lifted_universe_point_excludes_exact_line_factor
#print axioms same_universe_point_excludes_exact_line_factor

end GCExactLimitApproximationReview

open Set Filter Metric
open scoped Topology

namespace GCUniformSplittingCompatibilityReview

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

private abbrev E1 := EuclideanSpace ℝ (Fin 1)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev Unit := PUnit.{1}

private theorem real_no_rank_two_fixed_quality :
    ¬ ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ w : W, Nonempty (KleinerLottApprox (0 : ℝ)
        (WithLp.toLp 2 ((0 : E2), w)) (1 / 1000 : ℝ)) := by
  rintro ⟨W, m, w, F⟩
  let := m
  obtain ⟨F⟩ := F
  obtain ⟨_, a, _, _, _, ha, _, _, hpair⟩ :=
    F.exists_exact_radius_unit_vector_lifts real_segments
      (fun j : Fin 2 => PiLp.single 2 j (1 : ℝ))
      (fun _ => by simp only [PiLp.norm_single, norm_one])
      (r := 1) (by norm_num) (by norm_num)
  let N : ℝ := ‖(PiLp.single 2 (0 : Fin 2) (1 : ℝ) : E2) - PiLp.single 2 1 1‖
  have hN : N ^ 2 = 2 := by
    norm_num [N, EuclideanSpace.norm_eq, Fin.sum_univ_two, PiLp.sub_apply, PiLp.single_apply]
  have hNpos : 0 ≤ N := norm_nonneg _
  have he := hpair 0 1
  change |dist (a 0) (a 1) - 1 * N| < 27 * (1 / 1000 : ℝ) at he
  rw [one_mul] at he
  have ha' (j : Fin 2) : a j = 1 ∨ a j = -1 := by
    have hh := ha j
    rw [Real.dist_eq, zero_sub, abs_neg] at hh
    rcases le_total 0 (a j) with hj | hj
    · left
      rwa [abs_of_nonneg hj] at hh
    · right
      rw [abs_of_nonpos hj] at hh
      linarith
  rcases ha' 0 with h0 | h0 <;> rcases ha' 1 with h1 | h1
  all_goals rw [h0, h1] at he
  all_goals norm_num [Real.dist_eq] at he
  all_goals first
    | have hh : N < 1 := by linarith [(abs_lt.mp he).1, (abs_lt.mp he).2]
      have hs := (sq_lt_sq₀ hNpos (by norm_num : (0 : ℝ) ≤ 1)).mpr hh
      nlinarith
    | have hh : (19 / 10 : ℝ) < N := by linarith [(abs_lt.mp he).1, (abs_lt.mp he).2]
      have hs := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 19 / 10) hNpos).mpr hh
      nlinarith

private noncomputable def realProduct : ℝ ≃ᵢ WithLp 2 (E1 × Unit) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toIsometryEquiv.trans
    (IsometryEquiv.withLpProdUnique 2 E1 Unit).symm

private theorem realProduct_base : realProduct 0 = WithLp.toLp 2 (0, PUnit.unit) := by
  change (IsometryEquiv.withLpProdUnique 2 E1 Unit).symm
    ((OrthonormalBasis.singleton (Fin 1) ℝ).repr 0) = _
  rw [(OrthonormalBasis.singleton (Fin 1) ℝ).repr.map_zero]
  rfl

private theorem realProduct_coordinate (x : ℝ) : (realProduct x).fst 0 = x := by
  change (OrthonormalBasis.singleton (Fin 1) ℝ).repr x 0 = x
  simp only [OrthonormalBasis.singleton_repr]

private noncomputable def reverseProduct : ℝ ≃ᵢ WithLp 2 (E1 × Unit) :=
  (LinearIsometryEquiv.neg ℝ (E := ℝ)).toIsometryEquiv.trans realProduct

private theorem reverseProduct_base : reverseProduct 0 = WithLp.toLp 2 (0, PUnit.unit) := by
  change realProduct (-0) = _
  simpa only [neg_zero] using realProduct_base

theorem actual_uniform_parameter_opposite_real_maps :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧
      ∃ φ ψ : KleinerLottApprox (0 : ℝ) (WithLp.toLp 2 ((0 : E1), (PUnit.unit : Unit))) σ,
        (∀ x : ℝ, (φ.toFun x).fst 0 = x) ∧
        (∀ x : ℝ, (ψ.toFun x).fst 0 = -x) ∧
        SplittingCompatible φ ψ (1 / 2 : ℝ) := by
  obtain ⟨σ, hσ, hσone, hparameter⟩ := exists_splitting_compatibility_parameter
    (j := 1) (k := 1) (n := 1) (τ := (1 / 2 : ℝ)) (ν := (1 / 1000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let φ := realProduct.toKleinerLottApprox realProduct_base hσ hσone
  let ψ := reverseProduct.toKleinerLottApprox reverseProduct_base hσ hσone
  have hdim : dimH (ball (0 : ℝ) σ⁻¹) ≤ (1 : ENNReal) :=
    (dimH_mono (subset_univ _)).trans_eq Real.dimH_univ
  have hc := hparameter ℝ 0
    (arbitrarily_short_curves_of_metric_segments real_segments)
    (by simpa only [Nat.cast_one] using hdim)
    (fun z _ => ⟨univ, isOpen_univ, real_comparison hσ.le, mem_univ z⟩)
    real_no_rank_two_fixed_quality Unit Unit PUnit.unit PUnit.unit φ ψ
  exact ⟨σ, hσ, hσone, φ, ψ, realProduct_coordinate,
    (fun x => realProduct_coordinate (-x)), hc⟩

#print axioms real_no_rank_two_fixed_quality
#print axioms actual_uniform_parameter_opposite_real_maps

end GCUniformSplittingCompatibilityReview

#print axioms GC.MetricGeometry.PointedGHConverges.eventually_kleinerLott_approx_isometric_target
#print axioms GC.MetricGeometry.PointedGHConverges.not_exists_product_isometry_of_frequently_no_kleinerLott
#print axioms GC.MetricGeometry.PointedGHConverges.not_exists_small_product_isometry_of_frequently_no_kleinerLott
#print axioms GC.MetricGeometry.exists_splitting_compatibility_parameter

#lint- only unusedArguments simpNF synTaut
```
