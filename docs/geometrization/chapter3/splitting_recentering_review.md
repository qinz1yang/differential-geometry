# Full AC79-80 independent acceptance

Seven public theorems, five definitions and two private helpers in three leaves add34 owned declarations, including20 generated declarations. The346-module gate checks1556 declarations in3181 jobs. All new closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import review lint is silent;18 reports check the declarations and regressions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves remain unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

One agent implemented generic whole-KL isometry transports and AC79. Root and the AC80 author independently read their full proofs. The AC80 author implemented the same-Q factor construction and final actual-map corollary. Root and a third agent independently reviewed those proofs; the third agent built the nonzero-repair regression. Root added a concrete application of the final SplittingCompatible.recenterEuclidean corollary. The final driver imports accepted leaves, not copied production bodies. A missing direct PiL2 import was fixed during the initial individual build; the final individual and combined builds are clean.

Target isometry transport preserves exact infimum-distance coverage, and source transport uses the actual image of the original controlled ball. The explicit-base variants preserve formulas definitionally. AC79 uses the original image as new target, so its map has no repair; translating only the Euclidean factor gives the exact original coordinate difference and residual coordinate EVERYWHERE, with actual z(c) basepoint.

AC80 first places c inside the old source ball. Both factor displacement bounds come from that SAME original psi(c) and its radial distortion. Compatibility at c supplies the joint product bound, not two unrelated error allowances. The two original factor maps are repaired at their actual new factor inputs, then source/target translations yield their OWN pointed KL delta coverage. The joint repair bound applies at all factor arguments, including repetitions away from c. The new source ball lies inside the old ball; translated-back coordinates cancel exactly. Thus the new product error is<=2epsilon<delta, with SAME Q. The actual phi_c/psi_c are unchanged coordinate translations. No geometric or continuity hypothesis is added.

The AC79 regression uses actual identity product maps on E1 times Q and proves source incompleteness. At c=(3,1), delta1/2,C4,epsilon1/800, it retains the exact whole map(x1-3,x2); the outside point(100,5) maps to(97,5) and is proved outside the new controlled ball. A Fin0 example retains the whole identity map and actual rational residual center.

The AC80 regression uses actual identity source maps on E1 times E1 with equal ranks and singleton leftover. BOTH factor witnesses have genuine epsilon/4 bumps at coordinate1 and their actual KL coverage is proved. Both new target repairs have nonzero displacement, proved exactly. The stronger theorem returns whole-factor witnesses and the strict estimate on the original recentered radius2 ball. Vertical and horizontal noncenter points in that ball repeat one of the repaired center factor arguments. Root's added test constructs original SplittingCompatible from those same bumped witnesses and invokes the final recentering corollary, retaining the exact global source-map formula.

Sources checked are frozen AC79-80 and actual KL4.10/4.14, including the explicitly omitted compatibility proof and retained errata. Full AC79-80 are complete under the documented zero/equal-rank extension of directed compatibility. Neither continuity of repaired witnesses, smooth coordinate compatibility nor a cocycle identity is asserted. Moving-point and cone work remain; blueprint207 and migration interfaces are unchanged.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.CompatibilityRecentering
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric GC.MetricGeometry

namespace GCNormalizedSplittingRecenteringReview

private abbrev E1 := EuclideanSpace ℝ (Fin 1)
private abbrev X1 := WithLp 2 (E1 × ℚ)
private noncomputable def axis (t : ℝ) : E1 := PiLp.single 2 0 t
private noncomputable def base : X1 := WithLp.toLp 2 (0, 0)
private noncomputable def center : X1 := WithLp.toLp 2 (axis 3, 1)
private noncomputable def outside : X1 := WithLp.toLp 2 (axis 100, 5)

private theorem rat_incomplete : ¬ CompleteSpace ℚ := by
  intro hc
  let := hc
  have hi : Isometry (fun r : ℚ => (r : ℝ)) := Isometry.of_dist_eq (fun _ _ => rfl)
  have hclosed := hi.antilipschitzWith.isClosed_range hi.uniformContinuous
  have hdense : DenseRange (fun r : ℚ => (r : ℝ)) := Rat.denseRange_cast
  have heq : range (fun r : ℚ => (r : ℝ)) = univ := hclosed.closure_eq.symm.trans hdense.closure_range
  exact irrational_sqrt_two (by rw [heq]; exact mem_univ _)

private theorem source_incomplete : ¬ CompleteSpace X1 := by
  intro hc
  let := hc
  exact rat_incomplete ((IsometryEquiv.refl X1).completeSpace_l2_product_factor (0 : E1))

private noncomputable def original : KleinerLottApprox base base (1 / 800 : ℝ) :=
  (IsometryEquiv.refl X1).toKleinerLottApprox rfl (by norm_num) (by norm_num)

private theorem center_bound : dist base center ≤ 4 := by
  let m : X1 := WithLp.toLp 2 (axis 3, 0)
  have h₁ : dist base m = 3 := by
    change dist (WithLp.toLp 2 ((0 : E1), (0 : ℚ))) (WithLp.toLp 2 (axis 3, 0)) = _
    rw [(WithLp.isometry_prodMk_right (E := E1) (0 : ℚ)).dist_eq]
    norm_num [axis, dist_zero_left, PiLp.norm_single]
  have h₂ : dist m center = 1 := by
    change dist (WithLp.toLp 2 (axis 3, (0 : ℚ))) (WithLp.toLp 2 (axis 3, 1)) = _
    rw [(WithLp.isometry_prodMk_left (axis 3)).dist_eq (0 : ℚ) 1]
    norm_num [Rat.dist_eq]
  calc
    dist base center ≤ dist base m + dist m center := dist_triangle _ _ _
    _ = 4 := by rw [h₁, h₂]; norm_num

private theorem small_error : (1 / 800 : ℝ) ≤ recenterTolerance (1 / 2) 4 := by
  norm_num [recenterTolerance]

theorem incomplete_source_rank_one_actual_recenter :
    ¬ CompleteSpace X1 ∧
    ∃ φc : KleinerLottApprox center (WithLp.toLp 2 ((0 : E1), (1 : ℚ))) (1 / 2 : ℝ),
      (∀ x : X1, φc.toFun x = WithLp.toLp 2 (x.fst - axis 3, x.snd)) ∧
      φc.toFun outside = WithLp.toLp 2 (axis 97, (5 : ℚ)) ∧
      outside ∉ ball center 2 := by
  let φc := original.recenterEuclidean center (by norm_num) (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 4) small_error center_bound
  refine ⟨source_incomplete, φc, ?_, ?_, ?_⟩
  · intro x
    rfl
  · change WithLp.toLp 2 (axis 100 - axis 3, (5 : ℚ)) = _
    congr 2
    ext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    norm_num [axis, PiLp.sub_apply, PiLp.single_apply]
  · intro hm
    have h := WithLp.dist_snd_le outside center
    have hn : dist outside.snd center.snd = 4 := by
      change dist (5 : ℚ) 1 = 4
      norm_num [Rat.dist_eq]
    rw [hn] at h
    exact (not_lt_of_ge h) ((Metric.mem_ball.mp hm).trans (by norm_num))

private abbrev E0 := EuclideanSpace ℝ (Fin 0)
private abbrev X0 := WithLp 2 (E0 × ℚ)
private noncomputable def base0 : X0 := WithLp.toLp 2 (0, 0)
private noncomputable def center0 : X0 := WithLp.toLp 2 (0, 1)

private noncomputable def original0 : KleinerLottApprox base0 base0 (1 / 500 : ℝ) :=
  (IsometryEquiv.refl X0).toKleinerLottApprox rfl (by norm_num) (by norm_num)

theorem rank_zero_actual_recenter :
    ∃ φc : KleinerLottApprox center0 center0 (1 / 2 : ℝ),
      ∀ x : X0, φc.toFun x = x := by
  have hc : dist base0 center0 ≤ 1 := by
    change dist (WithLp.toLp 2 ((0 : E0), (0 : ℚ))) (WithLp.toLp 2 ((0 : E0), 1)) ≤ _
    rw [(WithLp.isometry_prodMk_left (0 : E0)).dist_eq (0 : ℚ) 1]
    norm_num [Rat.dist_eq]
  let φc := original0.recenterEuclidean (δ := (1 / 2 : ℝ)) center0 (by norm_num) (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num [recenterTolerance]) hc
  refine ⟨φc, ?_⟩
  intro x
  change WithLp.toLp 2 (x.fst - (0 : E0), x.snd) = x
  rw [sub_zero]
  rfl

end GCNormalizedSplittingRecenteringReview

namespace GCAC80Review

open GC.MetricGeometry Metric Set

private noncomputable def bumpApprox {T : Type*} [MetricSpace T] (p c b : T)
    {ε : ℝ} (hε : 0 < ε) (hεone : ε < 1) (hpc : p ≠ c)
    (hcb : dist c b ≤ ε / 4) : KleinerLottApprox p p ε := by
  classical
  let f : T → T := fun x => if x = c then b else x
  have hf (x : T) : dist (f x) x ≤ ε / 4 := by
    dsimp only [f]
    split_ifs with hx
    · subst x
      simpa only [dist_comm] using hcb
    · simpa only [dist_self] using (by linarith : (0 : ℝ) ≤ ε / 4)
  refine ⟨hε, hεone, f, ?_, ?_, ?_⟩
  · simp only [f, ite_eq_right hpc]
  · intro x _ y _
    have ht := dist_triangle4 (f x) x y (f y)
    have hs := dist_triangle4 x (f x) (f y) y
    rw [dist_comm y (f y)] at ht
    rw [dist_comm x (f x)] at hs
    exact abs_le.mpr ⟨by linarith [hf x, hf y], by linarith [hf x, hf y]⟩
  · intro y hy
    have hm : f y ∈ f '' ball p ε⁻¹ := ⟨y, by change dist y p < ε⁻¹; linarith, rfl⟩
    have hh := Metric.infDist_le_dist_of_mem (x := y) hm
    rw [dist_comm y (f y)] at hh
    exact hh.trans (by linarith [hf y])

private abbrev E := EuclideanSpace ℝ (Fin 1)
private abbrev O := EuclideanSpace ℝ (Fin 0)
private abbrev X := WithLp 2 (E × E)
private noncomputable def v (t : ℝ) : E := PiLp.single 2 0 t
private theorem prod_bound (x y : X) :
    dist x y ≤ dist x.fst y.fst + dist x.snd y.snd := by
  have hh := WithLp.prod_dist_sq_eq_add_sq x y
  nlinarith [dist_nonneg (x := x.fst) (y := y.fst),
    dist_nonneg (x := x.snd) (y := y.snd), dist_nonneg (x := x) (y := y)]

private noncomputable def p : X := WithLp.toLp 2 (0, 0)
private noncomputable def c : X := WithLp.toLp 2 (v 1, v 1)
private noncomputable def ε : ℝ := 1 / 1000
private noncomputable def Q : E ≃ₗᵢ[ℝ] WithLp 2 (E × O) :=
  (LinearIsometryEquiv.withLpProdUnique 2 ℝ E O).symm
private noncomputable def H : WithLp 2 (O × E) ≃ᵢ E :=
  IsometryEquiv.withLpUniqueProd 2 O E

private theorem v_dist (s t : ℝ) : dist (v s) (v t) = |s - t| := by
  rw [dist_eq_norm]
  change ‖(PiLp.single 2 0 s : E) - PiLp.single 2 0 t‖ = _
  rw [← PiLp.single_sub, PiLp.norm_single]
  exact Real.norm_eq_abs _

private noncomputable def G : KleinerLottApprox (0 : E) (0 : E) ε :=
  bumpApprox 0 (v 1) (v (1 + ε / 4)) (by norm_num [ε]) (by norm_num [ε])
    (by intro hh; have hz := congrArg (fun z : E => z 0) hh; norm_num [v] at hz)
    (by rw [v_dist]; norm_num [ε])

private theorem G_displacement (x : E) : dist (G.toFun x) x ≤ ε / 4 := by
  classical
  simp only [G, bumpApprox]
  split_ifs with hx
  · subst x
    rw [v_dist]
    norm_num [ε]
  · simp only [dist_self]
    norm_num [ε]

private noncomputable def F : KleinerLottApprox (WithLp.toLp 2 ((0 : O), (0 : E))) (0 : E) ε :=
  G.comapSourceIsometryAt H (WithLp.toLp 2 (0, 0)) rfl

private noncomputable def φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : E), (0 : E))) ε :=
  (IsometryEquiv.refl X).toKleinerLottApprox rfl (by norm_num [ε]) (by norm_num [ε])

private theorem original_compatibility (x : X) :
    dist (WithLp.toLp 2 (G.toFun (Q (φ.toFun x).fst).fst,
      F.toFun (WithLp.toLp 2 ((Q (φ.toFun x).fst).snd, (φ.toFun x).snd))))
      (φ.toFun x) ≤ ε := by
  change dist (WithLp.toLp 2 (G.toFun x.fst, G.toFun x.snd)) x ≤ ε
  have ht := prod_bound (WithLp.toLp 2 (G.toFun x.fst, G.toFun x.snd)) x
  simp only [WithLp.toLp_fst, WithLp.toLp_snd] at ht
  have he : 0 < ε := by norm_num [ε]
  linarith [G_displacement x.fst, G_displacement x.snd]

private theorem nonzero_joint_repairs :
    dist (G.toFun (v 1)) (v 1) = ε / 4 ∧
    dist (F.toFun (WithLp.toLp 2 ((0 : O), v 1))) (v 1) = ε / 4 := by
  classical
  have hg : G.toFun (v 1) = v (1 + ε / 4) := by
    simp only [G, bumpApprox]
    rw [ite_true]
  constructor
  · rw [hg, v_dist]
    norm_num [ε]
  · change dist (G.toFun (v 1)) (v 1) = ε / 4
    rw [hg, v_dist]
    norm_num [ε]

private theorem bumped_equal_rank_recentered_compatibility :
    ∃ (Ec : KleinerLottApprox (0 : E) (0 : E) (1 / 2))
      (Fc : KleinerLottApprox (WithLp.toLp 2 ((0 : O), v 1)) (v 1) (1 / 2)),
      ∀ x ∈ ball c 2,
        dist (WithLp.toLp 2 (Ec.toFun (x.fst - v 1),
          Fc.toFun (WithLp.toLp 2 ((0 : O), x.snd))))
          (WithLp.toLp 2 (x.fst - v 1, x.snd)) < 1 / 2 := by
  have hc : dist p c ≤ (2 : ℝ) := by
    have hh := prod_bound p c
    change dist p c ≤ dist (0 : E) (v 1) + dist (0 : E) (v 1) at hh
    have hv : dist (0 : E) (v 1) = 1 := by
      have hz : (0 : E) = v 0 := by ext i; simp [v, PiLp.single_apply]
      rw [hz, v_dist]
      norm_num
    simpa only [hv, one_add_one_eq_two] using hh
  obtain ⟨Ec, Fc, hEc⟩ := exists_recentered_splitting_compatibility_witnesses
    φ φ Q G F (fun x _ => original_compatibility x)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num [ε, recenterTolerance] : ε ≤ recenterTolerance (1 / 2) (2 + 1)) hc
  refine ⟨Ec, Fc, ?_⟩
  intro x hx
  have hh := hEc x (by simpa using hx)
  have hφ (z : X) : φ.toFun z = z := rfl
  have hQ (z : E) : Q z = WithLp.toLp 2 (z, (0 : O)) := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  simp only [hφ, hQ, WithLp.toLp_fst, WithLp.toLp_snd] at hh
  exact hh

private theorem repeated_center_arguments_away_from_source_center :
    ∃ x y : X, x ≠ c ∧ y ≠ c ∧ x ∈ ball c 2 ∧ y ∈ ball c 2 ∧
      x.fst = c.fst ∧ y.snd = c.snd := by
  let x : X := WithLp.toLp 2 (v 1, v 2)
  let y : X := WithLp.toLp 2 (v 2, v 1)
  refine ⟨x, y, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro hh
    have hh' := congrArg (fun z : X => z.snd 0) hh
    norm_num [x, c, v] at hh'
  · intro hh
    have hh' := congrArg (fun z : X => z.fst 0) hh
    norm_num [y, c, v] at hh'
  · have hh := prod_bound x c
    change dist x c ≤ dist (v 1) (v 1) + dist (v 2) (v 1) at hh
    rw [dist_self, v_dist] at hh
    change dist x c < 2
    norm_num at hh ⊢
    linarith
  · have hh := prod_bound y c
    change dist y c ≤ dist (v 2) (v 1) + dist (v 1) (v 1) at hh
    rw [dist_self, v_dist] at hh
    change dist y c < 2
    norm_num at hh ⊢
    linarith

#print axioms nonzero_joint_repairs
#print axioms bumped_equal_rank_recentered_compatibility
#print axioms repeated_center_arguments_away_from_source_center

end GCAC80Review

#lint- only unusedArguments simpNF synTaut

namespace GCAC80Review

open GC.MetricGeometry Metric Set

private theorem original_recentered_maps_compatible :
    ∃ Gc : KleinerLottApprox c (WithLp.toLp 2 ((0 : E), v 1)) (1 / 2 : ℝ),
      (∀ x : X, Gc.toFun x = WithLp.toLp 2 (x.fst - v 1, x.snd)) ∧
      SplittingCompatible Gc Gc (1 / 2 : ℝ) := by
  have hc : dist p c ≤ (2 : ℝ) := by
    have hh := prod_bound p c
    have hv : dist (0 : E) (v 1) = 1 := by
      norm_num [v, dist_zero_left, PiLp.norm_single]
    change dist p c ≤ dist (0 : E) (v 1) + dist (0 : E) (v 1) at hh
    simpa only [hv, one_add_one_eq_two] using hh
  have hcomp : SplittingCompatible φ φ ε :=
    ⟨by omega, Q, G, F, fun x _ => original_compatibility x⟩
  have hnew := hcomp.recenterEuclidean c
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num [ε, recenterTolerance] : ε ≤ recenterTolerance (1 / 2) (2 + 1)) hc
  exact ⟨_, (fun _ => rfl), hnew⟩

#print axioms original_recentered_maps_compatible

end GCAC80Review

#print axioms GC.MetricGeometry.KleinerLottApprox.mapTargetIsometry
#print axioms GC.MetricGeometry.KleinerLottApprox.mapTargetIsometry_apply
#print axioms GC.MetricGeometry.KleinerLottApprox.mapTargetIsometryAt
#print axioms GC.MetricGeometry.KleinerLottApprox.mapTargetIsometryAt_apply
#print axioms GC.MetricGeometry.KleinerLottApprox.comapSourceIsometryAt
#print axioms GC.MetricGeometry.KleinerLottApprox.comapSourceIsometryAt_apply
#print axioms GC.MetricGeometry.KleinerLottApprox.comapSourceIsometry
#print axioms GC.MetricGeometry.KleinerLottApprox.comapSourceIsometry_apply
#print axioms GC.MetricGeometry.KleinerLottApprox.recenterEuclidean
#print axioms GC.MetricGeometry.KleinerLottApprox.recenterEuclidean_apply
#print axioms GC.MetricGeometry.exists_recentered_splitting_compatibility_witnesses
#print axioms GC.MetricGeometry.SplittingCompatible.recenterEuclidean
#print axioms GCNormalizedSplittingRecenteringReview.incomplete_source_rank_one_actual_recenter
#print axioms GCNormalizedSplittingRecenteringReview.rank_zero_actual_recenter
#lint- only unusedArguments simpNF synTaut
```
