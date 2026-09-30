# Full AC74 independent acceptance

Five public theorems in four leaves add five owned declarations. The336-module gate checks1457 declarations in3171 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy lint and accepted-import review lint are silent; the review emits12 standard axiom reports. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside the new closures. The separate blueprint static audit passes; no new PDF/Overleaf build, migrated-root acceptance or human approval is claimed.

One agent implemented the one-product producer and full paired extraction, root read the complete proofs, and another agent independently reviewed and recompiled them. Root implemented the PointedGHConverges-only wrapper; the second agent independently checked its source/target indices and full output and compiled a concrete original-input regression. The final driver imports the actual accepted leaves, with no copied production theorem bodies.

The one-product theorem uses exactly the supplied source maps on its returned subsequence, with restrictions/enlargements changing only carriers/error bounds. Both factor-domain membership and full Euclidean/transverse product error are exposed. The two-product theorem applies that producer twice while preserving the first output through the second extraction. Both limit isometries have the SAME specified target as domain. The pointed-only wrapper first chooses actual maps from pointed convergence. Its final original indices are beta(alpha(i)), while its source radii/errors are J(alpha(i)),epsilon(alpha(i)); the return value preserves this distinction exactly. No chosen source map is assumed to be the identity.

The concrete source sequence is R times Ioi(-3(i+1)); the target is R squared and original source maps are inclusions at radii i+1/errors1/[100(i+1)]. The tests prove the sources AND transverse factors are incomplete. The two original whole-source KL maps are the identity and reflection of the first coordinate, and their difference is proved for every index. The supplied-map regression retains the entire paired conclusion through the original inclusion. The pointed-only regression starts with actual pointed convergence and retains all returned R/epsilon/f, both factor maps, all growth/error limits, both factor/source convergences and the two full controls through that SAME returned f. It does not replace f or impose an identity on it.

Source review uses the actual KL4.17 proof and frozen AC74 body, with retained errata. The earlier strict/equal-rank convention mismatch is preserved explicitly. This metric producer neither needs the rank inequalities nor infers compactness from the source's shrinking-ball typo. Full AC74 is complete. AC75 transfer and AC76 uniform compatibility remain separate acceptance batches; Chapters3-4 are not declared complete. Blueprint207 and the migration boundary remain unchanged.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.PointedFullProductLimits
import Mathlib.Tactic

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GCFullProductGivenMapsReview

open GC.MetricGeometry

private def radius (i : ℕ) : ℝ := (i : ℝ) + 1
private theorem radius_one (i : ℕ) : 1 ≤ radius i := by dsimp [radius]; linarith [Nat.cast_nonneg (α := ℝ) i]
private theorem radius_pos (i : ℕ) : 0 < radius i := lt_of_lt_of_le (by norm_num) (radius_one i)
private theorem radius_top : Tendsto radius atTop atTop :=
  tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
private noncomputable def errors (i : ℕ) : ℝ := (1 / ((i : ℝ) + 1)) / 100
private theorem errors_pos (i : ℕ) : 0 < errors i := by dsimp [errors]; positivity
private theorem errors_lt (i : ℕ) : errors i < radius i := by
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hh : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  dsimp [errors, radius]
  linarith
private theorem errors_zero : Tendsto errors atTop (𝓝 0) := by
  change Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1)) / 100) atTop (𝓝 0)
  simpa only [zero_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100

private abbrev Factor (i : ℕ) := Ioi (-(3 * radius i))
private def factorBase (i : ℕ) : Factor i := ⟨0, by change -(3 * radius i) < 0; linarith [radius_pos i]⟩
private abbrev Source (i : ℕ) := WithLp 2 (ℝ × Factor i)
private abbrev Target := WithLp 2 (ℝ × ℝ)
private def sourceBase (i : ℕ) : Source i := WithLp.toLp 2 (0, factorBase i)
private def targetBase : Target := WithLp.toLp 2 (0, 0)
private def inclusion (i : ℕ) (x : Source i) : Target := WithLp.toLp 2 (x.fst, x.snd.val)

private theorem inclusion_isometry (i : ℕ) : Isometry (inclusion i) := by
  apply Isometry.of_dist_eq
  intro x y
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  simp only [WithLp.prod_dist_sq_eq_add_sq, inclusion, WithLp.toLp_fst, WithLp.toLp_snd,
    Subtype.dist_eq]

private theorem inclusion_base (i : ℕ) : inclusion i (sourceBase i) = targetBase := rfl

private def originalApprox (i : ℕ) :
    PointedBallApprox (sourceBase i) targetBase (radius i) (errors i) where
  error_pos := errors_pos i
  error_lt_radius := errors_lt i
  toFun x := inclusion i x.val
  basepoint := rfl
  distortion x y := by
    simpa only [(inclusion_isometry i).dist_eq, sub_self, abs_zero] using errors_pos i
  coverage y hy := by
    have hs := (WithLp.dist_snd_le y targetBase).trans hy
    change |y.snd - 0| ≤ radius i - errors i at hs
    rw [sub_zero] at hs
    have hsrc : -(3 * radius i) < y.snd := by
      linarith [(abs_le.mp hs).1, errors_pos i, radius_pos i]
    let x : Source i := WithLp.toLp 2 (y.fst, ⟨y.snd, hsrc⟩)
    have himage : inclusion i x = y := rfl
    have hrad : dist x (sourceBase i) = dist y targetBase := by
      rw [← (inclusion_isometry i).dist_eq, inclusion_base, himage]
    refine ⟨⟨x, ?_⟩, ?_⟩
    · rw [hrad]
      linarith [errors_pos i]
    · change dist y (inclusion i x) < errors i
      rw [himage, dist_self]
      exact errors_pos i

private theorem errors_lt_one (i : ℕ) : errors i < 1 := by
  have hh : 1 / ((i : ℝ) + 1) ≤ 1 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) i])
  dsimp [errors]
  linarith

private def originalSplitting (i : ℕ) :
    KleinerLottApprox (sourceBase i) (WithLp.toLp 2 ((0 : ℝ), factorBase i)) (errors i) where
  error_pos := errors_pos i
  error_lt_one := errors_lt_one i
  toFun := id
  basepoint := rfl
  distortion _ _ _ _ := by simpa only [id_eq, sub_self, abs_zero] using (errors_pos i).le
  coverage y hy := by
    change dist y (sourceBase i) < (errors i)⁻¹ - errors i at hy
    have hmem : y ∈ id '' ball (sourceBase i) (errors i)⁻¹ :=
      ⟨y, show dist y (sourceBase i) < (errors i)⁻¹ by linarith [errors_pos i], rfl⟩
    exact (Metric.infDist_le_dist_of_mem hmem).trans (by simpa using (errors_pos i).le)

theorem factor_not_complete (i : ℕ) : ¬ CompleteSpace (Factor i) := by
  intro h
  let := h
  have hi : Isometry (Subtype.val : Factor i → ℝ) := isometry_subtype_coe
  have hc : IsClosed (Ioi (-(3 * radius i))) := by
    simpa only [Subtype.range_val] using hi.isUniformInducing.isComplete_range.isClosed
  have hz : -(3 * radius i) ∈ closure (Ioi (-(3 * radius i))) := by
    simpa only [closure_Ioi, mem_Ici] using (le_rfl : -(3 * radius i) ≤ -(3 * radius i))
  rw [hc.closure_eq] at hz
  change -(3 * radius i) < -(3 * radius i) at hz
  exact lt_irrefl (-(3 * radius i)) hz

theorem source_not_complete (i : ℕ) : ¬ CompleteSpace (Source i) := by
  intro h
  let := h
  exact factor_not_complete i ((IsometryEquiv.refl (Source i)).completeSpace_l2_product_factor (0 : ℝ))

private def ConcreteControl : Prop :=
    ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (χ : ℕ → ℕ), StrictMono χ ∧ ProperSpace W ∧ CompleteSpace W ∧
        PointedGHConverges (fun i => factorBase (χ i)) w ∧
        PointedGHConverges (fun i => sourceBase (χ i)) targetBase ∧
        ∃ e : Target ≃ᵢ WithLp 2 (ℝ × W), e targetBase = WithLp.toLp 2 ((0 : ℝ), w) ∧
          ∃ P τ : ℕ → ℝ, Tendsto P atTop atTop ∧ Tendsto τ atTop (𝓝 0) ∧
            ∃ g : ∀ i, PointedBallApprox (factorBase (χ i)) w (P i) (τ i),
              ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
                S ≤ radius (χ i) ∧
                ∀ x : BallCarrier (sourceBase (χ i)) (radius (χ i)), dist x.val (sourceBase (χ i)) ≤ S →
                  (dist ((originalSplitting (χ i)).toFun x.val).snd (factorBase (χ i)) ≤ P i ∧
                  ∀ hx : dist ((originalSplitting (χ i)).toFun x.val).snd (factorBase (χ i)) ≤ P i,
                    dist (WithLp.toLp 2 (((originalSplitting (χ i)).toFun x.val).fst,
                      (g i).toFun ⟨((originalSplitting (χ i)).toFun x.val).snd, hx⟩))
                      (e ((originalApprox (χ i)).toFun x)) < ζ)

theorem original_full_product_maps_with_incomplete_sources : ConcreteControl :=
  exists_full_product_limit_of_approximate_products_with_given_maps
    originalApprox radius_top errors_zero originalSplitting errors_zero

end GCFullProductGivenMapsReview

#print axioms GCFullProductGivenMapsReview.factor_not_complete
#print axioms GCFullProductGivenMapsReview.source_not_complete
#print axioms GCFullProductGivenMapsReview.original_full_product_maps_with_incomplete_sources
#lint- only unusedArguments simpNF synTaut

namespace GCFullProductGivenMapsReview

open GC.MetricGeometry

private noncomputable def reflection (i : ℕ) : Source i ≃ᵢ Source i :=
  IsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.neg ℝ).toIsometryEquiv
    (IsometryEquiv.refl (Factor i))

private theorem reflection_base (i : ℕ) : reflection i (sourceBase i) = sourceBase i := by
  change WithLp.toLp 2 (-(0 : ℝ), factorBase i) = sourceBase i
  rw [neg_zero]
  rfl

private noncomputable def reflectedSplitting (i : ℕ) :
    GC.MetricGeometry.KleinerLottApprox (sourceBase i)
      (WithLp.toLp 2 ((0 : ℝ), factorBase i)) (errors i) where
  error_pos := errors_pos i
  error_lt_one := errors_lt_one i
  toFun := reflection i
  basepoint := reflection_base i
  distortion x _ y _ := by
    rw [(reflection i).dist_eq, sub_self, abs_zero]
    exact (errors_pos i).le
  coverage y hy := by
    change dist y (sourceBase i) < (errors i)⁻¹ - errors i at hy
    have hm : (reflection i).symm y ∈ ball (sourceBase i) (errors i)⁻¹ := by
      rw [mem_ball, ← (reflection i).dist_eq, (reflection i).apply_symm_apply, reflection_base]
      linarith [errors_pos i]
    have hi : y ∈ reflection i '' ball (sourceBase i) (errors i)⁻¹ :=
      ⟨(reflection i).symm y, hm, (reflection i).apply_symm_apply y⟩
    exact (Metric.infDist_le_dist_of_mem hi).trans (by simpa using (errors_pos i).le)

private theorem original_maps_are_distinct (i : ℕ) :
    (originalSplitting i).toFun ≠ (reflectedSplitting i).toFun := by
  intro hh
  have he := congrArg (fun f : Source i → Source i => (f (WithLp.toLp 2 (1, factorBase i))).fst) hh
  change (1 : ℝ) = -1 at he
  norm_num at he

private def ConcreteTwoControl : Prop :=
    ∃ (W : Type) (mW : MetricSpace W), letI := mW
      ∃ (V : Type) (mV : MetricSpace V), letI := mV
        ∃ (w : W) (v : V) (χ : ℕ → ℕ), StrictMono χ ∧
          ProperSpace W ∧ CompleteSpace W ∧ ProperSpace V ∧ CompleteSpace V ∧
          PointedGHConverges (fun i => factorBase (χ i)) w ∧
          PointedGHConverges (fun i => factorBase (χ i)) v ∧
          PointedGHConverges (fun i => sourceBase (χ i)) targetBase ∧
          ∃ (eA : Target ≃ᵢ WithLp 2 (ℝ × W)) (eB : Target ≃ᵢ WithLp 2 (ℝ × V)),
            eA targetBase = WithLp.toLp 2 ((0 : ℝ), w) ∧ eB targetBase = WithLp.toLp 2 ((0 : ℝ), v) ∧
            ∃ P τ Q η : ℕ → ℝ,
              Tendsto P atTop atTop ∧ Tendsto τ atTop (𝓝 0) ∧
              Tendsto Q atTop atTop ∧ Tendsto η atTop (𝓝 0) ∧
              ∃ (g : ∀ i, PointedBallApprox (factorBase (χ i)) w (P i) (τ i))
                (h : ∀ i, PointedBallApprox (factorBase (χ i)) v (Q i) (η i)),
                ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
                  S ≤ radius (χ i) ∧
                  ∀ x : BallCarrier (sourceBase (χ i)) (radius (χ i)), dist x.val (sourceBase (χ i)) ≤ S →
                    (dist ((originalSplitting (χ i)).toFun x.val).snd (factorBase (χ i)) ≤ P i ∧
                      ∀ hx : dist ((originalSplitting (χ i)).toFun x.val).snd (factorBase (χ i)) ≤ P i,
                        dist (WithLp.toLp 2 (((originalSplitting (χ i)).toFun x.val).fst,
                          (g i).toFun ⟨((originalSplitting (χ i)).toFun x.val).snd, hx⟩))
                          (eA ((originalApprox (χ i)).toFun x)) < ζ) ∧
                    (dist ((reflectedSplitting (χ i)).toFun x.val).snd (factorBase (χ i)) ≤ Q i ∧
                      ∀ hx : dist ((reflectedSplitting (χ i)).toFun x.val).snd (factorBase (χ i)) ≤ Q i,
                        dist (WithLp.toLp 2 (((reflectedSplitting (χ i)).toFun x.val).fst,
                          (h i).toFun ⟨((reflectedSplitting (χ i)).toFun x.val).snd, hx⟩))
                          (eB ((originalApprox (χ i)).toFun x)) < ζ)


theorem original_two_product_maps_with_incomplete_sources : ConcreteTwoControl :=
  GC.MetricGeometry.exists_two_full_product_limits_of_approximate_products_with_given_maps
    originalApprox radius_top errors_zero originalSplitting errors_zero
    reflectedSplitting errors_zero

#print axioms original_maps_are_distinct
#print axioms original_two_product_maps_with_incomplete_sources

end GCFullProductGivenMapsReview

#lint- only unusedArguments simpNF synTaut

namespace GCFullProductGivenMapsReview

open GC.MetricGeometry

private theorem original_pointed_convergence : PointedGHConverges sourceBase targetBase := by
  refine ⟨inferInstance, ?_⟩
  intro S η hη hηS
  filter_upwards [radius_top.eventually (eventually_ge_atTop S),
    errors_zero.eventually (eventually_lt_nhds (by positivity : 0 < η / 2))] with i hiR hiε
  exact ⟨((originalApprox i).restrict (by linarith) hiR).enlargeError (by linarith) hηS⟩

private def ConcretePointedTwoControl : Prop :=
    ∃ (W : Type) (mW : MetricSpace W), letI := mW
      ∃ (V : Type) (mV : MetricSpace V), letI := mV
        ∃ (w : W) (v : V) (χ : ℕ → ℕ), StrictMono χ ∧
          ProperSpace W ∧ CompleteSpace W ∧ ProperSpace V ∧ CompleteSpace V ∧
          PointedGHConverges (fun i => factorBase (χ i)) w ∧
          PointedGHConverges (fun i => factorBase (χ i)) v ∧
          PointedGHConverges (fun i => sourceBase (χ i)) targetBase ∧
          ∃ (eA : Target ≃ᵢ WithLp 2 (ℝ × W)) (eB : Target ≃ᵢ WithLp 2 (ℝ × V)),
            eA targetBase = WithLp.toLp 2 ((0 : ℝ), w) ∧ eB targetBase = WithLp.toLp 2 ((0 : ℝ), v) ∧
            ∃ R ε P τ Q η : ℕ → ℝ,
              Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
              Tendsto P atTop atTop ∧ Tendsto τ atTop (𝓝 0) ∧
              Tendsto Q atTop atTop ∧ Tendsto η atTop (𝓝 0) ∧
              ∃ (f : ∀ i, PointedBallApprox (sourceBase (χ i)) targetBase (R i) (ε i))
                (g : ∀ i, PointedBallApprox (factorBase (χ i)) w (P i) (τ i))
                (h : ∀ i, PointedBallApprox (factorBase (χ i)) v (Q i) (η i)),
                ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
                  S ≤ R i ∧
                  ∀ x : BallCarrier (sourceBase (χ i)) (R i), dist x.val (sourceBase (χ i)) ≤ S →
                    (dist ((originalSplitting (χ i)).toFun x.val).snd (factorBase (χ i)) ≤ P i ∧
                      ∀ hx : dist ((originalSplitting (χ i)).toFun x.val).snd (factorBase (χ i)) ≤ P i,
                        dist (WithLp.toLp 2 (((originalSplitting (χ i)).toFun x.val).fst,
                          (g i).toFun ⟨((originalSplitting (χ i)).toFun x.val).snd, hx⟩))
                          (eA ((f i).toFun x)) < ζ) ∧
                    (dist ((reflectedSplitting (χ i)).toFun x.val).snd (factorBase (χ i)) ≤ Q i ∧
                      ∀ hx : dist ((reflectedSplitting (χ i)).toFun x.val).snd (factorBase (χ i)) ≤ Q i,
                        dist (WithLp.toLp 2 (((reflectedSplitting (χ i)).toFun x.val).fst,
                          (h i).toFun ⟨((reflectedSplitting (χ i)).toFun x.val).snd, hx⟩))
                          (eB ((f i).toFun x)) < ζ)


theorem original_pointed_two_product_maps_with_incomplete_sources : ConcretePointedTwoControl :=
  original_pointed_convergence.exists_two_full_product_limits
    originalSplitting errors_zero reflectedSplitting errors_zero

#print axioms original_pointed_convergence
#print axioms original_pointed_two_product_maps_with_incomplete_sources

end GCFullProductGivenMapsReview

#lint- only unusedArguments simpNF synTaut

#print axioms GC.MetricGeometry.KleinerLottApprox.productLimitApprox_factor_mem
#print axioms GC.MetricGeometry.KleinerLottApprox.productLimitApprox_apply
#print axioms GC.MetricGeometry.exists_full_product_limit_of_approximate_products_with_given_maps
#print axioms GC.MetricGeometry.exists_two_full_product_limits_of_approximate_products_with_given_maps
#print axioms GC.MetricGeometry.PointedGHConverges.exists_two_full_product_limits
```
