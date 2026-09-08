import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra
import DifferentialGeometry.Analysis.Calculus.Trace
import DifferentialGeometry.Analysis.ODE.InvariantSet
import DifferentialGeometry.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem two_thirds_trace_sq_le_trace_curvatureOperatorReactionEndomorphism3
    (hdim : Module.finrank ℝ V = 3) (A : V →ₗ[ℝ] V) (hA : A.IsSymmetric) :
    (2 / 3 : ℝ) * (LinearMap.trace ℝ V A) ^ 2 ≤
      LinearMap.trace ℝ V (curvatureOperatorReactionEndomorphism3 A) := by
  rw [trace_curvatureOperatorReactionEndomorphism3 hdim]
  have h := hA.trace_sq_le_finrank_mul_trace_comp
  rw [hdim] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

end DifferentialGeometry.Geometry.Curvature.DimensionThree

namespace DifferentialGeometry.Analysis

private theorem lower_barrier_of_deriv_pos_at_boundary {f f' : ℝ → ℝ} {a b c : ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hd : ∀ x ∈ Set.Ico a b, HasDerivWithinAt f (f' x) (Set.Ici x) x)
    (ha : c ≤ f a) (hpos : ∀ x ∈ Set.Ico a b, f x = c → 0 < f' x) :
    ∀ ⦃x⦄, x ∈ Set.Icc a b → c ≤ f x := by
  have h := image_le_of_deriv_right_lt_deriv_boundary
    hf.neg (fun x hx => (hd x hx).neg) (B := fun _ => -c) (B' := fun _ => 0)
    (neg_le_neg ha) (fun x => hasDerivAt_const x (-c)) (by
      intro x hx hxc
      have hx' : f x = c := neg_injective hxc
      exact neg_neg_of_pos (hpos x hx hx'))
  intro x hx
  exact neg_le_neg_iff.mp (h hx)

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem trace_normalized_curvature_reaction_lower_bound
    (hdim : Module.finrank ℝ V = 3) (A : V →L[ℝ] V) (hA : A.toLinearMap.IsSymmetric) :
    LinearMap.trace ℝ V A.toLinearMap + (2 / 3 : ℝ) * (LinearMap.trace ℝ V A.toLinearMap) ^ 2 ≤
      LinearMap.trace ℝ V
        (A + (curvatureOperatorReactionEndomorphism3 A.toLinearMap).toContinuousLinearMap).toLinearMap := by
  change _ ≤ LinearMap.trace ℝ V (A.toLinearMap + curvatureOperatorReactionEndomorphism3 A.toLinearMap)
  rw [map_add]
  exact add_le_add_right (two_thirds_trace_sq_le_trace_curvatureOperatorReactionEndomorphism3 hdim _ hA) _

theorem neg_three_le_trace_of_normalized_curvature_reaction_ode
    (hdim : Module.finrank ℝ V = 3) {A : ℝ → V →L[ℝ] V} {a b : ℝ}
    (hA : ContinuousOn A (Set.Icc a b))
    (hsymm : ∀ t ∈ Set.Icc a b, (A t).toLinearMap.IsSymmetric)
    (hode : ∀ t ∈ Set.Ico a b, HasDerivWithinAt A
      (A t + (curvatureOperatorReactionEndomorphism3 (A t).toLinearMap).toContinuousLinearMap)
      (Set.Icc a b) t)
    (hinit : -3 ≤ LinearMap.trace ℝ V (A a).toLinearMap) :
    ∀ t ∈ Set.Icc a b, -3 ≤ LinearMap.trace ℝ V (A t).toLinearMap := by
  let tr : (V →L[ℝ] V) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((LinearMap.trace ℝ V).comp
      (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] V) ≃ₗ[ℝ] (V →L[ℝ] V)).symm.toLinearMap)
  have hcont : ContinuousOn (fun t => tr (A t)) (Set.Icc a b) := tr.continuous.comp_continuousOn hA
  have hderiv t (ht : t ∈ Set.Ico a b) :=
    DifferentialGeometry.Analysis.hasDerivWithinAt_linearMap_trace (hode t ht)
  apply DifferentialGeometry.Analysis.lower_barrier_of_deriv_pos_at_boundary hcont
    (fun t ht => (hderiv t ht).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Set.Icc_subset_Icc_left ht.1))) hinit
  intro t ht heq
  have hb := trace_normalized_curvature_reaction_lower_bound hdim (A t)
    (hsymm t ⟨ht.1, ht.2.le⟩)
  change LinearMap.trace ℝ V (A t).toLinearMap = -3 at heq
  rw [heq] at hb
  norm_num only [neg_add_rev, neg_mul, mul_neg, neg_neg, neg_sq, OfNat.ofNat_ne_zero, Nat.cast_ofNat] at hb
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hb

theorem isForwardInvariantForODE_neg_three_le_trace_normalized_curvature_reaction
    (hdim : Module.finrank ℝ V = 3) :
    DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODE
      (fun (_ : ℝ) (A : selfAdjoint (V →L[ℝ] V)) => A + curvatureOperatorReactionSelfAdjoint3 A)
      {A | -3 ≤ LinearMap.trace ℝ V (A : V →L[ℝ] V).toLinearMap} := by
  intro a b _ A hA hinit
  let inc : selfAdjoint (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) :=
    { toLinearMap :=
        { toFun := fun B => B.val
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      cont := continuous_subtype_val }
  have hcont : ContinuousOn (fun t => inc (A t)) (Set.Icc a b) :=
    inc.continuous.comp_continuousOn hA.continuousOn
  have hsymm t (_ : t ∈ Set.Icc a b) : (inc (A t)).toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (A t).property
  have hderiv t (ht : t ∈ Set.Ico a b) :=
    inc.hasFDerivAt.comp_hasDerivWithinAt t (hA t ⟨ht.1, ht.2.le⟩)
  exact neg_three_le_trace_of_normalized_curvature_reaction_ode hdim hcont hsymm hderiv hinit

end DifferentialGeometry.Geometry.Curvature.DimensionThree
