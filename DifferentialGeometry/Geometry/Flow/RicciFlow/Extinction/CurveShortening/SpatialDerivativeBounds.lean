import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ArcLengthTensorBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParameterDerivatives
import DifferentialGeometry.Geometry.Metric.Family.CovariantDerivativeBounds
import Mathlib.Analysis.Normed.Module.FiniteDimension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParameterSpeedBounds

open scoped ContDiff

namespace DifferentialGeometry.Analysis

private theorem exists_iteratedDeriv_bound_of_scalar {F α : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (n : ℕ) (x : α → ℝ) (f : α → ℝ → F)
    (hf : ∀ a, ContDiffAt ℝ n (f a) (x a))
    (hb : ∀ L : F →L[ℝ] ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a,
      ‖iteratedDeriv n (fun y => L (f a y)) (x a)‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖iteratedDeriv n (f a) (x a)‖ ≤ C := by
  classical
  let b := Module.finBasis ℝ F
  let L (i : Fin (Module.finrank ℝ F)) : F →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap
  choose C hC hbound using fun i => hb (L i)
  refine ⟨∑ i, C i * ‖b i‖, Finset.sum_nonneg fun i _ => mul_nonneg (hC i) (norm_nonneg _), ?_⟩
  intro a
  have hcoord (i : Fin (Module.finrank ℝ F)) :
      ‖b.equivFun (iteratedDeriv n (f a) (x a)) i‖ ≤ C i := by
    have heq : iteratedDeriv n (fun y => L i (f a y)) (x a) =
        L i (iteratedDeriv n (f a) (x a)) := by
      rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
        show (fun y => L i (f a y)) = L i ∘ f a from rfl,
        (L i).iteratedFDeriv_comp_left (hf a) le_rfl]
      rfl
    have h := hbound i a
    rw [heq] at h
    exact h
  conv_lhs => rw [← b.sum_equivFun (iteratedDeriv n (f a) (x a))]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hcoord i) (norm_nonneg _)

end DifferentialGeometry.Analysis

open Set
open scoped Manifold
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem exists_scalar_derivative_bound (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hambient : ∀ j, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (normSq0S (g t) (c.lift x t) (0 + j)
        (iterCov (g t) 0 (Tensor0SField.fromScalarField ∞ f hf) j (c.lift x t))) ≤ C)
    (hjets : ∀ j, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (c.normSq g (c.iteratedDs g j (c.unitTangent g)) x t) ≤ C)
    (n : ℕ)
    (hvb : ∀ i < n, ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, t ∈ J →
      ‖iteratedDeriv i (fun y => c.speed g y t) x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, t ∈ J →
      ‖iteratedDeriv n (fun y => f (c.lift y t)) x‖ ≤ C := by
  have hb (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, t ∈ J →
      ‖(c.ds g)^[k] (fun y τ => f (c.lift y τ)) x t‖ ≤ C := by
    obtain ⟨C, hC, hb⟩ := c.exists_iterated_ds_tensor_unitTangent_bound g hc hi
      (fun _ => Tensor0SField.fromScalarField ∞ f hf) hambient hjets k
    refine ⟨C, hC.le, ?_⟩
    simpa only [Tensor0SField.fromScalarField_apply, Real.norm_eq_abs] using hb
  obtain ⟨C, hC, hb⟩ := c.exists_iteratedDeriv_bound_of_iterate_ds g
    (fun y τ => f (c.lift y τ)) (univ ×ˢ J) n
    (fun p hp => (c.speed_contDiff g J hc hi p.2 hp.2).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top))
    (fun p hp => by
      have hq : ContDiffAt ℝ (∞ : ℕ∞ω)
          (fun y => f (c.lift y p.2)) p.1 :=
        (hf.contMDiffAt.comp p.1
          (contMDiffWithinAt_univ.mp
            (c.space_slice_contMDiffWithinAt J hc p.1 p.2 hp.2))).contDiffAt
      exact hq.of_le (WithTop.coe_le_coe.mpr le_top))
    (fun p hp => (c.speed_pos g hi p.1 p.2 hp.2).ne')
    (fun i hi => by
      obtain ⟨C, hC, hb⟩ := hvb i hi
      exact ⟨C, hC, fun p hp => hb p.1 p.2 hp.2⟩)
    (fun k _ => by
      obtain ⟨C, hC, hb⟩ := hb k
      exact ⟨C, hC, fun p hp => hb p.1 p.2 hp.2⟩)
  exact ⟨C, hC, fun x t ht => hb (x, t) ⟨mem_univ _, ht⟩⟩


theorem exists_iteratedDeriv_comp_lift_bound [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (c : CurveMap M) {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn (I := I) (M := M) D g)
    {K J : Set ℝ} (hK : IsCompact K) (hKreg : K ⊆ D.regular) (hJK : J ⊆ K)
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (f : M → F) (hf : ContMDiff I 𝓘(ℝ, F) ∞ f)
    (hjets : ∀ j, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (c.normSq g (c.iteratedDs g j (c.unitTangent g)) x t) ≤ C)
    (n : ℕ)
    (hvb : ∀ i < n, ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, t ∈ J →
      ‖iteratedDeriv i (fun y => c.speed g y t) x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, t ∈ J →
      ‖iteratedDeriv n (fun y => f (c.lift y t)) x‖ ≤ C := by
  have hmap (x t : ℝ) (ht : t ∈ J) :
      ContDiffAt ℝ n (fun y => f (c.lift y t)) x := by
    have h : ContDiffAt ℝ ∞ (fun y => f (c.lift y t)) x :=
      (hf.contMDiffAt.comp x
        (contMDiffWithinAt_univ.mp (c.space_slice_contMDiffWithinAt J hc x t ht))).contDiffAt
    exact h.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C, hC, hb⟩ := DifferentialGeometry.Analysis.exists_iteratedDeriv_bound_of_scalar
    n (fun p : ℝ × J => p.1) (fun p : ℝ × J => fun y => f (c.lift y p.2))
    (fun p => hmap p.1 p.2 p.2.property) (fun L => by
      have hLf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => L (f x)) := L.contMDiff.comp hf
      have hambient (j : ℕ) : ∃ C : ℝ, ∀ x t, t ∈ J →
          Real.sqrt (normSq0S (g t) (c.lift x t) (0 + j)
            (iterCov (g t) 0 (Tensor0SField.fromScalarField ∞ (fun x => L (f x)) hLf) j
              (c.lift x t))) ≤ C := by
        obtain ⟨C, _, hb⟩ := DifferentialGeometry.Geometry.Tensor.exists_pos_bound_iterCov_scalar_on_compact
          hg (fun x => L (f x)) hLf j hK isCompact_univ hKreg
        exact ⟨C, fun x t ht => hb t (hJK ht) (c.lift x t) (mem_univ _)⟩
      obtain ⟨C, hC, hb⟩ := exists_scalar_derivative_bound c g hc hi (fun x => L (f x)) hLf
        hambient hjets n hvb
      exact ⟨C, hC, fun p => hb p.1 p.2 p.2.property⟩)
  exact ⟨C, hC, fun x t ht => hb (x, ⟨t, ht⟩)⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap


namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}

theorem exists_iteratedDeriv_comp_lift_bounds_on_Ico_of_curvature_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (B : RicciBackground (I := I) (M := M) D a b) {T : ℝ}
    (haT : a < T) (hTb : T ≤ b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Ico a T)) {K : ℝ}
    (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K)
    (f : M → F) (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (s : ℝ) (has : a < s) :
    ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, t ∈ Ico s T →
      ‖iteratedDeriv j (fun y => f (c.lift y t)) x‖ ≤ C := by
  have hsub : Ico s T ⊆ Ico a T := fun t ht => ⟨has.le.trans ht.1, ht.2⟩
  have hT := c.exists_iteratedDs_unitTangent_bounds_on_Ico_of_curvature_le B haT hTb hc hcurv s has
  have hv := c.exists_iteratedDeriv_speed_bounds_on_Ico_of_curvature_le B haT hTb hc hcurv s has
  intro j
  apply c.exists_iteratedDeriv_comp_lift_bound B.family.metric B.smooth isCompact_Icc
    B.regular (fun t ht => ⟨has.le.trans ht.1, ht.2.le.trans hTb⟩)
    (hc.smooth.mono (prod_mono_right hsub)) (fun x t ht => hc.immersed x t (hsub ht))
    f hf hT j
  exact fun i _ => hv i

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
