import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CurvatureDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.IteratedDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution

open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_iteratedDs_unitTangent_bounds_of_curvature_bounds
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M) {J : Set ℝ}
    (hi : c.ImmersedOn (I := I) J)
    (hbound : ∀ m, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (c.normSq g (c.iteratedDs g m (c.curvatureVector g)) x t) ≤ C) :
    ∀ m, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (c.normSq g (c.iteratedDs g m (c.unitTangent g)) x t) ≤ C := by
  intro m
  cases m with
  | zero =>
    refine ⟨1, fun x t ht => ?_⟩
    simp only [iteratedDs, Function.iterate_zero, id_eq, normSq,
      c.unitTangent_inner_self g hi x t ht, Real.sqrt_one, le_refl]
  | succ m =>
    obtain ⟨C, hC⟩ := hbound m
    refine ⟨C, fun x t ht => ?_⟩
    rw [c.iteratedDs_unitTangent_succ g m]
    exact hC x t ht

variable [T2Space M] [I.Boundaryless]

theorem exists_iterated_ds_inner_bounds
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (V W : c.Field (I := I))
    (hV : ∀ t ∈ J, ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => (⟨c.lift x t, V x t⟩ : TangentBundle I M)))
    (hW : ∀ t ∈ J, ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => (⟨c.lift x t, W x t⟩ : TangentBundle I M)))
    (hVB : ∀ m, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (c.normSq g (c.iteratedDs g m V) x t) ≤ C)
    (hWB : ∀ m, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (c.normSq g (c.iteratedDs g m W) x t) ≤ C) :
    ∀ m, ∃ C : ℝ, ∀ x t, t ∈ J →
      |(c.ds g)^[m] (fun y τ => (g τ).inner (c.lift y τ) (V y τ) (W y τ)) x t| ≤ C := by
  classical
  choose A hA using hVB
  choose B hB using hWB
  intro m
  refine ⟨∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A i * B (m - i), ?_⟩
  intro x t ht
  rw [c.iterated_ds_inner g hc hi V W t ht (hV t ht) (hW t ht) m x]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi'
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hinner := abs_inner_le_sqrt_mul_sqrt (g t) (c.lift x t)
    (c.iteratedDs g i V x t) (c.iteratedDs g (m - i) W x t)
  have hprod : Real.sqrt (c.normSq g (c.iteratedDs g i V) x t) *
      Real.sqrt (c.normSq g (c.iteratedDs g (m - i) W) x t) ≤ A i * B (m - i) :=
    mul_le_mul (hA i x t ht) (hB (m - i) x t ht) (Real.sqrt_nonneg _)
      ((Real.sqrt_nonneg _).trans (hA i x t ht))
  exact (mul_le_mul_of_nonneg_left (hinner.trans hprod) (Nat.cast_nonneg _)).trans_eq
    (mul_assoc _ _ _).symm


theorem exists_iterated_ds_curvatureSq_bounds
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (hbound : ∀ m, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (c.normSq g (c.iteratedDs g m (c.curvatureVector g)) x t) ≤ C) :
    ∀ m, ∃ C : ℝ, ∀ x t, t ∈ J → |(c.ds g)^[m] (c.curvatureSq g) x t| ≤ C := by
  exact c.exists_iterated_ds_inner_bounds g hc hi (c.curvatureVector g) (c.curvatureVector g)
    (fun t ht => c.curvatureVector_contMDiff g J hc hi t ht)
    (fun t ht => c.curvatureVector_contMDiff g J hc hi t ht) hbound hbound

variable [CompactSpace M] {D : RealTimeInterval} {a b : ℝ}

theorem exists_iteratedDs_unitTangent_bounds_on_Ico_of_curvature_le
    (B : RicciBackground (I := I) (M := M) D a b) {T : ℝ}
    (haT : a < T) (hTb : T ≤ b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Ico a T)) {K : ℝ}
    (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K)
    (s : ℝ) (has : a < s) :
    ∀ m, ∃ C : ℝ, ∀ x t, t ∈ Ico s T →
      Real.sqrt (c.normSq B.family.metric
        (c.iteratedDs B.family.metric m (c.unitTangent B.family.metric)) x t) ≤ C := by
  obtain ⟨A, hA, hbound⟩ := c.exists_iteratedDs_curvature_bounds_on_Ico_of_curvature_le
    B haT hTb hc hcurv s has
  have hsub : Ico s T ⊆ Ico a T := fun t ht => ⟨has.le.trans ht.1, ht.2⟩
  exact c.exists_iteratedDs_unitTangent_bounds_of_curvature_bounds B.family.metric
    (fun x t ht => hc.immersed x t (hsub ht)) (fun m =>
      ⟨Real.sqrt (A m), fun x t ht => Real.sqrt_le_sqrt (hbound m x t ht)⟩)

theorem exists_iterated_ds_curvatureSq_bounds_on_Ico_of_curvature_le
    (B : RicciBackground (I := I) (M := M) D a b) {T : ℝ}
    (haT : a < T) (hTb : T ≤ b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Ico a T)) {K : ℝ}
    (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K)
    (s : ℝ) (has : a < s) :
    ∀ m, ∃ C : ℝ, ∀ x t, t ∈ Ico s T →
      |(c.ds B.family.metric)^[m] (c.curvatureSq B.family.metric) x t| ≤ C := by
  obtain ⟨A, hA, hbound⟩ := c.exists_iteratedDs_curvature_bounds_on_Ico_of_curvature_le
    B haT hTb hc hcurv s has
  have hsub : Ico s T ⊆ Ico a T := fun t ht => ⟨has.le.trans ht.1, ht.2⟩
  exact c.exists_iterated_ds_curvatureSq_bounds B.family.metric
    (hc.smooth.mono (prod_mono_right hsub))
    (fun x t ht => hc.immersed x t (hsub ht)) (fun m =>
      ⟨Real.sqrt (A m), fun x t ht => Real.sqrt_le_sqrt (hbound m x t ht)⟩)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
