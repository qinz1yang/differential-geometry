import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BusemannPerturbation
import DifferentialGeometry.Geometry.Connection.Hessian.Scalar
import DifferentialGeometry.Analysis.Calculus.LocalExtrema
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Algebra.Field.Periodic

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Hyperboloid

private theorem abs_sub_le_third_of_deriv_zero_of_second_deriv_bound
    {f : ℝ → ℝ} (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f t)
    (hzero : deriv f 0 = 0)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv f) t| ≤ 2 / 3) :
    |f 1 - f 0| ≤ 1 / 3 := by
  have hon : ContDiffOn ℝ (1 + 1 : ℕ) f (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact fun t ht => (hf t ht).contDiffWithinAt
  obtain ⟨t, ht, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1)
    (show (0 : ℝ) ≠ 1 by norm_num) hon
  have hd0 := (hf 0 (by simp)).differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0) |>.hasDerivAt
  rw [hzero] at hd0
  have hwithin : derivWithin f (Set.Icc (0 : ℝ) 1) 0 = 0 := by
    apply hd0.hasDerivWithinAt.derivWithin
    exact (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) 0 (by simp)
  have hTaylor : taylorWithinEval f 1 (Set.uIcc (0 : ℝ) 1) 0 1 = f 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ]
    simp [iteratedDerivWithin_one, hwithin]
  rw [hTaylor] at heq
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    have hto : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [Set.uIoo_of_lt (by norm_num : (0 : ℝ) < 1)] using ht
    exact ⟨hto.1.le, hto.2.le⟩
  have hb := hbound t ht'
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat, one_mul, mul_one, sub_zero, one_pow] at heq
  rw [iteratedDeriv_succ, iteratedDeriv_one] at heq
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith only [hb]

section CurveCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem deriv_comp_eq_mvfderiv_velocity
    {f : M → ℝ} {γ : ℝ → M} {t : ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f (γ t))
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t) :
    deriv (f ∘ γ) t = mvfderiv I f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
  have hfm := hf.mdifferentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hγm := hγ.mdifferentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hd : deriv (f ∘ γ) t = mvfderiv 𝓘(ℝ, ℝ) (f ∘ γ) t (1 : TangentSpace 𝓘(ℝ, ℝ) t) := by
    rw [mvfderiv_eq_fderiv]
    exact (fderiv_apply_one_eq_deriv (f := f ∘ γ)).symm
  rw [hd]
  exact mvfderiv_comp_apply t hfm hγm _

private theorem deriv_deriv_comp_eq_hessFun
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {γ : ℝ → M} {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hgeo : Geometry.Riemannian.Geodesic.HasGeodesicEquationAt g γ t) :
    deriv (deriv (f ∘ γ)) t = Geometry.Operator.hessFun g f (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
  rw [Geometry.Connection.hessFun_eq_abstract _ hf]
  have h := Geometry.Connection.abstractHessian_apply_velocity_of_hasGeodesicEquationAt
    g (hf.contMDiffAt.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) hγ
    (BoundarylessManifold.isInteriorPoint (I := I)) hgeo
  have h1 : (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1 =
      (1 : TangentSpace 𝓘(ℝ, ℝ) t) := by
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, h1] using h.symm

end CurveCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem abs_two_mul_log_time_sub_inner_sub_le_of_isGeodesicOn
    (U : TopologicalSpace.Opens (Hyperboloid E))
    (h : SmoothRiemannianMetric 𝓘(ℝ, E) U) (ξ : Metric.sphere (0 : E) 1)
    {K : Set U} {p : ℕ} (hp : 1 ≤ p)
    (hsmall : CheegerGromovCompactness.metricCkENormOn K p h
      ((scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U)
      ((scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U) ≤ ENNReal.ofReal (1 / 100))
    (γ : ℝ → U)
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 γ t)
    (hgeo : Geometry.Riemannian.Geodesic.IsGeodesicOn h γ (Set.Icc (0 : ℝ) 1))
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ K)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      h.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1) = 1)
    (hzero : mvfderiv 𝓘(ℝ, E)
      (fun y : U => 2 * Real.log (y.val.time - inner ℝ (ξ : E) y.val.space)) (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0 1) = 0) :
    |2 * Real.log ((γ 1).val.time - inner ℝ (ξ : E) (γ 1).val.space) -
      2 * Real.log ((γ 0).val.time - inner ℝ (ξ : E) (γ 0).val.space)| ≤ 1 / 3 := by
  let ρ := fun y : U => 2 * Real.log (y.val.time - inner ℝ (ξ : E) y.val.space)
  have hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ :=
    (contMDiff_const.mul (contMDiff_log_time_sub_inner ξ)).comp contMDiff_subtype_val
  have hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 (ρ ∘ γ) t := by
    intro t ht
    exact (hρ.contMDiffAt.of_le (by simp : (2 : ℕ∞ω) ≤ ∞) |>.comp t (hγ t ht)).contDiffAt
  have hd0 : deriv (ρ ∘ γ) 0 = 0 := by
    rw [deriv_comp_eq_mvfderiv_velocity
      (hρ.contMDiffAt.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) (hγ 0 (by simp))]
    exact hzero
  apply abs_sub_le_third_of_deriv_zero_of_second_deriv_bound hf hd0
  intro t ht
  rw [deriv_deriv_comp_eq_hessFun h hρ (hγ t ht) (hgeo t ht)]
  exact abs_hessFun_two_mul_log_time_sub_inner_le_of_metricCkENormOn
    U h ξ hp hsmall (hmem t ht) _ (hunit t ht)

theorem not_periodic_two_mul_log_time_sub_inner_of_isGeodesicOn
    (U : TopologicalSpace.Opens (Hyperboloid E))
    (h : SmoothRiemannianMetric 𝓘(ℝ, E) U) (ξ : Metric.sphere (0 : E) 1)
    {K : Set U} {p : ℕ} (hp : 1 ≤ p)
    (hsmall : CheegerGromovCompactness.metricCkENormOn K p h
      ((scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U)
      ((scaleMetric 4 (by norm_num) riemannianMetric).restrictOpen U) ≤ ENNReal.ofReal (1 / 100))
    (γ : ℝ → U) {T : ℝ} (hT : 0 < T)
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) T, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 γ t)
    (hgeo : Geometry.Riemannian.Geodesic.IsGeodesicOn h γ (Set.Icc (0 : ℝ) T))
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) T, γ t ∈ K)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) T,
      h.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1) = 1) :
    ¬Function.Periodic
      (fun t => 2 * Real.log ((γ t).val.time - inner ℝ (ξ : E) (γ t).val.space)) T := by
  let ρ := fun y : U => 2 * Real.log (y.val.time - inner ℝ (ξ : E) y.val.space)
  have hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ :=
    (contMDiff_const.mul (contMDiff_log_time_sub_inner ξ)).comp contMDiff_subtype_val
  have hf : ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiffAt ℝ 2 (ρ ∘ γ) t := by
    intro t ht
    exact (hρ.contMDiffAt.of_le (by simp : (2 : ℕ∞ω) ≤ ∞) |>.comp t (hγ t ht)).contDiffAt
  intro hperiodic
  change Function.Periodic (ρ ∘ γ) T at hperiodic
  have hcont : ContinuousOn (ρ ∘ γ) (Set.Icc (0 : ℝ) T) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (0 : ℝ) T).Nonempty from ⟨0, by simp [hT.le]⟩) hcont
  have hglobal : IsLocalMax (ρ ∘ γ) t := Filter.Eventually.of_forall fun s => by
    obtain ⟨r, hr, heq⟩ := hperiodic.exists_mem_Ico₀ hT s
    rw [heq]
    exact hmax ⟨hr.1, hr.2.le⟩
  have hzero : mvfderiv 𝓘(ℝ, E) ρ (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1) = 0 := by
    rw [← deriv_comp_eq_mvfderiv_velocity
      (hρ.contMDiffAt.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)) (hγ t ht)]
    exact hglobal.deriv_eq_zero
  have hnonpos := hglobal.deriv_deriv_nonpos (hf t ht).continuousAt
  rw [deriv_deriv_comp_eq_hessFun h hρ (hγ t ht) (hgeo t ht)] at hnonpos
  have hpos := hessFun_two_mul_log_time_sub_inner_lower_bound_of_metricCkENormOn
    U h ξ hp hsmall (hmem t ht) _ (hunit t ht) hzero
  linarith only [hnonpos, hpos]

end DifferentialGeometry.Hyperboloid
