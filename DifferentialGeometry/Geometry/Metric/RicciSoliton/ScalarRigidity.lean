import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Strong
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureNullity

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedGradientRicciSoliton_scalar_eq_zero_everywhere_of_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : metricScalarAt (I := I) g x = 0) :
    ∀ y : M, metricScalarAt (I := I) g y = 0 := by
  let R : C^∞⟮I, M; Real⟯ :=
    ⟨(fun z : M => metricScalarAt (I := I) g z),
      metricScalar_smooth (I := I) (M := M) g⟩
  let X : Real → (z : M) → TangentSpace I z := fun _ z =>
    -gradientFun (I := I) g f z
  let u : Real → M → Real := fun t z => Real.exp t * R z
  have hX : ∀ K : Set M, IsCompact K →
      ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ Set.Icc 0 1, ∀ z ∈ K,
        g.inner z (X t z) (X t z) ≤ C := by
    intro K hK
    let q : M → Real := fun z => g.inner z
      (gradientFun (I := I) g f z) (gradientFun (I := I) g f z)
    have hq : Continuous q := by
      apply continuous_iff_continuousAt.mpr
      intro z
      have hgrad : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
          (T% fun y : M => gradientFun (I := I) g f y) z :=
        (gradientFun_smooth (I := I) g f.contMDiff).contMDiffAt
      exact (CovariantDerivative.metric_inner_contMDiffAt
        (I := I) g hgrad hgrad le_rfl).continuousAt
    obtain ⟨C, hC⟩ := hK.bddAbove_image hq.continuousOn
    refine ⟨max C 0, le_max_right C 0, ?_⟩
    intro t ht z hz
    calc
      g.inner z (X t z) (X t z) = q z := by simp [X, q]
      _ ≤ C := hC ⟨z, hz, rfl⟩
      _ ≤ max C 0 := le_max_left C 0
  have hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) 1) := by
    apply Continuous.continuousOn
    dsimp only [u, R]
    fun_prop
  have hu_nonneg : ∀ t ∈ Set.Icc 0 1, ∀ z : M, 0 ≤ u t z := by
    intro t ht z
    exact mul_nonneg (Real.exp_pos _).le
      (normalizedGradientRicciSoliton_scalar_nonneg (I := I) h z)
  have hu_time : ∀ t ∈ Set.Icc 0 1, 0 < t → ∀ z : M,
      DifferentiableWithinAt Real (fun s => u s z) (Set.Icc 0 1) t := by
    intro t ht htpos z
    dsimp only [u]
    exact ((Real.hasDerivAt_exp t).mul_const
      (R z)).differentiableAt.differentiableWithinAt
  have hu_space : ∀ t ∈ Set.Icc 0 1, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t) := by
    intro t ht htpos
    dsimp only [u]
    exact contMDiff_const.mul R.contMDiff
  have hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 1) (htpos : 0 < t)
      (z : M),
      0 ≤ derivWithin (fun s => u s z) (Set.Icc 0 1) t -
        (ΔG (I := I) g ⟨u t, hu_space t ht htpos⟩ z +
          g.inner z (X t z) (gradientFun (I := I) g (u t) z)) := by
    intro t ht htpos z
    have hderiv : derivWithin (fun s => u s z) (Set.Icc 0 1) t =
        Real.exp t * R z := by
      exact ((Real.hasDerivAt_exp t).mul_const (R z)).hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Icc (by norm_num : (0 : Real) < 1)).uniqueDiffWithinAt ht)
    have hlap : ΔG (I := I) g ⟨u t, hu_space t ht htpos⟩ z =
        Real.exp t * ΔG (I := I) g R z := by
      have hfun : u t = Real.exp t • (R : M → Real) := by
        funext y
        simp [u, smul_eq_mul]
      calc
        ΔG (I := I) g ⟨u t, hu_space t ht htpos⟩ z =
            laplacian (I := I) (LeviCivita (I := I) g) g (u t) z :=
          (laplacian_levi_eq (I := I) g (hu_space t ht htpos) z).symm
        _ = Real.exp t * laplacian (I := I) (LeviCivita (I := I) g) g R z := by
          rw [hfun]
          exact laplacian_const_smul (I := I) (LeviCivita (I := I) g) g
            (Real.exp t) (fun y => R.contMDiff.mdifferentiable (by simp) y)
            ((gradG (I := I) g R).mdifferentiable z)
        _ = Real.exp t * ΔG (I := I) g R z := by
          rw [laplacian_levi_eq (I := I) g R.contMDiff z]
          congr 1
    have hgrad : gradientFun (I := I) g (u t) z =
        Real.exp t • gradientFun (I := I) g R z := by
      have hfun : u t = Real.exp t • (R : M → Real) := by
        funext y
        simp [u, smul_eq_mul]
      rw [hfun]
      exact gradientFun_const_smul (I := I) g (Real.exp t)
        (R.contMDiff.mdifferentiable (by simp) z)
    have hweighted := gradientRicciSoliton_weightedLaplacian_scalar h.2.1 z
    have hnorm := Tensor0SBundle.normSq0S_nonneg (I := I) g z 2
      (metricRicciAt (I := I) (M := M) g z)
    rw [hderiv, hlap, hgrad]
    change 0 ≤ Real.exp t * R z -
      (Real.exp t * ΔG (I := I) g R z +
        g.inner z (-gradientFun (I := I) g f z)
          (Real.exp t • gradientFun (I := I) g R z))
    rw [one_mul] at hweighted
    change weightedLaplacian (I := I) g f R z =
      R z - 2 * Tensor0SBundle.normSq0S (I := I) g z 2
        (metricRicciAt (I := I) (M := M) g z) at hweighted
    change ΔG (I := I) g R z -
      g.inner z (gradientFun (I := I) g f z)
        (gradientFun (I := I) g R z) =
      R z - 2 * Tensor0SBundle.normSq0S (I := I) g z 2
        (metricRicciAt (I := I) (M := M) g z) at hweighted
    have hinner : g.inner z (-gradientFun (I := I) g f z)
        (Real.exp t • gradientFun (I := I) g R z) =
        -(Real.exp t * g.inner z (gradientFun (I := I) g f z)
          (gradientFun (I := I) g R z)) := by
      simp
    rw [hinner]
    have heq : Real.exp t * R z -
        (Real.exp t * ΔG (I := I) g R z +
          -(Real.exp t * g.inner z (gradientFun (I := I) g f z)
            (gradientFun (I := I) g R z))) =
        2 * Real.exp t * Tensor0SBundle.normSq0S (I := I) g z 2
          (metricRicciAt (I := I) (M := M) g z) := by
      calc
        _ = Real.exp t * (R z -
            (ΔG (I := I) g R z -
              g.inner z (gradientFun (I := I) g f z)
                (gradientFun (I := I) g R z))) := by ring
        _ = _ := by rw [hweighted]; ring
    rw [heq]
    positivity
  intro y
  apply le_antisymm (le_of_not_gt ?_)
    (normalizedGradientRicciSoliton_scalar_nonneg (I := I) h y)
  intro hy
  have hpos :=
    scalar_strong_maximum_principle_fixed_metric_with_locally_bounded_drift_spatial
      (I := I) g (by norm_num : (0 : Real) < 1) X hX u hu_cont hu_nonneg
        hu_time hu_space hu_super (c := y) (mul_pos (Real.exp_pos 1) hy) x
  simp [u, R, hx] at hpos

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem normalizedGradientRicciSoliton_metricRicciAt_eq_zero_of_scalar_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : metricScalarAt (I := I) g x = 0) (y : M) :
    metricRicciAt (I := I) (M := M) g y = 0 := by
  let R : C^∞⟮I, M; Real⟯ :=
    ⟨(fun z : M => metricScalarAt (I := I) g z),
      metricScalar_smooth (I := I) (M := M) g⟩
  have hR :=
    normalizedGradientRicciSoliton_scalar_eq_zero_everywhere_of_eq_zero
      (I := I) h hx
  have hRzero : R = 0 := by
    apply ContMDiffMap.ext
    intro z
    exact hR z
  have hweighted := gradientRicciSoliton_weightedLaplacian_scalar h.2.1 y
  have hweighted' : weightedLaplacian (I := I) g f R y =
      1 * metricScalarAt (I := I) g y -
        2 * Tensor0SBundle.normSq0S (I := I) g y 2
          (metricRicciAt (I := I) (M := M) g y) := by
    simpa only [R] using hweighted
  have hweightedZero : weightedLaplacian (I := I) g f
      (0 : C^∞⟮I, M; Real⟯) y = 0 := by
    have hlap : ΔG (I := I) g (0 : C^∞⟮I, M; Real⟯) y = 0 := by
      have hzero : (0 : C^∞⟮I, M; Real⟯) =
          ContMDiffMap.const (I := I) (I' := 𝓘(ℝ, ℝ)) (M := M) 0 := by
        apply ContMDiffMap.ext
        intro z
        rfl
      rw [hzero]
      exact Δ_g_const (I := I) g 0 y
    have hgrad : gradFun (I := I) g (0 : C^∞⟮I, M; Real⟯) y = 0 := by
      change gradFun (I := I) g (fun _ : M => (0 : Real)) y = 0
      exact gradFun_zero (I := I) g y
    rw [weightedLaplacian_apply, hlap, hgrad]
    simp
  rw [hR y, hRzero, hweightedZero] at hweighted'
  have hnorm : Tensor0SBundle.normSq0S (I := I) g y 2
      (metricRicciAt (I := I) (M := M) g y) = 0 := by
    linarith
  exact (Tensor0SBundle.normSq0S_eq_zero_iff (I := I) g y 2 _).mp hnorm

theorem normalizedGradientRicciSoliton_ricciTensor_eq_zero_of_scalar_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : metricScalarAt (I := I) g x = 0)
    (y : M) (v w : TangentSpace I y) :
    ricciTensor (I := I) g y v w = 0 := by
  rw [← metricRicciAt_apply_eq_ricciTensor]
  rw [normalizedGradientRicciSoliton_metricRicciAt_eq_zero_of_scalar_eq_zero
    (I := I) h hx y]
  rfl

theorem normalizedGradientRicciSoliton_hessFun_eq_half_metric_of_scalar_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : metricScalarAt (I := I) g x = 0)
    (y : M) (v w : TangentSpace I y) :
    hessFun (I := I) g f y v w = (1 / 2 : Real) * g.inner y v w := by
  have hsol := h.2.1 y v w
  rw [normalizedGradientRicciSoliton_ricciTensor_eq_zero_of_scalar_eq_zero
    (I := I) h hx y v w] at hsol
  norm_num at hsol ⊢
  exact hsol

theorem normalizedGradientRicciSoliton_cov_gradFun_eq_half_smul_of_scalar_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : metricScalarAt (I := I) g x = 0)
    (y : M) (v : TangentSpace I y) :
    (LeviCivita (I := I) g).toFun
        (fun z => gradFun (I := I) g f z) y v =
      (1 / 2 : Real) • v := by
  apply metricFlatLinear_injective (I := I) g y
  ext w
  change g.inner y
      ((LeviCivita (I := I) g).toFun
        (fun z => gradFun (I := I) g f z) y v) w =
    g.inner y ((1 / 2 : Real) • v) w
  rw [← hessFun_eq_cov_grad (I := I) g f.contMDiff y v w]
  rw [normalizedGradientRicciSoliton_hessFun_eq_half_metric_of_scalar_eq_zero
    (I := I) h hx y v w]
  simp

theorem normalizedGradientRicciSoliton_riemannOp_gradFun_eq_zero_of_scalar_eq_zero
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x : M} (hx : metricScalarAt (I := I) g x = 0)
    (y : M) (v w : TangentSpace I y) :
    riemannOp (LeviCivita (I := I) g) y v w
      (gradFun (I := I) g f y) = 0 := by
  exact riemannOp_apply_eq_zero_of_covApply_eq_smul
    (cov := LeviCivita (I := I) g)
    (LeviCivita_torsion_eq_zero (I := I) g)
    (gradientFun_smooth (I := I) g f.contMDiff)
    (c := 1 / 2)
    (fun z u =>
      normalizedGradientRicciSoliton_cov_gradFun_eq_half_smul_of_scalar_eq_zero
        (I := I) h hx z u)
    y v w

end DifferentialGeometry.Geometry
