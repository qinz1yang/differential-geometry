import DifferentialGeometry.Geometry.Curvature.Metric.Sectional
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ContractionLeibniz
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNorm

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open Connection Tensor0SBundle CheegerGromovCompactness

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem covStep_metricRm04_eq_zero_of_constant_sectional
    (g : SmoothRiemannianMetric I M) (κ : ℝ)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      metricRm04StandardAt g x v w w v =
        κ * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w)) :
    covStep g 4 (metricRm04 g) = 0 := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  let _ : IsManifold I 3 M := IsManifold.of_le (n := ∞) (by simp)
  let G := metricTensorField g
  let P := tensor0SFieldProduct ∞ G G
  let e₁ : Fin 4 ≃ Fin 4 := (Equiv.swap 1 3).trans (Equiv.swap 1 2)
  let e₂ : Fin 4 ≃ Fin 4 := Equiv.swap 1 2
  have hRm : metricRm04 g = κ •
      (Tensor0SField.domDomCongr ∞ e₁ P - Tensor0SField.domDomCongr ∞ e₂ P) := by
    refine DFunLike.ext _ _ fun x => ?_
    refine tensor0SSpace_ext (I := I) 4 x fun v => ?_
    change metricRm04At g x v =
      κ * ((Tensor0SField.domDomCongr ∞ e₁ P x) v -
        (Tensor0SField.domDomCongr ∞ e₂ P x) v)
    rw [Tensor0SField.domDomCongr_apply, Tensor0SField.domDomCongr_apply,
      Tensor0SSpace.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
    dsimp only [P]
    rw [tensor0SField_product_apply, tensor0SField_product_apply]
    dsimp only [G]
    rw [metricTensorField_apply, metricTensorField_apply,
      metricTensorField_apply, metricTensorField_apply]
    change metricRm04At g x v = κ *
      (g.inner x (v 0) (v 3) * g.inner x (v 1) (v 2) -
        g.inner x (v 0) (v 2) * g.inner x (v 1) (v 3))
    have hv : vec4 (v 0) (v 1) (v 2) (v 3) = v := by
      funext i
      fin_cases i <;> rfl
    have h := metricRm_of_sec g x κ (hsec x) (v 0) (v 1) (v 2) (v 3)
    rw [metricRm04StandardAt_apply, hv] at h
    rw [h]
    ring
  have hG : TotalNabla0SRealizes 2 (leviCivitaConnectionOfMetric g) G 0 := by
    intro X x slots
    rw [nabla_metric_zero _ g (leviCivitaConnectionOfMetric_isMetricCompatible g) X x]
    simp
  have hP : TotalNabla0SRealizes 4 (leviCivitaConnectionOfMetric g) P 0 :=
    nabla_product_zero_of_zero (leviCivitaConnectionOfMetric g) G G hG hG
  have hperm (e : Fin 4 ≃ Fin 4) :
      covStep g 4 (Tensor0SField.domDomCongr ∞ e P) = 0 := by
    apply Tensor0SBundle.totalNabla0SRealizes_unique
      (totalNabla0S_realizes 4 (leviCivitaConnectionOfMetric g) _
        (totalNabla0S_regularity 4 (leviCivitaConnectionOfMetric g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally g) _))
    simpa only [Tensor0SField.domDomCongr_zero] using
      totalNabla0SRealizes_domDomCongr (leviCivitaConnectionOfMetric g) e P 0 hP
  rw [hRm, covStep_smul, covStep_sub, hperm e₁, hperm e₂, sub_self, smul_zero]

private theorem metricCovariantDerivative_rm04_eq_zero_of_constant_sectional
    (g : SmoothRiemannianMetric I M) (κ : ℝ)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      metricRm04StandardAt g x v w w v =
        κ * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w)) :
    metricCovariantDerivative g 4 (metricRm04At g) = 0 := by
  have hRm : metricRm04At g = fun x => metricRm04 g x := by
    funext x
    exact (metricRm04_apply g x).symm
  rw [hRm]
  funext x
  change covStep g 4 (metricRm04 g) x = 0
  rw [covStep_metricRm04_eq_zero_of_constant_sectional g κ hsec]
  rfl

theorem iteratedMetricCovariantDerivative_rm04_eq_zero_of_constant_sectional
    (g : SmoothRiemannianMetric I M) (κ : ℝ)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      metricRm04StandardAt g x v w w v =
        κ * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (k : ℕ) (hk : 0 < k) :
    iteratedMetricCovariantDerivative g 4 (metricRm04At g) k = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  clear hk
  induction j with
  | zero => exact metricCovariantDerivative_rm04_eq_zero_of_constant_sectional g κ hsec
  | succ j ih =>
      change metricCovariantDerivative g (4 + (j + 1))
        (iteratedMetricCovariantDerivative g 4 (metricRm04At g) (j + 1)) = 0
      rw [ih]
      funext x
      change covStep g (4 + (j + 1))
        (0 : Tensor0SField (I := I) (M := M) (n := ∞) (4 + (j + 1))) x = 0
      rw [covStep_zero]
      rfl

theorem curvatureDerivativeNorm_eq_zero_of_constant_sectional
    (g : SmoothRiemannianMetric I M) (κ : ℝ)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      metricRm04StandardAt g x v w w v =
        κ * (g.inner x v v * g.inner x w w - g.inner x v w * g.inner x v w))
    (k : ℕ) (hk : 0 < k) (x : M) : curvatureDerivativeNorm g k x = 0 := by
  unfold curvatureDerivativeNorm
  rw [iteratedMetricCovariantDerivative_rm04_eq_zero_of_constant_sectional g κ hsec k hk]
  change Real.sqrt (normSq0S g x (4 + k) 0) = 0
  rw [(normSq0S_eq_zero_iff g x (4 + k) 0).mpr rfl, Real.sqrt_zero]

end DifferentialGeometry.Geometry.Curvature
