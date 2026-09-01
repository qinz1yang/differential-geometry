import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximationDefs
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PullbackTowerBounds
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphComposition

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators ENNReal
open Bundle Manifold
open DifferentialGeometry.Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section ReflData

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem tensor02CovDeriv_metric_zero {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] [T2Space M']
    [IsManifold I 1 M'] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
    (g : SmoothRiemannianMetric I M') (a : ℕ) :
    tensor02CovDeriv (I := I) (Tensor0SBundle.metricTensorField (I := I) g) g (a + 1) = 0 := by
  rw [tensor02_eq_covDOF, covDerivOfField_eq_iterCov, iterCov_metric_zero,
    Tensor0SField.domDomCongr_zero]

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem partial_diffeomorph_metric_approximation_refl {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] [T2Space M'] [SigmaCompactSpace M']
    [IsManifold I 1 M'] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
    (K : Set M') (g : SmoothRiemannianMetric I M') (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (p : ℕ) :
    Nonempty (PartialDiffeomorphMetricApproximation (I := I) K ε p
      (PartialDiffeomorph.refl (I := I) M') g g) := by
  let _ := (inferInstance : (SigmaCompactSpace M'))
  classical
  have hcoe : ∀ x : M', (PartialDiffeomorph.refl (I := I) M' : M' → M') x = x := fun _ => rfl
  have hmfd : ∀ x : M', mfderiv I I (PartialDiffeomorph.refl (I := I) M' : M' → M') x
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := fun x => mfderiv_id
  have hsymmcoe : ∀ x : M', ((PartialDiffeomorph.refl (I := I) M').symm : M' → M') x = x :=
    fun _ => rfl
  have hsymmmfd : ∀ x : M', mfderiv I I ((PartialDiffeomorph.refl (I := I) M').symm : M' → M') x
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := fun x => mfderiv_id
  have hnz : ∀ (s : ℕ) (y : M'),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y s
        (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M') s y)) =
          0 := by
    intro s y
    have hz : Tensor0SBundle.inner0S (I := I) g y s
        (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M') s y) 0 =
          0 := by
      change (Tensor0SBundle.tensor0SMetricData (I := I) g y s).flat 0 0 = 0
      rw [(Tensor0SBundle.tensor0SMetricData (I := I) g y s).flat.map_zero]
      exact LinearMap.zero_apply _
    rw [Tensor0SBundle.normSq0S_eq_inner, hz, Real.sqrt_zero]
  have mkPre : ∀ (K' : Set M') (Φcoe : M' → M')
      (hΦ : ∀ x, Φcoe x = x) (hΦd : ∀ x, mfderiv I I Φcoe x
        = ContinuousLinearMap.id ℝ (TangentSpace I x))
      (hsm : ContMDiffOn I I (∞ : WithTop ℕ∞) Φcoe K'),
      MapMetricApproximationOn (I := I) K' ε p Φcoe g g := by
    intro K' Φcoe hΦ hΦd hsm
    refine
      { eps_pos := hε
        eps_lt_one := hε1
        smoothOn := hsm
        pullback := Tensor0SBundle.metricTensorField (I := I) g
        pullback_apply := ?_
        c0_small := ?_
        cov_deriv_small := ?_ }
    · intro x _ v
      rw [Tensor0SBundle.metricTensorField_apply, hΦ x, hΦd x]
      simp only [ContinuousLinearMap.id_apply]
    · intro x _
      change Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2
        (Tensor0SBundle.metricTensorField (I := I) g x
          - Tensor0SBundle.metricTensorField (I := I) g x)) ≤ ε
      have hs : (Tensor0SBundle.metricTensorField (I := I) g x
          - Tensor0SBundle.metricTensorField (I := I) g x)
          = (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M') 2 x) :=
        sub_self _
      rw [hs, hnz]
      exact le_of_lt hε
    · intro a ha1 _ x _
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      change Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a' + 1 + 2)
        (tensor02CovDeriv (I := I) (Tensor0SBundle.metricTensorField (I := I) g) g (a' + 1) x))
        ≤ ε
      rw [tensor02CovDeriv_metric_zero]
      change Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a' + 1 + 2)
        (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M')
          (a' + 1 + 2) x)) ≤ ε
      rw [hnz]
      exact le_of_lt hε
  refine ⟨{
    source_sub := fun x _ => Set.mem_univ x
    forward := mkPre K (PartialDiffeomorph.refl (I := I) M' : M' → M') hcoe hmfd
      (contMDiffOn_id (I := I))
    reverse := mkPre ((PartialDiffeomorph.refl (I := I) M' : M' → M') '' K)
        ((PartialDiffeomorph.refl (I := I) M').symm : M' → M') hsymmcoe hsymmmfd
      (contMDiffOn_id (I := I)) }⟩

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem reflSepData {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] [T2Space M'] [SigmaCompactSpace M']
    [IsManifold I 1 M'] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
    (K : Set M') (g : SmoothRiemannianMetric I M') (p : ℕ) :
    Nonempty (PartialDiffeomorphMetricApproximationBounds (I := I) K 0 0 p
      (PartialDiffeomorph.refl (I := I) M') g g) := by
  let _ := (inferInstance : (SigmaCompactSpace M'))
  classical
  have hcoe : ∀ x : M', (PartialDiffeomorph.refl (I := I) M' : M' → M') x = x := fun _ => rfl
  have hmfd : ∀ x : M', mfderiv I I (PartialDiffeomorph.refl (I := I) M' : M' → M') x
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := fun x => mfderiv_id
  have hsymmcoe : ∀ x : M', ((PartialDiffeomorph.refl (I := I) M').symm : M' → M') x = x :=
    fun _ => rfl
  have hsymmmfd : ∀ x : M', mfderiv I I ((PartialDiffeomorph.refl (I := I) M').symm : M' → M') x
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := fun x => mfderiv_id
  have hnz : ∀ (s : ℕ) (y : M'),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y s
        (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M') s y)) =
          0 := by
    intro s y
    have hz : Tensor0SBundle.inner0S (I := I) g y s
        (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M') s y) 0 =
          0 := by
      change (Tensor0SBundle.tensor0SMetricData (I := I) g y s).flat 0 0 = 0
      rw [(Tensor0SBundle.tensor0SMetricData (I := I) g y s).flat.map_zero]
      exact LinearMap.zero_apply _
    rw [Tensor0SBundle.normSq0S_eq_inner, hz, Real.sqrt_zero]
  have mkPre : ∀ (K' : Set M') (Φcoe : M' → M')
      (hΦ : ∀ x, Φcoe x = x) (hΦd : ∀ x, mfderiv I I Φcoe x
        = ContinuousLinearMap.id ℝ (TangentSpace I x))
      (hsm : ContMDiffOn I I (∞ : WithTop ℕ∞) Φcoe K'),
      MapMetricApproximationBoundsOn (I := I) K' 0 0 p Φcoe g g := by
    intro K' Φcoe hΦ hΦd hsm
    refine
      { c0_nonneg := le_rfl
        cov_nonneg := le_rfl
        smoothOn := hsm
        pullback := Tensor0SBundle.metricTensorField (I := I) g
        pullback_apply := ?_
        c0_small := ?_
        cov_small := ?_ }
    · intro x _ v
      rw [Tensor0SBundle.metricTensorField_apply, hΦ x, hΦd x]
      simp only [ContinuousLinearMap.id_apply]
    · intro x _
      change Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2
        (Tensor0SBundle.metricTensorField (I := I) g x
          - Tensor0SBundle.metricTensorField (I := I) g x)) ≤ 0
      have hs : (Tensor0SBundle.metricTensorField (I := I) g x
          - Tensor0SBundle.metricTensorField (I := I) g x)
          = (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M') 2 x) :=
        sub_self _
      rw [hs, hnz]
    · intro a ha1 _ x _
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      change Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a' + 1 + 2)
        (tensor02CovDeriv (I := I) (Tensor0SBundle.metricTensorField (I := I) g) g (a' + 1) x))
        ≤ 0
      rw [tensor02CovDeriv_metric_zero]
      change Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a' + 1 + 2)
        (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M')
          (a' + 1 + 2) x)) ≤ 0
      rw [hnz]
  refine ⟨{
    source_sub := fun x _ => Set.mem_univ x
    forward := mkPre K (PartialDiffeomorph.refl (I := I) M' : M' → M') hcoe hmfd
      (contMDiffOn_id (I := I))
    reverse := mkPre ((PartialDiffeomorph.refl (I := I) M' : M' → M') '' K)
      ((PartialDiffeomorph.refl (I := I) M').symm : M' → M') hsymmcoe hsymmmfd
      (contMDiffOn_id (I := I)) }⟩

end ReflData

end HCGCompactness
end DifferentialGeometry
