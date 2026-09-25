import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.Local

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem time_weighted_curvature_derivative_bound_of_complete
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b C : ℝ}
    (hcarrier : Set.Icc a b ⊆ D.carrier)
    (hregular : Set.Ioc a b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a))
    (hC : 0 ≤ C)
    (hcurv : ∀ t ∈ Set.Icc a b, ∀ x : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (k : ℕ) :
    ∀ t ∈ Set.Ioc a b, ∀ x : M,
      (t - a) ^ k * nablaKRm04NormSqIntrinsic (I := I) S k t x ≤
      (2 : ℝ) ^ k *
        (towerConst (max 0 (∑ j ∈ Finset.range (k + 2), rmTowerCost (Module.finrank ℝ E) j))
          (max 1 C * (b - a)) k) ^ 2 * (max 1 C) ^ 2 := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hEmpty =>
      let _ : IsEmpty M := hEmpty
      exact fun _ _ x => isEmptyElim x
  | inr hNonempty =>
      let F : PointedFlowData (I := I) D := {
        M := M
        topology := inferInstance
        charted := inferInstance
        smooth := inferInstance
        sigmaCompact := inferInstance
        t2 := inferInstance
        t2TangentBundle := by infer_instance
        basepoint := Classical.choice hNonempty
        S := S
        isSolution := hS
      }
      let K : ℝ := max 1 C
      let c : ℝ := max 0 (∑ j ∈ Finset.range (k + 2), rmTowerCost (Module.finrank ℝ E) j)
      let P : ℝ := (towerConst c (K * (b - a)) k) ^ 2 * K ^ 2
      intro t ht x
      have hbound := movingRm_of_bound (I := I) F ht.1 ht.2
        hcarrier hregular hcomplete.complete hC hcurv k k le_rfl t ⟨le_rfl, ht.2⟩ x
      have hraw : nablaKRm04NormSqIntrinsic (I := I) S k t x ≤
          P / ((t - a) / 2) ^ k := by
        simpa only [F, rmOpenBound, P, c, K] using hbound
      have hmul := (le_div_iff₀ (pow_pos (half_pos (sub_pos.mpr ht.1)) k)).mp hraw
      have hpow : (t - a) ^ k = (2 : ℝ) ^ k * ((t - a) / 2) ^ k := by
        rw [← mul_pow]
        congr 1
        ring
      change (t - a) ^ k * nablaKRm04NormSqIntrinsic S k t x ≤
        (2 : ℝ) ^ k * (towerConst c (K * (b - a)) k) ^ 2 * K ^ 2
      calc
        (t - a) ^ k * nablaKRm04NormSqIntrinsic (I := I) S k t x =
            (2 : ℝ) ^ k *
              (nablaKRm04NormSqIntrinsic (I := I) S k t x * ((t - a) / 2) ^ k) := by
                rw [hpow]
                ring
        _ ≤ (2 : ℝ) ^ k * P := mul_le_mul_of_nonneg_left hmul (by positivity)
        _ = _ := by dsimp only [P]; ring

theorem exists_time_weighted_curvature_derivative_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b C : ℝ}
    (hcarrier : Set.Icc a b ⊆ D.carrier)
    (hregular : Set.Ioc a b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a))
    (hC : 0 ≤ C)
    (hcurv : ∀ t ∈ Set.Icc a b, ∀ x : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C)
    (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Set.Ioc a b, ∀ x : M,
      (t - a) ^ k * nablaKRm04NormSqIntrinsic (I := I) S k t x ≤ A := by
  refine ⟨(2 : ℝ) ^ k *
        (towerConst (max 0 (∑ j ∈ Finset.range (k + 2), rmTowerCost (Module.finrank ℝ E) j))
          (max 1 C * (b - a)) k) ^ 2 * (max 1 C) ^ 2, by positivity, ?_⟩
  exact time_weighted_curvature_derivative_bound_of_complete S hS hcarrier hregular
    hcomplete hC hcurv k

end DifferentialGeometry.PDE.RicciFlow
