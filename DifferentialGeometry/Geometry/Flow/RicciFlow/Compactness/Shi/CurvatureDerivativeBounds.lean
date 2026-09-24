import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

theorem sqrt_normSq0S_ricCovTower_le_curvDerivNorm
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    Real.sqrt (normSq0S g x (2 + m) (ricCovTower g g m x)) ≤
      Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + m) + 2)) * curvDerivNorm m g x := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 0 le_rfl) :=
    { base.metric := fun _ => g }
  have hsq : normSq0S g x (2 + m) (ricCovTower g g m x) ≤
      (Module.finrank ℝ E : ℝ) ^ ((2 + m) + 2) * curvDerivNormSq m g x := by
    rw [show curvDerivNormSq m g x = nablaKRm04NormSqIntrinsic S m 0 x from
      curvNormSq_eq S m 0 x]
    exact ricTower_normSq_le S 0 m x
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (by positivity)] at hsqrt
  exact hsqrt

theorem movingShiBoundOn_of_curvDerivNorm_on_closed_interval
    (X : PointedFlowSeq (I := I)) {a b : ℝ} (N : ℕ) (C : ℕ → ℝ)
    (hcurv : ∀ k m : ℕ, m ≤ N → ∀ t ∈ Icc a b,
      letI : TopologicalSpace (X.term k).M := (X.term k).topology
      letI : ChartedSpace H (X.term k).M := (X.term k).charted
      letI : T2Space (X.term k).M := (X.term k).t2
      letI : IsManifold I ∞ (X.term k).M := (X.term k).smooth
      ∀ x : (X.term k).M, curvDerivNorm m ((X.term k).S.base.metric t) x ≤ C m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ,
      letI : TopologicalSpace (X.term k).M := (X.term k).topology
      letI : ChartedSpace H (X.term k).M := (X.term k).charted
      letI : T2Space (X.term k).M := (X.term k).t2
      letI : IsManifold I ∞ (X.term k).M := (X.term k).smooth
      MovingShiBoundOn univ a b (fun _ t => (X.term k).S.base.metric t) N K := by
  classical
  let coeff : ℕ → ℝ := fun m =>
    max (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + m) + 2)) * C m) 0
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  let K : ℝ := (Finset.range (N + 1)).sup' hne coeff
  have hK : 0 ≤ K := (le_max_right _ _).trans
    (Finset.le_sup' coeff (show 0 ∈ Finset.range (N + 1) by simp))
  refine ⟨K, hK, fun k => ?_⟩
  let : TopologicalSpace (X.term k).M := (X.term k).topology
  let : ChartedSpace H (X.term k).M := (X.term k).charted
  let : IsManifold I ∞ (X.term k).M := (X.term k).smooth
  let : T2Space (X.term k).M := (X.term k).t2
  intro m hm _ t ht x _
  calc
    _ ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + m) + 2)) *
        curvDerivNorm m ((X.term k).S.base.metric t) x :=
      sqrt_normSq0S_ricCovTower_le_curvDerivNorm ((X.term k).S.base.metric t) m x
    _ ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + m) + 2)) * C m :=
      mul_le_mul_of_nonneg_left (hcurv k m hm t ht x) (Real.sqrt_nonneg _)
    _ ≤ coeff m := le_max_left _ _
    _ ≤ K := Finset.le_sup' coeff (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hm))

end DifferentialGeometry.CheegerGromovCompactness
