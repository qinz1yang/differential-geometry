import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativeRestriction

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Manifold Topology ContDiff ENNReal

open DifferentialGeometry.Geometry.Curvature.CovariantDerivative

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
  [IsManifold I 1 M] [IsManifold I 2 M]

omit [I.Boundaryless] in
omit [IsManifold I 2 M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciSection_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [hManifoldU : IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (x : U) (slots : Fin 2 → TangentSpace I x) :
    CovariantDerivative.ricciSection (I := I)
        (leviCivitaConnectionOfMetric (I := I) (g.restrictOpen (I := I) U))
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
          (g.restrictOpen (I := I) U)) x slots
      = CovariantDerivative.ricciSection (I := I)
          (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g)
          (x : M) slots := by
  let _ := hManifoldU
  have hLHS :
      CovariantDerivative.ricciSection (I := I)
          (leviCivitaConnectionOfMetric (I := I) (g.restrictOpen (I := I) U))
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
            (g.restrictOpen (I := I) U)) x slots
        = ricciTensor (I := I) (M := U) (g.restrictOpen (I := I) U) x (slots 0) (slots 1) := by
    have hvecU : slots = vec2 (I := I) (slots 0) (slots 1) := by
      funext i; fin_cases i <;> rfl
    rw [hvecU]
    exact ricciSection_eq_ricciTensor (I := I) (g.restrictOpen (I := I) U) x (slots 0) (slots 1)
  have hRHS :
      CovariantDerivative.ricciSection (I := I)
          (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g)
          (x : M) slots
        = ricciTensor (I := I) (M := M) g (x : M) (slots 0) (slots 1) := by
    have hvecM : slots = vec2 (I := I) (slots 0) (slots 1) := by
      funext i; fin_cases i <;> rfl
    rw [hvecM]
    exact ricciSection_eq_ricciTensor (I := I) g (x : M) (slots 0) (slots 1)
  rw [hLHS, hRHS]
  exact ricciTensor_restrictOpen (I := I) g U x (slots 0) (slots 1)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem covDerivOfField_apply_eq_iterCov'
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (m : ℕ) (x : M) (slots : Fin (m + 2) → TangentSpace I x) :
    covDerivOfField (I := I) gRef A0 m x slots
      = iterCov (I := I) gRef 2 A0 m x (slots ∘ ⇑(acEquiv m)) := by
  rw [covDerivOfField_eq_iterCov]
  rfl

omit [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricCovTower_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I 2 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (s : ℕ) (x : U) (slots : Fin (2 + s) → TangentSpace I x) :
    ricCovTower (I := I) (g.restrictOpen (I := I) U)
        (g.restrictOpen (I := I) U) s x slots
      = ricCovTower (I := I) g g s (x : M) slots := by
  have hrestrict := covDerivOfField_restrictOpen (I := I) g U
    (CovariantDerivative.ricciSection (I := I)
      (leviCivitaConnectionOfMetric (I := I) (g.restrictOpen (I := I) U))
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
        (g.restrictOpen (I := I) U)))
    (CovariantDerivative.ricciSection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g))
    (ricciSection_restrictOpen (I := I) g U) s x (slots ∘ (acEquiv s).symm)
  rw [covDerivOfField_apply_eq_iterCov', covDerivOfField_apply_eq_iterCov'] at hrestrict
  convert hrestrict using 2 <;>
    · funext i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]

omit [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricCovTower_normSq0S_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I 2 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (s : ℕ) (x : U) :
    Tensor0SBundle.normSq0S (I := I) (g.restrictOpen (I := I) U) x (2 + s)
        (ricCovTower (I := I) (g.restrictOpen (I := I) U)
          (g.restrictOpen (I := I) U) s x)
      = Tensor0SBundle.normSq0S (I := I) g (x : M) (2 + s)
          (ricCovTower (I := I) g g s (x : M)) := by
  rw [normSq0S_restrictOpen_apply (I := I) g U (2 + s) x
    (ricCovTower (I := I) (g.restrictOpen (I := I) U) (g.restrictOpen (I := I) U) s x)]
  have htensor :
      ricCovTower (I := I) (g.restrictOpen (I := I) U) (g.restrictOpen (I := I) U) s x
        = ricCovTower (I := I) g g s (x : M) := by
    ext slots
    exact ricCovTower_restrictOpen (I := I) g U s x slots
  rw [htensor]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem movingShiBoundOn_restrictOpen
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I 2 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (U₀ : Set M) (β ψ : ℝ) (Nord : ℕ) (KShi : ℝ) (V : Set U)
    (hV : ∀ x ∈ V, (x : M) ∈ U₀)
    (hShi : MovingShiBoundOn (I := I) U₀ β ψ gSeq Nord KShi) :
    MovingShiBoundOn (I := I) V β ψ
      (fun i t => (gSeq i t).restrictOpen (I := I) U) Nord KShi := by
  intro s hs i t ht x hx
  rw [ricCovTower_normSq0S_restrictOpen (I := I) (gSeq i t) U s x]
  exact hShi s hs i t ht (x : M) (hV x hx)

end HCGCompactness
end DifferentialGeometry

end
