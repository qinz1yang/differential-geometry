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
  simpa only [metricRicci, metricCov, mfderiv_subtype_val_apply] using
    metricRicci_restrictOpen_eval (I := I) g U x slots

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
  let slotsU : Fin (s + 2) → TangentSpace I x := slots ∘ (acEquiv s).symm
  let slotsM : Fin (2 + s) → TangentSpace I (x : M) := fun i => slots i
  let slotsCovM : Fin (s + 2) → TangentSpace I (x : M) :=
    slotsM ∘ (acEquiv s).symm
  let slotsUCoe : Fin (s + 2) → TangentSpace I (x : M) := fun i => slotsU i
  have hrestrict := covDerivOfField_restrictOpen (I := I) g U
    (CovariantDerivative.ricciSection (I := I)
      (leviCivitaConnectionOfMetric (I := I) (g.restrictOpen (I := I) U))
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
        (g.restrictOpen (I := I) U)))
    (CovariantDerivative.ricciSection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g))
    (ricciSection_restrictOpen (I := I) g U) s x slotsU
  change covDerivOfField (I := I) (g.restrictOpen (I := I) U)
      (CovariantDerivative.ricciSection (I := I)
        (leviCivitaConnectionOfMetric (I := I) (g.restrictOpen (I := I) U))
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
          (g.restrictOpen (I := I) U))) s x slotsU =
    covDerivOfField (I := I) g
      (CovariantDerivative.ricciSection (I := I)
        (leviCivitaConnectionOfMetric (I := I) g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g))
      s (x : M) slotsUCoe at hrestrict
  have hslots : slotsUCoe = slotsCovM := by
    funext i
    rfl
  rw [hslots] at hrestrict
  rw [covDerivOfField_apply_eq_iterCov' (I := I),
    covDerivOfField_apply_eq_iterCov' (I := I)] at hrestrict
  change
    (iterCov (I := I) (g.restrictOpen (I := I) U) 2
      (CovariantDerivative.ricciSection (I := I)
        (leviCivitaConnectionOfMetric (I := I) (g.restrictOpen (I := I) U))
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
          (g.restrictOpen (I := I) U))) s x) slots =
      (iterCov (I := I) g 2
        (CovariantDerivative.ricciSection (I := I)
          (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g))
        s (x : M)) slotsM
  convert hrestrict using 2 <;>
    funext i
  · change slots i = slots ((acEquiv s).symm ((acEquiv s) i))
    rw [Equiv.symm_apply_apply]
  · change slotsM i = slotsM ((acEquiv s).symm ((acEquiv s) i))
    rw [Equiv.symm_apply_apply]

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
