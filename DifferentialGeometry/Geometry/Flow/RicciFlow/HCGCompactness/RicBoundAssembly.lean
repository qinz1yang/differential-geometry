import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBoundClaims
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Claim1Wiring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# ric_bound assembly: from the component `(A_N)` bound to the intrinsic norm bound

This file lifts the per-frame component `(A_N)` bound (`aN_component`,
`RicBoundClaims.lean`) to the intrinsic `gRef`-norm form needed by the
`ric_bound` endpoint, using the `B5` component↔intrinsic bridge
`compL2_tower_eq` (`Claim1Wiring.lean`) at a `gRef`-orthonormal frame point.

* **`tower_bound_to_intrinsic`** (R4b): the pure `B5`-lift — a component-tower
  inequality between two bundled `(0,2)` fields converts, at a `gRef`-ON point,
  into the corresponding `√normSq0S` inequality of their `iterCov` towers.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- **R4b — the `B5` lift.**  If the order-`N` `gRef`-frame component towers of
two bundled `(0,2)` fields `T`, `T'` satisfy a linear inequality at a point `y`
where the frame is `gRef`-orthonormal (`hinv`), then their intrinsic
`√normSq0S` towers satisfy the same inequality.  Both sides are rewritten by
`compL2_tower_eq` (`B5`). -/
theorem tower_bound_to_intrinsic
    (gRef : SmoothRiemannianMetric I M)
    (T T' : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u)
    {y : M} (hy : y ∈ u)
    (hinv : Tensor0SBundle.MetricInverseInBasis (I := I) gRef y (hframe.toBasisAt hy)
      (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (N : ℕ) (Cpp Cppp : Real)
    (hbound :
      compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
          (frameComp0S (I := I) T frame) N y) ≤
        Cpp * compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
          (frameComp0S (I := I) T' frame) N y) + Cppp) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (2 + N)
        (iterCov (I := I) gRef 2 T N y)) ≤
      Cpp * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (2 + N)
        (iterCov (I := I) gRef 2 T' N y)) + Cppp := by
  rw [← compL2_tower_eq (I := I) gRef T frame hframe hu hy hinv N,
    ← compL2_tower_eq (I := I) gRef T' frame hframe hu hy hinv N]
  exact hbound

/-- **R4c — the per-frame-point intrinsic `(A_N)` bound.**  On a smooth local
frame domain `u` that is `gRef`-orthonormal at a point `y` (`hinvON`), with the
`claim1_LC` geometric inputs (frame smoothness, the two LC frame Christoffels'
smoothness, the metric-component smoothness, the `g`-inverse data `Ginv`/`hinv`/
`hGinv`), the lower-order metric-derivative bounds `|∇_H^j g| ≤ Kg` for
`1 ≤ j ≤ N − 1` (`hgB`, the `(B_r)` inputs), and the moving Shi bounds on the
Ricci component tower up to order `N` (`hShi`), the intrinsic `gRef`-norm of the
order-`N` `gRef`-derivative of `Ric(g)` is bounded linearly by that of the
metric:
`√normSq0S gRef (∇_gRef^N Ric(g)) ≤ Cpp·√normSq0S gRef (∇_gRef^N g) + Cppp` at `y`.
Chain: `claim1_LC` (totalized lower bounds + the top bound) → `aN_component`
(the component `(A_N)`) → `tower_bound_to_intrinsic` (the `B5` lift at `y`). -/
theorem aN_intrinsic_point
    (g gRef : SmoothRiemannianMetric I M)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u)
    (hframeS : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrG : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (leviCivitaConnectionOfMetric (I := I) g) frame hframe y d i j) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y d i j) u)
    (hgsm : ∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I) (metricTensorField (I := I) g) frame y k) u)
    (Ginv : M → (Fin (1 + 1) → Idx) → Real)
    (hinv : ∀ x ∈ u, ∀ c e : Idx,
      (∑ l : Idx, frameComp0S (I := I) (metricTensorField (I := I) g) frame x
          (Fin.snoc (fun _ : Fin 1 => l) c) *
        Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0)
    (C0 : Real) (hGinv : ∀ x ∈ u, compL2 (Ginv x) ≤ C0)
    (hRicSm : ∀ k : Fin 2 → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I)
        (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
          (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g))
        frame y k) u)
    (N : ℕ) (hN : 1 ≤ N)
    (Kg : Real) (hKg0 : 0 ≤ Kg)
    (hgB : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ N - 1 →
      compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
        (frameComp0S (I := I) (metricTensorField (I := I) g) frame) j x) ≤ Kg)
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (hShi : ∀ z ∈ u, ∀ s : ℕ, s ≤ N →
      compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) g) frame hframe y')
        (frameComp0S (I := I)
          (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
            (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g))
          frame) s z) ≤ KShi)
    {y : M} (hy : y ∈ u)
    (hinvON : Tensor0SBundle.MetricInverseInBasis (I := I) gRef y (hframe.toBasisAt hy)
      (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    ∃ Cpp Cppp : Real, 0 ≤ Cpp ∧ 0 ≤ Cppp ∧
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (2 + N)
        (iterCov (I := I) gRef 2
          (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
            (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g))
          N y)) ≤
        Cpp * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (2 + N)
          (iterCov (I := I) gRef 2 (metricTensorField (I := I) g) N y)) + Cppp := by
  classical
  -- totalize the lower-order difference-tower constants from `claim1_LC`
  have hBd : ∀ c : ℕ, ∃ Bc, 0 ≤ Bc ∧ (c < N - 1 → ∀ z ∈ u,
      compL2 (iterCovCompU (I := I) frame
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
        (chrDiffField
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) g) frame hframe y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')) c z) ≤ Bc) := by
    intro c
    by_cases hc : c < N - 1
    · obtain ⟨C, hC0, hCb⟩ := claim1_LC hu g gRef frame hframe hframeS hchrG hchrH hgsm Ginv hinv
        C0 Kg hGinv c (fun x hx j h1 h2 => hgB x hx j h1 (by omega))
      refine ⟨C * (1 + Kg), mul_nonneg hC0 (by linarith), fun _ z hz => ?_⟩
      have hg := hgB z hz (c + 1) (by omega) (by omega)
      have hcb := hCb z hz
      have hgnn := compL2_nonneg (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
        (frameComp0S (I := I) (metricTensorField (I := I) g) frame) (c + 1) z)
      nlinarith [hC0, hg, hcb, hgnn]
    · exact ⟨0, le_rfl, fun h => absurd h hc⟩
  choose B hB0 hBb using hBd
  -- the top difference-tower bound from `claim1_LC` at `m = N - 1`
  obtain ⟨Ctop, hCtop0, htop⟩ := claim1_LC hu g gRef frame hframe hframeS hchrG hchrH hgsm Ginv hinv
    C0 Kg hGinv (N - 1) (fun x hx j h1 h2 => hgB x hx j h1 h2)
  have hDtop : ∀ x ∈ u,
      compL2 (iterCovCompU (I := I) frame
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
        (chrDiffField
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) g) frame hframe y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')) (N - 1) x) ≤
        Ctop * (1 + compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
          (frameComp0S (I := I) (metricTensorField (I := I) g) frame) N x)) := by
    intro x hx
    have h := htop x hx
    rwa [show N - 1 + 1 = N from by omega] at h
  -- the per-frame component `(A_N)` bound
  obtain ⟨Cpp, Cppp, hpp0, hppp0, hcomp⟩ := aN_component hu frame
    (fun y' => christoffelSymbolInFrame
      (leviCivitaConnectionOfMetric (I := I) g) frame hframe y')
    (fun y' => christoffelSymbolInFrame
      (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
    hframeS hchrG hchrH
    (frameComp0S (I := I)
      (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
        (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g))
      frame)
    hRicSm N hN B hB0 (fun c hc z hz => hBb c hc z hz)
    (frameComp0S (I := I) (metricTensorField (I := I) g) frame) Ctop hCtop0 hDtop
    KShi hKShi0 hShi
  exact ⟨Cpp, Cppp, hpp0, hppp0,
    tower_bound_to_intrinsic gRef
      (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
        (I := I) (M := M) (leviCivitaConnectionOfMetric (I := I) g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g))
      (metricTensorField (I := I) g) frame hframe hu hy hinvON N Cpp Cppp (hcomp y hy)⟩

end DifferentialGeometry.PDE.RicciFlow
