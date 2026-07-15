import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The rank-uniform component realization of `iterCov` (`∇ᵃ` of any tensor field)

`Evolution/RmRealizationBridgeAllK.lean` proves the all-`k` bridge
`iteratedRmComp … k = nablaKRm04Field … k` for the lowered Riemann tensor and the
*moving* connection.  The MSM135 Lemma 3.11 covariant-derivative estimate (eq 3.4)
needs the same bridge for an **arbitrary** covariant `(0,r)` field and the **fixed**
background connection (the Levi-Civita connection of `gRef`), because both sides of
the target estimate `|∇ᵃRc| ≤ C̃ |∇ᵃg| + C̃'` are `√normSq0S` of `iterCov gRef`-towers
(`metricCovDeriv = iterCov gRef`).

This file provides:

* `iterCovComp` — the general iterated `covDerivStepComp` component tower (any base
  array, any Christoffel data), the rank/base-uniform generalization of
  `iteratedRmComp`.
* `iterCov_realizes` — the canonical step realization of `iterCov`, read off from
  `covStep = totalNabla0S` (`covStep_apply`) and `totalNabla0S_realizes`.
* `iterCovComp_eq_iterCov` — **the bridge**: at every point of a local frame, the
  general component tower fed `gRef`'s in-frame Christoffel data and the
  frame-component array of `T` equals `iterCov gRef r T a` on the frame vectors.
  Proved by induction on `a` exactly as `iteratedRmComp_eq_nablaKRm04Field`, using
  the rank-uniform step bridge `covDerivStepComp_frameComp_eq`.
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

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}

/-! ## The general iterated component tower -/

/-- The general iterated covariant-derivative component tower: `a` applications of
`covDerivStepComp`, starting from a base component array of rank `r`, using the
frame directional derivative of the running array and fixed Christoffel data.

This is the base/rank-uniform generalization of `iteratedRmComp` (which fixes
`r = 4`, the Riemann base, and threads a time parameter). -/
def iterCovComp {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real) :
    (a : ℕ) → M → (Fin (r + a) → Idx) → Real
  | 0 => base
  | (a + 1) => fun x =>
      covDerivStepComp
        (frameExtData (I := I) frame
          (fun y : M => iterCovComp frame chr base a y) x)
        (chr x)
        (iterCovComp frame chr base a x)

@[simp] theorem iterCovComp_zero {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real) :
    iterCovComp (I := I) frame chr base 0 = base := rfl

theorem iterCovComp_succ {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real) (a : ℕ) (x : M) :
    iterCovComp (I := I) frame chr base (a + 1) x =
      covDerivStepComp
        (frameExtData (I := I) frame
          (fun y : M => iterCovComp (I := I) frame chr base a y) x)
        (chr x)
        (iterCovComp (I := I) frame chr base a x) := rfl

/-! ## The step realization of `iterCov` -/

/-- **The step realization of `iterCov`.**  `iterCov gRef r T (a+1)` realizes the
canonical total covariant derivative of `iterCov gRef r T a`, read off from the
definitional `covStep = totalNabla0SFun` (`covStep_apply`) together with the
rank-uniform `totalNabla0S_realizes`. -/
theorem iterCov_realizes
    (gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r) (a : ℕ) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (r + a) (leviCivitaConnectionOfMetric (I := I) gRef)
      (iterCov (I := I) gRef r T a)
      (iterCov (I := I) gRef r T (a + 1)) := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) (leviCivitaConnectionOfMetric (I := I) gRef)
        (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) gRef
  intro X x slots
  rw [iterCov_succ, covStep_apply]
  exact totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (r + a) (leviCivitaConnectionOfMetric (I := I) gRef)
    (iterCov (I := I) gRef r T a)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M) (r + a)
      (leviCivitaConnectionOfMetric (I := I) gRef) hcov
      (iterCov (I := I) gRef r T a))
    X x slots

/-! ## The bridge -/

/-- **The rank-uniform `iterCov` component realization.**  At every point of a local
frame, the general component tower fed `gRef`'s in-frame Christoffel data and the
frame-component array of `T` equals `iterCov gRef r T a` evaluated on the frame
vectors.

Proved by induction on `a`, exactly as `iteratedRmComp_eq_nablaKRm04Field`: the base
`a = 0` is definitional (`frameComp0S`), and the step rewrites the inner level-`a`
tower as the frame-component array of the bundled `iterCov … a` throughout the frame
neighbourhood (the inductive hypothesis), then applies the rank-uniform step bridge
`covDerivStepComp_frameComp_eq` for the rank-`(r+a)` field `iterCov … a`. -/
theorem iterCovComp_eq_iterCov
    (gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u) :
    ∀ (a : ℕ) {x : M}, x ∈ u → ∀ n : Fin (r + a) → Idx,
      iterCovComp (I := I) frame
          (fun y : M =>
            christoffelSymbolInFrame
              (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y)
          (frameComp0S (I := I) T frame) a x n =
        iterCov (I := I) gRef r T a x (frameTuple (I := I) frame x n) := by
  classical
  intro a
  induction a with
  | zero =>
      intro x hx n
      rw [iterCovComp_zero]
      rfl
  | succ a ih =>
      intro x hx n
      -- The inner level-`a` tower equals the frame-component array of the bundled
      -- `iterCov … a` throughout the frame neighbourhood (the IH).
      have hlevela :
          (fun y : M =>
              iterCovComp (I := I) frame
                (fun z : M =>
                  christoffelSymbolInFrame
                    (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe z)
                (frameComp0S (I := I) T frame) a y) =ᶠ[nhds x]
            fun y : M =>
              frameComp0S (I := I) (iterCov (I := I) gRef r T a) frame y := by
        refine Filter.eventually_of_mem (hu.mem_nhds hx) ?_
        intro y hy
        funext m
        simpa [frameComp0S, frameTuple] using ih hy m
      -- Expand the level-`(a+1)` step.
      rw [iterCovComp_succ]
      -- Rewrite the `covDerivStepComp` inputs using the level-`a` identity near `x`.
      have hext :
          frameExtData (I := I) frame
              (fun y : M =>
                iterCovComp (I := I) frame
                  (fun z : M =>
                    christoffelSymbolInFrame
                      (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe z)
                  (frameComp0S (I := I) T frame) a y) x =
            frameExtData (I := I) frame
              (frameComp0S (I := I) (iterCov (I := I) gRef r T a) frame) x := by
        funext m d
        simp only [frameExtData]
        refine extDerivFun_eventuallyEq_congr (I := I) _ ?_
        exact hlevela.mono fun y hy => congrFun hy m
      have hbase :
          iterCovComp (I := I) frame
              (fun z : M =>
                christoffelSymbolInFrame
                  (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe z)
              (frameComp0S (I := I) T frame) a x =
            frameComp0S (I := I) (iterCov (I := I) gRef r T a) frame x :=
        hlevela.self_of_nhds
      rw [hext, hbase]
      -- Apply the rank-uniform step bridge for the rank-`(r+a)` field `iterCov … a`.
      exact covDerivStepComp_frameComp_eq
        (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
        (iterCov (I := I) gRef r T a)
        (iterCov (I := I) gRef r T (a + 1))
        (iterCov_realizes (I := I) gRef T a)
        frame hframe hu hx n

end DifferentialGeometry.PDE.RicciFlow
