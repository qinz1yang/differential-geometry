import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Lemma45Engine
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The intrinsic-norm lift for MSM135 Lemma 4.5 (the `hF3` producer kernel)

`lemma45_F3` (`Lemma45Engine.lean`) proves Lemma I at the level of frame-component
`compL2` towers.  `lemma45_cor_II_of_intrinsic` (`Lemma45Covariant.lean`) consumes
the **intrinsic** (`normSq0S`) form `hF3`.  The bridge is the orthonormal-frame
Parseval identity — but F4 needs it in a **decoupled** form: the norm is measured
in the moving metric `g`, while the tower is built from the *reference* metric's
connection.  The matched-metric `B5` (`compL2_tower_eq`, `Claim1Wiring.lean`)
cannot express that; `compL2_tower_eq_gen` below does.

`compL2_tower_eq_gen`: at a point where the frame is `g`-orthonormal, the
`compL2` of the `gC`-Levi-Civita tower of a field `T` equals the intrinsic
`g`-norm of the `iterCov gC` tower — for ANY metric `gC` driving the connection.
With `gC = g` this is the `g`-version of `B5`; with `gC = gRef` it is exactly the
`√normSq0S g (∇_gRef^k T)` term in `hF3`'s right-hand side.
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

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- **The decoupled tower norm identity** (generalized `B5`).  At a point `y`
where the local frame is `g`-orthonormal (`hinv`), the frame-component `compL2`
of the order-`j` `gC`-Levi-Civita derivative tower of a `(0,r)` field `T` equals
the intrinsic `g`-norm of the `iterCov gC` tower:
`compL2 (∇_{gC}^j T)_frame = √normSq0S g (iterCov gC r T j)`.
The norm metric `g` (from the orthonormal frame + `normSq0S`) is decoupled from
the connection metric `gC` (driving the tower).  Same proof as `compL2_tower_eq`
with the two metrics separated; `gC = g` recovers the matched `B5`. -/
theorem compL2_tower_eq_gen
    (g gC : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u)
    {y : M} (hy : y ∈ u)
    (hinv : Tensor0SBundle.MetricInverseInBasis (I := I) g y (hframe.toBasisAt hy)
      (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (j : ℕ) :
    compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gC) frame hframe y')
        (frameComp0S (I := I) T frame) j y) =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y (r + j)
        (iterCov (I := I) gC r T j y)) := by
  rw [compL2]
  congr 1
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) g y (r + j)
    (hframe.toBasisAt hy) hinv (iterCov (I := I) gC r T j y)]
  simp only [compL2Sq]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [iterCovComp_eq_iterCov (I := I) gC T frame hframe hu j hy n]
  congr 1
  rw [Tensor0SBundle.component0S_apply]
  congr 1
  funext q
  rw [IsLocalFrameOn.toBasisAt_coe]
  rfl

/-- **The intrinsic Lemma I from the component Lemma I** (the `hF3` lift atom).
At a `g`-orthonormal frame point `x`, a single-order `compL2` Lemma-I inequality
(`lemma45_F3`'s output for the bundled field `T`) lifts to the intrinsic
`normSq0S g` form: `|∇_g^r T|_g ≤ |∇_gRef^r T|_g + ε·Cc·Σ_{k<r}|∇_gRef^k T|_g`.
The LHS lifts through `compL2_tower_eq_gen` at `gC = g`; the `gRef`-tower terms
through `gC = gRef` (the decoupled norm metric stays `g`).  Feeding this into
`lemma45_cor_II_of_intrinsic` discharges F4's `hF3`. -/
theorem hF3_term {q₂ : ℕ} {u : Set M} (hu : IsOpen u)
    (g gRef : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q₂)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    {x : M} (hx : x ∈ u)
    (hinv : Tensor0SBundle.MetricInverseInBasis (I := I) g x (hframe.toBasisAt hx)
      (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (eps Cc : Real) (r : ℕ)
    (hineq :
      compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) g) frame hframe y')
          (frameComp0S (I := I) T frame) r x) ≤
        compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
          (frameComp0S (I := I) T frame) r x) +
        eps * Cc * ∑ k ∈ Finset.range r,
          compL2 (iterCovComp (I := I) frame
            (fun y' => christoffelSymbolInFrame
              (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
            (frameComp0S (I := I) T frame) k x)) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + r) (iterCov (I := I) g q₂ T r x)) ≤
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + r)
        (iterCov (I := I) gRef q₂ T r x)) +
      eps * Cc * ∑ k ∈ Finset.range r,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + k)
          (iterCov (I := I) gRef q₂ T k x)) := by
  rw [← compL2_tower_eq_gen (I := I) g g T frame hframe hu hx hinv r,
    ← compL2_tower_eq_gen (I := I) g gRef T frame hframe hu hx hinv r,
    show (∑ k ∈ Finset.range r,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + k)
          (iterCov (I := I) gRef q₂ T k x))) =
      ∑ k ∈ Finset.range r,
        compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
          (frameComp0S (I := I) T frame) k x) from
      Finset.sum_congr rfl fun k _ =>
        (compL2_tower_eq_gen (I := I) g gRef T frame hframe hu hx hinv k).symm]
  exact hineq

end DifferentialGeometry.PDE.RicciFlow
