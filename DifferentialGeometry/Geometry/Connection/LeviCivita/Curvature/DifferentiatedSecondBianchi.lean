import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Realized
import DifferentialGeometry.Tensor.RSTensor.NablaDomDomCongr

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Topology Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

/-!
# Differentiated second Bianchi identity

This file differentiates the canonical lowered second Bianchi identity while
keeping the new leading covariant-derivative slot fixed.  The result is the
rank-six cyclic identity needed before contracting `∇²Rm04` in the
arbitrary-dimensional Hamilton curvature evolution formula.
-/

/-- Cyclically route the first three slots of a rank-five tensor. -/
private def rmBianchiCyc : Fin 5 ≃ Fin 5 :=
  Equiv.ofBijective ![1, 2, 0, 3, 4] (by decide)

/-- Apply the inverse cyclic routing to the first three rank-five slots. -/
private def rmBianchiCyc2 : Fin 5 ≃ Fin 5 :=
  Equiv.ofBijective ![2, 0, 1, 3, 4] (by decide)

/-- The second covariant derivative of canonical lowered Riemann satisfies the
differentiated second Bianchi identity.  Its slots are
`(outer derivative, inner derivative, X, Y, Z, W)`. -/
theorem canRmSecond_nabla
    (g : SmoothRiemannianMetric I M)
    {x : M} (V A X Y Z W : TangentSpace I x) :
    let cov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric
        (I := I) g
    let hcov :=
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section
        (I := I) g cov hcov
    let nablaRm04 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 5 :=
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          4 cov hcov Rm04)
    let nabla2Rm04 :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        5 cov nablaRm04 x
    nabla2Rm04 (Fin.cons V (vec5 (I := I) A X Y Z W)) +
        nabla2Rm04 (Fin.cons V (vec5 (I := I) X Y A Z W)) +
      nabla2Rm04 (Fin.cons V (vec5 (I := I) Y A X Z W)) = 0 := by
  classical
  let cov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric
      (I := I) g
  let hcov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section
      (I := I) g cov hcov
  let nablaRm04 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 5 :=
    totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov Rm04
      (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        4 cov hcov Rm04)
  let nabla2Rm04 :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      5 cov nablaRm04 x
  let nablaRmCyc : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 5 :=
    MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) rmBianchiCyc nablaRm04
  let nablaRmCyc2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 5 :=
    MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) rmBianchiCyc2 nablaRm04
  have hcyc : nablaRm04 + nablaRmCyc + nablaRmCyc2 = 0 := by
    refine DFunLike.ext _ _ fun y => ?_
    apply ContinuousMultilinearMap.ext
    intro slots
    change nablaRm04 y slots +
        nablaRm04 y (slots ∘ rmBianchiCyc) +
      nablaRm04 y (slots ∘ rmBianchiCyc2) = 0
    have hB := canRmSecond (I := I) (M := M) g (x := y)
    dsimp at hB
    have hB' := hB (slots 0) (slots 1) (slots 2) (slots 3) (slots 4)
    have h0 :
        vec5 (I := I) (slots 0) (slots 1) (slots 2) (slots 3) (slots 4) = slots := by
      funext q
      fin_cases q <;> simp [vec5]
    have h1 :
        vec5 (I := I) (slots 1) (slots 2) (slots 0) (slots 3) (slots 4) =
          slots ∘ rmBianchiCyc := by
      funext q
      fin_cases q <;> simp [vec5, rmBianchiCyc]
    have h2 :
        vec5 (I := I) (slots 2) (slots 0) (slots 1) (slots 3) (slots 4) =
          slots ∘ rmBianchiCyc2 := by
      funext q
      fin_cases q <;> simp [vec5, rmBianchiCyc2]
    rwa [h0, h1, h2] at hB'
  have hzero :
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          5 cov
          (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 5) x = 0 := by
    let nablaZero :=
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        5 cov
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 5)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          5 cov hcov 0)
    have hcan : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 5 cov
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 5)
        nablaZero := by
      exact totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 5 cov 0 _
    have heq : nablaZero =
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 6) :=
      totalNabla0SRealizes_unique (I := I) hcan
        (zero_realizes_nabla (I := I) 5 cov)
    have hx := congrArg (fun T => T x) heq
    simpa [nablaZero] using hx
  have hderiv :
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          5 cov (nablaRm04 + nablaRmCyc + nablaRmCyc2) x = 0 := by
    rw [hcyc]
    exact hzero
  rw [totalNabla0SFun_add (I := I), totalNabla0SFun_add (I := I),
    totalNabla0SFun_domDomCongr (I := I),
    totalNabla0SFun_domDomCongr (I := I)] at hderiv
  have heval := congrArg
    (fun T => T (Fin.cons V (vec5 (I := I) A X Y Z W))) hderiv
  change nabla2Rm04 (Fin.cons V (vec5 (I := I) A X Y Z W)) +
      nabla2Rm04
        ((Fin.cons V (vec5 (I := I) A X Y Z W)) ∘
          frontExtendEquiv rmBianchiCyc) +
    nabla2Rm04
      ((Fin.cons V (vec5 (I := I) A X Y Z W)) ∘
        frontExtendEquiv rmBianchiCyc2) = 0 at heval
  have h1 :
      (Fin.cons V (vec5 (I := I) A X Y Z W)) ∘ frontExtendEquiv rmBianchiCyc =
        Fin.cons V (vec5 (I := I) X Y A Z W) := by
    have htail :
        vec5 (I := I) A X Y Z W ∘ rmBianchiCyc =
          vec5 (I := I) X Y A Z W := by
      funext q
      fin_cases q <;> simp [vec5, rmBianchiCyc]
    funext q
    rw [Function.comp_apply, cons_apply_frontExtendEquiv, htail]
  have h2 :
      (Fin.cons V (vec5 (I := I) A X Y Z W)) ∘ frontExtendEquiv rmBianchiCyc2 =
        Fin.cons V (vec5 (I := I) Y A X Z W) := by
    have htail :
        vec5 (I := I) A X Y Z W ∘ rmBianchiCyc2 =
          vec5 (I := I) Y A X Z W := by
      funext q
      fin_cases q <;> simp [vec5, rmBianchiCyc2]
    funext q
    rw [Function.comp_apply, cons_apply_frontExtendEquiv, htail]
  simpa [h1, h2] using heval

end DifferentialGeometry.Integral.Connection
