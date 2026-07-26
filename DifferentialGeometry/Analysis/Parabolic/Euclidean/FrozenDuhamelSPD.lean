import DifferentialGeometry.Analysis.Parabolic.Euclidean.FrozenDuhamel
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelSPD
import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

/-!
# Frozen positive-definite Duhamel evolution

This file conjugates the dimension-generic isotropic producer in
`FrozenDuhamel` by the canonical positive square root of a real
positive-definite matrix.  It exposes the value, gradient, and Hessian maps
in the original coordinates and proves the actual constant-coefficient PDE

`(∂ₜ - A : D²) H_A(a ⊗ u) = a(t) u`.

The matrix contraction is not hidden behind an assumed operator identity.
`spd_factorLap` expands the square-root trace and identifies it with the
double matrix contraction.
-/

noncomputable section

open MeasureTheory Real Matrix
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section Pullback

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Precomposition of a bounded continuous function by a continuous linear
equivalence. -/
def linPullBcf (L : V ≃L[ℝ] V) (u : BoundedContinuousFunction V F) :
    BoundedContinuousFunction V F where
  toFun := fun x => u (L x)
  continuous_toFun := u.continuous.comp L.continuous
  map_bounded' := by
    obtain ⟨C, hC⟩ := u.bounded
    exact ⟨C, fun x y => hC (L x) (L y)⟩

@[simp]
theorem linPullBcf_apply (L : V ≃L[ℝ] V)
    (u : BoundedContinuousFunction V F) (x : V) :
    linPullBcf L u x = u (L x) := rfl

/-- Precompose a continuous linear map by `L`, bundled as a continuous
linear operation on the operator space. -/
def precompJet (L : V ≃L[ℝ] V) :
    (V →L[ℝ] F) →L[ℝ] V →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ V V F).flip
    (L : V →L[ℝ] V)

@[simp]
theorem precompJet_apply (L : V ≃L[ℝ] V) (D : V →L[ℝ] F) (v : V) :
    precompJet L D v = D (L v) := by
  simp [precompJet, ContinuousLinearMap.compL_apply]

/-- Apply `L` in both slots of a bounded bilinear map. -/
def pushHess (L : V ≃L[ℝ] V) :
    (V →L[ℝ] V →L[ℝ] F) →L[ℝ] V →L[ℝ] V →L[ℝ] F :=
  let P := precompJet (F := F) L
  ((ContinuousLinearMap.compL ℝ V (V →L[ℝ] F) (V →L[ℝ] F)) P).comp
    ((ContinuousLinearMap.compL ℝ V V (V →L[ℝ] F)).flip
      (L : V →L[ℝ] V))

@[simp]
theorem pushHess_apply (L : V ≃L[ℝ] V)
    (B : V →L[ℝ] V →L[ℝ] F) (v w : V) :
    pushHess L B v w = B (L v) (L w) := by
  simp [pushHess, precompJet, ContinuousLinearMap.compL_apply]

/-- The first derivative jet of a pullback. -/
def pullJet1 (L : V ≃L[ℝ] V)
    (du : BoundedContinuousFunction V (V →L[ℝ] F)) :
    BoundedContinuousFunction V (V →L[ℝ] F) :=
  (precompJet (F := F) L).compLeftContinuousBounded V (linPullBcf L du)

/-- The second derivative jet of a pullback. -/
def pullJet2 (L : V ≃L[ℝ] V)
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F)) :
    BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F) :=
  (pushHess (F := F) L).compLeftContinuousBounded V (linPullBcf L d2u)

@[simp]
theorem pullJet1_apply (L : V ≃L[ℝ] V)
    (du : BoundedContinuousFunction V (V →L[ℝ] F)) (x v : V) :
    pullJet1 L du x v = du (L x) (L v) := by
  simp [pullJet1]

@[simp]
theorem pullJet2_apply (L : V ≃L[ℝ] V)
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (x v w : V) :
    pullJet2 L d2u x v w = d2u (L x) (L v) (L w) := by
  simp [pullJet2]

/-- A globally realized first jet pulls back to the explicitly transformed
jet. -/
theorem linPull_fderiv (L : V ≃L[ℝ] V)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x) (x : V) :
    HasFDerivAt (linPullBcf L u : V → F) (pullJet1 L du x) x := by
  have h := (hu (L x)).comp x L.hasFDerivAt
  simpa only [linPullBcf_apply, pullJet1_apply,
    ContinuousLinearMap.comp_apply] using h

/-- A globally realized second jet pulls back to the explicitly transformed
bilinear jet. -/
theorem pullJet1_fderiv (L : V ≃L[ℝ] V)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hdu : ∀ x : V,
      HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x) (x : V) :
    HasFDerivAt (pullJet1 L du : V → V →L[ℝ] F)
      (pullJet2 L d2u x) x := by
  have houter := (hdu (L x)).comp x L.hasFDerivAt
  have h := (precompJet (F := F) L).hasFDerivAt.comp x houter
  simpa only [pullJet1, pullJet2, pushHess, linPullBcf_apply,
    ContinuousLinearMap.compLeftContinuousBounded_apply,
    Function.comp_apply] using h

end Pullback

section TraceAlgebra

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The trace of a bilinear map may be computed in any finite orthonormal
basis. -/
theorem lapEval_basis {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ V) (B : V →L[ℝ] V →L[ℝ] F) :
    lapEval B = ∑ i, B (e i) (e i) := by
  let T : V ⊗[ℝ] V →ₗ[ℝ] F := TensorProduct.lift B.toLinearMap₁₂
  have h := congrArg T
    (InnerProductSpace.canonicalCovariantTensor_eq_sum V e)
  simpa only [T, InnerProductSpace.canonicalCovariantTensor, map_sum,
    TensorProduct.lift.tmul, ContinuousLinearMap.toLinearMap₁₂_apply,
    lapEval, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply] using h

variable {n : Type*} [Fintype n] [DecidableEq n]

private abbrev Euc (n : Type*) := EuclideanSpace ℝ n

/-- Trace in the directions obtained by applying a fixed linear equivalence
to the canonical Euclidean orthonormal basis. -/
def factorLap (L : Euc n ≃L[ℝ] Euc n)
    (B : Euc n →L[ℝ] Euc n →L[ℝ] F) : F :=
  ∑ i : n, B (L (EuclideanSpace.basisFun n ℝ i))
    (L (EuclideanSpace.basisFun n ℝ i))

/-- Matrix contraction with a bilinear map in canonical Euclidean
coordinates. -/
def matrixLap (A : Matrix n n ℝ)
    (B : Euc n →L[ℝ] Euc n →L[ℝ] F) : F :=
  ∑ i : n, ∑ j : n,
    A i j • B (EuclideanSpace.basisFun n ℝ i)
      (EuclideanSpace.basisFun n ℝ j)

/-- Pulling a Hessian back by `L⁻¹` converts the factor trace for `L` to the
ordinary isotropic trace. -/
theorem factorLap_pull (L : Euc n ≃L[ℝ] Euc n)
    (B : Euc n →L[ℝ] Euc n →L[ℝ] F) :
    factorLap L (pushHess (F := F) L.symm B) = lapEval B := by
  rw [lapEval_basis (EuclideanSpace.basisFun n ℝ)]
  apply Finset.sum_congr rfl
  intro i hi
  simp [factorLap]

/-- Expansion of a self-adjoint factor trace. -/
private theorem factorLap_self (L : Euc n ≃L[ℝ] Euc n)
    (hL : IsSelfAdjoint (L : Euc n →L[ℝ] Euc n))
    (B : Euc n →L[ℝ] Euc n →L[ℝ] F) :
    factorLap L B =
      ∑ i : n, ∑ j : n,
        ⟪EuclideanSpace.basisFun n ℝ i,
          L (L (EuclideanSpace.basisFun n ℝ j))⟫_ℝ •
            B (EuclideanSpace.basisFun n ℝ i)
              (EuclideanSpace.basisFun n ℝ j) := by
  let e := EuclideanSpace.basisFun n ℝ
  have hdiag : ∀ k : n,
      B (L (e k)) (L (e k)) =
        ∑ i : n, ∑ j : n,
          (⟪e i, L (e k)⟫_ℝ * ⟪e j, L (e k)⟫_ℝ) • B (e i) (e j) := by
    intro k
    have hk := e.sum_repr' (L (e k))
    calc
      B (L (e k)) (L (e k)) =
          B (∑ i : n, ⟪e i, L (e k)⟫_ℝ • e i)
            (∑ j : n, ⟪e j, L (e k)⟫_ℝ • e j) := by rw [hk, hk]
      _ = ∑ i : n, ∑ j : n,
          (⟪e i, L (e k)⟫_ℝ * ⟪e j, L (e k)⟫_ℝ) • B (e i) (e j) := by
        simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring_nf
  have hcoef : ∀ i j : n,
      (∑ k : n, ⟪e i, L (e k)⟫_ℝ * ⟪e j, L (e k)⟫_ℝ) =
        ⟪e i, L (L (e j))⟫_ℝ := by
    intro i j
    calc
      (∑ k : n, ⟪e i, L (e k)⟫_ℝ * ⟪e j, L (e k)⟫_ℝ) =
          ∑ k : n, ⟪L (e i), e k⟫_ℝ * ⟪e k, L (e j)⟫_ℝ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hL.isSymmetric, hL.isSymmetric]
        rw [real_inner_comm (e j) (L (e k)),
          real_inner_comm (L (e j)) (e k)]
      _ = ⟪L (e i), L (e j)⟫_ℝ := e.sum_inner_mul_inner _ _
      _ = ⟪e i, L (L (e j))⟫_ℝ := hL.isSymmetric _ _
  unfold factorLap
  simp_rw [hdiag]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_smul, hcoef]

/-- The canonical positive square root factors exactly the explicit matrix
contraction `A : B`. -/
theorem spd_factorLap (A : Matrix n n ℝ) (hA : A.PosDef)
    (B : Euc n →L[ℝ] Euc n →L[ℝ] F) :
    factorLap (spdSqrtEquiv A hA) B = matrixLap A B := by
  rw [factorLap_self (spdSqrtEquiv A hA) (spdSqrt_selfAdj A hA)]
  unfold matrixLap
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [spdSqrt_comp]
  have hentry :
      ⟪EuclideanSpace.basisFun n ℝ i,
        Matrix.toEuclideanCLM A (EuclideanSpace.basisFun n ℝ j)⟫_ℝ = A i j := by
    rw [Matrix.inner_toEuclideanCLM]
    simp [EuclideanSpace.basisFun_apply, dotProduct, Matrix.mulVec]
  rw [hentry]

end TraceAlgebra

section SPDEvolution

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private abbrev Euc (n : Type*) := EuclideanSpace ℝ n

/-- Frozen positive-definite Duhamel value in the original coordinates. -/
def spdDuh (A : Matrix n n ℝ) (hA : A.PosDef) (t : ℝ)
    (a : BoundedContinuousFunction ℝ ℝ)
    (u : BoundedContinuousFunction (Euc n) F) (x : Euc n) : F :=
  let L := spdSqrtEquiv A hA
  frozenDuh t a (linPullBcf L u) (L.symm x)

/-- Realized gradient of the frozen positive-definite Duhamel value. -/
def spdDuhD1 (A : Matrix n n ℝ) (hA : A.PosDef) (t : ℝ)
    (a : BoundedContinuousFunction ℝ ℝ)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[ℝ] F))
    (x : Euc n) : Euc n →L[ℝ] F :=
  let L := spdSqrtEquiv A hA
  (frozenDuh t a (pullJet1 L du) (L.symm x)).comp
    (L.symm : Euc n →L[ℝ] Euc n)

/-- Realized Hessian of the frozen positive-definite Duhamel value. -/
def spdDuhD2 (A : Matrix n n ℝ) (hA : A.PosDef) (t : ℝ)
    (a : BoundedContinuousFunction ℝ ℝ)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[ℝ] Euc n →L[ℝ] F))
    (x : Euc n) : Euc n →L[ℝ] Euc n →L[ℝ] F :=
  let L := spdSqrtEquiv A hA
  pushHess (F := F) L.symm
    (frozenDuh t a (pullJet2 L d2u) (L.symm x))

@[simp]
theorem spdDuh_zero (A : Matrix n n ℝ) (hA : A.PosDef)
    (a : BoundedContinuousFunction ℝ ℝ)
    (u : BoundedContinuousFunction (Euc n) F) (x : Euc n) :
    spdDuh A hA 0 a u x = 0 := by
  simp [spdDuh]

@[simp]
theorem spdDuhD1_zero (A : Matrix n n ℝ) (hA : A.PosDef)
    (a : BoundedContinuousFunction ℝ ℝ)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[ℝ] F))
    (x : Euc n) : spdDuhD1 A hA 0 a du x = 0 := by
  ext v
  simp [spdDuhD1]

@[simp]
theorem spdDuhD2_zero (A : Matrix n n ℝ) (hA : A.PosDef)
    (a : BoundedContinuousFunction ℝ ℝ)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[ℝ] Euc n →L[ℝ] F))
    (x : Euc n) : spdDuhD2 A hA 0 a d2u x = 0 := by
  ext v w
  simp [spdDuhD2]

/-- Original-coordinate value derivative. -/
theorem spdDuh_space (A : Matrix n n ℝ) (hA : A.PosDef) (t : ℝ)
    (a : BoundedContinuousFunction ℝ ℝ)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[ℝ] F))
    (hu : ∀ x : Euc n, HasFDerivAt (u : Euc n → F) (du x) x)
    (x : Euc n) :
    HasFDerivAt (fun y : Euc n => spdDuh A hA t a u y)
      (spdDuhD1 A hA t a du x) x := by
  let L := spdSqrtEquiv A hA
  have hpull : ∀ z : Euc n,
      HasFDerivAt (linPullBcf L u : Euc n → F) (pullJet1 L du z) z :=
    fun z => linPull_fderiv L u du hu z
  have h := (frozenDuh_space t a (linPullBcf L u)
    (pullJet1 L du) hpull (L.symm x)).comp x L.symm.hasFDerivAt
  simpa only [spdDuh, spdDuhD1, L, ContinuousLinearMap.comp_apply] using h

/-- Original-coordinate gradient derivative realizes the Hessian map. -/
theorem spdDuhD1_space (A : Matrix n n ℝ) (hA : A.PosDef) (t : ℝ)
    (a : BoundedContinuousFunction ℝ ℝ)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[ℝ] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[ℝ] Euc n →L[ℝ] F))
    (hdu : ∀ x : Euc n,
      HasFDerivAt (du : Euc n → Euc n →L[ℝ] F) (d2u x) x)
    (x : Euc n) :
    HasFDerivAt (fun y : Euc n => spdDuhD1 A hA t a du y)
      (spdDuhD2 A hA t a d2u x) x := by
  let L := spdSqrtEquiv A hA
  have hpull : ∀ z : Euc n,
      HasFDerivAt (pullJet1 L du : Euc n → Euc n →L[ℝ] F)
        (pullJet2 L d2u z) z :=
    fun z => pullJet1_fderiv L du d2u hdu z
  have hz := frozenDuh_space t a (pullJet1 L du)
    (pullJet2 L d2u) hpull (L.symm x)
  have hdom := hz.comp x L.symm.hasFDerivAt
  have h := (precompJet (F := F) L.symm).hasFDerivAt.comp x hdom
  simpa only [spdDuhD1, spdDuhD2, L, Function.comp_apply,
    ContinuousLinearMap.comp_apply] using h

/-- The original-coordinate Hessian contraction is the isotropic trace of
the pulled-back Hessian. -/
theorem spdDuh_lap (A : Matrix n n ℝ) (hA : A.PosDef) (t : ℝ)
    (a : BoundedContinuousFunction ℝ ℝ)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[ℝ] Euc n →L[ℝ] F)) (x : Euc n) :
    matrixLap A (spdDuhD2 A hA t a d2u x) =
      lapEval (frozenDuh t a
        (pullJet2 (spdSqrtEquiv A hA) d2u)
        ((spdSqrtEquiv A hA).symm x)) := by
  rw [← spd_factorLap A hA]
  exact factorLap_pull (spdSqrtEquiv A hA)
    (frozenDuh t a (pullJet2 (spdSqrtEquiv A hA) d2u)
      ((spdSqrtEquiv A hA).symm x))

/-- Consumer-shaped frozen positive-definite zero-trace Duhamel PDE. -/
theorem spdDuh_pde {t : ℝ} (ht : 0 < t)
    (A : Matrix n n ℝ) (hA : A.PosDef)
    (a da : BoundedContinuousFunction ℝ ℝ)
    (ha : ∀ q : ℝ, HasDerivAt (a : ℝ → ℝ) (da q) q)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[ℝ] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[ℝ] Euc n →L[ℝ] F))
    (hu : ∀ x : Euc n, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x : Euc n,
      HasFDerivAt (du : Euc n → Euc n →L[ℝ] F) (d2u x) x)
    (x : Euc n) :
    HasFDerivAt (fun y : Euc n => spdDuh A hA t a u y)
        (spdDuhD1 A hA t a du x) x ∧
      HasFDerivAt (fun y : Euc n => spdDuhD1 A hA t a du y)
        (spdDuhD2 A hA t a d2u x) x ∧
      HasDerivAt (fun q : ℝ => spdDuh A hA q a u x)
        (matrixLap A (spdDuhD2 A hA t a d2u x) + a t • u x) t := by
  refine ⟨spdDuh_space A hA t a u du hu x,
    spdDuhD1_space A hA t a du d2u hdu x, ?_⟩
  let L := spdSqrtEquiv A hA
  have hpull0 : ∀ z : Euc n,
      HasFDerivAt (linPullBcf L u : Euc n → F) (pullJet1 L du z) z :=
    fun z => linPull_fderiv L u du hu z
  have hpull1 : ∀ z : Euc n,
      HasFDerivAt (pullJet1 L du : Euc n → Euc n →L[ℝ] F)
        (pullJet2 L d2u z) z :=
    fun z => pullJet1_fderiv L du d2u hdu z
  have htime := frozenDuh_time ht a da ha (linPullBcf L u)
    (pullJet1 L du) (pullJet2 L d2u) hpull0 hpull1 (L.symm x)
  have hlap := spdDuh_lap A hA t a d2u x
  simpa only [spdDuh, L, linPullBcf_apply,
    ContinuousLinearEquiv.apply_symm_apply, hlap, add_comm] using htime

end SPDEvolution

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
