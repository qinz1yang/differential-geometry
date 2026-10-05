import DifferentialGeometry.Geometry.Connection.HomBundle.Kernel
import DifferentialGeometry.Geometry.Connection.Subbundle
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

open Bundle DifferentialGeometry
open scoped Manifold ContDiff Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

omit [IsContMDiffRiemannianBundle I 1 F V] in
theorem inner_hom_apply_of_eventually_mem_ker
    (cov : CovariantDerivative I F V)
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (hA : ∀ y, (A y : V y →ₗ[ℝ] V y).IsSymmetric)
    (w : Cₛ^∞⟮I; F, V⟯) {x : M} {U : Set M}
    (hU : IsOpen U) (hxU : x ∈ U) (hw : ∀ y ∈ U, A y (w y) = 0)
    (v : TangentSpace I x) :
    inner ℝ
      ((hom I M F V F V cov cov A x v) (w x))
      (w x) = 0 := by
  rw [hom_apply_of_eventually_mem_ker
    cov A w hU hxU hw v, inner_neg_left]
  have hswap :
      inner ℝ (A x (cov w x v)) (w x) =
        inner ℝ (cov w x v) (A x (w x)) := hA x _ _
  rw [hswap]
  rw [hw x hxU, inner_zero_right, neg_zero]

theorem hom_isSymmetric_of_eventually
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    {x : M} (hA : ∀ᶠ y in 𝓝 x, (A y : V y →ₗ[ℝ] V y).IsSymmetric)
    (v : TangentSpace I x) :
    ((hom I M F V F V cov cov A x v :
      V x →L[ℝ] V x) : V x →ₗ[ℝ] V x).IsSymmetric := by
  intro a b
  have hAx := hA.self_of_nhds
  obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞)) x a
  obtain ⟨Z, hZx⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞)) x b
  let AY : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => A y (Y y), ContMDiff.clm_bundle_apply (b := id) A.contMDiff Y.contMDiff⟩
  let AZ : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y => A y (Z y), ContMDiff.clm_bundle_apply (b := id) A.contMDiff Z.contMDiff⟩
  have hfun : (fun y : M => inner ℝ (AY y) (Z y)) =ᶠ[𝓝 x]
      (fun y : M => inner ℝ (Y y) (AZ y)) := hA.mono fun y hy => hy _ _
  have hderiv : d% (fun y : M => inner ℝ (AY y) (Z y)) x (X x) =
      d% (fun y : M => inner ℝ (Y y) (AZ y)) x (X x) := by
    exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (X x))
      (Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hfun)
  have hleft := hcov.mvfderiv_inner_eq (x := x) (fun y => X y)
    AY.mdifferentiableAt Z.mdifferentiableAt
  have hright := hcov.mvfderiv_inner_eq (x := x) (fun y => X y)
    Y.mdifferentiableAt AZ.mdifferentiableAt
  rw [hleft, hright] at hderiv
  rw [← hXx, ← hYx, ← hZx]
  have hDY := hom_apply I M F V F V cov cov A Y x (X x)
  have hDZ := hom_apply I M F V F V cov cov A Z x (X x)
  have hcovY : inner ℝ (A x (cov Y x (X x))) (Z x) =
      inner ℝ (cov Y x (X x)) (A x (Z x)) := hAx _ _
  have hcovZ : inner ℝ (A x (Y x)) (cov Z x (X x)) =
      inner ℝ (Y x) (A x (cov Z x (X x))) := hAx _ _
  change inner ℝ (cov (fun y => A y (Y y)) x (X x)) (Z x) +
      inner ℝ (A x (Y x)) (cov Z x (X x)) =
    inner ℝ (cov Y x (X x)) (A x (Z x)) +
      inner ℝ (Y x) (cov (fun y => A y (Z y)) x (X x)) at hderiv
  rw [hcovZ, ← hcovY] at hderiv
  calc
    inner ℝ ((hom I M F V F V cov cov A x (X x)) (Y x))
        (Z x) = inner ℝ (cov (fun y => A y (Y y)) x (X x) - A x (cov Y x (X x)))
        (Z x) := congrArg (fun q : V x => inner ℝ q (Z x)) hDY
    _ = inner ℝ (Y x) (cov (fun y => A y (Z y)) x (X x) - A x (cov Z x (X x))) := by
      simp only [inner_sub_left, inner_sub_right]
      linear_combination hderiv
    _ = inner ℝ (Y x)
        ((hom I M F V F V cov cov A x (X x)) (Z x)) :=
      congrArg (fun q : V x => inner ℝ (Y x) q) hDZ.symm

theorem hom_isSymmetric
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    (A : Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M => V x →L[ℝ] V x)⟯)
    (hA : ∀ y, (A y : V y →ₗ[ℝ] V y).IsSymmetric)
    (x : M) (v : TangentSpace I x) :
    ((hom I M F V F V cov cov A x v :
      V x →L[ℝ] V x) : V x →ₗ[ℝ] V x).IsSymmetric :=
  hom_isSymmetric_of_eventually cov hcov A
    (Filter.Eventually.of_forall hA) v

theorem hom_isCovariantlyInvariant_selfAdjoint
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible) :
    letI : ∀ x, FiniteDimensional ℝ (V x) :=
      fun x => VectorBundle.finiteDimensional ℝ F V x
    letI : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
    DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily
      (hom I M F V F V cov cov)
      (fun x => _root_.selfAdjoint.submodule ℝ (V x →L[ℝ] V x)) := by
  let : ∀ x, FiniteDimensional ℝ (V x) :=
    fun x => VectorBundle.finiteDimensional ℝ F V x
  let : ∀ x, CompleteSpace (V x) := fun x => FiniteDimensional.complete ℝ (V x)
  intro A U hU hA x hx v
  change IsSelfAdjoint (hom I M F V F V cov cov A x v)
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  apply hom_isSymmetric_of_eventually cov hcov A
  filter_upwards [hU.mem_nhds hx] with y hy
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA y hy)

end CovariantDerivative
