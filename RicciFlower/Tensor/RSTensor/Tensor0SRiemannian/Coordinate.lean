import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Riemannian Metrics on Covariant Tensor Fibers

The metric on `T_x M` induces metrics on all covariant tensor powers.  The
construction is intrinsic on the fiber `Tensor0SSpace s I x`; coordinate
formulas are evaluation theorems for local frames.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem sum_fin_two_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Idx) -> α) :
    (∑ I0 : Fin 2 -> Idx, F I0) =
      ∑ i : Idx, ∑ j : Idx, F (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  rw [Fintype.sum_equiv (finTwoArrowEquiv Idx) F
    (fun p : Idx × Idx => F (fun a : Fin 2 => if a = 0 then p.1 else p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr
    funext a
    fin_cases a <;> simp [finTwoArrowEquiv]

theorem sum_fin_succ_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α] (s : Nat)
    (F : (Fin (s + 1) -> Idx) -> α) :
    (∑ I0 : Fin (s + 1) -> Idx, F I0) =
      ∑ i : Idx, ∑ tail : Fin s -> Idx, F (Fin.cons i tail) := by
  classical
  rw [Fintype.sum_equiv
    (Fin.consEquiv (fun _ : Fin (s + 1) => Idx)).symm
    F (fun p : Idx × (Fin s -> Idx) => F (Fin.cons p.1 p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr 1
    exact (Fin.cons_self_tail I0).symm

theorem sum_fin_one_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 1 -> Idx) -> α) :
    (∑ I0 : Fin 1 -> Idx, F I0) =
      ∑ i : Idx, F (fun _ : Fin 1 => i) := by
  classical
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Idx)
    F (fun i : Idx => F (fun _ : Fin 1 => i))]
  intro I0
  congr 1
  funext a
  simpa [Equiv.funUnique] using congrArg I0 (Subsingleton.elim a (0 : Fin 1))

theorem basis_repr_eq_sum_inv_inner
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Z : TangentSpace I x) (i : Idx) :
    basis.repr Z i =
      ∑ j : Idx, gInv i j * g.inner x Z (basis j) := by
  classical
  let Z' : TangentSpace I x :=
    ∑ i : Idx, (∑ j : Idx, gInv i j * g.inner x Z (basis j)) • basis i
  have hZ : Z = Z' := by
    apply eq_of_inner_basis_eq (I := I) g x basis
    intro l
    calc
      g.inner x Z (basis l)
          = ∑ j : Idx, (if l = j then 1 else 0) *
              g.inner x Z (basis j) := by
            simp
      _ = ∑ j : Idx,
            (∑ i : Idx, g.inner x (basis l) (basis i) * gInv i j) *
              g.inner x Z (basis j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [(hinv l j).2]
      _ = ∑ i : Idx,
            (∑ j : Idx, gInv i j * g.inner x Z (basis j)) *
              g.inner x (basis i) (basis l) := by
            calc
              (∑ j : Idx,
                  (∑ i : Idx, g.inner x (basis l) (basis i) * gInv i j) *
                    g.inner x Z (basis j))
                  = ∑ j : Idx, ∑ i : Idx,
                      (g.inner x (basis l) (basis i) * gInv i j) *
                        g.inner x Z (basis j) := by
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [Finset.sum_mul]
              _ = ∑ i : Idx, ∑ j : Idx,
                      (g.inner x (basis l) (basis i) * gInv i j) *
                        g.inner x Z (basis j) := by
                      rw [Finset.sum_comm]
              _ = ∑ i : Idx,
                    (∑ j : Idx, gInv i j * g.inner x Z (basis j)) *
                      g.inner x (basis i) (basis l) := by
                      apply Finset.sum_congr rfl
                      intro i _
                      rw [Finset.sum_mul]
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [g.symm x (basis l) (basis i)]
                      ring
      _ = g.inner x Z' (basis l) := by
            simp [Z', map_sum]
  calc
    basis.repr Z i = basis.repr Z' i := by rw [hZ]
    _ = ∑ j : Idx, gInv i j * g.inner x Z (basis j) := by
      change
        basis.repr
            (∑ i : Idx, (∑ j : Idx, gInv i j * g.inner x Z (basis j)) • basis i) i =
          ∑ j : Idx, gInv i j * g.inner x Z (basis j)
      rw [map_sum]
      rw [show
          (∑ x_1 : Idx,
              basis.repr
                ((∑ j : Idx, gInv x_1 j * g.inner x Z (basis j)) • basis x_1)) i =
          ∑ x_1 : Idx,
              (basis.repr
                ((∑ j : Idx, gInv x_1 j * g.inner x Z (basis j)) • basis x_1)) i by
        simp]
      simp only [map_smul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hi
        simp at hi

/-- Coordinate trace formula for an endomorphism in a basis with inverse metric
components. -/
theorem linearMap_trace_eq_sum_inv_inner_apply
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : TangentSpace I x →ₗ[Real] TangentSpace I x) :
    LinearMap.trace Real (TangentSpace I x) A =
      ∑ i : Idx, ∑ j : Idx, gInv i j * g.inner x (A (basis i)) (basis j) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace Real basis A]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply]
  exact basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv (A (basis i)) i

/-- Positivity of the trace of a tangent endomorphism from positivity of its
metric quadratic form. -/
theorem linearMap_trace_nonneg_of_metric_inner_apply_self_nonneg
    (g : SmoothMetric I M) (x : M)
    (A : TangentSpace I x →ₗ[Real] TangentSpace I x)
    (hA : ∀ v : TangentSpace I x, 0 <= g.inner x (A v) v) :
    0 <= LinearMap.trace Real (TangentSpace I x) A := by
  classical
  let D := (tangentMetricData (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  rw [LinearMap.trace_eq_sum_inner A
    (stdOrthonormalBasis Real (TangentSpace I x))]
  exact Finset.sum_nonneg fun i _ => by
    have hi := hA (stdOrthonormalBasis Real (TangentSpace I x) i)
    have hinner :
        Inner.inner Real
            (A (stdOrthonormalBasis Real (TangentSpace I x) i))
            (stdOrthonormalBasis Real (TangentSpace I x) i) =
          g.inner x
            (A (stdOrthonormalBasis Real (TangentSpace I x) i))
            (stdOrthonormalBasis Real (TangentSpace I x) i) := by
      change D.inner
          (A (stdOrthonormalBasis Real (TangentSpace I x) i))
          (stdOrthonormalBasis Real (TangentSpace I x) i) =
        g.inner x
          (A (stdOrthonormalBasis Real (TangentSpace I x) i))
          (stdOrthonormalBasis Real (TangentSpace I x) i)
      rfl
    rw [real_inner_comm, hinner]
    exact hi

theorem hom_normSq_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A : TangentSpace I x →ₗ[Real] W) :
    MetricFiberData.homFlatLinear (tangentMetricData (I := I) g x).metric D A A =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (A (basis j)) := by
  change LinearMap.trace Real (TangentSpace I x)
      ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D A).comp A) =
    ∑ i : Idx, ∑ j : Idx,
      gInv i j * D.inner (A (basis i)) (A (basis j))
  classical
  rw [LinearMap.trace_eq_matrix_trace Real basis
    ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D A).comp A)]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply]
  rw [basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change
    g.inner x
        ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D A)
          (A (basis i)))
        (basis j) =
      D.inner (A (basis i)) (A (basis j))
  rw [← TangentMetricData.inner_eq (I := I)
    (tangentMetricData (I := I) g x)
    ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D A)
      (A (basis i)))
    (basis j)]
  exact MetricFiberData.adjoint_inner
    (tangentMetricData (I := I) g x).metric D A (A (basis i)) (basis j)

theorem hom_inner_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A B : TangentSpace I x →ₗ[Real] W) :
    MetricFiberData.homFlatLinear (tangentMetricData (I := I) g x).metric D A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (B (basis j)) := by
  rw [MetricFiberData.homFlatLinear_comm
    (tangentMetricData (I := I) g x).metric D A B]
  change LinearMap.trace Real (TangentSpace I x)
      ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D B).comp A) =
    ∑ i : Idx, ∑ j : Idx,
      gInv i j * D.inner (A (basis i)) (B (basis j))
  classical
  rw [LinearMap.trace_eq_matrix_trace Real basis
    ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D B).comp A)]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply]
  rw [basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change
    g.inner x
        ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D B)
          (A (basis i)))
        (basis j) =
      D.inner (A (basis i)) (B (basis j))
  rw [← TangentMetricData.inner_eq (I := I)
    (tangentMetricData (I := I) g x)
    ((MetricFiberData.adjoint (tangentMetricData (I := I) g x).metric D B)
      (A (basis i)))
    (basis j)]
  exact MetricFiberData.adjoint_inner
    (tangentMetricData (I := I) g x).metric D B (A (basis i)) (basis j)

theorem homCLM_normSq_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    (hTopAdd : IsTopologicalAddGroup W) (hContSMul : ContinuousSMul Real W)
    [FiniteDimensional Real W]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A : TangentSpace I x →L[Real] W) :
    (@MetricFiberData.homCLM
      (TangentSpace I x) W
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hTopAdd hContSMul inferInstance
      (tangentMetricData (I := I) g x).metric D).flat A A =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (A (basis j)) := by
  exact hom_normSq_eq_basis (I := I) g x basis gInv hinv D A.toLinearMap

theorem homCLM_inner_eq_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {W : Type*} [AddCommGroup W] [Module Real W] [TopologicalSpace W]
    (hTopAdd : IsTopologicalAddGroup W) (hContSMul : ContinuousSMul Real W)
    [FiniteDimensional Real W]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData W)
    (A B : TangentSpace I x →L[Real] W) :
    (@MetricFiberData.homCLM
      (TangentSpace I x) W
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hTopAdd hContSMul inferInstance
      (tangentMetricData (I := I) g x).metric D).flat A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * D.inner (A (basis i)) (B (basis j)) := by
  exact hom_inner_eq_basis (I := I) g x basis gInv hinv D A.toLinearMap B.toLinearMap

theorem tensor0S_curry_one_apply
    {x : M} (A : Tensor0SSpace 2 I x)
    (X Y : TangentSpace I x) :
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A X)
        (fun _ : Fin 1 => Y) =
      A (fun a : Fin 2 => if a = 0 then X else Y) := by
  change
    (((continuousMultilinearCurryLeftEquiv Real
        (fun _ : Fin (1 + 1) => E) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (1 + 1) x) A)
        X)
        (fun _ : Fin 1 => Y)) =
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (1 + 1) x) A)
        (fun a : Fin 2 => if a = 0 then X else Y)
  rw [continuousMultilinearCurryLeftEquiv_apply]
  congr 1
  funext a
  fin_cases a <;> simp [Fin.cons_zero]

theorem tensor0S_curry_apply_cons
    {x : M} (s : Nat) (A : Tensor0SSpace (s + 1) I x)
    (X : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A X) tail =
      A (Fin.cons X tail) := by
  change
    (((continuousMultilinearCurryLeftEquiv Real
        (fun _ : Fin (s + 1) => E) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x) A)
        X)
        tail) =
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x) A)
        (Fin.cons X tail)
  rw [continuousMultilinearCurryLeftEquiv_apply]

/-- Direct coordinate squared-norm formula for `(0,2)` covariant tensors.

This is the checked bridge used by the Bochner layer while the fully general
`inner0S_eq_coord` induction remains open. -/
theorem normSq0S_two_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace 2 I x) :
    normSq0S (I := I) g x 2 A =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
  classical
  have hTopAdd1 : IsTopologicalAddGroup (Tensor0SSpace 1 I x) :=
    Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
      (𝕜 := Real) (F := E) (E := TangentSpace I) 1 x
  haveI : IsTopologicalAddGroup (Tensor0SSpace 1 I x) := hTopAdd1
  have hContSMul1 : ContinuousSMul Real (Tensor0SSpace 1 I x) :=
    Bundle.continuousMultilinearMap.instContinuousSMul
      (𝕜 := Real) (F := E) (E := TangentSpace I) 1 x
  haveI : ContinuousSMul Real (Tensor0SSpace 1 I x) := hContSMul1
  have hContAdd1 : ContinuousAdd (Tensor0SSpace 1 I x) :=
    IsTopologicalAddGroup.toContinuousAdd
  haveI : ContinuousAdd (Tensor0SSpace 1 I x) := hContAdd1
  haveI : ContinuousConstSMul Real (Tensor0SSpace 1 I x) := inferInstance
  letI : TopologicalSpace (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.topologicalSpace
      Real Real inferInstance inferInstance (RingHom.id Real)
      (TangentSpace I x) (Tensor0SSpace 1 I x)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hTopAdd1
  letI : AddCommGroup (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.addCommGroup
      Real inferInstance Real inferInstance
      (TangentSpace I x) inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance
      inferInstance inferInstance (RingHom.id Real) hTopAdd1
  letI : Module Real (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.module
      Real Real Real inferInstance inferInstance inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RingHom.id Real) hContAdd1
  letI : FiniteDimensional Real (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    (@LinearMap.toContinuousLinearMap
      Real inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance inferInstance hTopAdd1 hContSMul1
      inferInstance inferInstance inferInstance).finiteDimensional
  unfold normSq0S inner0S MetricFiberData.inner
  change
    (tensor0SMetricStep (I := I) g x 1 (cotangentMetricData (I := I) g x)).flat A A =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l)
  unfold tensor0SMetricStep MetricFiberData.pullback MetricFiberData.homCLM
    MetricFiberData.hom
  change
    MetricFiberData.homFlatLinear
      (tangentMetricData (I := I) g x).metric
      (cotangentMetricData (I := I) g x)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l)
  rw [hom_normSq_eq_basis (I := I) g x basis gInv hinv
    (cotangentMetricData (I := I) g x)
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)]
  calc
    (∑ i : Idx, ∑ k : Idx,
        gInv i k *
          (cotangentMetricData (I := I) g x).inner
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A) (basis k)))
        = ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx,
            gInv i k *
              (gInv j l *
                A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
                  A (fun a : Fin 2 => if a = 0 then basis k else basis l)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          rw [cotangentMetricData_inner_eq_coord (I := I) g x basis gInv hinv]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          rw [cotangentToDual_apply, cotangentToDual_apply]
          rw [tensor0S_curry_one_apply, tensor0S_curry_one_apply]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            A (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          ring

/-- Direct coordinate inner-product formula for `(0,2)` covariant tensors.

This is the bilinear analogue of `normSq0S_two_eq_coord`; it avoids the
currently open general tensor-power coordinate theorem. -/
theorem inner0S_two_eq_coord_direct
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 2 A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
  classical
  have hTopAdd1 : IsTopologicalAddGroup (Tensor0SSpace 1 I x) :=
    Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
      (𝕜 := Real) (F := E) (E := TangentSpace I) 1 x
  haveI : IsTopologicalAddGroup (Tensor0SSpace 1 I x) := hTopAdd1
  have hContSMul1 : ContinuousSMul Real (Tensor0SSpace 1 I x) :=
    Bundle.continuousMultilinearMap.instContinuousSMul
      (𝕜 := Real) (F := E) (E := TangentSpace I) 1 x
  haveI : ContinuousSMul Real (Tensor0SSpace 1 I x) := hContSMul1
  have hContAdd1 : ContinuousAdd (Tensor0SSpace 1 I x) :=
    IsTopologicalAddGroup.toContinuousAdd
  haveI : ContinuousAdd (Tensor0SSpace 1 I x) := hContAdd1
  haveI : ContinuousConstSMul Real (Tensor0SSpace 1 I x) := inferInstance
  letI : TopologicalSpace (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.topologicalSpace
      Real Real inferInstance inferInstance (RingHom.id Real)
      (TangentSpace I x) (Tensor0SSpace 1 I x)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hTopAdd1
  letI : AddCommGroup (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.addCommGroup
      Real inferInstance Real inferInstance
      (TangentSpace I x) inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance
      inferInstance inferInstance (RingHom.id Real) hTopAdd1
  letI : Module Real (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    @ContinuousLinearMap.module
      Real Real Real inferInstance inferInstance inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RingHom.id Real) hContAdd1
  letI : FiniteDimensional Real (TangentSpace I x →L[Real] Tensor0SSpace 1 I x) :=
    (@LinearMap.toContinuousLinearMap
      Real inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance inferInstance inferInstance
      (Tensor0SSpace 1 I x) inferInstance inferInstance inferInstance hTopAdd1 hContSMul1
      inferInstance inferInstance inferInstance).finiteDimensional
  unfold inner0S MetricFiberData.inner
  change
    (tensor0SMetricStep (I := I) g x 1 (cotangentMetricData (I := I) g x)).flat A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l)
  unfold tensor0SMetricStep MetricFiberData.pullback MetricFiberData.homCLM
    MetricFiberData.hom
  change
    MetricFiberData.homFlatLinear
      (tangentMetricData (I := I) g x).metric
      (cotangentMetricData (I := I) g x)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x B).toLinearMap) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l)
  rw [hom_inner_eq_basis (I := I) g x basis gInv hinv
    (cotangentMetricData (I := I) g x)
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A).toLinearMap)
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x B).toLinearMap)]
  calc
    (∑ i : Idx, ∑ k : Idx,
        gInv i k *
          (cotangentMetricData (I := I) g x).inner
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 1 x B) (basis k)))
        = ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx,
            gInv i k *
              (gInv j l *
                A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
                  B (fun a : Fin 2 => if a = 0 then basis k else basis l)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          rw [cotangentMetricData_inner_eq_coord (I := I) g x basis gInv hinv]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          rw [cotangentToDual_apply, cotangentToDual_apply]
          rw [tensor0S_curry_one_apply, tensor0S_curry_one_apply]
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          ring

theorem inner0S_zero_eq
    (g : SmoothMetric I M) (x : M)
    (A B : Tensor0SSpace 0 I x) :
    inner0S (I := I) g x 0 A B = A Fin.elim0 * B Fin.elim0 := by
  unfold inner0S tensor0SMetricData scalarMetricData MetricFiberData.inner
    MetricFiberData.pullback MetricFiberData.real MetricFiberData.ofFlat
    MetricFiberData.realFlatLinear
  change
    ((continuousMultilinearCurryFin0 Real (TangentSpace I x) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 0 x) A)) *
      ((continuousMultilinearCurryFin0 Real (TangentSpace I x) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 0 x) B)) =
      A Fin.elim0 * B Fin.elim0
  simp [tensor0SSpace_continuousLinearEquiv]
  congr

theorem coordInner0S_zero_eq
    {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace 0 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 0 gInv A B basis =
      A Fin.elim0 * B Fin.elim0 := by
  classical
  unfold coordInner0S tensor0SComponent
  simp only [Finset.univ_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
    Finset.sum_singleton]
  congr <;> funext a <;> exact Fin.elim0 a

theorem coordInner0S_one_eq
    {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx -> Idx -> Real)
    (α β : Tensor0SSpace 1 I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 1 gInv α β basis =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * cotangentToDual (I := I) α (basis i) *
          cotangentToDual (I := I) β (basis j) := by
  classical
  unfold coordInner0S tensor0SComponent
  rw [sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro j _
  simp [cotangentToDual_apply]

theorem tensor0SMetricStep_inner_eq_coordStep
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (D : MetricFiberData (Tensor0SSpace s I x))
    (A B : Tensor0SSpace (s + 1) I x) :
    (tensor0SMetricStep (I := I) g x s D).inner A B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          D.inner
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j)) := by
  classical
  have hTopAdd0 : IsTopologicalAddGroup (Tensor0SSpace s I x) :=
    Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
      (𝕜 := Real) (F := E) (E := TangentSpace I) s x
  haveI : IsTopologicalAddGroup (Tensor0SSpace s I x) := hTopAdd0
  have hContSMul0 : ContinuousSMul Real (Tensor0SSpace s I x) :=
    Bundle.continuousMultilinearMap.instContinuousSMul
      (𝕜 := Real) (F := E) (E := TangentSpace I) s x
  haveI : ContinuousSMul Real (Tensor0SSpace s I x) := hContSMul0
  have hContAdd0 : ContinuousAdd (Tensor0SSpace s I x) :=
    IsTopologicalAddGroup.toContinuousAdd
  haveI : ContinuousAdd (Tensor0SSpace s I x) := hContAdd0
  haveI : ContinuousConstSMul Real (Tensor0SSpace s I x) := inferInstance
  letI : TopologicalSpace (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.topologicalSpace
      Real Real inferInstance inferInstance (RingHom.id Real)
      (TangentSpace I x) (Tensor0SSpace s I x)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hTopAdd0
  letI : AddCommGroup (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.addCommGroup
      Real inferInstance Real inferInstance
      (TangentSpace I x) inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance
      inferInstance inferInstance (RingHom.id Real) hTopAdd0
  letI : Module Real (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    @ContinuousLinearMap.module
      Real Real Real inferInstance inferInstance inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (RingHom.id Real) hContAdd0
  letI : FiniteDimensional Real (TangentSpace I x →L[Real] Tensor0SSpace s I x) :=
    (@LinearMap.toContinuousLinearMap
      Real inferInstance
      (TangentSpace I x) inferInstance inferInstance inferInstance inferInstance inferInstance
      (Tensor0SSpace s I x) inferInstance inferInstance inferInstance hTopAdd0 hContSMul0
      inferInstance inferInstance inferInstance).finiteDimensional
  unfold MetricFiberData.inner tensor0SMetricStep MetricFiberData.pullback
    MetricFiberData.homCLM MetricFiberData.hom
  change
    MetricFiberData.homFlatLinear
      (tangentMetricData (I := I) g x).metric D
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A).toLinearMap)
      ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B).toLinearMap) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          D.inner
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
  rw [hom_inner_eq_basis (I := I) g x basis gInv hinv D
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A).toLinearMap)
    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B).toLinearMap)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rfl

theorem coordInner0S_succ_summand_eq
    {Idx : Type*}  {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace (s + 1) I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i j : Idx) (tailI tailJ : Fin s -> Idx) :
    ((∏ a : Fin (s + 1),
        gInv (((Fin.cons i tailI : Fin (s + 1) -> Idx) a))
          (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) *
        A (fun a : Fin (s + 1) =>
          basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)))) *
      B (fun a : Fin (s + 1) =>
        basis (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) =
      (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
          ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            (fun a : Fin s => basis (tailI a))) *
        ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
          (fun a : Fin s => basis (tailJ a)) := by
  rw [Fin.prod_univ_succ]
  rw [tensor0S_curry_apply_cons, tensor0S_curry_apply_cons]
  have hA :
      (fun a : Fin (s + 1) =>
          basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a))) =
        Fin.cons (basis i) (fun a : Fin s => basis (tailI a)) := by
    funext a
    cases a using Fin.cases <;> simp
  have hB :
      (fun a : Fin (s + 1) =>
          basis (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) =
        Fin.cons (basis j) (fun a : Fin s => basis (tailJ a)) := by
    funext a
    cases a using Fin.cases <;> simp
  rw [hA, hB]
  simp [Fin.cons_zero, Fin.cons_succ]

theorem coordInner0S_succ_eq
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace (s + 1) I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) (s + 1) gInv A B basis =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          coordInner0S (I := I) (x := x) s gInv
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
            basis := by
  classical
  unfold coordInner0S tensor0SComponent
  rw [sum_fin_succ_fun s]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ tailI : Fin s -> Idx,
        ∑ J0 : Fin (s + 1) -> Idx,
          ((∏ a : Fin (s + 1),
              gInv (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)) (J0 a)) *
              A (fun a : Fin (s + 1) =>
                basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)))) *
            B (fun a : Fin (s + 1) => basis (J0 a)))
        =
        ∑ tailI : Fin s -> Idx, ∑ j : Idx, ∑ tailJ : Fin s -> Idx,
          ((∏ a : Fin (s + 1),
              gInv (((Fin.cons i tailI : Fin (s + 1) -> Idx) a))
                (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) *
              A (fun a : Fin (s + 1) =>
                basis (((Fin.cons i tailI : Fin (s + 1) -> Idx) a)))) *
            B (fun a : Fin (s + 1) =>
              basis (((Fin.cons j tailJ : Fin (s + 1) -> Idx) a))) := by
          apply Finset.sum_congr rfl
          intro tailI _
          rw [sum_fin_succ_fun s]
    _ =
        ∑ tailI : Fin s -> Idx, ∑ j : Idx, ∑ tailJ : Fin s -> Idx,
          (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
              ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
                (fun a : Fin s => basis (tailI a))) *
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
              (fun a : Fin s => basis (tailJ a)) := by
          apply Finset.sum_congr rfl
          intro tailI _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro tailJ _
          exact coordInner0S_succ_summand_eq (I := I) s gInv A B basis i j tailI tailJ
    _ =
        ∑ j : Idx, ∑ tailI : Fin s -> Idx, ∑ tailJ : Fin s -> Idx,
          (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
              ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
                (fun a : Fin s => basis (tailI a))) *
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
              (fun a : Fin s => basis (tailJ a)) := by
          rw [Finset.sum_comm]
    _ =
        ∑ j : Idx,
          gInv i j *
            ∑ tailI : Fin s -> Idx, ∑ tailJ : Fin s -> Idx,
              (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
                ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A) (basis i))
                  (fun a : Fin s => basis (tailI a)) *
                  ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x B) (basis j))
                    (fun a : Fin s => basis (tailJ a)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tailI _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tailJ _
          ring

theorem coordInner0S_smul_smul
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (c d : Real) :
    coordInner0S (I := I) (x := x) s gInv (c • A) (d • B) basis =
      c * d * coordInner0S (I := I) (x := x) s gInv A B basis := by
  classical
  unfold coordInner0S tensor0SComponent
  simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem coordInner0S_smul_right
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (c : Real) :
    coordInner0S (I := I) (x := x) s gInv A (c • B) basis =
      c * coordInner0S (I := I) (x := x) s gInv A B basis := by
  classical
  unfold coordInner0S tensor0SComponent
  simp [Finset.mul_sum, mul_left_comm, mul_comm]

theorem coordInner0S_smul_left
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (c : Real) :
    coordInner0S (I := I) (x := x) s gInv (c • A) B basis =
      c * coordInner0S (I := I) (x := x) s gInv A B basis := by
  classical
  unfold coordInner0S tensor0SComponent
  simp [Finset.mul_sum, mul_left_comm, mul_comm]

theorem coordInner0S_zero_left
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s gInv 0 B basis = 0 := by
  classical
  unfold coordInner0S tensor0SComponent
  simp

theorem coordInner0S_add_left
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A B C : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s gInv (A + B) C basis =
      coordInner0S (I := I) (x := x) s gInv A C basis +
        coordInner0S (I := I) (x := x) s gInv B C basis := by
  classical
  unfold coordInner0S tensor0SComponent
  simp [Finset.sum_add_distrib, mul_add, mul_left_comm, mul_comm]

theorem coordInner0S_sum_left
    {Idx ι : Type*} [Fintype Idx] [Fintype ι] {x : M} (s : Nat)
    (gInv : Idx -> Idx -> Real)
    (A : ι -> Tensor0SSpace s I x) (B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (c : ι -> Real) :
    coordInner0S (I := I) (x := x) s gInv
        (∑ i : ι, c i • A i) B basis =
      ∑ i : ι, c i *
        coordInner0S (I := I) (x := x) s gInv (A i) B basis := by
  classical
  simpa using
    (show
      coordInner0S (I := I) (x := x) s gInv
          ((Finset.univ : Finset ι).sum fun i : ι => c i • A i) B basis =
        (Finset.univ : Finset ι).sum fun i : ι =>
          c i * coordInner0S (I := I) (x := x) s gInv (A i) B basis from by
        refine Finset.induction_on (Finset.univ : Finset ι) ?base ?step
        · exact coordInner0S_zero_left (I := I) s gInv B basis
        · intro a S ha hS
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          change
            coordInner0S (I := I) (x := x) s gInv
                ((c a • A a) + (∑ i ∈ S, c i • A i)) B basis =
              c a * coordInner0S (I := I) (x := x) s gInv (A a) B basis +
                ∑ i ∈ S, c i *
                  coordInner0S (I := I) (x := x) s gInv (A i) B basis
          rw [coordInner0S_add_left (I := I) s gInv (c a • A a)
            (∑ i ∈ S, c i • A i) B basis]
          rw [coordInner0S_smul_left (I := I) s gInv (A a) B basis]
          rw [hS])

theorem tensor0S_curry_product_one_two
    {x : M}
    (α : Tensor0SSpace 1 I x) (A : Tensor0SSpace 2 I x)
    (X : TangentSpace I x) :
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
        (Bundle.continuousMultilinearMap.product_fun
          (s := 1) (q := 2) α A) X) =
      α (fun _ : Fin 1 => X) • A := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [tensor0S_curry_apply_cons]
  rw [Bundle.continuousMultilinearMap.product_fun_apply]
  have hhead :
      (Fin.cons X v ∘ Fin.castAdd 2) = fun _ : Fin 1 => X := by
    funext a
    fin_cases a
    rfl
  have htail :
      (Fin.cons X v ∘ Fin.natAdd 1) = v := by
    funext a
    fin_cases a <;> rfl
  rw [hhead, htail]
  rfl

/-- Coordinate formula for the covariant tensor metric in a basis.

This is the general tensor-power contraction theorem. The `s = 1` theorem is
proved in `CotangentRiemannian`; the `s = 2` form used by Bochner is exposed
below. The remaining proof is finite-dimensional tensor-basis induction. -/
theorem inner0S_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B =
      coordInner0S (I := I) (x := x) s gInv A B basis := by
  induction s with
  | zero =>
      rw [inner0S_zero_eq (I := I) g x A B,
        coordInner0S_zero_eq (I := I) gInv A B basis]
  | succ s ih =>
      cases s with
      | zero =>
          rw [inner0S_one_eq_cotangent (I := I) g x A B,
            cotangentInner_eq_coord (I := I) g x basis gInv hinv A B,
            coordInner0S_one_eq (I := I) gInv A B basis]
      | succ s =>
          rw [coordInner0S_succ_eq (I := I) (s + 1) gInv A B basis]
          unfold inner0S
          change
            (tensor0SMetricStep (I := I) g x (s + 1)
              (tensor0SMetricData (I := I) g x (s + 1))).inner A B =
              ∑ i : Idx, ∑ j : Idx,
                gInv i j *
                  coordInner0S (I := I) (x := x) (s + 1) gInv
                    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x A)
                      (basis i))
                    ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x B)
                      (basis j))
                    basis
          rw [tensor0SMetricStep_inner_eq_coordStep (I := I) g x (s + 1)
            basis gInv hinv (tensor0SMetricData (I := I) g x (s + 1)) A B]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          change
            gInv i j *
                inner0S (I := I) g x (s + 1)
                  (((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x A)
                    (basis i)))
                  (((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x B)
                    (basis j))) =
              gInv i j *
                coordInner0S (I := I) (x := x) (s + 1) gInv
                  (((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x A)
                    (basis i)))
                  (((tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x B)
                    (basis j)))
                  basis
          rw [ih]

/-- Coordinate formula for the covariant tensor squared norm. -/
theorem normSq0S_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A =
      coordInner0S (I := I) (x := x) s gInv A A basis := by
  rw [normSq0S_eq_inner, inner0S_eq_coord (I := I) g x s basis gInv hinv]

/-- The `(0,2)` coordinate formula in the nested-index form used by Ricci
calculations. -/
theorem inner0S_two_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A B : Tensor0SSpace 2 I x) :
    inner0S (I := I) g x 2 A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (fun a : Fin 2 => if a = 0 then basis i else basis j) *
            B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
  exact inner0S_two_eq_coord_direct (I := I) g x basis gInv hinv A B

end

end Tensor0SBundle
