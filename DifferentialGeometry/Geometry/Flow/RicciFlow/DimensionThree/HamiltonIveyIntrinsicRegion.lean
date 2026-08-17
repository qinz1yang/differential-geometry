import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIveyRegionReaction
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]

private lemma sum_fin3 {α : Type*} [AddCommMonoid α] (f : Fin 3 → α) :
    (∑ k : Fin 3, f k) = f 0 + f 1 + f 2 := by
  classical
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp [add_assoc]

private def slots4Equiv : (Fin 4 → Fin 3) ≃ ((((Fin 3 × Fin 3) × Fin 3) × Fin 3)) where
  toFun f := (((f 0, f 1), f 2), f 3)
  invFun p := slots4 p.1.1.1 p.1.1.2 p.1.2 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [slots4]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [slots4]

private lemma sum_tuple_eq_sum_slots
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 4 → Fin 3) → α) :
    (∑ I0 : Fin 4 → Fin 3, F I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        F (slots4 i j k l) := by
  classical
  rw [Fintype.sum_equiv slots4Equiv F
    (fun p : ((((Fin 3 × Fin 3) × Fin 3) × Fin 3)) =>
      F (slots4 p.1.1.1 p.1.1.2 p.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro I0
    have hslot :
        slots4 (slots4Equiv I0).1.1.1 (slots4Equiv I0).1.1.2
            (slots4Equiv I0).1.2 (slots4Equiv I0).2 = I0 := by
      change slots4Equiv.symm (slots4Equiv I0) = I0
      exact slots4Equiv.left_inv I0
    rw [hslot]

private lemma sum_four_by_pairs
    (X : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hij : ∀ i j k l : Fin 3, X i j k l = X j i k l)
    (hkl : ∀ i j k l : Fin 3, X i j k l = X i j l k)
    (hdi : ∀ i _j k l : Fin 3, X i i k l = 0)
    (hdj : ∀ i j k _l : Fin 3, X i j k k = 0) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, X i j k l) =
      4 * (∑ p : Fin 3, ∑ q : Fin 3,
        X (bivectorIndex3 p).1 (bivectorIndex3 p).2
          (bivectorIndex3 q).2 (bivectorIndex3 q).1) := by
  classical
  have hkl2 : ∀ i j : Fin 3,
      (∑ k : Fin 3, ∑ l : Fin 3, X i j k l) =
        2 * (∑ q : Fin 3, X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2) := by
    intro i j
    rw [sum_fin3 (fun k : Fin 3 => ∑ l : Fin 3, X i j k l)]
    rw [sum_fin3 (fun l : Fin 3 => X i j 0 l), sum_fin3 (fun l : Fin 3 => X i j 1 l),
      sum_fin3 (fun l : Fin 3 => X i j 2 l)]
    rw [sum_fin3 (fun q : Fin 3 => X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2)]
    rw [hkl i j 1 0, hkl i j 2 0, hkl i j 2 1, hdj i j 0 0, hdj i j 1 1, hdj i j 2 2]
    simp [bivectorIndex3]
    ring
  have hij2 : ∀ q : Fin 3,
      (∑ i : Fin 3, ∑ j : Fin 3, X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2) =
        2 * (∑ p : Fin 3, X (bivectorIndex3 p).1 (bivectorIndex3 p).2
          (bivectorIndex3 q).1 (bivectorIndex3 q).2) := by
    intro q
    rw [sum_fin3 (fun i : Fin 3 => ∑ j : Fin 3, X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2)]
    rw [sum_fin3 (fun j : Fin 3 => X 0 j (bivectorIndex3 q).1 (bivectorIndex3 q).2),
      sum_fin3 (fun j : Fin 3 => X 1 j (bivectorIndex3 q).1 (bivectorIndex3 q).2),
      sum_fin3 (fun j : Fin 3 => X 2 j (bivectorIndex3 q).1 (bivectorIndex3 q).2)]
    rw [sum_fin3 (fun p : Fin 3 => X (bivectorIndex3 p).1 (bivectorIndex3 p).2
      (bivectorIndex3 q).1 (bivectorIndex3 q).2)]
    rw [hij 1 0 (bivectorIndex3 q).1 (bivectorIndex3 q).2,
      hij 2 0 (bivectorIndex3 q).1 (bivectorIndex3 q).2,
      hij 2 1 (bivectorIndex3 q).1 (bivectorIndex3 q).2,
      hdi 0 0 (bivectorIndex3 q).1 (bivectorIndex3 q).2,
      hdi 1 1 (bivectorIndex3 q).1 (bivectorIndex3 q).2,
      hdi 2 2 (bivectorIndex3 q).1 (bivectorIndex3 q).2]
    simp [bivectorIndex3]
    ring
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, X i j k l)
        = ∑ i : Fin 3, ∑ j : Fin 3,
            (2 * (∑ q : Fin 3, X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact hkl2 i j
    _ = 2 * (∑ i : Fin 3, ∑ j : Fin 3, ∑ q : Fin 3,
          X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2) := by
          calc
            (∑ i : Fin 3, ∑ j : Fin 3, 2 * (∑ q : Fin 3, X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2))
                = ∑ i : Fin 3, 2 * (∑ j : Fin 3, ∑ q : Fin 3,
                    X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  rw [← Finset.mul_sum]
            _ = 2 * (∑ i : Fin 3, ∑ j : Fin 3, ∑ q : Fin 3,
                  X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2) := by
                  rw [← Finset.mul_sum]
    _ = 2 * (∑ q : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
          X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2) := by
          have h1 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ q : Fin 3,
              X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2) =
              ∑ i : Fin 3, ∑ q : Fin 3, ∑ j : Fin 3,
                X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using (Finset.sum_comm :
              (∑ j : Fin 3, ∑ q : Fin 3, X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2) =
                ∑ q : Fin 3, ∑ j : Fin 3, X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2)
          have h2 : (∑ i : Fin 3, ∑ q : Fin 3, ∑ j : Fin 3,
              X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2) =
              ∑ q : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
                X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2 := by
            simpa using (Finset.sum_comm
              (s := (Finset.univ : Finset (Fin 3))) (t := (Finset.univ : Finset (Fin 3)))
              (f := fun i q => ∑ j : Fin 3, X i j (bivectorIndex3 q).1 (bivectorIndex3 q).2))
          rw [h1, h2]
    _ = 2 * (∑ q : Fin 3, 2 * (∑ p : Fin 3,
          X (bivectorIndex3 p).1 (bivectorIndex3 p).2
            (bivectorIndex3 q).1 (bivectorIndex3 q).2)) := by
          refine congrArg (fun z : ℝ => 2 * z) ?_
          refine Finset.sum_congr rfl ?_
          intro q hq
          exact hij2 q
    _ = 4 * (∑ p : Fin 3, ∑ q : Fin 3,
          X (bivectorIndex3 p).1 (bivectorIndex3 p).2
            (bivectorIndex3 q).1 (bivectorIndex3 q).2) := by
          calc
            2 * (∑ q : Fin 3, 2 * (∑ p : Fin 3,
                X (bivectorIndex3 p).1 (bivectorIndex3 p).2
                  (bivectorIndex3 q).1 (bivectorIndex3 q).2))
                = ∑ q : Fin 3, 2 * (2 * (∑ p : Fin 3,
                    X (bivectorIndex3 p).1 (bivectorIndex3 p).2
                      (bivectorIndex3 q).1 (bivectorIndex3 q).2)) := by
                  rw [Finset.mul_sum]
            _ = ∑ q : Fin 3, 4 * (∑ p : Fin 3,
                  X (bivectorIndex3 p).1 (bivectorIndex3 p).2
                    (bivectorIndex3 q).1 (bivectorIndex3 q).2) := by
                  refine Finset.sum_congr rfl ?_
                  intro q hq
                  ring
            _ = ∑ q : Fin 3, ∑ p : Fin 3, 4 * X (bivectorIndex3 p).1 (bivectorIndex3 p).2
                  (bivectorIndex3 q).1 (bivectorIndex3 q).2 := by
                  refine Finset.sum_congr rfl ?_
                  intro q hq
                  rw [Finset.mul_sum]
            _ = 4 * (∑ p : Fin 3, ∑ q : Fin 3,
                  X (bivectorIndex3 p).1 (bivectorIndex3 p).2
                    (bivectorIndex3 q).1 (bivectorIndex3 q).2) := by
                  calc
                    ∑ q : Fin 3, ∑ p : Fin 3, 4 * X (bivectorIndex3 p).1 (bivectorIndex3 p).2
                          (bivectorIndex3 q).1 (bivectorIndex3 q).2
                        = ∑ q : Fin 3, 4 * (∑ p : Fin 3,
                            X (bivectorIndex3 p).1 (bivectorIndex3 p).2
                              (bivectorIndex3 q).1 (bivectorIndex3 q).2) := by
                          refine Finset.sum_congr rfl ?_
                          intro q hq
                          rw [Finset.mul_sum]
                    _ = 4 * (∑ q : Fin 3, ∑ p : Fin 3,
                          X (bivectorIndex3 p).1 (bivectorIndex3 p).2
                            (bivectorIndex3 q).1 (bivectorIndex3 q).2) := by
                          rw [← Finset.mul_sum]
                    _ = 4 * (∑ p : Fin 3, ∑ q : Fin 3,
                          X (bivectorIndex3 p).1 (bivectorIndex3 p).2
                            (bivectorIndex3 q).1 (bivectorIndex3 q).2) := by
                          rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3)))
                            (t := (Finset.univ : Finset (Fin 3)))
                            (f := fun q p => X (bivectorIndex3 p).1 (bivectorIndex3 p).2
                              (bivectorIndex3 q).1 (bivectorIndex3 q).2)]
    _ = 4 * (∑ p : Fin 3, ∑ q : Fin 3,
          X (bivectorIndex3 p).1 (bivectorIndex3 p).2
            (bivectorIndex3 q).2 (bivectorIndex3 q).1) := by
          refine congrArg (fun z : ℝ => 4 * z) ?_
          refine Finset.sum_congr rfl ?_
          intro p hp
          refine Finset.sum_congr rfl ?_
          intro q hq
          exact hkl (bivectorIndex3 p).1 (bivectorIndex3 p).2
            (bivectorIndex3 q).1 (bivectorIndex3 q).2

omit [IsManifold I 1 M] [IsManifold I 2 M] in
theorem inner0S_algebraic_eq_four_mul_operatorInner
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    inner0S (I := I) g x 4 (A : Tensor04At (I := I) (M := M) x)
        (B : Tensor04At (I := I) (M := M) x) =
      4 * (∑ p : Fin 3, ∑ q : Fin 3,
        curvatureOperatorMatrixAt (I := I) x basis A p q *
          curvatureOperatorMatrixAt (I := I) x basis B p q) := by
  classical
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Fin 3)) := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal (I := I) g basis horth
  have hcoord := inner0S_eq_coord (I := I) g x 4 basis
    (identityInvMetric (Idx := Fin 3)) hinv
    (A : Tensor04At (I := I) (M := M) x) (B : Tensor04At (I := I) (M := M) x)
  rw [hcoord]
  change (∑ I0 : Fin 4 → Fin 3, ∑ J0 : Fin 4 → Fin 3,
      (∏ a : Fin 4, identityInvMetric (Idx := Fin 3) (I0 a) (J0 a)) *
        tensor0SComponent (I := I) (A : Tensor04At (I := I) (M := M) x)
          (fun i : Fin 3 => basis i) I0 *
        tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
          (fun i : Fin 3 => basis i) J0) =
    4 * (∑ p : Fin 3, ∑ q : Fin 3,
      tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
        (basis (bivectorIndex3 p).1) (basis (bivectorIndex3 p).2)
        (basis (bivectorIndex3 q).2) (basis (bivectorIndex3 q).1) *
      tensor04StdAt (I := I) (M := M) (B : Tensor04At (I := I) (M := M) x)
        (basis (bivectorIndex3 p).1) (basis (bivectorIndex3 p).2)
        (basis (bivectorIndex3 q).2) (basis (bivectorIndex3 q).1))
  have hcollapse : (∑ I0 : Fin 4 → Fin 3, ∑ J0 : Fin 4 → Fin 3,
      (∏ a : Fin 4, identityInvMetric (Idx := Fin 3) (I0 a) (J0 a)) *
        tensor0SComponent (I := I) (A : Tensor04At (I := I) (M := M) x)
          (fun i : Fin 3 => basis i) I0 *
        tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
          (fun i : Fin 3 => basis i) J0) =
      ∑ I0 : Fin 4 → Fin 3,
        tensor0SComponent (I := I) (A : Tensor04At (I := I) (M := M) x)
            (fun i : Fin 3 => basis i) I0 *
          tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
            (fun i : Fin 3 => basis i) I0 := by
    refine Finset.sum_congr rfl ?_
    intro I0 hI0
    have hJ : (∑ J0 : Fin 4 → Fin 3,
        (∏ a : Fin 4, identityInvMetric (Idx := Fin 3) (I0 a) (J0 a)) *
          tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
            (fun i : Fin 3 => basis i) J0) =
        tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
          (fun i : Fin 3 => basis i) I0 := by
      have hprod : ∀ J0 : Fin 4 → Fin 3,
          (∏ a : Fin 4, identityInvMetric (Idx := Fin 3) (I0 a) (J0 a)) =
            if J0 = I0 then (1 : Real) else 0 := by
        intro J0
        by_cases h : J0 = I0
        · subst J0
          simp
        · have hne : ∃ a : Fin 4, J0 a ≠ I0 a := by
            by_contra hne
            exact h (by
              funext a
              by_contra ha
              exact hne ⟨a, ha⟩)
          rcases hne with ⟨a, ha⟩
          have hzero : (∏ b : Fin 4, identityInvMetric (Idx := Fin 3) (I0 b) (J0 b)) = 0 := by
            exact Finset.prod_eq_zero (Finset.mem_univ a) (by
              rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (Ne.symm ha)])
          simp [h, hzero]
      calc
        (∑ J0 : Fin 4 → Fin 3,
            (∏ a : Fin 4, identityInvMetric (Idx := Fin 3) (I0 a) (J0 a)) *
              tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
                (fun i : Fin 3 => basis i) J0)
            = (∑ J0 : Fin 4 → Fin 3,
                (if J0 = I0 then (1 : Real) else 0) *
                  tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
                    (fun i : Fin 3 => basis i) J0) := by
              refine Finset.sum_congr rfl ?_
              intro J0 hJ0
              rw [hprod J0]
        _ = tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
              (fun i : Fin 3 => basis i) I0 := by
              simp
    calc
      (∑ J0 : Fin 4 → Fin 3,
          (∏ a : Fin 4, identityInvMetric (Idx := Fin 3) (I0 a) (J0 a)) *
            tensor0SComponent (I := I) (A : Tensor04At (I := I) (M := M) x)
              (fun i : Fin 3 => basis i) I0 *
            tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
              (fun i : Fin 3 => basis i) J0)
          = tensor0SComponent (I := I) (A : Tensor04At (I := I) (M := M) x)
              (fun i : Fin 3 => basis i) I0 *
              (∑ J0 : Fin 4 → Fin 3,
                (∏ a : Fin 4, identityInvMetric (Idx := Fin 3) (I0 a) (J0 a)) *
                  tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
                    (fun i : Fin 3 => basis i) J0) := by
            simp [Finset.mul_sum, mul_left_comm, mul_comm]
      _ = tensor0SComponent (I := I) (A : Tensor04At (I := I) (M := M) x)
            (fun i : Fin 3 => basis i) I0 *
          tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
            (fun i : Fin 3 => basis i) I0 := by
            rw [hJ]
  rw [hcollapse]
  have htuple := sum_tuple_eq_sum_slots
    (fun I0 : Fin 4 → Fin 3 =>
      tensor0SComponent (I := I) (A : Tensor04At (I := I) (M := M) x)
          (fun i : Fin 3 => basis i) I0 *
        tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
          (fun i : Fin 3 => basis i) I0)
  rw [htuple]
  have hA1 := mem_algebraicCurvatureTensorSubmodule_iff_symmetries.mp A.2
  have hB1 := mem_algebraicCurvatureTensorSubmodule_iff_symmetries.mp B.2
  let X : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Real :=
    fun i j k l =>
      tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (basis i) (basis j) (basis k) (basis l) *
        tensor04StdAt (I := I) (M := M) (B : Tensor04At (I := I) (M := M) x)
          (basis i) (basis j) (basis k) (basis l)
  have hX : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      tensor0SComponent (I := I) (A : Tensor04At (I := I) (M := M) x)
          (fun m : Fin 3 => basis m) (slots4 i j k l) *
        tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
          (fun m : Fin 3 => basis m) (slots4 i j k l)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, X i j k l := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro j hj
    refine Finset.sum_congr rfl ?_
    intro k hk
    refine Finset.sum_congr rfl ?_
    intro l hl
    unfold X
    rw [show tensor0SComponent (I := I) (A : Tensor04At (I := I) (M := M) x)
          (fun m : Fin 3 => basis m) (slots4 i j k l) =
        tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (basis i) (basis j) (basis k) (basis l) from by
        simp only [tensor0SComponent_apply, tensor04StdAt_apply]
        congr 1
        funext a
        fin_cases a <;> simp [slots4, vec4]]
    rw [show tensor0SComponent (I := I) (B : Tensor04At (I := I) (M := M) x)
          (fun m : Fin 3 => basis m) (slots4 i j k l) =
        tensor04StdAt (I := I) (M := M) (B : Tensor04At (I := I) (M := M) x)
          (basis i) (basis j) (basis k) (basis l) from by
        simp only [tensor0SComponent_apply, tensor04StdAt_apply]
        congr 1
        funext a
        fin_cases a <;> simp [slots4, vec4]]
  rw [hX]
  have hmain := sum_four_by_pairs X
    (by
      intro i j k l
      have h1 := hA1.1 (basis i) (basis j) (basis k) (basis l)
      have h2 := hB1.1 (basis i) (basis j) (basis k) (basis l)
      unfold X
      rw [h1, h2]
      ring)
    (by
      intro i j k l
      have h1 := hA1.2.1 (basis i) (basis j) (basis k) (basis l)
      have h2 := hB1.2.1 (basis i) (basis j) (basis k) (basis l)
      unfold X
      rw [h1, h2]
      ring)
    (by
      intro i j k l
      have h1 := hA1.1 (basis i) (basis i) (basis k) (basis l)
      have h2 := hB1.1 (basis i) (basis i) (basis k) (basis l)
      have hA0 : tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (basis i) (basis i) (basis k) (basis l) = 0 := by linarith
      have hB0 : tensor04StdAt (I := I) (M := M) (B : Tensor04At (I := I) (M := M) x)
          (basis i) (basis i) (basis k) (basis l) = 0 := by linarith
      unfold X
      rw [hA0, hB0]
      ring)
    (by
      intro i j k l
      have h1 := hA1.2.1 (basis i) (basis j) (basis k) (basis k)
      have h2 := hB1.2.1 (basis i) (basis j) (basis k) (basis k)
      have hA0 : tensor04StdAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
          (basis i) (basis j) (basis k) (basis k) = 0 := by linarith
      have hB0 : tensor04StdAt (I := I) (M := M) (B : Tensor04At (I := I) (M := M) x)
          (basis i) (basis j) (basis k) (basis k) = 0 := by linarith
      unfold X
      rw [hA0, hB0]
      ring)
  rw [hmain]

end DifferentialGeometry.PDE.RicciFlow

end
