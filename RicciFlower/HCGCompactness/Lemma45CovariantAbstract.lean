import RicciFlower.HCGCompactness.SumLemmas
import RicciFlower.Tensor.RSTensor.NablaOnTensors.HigherOrder
import RicciFlower.Tensor.RSTensor.NablaOnTensors.ConnectionDifference
import RicciFlower.Tensor.RSTensor.NablaOnTensors.ConnectionDifferenceAction
import RicciFlower.Tensor.RSTensor.NablaOnTensors.ConnectionDifferenceActionIdentity

set_option autoImplicit false

/-!
# Covariant Abstract Boundary for MSM135 Lemma 4.5

This file pins down the checked RicciFlower names used by the covariant
`(0,s)` route to MSM135 Lemma 4.5.  It intentionally contains no new
frontier hypothesis and no approximate-isometry specialization.

Notation map for the later theorem:

* `H` is the comparison metric/connection.  Its Levi-Civita connection is
  `LeviCivita.leviCivitaConnectionOfMetric`.
* `A = nabla_g - nabla_H` is represented intrinsically by
  `Tensor0SBundle.connectionDifferenceTensorAt`.
* The checked first-order covariant connection-change identity is
  `Tensor0SBundle.nabla0SFun_sub_cov`.
* The checked mixed component version is
  `Tensor0SBundle.componentRS_nablaRSFun_sub`.
* The checked component action and coarse norm constant are
  `Tensor0SBundle.connActComp` and `Tensor0SBundle.connActConst`.
* The checked first-order norm producer is
  `Tensor0SBundle.totalNablaNorm_bound`.
* The checked algebraic induction constants are
  `oneStepConst`, `lemma45Const`, and `main_step_to_lemma45Const`.

The next missing producer is the iterated `H`-Leibniz estimate for repeated
covariant derivatives of the connection-difference action.  That proof should
live below the final approximate-isometry theorem and consume the names above,
rather than expanding Christoffel symbols in the Lemma 4.5 induction.
-/

noncomputable section

namespace RicciFlower
namespace HCGCompactness

open scoped BigOperators

/-- Scalar induction skeleton for MSM135 Lemma 4.5.

`N i` represents the `H`-derivative norms of a tensor `T`, `G k` represents the
`H`-derivative norms of `nabla_g T`, and `D r` represents the `g`-derivative
norms of `T`.  The hypotheses are exactly the two non-algebraic inputs used by
the book proof:

* `hLift`: apply the lower-order Lemma 4.5 estimate to `nabla_g T`;
* `hOne`: the one-step estimate comparing `H^k (nabla_g T)` to `H`-derivatives
  of `T`.

The conclusion is the recursive Lemma 4.5 estimate with `lemma45Const`. -/
theorem lemma45Scalar
    {eps : Real} {B N G D : Nat -> Real} {s : Nat}
    (heps0 : 0 <= eps)
    (heps1 : eps <= 1)
    (hB : forall i : Nat, 0 <= B i)
    (hN : forall i : Nat, 0 <= N i)
    (hLift : forall p : Nat,
      D (p + 1) <= G p + eps * lemma45Const B p (s + 1) *
        Finset.sum (Finset.range p) (fun k => G k))
    (hOne : forall k : Nat,
      G k <= N (k + 1) + eps * oneStepConst B k s *
        Finset.sum (Finset.range (k + 1)) (fun i => N i)) :
    forall p r : Nat, 0 < r -> r <= p ->
      D r <= N r + eps * lemma45Const B p s *
        Finset.sum (Finset.range r) (fun i => N i) := by
  intro p
  induction p with
  | zero =>
      intro r hr0 hrp
      omega
  | succ p ih =>
      intro r hr0 hrp
      by_cases hr_le_p : r <= p
      · have hih := ih r hr0 hr_le_p
        let S : Real := Finset.sum (Finset.range r) (fun i => N i)
        have hS_nonneg : 0 <= S := by
          exact Finset.sum_nonneg fun i _hi => hN i
        have hcoef :
            lemma45Const B p s <= lemma45Const B (p + 1) s :=
          lemma45Const_le_succ hB p s
        have hepsS_nonneg : 0 <= eps * S := mul_nonneg heps0 hS_nonneg
        have hmul :
            eps * lemma45Const B p s * S <=
              eps * lemma45Const B (p + 1) s * S := by
          calc
            eps * lemma45Const B p s * S = (eps * S) * lemma45Const B p s := by
              ring
            _ <= (eps * S) * lemma45Const B (p + 1) s :=
              mul_le_mul_of_nonneg_left hcoef hepsS_nonneg
            _ = eps * lemma45Const B (p + 1) s * S := by
              ring
        have hmono :
            N r + eps * lemma45Const B p s * S <=
              N r + eps * lemma45Const B (p + 1) s * S :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hmul (N r)
        exact hih.trans (by simpa [S] using hmono)
      · have hr_eq : r = p + 1 := by omega
        subst r
        exact main_step_to_lemma45Const_of_partials
          (eps := eps) (A := D (p + 1)) (B := B) (N := N) (G := G)
          (p := p) (s := s)
          heps0 heps1 hB hN (hLift p) (hOne p)
          (fun k _hk => hOne k)

/-- Scalar Lemma 4.5 induction with the one-step estimate supplied in the
natural antidiagonal Leibniz form.

`A a` represents the norm of the `a`-th `H`-derivative of the connection
difference, and `N b` represents the norm of the `b`-th `H`-derivative of the
tensor.  The theorem converts a raw product-rule estimate for each `G k` into
the final recursive Lemma 4.5 bound. -/
theorem lemma45Anti
    {eps : Real} {B A N G D : Nat -> Real} {s : Nat}
    (heps0 : 0 <= eps)
    (heps1 : eps <= 1)
    (hB : forall i : Nat, 0 <= B i)
    (hN : forall i : Nat, 0 <= N i)
    (hA : forall a : Nat, A a <= eps * B a)
    (hLift : forall p : Nat,
      D (p + 1) <= G p + eps * lemma45Const B p (s + 1) *
        Finset.sum (Finset.range p) (fun k => G k))
    (hLeib : forall k : Nat,
      G k <= N (k + 1) +
        (s : Real) *
          Finset.sum (Finset.antidiagonal k)
            (fun ab => (Nat.choose k ab.1 : Real) * A ab.1 * N ab.2)) :
    forall p r : Nat, 0 < r -> r <= p ->
      D r <= N r + eps * lemma45Const B p s *
        Finset.sum (Finset.range r) (fun i => N i) := by
  refine lemma45Scalar
    (eps := eps) (B := B) (N := N) (G := G) (D := D) (s := s)
    heps0 heps1 hB hN hLift ?_
  intro k
  exact oneStep_from_antidiagonal
    (eps := eps) (G := G k) (B := B) (A := A) (T := N) (N := N)
    (k := k) (s := s) heps0 hB
    (fun i _hi => hN i)
    (fun a _ha => hA a)
    (fun b hb => single_le_sum_range hN hb)
    (hLeib k)

end HCGCompactness
end RicciFlower
