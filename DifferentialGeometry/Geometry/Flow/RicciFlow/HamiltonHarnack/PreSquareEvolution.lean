import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.BlockReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.MEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TriangularJets

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

namespace UQuadratic

variable {Idx : Type*} [Fintype Idx]

private theorem sumSix_swap_cd
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F a b c d e f) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F a b d c e f := by
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

private theorem sumTwo_swap
    (F : Idx -> Idx -> Real) :
    (∑ a, ∑ b, F a b) = ∑ a, ∑ b, F b a := by
  rw [Finset.sum_comm]

private theorem sumSix_lastTwo_first
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F a b c d e f) =
      ∑ e, ∑ f, ∑ a, ∑ b, ∑ c, ∑ d, F a b c d e f := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F a b c d e f) =
        ∑ a, ∑ b, ∑ c, ∑ e, ∑ d, ∑ f, F a b c d e f := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ e, ∑ f, ∑ d, F a b c d e f := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ e, ∑ c, ∑ f, ∑ d, F a b c d e f := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ e, ∑ f, ∑ c, ∑ d, F a b c d e f := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ b, ∑ f, ∑ c, ∑ d, F a b c d e f := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ f, ∑ b, ∑ c, ∑ d, F a b c d e f := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = ∑ e, ∑ a, ∑ f, ∑ b, ∑ c, ∑ d, F a b c d e f := Finset.sum_comm
    _ = ∑ e, ∑ f, ∑ a, ∑ b, ∑ c, ∑ d, F a b c d e f := by
      refine Finset.sum_congr rfl fun e _ => Finset.sum_comm

private theorem sumSix_neg
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, -F a b c d e f) =
      -(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F a b c d e f) := by
  simp only [Finset.sum_neg_distrib]

private theorem sumTwo_neg (F : Idx -> Idx -> Real) :
    (∑ a, ∑ b, -F a b) = -(∑ a, ∑ b, F a b) := by
  simp only [Finset.sum_neg_distrib]

private theorem sumFour_mul (F : Idx -> Idx -> Idx -> Idx -> Real) (r : Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * r) =
      (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) * r := by
  simp only [Finset.sum_mul]

private theorem curvature_reaction_contraction
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real)
    (hRm : Rm04Symm R)
    (hU : forall a b, U a b = -U b a) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      hamiltonRmReactionComponent R a b d c * U a b * U c d) =
      4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
        R a e f c * R b e f d * U a b * U c d) +
      ∑ a, ∑ b, (∑ c, ∑ d, R a b d c * U c d) ^ 2 := by
  classical
  let T := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    R a e b f * R c e d f * U a b * U c d
  let E := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
    R a e c f * R b e d f * U a b * U c d
  let C := fun e f => ∑ a, ∑ b, R a b e f * U a b
  have hfirst :
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
        R a e b f * R d e c f * U a b * U c d) = -T := by
    rw [sumSix_swap_cd]
    unfold T
    rw [← sumSix_neg (fun a b c d e f =>
      R a e b f * R c e d f * U a b * U c d)]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hU d c]
    ring
  have hthird :
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
        R a e d f * R b e c f * U a b * U c d) = -E := by
    rw [sumSix_swap_cd]
    unfold E
    rw [← sumSix_neg (fun a b c d e f =>
      R a e c f * R b e d f * U a b * U c d)]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hU d c]
    ring
  have hfirst' :
      (∑ a, ∑ b, ∑ c, ∑ d,
        (∑ e, ∑ f, R a e b f * R d e c f) * U a b * U c d) = -T := by
    rw [← hfirst]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_mul]
    rw [Finset.sum_mul]
  have hthird' :
      (∑ a, ∑ b, ∑ c, ∑ d,
        (∑ e, ∑ f, R a e d f * R b e c f) * U a b * U c d) = -E := by
    rw [← hthird]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_mul]
    rw [Finset.sum_mul]
  have hsecond' :
      (∑ a, ∑ b, ∑ c, ∑ d,
        (∑ e, ∑ f, R a e b f * R c e d f) * U a b * U c d) = T := by
    unfold T
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_mul]
    rw [Finset.sum_mul]
  have hfourth' :
      (∑ a, ∑ b, ∑ c, ∑ d,
        (∑ e, ∑ f, R a e c f * R b e d f) * U a b * U c d) = E := by
    unfold E
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_mul]
    rw [Finset.sum_mul]
  have hE :
      E = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
        R a e f c * R b e f d * U a b * U c d := by
    unfold E
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hRm.swap34 a e c f, hRm.swap34 b e d f]
    ring
  have hC (e f : Idx) :
      (∑ a, ∑ b, R a e b f * U a b) = (1 / 2 : Real) * C e f := by
    have hzero :
        (∑ a, ∑ b,
          (R a e b f + R e b a f + R b a e f) * U a b) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      rw [hRm.bianchi a e b f]
      ring
    have hsecond :
        (∑ a, ∑ b, R e b a f * U a b) =
          ∑ a, ∑ b, R a e b f * U a b := by
      calc
        (∑ a, ∑ b, R e b a f * U a b) =
            ∑ a, ∑ b, R e a b f * U b a := by
          simpa only using sumTwo_swap (fun a b => R e b a f * U a b)
        _ = ∑ a, ∑ b, R a e b f * U a b := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hU b a, hRm.swap12 e a b f]
          ring
    have hlast :
        (∑ a, ∑ b, R b a e f * U a b) = -C e f := by
      unfold C
      calc
        (∑ a, ∑ b, R b a e f * U a b) =
            ∑ a, ∑ b, -(R a b e f * U a b) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hRm.swap12 b a e f]
          ring
        _ = -∑ a, ∑ b, R a b e f * U a b := by
          simp only [Finset.sum_neg_distrib]
    simp only [add_mul, Finset.sum_add_distrib] at hzero
    rw [hsecond, hlast] at hzero
    linear_combination (norm := ring_nf) (1 / 2 : Real) * hzero
  have hT : T = (1 / 4 : Real) * ∑ e, ∑ f, (C e f) ^ 2 := by
    unfold T
    calc
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
          R a e b f * R c e d f * U a b * U c d) =
          ∑ e, ∑ f,
            (∑ a, ∑ b, R a e b f * U a b) *
              (∑ c, ∑ d, R c e d f * U c d) := by
        rw [sumSix_lastTwo_first]
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        ring
      _ = (1 / 4 : Real) * ∑ e, ∑ f, (C e f) ^ 2 := by
        simp_rw [hC]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        ring
  have hSquare :
      (∑ a, ∑ b, (∑ c, ∑ d, R a b d c * U c d) ^ 2) =
        ∑ e, ∑ f, (C e f) ^ 2 := by
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun f _ => ?_
    unfold C
    have hinner :
      (∑ c, ∑ d, R e f d c * U c d) = -∑ c, ∑ d, R c d e f * U c d := by
      rw [← sumTwo_neg (fun c d => R c d e f * U c d)]
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hRm.swap34 e f d c, hRm.pair e f c d]
      ring
    rw [hinner]
    ring
  have hReaction :
      (∑ a, ∑ b, ∑ c, ∑ d,
        hamiltonRmReactionComponent R a b d c * U a b * U c d) =
        4 * T + 4 * E := by
    calc
      (∑ a, ∑ b, ∑ c, ∑ d,
          hamiltonRmReactionComponent R a b d c * U a b * U c d) =
          ∑ a, ∑ b, ∑ c, ∑ d,
            ((-2 : Real) *
                ((∑ e, ∑ f, R a e b f * R d e c f) * U a b * U c d) +
              2 * ((∑ e, ∑ f, R a e b f * R c e d f) * U a b * U c d) -
              2 * ((∑ e, ∑ f, R a e d f * R b e c f) * U a b * U c d) +
              2 * ((∑ e, ∑ f, R a e c f * R b e d f) * U a b * U c d)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        unfold hamiltonRmReactionComponent hamiltonBComponent
        ring
      _ = -2 * (∑ a, ∑ b, ∑ c, ∑ d,
            (∑ e, ∑ f, R a e b f * R d e c f) * U a b * U c d) +
          2 * (∑ a, ∑ b, ∑ c, ∑ d,
            (∑ e, ∑ f, R a e b f * R c e d f) * U a b * U c d) -
          2 * (∑ a, ∑ b, ∑ c, ∑ d,
            (∑ e, ∑ f, R a e d f * R b e c f) * U a b * U c d) +
          2 * (∑ a, ∑ b, ∑ c, ∑ d,
            (∑ e, ∑ f, R a e c f * R b e d f) * U a b * U c d) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [← Finset.mul_sum]
      _ = 4 * T + 4 * E := by
        rw [hfirst', hsecond', hthird', hfourth']
        ring
  rw [hReaction, hE, hT, hSquare]
  ring

end UQuadratic

namespace Mixed

variable {Idx : Type*} [Fintype Idx]

private theorem sumTwo_swap
    (F : Idx -> Idx -> Real) :
    (∑ a, ∑ b, F a b) = ∑ a, ∑ b, F b a := by
  rw [Finset.sum_comm]

private theorem sumFive_swap_ab
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F b a c d e := by
  rw [Finset.sum_comm]

private theorem sumFive_rotate_blocks
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F d e c a b := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e) =
        ∑ a, ∑ b, ∑ d, ∑ c, ∑ e, F a b c d e := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, ∑ e, F a b c d e := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, ∑ e, F a b c d e := Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ e, ∑ c, F a b c d e := by
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ e, ∑ b, ∑ c, F a b c d e := by
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ e, ∑ a, ∑ b, ∑ c, F a b c d e := by
      refine Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d, ∑ e, ∑ c, ∑ a, ∑ b, F a b c d e := by
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun e _ => ?_
      calc
        (∑ a, ∑ b, ∑ c, F a b c d e) =
            ∑ a, ∑ c, ∑ b, F a b c d e := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ c, ∑ a, ∑ b, F a b c d e := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F d e c a b := by rfl

private theorem sumFive_neg
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, -F a b c d e) =
      -(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e) := by
  simp only [Finset.sum_neg_distrib]

private theorem sumFive_swap_second_third
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ e, ∑ a, ∑ b, ∑ c, ∑ d, F e a b c d) =
      ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, F e b a c d := by
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]

private theorem sumFour_first_last
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ b, ∑ c, ∑ d, ∑ a, F a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
        ∑ b, ∑ a, ∑ c, ∑ d, F a b c d := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ d, F a b c d := by
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ d, ∑ a, F a b c d := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => Finset.sum_comm

private theorem sumThree_cycle
    (F : Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ b, ∑ c, F b c a := by
  calc
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ c, ∑ b, F a b c := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, F b c a := by rfl

private theorem sumFour_swap_ab
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, F b a c d := by
  rw [Finset.sum_comm]

private theorem sumFour_neg
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, -F a b c d) =
      -(∑ a, ∑ b, ∑ c, ∑ d, F a b c d) := by
  simp only [Finset.sum_neg_distrib]

private theorem sumFive_first_last
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ e, ∑ a, ∑ b, ∑ c, ∑ d, F e a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F e a b c d := by
  calc
    (∑ e, ∑ a, ∑ b, ∑ c, ∑ d, F e a b c d) =
        ∑ a, ∑ e, ∑ b, ∑ c, ∑ d, F e a b c d := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ e, ∑ c, ∑ d, F e a b c d := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ e, ∑ d, F e a b c d := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F e a b c d := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => Finset.sum_comm

private theorem pre_square_mixed_contraction
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (P : Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hRm : Rm04Symm R)
    (hP : forall a b c, P a b c = -P b a c)
    (hU : forall a b, U a b = -U b a) :
    4 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        (R a d e b * P d e c + R a d e c * P d b e +
          R b d e c * P a d e) * U a b * W c) =
      hamiltonBlockPreSquareP (fun a b c d => R a b d c) P U W := by
  classical
  let L1 := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    R a d e b * P d e c * U a b * W c
  let L2 := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    R a d e c * P d b e * U a b * W c
  let L3 := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    R b d e c * P a d e * U a b * W c
  let C := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    R d e a b * P a b c * U d e * W c
  have hL3 : L3 = L2 := by
    unfold L3 L2
    rw [sumFive_swap_ab]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hU b a, hP b d e]
    ring
  have hCurv (a b : Idx) :
      (∑ d, ∑ e, R d a b e * U d e) =
        -(1 / 2 : Real) * ∑ d, ∑ e, R d e a b * U d e := by
    have hzero :
        (∑ d, ∑ e,
          (R d a e b + R a e d b + R e d a b) * U d e) = 0 := by
      apply Finset.sum_eq_zero
      intro d _
      apply Finset.sum_eq_zero
      intro e _
      rw [hRm.bianchi d a e b]
      ring
    have hsecond :
        (∑ d, ∑ e, R a e d b * U d e) =
          ∑ d, ∑ e, R d a e b * U d e := by
      calc
        (∑ d, ∑ e, R a e d b * U d e) =
            ∑ d, ∑ e, R a d e b * U e d := by
          simpa only using sumTwo_swap (fun d e => R a e d b * U d e)
        _ = ∑ d, ∑ e, R d a e b * U d e := by
          refine Finset.sum_congr rfl fun d _ => ?_
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hU e d, hRm.swap12 a d e b]
          ring
    have hlast :
        (∑ d, ∑ e, R e d a b * U d e) =
          -∑ d, ∑ e, R d e a b * U d e := by
      calc
        (∑ d, ∑ e, R e d a b * U d e) =
            ∑ d, ∑ e, -(R d e a b * U d e) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hRm.swap12 e d a b]
          ring
        _ = _ := by simp only [Finset.sum_neg_distrib]
    simp only [add_mul, Finset.sum_add_distrib] at hzero
    rw [hsecond, hlast] at hzero
    have hbase :
        (∑ d, ∑ e, R d a e b * U d e) =
          (1 / 2 : Real) * ∑ d, ∑ e, R d e a b * U d e := by
      linear_combination (norm := ring_nf) (1 / 2 : Real) * hzero
    calc
      (∑ d, ∑ e, R d a b e * U d e) =
          -∑ d, ∑ e, R d a e b * U d e := by
        calc
          (∑ d, ∑ e, R d a b e * U d e) =
              ∑ d, ∑ e, -(R d a e b * U d e) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [hRm.swap34 d a b e]
            ring
          _ = _ := by simp only [Finset.sum_neg_distrib]
      _ = _ := by rw [hbase]; ring
  have hL1 : L1 = -(1 / 2 : Real) * C := by
    unfold L1 C
    rw [sumFive_rotate_blocks]
    calc
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          R d a b e * P a b c * U d e * W c) =
          ∑ a, ∑ b, ∑ c,
            (∑ d, ∑ e, R d a b e * U d e) * P a b c * W c := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_mul]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_mul]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
      _ = ∑ a, ∑ b, ∑ c,
          (-(1 / 2 : Real) * ∑ d, ∑ e, R d e a b * U d e) *
            P a b c * W c := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hCurv]
      _ = -(1 / 2 : Real) *
          ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
            R d e a b * P a b c * U d e * W c := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        ring_nf
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
  have hCross :
      (∑ a, ∑ b,
        (∑ c, P a b c * W c) * (∑ d, ∑ e, R a b e d * U d e)) =
        2 * L1 := by
    calc
      (∑ a, ∑ b,
          (∑ c, P a b c * W c) * (∑ d, ∑ e, R a b e d * U d e)) =
          ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
            P a b c * W c * R a b e d * U d e := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
      _ = -C := by
        unfold C
        rw [← sumFive_neg (fun a b c d e =>
          R d e a b * P a b c * U d e * W c)]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hRm.swap34 a b e d, hRm.pair a b d e]
        ring
      _ = 2 * L1 := by rw [hL1]; ring
  have hLeft :
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        (R a d e b * P d e c + R a d e c * P d b e +
          R b d e c * P a d e) * U a b * W c) = L1 + L2 + L3 := by
    unfold L1 L2 L3
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hLeft]
  change 4 * (L1 + L2 + L3) = 8 * L2 +
    2 * (∑ a, ∑ b,
      (∑ c, P a b c * W c) * (∑ d, ∑ e, R a b e d * U d e))
  rw [hL3, hCross]
  ring

variable [DecidableEq Idx]

private theorem mixed_evolution_contraction
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hRm : Rm04Symm R)
    (hNablaRm : forall e, Rm04PairSymm (nablaR e))
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (hContract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hU : forall a b, U a b = -U b a) :
    2 * (∑ a, ∑ b, ∑ c,
        hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic a b c *
          U a b * W c) +
      2 * (∑ a, ∑ b, ∑ c,
        hamiltonPComponent nablaRic a b c * U a b *
          ((1 / clock.elapsed) * W c)) -
      4 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
        nablaR e a b d c *
          hamiltonTestJetDU clock Ric
            (fun i j => if i = j then 1 else 0) W e a b * U c d) =
      hamiltonBlockPreSquareP
        (fun a b c d => R a b d c)
        (hamiltonPComponent nablaRic) U W := by
  classical
  let P := hamiltonPComponent nablaRic
  let D := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    Ric d e * nablaR d a b e c * U a b * W c
  let F := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    nablaR a b c e d * Ric a b * W c * U d e
  let F2 := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    nablaR a b c e d * Ric a c * W b * U d e
  let G := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    nablaR a b c e d *
      ((1 / 2 : Real) * (Ric a b * W c - Ric a c * W b)) * U d e
  have hP (a b c : Idx) : P a b c = -P b a c := by
    unfold P hamiltonPComponent
    ring
  have hD : D = -F := by
    unfold D F
    rw [sumFive_rotate_blocks]
    rw [← sumFive_neg (fun a b c d e =>
      nablaR a b c e d * Ric a b * W c * U d e)]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [(hNablaRm a).pair d e b c, (hNablaRm a).swap34 b c e d]
    ring
  have hF2 : F2 = -F := by
    unfold F2 F
    rw [sumFive_swap_second_third]
    rw [← sumFive_neg (fun a b c d e =>
      nablaR a b c e d * Ric a b * W c * U d e)]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [(hNablaRm a).swap12 c b e d]
    ring
  have hG : G = F := by
    have hExpand : G = (1 / 2 : Real) * F - (1 / 2 : Real) * F2 := by
      unfold G F F2
      calc
        (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
            nablaR a b c e d *
              ((1 / 2 : Real) * (Ric a b * W c - Ric a c * W b)) * U d e) =
            ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
              ((1 / 2 : Real) *
                  (nablaR a b c e d * Ric a b * W c * U d e) -
                (1 / 2 : Real) *
                  (nablaR a b c e d * Ric a c * W b * U d e)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun c _ => ?_
          refine Finset.sum_congr rfl fun d _ => ?_
          refine Finset.sum_congr rfl fun e _ => ?_
          ring
        _ = (1 / 2 : Real) *
              (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
                nablaR a b c e d * Ric a b * W c * U d e) -
            (1 / 2 : Real) *
              (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
                nablaR a b c e d * Ric a c * W b * U d e) := by
          simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hExpand, hF2]
    ring
  let Q := ∑ a, ∑ b, ∑ c, P a b c * U a b * W c
  let H1 := ∑ a, ∑ b, ∑ c, ∑ d,
    nablaR a a b d c * W b * U c d
  let H2 := ∑ a, ∑ b, ∑ c, ∑ d,
    nablaR b a b d c * W a * U c d
  let H := ∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
    nablaR e a b d c *
      ((if e = a then (1 : Real) else 0) * W b -
        (if e = b then (1 : Real) else 0) * W a) * U c d
  have hDiv (b d c : Idx) :
      (∑ a, nablaR a a b d c) = P c d b := by
    unfold P hamiltonPComponent
    rw [hContract b c d, hNablaRic c b d, hNablaRic d b c]
  have hH2 : H2 = -H1 := by
    unfold H2 H1
    rw [sumFour_swap_ab]
    rw [← sumFour_neg (fun a b c d =>
      nablaR a a b d c * W b * U c d)]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [(hNablaRm a).swap12 b a d c]
    ring
  have hH1 : H1 = Q := by
    unfold H1 Q
    rw [sumFour_first_last]
    conv_rhs => rw [sumThree_cycle]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, hDiv]
    ring
  have hH : H = 2 * Q := by
    have hDelta : H = H1 - H2 := by
      unfold H H1 H2
      rw [sumFive_first_last]
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite,
        ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring
    rw [hDelta, hH2, hH1]
    ring
  let A := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    (R a d e b * P d e c + R a d e c * P d b e +
      R b d e c * P a d e) * U a b * W c
  have hLP :
      (∑ a, ∑ b, ∑ c,
        hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic a b c *
          U a b * W c) = 2 * A - 2 * D := by
    unfold A D P hamiltonPEvolutionReactionComponent hamiltonPComponent
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring_nf
    simp only [Finset.sum_mul]
    ring_nf
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    ring_nf
  have hLW :
      (∑ a, ∑ b, ∑ c,
        P a b c * U a b * ((1 / clock.elapsed) * W c)) =
        (1 / clock.elapsed) * Q := by
    calc
      (∑ a, ∑ b, ∑ c,
          P a b c * U a b * ((1 / clock.elapsed) * W c)) =
          ∑ a, ∑ b, ∑ c,
            (1 / clock.elapsed) * (P a b c * U a b * W c) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
      _ = (1 / clock.elapsed) * Q := by
        unfold Q
        simp only [Finset.mul_sum]
  have hDK :
      (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
        nablaR e a b d c *
          hamiltonTestJetDU clock Ric
            (fun i j => if i = j then 1 else 0) W e a b * U c d) =
        G + (1 / (4 * clock.elapsed) : Real) * H := by
    unfold G H hamiltonTestJetDU
    calc
      (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
          nablaR e a b d c *
            ((1 / 2 : Real) * (Ric e a * W b - Ric e b * W a) +
              (1 / (4 * clock.elapsed) : Real) *
                ((if e = a then (1 : Real) else 0) * W b -
                  (if e = b then (1 : Real) else 0) * W a)) * U c d) =
          ∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
            (nablaR e a b d c *
                ((1 / 2 : Real) * (Ric e a * W b - Ric e b * W a)) * U c d +
              (1 / (4 * clock.elapsed) : Real) *
                (nablaR e a b d c *
                  ((if e = a then (1 : Real) else 0) * W b -
                    (if e = b then (1 : Real) else 0) * W a) * U c d)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        ring
      _ = (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
              nablaR e a b d c *
                ((1 / 2 : Real) * (Ric e a * W b - Ric e b * W a)) * U c d) +
            (1 / (4 * clock.elapsed) : Real) *
              (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
                nablaR e a b d c *
                  ((if e = a then (1 : Real) else 0) * W b -
                    (if e = b then (1 : Real) else 0) * W a) * U c d) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = _ := by rfl
  have hReduced :
      2 * (∑ a, ∑ b, ∑ c,
          hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic a b c *
            U a b * W c) +
        2 * (∑ a, ∑ b, ∑ c,
          P a b c * U a b * ((1 / clock.elapsed) * W c)) -
        4 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
          nablaR e a b d c *
            hamiltonTestJetDU clock Ric
              (fun i j => if i = j then 1 else 0) W e a b * U c d) =
        4 * A := by
    rw [hLP, hLW, hDK, hD, hG, hH]
    field_simp [HarnackClock.elapsed_ne_zero clock]
    ring
  change
    2 * (∑ a, ∑ b, ∑ c,
        hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic a b c *
          U a b * W c) +
      2 * (∑ a, ∑ b, ∑ c,
        P a b c * U a b * ((1 / clock.elapsed) * W c)) -
      4 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
        nablaR e a b d c *
          hamiltonTestJetDU clock Ric
            (fun i j => if i = j then 1 else 0) W e a b * U c d) =
      hamiltonBlockPreSquareP (fun a b c d => R a b d c) P U W
  rw [hReduced]
  exact pre_square_mixed_contraction R P U W hRm hP hU

end Mixed

namespace Covector

variable {Idx : Type*} [Fintype Idx]

private theorem sumFour_swap12
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, F b a c d := by
  rw [Finset.sum_comm]

private theorem sumFour_swap23
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, F a c b d := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

private theorem sumFour_rotate_pairs
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, F c d a b := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
        ∑ a, ∑ c, ∑ b, ∑ d, F a b c d := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, F a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d := by
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
      refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, F c d a b := by rfl

private theorem sumFour_neg
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, -F a b c d) =
      -(∑ a, ∑ b, ∑ c, ∑ d, F a b c d) := by
  simp only [Finset.sum_neg_distrib]

variable [DecidableEq Idx]

private theorem hamilton_w2_derivative_terms
    (clock : HarnackClock)
    (Ric : Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (W : Idx -> Real)
    (hNablaPSkew : forall e a b c, nablaP e a b c = -nablaP e b a c) :
    2 * (∑ a, ∑ b, ∑ c, ∑ d,
        Ric c d * (nablaP c d a b + nablaP c d b a) * W a * W b) +
      2 * (1 / clock.elapsed) *
        (∑ a, ∑ b, (∑ e, nablaP e e a b) * W a * W b) -
      4 * (∑ e, ∑ a, ∑ b, ∑ c,
        nablaP e a b c *
          hamiltonTestJetDU clock Ric
            (fun i j => if i = j then 1 else 0) W e a b * W c) = 0 := by
  classical
  let AR := ∑ e, ∑ a, ∑ b, ∑ c,
    nablaP e a b c * Ric e a * W b * W c
  let AR' := ∑ e, ∑ a, ∑ b, ∑ c,
    nablaP e a b c * Ric e b * W a * W c
  let AD := ∑ e, ∑ a, ∑ b, ∑ c,
    nablaP e a b c * (if e = a then (1 : Real) else 0) * W b * W c
  let AD' := ∑ e, ∑ a, ∑ b, ∑ c,
    nablaP e a b c * (if e = b then (1 : Real) else 0) * W a * W c
  let D := ∑ a, ∑ b, (∑ e, nablaP e e a b) * W a * W b
  have hAR' : AR' = -AR := by
    unfold AR' AR
    rw [sumFour_swap23]
    rw [← sumFour_neg (fun e a b c =>
      nablaP e a b c * Ric e a * W b * W c)]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hNablaPSkew e b a c]
    ring
  have hAD' : AD' = -AD := by
    unfold AD' AD
    rw [sumFour_swap23]
    rw [← sumFour_neg (fun e a b c =>
      nablaP e a b c * (if e = a then (1 : Real) else 0) * W b * W c)]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hNablaPSkew e b a c]
    ring
  have hAD : AD = D := by
    unfold AD D
    calc
      (∑ e, ∑ a, ∑ b, ∑ c,
          nablaP e a b c * (if e = a then (1 : Real) else 0) * W b * W c) =
          ∑ e, ∑ b, ∑ c, nablaP e e b c * W b * W c := by
        refine Finset.sum_congr rfl fun e _ => ?_
        let G : Idx -> Real := fun a => ∑ b, ∑ c,
          nablaP e a b c * (if e = a then (1 : Real) else 0) * W b * W c
        change (∑ a, G a) = ∑ b, ∑ c, nablaP e e b c * W b * W c
        calc
          (∑ a, G a) = G e := by
            refine Finset.sum_eq_single e ?_ ?_
            · intro a _ ha
              unfold G
              simp [ha.symm]
            · simp
          _ = ∑ b, ∑ c, nablaP e e b c * W b * W c := by simp [G]
      _ = ∑ a, ∑ b, ∑ e, nablaP e e a b * W a * W b := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
      _ = ∑ a, ∑ b, (∑ e, nablaP e e a b) * W a * W b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
  have hReaction :
      (∑ a, ∑ b, ∑ c, ∑ d,
        Ric c d * (nablaP c d a b + nablaP c d b a) * W a * W b) =
        2 * AR := by
    have hFirst :
        (∑ a, ∑ b, ∑ c, ∑ d,
          Ric c d * nablaP c d a b * W a * W b) = AR := by
      unfold AR
      rw [sumFour_rotate_pairs]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    have hSecond :
        (∑ a, ∑ b, ∑ c, ∑ d,
          Ric c d * nablaP c d b a * W a * W b) = AR := by
      rw [sumFour_swap12]
      calc
        (∑ a, ∑ b, ∑ c, ∑ d,
            Ric c d * nablaP c d a b * W b * W a) =
            ∑ a, ∑ b, ∑ c, ∑ d,
              Ric c d * nablaP c d a b * W a * W b := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun c _ => ?_
          refine Finset.sum_congr rfl fun d _ => ?_
          ring
        _ = AR := hFirst
    rw [show
      (∑ a, ∑ b, ∑ c, ∑ d,
        Ric c d * (nablaP c d a b + nablaP c d b a) * W a * W b) =
        (∑ a, ∑ b, ∑ c, ∑ d,
          Ric c d * nablaP c d a b * W a * W b) +
        (∑ a, ∑ b, ∑ c, ∑ d,
          Ric c d * nablaP c d b a * W a * W b) by
        simp only [mul_add, add_mul, Finset.sum_add_distrib]]
    rw [hFirst, hSecond]
    ring
  have hJet :
      (∑ e, ∑ a, ∑ b, ∑ c,
        nablaP e a b c *
          hamiltonTestJetDU clock Ric
            (fun i j => if i = j then 1 else 0) W e a b * W c) =
        AR + (1 / (2 * clock.elapsed)) * D := by
    unfold hamiltonTestJetDU
    have hRicExpand :
        (∑ e, ∑ a, ∑ b, ∑ c,
          nablaP e a b c *
            ((1 / 2 : Real) * (Ric e a * W b - Ric e b * W a)) * W c) =
          (1 / 2 : Real) * AR - (1 / 2 : Real) * AR' := by
      calc
        (∑ e, ∑ a, ∑ b, ∑ c,
            nablaP e a b c *
              ((1 / 2 : Real) * (Ric e a * W b - Ric e b * W a)) * W c) =
            ∑ e, ∑ a, ∑ b, ∑ c,
              ((1 / 2 : Real) *
                  (nablaP e a b c * Ric e a * W b * W c) -
                (1 / 2 : Real) *
                  (nablaP e a b c * Ric e b * W a * W c)) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun c _ => ?_
          ring
        _ = (1 / 2 : Real) * AR - (1 / 2 : Real) * AR' := by
          unfold AR AR'
          simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hDeltaExpand :
        (∑ e, ∑ a, ∑ b, ∑ c,
          nablaP e a b c *
            ((1 / (4 * clock.elapsed) : Real) *
              ((if e = a then (1 : Real) else 0) * W b -
                (if e = b then (1 : Real) else 0) * W a)) * W c) =
          (1 / (4 * clock.elapsed) : Real) * AD -
            (1 / (4 * clock.elapsed) : Real) * AD' := by
      calc
        (∑ e, ∑ a, ∑ b, ∑ c,
            nablaP e a b c *
              ((1 / (4 * clock.elapsed) : Real) *
                ((if e = a then (1 : Real) else 0) * W b -
                  (if e = b then (1 : Real) else 0) * W a)) * W c) =
            ∑ e, ∑ a, ∑ b, ∑ c,
              ((1 / (4 * clock.elapsed) : Real) *
                  (nablaP e a b c *
                    (if e = a then (1 : Real) else 0) * W b * W c) -
                (1 / (4 * clock.elapsed) : Real) *
                  (nablaP e a b c *
                    (if e = b then (1 : Real) else 0) * W a * W c)) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun c _ => ?_
          ring
        _ = (1 / (4 * clock.elapsed) : Real) * AD -
              (1 / (4 * clock.elapsed) : Real) * AD' := by
          unfold AD AD'
          simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [show
      (∑ e, ∑ a, ∑ b, ∑ c,
          nablaP e a b c *
            ((1 / 2 : Real) * (Ric e a * W b - Ric e b * W a) +
              (1 / (4 * clock.elapsed) : Real) *
                ((if e = a then (1 : Real) else 0) * W b -
                  (if e = b then (1 : Real) else 0) * W a)) * W c) =
        (∑ e, ∑ a, ∑ b, ∑ c,
          nablaP e a b c *
            ((1 / 2 : Real) * (Ric e a * W b - Ric e b * W a)) * W c) +
        (∑ e, ∑ a, ∑ b, ∑ c,
          nablaP e a b c *
            ((1 / (4 * clock.elapsed) : Real) *
              ((if e = a then (1 : Real) else 0) * W b -
                (if e = b then (1 : Real) else 0) * W a)) * W c) by
          simp only [mul_add, add_mul, Finset.sum_add_distrib]]
    rw [hRicExpand, hDeltaExpand, hAR', hAD', hAD]
    ring
  rw [hReaction, hJet]
  unfold D
  field_simp [HarnackClock.elapsed_ne_zero clock]
  ring

omit [DecidableEq Idx] in
private theorem sumFive_swap12
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F b a c d e := by
  rw [Finset.sum_comm]

omit [DecidableEq Idx] in
private theorem sumFive_swap23
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a c b d e := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq Idx] in
private theorem sumFive_swap34
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b d c e := by
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq Idx] in
private theorem sumFive_swap45
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c e d := by
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq Idx] in
private theorem sumFive_neg
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, -F a b c d e) =
      -(∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e) := by
  simp only [Finset.sum_neg_distrib]

omit [DecidableEq Idx] in
private theorem hamilton_triangular_curvature_contraction
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (S : Idx -> Idx -> Real) (W : Idx -> Real)
    (hRm : Rm04Symm R) :
    (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
      R a b d c *
        ((1 / 2 : Real) * (S e a * W b - S e b * W a)) *
        ((1 / 2 : Real) * (S e c * W d - S e d * W c))) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        R a d e b * S c d * S c e * W a * W b := by
  classical
  let T := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    R a d e b * S c d * S c e * W a * W b
  let T1 := ∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
    R a b d c * S e a * W b * S e c * W d
  let T2 := ∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
    R a b d c * S e a * W b * S e d * W c
  let T3 := ∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
    R a b d c * S e b * W a * S e c * W d
  let T4 := ∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
    R a b d c * S e b * W a * S e d * W c
  have hT1 : T1 = T := by
    unfold T1 T
    rw [sumFive_swap45, sumFive_swap34, sumFive_swap23,
      sumFive_swap34, sumFive_swap45, sumFive_swap12, sumFive_swap23]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hRm.pair e b a d]
    ring
  have hT2 : T2 = -T := by
    unfold T2 T
    rw [sumFive_swap23, sumFive_swap34, sumFive_swap12, sumFive_swap23]
    rw [← sumFive_neg (fun a b c d e =>
      R a d e b * S c d * S c e * W a * W b)]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hRm.swap12 d a e b]
    ring
  have hT3 : T3 = -T := by
    unfold T3 T
    rw [sumFive_swap45, sumFive_swap34, sumFive_swap12, sumFive_swap23]
    rw [← sumFive_neg (fun a b c d e =>
      R a d e b * S c d * S c e * W a * W b)]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hRm.swap34 a d b e]
    ring
  have hT4 : T4 = T := by
    unfold T4 T
    rw [sumFive_swap34, sumFive_swap12, sumFive_swap23]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  have hExpand :
      (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
        R a b d c *
          ((1 / 2 : Real) * (S e a * W b - S e b * W a)) *
          ((1 / 2 : Real) * (S e c * W d - S e d * W c))) =
        (1 / 4 : Real) * (T1 - T2 - T3 + T4) := by
    unfold T1 T2 T3 T4
    calc
      (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
          R a b d c *
            ((1 / 2 : Real) * (S e a * W b - S e b * W a)) *
            ((1 / 2 : Real) * (S e c * W d - S e d * W c))) =
          ∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
            (1 / 4 : Real) *
              (R a b d c * S e a * W b * S e c * W d -
                R a b d c * S e a * W b * S e d * W c -
                R a b d c * S e b * W a * S e c * W d +
                R a b d c * S e b * W a * S e d * W c) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        ring
      _ = (1 / 4 : Real) *
          ((∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
              R a b d c * S e a * W b * S e c * W d) -
            (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
              R a b d c * S e a * W b * S e d * W c) -
            (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
              R a b d c * S e b * W a * S e c * W d) +
            (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
              R a b d c * S e b * W a * S e d * W c)) := by
        simp only [mul_add, mul_sub, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hExpand, hT1, hT2, hT3, hT4]
  ring

private theorem hamilton_w2_curvature_contraction
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (W : Idx -> Real)
    (hRm : Rm04Symm R)
    (hRic : forall a b, Ric a b = Ric b a)
    (hTrace : curvatureRicciTraceComponents R Ric) :
    (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
      R a b d c *
        hamiltonTestJetDU clock Ric
          (fun i j => if i = j then 1 else 0) W e a b *
        hamiltonTestJetDU clock Ric
          (fun i j => if i = j then 1 else 0) W e c d) =
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        R a d e b * Ric c d * Ric c e * W a * W b) +
      (1 / clock.elapsed) *
        (∑ a, ∑ b, ∑ c, ∑ d,
          R a c d b * Ric c d * W a * W b) +
      (1 / (4 * clock.elapsed ^ 2)) *
        ∑ a, ∑ b, Ric a b * W a * W b := by
  classical
  let q : Real := 1 / (2 * clock.elapsed)
  let S : Idx -> Idx -> Real := fun a b =>
    Ric a b + q * if a = b then 1 else 0
  let RR := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    R a d e b * Ric c d * Ric c e * W a * W b
  let C := ∑ a, ∑ b, ∑ c, ∑ d,
    R a c d b * Ric c d * W a * W b
  let T := ∑ a, ∑ b, Ric a b * W a * W b
  let Q1 := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    R a d e b * Ric c d * (if c = e then (1 : Real) else 0) * W a * W b
  let Q2 := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    R a d e b * (if c = d then (1 : Real) else 0) * Ric c e * W a * W b
  let Q0 := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    R a d e b * (if c = d then (1 : Real) else 0) *
      (if c = e then (1 : Real) else 0) * W a * W b
  have hDU (e a b : Idx) :
      hamiltonTestJetDU clock Ric
          (fun i j => if i = j then 1 else 0) W e a b =
        (1 / 2 : Real) * (S e a * W b - S e b * W a) := by
    unfold hamiltonTestJetDU S q
    field_simp [HarnackClock.elapsed_ne_zero clock]
    ring
  have hQ1 : Q1 = C := by
    unfold Q1 C
    calc
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          R a d e b * Ric c d * (if c = e then (1 : Real) else 0) * W a * W b) =
          ∑ a, ∑ b, ∑ c, ∑ d, R a d c b * Ric c d * W a * W b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        let G : Idx -> Real := fun e =>
          R a d e b * Ric c d * (if c = e then (1 : Real) else 0) * W a * W b
        change (∑ e, G e) = R a d c b * Ric c d * W a * W b
        calc
          (∑ e, G e) = G c := by
            refine Finset.sum_eq_single c ?_ ?_
            · intro e _ he
              unfold G
              simp [he.symm]
            · simp
          _ = _ := by simp [G]
      _ = ∑ a, ∑ b, ∑ c, ∑ d,
          R a c d b * Ric c d * W a * W b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hRic d c]
  have hQ2 : Q2 = C := by
    unfold Q2 C
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    let G : Idx -> Real := fun d => ∑ e,
      R a d e b * (if c = d then (1 : Real) else 0) * Ric c e * W a * W b
    change (∑ d, G d) = ∑ d, R a c d b * Ric c d * W a * W b
    calc
      (∑ d, G d) = G c := by
        refine Finset.sum_eq_single c ?_ ?_
        · intro d _ hd
          unfold G
          simp [hd.symm]
        · simp
      _ = ∑ d, R a c d b * Ric c d * W a * W b := by simp [G]
  have hQ0 : Q0 = T := by
    unfold Q0 T
    calc
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          R a d e b * (if c = d then (1 : Real) else 0) *
            (if c = e then (1 : Real) else 0) * W a * W b) =
          ∑ a, ∑ b, ∑ c, R a c c b * W a * W b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        let G : Idx -> Real := fun d => ∑ e,
          R a d e b * (if c = d then (1 : Real) else 0) *
            (if c = e then (1 : Real) else 0) * W a * W b
        change (∑ d, G d) = R a c c b * W a * W b
        calc
          (∑ d, G d) = G c := by
            refine Finset.sum_eq_single c ?_ ?_
            · intro d _ hd
              unfold G
              simp [hd.symm]
            · simp
          _ = R a c c b * W a * W b := by
            unfold G
            simp
      _ = ∑ a, ∑ b, Ric a b * W a * W b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        rw [show (∑ c, R a c c b) = Ric a b by
          calc
            (∑ c, R a c c b) = ∑ c, R c b a c := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [hRm.pair c b a c]
            _ = Ric b a := hTrace b a
            _ = Ric a b := hRic b a]
  have hTri :
      (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
        R a b d c *
          hamiltonTestJetDU clock Ric
            (fun i j => if i = j then 1 else 0) W e a b *
          hamiltonTestJetDU clock Ric
            (fun i j => if i = j then 1 else 0) W e c d) =
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          R a d e b * S c d * S c e * W a * W b := by
    simp_rw [hDU]
    exact hamilton_triangular_curvature_contraction R S W hRm
  have hExpand :
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        R a d e b * S c d * S c e * W a * W b) =
        RR + q * Q1 + q * Q2 + q ^ 2 * Q0 := by
    unfold S
    calc
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          R a d e b *
            (Ric c d + q * if c = d then 1 else 0) *
            (Ric c e + q * if c = e then 1 else 0) * W a * W b) =
          ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
            (R a d e b * Ric c d * Ric c e * W a * W b +
              q * (R a d e b * Ric c d *
                (if c = e then (1 : Real) else 0) * W a * W b) +
              q * (R a d e b * (if c = d then (1 : Real) else 0) *
                Ric c e * W a * W b) +
              q ^ 2 * (R a d e b * (if c = d then (1 : Real) else 0) *
                (if c = e then (1 : Real) else 0) * W a * W b)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        ring
      _ = RR + q * Q1 + q * Q2 + q ^ 2 * Q0 := by
        unfold RR Q1 Q2 Q0
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hTri, hExpand, hQ1, hQ2, hQ0]
  unfold RR C T q
  field_simp [HarnackClock.elapsed_ne_zero clock]
  ring

omit [DecidableEq Idx] in
private theorem hamilton_w2_p_square
    (P : Idx -> Idx -> Idx -> Real) (W : Idx -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      P c d a * P c d b * W a * W b) =
      ∑ a, ∑ b, (∑ c, P a b c * W c) ^ 2 := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d,
        P c d a * P c d b * W a * W b) =
        ∑ a, ∑ b, ∑ c, ∑ d,
          P a b c * W c * (P a b d * W d) := by
      rw [sumFour_rotate_pairs]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    _ = ∑ a, ∑ b, (∑ c, P a b c * W c) ^ 2 := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]

private theorem covector_evolution_contraction
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (W : Idx -> Real)
    (hRm : Rm04Symm R)
    (hRic : forall a b, Ric a b = Ric b a)
    (hTrace : curvatureRicciTraceComponents R Ric)
    (hNablaPSkew : forall e a b c, nablaP e a b c = -nablaP e b a c) :
    (∑ a, ∑ b,
        hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
          (fun i j => ∑ e, nablaP e e i j) a b * W a * W b) +
      2 * (∑ a, ∑ b,
        hamiltonMComponent clock R Ric (fun i j => ∑ e, nablaP e e i j) a b *
          ((1 / clock.elapsed) * W a) * W b) -
      4 * (∑ e, ∑ a, ∑ b, ∑ c,
        nablaP e a b c *
          hamiltonTestJetDU clock Ric
            (fun i j => if i = j then 1 else 0) W e a b * W c) -
      2 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
        R a b d c *
          hamiltonTestJetDU clock Ric
            (fun i j => if i = j then 1 else 0) W e a b *
          hamiltonTestJetDU clock Ric
            (fun i j => if i = j then 1 else 0) W e c d) =
      hamiltonBlockPreSquareM
        (fun a b c d => R a b d c)
        (hamiltonPComponent nablaRic)
        (hamiltonMComponent clock R Ric
          (fun i j => ∑ e, nablaP e e i j)) W := by
  classical
  let P := hamiltonPComponent nablaRic
  let divP : Idx -> Idx -> Real := fun a b => ∑ e, nablaP e e a b
  let M := hamiltonMComponent clock R Ric divP
  let RM := ∑ a, ∑ b, ∑ c, ∑ d,
    R a c d b * M c d * W a * W b
  let D := ∑ a, ∑ b, divP a b * W a * W b
  let C := ∑ a, ∑ b, ∑ c, ∑ d,
    R a c d b * Ric c d * W a * W b
  let T := ∑ a, ∑ b, Ric a b * W a * W b
  let Der := ∑ a, ∑ b, ∑ c, ∑ d,
    Ric c d * (nablaP c d a b + nablaP c d b a) * W a * W b
  let PS := ∑ a, ∑ b, ∑ c, ∑ d,
    P c d a * P c d b * W a * W b
  let PP := ∑ a, ∑ b, ∑ c, ∑ d,
    P a c d * P b d c * W a * W b
  let RR := ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    R a d e b * Ric c d * Ric c e * W a * W b
  let J := ∑ e, ∑ a, ∑ b, ∑ c,
    nablaP e a b c *
      hamiltonTestJetDU clock Ric
        (fun i j => if i = j then 1 else 0) W e a b * W c
  let A := ∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
    R a b d c *
      hamiltonTestJetDU clock Ric
        (fun i j => if i = j then 1 else 0) W e a b *
      hamiltonTestJetDU clock Ric
        (fun i j => if i = j then 1 else 0) W e c d
  have hReaction :
      (∑ a, ∑ b,
        hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP divP a b *
          W a * W b) =
        2 * RM + 2 * Der + PS - 2 * PP + 2 * RR -
          (1 / (2 * clock.elapsed ^ 2)) * T := by
    have hShift :
        (∑ a, ∑ b,
          (1 / (2 * clock.elapsed ^ 2)) * Ric a b * W a * W b) =
          (1 / (2 * clock.elapsed ^ 2)) * T := by
      unfold T
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    unfold hamiltonMEvolutionReactionComponent RM Der PS PP RR P M
    calc
      (∑ a, ∑ b,
          (2 * ∑ c, ∑ d,
                R a c d b * hamiltonMComponent clock R Ric divP c d +
            2 * ∑ c, ∑ d,
                Ric c d * (nablaP c d a b + nablaP c d b a) +
            (∑ c, ∑ d,
              hamiltonPComponent nablaRic c d a *
                hamiltonPComponent nablaRic c d b) -
            2 * ∑ c, ∑ d,
              hamiltonPComponent nablaRic a c d *
                hamiltonPComponent nablaRic b d c +
            2 * ∑ c, ∑ d, ∑ e,
              Ric c d * Ric c e * R a d e b -
            (1 / (2 * clock.elapsed ^ 2)) * Ric a b) * W a * W b) =
          ∑ a, ∑ b, (
            (2 * ∑ c, ∑ d,
                R a c d b * hamiltonMComponent clock R Ric divP c d * W a * W b) +
            (2 * ∑ c, ∑ d,
                Ric c d * (nablaP c d a b + nablaP c d b a) * W a * W b) +
            (∑ c, ∑ d,
              hamiltonPComponent nablaRic c d a *
                hamiltonPComponent nablaRic c d b * W a * W b) -
            (2 * ∑ c, ∑ d,
              hamiltonPComponent nablaRic a c d *
                hamiltonPComponent nablaRic b d c * W a * W b) +
            (2 * ∑ c, ∑ d, ∑ e,
              R a d e b * Ric c d * Ric c e * W a * W b) -
            (1 / (2 * clock.elapsed ^ 2)) * Ric a b * W a * W b) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        have hRRPoint :
            (∑ c, ∑ d, ∑ e,
              Ric c d * Ric c e * R a d e b) =
              ∑ c, ∑ d, ∑ e,
                R a d e b * Ric c d * Ric c e := by
          refine Finset.sum_congr rfl fun c _ => ?_
          refine Finset.sum_congr rfl fun d _ => ?_
          refine Finset.sum_congr rfl fun e _ => ?_
          ring
        rw [hRRPoint]
        simp only [← Finset.sum_mul]
        ring
      _ =
          2 * (∑ a, ∑ b, ∑ c, ∑ d,
            R a c d b * hamiltonMComponent clock R Ric divP c d * W a * W b) +
          2 * (∑ a, ∑ b, ∑ c, ∑ d,
            Ric c d * (nablaP c d a b + nablaP c d b a) * W a * W b) +
          (∑ a, ∑ b, ∑ c, ∑ d,
            hamiltonPComponent nablaRic c d a *
              hamiltonPComponent nablaRic c d b * W a * W b) -
          2 * (∑ a, ∑ b, ∑ c, ∑ d,
            hamiltonPComponent nablaRic a c d *
              hamiltonPComponent nablaRic b d c * W a * W b) +
          2 * (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
            R a d e b * Ric c d * Ric c e * W a * W b) -
          (1 / (2 * clock.elapsed ^ 2)) * T := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
        rw [hShift]
  have hClock :
      2 * (∑ a, ∑ b,
        M a b * ((1 / clock.elapsed) * W a) * W b) =
        2 * (1 / clock.elapsed) * D +
          2 * (1 / clock.elapsed) * C +
          (1 / clock.elapsed ^ 2) * T := by
    have hCGrouped :
        (∑ a, ∑ b,
          (∑ c, ∑ d, R a c d b * Ric c d) * W a * W b) = C := by
      unfold C
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
    have hPoint (a b : Idx) :
        M a b * ((1 / clock.elapsed) * W a) * W b =
          (1 / clock.elapsed) * (divP a b * W a * W b) +
          (1 / clock.elapsed) *
            ((∑ c, ∑ d, R a c d b * Ric c d) * W a * W b) +
          (1 / (2 * clock.elapsed ^ 2)) * (Ric a b * W a * W b) := by
      unfold M divP hamiltonMComponent hamiltonCurvatureRicciComponent
      field_simp [HarnackClock.elapsed_ne_zero clock]
    calc
      2 * (∑ a, ∑ b, M a b * ((1 / clock.elapsed) * W a) * W b) =
          2 * (∑ a, ∑ b,
            ((1 / clock.elapsed) * (divP a b * W a * W b) +
              (1 / clock.elapsed) *
                ((∑ c, ∑ d, R a c d b * Ric c d) * W a * W b) +
              (1 / (2 * clock.elapsed ^ 2)) *
                (Ric a b * W a * W b))) := by
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        exact hPoint a b
      _ =
          2 * (1 / clock.elapsed) *
              (∑ a, ∑ b, divP a b * W a * W b) +
            2 * (1 / clock.elapsed) *
              (∑ a, ∑ b,
                (∑ c, ∑ d, R a c d b * Ric c d) * W a * W b) +
            (1 / clock.elapsed ^ 2) *
              ∑ a, ∑ b, Ric a b * W a * W b := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        field_simp [HarnackClock.elapsed_ne_zero clock]
      _ = 2 * (1 / clock.elapsed) * D +
            2 * (1 / clock.elapsed) * C +
            (1 / clock.elapsed ^ 2) * T := by
        rw [hCGrouped]
  have hDerivative : 2 * Der + 2 * (1 / clock.elapsed) * D - 4 * J = 0 := by
    unfold Der D J divP
    exact hamilton_w2_derivative_terms clock Ric nablaP W hNablaPSkew
  have hCurvature :
      A = RR + (1 / clock.elapsed) * C +
        (1 / (4 * clock.elapsed ^ 2)) * T := by
    unfold A RR C T
    exact hamilton_w2_curvature_contraction clock R Ric W hRm hRic hTrace
  have hPS : PS = ∑ a, ∑ b, (∑ c, P a b c * W c) ^ 2 := by
    unfold PS
    exact hamilton_w2_p_square P W
  change
    (∑ a, ∑ b,
        hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP divP a b *
          W a * W b) +
      2 * (∑ a, ∑ b, M a b * ((1 / clock.elapsed) * W a) * W b) -
      4 * J - 2 * A =
      2 * RM - 2 * PP + (∑ a, ∑ b, (∑ c, P a b c * W c) ^ 2)
  rw [hReaction, hClock, hCurvature, hPS]
  linear_combination hDerivative

end Covector

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

theorem hamiltonBlockRawProduct_eq_pre_square
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (U : Idx -> Idx -> Real) (W : Idx -> Real)
    (hRm : Rm04Symm R)
    (hNablaRm : forall e, Rm04PairSymm (nablaR e))
    (hRic : forall a b, Ric a b = Ric b a)
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (hTrace : curvatureRicciTraceComponents R Ric)
    (hContract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hNablaPSkew : forall e a b c, nablaP e a b c = -nablaP e b a c)
    (hU : forall a b, U a b = -U b a) :
    hamiltonBlockRawProduct
        (fun a b c d => R a b d c)
        (hamiltonPComponent nablaRic)
        (hamiltonMComponent clock R Ric (fun a b => ∑ e, nablaP e e a b))
        (fun a b c d => hamiltonRmReactionComponent R a b d c)
        (hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic)
        (hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
          (fun a b => ∑ e, nablaP e e a b))
        (fun e a b c d => nablaR e a b d c) nablaP
        (hamiltonTestJetDU clock Ric (fun a b => if a = b then 1 else 0) W)
        (fun a => (1 / clock.elapsed) * W a) U W =
      hamiltonBlockPreSquare
        (fun a b c d => R a b d c)
        (hamiltonPComponent nablaRic)
        (hamiltonMComponent clock R Ric (fun a b => ∑ e, nablaP e e a b)) U W := by
  let K := fun a b c d => R a b d c
  let P := hamiltonPComponent nablaRic
  let M := hamiltonMComponent clock R Ric (fun a b => ∑ e, nablaP e e a b)
  let LK := fun a b c d => hamiltonRmReactionComponent R a b d c
  let LP := hamiltonPEvolutionReactionComponent R Ric nablaR nablaRic
  let LM := hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP
    (fun a b => ∑ e, nablaP e e a b)
  let DK := fun e a b c d => nablaR e a b d c
  let DU := hamiltonTestJetDU clock Ric (fun a b => if a = b then 1 else 0) W
  let LW := fun a => (1 / clock.elapsed) * W a
  let U2 := ∑ a, ∑ b, ∑ c, ∑ d, LK a b c d * U a b * U c d
  let UW :=
    2 * (∑ a, ∑ b, ∑ c, LP a b c * U a b * W c) +
    2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * LW c) -
    4 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
      DK e a b c d * DU e a b * U c d)
  let W2 :=
    (∑ a, ∑ b, LM a b * W a * W b) +
    2 * (∑ a, ∑ b, M a b * LW a * W b) -
    4 * (∑ e, ∑ a, ∑ b, ∑ c,
      nablaP e a b c * DU e a b * W c) -
    2 * (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
      K a b c d * DU e a b * DU e c d)
  have hU2 : U2 = hamiltonBlockPreSquareK K U := by
    unfold U2 LK K hamiltonBlockPreSquareK
    exact UQuadratic.curvature_reaction_contraction R U hRm hU
  have hUW : UW = hamiltonBlockPreSquareP K P U W := by
    unfold UW LP P LW DU K DK
    exact Mixed.mixed_evolution_contraction clock R Ric nablaR nablaRic U W hRm
      hNablaRm hNablaRic hContract hU
  have hW2 : W2 = hamiltonBlockPreSquareM K P M W := by
    unfold W2 LM M LW DU K P
    exact Covector.covector_evolution_contraction clock R Ric nablaRic nablaP W
      hRm hRic hTrace hNablaPSkew
  change hamiltonBlockRawProduct K P M LK LP LM DK nablaP DU LW U W =
    hamiltonBlockPreSquare K P M U W
  calc
    hamiltonBlockRawProduct K P M LK LP LM DK nablaP DU LW U W =
        U2 + UW + W2 := by
      unfold hamiltonBlockRawProduct U2 UW W2
      ring
    _ = hamiltonBlockPreSquareK K U +
        hamiltonBlockPreSquareP K P U W +
        hamiltonBlockPreSquareM K P M W := by rw [hU2, hUW, hW2]
    _ = hamiltonBlockPreSquare K P M U W :=
      (hamiltonBlockPreSquare_eq_split K P M U W).symm

end DifferentialGeometry.PDE.RicciFlow
