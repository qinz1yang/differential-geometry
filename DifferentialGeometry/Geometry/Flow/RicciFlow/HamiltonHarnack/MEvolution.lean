import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Reduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.HeatCommutator
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.PEvolution

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx]

def hamiltonBComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real) (a b c d : Idx) : Real :=
  -(∑ e : Idx, ∑ f : Idx, R a e b f * R c e d f)

def hamiltonCurvatureCommutatorComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (c d i j k l : Idx) : Real :=
  ∑ p : Idx,
    (R c d p i * R p j k l + R c d p j * R i p k l +
      R c d p k * R i j p l + R c d p l * R i j k p)

private theorem sum_cycle_four
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx, F a b c d) =
      ∑ b : Idx, ∑ c : Idx, ∑ d : Idx, ∑ a : Idx, F a b c d := by
  calc
    (∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx, F a b c d) =
        ∑ b : Idx, ∑ a : Idx, ∑ c : Idx, ∑ d : Idx, F a b c d :=
      Finset.sum_comm
    _ = ∑ b : Idx, ∑ c : Idx, ∑ a : Idx, ∑ d : Idx, F a b c d := by
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b : Idx, ∑ c : Idx, ∑ d : Idx, ∑ a : Idx, F a b c d := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem hamiltonCurvatureCommutator_contraction
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (hRm : Rm04Symm R)
    (hRic : forall a b, Ric a b = Ric b a)
    (hTrace : forall a d, (∑ e : Idx, R e a d e) = Ric a d)
    (a b : Idx) :
    -2 * ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        Ric d e * hamiltonCurvatureCommutatorComponent R c d c a e b =
      2 * ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        Ric c d * Ric c e * R a d e b +
      2 * ∑ c : Idx, ∑ d : Idx,
        Ric c d *
          (hamiltonBComponent R a b c d + hamiltonBComponent R a c b d -
            hamiltonBComponent R a c d b - hamiltonBComponent R a d c b) := by
  classical
  have hTraceTerm :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * (R c d p c * R p a e b)) =
        -(∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          Ric c d * Ric c e * R a d e b) := by
    calc
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * (R c d p c * R p a e b)) =
          ∑ d : Idx, ∑ e : Idx, ∑ p : Idx, ∑ c : Idx,
            Ric d e * (R c d p c * R p a e b) :=
        sum_cycle_four (fun c d e p => Ric d e * (R c d p c * R p a e b))
      _ = ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * Ric d p * R p a e b := by
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun p _ => ?_
        calc
          (∑ c : Idx, Ric d e * (R c d p c * R p a e b)) =
              ∑ c : Idx, (Ric d e * R c d p c) * R p a e b := by
            refine Finset.sum_congr rfl fun c _ => ?_
            ring_nf
          _ = (∑ c : Idx, Ric d e * R c d p c) * R p a e b := by
            rw [Finset.sum_mul]
          _ = (Ric d e * ∑ c : Idx, R c d p c) * R p a e b := by
            rw [Finset.mul_sum]
          _ = _ := by rw [hTrace d p]
      _ = ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          -(Ric d e * Ric d p * R a p e b) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hRm.swap12 p a e b]
        ring_nf
      _ = -(∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          Ric c d * Ric c e * R a d e b) := by
        simp only [Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        ring_nf
  have hSecondTerm :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * (R c d p a * R c p e b)) =
        (∑ c : Idx, ∑ d : Idx,
            Ric c d * (-hamiltonBComponent R a c b d)) -
          ∑ c : Idx, ∑ d : Idx,
            Ric c d * (-hamiltonBComponent R a c d b) := by
    have hPoint (d e : Idx) :
        (∑ c : Idx, ∑ p : Idx, R c d p a * R c p e b) =
          (∑ u : Idx, ∑ v : Idx, R a u d v * R b u e v) -
            ∑ u : Idx, ∑ v : Idx, R a u d v * R e u b v := by
      have hBianchi (u v : Idx) :
          R b u e v - R e u b v = -R e b u v := by
        have h := hRm.bianchi b u e v
        rw [hRm.swap12 e u b v]
        linarith
      calc
        (∑ c : Idx, ∑ p : Idx, R c d p a * R c p e b) =
            ∑ c : Idx, ∑ p : Idx,
              -(R a p d c * R e b p c) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hRm.pair c d p a, hRm.swap12 p a c d,
            hRm.swap34 a p c d, hRm.pair c p e b,
            hRm.swap34 e b c p]
          ring_nf
        _ = -(∑ u : Idx, ∑ v : Idx,
            R a u d v * R e b u v) := by
          simp only [Finset.sum_neg_distrib]
          congr 1
          rw [Finset.sum_comm]
        _ = (∑ u : Idx, ∑ v : Idx, R a u d v * R b u e v) -
            ∑ u : Idx, ∑ v : Idx, R a u d v * R e u b v := by
          symm
          calc
            (∑ u : Idx, ∑ v : Idx, R a u d v * R b u e v) -
                ∑ u : Idx, ∑ v : Idx, R a u d v * R e u b v =
              ∑ u : Idx, ∑ v : Idx,
                (R a u d v * R b u e v - R a u d v * R e u b v) := by
              simp only [Finset.sum_sub_distrib]
            _ = ∑ u : Idx, ∑ v : Idx,
                -(R a u d v * R e b u v) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              refine Finset.sum_congr rfl fun v _ => ?_
              calc
                R a u d v * R b u e v - R a u d v * R e u b v =
                    R a u d v * (R b u e v - R e u b v) := by ring_nf
                _ = _ := by rw [hBianchi u v]; ring_nf
            _ = -(∑ u : Idx, ∑ v : Idx,
                R a u d v * R e b u v) := by
              simp only [Finset.sum_neg_distrib]
    calc
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * (R c d p a * R c p e b)) =
          ∑ d : Idx, ∑ e : Idx, Ric d e *
            (∑ c : Idx, ∑ p : Idx, R c d p a * R c p e b) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
      _ = ∑ d : Idx, ∑ e : Idx, Ric d e *
          ((∑ u : Idx, ∑ v : Idx, R a u d v * R b u e v) -
            ∑ u : Idx, ∑ v : Idx, R a u d v * R e u b v) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hPoint d e]
      _ = _ := by
        simp only [hamiltonBComponent, neg_neg, mul_sub,
          Finset.sum_sub_distrib]
  have hThirdTerm :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * (R c d p e * R c a p b)) =
        ∑ c : Idx, ∑ d : Idx,
          Ric c d * (-hamiltonBComponent R a b c d) := by
    have hPoint (d e : Idx) :
        (∑ c : Idx, ∑ p : Idx, R c d p e * R c a p b) =
          ∑ u : Idx, ∑ v : Idx, R a u b v * R d u e v := by
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hRm.swap12 c d p e, hRm.swap34 d c p e,
        hRm.swap12 c a p b, hRm.swap34 a c p b]
      ring_nf
    calc
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * (R c d p e * R c a p b)) =
          ∑ d : Idx, ∑ e : Idx, Ric d e *
            (∑ c : Idx, ∑ p : Idx, R c d p e * R c a p b) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
      _ = ∑ d : Idx, ∑ e : Idx, Ric d e *
          (∑ u : Idx, ∑ v : Idx, R a u b v * R d u e v) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hPoint d e]
      _ = _ := by simp only [hamiltonBComponent, neg_neg]
  have hBsym :
      (∑ c : Idx, ∑ d : Idx,
          Ric c d * hamiltonBComponent R a c d b) =
        ∑ c : Idx, ∑ d : Idx,
          Ric c d * hamiltonBComponent R a d c b := by
    calc
      (∑ c : Idx, ∑ d : Idx,
          Ric c d * hamiltonBComponent R a c d b) =
          ∑ d : Idx, ∑ c : Idx,
            Ric c d * hamiltonBComponent R a c d b := Finset.sum_comm
      _ = ∑ c : Idx, ∑ d : Idx,
          Ric c d * hamiltonBComponent R a d c b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hRic d c]
  have hFourthTerm :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * (R c d p b * R c a e p)) =
        -(∑ c : Idx, ∑ d : Idx,
          Ric c d * (-hamiltonBComponent R a c d b)) := by
    have hPoint (d e : Idx) :
        (∑ c : Idx, ∑ p : Idx, R c d p b * R c a e p) =
          -(∑ u : Idx, ∑ v : Idx, R a u e v * R d u b v) := by
      calc
        (∑ c : Idx, ∑ p : Idx, R c d p b * R c a e p) =
            ∑ c : Idx, ∑ p : Idx,
              -(R a c e p * R d c b p) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hRm.swap12 c d p b, hRm.swap34 d c p b,
            hRm.swap12 c a e p]
          ring_nf
        _ = _ := by simp only [Finset.sum_neg_distrib]
    calc
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * (R c d p b * R c a e p)) =
          ∑ d : Idx, ∑ e : Idx, Ric d e *
            (∑ c : Idx, ∑ p : Idx, R c d p b * R c a e p) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
      _ = ∑ d : Idx, ∑ e : Idx, Ric d e *
          (-(∑ u : Idx, ∑ v : Idx, R a u e v * R d u b v)) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hPoint d e]
      _ = -(∑ c : Idx, ∑ d : Idx, Ric c d *
          (∑ u : Idx, ∑ v : Idx, R a u c v * R d u b v)) := by
        simp only [mul_neg, Finset.sum_neg_distrib]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hRic d c]
      _ = _ := by simp only [hamiltonBComponent, neg_neg]
  have hSplit :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          Ric d e * hamiltonCurvatureCommutatorComponent R c d c a e b) =
        (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * (R c d p c * R p a e b)) +
        (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * (R c d p a * R c p e b)) +
        (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * (R c d p e * R c a p b)) +
        (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ p : Idx,
          Ric d e * (R c d p b * R c a e p)) := by
    simp only [hamiltonCurvatureCommutatorComponent, Finset.mul_sum,
      mul_add, Finset.sum_add_distrib]
  rw [hSplit, hTraceTerm, hSecondTerm, hThirdTerm, hFourthTerm]
  simp only [mul_add, mul_sub, neg_mul, mul_neg,
    Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  linear_combination (norm := ring_nf) -2 * hBsym

def differentiatedCurvatureDivergenceComponents
    (nabla2R : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall d a e b,
    (∑ c : Idx, nabla2R d c c a e b) = nablaP d b e a

section

variable [DecidableEq Idx]

theorem hamilton_contracted_nabla2_curvature
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nabla2R : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (hRm : Rm04Symm R)
    (hRic : forall a b, Ric a b = Ric b a)
    (hTrace : forall a d, (∑ e : Idx, R e a d e) = Ric a d)
    (hComm : covariantTensorSecondDerivativeCommutatorComponents R
      (fun slots : Fin 4 -> Idx => R (slots 0) (slots 1) (slots 2) (slots 3))
      (fun c d (slots : Fin 4 -> Idx) =>
        nabla2R c d (slots 0) (slots 1) (slots 2) (slots 3)))
    (hDiv : differentiatedCurvatureDivergenceComponents nabla2R nablaP)
    (hNablaPSkew : forall d a b c, nablaP d a b c = -nablaP d b a c)
    (a b : Idx) :
    -2 * ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        Ric d e * nabla2R c d c a e b =
      2 * ∑ c : Idx, ∑ d : Idx, Ric c d * nablaP c d b a +
      2 * ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        Ric c d * Ric c e * R a d e b +
      2 * ∑ c : Idx, ∑ d : Idx,
        Ric c d *
          (hamiltonBComponent R a b c d + hamiltonBComponent R a c b d -
            hamiltonBComponent R a c d b - hamiltonBComponent R a d c b) := by
  classical
  have hCommSlots (c d i j k l : Idx) :
      nabla2R c d i j k l - nabla2R d c i j k l =
        hamiltonCurvatureCommutatorComponent R c d i j k l := by
    have h := covariantTensorSecondDerivativeCommutatorComponents_eq_slots
      R
      (fun slots : Fin 4 -> Idx => R (slots 0) (slots 1) (slots 2) (slots 3))
      (fun c d (slots : Fin 4 -> Idx) =>
        nabla2R c d (slots 0) (slots 1) (slots 2) (slots 3))
      hComm hRm.swap34 c d
      (fun q : Fin 4 =>
        if q = 0 then i else if q = 1 then j else if q = 2 then k else l)
    simpa [Fin.sum_univ_four, hamiltonCurvatureCommutatorComponent,
      Finset.sum_add_distrib] using h
  have hSplit :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          Ric d e * nabla2R c d c a e b) =
        (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          Ric d e * nabla2R d c c a e b) +
        ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          Ric d e * hamiltonCurvatureCommutatorComponent R c d c a e b := by
    calc
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          Ric d e * nabla2R c d c a e b) =
          ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            Ric d e *
              (nabla2R d c c a e b +
                hamiltonCurvatureCommutatorComponent R c d c a e b) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← hCommSlots c d c a e b]
        ring_nf
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib]
  have hDivergence :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          Ric d e * nabla2R d c c a e b) =
        -(∑ c : Idx, ∑ d : Idx, Ric c d * nablaP c d b a) := by
    calc
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          Ric d e * nabla2R d c c a e b) =
          ∑ d : Idx, ∑ e : Idx, Ric d e *
            (∑ c : Idx, nabla2R d c c a e b) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
      _ = ∑ d : Idx, ∑ e : Idx,
          Ric d e * nablaP d b e a := by
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hDiv d a e b]
      _ = ∑ d : Idx, ∑ e : Idx,
          -(Ric d e * nablaP d e b a) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hNablaPSkew d b e a]
        ring_nf
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hCurvature := hamiltonCurvatureCommutator_contraction
    R Ric hRm hRic hTrace a b
  rw [hSplit, hDivergence]
  linear_combination (norm := ring_nf) hCurvature

end

theorem hamilton_divP_gradient_reaction_regroup
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (hNablaRSkewFirst : forall d a b c e,
      nablaR d a b c e = -nablaR d b a c e)
    (hcontract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (a b : Idx) :
    2 * ((∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        nablaR c c d e a * hamiltonPComponent nablaRic d e b) +
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        nablaR c c d e b * hamiltonPComponent nablaRic d a e) +
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        nablaR c a d e b * hamiltonPComponent nablaRic c d e) -
      ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        nablaRic c d e * nablaR d c a e b) =
      (∑ c : Idx, ∑ d : Idx,
        hamiltonPComponent nablaRic c d a * hamiltonPComponent nablaRic c d b) -
      2 * ∑ c : Idx, ∑ d : Idx,
        hamiltonPComponent nablaRic a c d * hamiltonPComponent nablaRic b d c +
      2 * ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        nablaR e a c d b * nablaRic e c d := by
  classical
  have sum_swap_two (F : Idx -> Idx -> Real) :
      (∑ c : Idx, ∑ d : Idx, F c d) =
        ∑ c : Idx, ∑ d : Idx, F d c := by
    exact Finset.sum_comm.trans (by rfl)
  have sum_cycle_three (F : Idx -> Idx -> Idx -> Real) :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, F c d e) =
        ∑ c : Idx, ∑ d : Idx, ∑ e : Idx, F e c d := by
    calc
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, F c d e) =
          ∑ d : Idx, ∑ c : Idx, ∑ e : Idx, F c d e := Finset.sum_comm
      _ = ∑ d : Idx, ∑ e : Idx, ∑ c : Idx, F c d e := by
        refine Finset.sum_congr rfl fun d _ => Finset.sum_comm
      _ = _ := by rfl
  let P := hamiltonPComponent nablaRic
  have hPSkew (i j k : Idx) : P i j k = -P j i k := by
    simp only [P, hamiltonPComponent]
    ring_nf
  have hPCyclic (i j k : Idx) : P i j k + P j k i + P k i j = 0 := by
    simp only [P, hamiltonPComponent]
    rw [hNablaRic i j k, hNablaRic j k i, hNablaRic k i j]
    ring_nf
  have hDivR (d e i : Idx) :
      (∑ c : Idx, nablaR c c d e i) = P i e d := by
    rw [hcontract d i e]
    simp only [P, hamiltonPComponent]
    rw [hNablaRic i d e, hNablaRic e d i]
  have hXswap :
      (∑ c : Idx, ∑ d : Idx, P a d c * P c d b) =
        -(∑ c : Idx, ∑ d : Idx, P a c d * P c d b) := by
    calc
      (∑ c : Idx, ∑ d : Idx, P a d c * P c d b) =
          ∑ c : Idx, ∑ d : Idx, P a c d * P d c b :=
        sum_swap_two (fun c d => P a d c * P c d b)
      _ = ∑ c : Idx, ∑ d : Idx, -(P a c d * P c d b) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hPSkew d c b]
        ring_nf
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hXdiff :
      (∑ c : Idx, ∑ d : Idx, P a c d * P c d b) -
          (∑ c : Idx, ∑ d : Idx, P a d c * P c d b) =
        -(∑ c : Idx, ∑ d : Idx, P c d a * P c d b) := by
    calc
      (∑ c : Idx, ∑ d : Idx, P a c d * P c d b) -
          (∑ c : Idx, ∑ d : Idx, P a d c * P c d b) =
        ∑ c : Idx, ∑ d : Idx,
          (P a c d - P a d c) * P c d b := by
            simp only [sub_mul, Finset.sum_sub_distrib]
      _ = ∑ c : Idx, ∑ d : Idx,
          -(P c d a * P c d b) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        have h := hPCyclic a c d
        rw [hPSkew d a c] at h
        have : P a c d - P a d c = -P c d a := by linarith
        rw [this]
        ring_nf
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hFirstP :
      2 * (∑ c : Idx, ∑ d : Idx, P a c d * P d c b) =
        ∑ c : Idx, ∑ d : Idx, P c d a * P c d b := by
    have hSkewSum :
        (∑ c : Idx, ∑ d : Idx, P a c d * P d c b) =
          -(∑ c : Idx, ∑ d : Idx, P a c d * P c d b) := by
      calc
        (∑ c : Idx, ∑ d : Idx, P a c d * P d c b) =
            ∑ c : Idx, ∑ d : Idx, -(P a c d * P c d b) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [hPSkew d c b]
          ring_nf
        _ = _ := by simp only [Finset.sum_neg_distrib]
    linear_combination (norm := ring_nf) -hXdiff - hXswap + 2 * hSkewSum
  have hFirst :
      2 * (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          nablaR c c d e a * P d e b) =
        ∑ c : Idx, ∑ d : Idx, P c d a * P c d b := by
    calc
      2 * (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          nablaR c c d e a * P d e b) =
        2 * ∑ d : Idx, ∑ e : Idx,
          (∑ c : Idx, nablaR c c d e a) * P d e b := by
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.sum_mul]
      _ = 2 * ∑ d : Idx, ∑ e : Idx, P a e d * P d e b := by
        refine congrArg (2 * ·) ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hDivR d e a]
      _ = 2 * ∑ c : Idx, ∑ d : Idx, P a c d * P d c b := by
        congr 1
        exact sum_swap_two (fun d e => P a e d * P d e b)
      _ = _ := hFirstP
  have hSecond :
      2 * (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          nablaR c c d e b * P d a e) =
        -2 * ∑ c : Idx, ∑ d : Idx, P a c d * P b d c := by
    calc
      2 * (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          nablaR c c d e b * P d a e) =
        2 * ∑ d : Idx, ∑ e : Idx,
          (∑ c : Idx, nablaR c c d e b) * P d a e := by
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.sum_mul]
      _ = 2 * ∑ d : Idx, ∑ e : Idx, P b e d * P d a e := by
        refine congrArg (2 * ·) ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hDivR d e b]
      _ = -2 * ∑ d : Idx, ∑ e : Idx, P b e d * P a d e := by
        have hSkewSum :
            (∑ d : Idx, ∑ e : Idx, P b e d * P d a e) =
              -(∑ d : Idx, ∑ e : Idx, P b e d * P a d e) := by
          calc
            (∑ d : Idx, ∑ e : Idx, P b e d * P d a e) =
                ∑ d : Idx, ∑ e : Idx, -(P b e d * P a d e) := by
              refine Finset.sum_congr rfl fun d _ => ?_
              refine Finset.sum_congr rfl fun e _ => ?_
              rw [hPSkew d a e]
              ring_nf
            _ = _ := by simp only [Finset.sum_neg_distrib]
        rw [hSkewSum]
        ring_nf
      _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        ring_nf
  have hGradient :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          nablaR c a d e b * P c d e) -
        (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          nablaRic c d e * nablaR d c a e b) =
      ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        nablaR e a c d b * nablaRic e c d := by
    have hThird :
        (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            nablaR c a d e b * P c d e) =
          (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            nablaR c a d e b * nablaRic c d e) -
          ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            nablaR c a d e b * nablaRic d c e := by
      simp only [P, hamiltonPComponent, mul_sub,
        Finset.sum_sub_distrib]
    have hFourth :
        (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            nablaRic c d e * nablaR d c a e b) =
          -(∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            nablaR c a d e b * nablaRic d c e) := by
      calc
        (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            nablaRic c d e * nablaR d c a e b) =
          ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            nablaRic d c e * nablaR c d a e b :=
          sum_swap_two (fun c d =>
            ∑ e : Idx, nablaRic c d e * nablaR d c a e b)
        _ = ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            -(nablaR c a d e b * nablaRic d c e) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          refine Finset.sum_congr rfl fun d _ => ?_
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hNablaRSkewFirst c d a e b]
          ring_nf
        _ = _ := by simp only [Finset.sum_neg_distrib]
    calc
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          nablaR c a d e b * P c d e) -
          (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            nablaRic c d e * nablaR d c a e b) =
        ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          nablaR c a d e b * nablaRic c d e := by
            rw [hThird, hFourth]
            ring_nf
      _ = _ := sum_cycle_three
        (fun c d e => nablaR c a d e b * nablaRic c d e)
  simp only [P] at hFirst hSecond hGradient
  linear_combination (norm := ring_nf) hFirst + hSecond + 2 * hGradient

theorem hamilton_divP_nablaP_reaction_regroup
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric divP : Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (hRm : Rm04Symm R)
    (hTrace : forall a d, (∑ e : Idx, R e a d e) = Ric a d)
    (hDivP : forall a b, (∑ c : Idx, nablaP c c a b) = divP a b)
    (a b : Idx) :
    2 * ((∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        R c d e a * nablaP c d e b) +
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        R c d e b * nablaP c d a e) +
      ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
        R a d e b * nablaP c c d e) +
      (∑ c : Idx,
        curvatureSlotActionContraction R
          (fun e (slots : Fin 3 -> Idx) =>
            nablaP e (slots 0) (slots 1) (slots 2)) c
          (fun q : Fin 3 => if q = 0 then c else if q = 1 then a else b)) =
      2 * ∑ c : Idx, ∑ d : Idx, R a c d b * divP c d +
      2 * ∑ c : Idx, ∑ d : Idx, Ric c d * nablaP c d a b := by
  classical
  have hCancelA :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          R c d e a * nablaP c d e b) +
        (∑ c : Idx, ∑ e : Idx, ∑ d : Idx,
          R c e d a * nablaP e c d b) = 0 := by
    have hswap :
        (∑ c : Idx, ∑ e : Idx, ∑ d : Idx,
            R c e d a * nablaP e c d b) =
          -(∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            R c d e a * nablaP c d e b) := by
      calc
        (∑ c : Idx, ∑ e : Idx, ∑ d : Idx,
            R c e d a * nablaP e c d b) =
          ∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
            R c e d a * nablaP e c d b := Finset.sum_comm
        _ = ∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
            -(R e c d a * nablaP e c d b) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          refine Finset.sum_congr rfl fun c _ => ?_
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [hRm.swap12 e c d a]
          ring_nf
        _ = -(∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            R c d e a * nablaP c d e b) := by
          simp only [Finset.sum_neg_distrib]
    rw [hswap]
    ring_nf
  have hCancelB :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          R c d e b * nablaP c d a e) +
        (∑ c : Idx, ∑ e : Idx, ∑ d : Idx,
          R c e d b * nablaP e c a d) = 0 := by
    have hswap :
        (∑ c : Idx, ∑ e : Idx, ∑ d : Idx,
            R c e d b * nablaP e c a d) =
          -(∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            R c d e b * nablaP c d a e) := by
      calc
        (∑ c : Idx, ∑ e : Idx, ∑ d : Idx,
            R c e d b * nablaP e c a d) =
          ∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
            R c e d b * nablaP e c a d := Finset.sum_comm
        _ = ∑ e : Idx, ∑ c : Idx, ∑ d : Idx,
            -(R e c d b * nablaP e c a d) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          refine Finset.sum_congr rfl fun c _ => ?_
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [hRm.swap12 e c d b]
          ring_nf
        _ = -(∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
            R c d e b * nablaP c d a e) := by
          simp only [Finset.sum_neg_distrib]
    rw [hswap]
    ring_nf
  have hTraceTerm :
      (∑ c : Idx, ∑ e : Idx, ∑ d : Idx,
          R c e d c * nablaP e d a b) =
        ∑ c : Idx, ∑ d : Idx, Ric c d * nablaP c d a b := by
    calc
      (∑ c : Idx, ∑ e : Idx, ∑ d : Idx,
          R c e d c * nablaP e d a b) =
        ∑ e : Idx, ∑ d : Idx,
          (∑ c : Idx, R c e d c) * nablaP e d a b := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.sum_mul]
      _ = _ := by
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hTrace e d]
  have hDivTerm :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          R a d e b * nablaP c c d e) =
        ∑ c : Idx, ∑ d : Idx, R a c d b * divP c d := by
    calc
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          R a d e b * nablaP c c d e) =
        ∑ d : Idx, ∑ e : Idx,
          R a d e b * (∑ c : Idx, nablaP c c d e) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.mul_sum]
      _ = _ := by
        refine Finset.sum_congr rfl fun d _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hDivP d e]
  have hSlots :
      (∑ c : Idx,
          curvatureSlotActionContraction R
            (fun e (slots : Fin 3 -> Idx) =>
              nablaP e (slots 0) (slots 1) (slots 2)) c
            (fun q : Fin 3 => if q = 0 then c else if q = 1 then a else b)) =
        2 * ((∑ c : Idx, ∑ e : Idx, ∑ d : Idx,
            R c e d c * nablaP e d a b) +
          (∑ c : Idx, ∑ e : Idx, ∑ d : Idx,
            R c e d a * nablaP e c d b) +
          ∑ c : Idx, ∑ e : Idx, ∑ d : Idx,
            R c e d b * nablaP e c a d) := by
    simp only [curvatureSlotActionContraction, Fin.sum_univ_three,
      Function.update_apply]
    simp
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hSlots, hDivTerm, hTraceTerm]
  linear_combination (norm := ring_nf) 2 * hCancelA + 2 * hCancelB

def hamiltonNablaPEvolutionReactionComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nabla2R : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (q a b c : Idx) : Real :=
  2 * ∑ d : Idx, ∑ e : Idx,
      (nablaR q a d e b * hamiltonPComponent nablaRic d e c +
        R a d e b * nablaP q d e c) +
    2 * ∑ d : Idx, ∑ e : Idx,
      (nablaR q a d e c * hamiltonPComponent nablaRic d b e +
        R a d e c * nablaP q d b e) +
    2 * ∑ d : Idx, ∑ e : Idx,
      (nablaR q b d e c * hamiltonPComponent nablaRic a d e +
        R b d e c * nablaP q a d e) -
    2 * ∑ d : Idx, ∑ e : Idx,
      (nablaRic q d e * nablaR d a b e c +
        Ric d e * nabla2R q d a b e c)

def uhlenbeckHeatNablaPComponent
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaDtP : Idx -> Idx -> Idx -> Idx -> Real)
    (nabla3P : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (q a b c : Idx) : Real :=
  uhlenbeckTimeDerivativeOfCovariantDerivative Ric nablaRic
      (fun slots : Fin 3 -> Idx =>
        hamiltonPComponent nablaRic (slots 0) (slots 1) (slots 2))
      (fun e (slots : Fin 3 -> Idx) =>
        nablaP e (slots 0) (slots 1) (slots 2))
      (fun e (slots : Fin 3 -> Idx) =>
        nablaDtP e (slots 0) (slots 1) (slots 2)) q
      (fun r : Fin 3 => if r = 0 then a else if r = 1 then b else c) -
    roughLaplacianCovariantDerivativeComponents
      (fun e f d (slots : Fin 3 -> Idx) =>
        nabla3P e f d (slots 0) (slots 1) (slots 2)) q
      (fun r : Fin 3 => if r = 0 then a else if r = 1 then b else c)

def uhlenbeckNablaHeatPComponent
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaDtP : Idx -> Idx -> Idx -> Idx -> Real)
    (nabla3P : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (q a b c : Idx) : Real :=
  uhlenbeckCovariantDerivativeOfTimeDerivative Ric nablaRic
      (fun slots : Fin 3 -> Idx =>
        hamiltonPComponent nablaRic (slots 0) (slots 1) (slots 2))
      (fun e (slots : Fin 3 -> Idx) =>
        nablaP e (slots 0) (slots 1) (slots 2))
      (fun e (slots : Fin 3 -> Idx) =>
        nablaDtP e (slots 0) (slots 1) (slots 2)) q
      (fun r : Fin 3 => if r = 0 then a else if r = 1 then b else c) -
    covariantDerivativeRoughLaplacianComponents
      (fun e f d (slots : Fin 3 -> Idx) =>
        nabla3P e f d (slots 0) (slots 1) (slots 2)) q
      (fun r : Fin 3 => if r = 0 then a else if r = 1 then b else c)

section

variable [DecidableEq Idx]

theorem hamiltonP_heat_covariantDerivative_commutator_slots
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaDtP : Idx -> Idx -> Idx -> Idx -> Real)
    (nabla3P : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (hdiff : differentiatedTensorRicciIdentityComponents R nablaR
      (fun slots : Fin 3 -> Idx =>
        hamiltonPComponent nablaRic (slots 0) (slots 1) (slots 2))
      (fun e (slots : Fin 3 -> Idx) =>
        nablaP e (slots 0) (slots 1) (slots 2))
      (fun e f d (slots : Fin 3 -> Idx) =>
        nabla3P e f d (slots 0) (slots 1) (slots 2)))
    (hgrad : tensorGradientRicciIdentityComponents R
      (fun e (slots : Fin 3 -> Idx) =>
        nablaP e (slots 0) (slots 1) (slots 2))
      (fun e f d (slots : Fin 3 -> Idx) =>
        nabla3P e f d (slots 0) (slots 1) (slots 2)))
    (hcontract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hskewFirst : forall a e c d, R a e c d = -R e a c d)
    (hskewLast : forall a e c d, R a e c d = -R a e d c)
    (htrace : curvatureRicciTraceComponents R Ric)
    (a : Idx) (slots : Fin 3 -> Idx) :
    (uhlenbeckHeatNablaPComponent Ric nablaRic nablaP nablaDtP nabla3P a
        (slots 0) (slots 1) (slots 2) -
      uhlenbeckNablaHeatPComponent Ric nablaRic nablaP nablaDtP nabla3P a
        (slots 0) (slots 1) (slots 2)) =
      curvatureSlotActionContraction R
        (fun e (s : Fin 3 -> Idx) => nablaP e (s 0) (s 1) (s 2)) a slots := by
  have h := uhlenbeck_heat_covariantDerivative_commutator_slots
    R nablaR Ric nablaRic
    (fun s : Fin 3 -> Idx =>
      hamiltonPComponent nablaRic (s 0) (s 1) (s 2))
    (fun e (s : Fin 3 -> Idx) => nablaP e (s 0) (s 1) (s 2))
    (fun e (s : Fin 3 -> Idx) => nablaDtP e (s 0) (s 1) (s 2))
    (fun e f d (s : Fin 3 -> Idx) => nabla3P e f d (s 0) (s 1) (s 2))
    hdiff hgrad hcontract hskewFirst hskewLast htrace a slots
  have hslots :
      (fun r : Fin 3 => if r = 0 then slots 0 else if r = 1 then slots 1 else slots 2) =
        slots := by
    funext r
    fin_cases r <;> simp
  simpa [uhlenbeckHeatNablaPComponent, uhlenbeckNablaHeatPComponent,
    curvatureSlotActionContraction, Function.update_apply, hslots] using h

end

def hamiltonDivPHeatComponent
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaDtP : Idx -> Idx -> Idx -> Idx -> Real)
    (nabla3P : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (a b : Idx) : Real :=
  ∑ c : Idx,
    uhlenbeckHeatNablaPComponent Ric nablaRic nablaP nablaDtP nabla3P c c a b

def hamiltonDivPEvolutionComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (divP : Idx -> Idx -> Real)
    (a b : Idx) : Real :=
  2 * ∑ c : Idx, ∑ d : Idx, R a c d b * divP c d +
    2 * ∑ c : Idx, ∑ d : Idx,
      Ric c d * (nablaP c d a b + nablaP c d b a) +
    (∑ c : Idx, ∑ d : Idx,
      hamiltonPComponent nablaRic c d a * hamiltonPComponent nablaRic c d b) -
    2 * ∑ c : Idx, ∑ d : Idx,
      hamiltonPComponent nablaRic a c d * hamiltonPComponent nablaRic b d c +
    2 * ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
      Ric c d * Ric c e * R a d e b +
    2 * ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
      nablaR e a c d b * nablaRic e c d +
    2 * ∑ c : Idx, ∑ d : Idx,
      Ric c d *
        (hamiltonBComponent R a b c d + hamiltonBComponent R a c b d -
          hamiltonBComponent R a c d b - hamiltonBComponent R a d c b)

section

variable [DecidableEq Idx]

theorem hamiltonDivP_evolution
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nabla2R : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (divP : Idx -> Idx -> Real)
    (nablaDtP : Idx -> Idx -> Idx -> Idx -> Real)
    (nabla3P : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (hdiff : differentiatedTensorRicciIdentityComponents R nablaR
      (fun slots : Fin 3 -> Idx =>
        hamiltonPComponent nablaRic (slots 0) (slots 1) (slots 2))
      (fun e (slots : Fin 3 -> Idx) =>
        nablaP e (slots 0) (slots 1) (slots 2))
      (fun e f d (slots : Fin 3 -> Idx) =>
        nabla3P e f d (slots 0) (slots 1) (slots 2)))
    (hgrad : tensorGradientRicciIdentityComponents R
      (fun e (slots : Fin 3 -> Idx) =>
        nablaP e (slots 0) (slots 1) (slots 2))
      (fun e f d (slots : Fin 3 -> Idx) =>
        nabla3P e f d (slots 0) (slots 1) (slots 2)))
    (hcontract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hRm : Rm04Symm R)
    (hRic : forall a b, Ric a b = Ric b a)
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (hTrace : curvatureRicciTraceComponents R Ric)
    (hNablaRSkewFirst : forall d a b c e,
      nablaR d a b c e = -nablaR d b a c e)
    (hSecondComm : covariantTensorSecondDerivativeCommutatorComponents R
      (fun slots : Fin 4 -> Idx => R (slots 0) (slots 1) (slots 2) (slots 3))
      (fun c d (slots : Fin 4 -> Idx) =>
        nabla2R c d (slots 0) (slots 1) (slots 2) (slots 3)))
    (hDifferentiatedDiv : differentiatedCurvatureDivergenceComponents nabla2R nablaP)
    (hNablaPSkew : forall d a b c, nablaP d a b c = -nablaP d b a c)
    (hDivP : forall a b, (∑ c : Idx, nablaP c c a b) = divP a b)
    (hPReactionDerivative : forall q a b c,
      uhlenbeckNablaHeatPComponent Ric nablaRic nablaP nablaDtP nabla3P q a b c =
        hamiltonNablaPEvolutionReactionComponent R Ric nablaR nablaRic
          nabla2R nablaP q a b c)
    (a b : Idx) :
    hamiltonDivPHeatComponent Ric nablaRic nablaP nablaDtP nabla3P a b =
      hamiltonDivPEvolutionComponent R Ric nablaR nablaRic nablaP divP a b := by
  classical
  have hCommAt (c : Idx) :
      uhlenbeckHeatNablaPComponent Ric nablaRic nablaP nablaDtP nabla3P c c a b =
        hamiltonNablaPEvolutionReactionComponent R Ric nablaR nablaRic
            nabla2R nablaP c c a b +
          curvatureSlotActionContraction R
            (fun e (slots : Fin 3 -> Idx) =>
              nablaP e (slots 0) (slots 1) (slots 2)) c
            (fun q : Fin 3 => if q = 0 then c else if q = 1 then a else b) := by
    have h := uhlenbeck_heat_covariantDerivative_commutator R nablaR Ric nablaRic
      (fun slots : Fin 3 -> Idx =>
        hamiltonPComponent nablaRic (slots 0) (slots 1) (slots 2))
      (fun e (slots : Fin 3 -> Idx) =>
        nablaP e (slots 0) (slots 1) (slots 2))
      (fun e (slots : Fin 3 -> Idx) =>
        nablaDtP e (slots 0) (slots 1) (slots 2))
      (fun e f d (slots : Fin 3 -> Idx) =>
        nabla3P e f d (slots 0) (slots 1) (slots 2))
      hdiff hgrad hcontract hRm.swap12 hRm.swap34 hTrace c
      (fun q : Fin 3 => if q = 0 then c else if q = 1 then a else b)
    change
      uhlenbeckHeatNablaPComponent Ric nablaRic nablaP nablaDtP nabla3P c c a b -
        uhlenbeckNablaHeatPComponent Ric nablaRic nablaP nablaDtP nabla3P c c a b =
      curvatureSlotActionContraction R
        (fun e (slots : Fin 3 -> Idx) =>
          nablaP e (slots 0) (slots 1) (slots 2)) c
        (fun q : Fin 3 => if q = 0 then c else if q = 1 then a else b) at h
    rw [hPReactionDerivative c c a b] at h
    linarith
  have hHeatRaw :
      hamiltonDivPHeatComponent Ric nablaRic nablaP nablaDtP nabla3P a b =
        ∑ c : Idx,
          (hamiltonNablaPEvolutionReactionComponent R Ric nablaR nablaRic
              nabla2R nablaP c c a b +
            curvatureSlotActionContraction R
              (fun e (slots : Fin 3 -> Idx) =>
                nablaP e (slots 0) (slots 1) (slots 2)) c
              (fun q : Fin 3 => if q = 0 then c else if q = 1 then a else b)) := by
    rw [hamiltonDivPHeatComponent]
    refine Finset.sum_congr rfl fun c _ => hCommAt c
  have hGradient := hamilton_divP_gradient_reaction_regroup
    nablaR nablaRic hNablaRic hNablaRSkewFirst hcontract a b
  have hNablaP := hamilton_divP_nablaP_reaction_regroup
    R Ric divP nablaP hRm hTrace hDivP a b
  have hSecond := hamilton_contracted_nabla2_curvature
    R Ric nabla2R nablaP hRm hRic hTrace hSecondComm hDifferentiatedDiv
      hNablaPSkew a b
  have hBSplit :
      (∑ c : Idx, ∑ d : Idx,
          Ric c d *
            (hamiltonBComponent R a b c d + hamiltonBComponent R a c b d -
              hamiltonBComponent R a c d b - hamiltonBComponent R a d c b)) =
        (∑ c : Idx, ∑ d : Idx, Ric c d * hamiltonBComponent R a b c d) +
          (∑ c : Idx, ∑ d : Idx, Ric c d * hamiltonBComponent R a c b d) -
          (∑ c : Idx, ∑ d : Idx, Ric c d * hamiltonBComponent R a c d b) -
          ∑ c : Idx, ∑ d : Idx, Ric c d * hamiltonBComponent R a d c b := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  rw [hHeatRaw]
  simp only [hamiltonNablaPEvolutionReactionComponent,
    hamiltonDivPEvolutionComponent, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linear_combination (norm := skip) hGradient + hNablaP + hSecond
  simp only [← Finset.mul_sum]
  rw [hBSplit]
  ring_nf

end

def hamiltonRmReactionComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real) (a b c d : Idx) : Real :=
  2 * (hamiltonBComponent R a b c d - hamiltonBComponent R a b d c +
    hamiltonBComponent R a c b d - hamiltonBComponent R a d b c)

def hamiltonRicciReactionComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real) (a b : Idx) : Real :=
  2 * ∑ c : Idx, ∑ d : Idx, R a c d b * Ric c d

def hamiltonCurvatureRicciComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real) (a b : Idx) : Real :=
  ∑ c : Idx, ∑ d : Idx, R a c d b * Ric c d

def hamiltonCurvatureRicciHeatComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (a b : Idx) : Real :=
  ∑ c : Idx, ∑ d : Idx,
    (hamiltonRmReactionComponent R a c d b * Ric c d +
      R a c d b * hamiltonRicciReactionComponent R Ric c d -
      2 * ∑ e : Idx, nablaR e a c d b * nablaRic e c d)

def hamiltonCurvatureRicciEvolutionComponent
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (a b : Idx) : Real :=
  2 * ∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ f : Idx,
      R a c d b * R c e f d * Ric e f -
    2 * ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
      nablaR e a c d b * nablaRic e c d +
    2 * ∑ c : Idx, ∑ d : Idx,
      Ric c d *
        (hamiltonBComponent R a c d b - hamiltonBComponent R a c b d +
          hamiltonBComponent R a d c b - hamiltonBComponent R a b c d)

theorem hamiltonCurvatureRicci_evolution
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (a b : Idx) :
    hamiltonCurvatureRicciHeatComponent R Ric nablaR nablaRic a b =
      hamiltonCurvatureRicciEvolutionComponent R Ric nablaR nablaRic a b := by
  classical
  have hB :
      (∑ c : Idx, ∑ d : Idx,
        (2 * hamiltonBComponent R a c d b -
            2 * hamiltonBComponent R a c b d +
            2 * hamiltonBComponent R a d c b -
            2 * hamiltonBComponent R a b c d) * Ric c d) =
        2 * ∑ c : Idx, ∑ d : Idx,
          Ric c d *
            (hamiltonBComponent R a c d b - hamiltonBComponent R a c b d +
              hamiltonBComponent R a d c b - hamiltonBComponent R a b c d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring_nf
  have hCubic :
      (∑ c : Idx, ∑ d : Idx,
          R a c d b *
            (2 * ∑ e : Idx, ∑ f : Idx, R c e f d * Ric e f)) =
        2 * ∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ f : Idx,
          R a c d b * R c e f d * Ric e f := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    ring_nf
  have hGradient :
      (∑ c : Idx, ∑ d : Idx,
          2 * ∑ e : Idx, nablaR e a c d b * nablaRic e c d) =
        2 * ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
          nablaR e a c d b * nablaRic e c d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
  have hBSplit :
      2 * (∑ c : Idx, ∑ d : Idx,
          Ric c d *
            (hamiltonBComponent R a c d b - hamiltonBComponent R a c b d +
              hamiltonBComponent R a d c b - hamiltonBComponent R a b c d)) =
        2 * (∑ c : Idx, ∑ d : Idx,
          Ric c d * hamiltonBComponent R a c d b) -
        2 * (∑ c : Idx, ∑ d : Idx,
          Ric c d * hamiltonBComponent R a c b d) +
        2 * (∑ c : Idx, ∑ d : Idx,
          Ric c d * hamiltonBComponent R a d c b) -
        2 * (∑ c : Idx, ∑ d : Idx,
          Ric c d * hamiltonBComponent R a b c d) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  simp only [hamiltonCurvatureRicciHeatComponent,
    hamiltonCurvatureRicciEvolutionComponent, hamiltonRmReactionComponent,
    hamiltonRicciReactionComponent, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hB, hCubic, hGradient, hBSplit]
  ring_nf

def hamiltonMComponent
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric divP : Idx -> Idx -> Real) (a b : Idx) : Real :=
  divP a b + hamiltonCurvatureRicciComponent R Ric a b +
    (1 / (2 * clock.elapsed)) * Ric a b

def hamiltonShiftedRicciHeatComponent
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real) (a b : Idx) : Real :=
  (1 / (2 * clock.elapsed)) * hamiltonRicciReactionComponent R Ric a b -
    (1 / (2 * clock.elapsed ^ 2)) * Ric a b

def hamiltonShiftedRicciEvolutionComponent
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric divP : Idx -> Idx -> Real) (a b : Idx) : Real :=
  2 * ∑ c : Idx, ∑ d : Idx,
      R a c d b *
        (hamiltonMComponent clock R Ric divP c d - divP c d -
          hamiltonCurvatureRicciComponent R Ric c d) -
    (1 / (2 * clock.elapsed ^ 2)) * Ric a b

theorem hamiltonShiftedRicci_evolution
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric divP : Idx -> Idx -> Real) (a b : Idx) :
    hamiltonShiftedRicciHeatComponent clock R Ric a b =
      hamiltonShiftedRicciEvolutionComponent clock R Ric divP a b := by
  classical
  have hinside :
      (∑ c : Idx, ∑ d : Idx,
          R a c d b *
            (hamiltonMComponent clock R Ric divP c d - divP c d -
              hamiltonCurvatureRicciComponent R Ric c d)) =
        ∑ c : Idx, ∑ d : Idx,
          R a c d b * ((1 / (2 * clock.elapsed)) * Ric c d) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hamiltonMComponent]
    ring_nf
  have hscale :
      (1 / (2 * clock.elapsed)) *
          (2 * ∑ c : Idx, ∑ d : Idx, R a c d b * Ric c d) =
        2 * ∑ c : Idx, ∑ d : Idx,
          R a c d b * ((1 / (2 * clock.elapsed)) * Ric c d) := by
    have hscaleInner :
        (1 / (2 * clock.elapsed)) *
            (∑ c : Idx, ∑ d : Idx, R a c d b * Ric c d) =
          ∑ c : Idx, ∑ d : Idx,
            R a c d b * ((1 / (2 * clock.elapsed)) * Ric c d) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring_nf
    rw [show
      (1 / (2 * clock.elapsed)) *
          (2 * ∑ c : Idx, ∑ d : Idx, R a c d b * Ric c d) =
        2 * ((1 / (2 * clock.elapsed)) *
          (∑ c : Idx, ∑ d : Idx, R a c d b * Ric c d)) by ring_nf]
    rw [hscaleInner]
  rw [hamiltonShiftedRicciHeatComponent,
    hamiltonShiftedRicciEvolutionComponent, hamiltonRicciReactionComponent,
    hinside, hscale]

def hamiltonMHeatComponent
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (nablaDtP : Idx -> Idx -> Idx -> Idx -> Real)
    (nabla3P : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (a b : Idx) : Real :=
  hamiltonDivPHeatComponent Ric nablaRic nablaP nablaDtP nabla3P a b +
    hamiltonCurvatureRicciHeatComponent R Ric nablaR nablaRic a b +
    hamiltonShiftedRicciHeatComponent clock R Ric a b

def hamiltonMEvolutionReactionComponent
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (divP : Idx -> Idx -> Real)
    (a b : Idx) : Real :=
  2 * ∑ c : Idx, ∑ d : Idx,
      R a c d b * hamiltonMComponent clock R Ric divP c d +
    2 * ∑ c : Idx, ∑ d : Idx,
      Ric c d * (nablaP c d a b + nablaP c d b a) +
    (∑ c : Idx, ∑ d : Idx,
      hamiltonPComponent nablaRic c d a * hamiltonPComponent nablaRic c d b) -
    2 * ∑ c : Idx, ∑ d : Idx,
      hamiltonPComponent nablaRic a c d * hamiltonPComponent nablaRic b d c +
    2 * ∑ c : Idx, ∑ d : Idx, ∑ e : Idx,
      Ric c d * Ric c e * R a d e b -
    (1 / (2 * clock.elapsed ^ 2)) * Ric a b

section

variable [DecidableEq Idx]

theorem hamiltonM_evolution
    (clock : HarnackClock)
    (R : Idx -> Idx -> Idx -> Idx -> Real)
    (Ric : Idx -> Idx -> Real)
    (nablaR : Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaRic : Idx -> Idx -> Idx -> Real)
    (nabla2R : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (nablaP : Idx -> Idx -> Idx -> Idx -> Real)
    (divP : Idx -> Idx -> Real)
    (nablaDtP : Idx -> Idx -> Idx -> Idx -> Real)
    (nabla3P : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (hdiff : differentiatedTensorRicciIdentityComponents R nablaR
      (fun slots : Fin 3 -> Idx =>
        hamiltonPComponent nablaRic (slots 0) (slots 1) (slots 2))
      (fun e (slots : Fin 3 -> Idx) =>
        nablaP e (slots 0) (slots 1) (slots 2))
      (fun e f d (slots : Fin 3 -> Idx) =>
        nabla3P e f d (slots 0) (slots 1) (slots 2)))
    (hgrad : tensorGradientRicciIdentityComponents R
      (fun e (slots : Fin 3 -> Idx) =>
        nablaP e (slots 0) (slots 1) (slots 2))
      (fun e f d (slots : Fin 3 -> Idx) =>
        nabla3P e f d (slots 0) (slots 1) (slots 2)))
    (hcontract : contractedCurvatureDerivativeComponents nablaR nablaRic)
    (hRm : Rm04Symm R)
    (hRic : forall a b, Ric a b = Ric b a)
    (hNablaRic : forall a b c, nablaRic a b c = nablaRic a c b)
    (hTrace : curvatureRicciTraceComponents R Ric)
    (hNablaRSkewFirst : forall d a b c e,
      nablaR d a b c e = -nablaR d b a c e)
    (hSecondComm : covariantTensorSecondDerivativeCommutatorComponents R
      (fun slots : Fin 4 -> Idx => R (slots 0) (slots 1) (slots 2) (slots 3))
      (fun c d (slots : Fin 4 -> Idx) =>
        nabla2R c d (slots 0) (slots 1) (slots 2) (slots 3)))
    (hDifferentiatedDiv : differentiatedCurvatureDivergenceComponents nabla2R nablaP)
    (hNablaPSkew : forall d a b c, nablaP d a b c = -nablaP d b a c)
    (hDivP : forall a b, (∑ c : Idx, nablaP c c a b) = divP a b)
    (hPReactionDerivative : forall q a b c,
      uhlenbeckNablaHeatPComponent Ric nablaRic nablaP nablaDtP nabla3P q a b c =
        hamiltonNablaPEvolutionReactionComponent R Ric nablaR nablaRic
          nabla2R nablaP q a b c)
    (a b : Idx) :
    hamiltonMHeatComponent clock R Ric nablaR nablaRic nablaP
        nablaDtP nabla3P a b =
      hamiltonMEvolutionReactionComponent clock R Ric nablaRic nablaP divP a b := by
  classical
  have hDivPEvolution := hamiltonDivP_evolution R Ric nablaR nablaRic
    nabla2R nablaP divP nablaDtP nabla3P hdiff hgrad hcontract hRm hRic
    hNablaRic hTrace hNablaRSkewFirst hSecondComm hDifferentiatedDiv
    hNablaPSkew hDivP hPReactionDerivative a b
  have hBCancel :
      (∑ c : Idx, ∑ d : Idx,
          Ric c d *
            (hamiltonBComponent R a b c d + hamiltonBComponent R a c b d -
              hamiltonBComponent R a c d b - hamiltonBComponent R a d c b)) +
        (∑ c : Idx, ∑ d : Idx,
          Ric c d *
            (hamiltonBComponent R a c d b - hamiltonBComponent R a c b d +
              hamiltonBComponent R a d c b - hamiltonBComponent R a b c d)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro c _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro d _
    ring_nf
  have hCurvature :
      (∑ c : Idx, ∑ d : Idx, ∑ e : Idx, ∑ f : Idx,
          R a c d b * R c e f d * Ric e f) =
        ∑ c : Idx, ∑ d : Idx,
          R a c d b * hamiltonCurvatureRicciComponent R Ric c d := by
    simp only [hamiltonCurvatureRicciComponent]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring_nf
  have hMCombine :
      (∑ c : Idx, ∑ d : Idx, R a c d b * divP c d) +
          (∑ c : Idx, ∑ d : Idx,
            R a c d b * hamiltonCurvatureRicciComponent R Ric c d) +
          (∑ c : Idx, ∑ d : Idx,
            R a c d b *
              (hamiltonMComponent clock R Ric divP c d - divP c d -
                hamiltonCurvatureRicciComponent R Ric c d)) =
        ∑ c : Idx, ∑ d : Idx,
          R a c d b * hamiltonMComponent clock R Ric divP c d := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring_nf
  rw [hamiltonMHeatComponent, hDivPEvolution,
    hamiltonCurvatureRicci_evolution R Ric nablaR nablaRic a b,
    hamiltonShiftedRicci_evolution clock R Ric divP a b]
  simp only [hamiltonDivPEvolutionComponent,
    hamiltonCurvatureRicciEvolutionComponent,
    hamiltonShiftedRicciEvolutionComponent,
    hamiltonMEvolutionReactionComponent]
  rw [hCurvature]
  linear_combination (norm := ring_nf) 2 * hBCancel + 2 * hMCombine

end

end DifferentialGeometry.PDE.RicciFlow
