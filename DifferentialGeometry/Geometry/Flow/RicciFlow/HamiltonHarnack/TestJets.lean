import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*}

def hamiltonTriangularA
    (S : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b c : Idx) : Real :=
  (1 / 2 : Real) * (S a b * W c - S a c * W b)

def hamiltonTestJetDU
    (clock : HarnackClock)
    (Ric h : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b c : Idx) : Real :=
  (1 / 2 : Real) * (Ric a b * W c - Ric a c * W b) +
    (1 / (4 * clock.elapsed) : Real) * (h a b * W c - h a c * W b)

def hamiltonTriangularConnectionU
    (S : Idx -> Idx -> Real) (W : Idx -> Real)
    (DU : Idx -> Idx -> Idx -> Real) (a b c : Idx) : Real :=
  DU a b c - hamiltonTriangularA S W a b c

def hamiltonTriangularConnectionW
    (DW : Idx -> Idx -> Real) (a b : Idx) : Real :=
  DW a b

theorem hamiltonTriangularA_skew
    (S : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b c : Idx) :
    hamiltonTriangularA S W a b c = -hamiltonTriangularA S W a c b := by
  unfold hamiltonTriangularA
  ring

theorem hamiltonTestJetDU_skew
    (clock : HarnackClock)
    (Ric h : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b c : Idx) :
    hamiltonTestJetDU clock Ric h W a b c =
      -hamiltonTestJetDU clock Ric h W a c b := by
  unfold hamiltonTestJetDU
  ring

theorem hamiltonTestJetDU_eq_triangularA
    (clock : HarnackClock)
    (Ric h : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b c : Idx) :
    hamiltonTestJetDU clock Ric h W a b c =
      hamiltonTriangularA
        (fun i j => Ric i j + (1 / (2 * clock.elapsed) : Real) * h i j)
        W a b c := by
  unfold hamiltonTestJetDU hamiltonTriangularA
  field_simp [HarnackClock.elapsed_ne_zero clock]
  ring

theorem hamiltonTriangularConnectionU_zero_of_testJet
    (clock : HarnackClock)
    (Ric h : Idx -> Idx -> Real) (W : Idx -> Real)
    (a b c : Idx) :
    hamiltonTriangularConnectionU
        (fun i j => Ric i j + (1 / (2 * clock.elapsed) : Real) * h i j)
        W (hamiltonTestJetDU clock Ric h W) a b c = 0 := by
  unfold hamiltonTriangularConnectionU
  rw [hamiltonTestJetDU_eq_triangularA]
  ring

theorem hamiltonTriangularConnectionW_zero_of_testJet
    (DW : Idx -> Idx -> Real) (a b : Idx)
    (hDW : DW a b = 0) :
    hamiltonTriangularConnectionW DW a b = 0 := by
  exact hDW

theorem hamiltonTestJetDU_clock_coefficient
    (clock : HarnackClock) :
    (1 / (4 * clock.elapsed) : Real) =
      (1 / 2 : Real) * (1 / (2 * clock.elapsed) : Real) := by
  field_simp [HarnackClock.elapsed_ne_zero clock]
  ring

theorem hamiltonTestJetDU_clock_coefficient_pos
    (clock : HarnackClock) :
    0 < (1 / (4 * clock.elapsed) : Real) := by
  exact one_div_pos.mpr (mul_pos (by norm_num) clock.elapsed_pos)

theorem hamiltonTestJetDU_zero_of_zero_W
    (clock : HarnackClock)
    (Ric h : Idx -> Idx -> Real) (a b c : Idx) :
    hamiltonTestJetDU clock Ric h (fun _ => 0) a b c = 0 := by
  unfold hamiltonTestJetDU
  simp

theorem hamilton_test_jet_realization
    (clock : HarnackClock)
    (Ric h : Idx -> Idx -> Real) (W : Idx -> Real) :
    ∃ (DU : Idx -> Idx -> Idx -> Real) (DW : Idx -> Idx -> Real),
      (∀ a b c, DU a b c = hamiltonTestJetDU clock Ric h W a b c) ∧
      (∀ a b, DW a b = 0) ∧
      (∀ a b c,
        hamiltonTriangularConnectionU
          (fun i j => Ric i j + (1 / (2 * clock.elapsed) : Real) * h i j)
          W DU a b c = 0) ∧
      (∀ a b, hamiltonTriangularConnectionW DW a b = 0) := by
  refine ⟨hamiltonTestJetDU clock Ric h W, (fun _ _ => 0), ?_, ?_, ?_, ?_⟩
  · intro a b c
    rfl
  · intro a b
    rfl
  · intro a b c
    exact hamiltonTriangularConnectionU_zero_of_testJet clock Ric h W a b c
  · intro a b
    exact hamiltonTriangularConnectionW_zero_of_testJet (fun _ _ => 0) a b rfl

end DifferentialGeometry.PDE.RicciFlow
