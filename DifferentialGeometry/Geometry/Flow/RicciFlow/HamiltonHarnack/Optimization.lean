import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx]

def ricciKernelDirection
    (Ric : Idx -> Idx -> Real) (z : Idx -> Real) : Prop :=
  ∀ b, ∑ a, Ric a b * z a = 0

def ricciQuadratic
    (Ric : Idx -> Idx -> Real) (z : Idx -> Real) : Real :=
  ∑ a, ∑ b, Ric a b * z a * z b

def ricciCovectorPairing
    (dR z : Idx -> Real) : Real :=
  ∑ a, dR a * z a

theorem ricci_quadratic_eq_zero_of_kernel
    (Ric : Idx -> Idx -> Real) (z : Idx -> Real)
    (hker : ricciKernelDirection Ric z) :
    ricciQuadratic Ric z = 0 := by
  unfold ricciQuadratic ricciKernelDirection at *
  calc
    (∑ a, ∑ b, Ric a b * z a * z b) =
        ∑ b, (∑ a, Ric a b * z a) * z b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
    _ = 0 := by simp [hker]

theorem ricci_quadratic_smul
    (Ric : Idx -> Idx -> Real) (z : Idx -> Real) (s : Real) :
    ricciQuadratic Ric (fun a => s * z a) =
      s ^ 2 * ricciQuadratic Ric z := by
  unfold ricciQuadratic
  calc
    (∑ a, ∑ b, Ric a b * (s * z a) * (s * z b)) =
        ∑ a, ∑ b, s ^ 2 * (Ric a b * z a * z b) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    _ = s ^ 2 * (∑ a, ∑ b, Ric a b * z a * z b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
    _ = s ^ 2 * ricciQuadratic Ric z := rfl

theorem ricciCovectorPairing_smul
    (dR z : Idx -> Real) (s : Real) :
    ricciCovectorPairing dR (fun a => s * z a) =
      s * ricciCovectorPairing dR z := by
  unfold ricciCovectorPairing
  rw [show (∑ a, dR a * (s * z a)) =
      ∑ a, s * (dR a * z a) by
        refine Finset.sum_congr rfl fun a _ => ?_
        ring]
  rw [Finset.mul_sum]

theorem hamilton_trace_ricci_kernel_annihilation
    (c : Real) (Ric : Idx -> Idx -> Real) (dR : Idx -> Real)
    (htrace : ∀ z, 0 ≤ c + 2 * ricciCovectorPairing dR z +
      2 * ricciQuadratic Ric z) :
    ∀ z, ricciKernelDirection Ric z →
      ricciCovectorPairing dR z = 0 := by
  intro z hker
  have hqzero : ricciQuadratic Ric z = 0 :=
    ricci_quadratic_eq_zero_of_kernel Ric z hker
  have hbound : ∀ s : Real, 0 ≤ c + 2 * s * ricciCovectorPairing dR z := by
    intro s
    have hs := htrace (fun a => s * z a)
    rw [ricciCovectorPairing_smul, ricci_quadratic_smul, hqzero] at hs
    simpa [pow_two, mul_assoc] using hs
  have hc : 0 ≤ c := by
    have h0 := hbound 0
    simpa using h0
  by_contra hne
  have hpos_or_neg := lt_or_gt_of_ne hne
  rcases hpos_or_neg with hneg | hpos
  · let s : Real := (c + 1) / (2 * (-ricciCovectorPairing dR z))
    have hsden : 0 < 2 * (-ricciCovectorPairing dR z) :=
      mul_pos (by norm_num) (neg_pos.mpr hneg)
    have hs := hbound s
    have hsval : c + 2 * s * ricciCovectorPairing dR z = -1 := by
      dsimp [s]
      field_simp [ne_of_gt hsden]
      ring
    rw [hsval] at hs
    linarith
  · let s : Real := -(c + 1) / (2 * ricciCovectorPairing dR z)
    have hsden : 0 < 2 * ricciCovectorPairing dR z :=
      mul_pos (by norm_num) hpos
    have hs := hbound s
    have hsval : c + 2 * s * ricciCovectorPairing dR z = -1 := by
      dsimp [s]
      field_simp [ne_of_gt hsden]
      ring
    rw [hsval] at hs
    linarith

theorem hamilton_trace_semidefinite_optimized
    (c : Real) (Ric : Idx -> Idx -> Real) (dR Y : Idx -> Real)
    (htrace : ∀ z, 0 ≤ c + 2 * ricciCovectorPairing dR z +
      2 * ricciQuadratic Ric z)
    (hpreimage : ∀ a, ∑ b, Ric a b * Y b = dR a) :
    0 ≤ c - (1 / 2 : Real) * ricciQuadratic Ric Y := by
  have hpair : ricciCovectorPairing dR Y = ricciQuadratic Ric Y := by
    unfold ricciCovectorPairing ricciQuadratic
    calc
      (∑ a, dR a * Y a) =
          ∑ a, (∑ b, Ric a b * Y b) * Y a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hpreimage]
      _ = ∑ a, ∑ b, Ric a b * Y b * Y a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
      _ = ∑ a, ∑ b, Ric a b * Y a * Y b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
  have hs := htrace (fun a => -(1 / 2 : Real) * Y a)
  rw [ricciCovectorPairing_smul, ricci_quadratic_smul, hpair] at hs
  norm_num [pow_two] at hs
  linarith

end DifferentialGeometry.PDE.RicciFlow
