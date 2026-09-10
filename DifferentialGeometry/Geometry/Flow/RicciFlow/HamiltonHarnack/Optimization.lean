import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

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

private def ricciBilinear
    (Ric : Idx -> Idx -> Real) :
    (Idx -> Real) →ₗ[Real] (Idx -> Real) →ₗ[Real] Real :=
  LinearMap.mk₂ Real
    (fun z w => ∑ b, (∑ a, Ric a b * z a) * w b)
    (by
      intro z₁ z₂ w
      simp [Pi.add_apply, Finset.sum_add_distrib, add_mul, mul_add])
    (by
      intro c z w
      simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm])
    (by
      intro z w₁ w₂
      simp [Pi.add_apply, Finset.sum_add_distrib, mul_add])
    (by
      intro c z w
      simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm])

private def dotFunctional (z : Idx -> Real) : (Idx -> Real) →ₗ[Real] Real :=
  { toFun := fun w => ∑ a, z a * w a
    map_add' := by
      intro w₁ w₂
      simp [Pi.add_apply, Finset.sum_add_distrib, mul_add]
    map_smul' := by
      intro c w
      simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm] }

private theorem ricciBilinear_flip_eq_of_symmetric
    (Ric : Idx -> Idx -> Real)
    (hsym : ∀ a b, Ric a b = Ric b a) :
    (ricciBilinear Ric).flip = ricciBilinear Ric := by
  ext z w
  change (∑ b, (∑ a, Ric a b * w a) * z b) =
    ∑ b, (∑ a, Ric a b * z a) * w b
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [hsym]
  ring

private theorem dotFunctional_mem_dualAnnihilator_ricciBilinear_ker
    (Ric : Idx -> Idx -> Real) (dR : Idx -> Real)
    (hker : ∀ z, ricciKernelDirection Ric z →
      ricciCovectorPairing dR z = 0) :
    dotFunctional dR ∈ (ricciBilinear Ric).ker.dualAnnihilator := by
  classical
  rw [Submodule.mem_dualAnnihilator]
  intro z hz
  have hzfun : ricciBilinear Ric z = 0 := LinearMap.mem_ker.mp hz
  have hzker : ricciKernelDirection Ric z := by
    intro b
    have hzb := LinearMap.congr_fun hzfun (Pi.single b 1)
    have hsingle :
        (∑ x, (∑ i, Ric i x * z i) *
          (Pi.single b (1 : Real) : Idx → Real) x) =
          ∑ i, Ric i b * z i := by
      rw [Finset.sum_eq_single b]
      · simp
      · intro a ha hab
        simp [hab]
      · intro hb
        exact False.elim (hb (Finset.mem_univ b))
    change (∑ x, (∑ i, Ric i x * z i) *
      (Pi.single b (1 : Real) : Idx → Real) x) = 0 at hzb
    rw [hsingle] at hzb
    simpa using hzb
  have hzero := hker z hzker
  simpa [dotFunctional, ricciCovectorPairing] using hzero

private theorem ricciBilinear_range_exists_of_kernel_annihilation
    (Ric : Idx -> Idx -> Real) (dR : Idx -> Real)
    (hsym : ∀ a b, Ric a b = Ric b a)
    (hker : ∀ z, ricciKernelDirection Ric z →
      ricciCovectorPairing dR z = 0) :
    ∃ Y : Idx -> Real, ∀ a, ∑ b, Ric a b * Y b = dR a := by
  classical
  have hmem := dotFunctional_mem_dualAnnihilator_ricciBilinear_ker Ric dR hker
  rw [LinearMap.dualAnnihilator_ker_eq_range_flip] at hmem
  rw [ricciBilinear_flip_eq_of_symmetric Ric hsym] at hmem
  obtain ⟨Y, hY⟩ : ∃ Y : Idx -> Real, ricciBilinear Ric Y = dotFunctional dR :=
    LinearMap.mem_range.mp hmem
  refine ⟨Y, ?_⟩
  intro a
  have hYa := LinearMap.congr_fun hY (Pi.single a (1 : Real) : Idx -> Real)
  change (∑ b, (∑ i, Ric i b * Y i) *
      (Pi.single a (1 : Real) : Idx -> Real) b) =
    ∑ b, dR b * (Pi.single a (1 : Real) : Idx -> Real) b at hYa
  have hsingleL :
      (∑ b, (∑ i, Ric i b * Y i) *
        (Pi.single a (1 : Real) : Idx -> Real) b) =
        ∑ i, Ric i a * Y i := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      simp [hba]
    · intro ha
      exact False.elim (ha (Finset.mem_univ a))
  have hsingleR :
      (∑ b, dR b * (Pi.single a (1 : Real) : Idx -> Real) b) = dR a := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      simp [hba]
    · intro ha
      exact False.elim (ha (Finset.mem_univ a))
  rw [hsingleL, hsingleR] at hYa
  calc
    ∑ b, Ric a b * Y b = ∑ b, Ric b a * Y b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hsym]
    _ = dR a := hYa

private theorem ricci_quadratic_eq_pairing_of_preimage
    (Ric : Idx -> Idx -> Real) (dR Y : Idx -> Real)
    (hY : ∀ a, ∑ b, Ric a b * Y b = dR a) :
    ricciQuadratic Ric Y = ricciCovectorPairing dR Y := by
  unfold ricciQuadratic ricciCovectorPairing
  symm
  calc
    ∑ a, dR a * Y a = ∑ a, (∑ b, Ric a b * Y b) * Y a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hY]
    _ = ∑ a, ∑ b, Ric a b * Y b * Y a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
    _ = ∑ a, ∑ b, Ric a b * Y a * Y b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

private theorem ricci_quadratic_eq_of_preimages
    (Ric : Idx -> Idx -> Real) (dR Y Z : Idx -> Real)
    (hsym : ∀ a b, Ric a b = Ric b a)
    (hY : ∀ a, ∑ b, Ric a b * Y b = dR a)
    (hZ : ∀ a, ∑ b, Ric a b * Z b = dR a) :
    ricciQuadratic Ric Y = ricciQuadratic Ric Z := by
  have hdiff : ricciKernelDirection Ric (fun a => Y a - Z a) := by
    intro b
    calc
      ∑ a, Ric a b * (Y a - Z a) =
          ∑ a, Ric b a * (Y a - Z a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hsym]
      _ = (∑ a, Ric b a * Y a) - ∑ a, Ric b a * Z a := by
        simp [mul_sub, Finset.sum_sub_distrib]
      _ = 0 := by rw [hY, hZ, sub_self]
  have hzero : ricciCovectorPairing dR (fun a => Y a - Z a) = 0 := by
    unfold ricciCovectorPairing
    calc
      ∑ a, dR a * (Y a - Z a) =
          ∑ a, (∑ b, Ric a b * Y b) * (Y a - Z a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hY]
      _ = ∑ a, ∑ b, Ric a b * Y b * (Y a - Z a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_mul]
      _ = ∑ b, ∑ a, Ric a b * Y b * (Y a - Z a) := by
        rw [Finset.sum_comm]
      _ = ∑ b, Y b * (∑ a, Ric a b * (Y a - Z a)) := by
        apply Finset.sum_congr rfl
        intro b hb
        calc
          ∑ a, Ric a b * Y b * (Y a - Z a) =
              ∑ a, Y b * (Ric a b * (Y a - Z a)) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ = Y b * (∑ a, Ric a b * (Y a - Z a)) := by
            rw [Finset.mul_sum]
      _ = 0 := by
        unfold ricciKernelDirection at hdiff
        simp [hdiff]
  rw [show ricciCovectorPairing dR (fun a => Y a - Z a) =
      ricciCovectorPairing dR Y - ricciCovectorPairing dR Z by
        unfold ricciCovectorPairing
        simp [mul_sub, Finset.sum_sub_distrib]] at hzero
  rw [ricci_quadratic_eq_pairing_of_preimage Ric dR Y hY,
    ricci_quadratic_eq_pairing_of_preimage Ric dR Z hZ]
  linarith

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

private theorem hamilton_trace_semidefinite_optimized_of_preimage
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

theorem hamilton_trace_semidefinite_optimized_of_symmetric
    (c : Real) (Ric : Idx -> Idx -> Real) (dR : Idx -> Real)
    (hsym : ∀ a b, Ric a b = Ric b a)
    (htrace : ∀ z, 0 ≤ c + 2 * ricciCovectorPairing dR z +
      2 * ricciQuadratic Ric z) :
    ∃ Y : Idx -> Real,
      (∀ a, ∑ b, Ric a b * Y b = dR a) ∧
      (∀ Z, (∀ a, ∑ b, Ric a b * Z b = dR a) →
        ricciQuadratic Ric Z = ricciQuadratic Ric Y) ∧
      0 ≤ c - (1 / 2 : Real) * ricciQuadratic Ric Y := by
  have hkernel := hamilton_trace_ricci_kernel_annihilation c Ric dR htrace
  obtain ⟨Y, hY⟩ := ricciBilinear_range_exists_of_kernel_annihilation
    Ric dR hsym hkernel
  refine ⟨Y, hY, ?_, ?_⟩
  · intro Z hZ
    exact (ricci_quadratic_eq_of_preimages Ric dR Y Z hsym hY hZ).symm
  · exact hamilton_trace_semidefinite_optimized_of_preimage c Ric dR Y htrace hY

end DifferentialGeometry.PDE.RicciFlow
