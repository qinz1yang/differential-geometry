import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.Differentiation
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.SecondOrder
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Restriction

noncomputable section

open MeasureTheory Set
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open scoped ENNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memWkp_add_two_of_bilinFormOfCoeff_eq_integral
    (m : ℕ) {Omega V : Set E} (hOmega : IsOpen Omega)
    (hV_open : IsOpen V) (hV_compact : IsCompact (closure V))
    (hV_Omega : closure V ⊆ Omega)
    {A : EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : MemW1pWitness 2 u Omega)
    (hf : MemWkp (d := d) m 2 f Omega)
    (hweak : ∀ v, MemH01 v Omega →
      ∀ hv : MemW1pWitness 2 v Omega,
        bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : rho ≠ 0)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d,
      A.a x i j = rho * B.a x i j) :
    MemWkp (d := d) (m + 2) 2 u V := by
  classical
  induction m generalizing Omega V A u f with
  | zero =>
      apply memWkp_two_of_bilinFormOfCoeff_eq_integral (d := d)
        hOmega hV_open hV_compact hV_Omega
        hu hf.memLp hweak B hrho hcoeff
  | succ m ih =>
      obtain ⟨U, hU_open, hV_U, hU_Omega, hU_compact⟩ :=
        exists_open_between_and_isCompact_closure hV_compact hOmega hV_Omega
      have hU_sub : U ⊆ Omega := subset_closure.trans hU_Omega
      have hV_sub_U : V ⊆ U := subset_closure.trans hV_U
      have hV_sub_Omega : V ⊆ Omega := hV_sub_U.trans hU_sub
      have huU_high : MemWkp (d := d) (m + 2) 2 u U :=
        ih (Omega := Omega) (V := U) (A := A) (u := u) (f := f)
          hOmega hU_open hU_compact hU_Omega hu hf.le_succ hweak hcoeff
      let AU : EllipticCoeff d U := A.restrict hU_sub
      let huU : MemW1pWitness 2 u U := hu.restrict hU_open hU_sub
      have hweakU : ∀ v, MemH01 v U →
          ∀ hv : MemW1pWitness 2 v U,
            bilinFormOfCoeff AU huU hv =
              ∫ x in U, f x * v x ∂(volume : Measure E) := by
        intro v hv0 hv
        simpa only [AU, huU] using
          bilinFormOfCoeff_restrict_eq_integral (d := d)
            hOmega hU_open hU_sub hu hweak hv0 hv
      have hcoeffU : ∀ x ∈ U, ∀ i j : Fin d,
          AU.a x i j = rho * B.a x i j := by
        intro x hx i j
        simpa only [AU, EllipticCoeff.restrict_a] using
          hcoeff x (hU_sub hx) i j
      have hfU : MemWkp (d := d) (m + 1) 2 f U :=
        hf.mono_set (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          hU_open hU_sub
      have hfU1 : MemWkp (d := d) 1 2 f U :=
        hfU.le_of_le (by omega)
      have huU2 : MemWkp (d := d) 2 2 u U :=
        huU_high.le_of_le (by omega)
      rw [show m.succ + 2 = (m + 2) + 1 by omega, MemWkp_succ]
      refine ⟨(hu.restrict hV_open hV_sub_Omega).memW1p, ?_⟩
      intro l
      have hduU1 : MemW1p 2
          (chosenWeakPartialOrZero 2 l u U) U :=
        (huU_high.chosenWeakPartial_mem l).memW1p
      let hw : MemW1pWitness 2
          (chosenWeakPartialOrZero 2 l u U) U := hduU1.someWitness
      let q : E → ℝ := fun x =>
        chosenWeakPartialOrZero 2 l f U x +
          rho * coefficientDerivativeSource 2 B.a u U l x
      have hdf : MemWkp (d := d) m 2
          (chosenWeakPartialOrZero 2 l f U) U :=
        hfU.chosenWeakPartial_mem l
      have hcoeff_source : MemWkp (d := d) m 2
          (coefficientDerivativeSource 2 B.a u U l) U :=
        memWkp_coefficientDerivativeSource m (by norm_num) hU_open hU_compact B.smooth_a huU_high l
      have hq : MemWkp (d := d) m 2 q U := by
        simpa only [q] using MemWkp.add (d := d)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hU_open hdf
          (hcoeff_source.const_smul (by norm_num : (1 : ℝ≥0∞) ≤ 2)
            hU_open rho)
      have hdu_weak : ∀ v, MemH01 v U →
          ∀ hv : MemW1pWitness 2 v U,
            bilinFormOfCoeff AU hw hv =
              ∫ x in U, q x * v x ∂(volume : Measure E) := by
        intro v hv0 hv
        simpa only [q] using bilinFormOfCoeff_chosenWeakPartialOrZero_eq_integral
          (d := d) (A := AU) (u := u) (f := f)
          hU_open hU_compact huU hweakU hfU1.memW1p B.smooth_a hcoeffU huU2
          l hw v hv0 hv
      have hdu_high : MemWkp (d := d) (m + 2) 2
          (chosenWeakPartialOrZero 2 l u U) V :=
        ih (Omega := U) (V := V) (A := AU)
          (u := chosenWeakPartialOrZero 2 l u U) (f := q)
          hU_open hV_open hV_compact hV_U hw hq hdu_weak hcoeffU
      have hmono := chosenWeakPartialOrZero_mono_set_ae (d := d)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV_open hV_sub_U huU.memW1p l
      exact (MemWkp_congr_ae (d := d)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV_open hmono).mp hdu_high


theorem IsSolution.memWkp
    (k : ℕ) {Omega V : Set E} (hOmega : IsOpen Omega)
    (hV : IsOpen V) (hcompact : IsCompact (closure V)) (hsub : closure V ⊆ Omega)
    {A : EllipticCoeff d Omega} {u : E → ℝ} (hsol : IsSolution A u)
    (B : SmoothEllipticBilinearForm d Set.univ) {rho : ℝ} (hrho : rho ≠ 0)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d, A.a x i j = rho * B.a x i j) :
    MemWkp k 2 u V := by
  let hu := MemW1p.someWitness hsol.1.1
  have hweak : ∀ v, MemH01 v Omega → ∀ hv : MemW1pWitness 2 v Omega,
      bilinFormOfCoeff A hu hv = ∫ x in Omega, (0 : ℝ) * v x := by
    intro v hv0 hv
    simpa only [zero_mul, integral_zero] using hsol.bilinFormOfCoeff_eq_zero hOmega hu hv0 hv
  exact (memWkp_add_two_of_bilinFormOfCoeff_eq_integral k hOmega hV hcompact hsub
    hu (MemWkp_zero_fun (by norm_num) hOmega) hweak B hrho hcoeff).le_of_le (by omega)

end DeGiorgi
