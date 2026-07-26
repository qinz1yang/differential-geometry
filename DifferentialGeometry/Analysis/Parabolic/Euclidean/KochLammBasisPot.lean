import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxValue
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLinear
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammValue

set_option autoImplicit false

/-!
# Finite-basis Koch--Lamm split potential

A genuine Euclidean divergence source with values in `F` is a field
`f₁ : ℝ × V → V →L[ℝ] F`.  Its heat potential is the finite sum of the
already proved directional potentials applied to the components of `f₁` in
the canonical orthonormal basis of `V`.

This file stays at the value level.  It also records the corresponding
CLM-valued spatial-gradient candidate, but makes no unproved pointwise or
weak-derivative identification and no gradient-norm claim.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Evaluation of an operator-valued Koch--Lamm flux on one canonical unit
basis vector preserves both source radii. -/
theorem klFluxComp {T : ℝ} {A₂ Aₚ : ℝ≥0}
    (f : ℝ × V → V →L[ℝ] F) (h : KLSource1 T A₂ Aₚ f)
    (i : Fin (Module.finrank ℝ V)) :
    KLSource1 T A₂ Aₚ
      (fun z ↦ f z ((stdOrthonormalBasis ℝ V) i)) := by
  let e := stdOrthonormalBasis ℝ V
  let ev : (V →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (e i)
  have hev : ‖ev‖ ≤ (1 : ℝ) := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro L
    calc
      ‖ev L‖ = ‖L (e i)‖ := rfl
      _ ≤ ‖L‖ * ‖e i‖ := L.le_opNorm (e i)
      _ = 1 * ‖L‖ := by rw [e.norm_eq_one i, mul_one, one_mul]
  have hmeas : AEStronglyMeasurable (fun z ↦ ev (f z))
      (klVolume : Measure (ℝ × V)) :=
    ev.continuous.comp_aestronglyMeasurable h.ae
  simpa only [ev, e, ContinuousLinearMap.apply_apply, one_mul] using
    (kl1_map_bound (V := V) (ε := 1) (A := fun _ : ℝ × V ↦ ev) (d := f)
      (hA := fun _ ↦ hev) (hmeas := hmeas) h)

/-- The canonical finite-dimensional heat potential of
`f₀ + div f₁`.  The ordinary source is `F`-valued, while the divergence
source is honestly `V →L[ℝ] F`-valued. -/
def klBasisPot (t : ℝ) (f₀ : ℝ × V → F)
    (f₁ : ℝ × V → V →L[ℝ] F) (x : V) : F :=
  klHeat0 t f₀ x +
    ∑ i : Fin (Module.finrank ℝ V),
      klHeat1 t ((stdOrthonormalBasis ℝ V) i)
        (fun z ↦ f₁ z ((stdOrthonormalBasis ℝ V) i)) x

/-- The finite-basis CLM-valued spatial-gradient candidate belonging to
`klBasisPot`.  Its realization and Koch--Lamm gradient bounds are separate
analytic theorems. -/
def klBasisGrad (t : ℝ) (f₀ : ℝ × V → F)
    (f₁ : ℝ × V → V →L[ℝ] F) (x : V) : V →L[ℝ] F :=
  heatGrad0 t f₀ x +
    ∑ i : Fin (Module.finrank ℝ V),
      heatGrad1 t ((stdOrthonormalBasis ℝ V) i)
        (fun z ↦ f₁ z ((stdOrthonormalBasis ℝ V) i)) x

/-- On controlled sources, the finite-basis realized potential is exactly
the ordinary Duhamel potential plus the directional `heatPot1` sum. -/
theorem klBasisPot_eq {T t : ℝ} {A₁ A_q A₂ Aₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f₀ : ℝ × V → F)
    (f₁ : ℝ × V → V →L[ℝ] F) (x : V)
    (h₀ : KLSource0 T A₁ A_q f₀) (h₁ : KLSource1 T A₂ Aₚ f₁) :
    klBasisPot t f₀ f₁ x =
      heatPot0 t f₀ x +
        ∑ i : Fin (Module.finrank ℝ V),
          heatPot1 t ((stdOrthonormalBasis ℝ V) i)
            (fun z ↦ f₁ z ((stdOrthonormalBasis ℝ V) i)) x := by
  unfold klBasisPot
  rw [klHeat0_eq_heatPot (V := V) ht htT f₀ x h₀]
  refine congrArg (fun z : F ↦ heatPot0 t f₀ x + z) ?_
  apply Finset.sum_congr rfl
  intro i _
  exact klHeat1_eq_heatPot (V := V) ht htT
    ((stdOrthonormalBasis ℝ V) i)
    (fun z ↦ f₁ z ((stdOrthonormalBasis ℝ V) i)) x
    (klFluxComp (V := V) f₁ h₁ i)

/-- The canonical finite-basis split potential has zero initial value. -/
@[simp] theorem klBasisPot_zero (f₀ : ℝ × V → F)
    (f₁ : ℝ × V → V →L[ℝ] F) (x : V) :
    klBasisPot 0 f₀ f₁ x = 0 := by
  classical
  simp [klBasisPot, klHeat0, klHeat1, heatEarly0, heatEarly1,
    klLateFull0, klFluxFull1, klTermMeasure]

/-- The realized ordinary value potential is linear under subtraction once
the two input integrals are known to be integrable from their source bounds. -/
theorem klHeat0_sub {T t : ℝ} {A₁ A_q B₁ B_q : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f g : ℝ × V → F) (x : V)
    (hf : KLSource0 T A₁ A_q f) (hg : KLSource0 T B₁ B_q g) :
    klHeat0 t (fun z ↦ f z - g z) x = klHeat0 t f x - klHeat0 t g x := by
  have hfE := klEarly0_int (V := V) ht htT f x hf
  have hgE := klEarly0_int (V := V) ht htT g x hg
  have hfL := klLate0_int (V := V) ht htT f x hf
  have hgL := klLate0_int (V := V) ht htT g x hg
  unfold klHeat0 heatEarly0 klLateFull0
  simp only [smul_sub, Real.sq_sqrt ht.le]
  rw [MeasureTheory.integral_sub hfE hgE,
    MeasureTheory.integral_sub hfL hgL]
  abel

/-- The realized directional flux value potential is linear under
subtraction once both directional integrals are controlled. -/
theorem klHeat1_sub {T t : ℝ} {A₂ Aₚ B₂ Bₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (w : V) (f g : ℝ × V → F) (x : V)
    (hf : KLSource1 T A₂ Aₚ f) (hg : KLSource1 T B₂ Bₚ g) :
    klHeat1 t w (fun z ↦ f z - g z) x =
      klHeat1 t w f x - klHeat1 t w g x := by
  have hfE := klEarly1_int (V := V) ht htT w f x hf
  have hgE := klEarly1_int (V := V) ht htT w g x hg
  have hfL := klLate1_int (V := V) ht htT w f x hf
  have hgL := klLate1_int (V := V) ht htT w g x hg
  unfold klHeat1 heatEarly1 klFluxFull1
  simp only [smul_sub, Real.sq_sqrt ht.le]
  rw [MeasureTheory.integral_sub hfE hgE,
    MeasureTheory.integral_sub hfL hgL]
  abel

/-- Linearity of the full finite-basis split potential under subtraction.
The hypotheses are only the source bounds needed for Bochner integrability. -/
theorem klBasisPot_sub {T t : ℝ}
    {A₁ A_q B₁ B_q A₂ Aₚ B₂ Bₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f₀ g₀ : ℝ × V → F)
    (f₁ g₁ : ℝ × V → V →L[ℝ] F) (x : V)
    (hf₀ : KLSource0 T A₁ A_q f₀) (hg₀ : KLSource0 T B₁ B_q g₀)
    (hf₁ : KLSource1 T A₂ Aₚ f₁) (hg₁ : KLSource1 T B₂ Bₚ g₁) :
    klBasisPot t (fun z ↦ f₀ z - g₀ z) (fun z ↦ f₁ z - g₁ z) x =
      klBasisPot t f₀ f₁ x - klBasisPot t g₀ g₁ x := by
  classical
  unfold klBasisPot
  rw [klHeat0_sub (V := V) ht htT f₀ g₀ x hf₀ hg₀]
  have hsum :
      (∑ i : Fin (Module.finrank ℝ V),
        klHeat1 t ((stdOrthonormalBasis ℝ V) i)
          (fun z ↦ (f₁ z - g₁ z) ((stdOrthonormalBasis ℝ V) i)) x) =
        (∑ i : Fin (Module.finrank ℝ V),
          klHeat1 t ((stdOrthonormalBasis ℝ V) i)
            (fun z ↦ f₁ z ((stdOrthonormalBasis ℝ V) i)) x) -
          ∑ i : Fin (Module.finrank ℝ V),
            klHeat1 t ((stdOrthonormalBasis ℝ V) i)
              (fun z ↦ g₁ z ((stdOrthonormalBasis ℝ V) i)) x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ContinuousLinearMap.sub_apply]
    exact klHeat1_sub (V := V) ht htT
      ((stdOrthonormalBasis ℝ V) i)
      (fun z ↦ f₁ z ((stdOrthonormalBasis ℝ V) i))
      (fun z ↦ g₁ z ((stdOrthonormalBasis ℝ V) i)) x
      (klFluxComp (V := V) f₁ hf₁ i)
      (klFluxComp (V := V) g₁ hg₁ i)
  rw [hsum]
  abel

/-- The already proved ordinary-source value constant. -/
def klVal0Bound (A₁ A_q : ℝ≥0) : ℝ≥0∞ :=
  earlyHeatC V * (A₁ : ℝ≥0∞) +
    ENNReal.ofReal
      (klLateSeries (Module.finrank ℝ V) * (klLateTailC V * (A_q : ℝ)))

/-- The already proved value constant for one unit directional component of
an operator-valued flux. -/
def klVal1Bound (A₂ Aₚ : ℝ≥0) : ℝ≥0∞ :=
  earlyFluxC V * (A₂ : ℝ≥0∞) *
      fluxShellSeries (Module.finrank ℝ V) +
    ENNReal.ofReal
      (klFluxSeries (Module.finrank ℝ V) * (klFluxTailC V * (Aₚ : ℝ)))

/-- The genuine finite-dimensional divergence value bound.  The flux cost is
the number of canonical orthonormal-basis components times the proved unit
directional cost. -/
theorem klBasisPot_norm {T t : ℝ} {A₁ A_q A₂ Aₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f₀ : ℝ × V → F)
    (f₁ : ℝ × V → V →L[ℝ] F) (x : V)
    (h₀ : KLSource0 T A₁ A_q f₀) (h₁ : KLSource1 T A₂ Aₚ f₁) :
    ‖klBasisPot t f₀ f₁ x‖ₑ ≤
      klVal0Bound (V := V) A₁ A_q +
        (Module.finrank ℝ V : ℝ≥0∞) * klVal1Bound (V := V) A₂ Aₚ := by
  classical
  let e := stdOrthonormalBasis ℝ V
  have hzero :
      ‖klHeat0 t f₀ x‖ₑ ≤ klVal0Bound (V := V) A₁ A_q := by
    simpa only [enorm_eq_nnnorm, klVal0Bound] using
      (klHeat0_norm (V := V) ht htT f₀ x h₀)
  have hone (i : Fin (Module.finrank ℝ V)) :
      ‖klHeat1 t (e i) (fun z ↦ f₁ z (e i)) x‖ₑ ≤
        klVal1Bound (V := V) A₂ Aₚ := by
    have hei : ‖e i‖ = 1 := e.norm_eq_one i
    have hi := klHeat1_norm (V := V) ht htT (e i)
      (fun z ↦ f₁ z (e i)) x
      (by simpa only [e] using klFluxComp (V := V) f₁ h₁ i)
    simpa only [enorm_eq_nnnorm, klVal1Bound, hei, ENNReal.ofReal_one,
      one_mul] using hi
  have hsum :
      ‖∑ i : Fin (Module.finrank ℝ V),
          klHeat1 t (e i) (fun z ↦ f₁ z (e i)) x‖ₑ ≤
        (Module.finrank ℝ V : ℝ≥0∞) *
          klVal1Bound (V := V) A₂ Aₚ := by
    calc
      ‖∑ i : Fin (Module.finrank ℝ V),
          klHeat1 t (e i) (fun z ↦ f₁ z (e i)) x‖ₑ ≤
          ∑ i : Fin (Module.finrank ℝ V),
            ‖klHeat1 t (e i) (fun z ↦ f₁ z (e i)) x‖ₑ := by
              simpa using enorm_sum_le Finset.univ
                (fun i : Fin (Module.finrank ℝ V) ↦
                  klHeat1 t (e i) (fun z ↦ f₁ z (e i)) x)
      _ ≤ ∑ _i : Fin (Module.finrank ℝ V),
          klVal1Bound (V := V) A₂ Aₚ :=
        Finset.sum_le_sum fun i _ ↦ hone i
      _ = (Module.finrank ℝ V : ℝ≥0∞) *
          klVal1Bound (V := V) A₂ Aₚ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  change
    ‖klHeat0 t f₀ x +
      ∑ i : Fin (Module.finrank ℝ V),
        klHeat1 t (e i) (fun z ↦ f₁ z (e i)) x‖ₑ ≤ _
  exact (enorm_add_le _ _).trans (add_le_add hzero hsum)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
