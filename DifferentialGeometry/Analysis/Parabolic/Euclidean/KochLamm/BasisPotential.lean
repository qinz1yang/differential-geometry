import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Value
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Linear
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Value

set_option autoImplicit false

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

omit [Nontrivial V]
  [CompleteSpace F] in
theorem kochLammFluxComp {T : ℝ} {A₂ Aₚ : ℝ≥0}
    (f : ℝ × V → V →L[ℝ] F) (h : KochLammSourceOne T A₂ Aₚ f)
    (i : Fin (Module.finrank ℝ V)) :
    KochLammSourceOne T A₂ Aₚ
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
      (kochLammVolume : Measure (ℝ × V)) :=
    ev.continuous.comp_aestronglyMeasurable h.ae
  simpa only [ev, e, ContinuousLinearMap.apply_apply, one_mul] using
    (KochLammSourceOne.clm_apply (V := V) (ε := 1) (A := fun _ : ℝ × V ↦ ev) (d := f)
      (hA := fun _ ↦ hev) (hmeas := hmeas) h)

def kochLammBasisPot (t : ℝ) (f₀ : ℝ × V → F)
    (f₁ : ℝ × V → V →L[ℝ] F) (x : V) : F :=
  kochLammHeat0 t f₀ x +
    ∑ i : Fin (Module.finrank ℝ V),
      kochLammHeat1 t ((stdOrthonormalBasis ℝ V) i)
        (fun z ↦ f₁ z ((stdOrthonormalBasis ℝ V) i)) x

def kochLammBasisGrad (t : ℝ) (f₀ : ℝ × V → F)
    (f₁ : ℝ × V → V →L[ℝ] F) (x : V) : V →L[ℝ] F :=
  heatGrad0 t f₀ x +
    ∑ i : Fin (Module.finrank ℝ V),
      heatGrad1 t ((stdOrthonormalBasis ℝ V) i)
        (fun z ↦ f₁ z ((stdOrthonormalBasis ℝ V) i)) x

omit [CompleteSpace F] in
theorem kochLammBasisPot_eq {T t : ℝ} {A₁ A_q A₂ Aₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f₀ : ℝ × V → F)
    (f₁ : ℝ × V → V →L[ℝ] F) (x : V)
    (h₀ : KochLammSourceZero T A₁ A_q f₀) (h₁ : KochLammSourceOne T A₂ Aₚ f₁) :
    kochLammBasisPot t f₀ f₁ x =
      heatPot0 t f₀ x +
        ∑ i : Fin (Module.finrank ℝ V),
          heatPot1 t ((stdOrthonormalBasis ℝ V) i)
            (fun z ↦ f₁ z ((stdOrthonormalBasis ℝ V) i)) x := by
  unfold kochLammBasisPot
  rw [kochLammHeat0_eq_heatPot (V := V) ht htT f₀ x h₀]
  refine congrArg (fun z : F ↦ heatPot0 t f₀ x + z) ?_
  apply Finset.sum_congr rfl
  intro i _
  exact kochLammHeat1_eq_heatPot (V := V) ht htT
    ((stdOrthonormalBasis ℝ V) i)
    (fun z ↦ f₁ z ((stdOrthonormalBasis ℝ V) i)) x
    (kochLammFluxComp (V := V) f₁ h₁ i)

omit [Nontrivial V]
  [CompleteSpace F] in
@[simp] theorem kochLammBasisPot_zero (f₀ : ℝ × V → F)
    (f₁ : ℝ × V → V →L[ℝ] F) (x : V) :
    kochLammBasisPot 0 f₀ f₁ x = 0 := by
  classical
  simp [kochLammBasisPot, kochLammHeat0, kochLammHeat1, heatEarly0, heatEarly1,
    kochLammLatePotential, kochLammFluxPotential, kochLammTermMeasure]

omit [CompleteSpace F] in
theorem kochLammHeat0_sub {T t : ℝ} {A₁ A_q B₁ B_q : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f g : ℝ × V → F) (x : V)
    (hf : KochLammSourceZero T A₁ A_q f) (hg : KochLammSourceZero T B₁ B_q g) :
    kochLammHeat0 t (fun z ↦ f z - g z) x = kochLammHeat0 t f x - kochLammHeat0 t g x := by
  have hfE := kochLammEarly0_int (V := V) ht htT f x hf
  have hgE := kochLammEarly0_int (V := V) ht htT g x hg
  have hfL := kochLammLate0_int (V := V) ht htT f x hf
  have hgL := kochLammLate0_int (V := V) ht htT g x hg
  unfold kochLammHeat0 heatEarly0 kochLammLatePotential
  simp only [smul_sub, Real.sq_sqrt ht.le]
  rw [MeasureTheory.integral_sub hfE hgE,
    MeasureTheory.integral_sub hfL hgL]
  abel

omit [CompleteSpace F] in
theorem kochLammHeat1_sub {T t : ℝ} {A₂ Aₚ B₂ Bₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (w : V) (f g : ℝ × V → F) (x : V)
    (hf : KochLammSourceOne T A₂ Aₚ f) (hg : KochLammSourceOne T B₂ Bₚ g) :
    kochLammHeat1 t w (fun z ↦ f z - g z) x =
      kochLammHeat1 t w f x - kochLammHeat1 t w g x := by
  have hfE := kochLammEarly1_int (V := V) ht htT w f x hf
  have hgE := kochLammEarly1_int (V := V) ht htT w g x hg
  have hfL := kochLammLate1_int (V := V) ht htT w f x hf
  have hgL := kochLammLate1_int (V := V) ht htT w g x hg
  unfold kochLammHeat1 heatEarly1 kochLammFluxPotential
  simp only [smul_sub, Real.sq_sqrt ht.le]
  rw [MeasureTheory.integral_sub hfE hgE,
    MeasureTheory.integral_sub hfL hgL]
  abel

omit [CompleteSpace F] in
theorem kochLammBasisPot_sub {T t : ℝ}
    {A₁ A_q B₁ B_q A₂ Aₚ B₂ Bₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f₀ g₀ : ℝ × V → F)
    (f₁ g₁ : ℝ × V → V →L[ℝ] F) (x : V)
    (hf₀ : KochLammSourceZero T A₁ A_q f₀) (hg₀ : KochLammSourceZero T B₁ B_q g₀)
    (hf₁ : KochLammSourceOne T A₂ Aₚ f₁) (hg₁ : KochLammSourceOne T B₂ Bₚ g₁) :
    kochLammBasisPot t (fun z ↦ f₀ z - g₀ z) (fun z ↦ f₁ z - g₁ z) x =
      kochLammBasisPot t f₀ f₁ x - kochLammBasisPot t g₀ g₁ x := by
  classical
  unfold kochLammBasisPot
  rw [kochLammHeat0_sub (V := V) ht htT f₀ g₀ x hf₀ hg₀]
  have hsum :
      (∑ i : Fin (Module.finrank ℝ V),
        kochLammHeat1 t ((stdOrthonormalBasis ℝ V) i)
          (fun z ↦ (f₁ z - g₁ z) ((stdOrthonormalBasis ℝ V) i)) x) =
        (∑ i : Fin (Module.finrank ℝ V),
          kochLammHeat1 t ((stdOrthonormalBasis ℝ V) i)
            (fun z ↦ f₁ z ((stdOrthonormalBasis ℝ V) i)) x) -
          ∑ i : Fin (Module.finrank ℝ V),
            kochLammHeat1 t ((stdOrthonormalBasis ℝ V) i)
              (fun z ↦ g₁ z ((stdOrthonormalBasis ℝ V) i)) x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [sub_apply]
    exact kochLammHeat1_sub (V := V) ht htT
      ((stdOrthonormalBasis ℝ V) i)
      (fun z ↦ f₁ z ((stdOrthonormalBasis ℝ V) i))
      (fun z ↦ g₁ z ((stdOrthonormalBasis ℝ V) i)) x
      (kochLammFluxComp (V := V) f₁ hf₁ i)
      (kochLammFluxComp (V := V) g₁ hg₁ i)
  rw [hsum]
  abel

def kochLammVal0Bound (A₁ A_q : ℝ≥0) : ℝ≥0∞ :=
  earlyHeatC V * (A₁ : ℝ≥0∞) +
    ENNReal.ofReal
      (kochLammLateSeries (Module.finrank ℝ V) * (kochLammLateTailC V * (A_q : ℝ)))

def kochLammVal1Bound (A₂ Aₚ : ℝ≥0) : ℝ≥0∞ :=
  earlyFluxC V * (A₂ : ℝ≥0∞) *
      fluxShellSeries (Module.finrank ℝ V) +
    ENNReal.ofReal
      (kochLammFluxSeries (Module.finrank ℝ V) * (kochLammFluxTailC V * (Aₚ : ℝ)))

omit [CompleteSpace F] in
theorem kochLammBasisPot_norm {T t : ℝ} {A₁ A_q A₂ Aₚ : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f₀ : ℝ × V → F)
    (f₁ : ℝ × V → V →L[ℝ] F) (x : V)
    (h₀ : KochLammSourceZero T A₁ A_q f₀) (h₁ : KochLammSourceOne T A₂ Aₚ f₁) :
    ‖kochLammBasisPot t f₀ f₁ x‖ₑ ≤
      kochLammVal0Bound (V := V) A₁ A_q +
        (Module.finrank ℝ V : ℝ≥0∞) * kochLammVal1Bound (V := V) A₂ Aₚ := by
  classical
  let e := stdOrthonormalBasis ℝ V
  have hzero :
      ‖kochLammHeat0 t f₀ x‖ₑ ≤ kochLammVal0Bound (V := V) A₁ A_q := by
    simpa only [enorm_eq_nnnorm, kochLammVal0Bound] using
      (kochLammHeat0_norm (V := V) ht htT f₀ x h₀)
  have hone (i : Fin (Module.finrank ℝ V)) :
      ‖kochLammHeat1 t (e i) (fun z ↦ f₁ z (e i)) x‖ₑ ≤
        kochLammVal1Bound (V := V) A₂ Aₚ := by
    have hei : ‖e i‖ = 1 := e.norm_eq_one i
    have hi := kochLammHeat1_norm (V := V) ht htT (e i)
      (fun z ↦ f₁ z (e i)) x
      (by simpa only [e] using kochLammFluxComp (V := V) f₁ h₁ i)
    simpa only [enorm_eq_nnnorm, kochLammVal1Bound, hei, ENNReal.ofReal_one,
      one_mul] using hi
  have hsum :
      ‖∑ i : Fin (Module.finrank ℝ V),
          kochLammHeat1 t (e i) (fun z ↦ f₁ z (e i)) x‖ₑ ≤
        (Module.finrank ℝ V : ℝ≥0∞) *
          kochLammVal1Bound (V := V) A₂ Aₚ := by
    calc
      ‖∑ i : Fin (Module.finrank ℝ V),
          kochLammHeat1 t (e i) (fun z ↦ f₁ z (e i)) x‖ₑ ≤
          ∑ i : Fin (Module.finrank ℝ V),
            ‖kochLammHeat1 t (e i) (fun z ↦ f₁ z (e i)) x‖ₑ := by
              simpa using enorm_sum_le Finset.univ
                (fun i : Fin (Module.finrank ℝ V) ↦
                  kochLammHeat1 t (e i) (fun z ↦ f₁ z (e i)) x)
      _ ≤ ∑ _i : Fin (Module.finrank ℝ V),
          kochLammVal1Bound (V := V) A₂ Aₚ :=
        Finset.sum_le_sum fun i _ ↦ hone i
      _ = (Module.finrank ℝ V : ℝ≥0∞) *
          kochLammVal1Bound (V := V) A₂ Aₚ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  change
    ‖kochLammHeat0 t f₀ x +
      ∑ i : Fin (Module.finrank ℝ V),
        kochLammHeat1 t (e i) (fun z ↦ f₁ z (e i)) x‖ₑ ≤ _
  exact (enorm_add_le _ _).trans (add_le_add hzero hsum)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
