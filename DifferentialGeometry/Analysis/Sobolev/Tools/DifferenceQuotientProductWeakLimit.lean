import DifferentialGeometry.Analysis.Integration.Lp.SpatialSteklov
import DifferentialGeometry.Analysis.Sobolev.Tools.SteklovAverage
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialGraph

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory.Lp

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} [SFinite μ]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "X" => Lp ℝ 2 (μ.prod (volume : Measure E))

def spatialDiffQuot (k : Fin d) (h : ℝ) (u : X) : X :=
  h⁻¹ • (spatialTranslate (h • EuclideanSpace.single k 1) u - u)

theorem coeFn_spatialDiffQuot (k : Fin d) (h : ℝ) (u : X) :
    spatialDiffQuot k h u =ᵐ[μ.prod volume] fun p =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h (fun x => u (p.1, x)) p.2 := by
  by_cases hh : h = 0
  · subst h
    simp only [spatialDiffQuot, inv_zero, zero_smul,
      DifferentialGeometry.Analysis.Sobolev.diffQuot_zero_h, Pi.zero_apply]
    exact coeFn_zero _ _ _
  filter_upwards [coeFn_smul h⁻¹ (spatialTranslate (h • EuclideanSpace.single k 1) u - u),
    coeFn_sub (spatialTranslate (h • EuclideanSpace.single k 1) u) u,
    coeFn_spatialTranslate (h • EuclideanSpace.single k 1) u] with p hsmul hsub htrans
  change (h⁻¹ • (spatialTranslate (h • EuclideanSpace.single k 1) u - u) : X) p = _
  rw [hsmul, Pi.smul_apply, hsub, Pi.sub_apply, htrans,
    DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne k hh, smul_eq_mul]
  ring

theorem norm_spatialDiffQuot_eq (k : Fin d) (h : ℝ) (u : X) :
    ‖spatialDiffQuot k h u‖ =
      (eLpNorm (fun p : Z × E =>
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h (fun x => u (p.1, x)) p.2)
          2 (μ.prod volume)).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_spatialDiffQuot k h u)]

theorem norm_spatialDiffQuot_le (k : Fin d) (h : ℝ) (u : X) {C : ℝ} (hC : 0 ≤ C)
    (hbound : eLpNorm (fun p : Z × E =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h (fun x => u (p.1, x)) p.2)
        2 (μ.prod volume) ≤ ENNReal.ofReal C) :
    ‖spatialDiffQuot k h u‖ ≤ C := by
  rw [norm_spatialDiffQuot_eq]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hC)

end MeasureTheory.Lp


namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "X" => Lp ℝ 2 (μ.prod (volume : Measure E))

theorem ae_hasWeakPartialDeriv_spatialSteklovAverage (k : Fin d) (h : ℝ) (u : X) :
    ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => Lp.spatialDiffQuot k h u (t, x))
      (fun x => Lp.spatialSteklovAverage (EuclideanSpace.single k 1) h u (t, x)) univ := by
  filter_upwards [(Lp.memLp u).prodMk_left (by norm_num),
    Measure.ae_ae_of_ae_prod (Lp.coeFn_spatialDiffQuot k h u),
    Measure.ae_ae_of_ae_prod (Lp.coeFn_spatialSteklovAverage (EuclideanSpace.single k 1) h u)]
    with t ht hdiff hav
  have hweak := hasWeakPartialDeriv_integral_translate ht k h
  intro φ hφ hφc hφs
  have htest := hweak φ hφ hφc hφs
  simp only [Measure.restrict_univ] at htest ⊢
  have hl : (∫ x, Lp.spatialSteklovAverage (EuclideanSpace.single k 1) h u (t, x) *
        fderiv ℝ φ x (EuclideanSpace.single k 1)) =
      ∫ x, (h⁻¹ * ∫ r in (0 : ℝ)..h, u (t, x + r • EuclideanSpace.single k 1)) *
        fderiv ℝ φ x (EuclideanSpace.single k 1) := by
    apply integral_congr_ae
    filter_upwards [hav] with x hx
    rw [hx]
  have hr : (∫ x, Lp.spatialDiffQuot k h u (t, x) * φ x) =
      ∫ x, diffQuot k h (fun y => u (t, y)) x * φ x := by
    apply integral_congr_ae
    filter_upwards [hdiff] with x hx
    rw [hx]
  exact hl.trans (htest.trans (congrArg Neg.neg hr.symm))

private theorem positive_vanishing_steps {h₀ : ℝ} (hh₀ : 0 < h₀) :
    ∃ H : ℕ → ℝ, (∀ n, 0 < |H n| ∧ |H n| ≤ h₀) ∧
      Tendsto H atTop (𝓝[≠] 0) := by
  let H : ℕ → ℝ := fun n => h₀ / ((n : ℝ) + 1)
  have hpos (n : ℕ) : 0 < H n := div_pos hh₀ (by positivity)
  refine ⟨H, ?_, ?_⟩
  · intro n
    rw [abs_of_pos (hpos n)]
    refine ⟨hpos n, ?_⟩
    dsimp [H]
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · have ht : Tendsto H atTop (𝓝 0) := by
      simpa only [H, div_eq_mul_inv, one_div, one_mul, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul h₀
    exact tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall fun n => (hpos n).ne'⟩

theorem exists_ae_hasWeakPartialDeriv_of_spatial_diffQuot_uniform_bound
    (u : X) (k : Fin d) {C h₀ : ℝ} (hC : 0 ≤ C) (hh₀ : 0 < h₀)
    (hbound : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (fun p : ℝ × E => diffQuot k h (fun x => u (p.1, x)) p.2)
        2 (μ.prod volume) ≤ ENNReal.ofReal C) :
    ∃ v : X, ‖v‖ ≤ C ∧ ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => v (t, x)) (fun x => u (t, x)) univ := by
  let _ : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let _ : SecondCountableTopology X := Lp.SecondCountableTopology
  obtain ⟨H, hH, hHlim⟩ := positive_vanishing_steps hh₀
  let U : ℕ → X := fun n => Lp.spatialSteklovAverage (EuclideanSpace.single k 1) (H n) u
  let V : ℕ → X := fun n => Lp.spatialDiffQuot k (H n) u
  have hU : Tendsto U atTop (𝓝 u) :=
    (Lp.tendsto_spatialSteklovAverage (EuclideanSpace.single k 1) u).comp hHlim
  have hV (n : ℕ) : ‖V n‖ ≤ C :=
    Lp.norm_spatialDiffQuot_le k (H n) u hC (hbound (H n) (hH n).1 (hH n).2)
  have hw (n : ℕ) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => V n (t, x)) (fun x => U n (t, x)) univ :=
    ae_hasWeakPartialDeriv_spatialSteklovAverage k (H n) u
  have hcompact := fun (U V : ℕ → Lp ℝ 2 (μ.prod (volume.restrict (univ : Set E))))
    (u : Lp ℝ 2 (μ.prod (volume.restrict (univ : Set E)))) (C : ℝ) =>
      @Euclidean.exists_ae_hasWeakPartialDeriv_of_norm_bounded d ℝ _ μ univ inferInstance k U V u C
  rw [Measure.restrict_univ] at hcompact
  exact hcompact U V u C hU hV hw

end DifferentialGeometry.Analysis.Sobolev
