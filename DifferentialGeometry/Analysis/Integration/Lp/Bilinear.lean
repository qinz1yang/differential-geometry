import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable
    {P X Y : Type*} [MeasurableSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {μ : Measure P} (A : P → X →L[ℝ] Y)
    (hA : ∀ x, AEStronglyMeasurable (fun p => A p x) μ)
    (u : P → X) (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun p => A p (u p)) μ := by
  classical
  let u' : P → X := hu.mk u
  have hu' : StronglyMeasurable u' := hu.stronglyMeasurable_mk
  let s : ℕ → SimpleFunc P X := hu'.approx
  have hs (m : ℕ) : AEStronglyMeasurable (fun p => A p (s m p)) μ := by
    let F : P → Y := fun p =>
      ∑ x ∈ (s m).range, (s m ⁻¹' {x}).indicator (fun r => A r x) p
    have hF : AEStronglyMeasurable F μ := by
      let F' : P → Y :=
        ∑ x ∈ (s m).range, (s m ⁻¹' {x}).indicator (fun r => A r x)
      have hF' : AEStronglyMeasurable F' μ :=
        Finset.aestronglyMeasurable_sum (s m).range (fun x _ =>
          (hA x).indicator ((s m).measurableSet_fiber x))
      have hFF' : F = F' := by
        funext p
        simp only [F, F', Finset.sum_apply]
      exact hFF' ▸ hF'
    refine hF.congr (Eventually.of_forall fun p => ?_)
    dsimp only [F]
    rw [Finset.sum_eq_single (s m p)]
    · apply Set.indicator_of_mem
      change (s m p) ∈ ({s m p} : Set X)
      exact Set.mem_singleton _
    · intro x hx hne
      rw [Set.indicator_of_notMem]
      exact fun hmem => hne hmem.symm
    · exact fun hmem => (hmem ((s m).mem_range_self p)).elim
  refine aestronglyMeasurable_of_tendsto_ae atTop hs ?_
  filter_upwards [hu.ae_eq_mk] with p hup
  have hs_tendsto : Tendsto (fun m => s m p) atTop (nhds (u' p)) :=
    hu'.tendsto_approx p
  have happly : Tendsto (fun m => A p (s m p)) atTop (nhds (A p (u' p))) :=
    (A p).continuous.continuousAt.tendsto.comp hs_tendsto
  simpa only [u', hup] using happly

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace MeasureTheory

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem integrable_bilinear_of_apply_aestronglyMeasurable
    {P : Type*} [MeasurableSpace P] {μ : Measure P}
    (B : P → X →L[ℝ] Y →L[ℝ] Z)
    (hB : ∀ x y, AEStronglyMeasurable (fun t => B t x y) μ)
    {C : ℝ} (hC : ∀ᵐ t ∂μ, ‖B t‖ ≤ C)
    {u : P → X} (hu : MemLp u 2 μ) {v : P → Y} (hv : MemLp v 2 μ) :
    Integrable (fun t => B t (u t) (v t)) μ := by
  have hmeas : AEStronglyMeasurable (fun t => B t (u t) (v t)) μ := by
    apply DifferentialGeometry.Analysis.Parabolic.TimeSobolev.AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable
      (fun t => B t (u t)) _ v hv.aestronglyMeasurable
    intro y
    exact DifferentialGeometry.Analysis.Parabolic.TimeSobolev.AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable
      (fun t => (B t).flip y) (fun x => hB x y) u hu.aestronglyMeasurable
  have hprod : Integrable (fun t => ‖u t‖ * ‖v t‖) μ :=
    hu.norm.integrable_mul hv.norm
  refine (hprod.const_mul C).mono' hmeas ?_
  filter_upwards [hC] with t ht
  calc
    ‖B t (u t) (v t)‖ ≤ ‖B t‖ * ‖u t‖ * ‖v t‖ := (B t).le_opNorm₂ _ _
    _ ≤ C * (‖u t‖ * ‖v t‖) := by
      calc
        _ ≤ C * ‖u t‖ * ‖v t‖ := by gcongr
        _ = _ := mul_assoc _ _ _

end MeasureTheory

namespace MeasureTheory

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
private theorem integral_norm_mul_norm_le_lp_norm
    {P : Type*} [MeasurableSpace P] {μ : Measure P}
    (u : Lp X 2 μ) (v : Lp Y 2 μ) :
    (∫ t, ‖u t‖ * ‖v t‖ ∂μ) ≤ ‖u‖ * ‖v‖ := by
  let uN : Lp ℝ 2 μ := (Lp.memLp u).norm.toLp (fun t => ‖u t‖)
  let vN : Lp ℝ 2 μ := (Lp.memLp v).norm.toLp (fun t => ‖v t‖)
  have hpair : (∫ t, ‖u t‖ * ‖v t‖ ∂μ) = inner ℝ uN vN := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(Lp.memLp u).norm.coeFn_toLp, (Lp.memLp v).norm.coeFn_toLp]
      with t hu hv
    simp only [Real.inner_apply]
    change ‖u t‖ * ‖v t‖ = uN t * vN t
    rw [show uN t = ‖u t‖ from hu, show vN t = ‖v t‖ from hv]
  have hun : ‖uN‖ = ‖u‖ := by rw [Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]
  have hvn : ‖vN‖ = ‖v‖ := by rw [Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]
  rw [hpair, ← hun, ← hvn]
  exact real_inner_le_norm _ _

theorem norm_integral_bilinear_le_lp_norm
    {P : Type*} [MeasurableSpace P] {μ : Measure P}
    (B : P → X →L[ℝ] Y →L[ℝ] Z)
    (hB : ∀ x y, AEStronglyMeasurable (fun t => B t x y) μ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ t ∂μ, ‖B t‖ ≤ C)
    (u : Lp X 2 μ) (v : Lp Y 2 μ) :
    ‖∫ t, B t (u t) (v t) ∂μ‖ ≤ C * (‖u‖ * ‖v‖) := by
  have hint := integrable_bilinear_of_apply_aestronglyMeasurable B hB hC
    (Lp.memLp u) (Lp.memLp v)
  have hprod : Integrable (fun t => ‖u t‖ * ‖v t‖) μ :=
    (Lp.memLp u).norm.integrable_mul (Lp.memLp v).norm
  calc
    _ ≤ ∫ t, ‖B t (u t) (v t)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, C * (‖u t‖ * ‖v t‖) ∂μ := by
      apply integral_mono_ae hint.norm (hprod.const_mul C)
      filter_upwards [hC] with t ht
      calc
        _ ≤ ‖B t‖ * ‖u t‖ * ‖v t‖ := (B t).le_opNorm₂ _ _
        _ ≤ C * (‖u t‖ * ‖v t‖) := by
          calc
            _ ≤ C * ‖u t‖ * ‖v t‖ := by gcongr
            _ = _ := mul_assoc _ _ _
    _ = C * ∫ t, ‖u t‖ * ‖v t‖ ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_norm_mul_norm_le_lp_norm u v) hC0

theorem continuous_integral_bilinear_lp_right
    {P : Type*} [MeasurableSpace P] {μ : Measure P}
    (B : P → X →L[ℝ] Y →L[ℝ] Z)
    (hB : ∀ x y, AEStronglyMeasurable (fun t => B t x y) μ)
    {C : ℝ} (hC : ∀ᵐ t ∂μ, ‖B t‖ ≤ C) (u : Lp X 2 μ) :
    Continuous (fun v : Lp Y 2 μ => ∫ t, B t (u t) (v t) ∂μ) := by
  have hC' : ∀ᵐ t ∂μ, ‖B t‖ ≤ max 0 C := hC.mono fun _ ht => ht.trans (le_max_right 0 C)
  apply LipschitzWith.continuous (K := ⟨max 0 C * ‖u‖, mul_nonneg (le_max_left 0 C) (norm_nonneg _)⟩)
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have hid : (∫ t, B t (u t) (v t) ∂μ) - (∫ t, B t (u t) (w t) ∂μ) =
      ∫ t, B t (u t) ((v - w) t) ∂μ := by
    rw [← integral_sub
      (integrable_bilinear_of_apply_aestronglyMeasurable B hB hC (Lp.memLp u) (Lp.memLp v))
      (integrable_bilinear_of_apply_aestronglyMeasurable B hB hC (Lp.memLp u) (Lp.memLp w))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub v w] with t ht
    rw [ht, Pi.sub_apply, map_sub]
  rw [dist_eq_norm, hid, dist_eq_norm]
  exact (norm_integral_bilinear_le_lp_norm B hB (le_max_left 0 C) hC' u (v - w)).trans_eq
    (mul_assoc _ _ _).symm

end MeasureTheory
