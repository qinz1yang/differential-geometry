import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDual
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.SteklovEnergy
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeOperatorH1

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private theorem measurePreserving_add_timeMeasure (a b : ℝ) :
    MeasurePreserving (fun s : ℝ => a + s) (timeMeasure (b - a))
      (volume.restrict (Icc a b)) := by
  have h := (measurePreserving_add_right volume a).restrict_image_emb
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding (Icc (0 : ℝ) (b - a))
  simpa only [timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel, add_comm a] using h

private theorem measurePreserving_sub_timeMeasure (a b : ℝ) :
    MeasurePreserving (fun t : ℝ => t - a) (volume.restrict (Icc a b))
      (timeMeasure (b - a)) := by
  have h := (measurePreserving_add_right volume (-a)).restrict_image_emb
    (Homeomorph.addRight (-a)).isClosedEmbedding.measurableEmbedding (Icc a b)
  simpa only [timeMeasure, image_add_const_Icc, add_neg_cancel, sub_eq_add_neg] using h



variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem timeL2.integral_mul_bilinear_le_of_forced_timeH1_test_identity
    {T : ℝ} (hT : 0 ≤ T) (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) (timeMeasure T))
    {CF : ℝ} (hCF : ∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ CF)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    (u : timeL2 X T) (ℓ : timeL2 (X →L[ℝ] ℝ) T)
    (htest : ∀ w : timeH1 X T, w.init = 0 → w.toFun T = 0 →
      (∫ t, F t (u t) (w.toFun t) ∂timeMeasure T) =
        (∫ t, B (u t) (w.deriv t) ∂timeMeasure T) +
          ∫ t, ℓ t (w.toFun t) ∂timeMeasure T)
    {ζ : ℝ → ℝ} (hζsmooth : ContDiff ℝ 1 ζ)
    (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) (hζ0 : ζ 0 = 0) (hζT : ζ T = 0) :
    (∫ t, ζ t * F t (u t) (u t) ∂timeMeasure T) ≤
      (3 * (K : ℝ) / 2) * ∫ t, B (u t) (u t) ∂timeMeasure T +
        ∫ t, ζ t * ℓ t (u t) ∂timeMeasure T := by
  apply u.integral_mul_bilinear_le_of_forced_cutoff_steklov_identity F hF hCF B hB hBpos
    ℓ hζsmooth hζ hζpos hζlip
  intro s hs
  let U : ℝ → X := (Icc (0 : ℝ) T).indicator u
  let W : ℝ → X := fun t => DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage s U t
  let Q : ℝ → X := fun t => s⁻¹ • (U (t + s) - U t)
  obtain ⟨w, hwi, hw, hwd, hwT⟩ :=
    exists_timeH1_cutoff_steklovAverage_timeL2 hT u s hζsmooth.contDiffOn hζ0 hζT
  have hW : MemLp W 2 (timeMeasure T) :=
    (memLp_congr_ae (timeL2.coeFn_steklovAverage s u)).mp (Lp.memLp (u.steklovAverage s))
  have hU : MemLp U 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).mpr (Lp.memLp u)
  have hQ : MemLp Q 2 (timeMeasure T) :=
    (((hU.comp_measurePreserving (measurePreserving_add_right volume s)).sub hU).const_smul s⁻¹).restrict _
  have hintB (v : ℝ → X) (hv : MemLp v 2 (timeMeasure T)) :
      Integrable (fun t => B (u t) (v t)) (timeMeasure T) :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable (fun _ => B)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl) (Lp.memLp u) hv
  have hβ : MemLp (_root_.deriv ζ) ∞ (timeMeasure T) :=
    memLp_top_of_bound hζsmooth.continuous_deriv_one.aestronglyMeasurable K
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hζlip)
  have hI₁ : Integrable (fun t => _root_.deriv ζ t * B (u t) (W t)) (timeMeasure T) :=
    (hintB W hW).mul_of_top_right hβ
  have hI₂ : Integrable (fun t => ζ t * B (u t) (Q t)) (timeMeasure T) :=
    (hintB Q hQ).mul_of_top_right (hζ.restrict (Icc (0 : ℝ) T))
  have hleft : (∫ t, F t (u t) (w.toFun t) ∂timeMeasure T) =
      ∫ t, ζ t * F t (u t) (W t) ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hw t ht, map_smul]
    rfl
  have hmass : (∫ t, B (u t) (w.deriv t) ∂timeMeasure T) =
      (∫ t, _root_.deriv ζ t * B (u t) (W t) ∂timeMeasure T) +
        ∫ t, ζ t * B (u t) (Q t) ∂timeMeasure T := by
    rw [← integral_add hI₁ hI₂]
    apply integral_congr_ae
    filter_upwards [hwd] with t ht
    rw [ht, map_add, map_smul, map_smul]
    rfl
  have hsource : (∫ t, ℓ t (w.toFun t) ∂timeMeasure T) =
      ∫ t, ζ t * ℓ t (W t) ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hw t ht, map_smul]
    rfl
  have h := htest w hwi hwT
  rw [hleft, hmass, hsource] at h
  exact h

theorem timeL2.integral_bilinear_eq_of_timeH1_mass_dual
    {T : ℝ} (hT : 0 ≤ T) (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) (timeMeasure T))
    {CF : ℝ} (hCF : ∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ CF)
    (B : X →L[ℝ] X →L[ℝ] ℝ)
    (u : timeL2 X T) (ℓ : timeL2 (X →L[ℝ] ℝ) T)
    (w : timeH1 (X →L[ℝ] ℝ) T)
    (hwmass : w.toFun =ᵐ[timeMeasure T] fun t => B (u t))
    (hwderiv : w.deriv =ᵐ[timeMeasure T] fun t => ℓ t - F t (u t))
    (v : timeH1 X T) (hv0 : v.init = 0) (hvT : v.toFun T = 0) :
    (∫ t, F t (u t) (v.toFun t) ∂timeMeasure T) =
      (∫ t, B (u t) (v.deriv t) ∂timeMeasure T) +
        ∫ t, ℓ t (v.toFun t) ∂timeMeasure T := by
  have h := timeH1.integral_dual_deriv_add_deriv_dual hT w v
  have hvzero : v.toFun 0 = 0 := by simpa only [timeH1.toFun_zero] using hv0
  rw [hvT, hvzero, map_zero, map_zero, sub_self] at h
  have hvmem : MemLp v.toFun 2 (timeMeasure T) := memLp_of_continuousOn v.continuousOn_toFun
  have hsource : Integrable (fun t => ℓ t (v.toFun t)) (timeMeasure T) :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable
      (fun _ => ContinuousLinearMap.id ℝ (X →L[ℝ] ℝ))
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl)
      (Lp.memLp ℓ) hvmem
  have hform : Integrable (fun t => F t (u t) (v.toFun t)) (timeMeasure T) :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable F hF hCF (Lp.memLp u) hvmem
  have hm : (∫ t, w.toFun t (v.deriv t) ∂timeMeasure T) =
      ∫ t, B (u t) (v.deriv t) ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [hwmass] with t ht
    exact congrArg (fun L : X →L[ℝ] ℝ => L (v.deriv t)) ht
  have hd : (∫ t, w.deriv t (v.toFun t) ∂timeMeasure T) =
      (∫ t, ℓ t (v.toFun t) ∂timeMeasure T) -
        ∫ t, F t (u t) (v.toFun t) ∂timeMeasure T := by
    rw [← integral_sub hsource hform]
    apply integral_congr_ae
    filter_upwards [hwderiv] with t ht
    exact congrArg (fun L : X →L[ℝ] ℝ => L (v.toFun t)) ht
  rw [hm, hd] at h
  linarith only [h]

theorem timeL2.integral_mul_bilinear_le_of_timeH1_mass_dual
    {T : ℝ} (hT : 0 ≤ T) (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) (timeMeasure T))
    {CF : ℝ} (hCF : ∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ CF)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    (u : timeL2 X T) (ℓ : timeL2 (X →L[ℝ] ℝ) T)
    (w : timeH1 (X →L[ℝ] ℝ) T)
    (hwmass : w.toFun =ᵐ[timeMeasure T] fun t => B (u t))
    (hwderiv : w.deriv =ᵐ[timeMeasure T] fun t => ℓ t - F t (u t))
    {ζ : ℝ → ℝ} (hζsmooth : ContDiff ℝ 1 ζ)
    (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) (hζ0 : ζ 0 = 0) (hζT : ζ T = 0) :
    (∫ t, ζ t * F t (u t) (u t) ∂timeMeasure T) ≤
      (3 * (K : ℝ) / 2) * ∫ t, B (u t) (u t) ∂timeMeasure T +
        ∫ t, ζ t * ℓ t (u t) ∂timeMeasure T := by
  exact u.integral_mul_bilinear_le_of_forced_timeH1_test_identity hT F hF hCF B hB hBpos ℓ
    (fun v hv0 hvT => u.integral_bilinear_eq_of_timeH1_mass_dual hT F hF hCF B ℓ w hwmass
      hwderiv v hv0 hvT) hζsmooth hζ hζpos hζlip hζ0 hζT

theorem timeL2.integral_mul_bilinear_le_of_timeH1_mass_dual_integral
    {T : ℝ} (hT : 0 ≤ T) (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) (timeMeasure T))
    {CF : ℝ} (hCF : ∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ CF)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    (u : timeL2 X T) (ℓ : timeL2 (X →L[ℝ] ℝ) T)
    (w : timeH1 (X →L[ℝ] ℝ) T)
    (hwmass : w.toFun =ᵐ[timeMeasure T] fun t => B (u t))
    (hpair : ∀ z : timeL2 X T,
      (∫ t, w.deriv t (z t) ∂timeMeasure T) =
        (∫ t, ℓ t (z t) ∂timeMeasure T) -
          ∫ t, F t (u t) (z t) ∂timeMeasure T)
    {ζ : ℝ → ℝ} (hζsmooth : ContDiff ℝ 1 ζ)
    (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) (hζ0 : ζ 0 = 0) (hζT : ζ T = 0) :
    (∫ t, ζ t * F t (u t) (u t) ∂timeMeasure T) ≤
      (3 * (K : ℝ) / 2) * ∫ t, B (u t) (u t) ∂timeMeasure T +
        ∫ t, ζ t * ℓ t (u t) ∂timeMeasure T := by
  refine u.integral_mul_bilinear_le_of_forced_timeH1_test_identity hT F hF hCF B hB hBpos ℓ
    ?_ hζsmooth hζ hζpos hζlip hζ0 hζT
  intro v hv0 hvT
  have h := timeH1.integral_dual_deriv_add_deriv_dual hT w v
  have hvzero : v.toFun 0 = 0 := by simpa only [timeH1.toFun_zero] using hv0
  rw [hvT, hvzero, map_zero, map_zero, sub_self] at h
  have hm : (∫ t, w.toFun t (v.deriv t) ∂timeMeasure T) =
      ∫ t, B (u t) (v.deriv t) ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [hwmass] with t ht
    exact congrArg (fun L : X →L[ℝ] ℝ => L (v.deriv t)) ht
  have hrep : (v.toFunL2 : ℝ → X) =ᵐ[timeMeasure T] v.toFun :=
    TimeSobolev.coeFn_ofContinuousOn v.continuousOn_toFun
  have heq (L : ℝ → X →L[ℝ] ℝ) :
      (∫ t, L t (v.toFunL2 t) ∂timeMeasure T) = ∫ t, L t (v.toFun t) ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [hrep] with t ht
    exact congrArg (L t) ht
  have hd := hpair v.toFunL2
  rw [heq, heq, heq] at hd
  rw [hm, hd] at h
  linarith only [h]



theorem integral_mul_bilinear_le_of_timeH1_mass_dual_integral_on
    {a b : ℝ} (hab : a ≤ b) (μ : Measure ℝ) (hμ : μ = volume.restrict (Icc a b))
    (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) μ)
    {CF : ℝ} (hCF : ∀ᵐ t ∂μ, ‖F t‖ ≤ CF)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    (u : Lp X 2 μ)
    (ℓ β : Lp (X →L[ℝ] ℝ) 2 μ)
    (w : timeH1 (X →L[ℝ] ℝ) (b - a))
    (hwmass : w.toFun =ᵐ[timeMeasure (b - a)] fun s => B (u (a + s)))
    (hwderiv : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (hpair : ∀ z : Lp X 2 μ,
      (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
        ∫ t, F t (u t) (z t) ∂μ)
    {ζ : ℝ → ℝ} (hζsmooth : ContDiff ℝ 1 ζ)
    (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) (hζ0 : ζ 0 = 0) (hζb : ζ (b - a) = 0) :
    (∫ s, ζ s * F (a + s) (u (a + s)) (u (a + s)) ∂timeMeasure (b - a)) ≤
      (3 * (K : ℝ) / 2) * ∫ s, B (u (a + s)) (u (a + s)) ∂timeMeasure (b - a) +
        ∫ s, ζ s * β (a + s) (u (a + s)) ∂timeMeasure (b - a) := by
  subst μ
  let hf := measurePreserving_add_timeMeasure a b
  let hb := measurePreserving_sub_timeMeasure a b
  let U : timeL2 X (b - a) := Lp.compMeasurePreserving (fun s => a + s) hf u
  let P : timeL2 (X →L[ℝ] ℝ) (b - a) := Lp.compMeasurePreserving (fun s => a + s) hf β
  have hU : (U : ℝ → X) =ᵐ[timeMeasure (b - a)] fun s => u (a + s) :=
    Lp.coeFn_compMeasurePreserving u hf
  have hP : (P : ℝ → X →L[ℝ] ℝ) =ᵐ[timeMeasure (b - a)] fun s => β (a + s) :=
    Lp.coeFn_compMeasurePreserving β hf
  have hm : w.toFun =ᵐ[timeMeasure (b - a)] fun s => B (U s) := by
    filter_upwards [hwmass, hU] with s hs hu
    exact hs.trans (congrArg B hu).symm
  have hp : ∀ z : timeL2 X (b - a),
      (∫ s, w.deriv s (z s) ∂timeMeasure (b - a)) =
        (∫ s, P s (z s) ∂timeMeasure (b - a)) -
          ∫ s, F (a + s) (U s) (z s) ∂timeMeasure (b - a) := by
    intro z
    let Z : Lp X 2 (volume.restrict (Icc a b)) :=
      Lp.compMeasurePreserving (fun t => t - a) hb z
    have hZ : (Z : ℝ → X) =ᵐ[volume.restrict (Icc a b)] fun t => z (t - a) :=
      Lp.coeFn_compMeasurePreserving z hb
    have hZshift : (fun s => Z (a + s)) =ᵐ[timeMeasure (b - a)] z := by
      filter_upwards [hf.quasiMeasurePreserving.ae hZ] with s hs
      simpa only [add_sub_cancel_left] using hs
    have ht (L : ℝ → X → ℝ) :
        (∫ t in Icc a b, L t (Z t)) = ∫ s, L (a + s) (z s) ∂timeMeasure (b - a) := by
      apply (hf.integral_comp (Homeomorph.addLeft a).isClosedEmbedding.measurableEmbedding
        (fun t => L t (Z t))).symm.trans
      exact integral_congr_ae (hZshift.mono fun s hs => congrArg (L (a + s)) hs)
    have h := hpair Z
    rw [ht, ht, ht] at h
    have hd : (∫ s, w.deriv s (z s) ∂timeMeasure (b - a)) =
        ∫ s, ℓ (a + s) (z s) ∂timeMeasure (b - a) := by
      exact integral_congr_ae (hwderiv.mono fun s hs => congrArg (fun L : X →L[ℝ] ℝ => L (z s)) hs)
    have hβ : (∫ s, P s (z s) ∂timeMeasure (b - a)) =
        ∫ s, β (a + s) (z s) ∂timeMeasure (b - a) := by
      exact integral_congr_ae (hP.mono fun s hs => congrArg (fun L : X →L[ℝ] ℝ => L (z s)) hs)
    have hu : (∫ s, F (a + s) (U s) (z s) ∂timeMeasure (b - a)) =
        ∫ s, F (a + s) (u (a + s)) (z s) ∂timeMeasure (b - a) := by
      exact integral_congr_ae (hU.mono fun s hs => congrArg (fun x => F (a + s) x (z s)) hs)
    exact hd.trans (h.trans (congrArg₂ (fun x y : ℝ => x - y) hβ.symm hu.symm))
  have h := U.integral_mul_bilinear_le_of_timeH1_mass_dual_integral (sub_nonneg.mpr hab)
    (fun s => F (a + s))
    (fun x y => (hF x y).comp_quasiMeasurePreserving hf.quasiMeasurePreserving)
    (hf.quasiMeasurePreserving.ae hCF) B hB hBpos P w hm hp
    hζsmooth hζ hζpos hζlip hζ0 hζb
  have hleft : (∫ s, ζ s * F (a + s) (U s) (U s) ∂timeMeasure (b - a)) =
      ∫ s, ζ s * F (a + s) (u (a + s)) (u (a + s)) ∂timeMeasure (b - a) := by
    exact integral_congr_ae (hU.mono fun s hs => congrArg (fun x => ζ s * F (a + s) x x) hs)
  have hmass : (∫ s, B (U s) (U s) ∂timeMeasure (b - a)) =
      ∫ s, B (u (a + s)) (u (a + s)) ∂timeMeasure (b - a) := by
    exact integral_congr_ae (hU.mono fun s hs => congrArg (fun x => B x x) hs)
  have hsource : (∫ s, ζ s * P s (U s) ∂timeMeasure (b - a)) =
      ∫ s, ζ s * β (a + s) (u (a + s)) ∂timeMeasure (b - a) := by
    apply integral_congr_ae
    filter_upwards [hP, hU] with s hs hu
    exact congrArg₂ (fun L x => ζ s * L x) hs hu
  rw [hleft, hmass, hsource] at h
  exact h



theorem timeL2.integral_mul_bilinear_comp_le_of_forced_timeH1_test_identity
    {T : ℝ} (hT : 0 ≤ T) (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) (timeMeasure T))
    {CF : ℝ} (hCF : ∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ CF)
    (B : X →L[ℝ] X →L[ℝ] ℝ)
    (u : timeL2 X T) (ℓ : timeL2 (X →L[ℝ] ℝ) T)
    (htest : ∀ w : timeH1 X T, w.init = 0 → w.toFun T = 0 →
      (∫ t, B (u t) (w.deriv t) ∂timeMeasure T) +
        (∫ t, F t (u t) (w.toFun t) ∂timeMeasure T) =
          ∫ t, ℓ t (w.toFun t) ∂timeMeasure T)
    (L : X →L[ℝ] X)
    (hBL : (-(B.bilinearComp (ContinuousLinearMap.id ℝ X) L)).flip =
      -(B.bilinearComp (ContinuousLinearMap.id ℝ X) L))
    (hBLpos : ∀ x, 0 ≤ -(B x (L x)))
    {ζ : ℝ → ℝ} (hζsmooth : ContDiff ℝ 1 ζ)
    (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) (hζ0 : ζ 0 = 0) (hζT : ζ T = 0) :
    (∫ t, ζ t * F t (u t) (L (u t)) ∂timeMeasure T) ≤
      (3 * (K : ℝ) / 2) * ∫ t, -(B (u t) (L (u t))) ∂timeMeasure T +
        ∫ t, ζ t * ℓ t (L (u t)) ∂timeMeasure T := by
  let FL : ℝ → X →L[ℝ] X →L[ℝ] ℝ := fun t =>
    (F t).bilinearComp (ContinuousLinearMap.id ℝ X) L
  let BL : X →L[ℝ] X →L[ℝ] ℝ :=
    -(B.bilinearComp (ContinuousLinearMap.id ℝ X) L)
  let precomp : (X →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ L
  let ℓL := precomp.compLpL 2 (timeMeasure T) ℓ
  have hℓL : ℓL =ᵐ[timeMeasure T] fun t => (ℓ t).comp L :=
    precomp.coeFn_compLpL ℓ
  have hFL : ∀ x y, AEStronglyMeasurable (fun t => FL t x y) (timeMeasure T) :=
    fun x y => hF x (L y)
  have hFLnorm : ∀ᵐ t ∂timeMeasure T, ‖FL t‖ ≤ max CF 0 * ‖L‖ := by
    filter_upwards [hCF] with t ht
    dsimp only [FL]
    rw [ContinuousLinearMap.bilinearComp, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.opNorm_flip]
    exact ((F t).flip.opNorm_comp_le L).trans (by
      rw [ContinuousLinearMap.opNorm_flip]
      exact mul_le_mul_of_nonneg_right (ht.trans (le_max_left _ _)) (norm_nonneg _))
  have htestL : ∀ w : timeH1 X T, w.init = 0 → w.toFun T = 0 →
      (∫ t, FL t (u t) (w.toFun t) ∂timeMeasure T) =
        (∫ t, BL (u t) (w.deriv t) ∂timeMeasure T) +
          ∫ t, ℓL t (w.toFun t) ∂timeMeasure T := by
    intro w hw0 hwT
    let v := timeOpH1 (fun _ : ℝ => L) contDiffOn_const w
    have hv0 : v.init = 0 := by
      rw [timeOpH1_init, hw0, map_zero]
    have hvT : v.toFun T = 0 := by
      rw [timeOpH1_toFun _ _ _ ⟨hT, le_rfl⟩, hwT, map_zero]
    have hv : ∀ᵐ t ∂timeMeasure T, v.toFun t = L (w.toFun t) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact timeOpH1_toFun _ _ _ ht
    have hvd : v.deriv =ᵐ[timeMeasure T] fun t => L (w.deriv t) := by
      simpa only [deriv_const, zero_apply, zero_add] using
        timeOpH1_deriv_ae (fun _ : ℝ => L) contDiffOn_const w
    have h := htest v hv0 hvT
    have hmass : (∫ t, B (u t) (v.deriv t) ∂timeMeasure T) =
        -(∫ t, BL (u t) (w.deriv t) ∂timeMeasure T) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [hvd] with t ht
      rw [ht]
      simp only [BL, neg_apply, ContinuousLinearMap.bilinearComp_apply,
        ContinuousLinearMap.id_apply, neg_neg]
    have hform : (∫ t, F t (u t) (v.toFun t) ∂timeMeasure T) =
        ∫ t, FL t (u t) (w.toFun t) ∂timeMeasure T := by
      apply integral_congr_ae
      filter_upwards [hv] with t ht
      rw [ht]
      rfl
    have hsource : (∫ t, ℓ t (v.toFun t) ∂timeMeasure T) =
        ∫ t, ℓL t (w.toFun t) ∂timeMeasure T := by
      apply integral_congr_ae
      filter_upwards [hv, hℓL] with t ht hℓt
      rw [ht, hℓt]
      rfl
    rw [hmass, hform, hsource] at h
    linarith only [h]
  have henergy := u.integral_mul_bilinear_le_of_forced_timeH1_test_identity hT FL hFL
    hFLnorm BL hBL hBLpos ℓL htestL hζsmooth hζ hζpos hζlip hζ0 hζT
  have hsource : (∫ t, ζ t * ℓL t (u t) ∂timeMeasure T) =
      ∫ t, ζ t * ℓ t (L (u t)) ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [hℓL] with t ht
    rw [ht]
    rfl
  rw [hsource] at henergy
  exact henergy


theorem integral_neg_bilinear_comp_le_of_timeH1_mass_dual_integral_on
    {a b : ℝ} (hab : a ≤ b) (μ : Measure ℝ) (hμ : μ = volume.restrict (Icc a b))
    (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) μ)
    {CF : ℝ} (hCF : ∀ᵐ t ∂μ, ‖F t‖ ≤ CF)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (u : Lp X 2 μ)
    (ℓ β : Lp (X →L[ℝ] ℝ) 2 μ)
    (w : timeH1 (X →L[ℝ] ℝ) (b - a))
    (hwmass : w.toFun =ᵐ[timeMeasure (b - a)] fun s => B (u (a + s)))
    (hwderiv : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (hpair : ∀ z : Lp X 2 μ,
      (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
        ∫ t, F t (u t) (z t) ∂μ)
    (L : X →L[ℝ] X)
    (hBL : (-(B.bilinearComp (ContinuousLinearMap.id ℝ X) L)).flip =
      -(B.bilinearComp (ContinuousLinearMap.id ℝ X) L))
    (hBLpos : ∀ x, 0 ≤ -(B x (L x)))
    {ζ : ℝ → ℝ} (hζsmooth : ContDiff ℝ 1 ζ)
    (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) (hζ0 : ζ 0 = 0) (hζb : ζ (b - a) = 0) :
    (∫ s, ζ s * -(F (a + s) (u (a + s)) (L (u (a + s)))) ∂timeMeasure (b - a)) ≤
      (3 * (K : ℝ) / 2) * ∫ s, -(B (u (a + s)) (L (u (a + s)))) ∂timeMeasure (b - a) +
        ∫ s, ζ s * -(β (a + s) (L (u (a + s)))) ∂timeMeasure (b - a) := by
  let P : (X →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ) := -(ContinuousLinearMap.precomp ℝ L)
  let FL : ℝ → X →L[ℝ] X →L[ℝ] ℝ := fun t =>
    -((F t).bilinearComp (ContinuousLinearMap.id ℝ X) L)
  let BL : X →L[ℝ] X →L[ℝ] ℝ :=
    -(B.bilinearComp (ContinuousLinearMap.id ℝ X) L)
  let ℓL := P.compLpL 2 μ ℓ
  let βL := P.compLpL 2 μ β
  let wL := timeOpH1 (fun _ : ℝ => P) contDiffOn_const w
  have hℓL : ℓL =ᵐ[μ] fun t => -((ℓ t).comp L) := P.coeFn_compLpL ℓ
  have hβL : βL =ᵐ[μ] fun t => -((β t).comp L) := P.coeFn_compLpL β
  have hFL : ∀ x y, AEStronglyMeasurable (fun t => FL t x y) μ :=
    fun x y => (hF x (L y)).neg
  have hFLnorm : ∀ᵐ t ∂μ, ‖FL t‖ ≤ max CF 0 * ‖L‖ := by
    filter_upwards [hCF] with t ht
    dsimp only [FL]
    rw [ContinuousLinearMap.opNorm_neg, ContinuousLinearMap.bilinearComp, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.opNorm_flip]
    exact ((F t).flip.opNorm_comp_le L).trans (by
      rw [ContinuousLinearMap.opNorm_flip]
      exact mul_le_mul_of_nonneg_right (ht.trans (le_max_left _ _)) (norm_nonneg _))
  have hshift : MeasurePreserving (fun s : ℝ => a + s) (timeMeasure (b - a)) μ := by
    rw [hμ]
    have h := (measurePreserving_add_right volume a).restrict_image_emb
      (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding (Icc (0 : ℝ) (b - a))
    simpa only [timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel, add_comm a] using h
  have hwLmass : wL.toFun =ᵐ[timeMeasure (b - a)] fun s => BL (u (a + s)) := by
    filter_upwards [hwmass, ae_restrict_mem measurableSet_Icc] with s hs hsmem
    rw [timeOpH1_toFun _ _ _ hsmem, hs]
    rfl
  have hwLderiv : wL.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓL (a + s) := by
    have hd : wL.deriv =ᵐ[timeMeasure (b - a)] fun s => P (w.deriv s) := by
      simpa only [deriv_const, zero_apply, zero_add] using
        timeOpH1_deriv_ae (fun _ : ℝ => P) contDiffOn_const w
    filter_upwards [hd, hwderiv, hshift.quasiMeasurePreserving.ae hℓL] with s hs hds hℓs
    rw [hs, hds, hℓs]
    rfl
  have hpairL : ∀ z : Lp X 2 μ,
      (∫ t, ℓL t (z t) ∂μ) = (∫ t, βL t (z t) ∂μ) -
        ∫ t, FL t (u t) (z t) ∂μ := by
    intro z
    let zL := L.compLpL 2 μ z
    have hzL : zL =ᵐ[μ] fun t => L (z t) := L.coeFn_compLpL z
    have hp (ψ : Lp (X →L[ℝ] ℝ) 2 μ) :
        (∫ t, (P.compLpL 2 μ ψ) t (z t) ∂μ) = -(∫ t, ψ t (zL t) ∂μ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [P.coeFn_compLpL ψ, hzL] with t hpt hzt
      rw [hpt, hzt]
      rfl
    have hf : (∫ t, FL t (u t) (z t) ∂μ) = -(∫ t, F t (u t) (zL t) ∂μ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [hzL] with t hzt
      rw [hzt]
      rfl
    rw [hp ℓ, hp β, hf, hpair zL]
    ring
  have h := integral_mul_bilinear_le_of_timeH1_mass_dual_integral_on hab μ hμ FL hFL hFLnorm
    BL hBL hBLpos u ℓL βL wL hwLmass hwLderiv hpairL hζsmooth hζ hζpos hζlip hζ0 hζb
  have hsource : (∫ s, ζ s * βL (a + s) (u (a + s)) ∂timeMeasure (b - a)) =
      ∫ s, ζ s * -(β (a + s) (L (u (a + s)))) ∂timeMeasure (b - a) := by
    apply integral_congr_ae
    filter_upwards [hshift.quasiMeasurePreserving.ae hβL] with s hs
    rw [hs]
    rfl
  rw [hsource] at h
  exact h


end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
