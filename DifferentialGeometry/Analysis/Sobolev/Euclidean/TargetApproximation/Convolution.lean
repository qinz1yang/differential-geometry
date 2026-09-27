import DifferentialGeometry.Analysis.Integration.Convolution.Range
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Poincare
import DifferentialGeometry.Analysis.Integration.BallBoundary
import DifferentialGeometry.Analysis.Integration.Measure.UniformIntegrability
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Retraction
import DifferentialGeometry.Analysis.Integration.Lp.Composition
import DifferentialGeometry.External.DeGiorgi.Localization
import Mathlib.Analysis.Calculus.ContDiff.Convolution

noncomputable section

open Set MeasureTheory ContinuousLinearMap
open scoped Convolution

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {ι : Type*} [Fintype ι]

local notation "F" => EuclideanSpace ℝ ι

theorem exists_normed_convolution_mem_of_integral_weakGrad_sq_lt
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ε > 0, ∀ (φ : ContDiffBump (0 : V)), φ.rOut ≤ 2 * φ.rIn →
      ∀ (f : V → F) (x : V)
        (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun y => f y i) (Metric.ball x φ.rOut)),
      (∀ᵐ y ∂volume.restrict (Metric.ball x φ.rOut), f y ∈ K) →
      (∑ i, ∫ y in Metric.ball x φ.rOut, ‖(hf i).weakGrad y‖ ^ 2) < ε →
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x ∈ U := by
  obtain ⟨δ, hδ, hbound⟩ :=
    hK.exists_normed_convolution_mem_of_integral_norm_sub_sq_lt (E := V) volume hU hKU
  let b : ℝ := volume.real (Metric.ball (0 : V) 1)
  have hb : 0 < b := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume (0 : V) (by norm_num)).ne' measure_ball_lt_top.ne
  let C : ℝ := 4 * (DeGiorgi.CPoincVal 2) ^ 2 / b
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨δ ^ 2 / (C + 1), by positivity, ?_⟩
  intro φ hφ f x hf hKf hsmall
  let s := Metric.ball x φ.rOut
  let t := Metric.closedBall x φ.rOut
  have hae : t =ᵐ[volume] s := by
    have hball := (ae_restrict_iff' measurableSet_closedBall).mp
      (ae_mem_ball_of_measure_sphere_eq_zero (Measure.addHaar_sphere volume x φ.rOut))
    filter_upwards [hball] with y hy
    exact propext ⟨hy, fun h => Metric.ball_subset_closedBall h⟩
  have hμ : volume.restrict t = volume.restrict s := Measure.restrict_congr_set hae
  let : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hfm : MemLp f 2 (volume.restrict s) := MemLp.of_eval_piLp fun i => (hf i).memLp
  let a : F := ⨍ y in s, f y
  have hmi : MemLp (fun y => f y - a) 2 (volume.restrict s) := hfm.sub (memLp_const _)
  have hi : IntegrableOn (fun y => ‖f y - a‖ ^ 2) s :=
    (memLp_two_iff_integrable_sq_norm hmi.aestronglyMeasurable).mp hmi
  have hvar := integral_norm_sub_average_sq_le_radius_sq_mul_weakGrad φ.rOut_pos hf
  have hvol : volume.real t = φ.rOut ^ 2 * b := by
    exact (Measure.addHaar_real_closedBall volume x φ.rOut_pos.le).trans
      (by rw [finrank_euclideanSpace_fin])
  apply hbound φ 2 hφ f x a
  · simpa only [← hμ, t] using hfm.aestronglyMeasurable
  · change ∀ᵐ y ∂volume.restrict t, f y ∈ K
    rw [hμ]
    exact hKf
  · simpa only [IntegrableOn, ← hμ, t] using hi
  · have hfactor : (2 : ℝ) ^ Module.finrank ℝ V / volume.real t *
        ((DeGiorgi.CPoincVal 2) ^ 2 * φ.rOut ^ 2) = C := by
      rw [finrank_euclideanSpace_fin, hvol]
      dsimp [C]
      field_simp [φ.rOut_pos.ne', hb.ne']
      ring
    have hm : 0 ≤ (2 : ℝ) ^ Module.finrank ℝ V / volume.real t := by positivity
    have hv := mul_le_mul_of_nonneg_left hvar hm
    rw [← mul_assoc, hfactor] at hv
    have hz : 0 ≤ ∑ i, ∫ y in s, ‖(hf i).weakGrad y‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
    have hcs : C * (∑ i, ∫ y in s, ‖(hf i).weakGrad y‖ ^ 2) < δ ^ 2 := by
      have h1 : (C + 1) * (∑ i, ∫ y in s, ‖(hf i).weakGrad y‖ ^ 2) < δ ^ 2 :=
        by have h := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hsmall
           nlinarith
      nlinarith
    simpa only [MeasureTheory.setIntegral_congr_set hae, a, s, t] using hv.trans_lt hcs

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set MeasureTheory ContinuousLinearMap
open scoped Convolution

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {ι : Type*} [Fintype ι]

local notation "F" => EuclideanSpace ℝ ι

theorem exists_pos_normed_convolution_mem_on_compact
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {Ω S : Set V} (hΩ : IsOpen Ω) (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (f : V → F) (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun y => f y i) Ω)
    (hfK : ∀ᵐ y ∂volume.restrict Ω, f y ∈ K) :
    ∃ r > 0, ∀ (φ : ContDiffBump (0 : V)), φ.rOut ≤ r → φ.rOut ≤ 2 * φ.rIn →
      ∀ x ∈ S, (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x ∈ U := by
  classical
  obtain ⟨ε, hε, hbound⟩ := exists_normed_convolution_mem_of_integral_weakGrad_sq_lt hK hU hKU
  let H : V → ℝ := fun y => ∑ i, ‖(hf i).weakGrad y‖ ^ 2
  have hH : IntegrableOn H Ω :=
    integrable_finsetSum _ fun i _ =>
      (memLp_two_iff_integrable_sq_norm (hf i).weakGrad_memLp.aestronglyMeasurable).mp
        (hf i).weakGrad_memLp
  have hH0 (y : V) : 0 ≤ H y := Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨R, hR, hsmall⟩ := hH.exists_pos_integral_norm_closedBall_lt hε
  obtain ⟨η, hη, hηΩ⟩ := hS.exists_cthickening_subset_open hΩ hSΩ
  refine ⟨min R η, lt_min hR hη, ?_⟩
  intro φ hφ hratio x hx
  have hφR : φ.rOut ≤ R := hφ.trans (min_le_left _ _)
  have hφη : φ.rOut ≤ η := hφ.trans (min_le_right _ _)
  have hballΩ : Metric.ball x φ.rOut ⊆ Ω := by
    intro y hy
    apply hηΩ
    exact Metric.mem_cthickening_of_dist_le y x η S hx
      ((Metric.mem_ball.mp hy).le.trans hφη)
  let hw (i : ι) := (hf i).restrict Metric.isOpen_ball hballΩ
  have hfk : ∀ᵐ y ∂volume.restrict (Metric.ball x φ.rOut), f y ∈ K :=
    ae_mono (Measure.restrict_mono_set volume hballΩ) hfK
  apply hbound φ hratio f x hw hfk
  have hsub : Metric.ball x φ.rOut ⊆ Metric.closedBall x R ∩ Ω := by
    intro y hy
    exact ⟨(Metric.closedBall_subset_closedBall hφR) (Metric.ball_subset_closedBall hy), hballΩ hy⟩
  have hb : (∫ y in Metric.ball x φ.rOut, H y) ≤
      ∫ y in Metric.closedBall x R ∩ Ω, H y :=
    setIntegral_mono_set (hH.mono_set inter_subset_right)
      (Filter.Eventually.of_forall hH0) (Filter.Eventually.of_forall fun _ hy => hsub hy)
  have heq : (∑ i, ∫ y in Metric.ball x φ.rOut, ‖(hw i).weakGrad y‖ ^ 2) =
      ∫ y in Metric.ball x φ.rOut, H y := by
    rw [integral_finsetSum _ (fun i _ => ?_)]
    · rfl
    · have hi : IntegrableOn (fun y => ‖(hf i).weakGrad y‖ ^ 2) Ω :=
        (memLp_two_iff_integrable_sq_norm (hf i).weakGrad_memLp.aestronglyMeasurable).mp
          (hf i).weakGrad_memLp
      exact hi.mono_set hballΩ
  rw [heq]
  apply hb.trans_lt
  simpa only [Real.norm_of_nonneg (hH0 _)] using hsmall x

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped ContDiff Topology ENNReal Convolution

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem tendsto_eLpNorm_partial_retracted_convolution_sub_weakGrad_on_ball
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : F → F) (hr : ContDiffOn ℝ ∞ r U) (hfix : ∀ y ∈ K, r y = y)
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    {c : E} {a : ℝ} (hball : Metric.closedBall c a ⊆ Ω)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (j : Fin 2) :
    Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (r ∘ ((mollifierBumpEps (d := 2) (hε n)).normed volume
        ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f))) x (EuclideanSpace.single j 1) -
        WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
      2 (volume.restrict (Metric.ball c a))) atTop (𝓝 0) := by
  obtain ⟨R, hR, hRc, hReq, C, _, hC⟩ :=
    Analysis.exists_contDiff_extension_fderiv_bound hK hU hKU r hr
  let S := Metric.closedBall c a
  let B := Metric.ball c a
  have hBΩ : B ⊆ Ω := Metric.ball_subset_closedBall.trans hball
  let φ (n : ℕ) := mollifierBumpEps (d := 2) (hε n)
  let v (n : ℕ) := (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f)
  let G : E → F := fun x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)
  have hfm : MemLp f 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).memLp
  have hglobal : LocallyIntegrable (Ω.indicator f) volume :=
    ((memLp_indicator_iff_restrict hΩ.measurableSet).mpr hfm).locallyIntegrable (by norm_num)
  have hv (n : ℕ) : ContDiff ℝ ∞ (v n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left
      (lsmul ℝ ℝ) (φ n).contDiff_normed hglobal
  have hratio (n : ℕ) : (φ n).rOut ≤ 2 * (φ n).rIn := by dsimp [φ, mollifierBumpEps]; linarith
  have hae : ∀ᵐ x ∂volume.restrict B, Tendsto (fun n => v n x) atTop (𝓝 (f x)) := by
    have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := volume) hε0 (Filter.Eventually.of_forall hratio) hglobal
    filter_upwards [ae_restrict_of_ae (s := B) h, ae_restrict_mem Metric.isOpen_ball.measurableSet]
      with x hx hxB
    simpa only [Set.indicator_of_mem (hBΩ hxB) f] using hx
  have hA (n : ℕ) : AEStronglyMeasurable (fun x => fderiv ℝ R (v n x))
      (volume.restrict B) :=
    ((hR.continuous_fderiv (by simp)).comp (hv n).continuous).aestronglyMeasurable
  have hAr : ∀ᵐ x ∂volume.restrict B, Tendsto (fun n => fderiv ℝ R (v n x)) atTop
      (𝓝 (fderiv ℝ R (f x))) :=
    hae.mono fun x hx => ((hR.continuous_fderiv (by simp)).tendsto (f x)).comp hx
  have hdu (n : ℕ) : MemLp (fun x => fderiv ℝ (v n) x (EuclideanSpace.single j 1))
      2 (volume.restrict B) :=
    (memLp_fderiv_normed_convolution_apply_on_compact (isCompact_closedBall c a)
      (φ n) hglobal (EuclideanSpace.single j 1) 2).mono_measure
        (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  have hG : MemLp G 2 (volume.restrict B) :=
    MemLp.of_eval_piLp fun i => ((hf i).weakGrad_component_memLp j).mono_measure
      (Measure.restrict_mono_set volume hBΩ)
  have hder : Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (v n) x (EuclideanSpace.single j 1) - G x) 2 (volume.restrict B)) atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_partial_normed_convolution_indicator_sub_weakGrad
      hΩ (isCompact_closedBall c a) hball hf hε hε0 j
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
      (fun _ => eLpNorm_mono_measure _ (Measure.restrict_mono_set volume Metric.ball_subset_closedBall))
  have hRfix (y : F) (hy : y ∈ K) : R y = y :=
    ((hReq.filter_mono (nhds_le_nhdsSet hy)).eq_of_nhds).trans (hfix y hy)
  have htangent := weakGrad_fixed_by_fderiv_retraction_on_ball hK isOpen_univ (subset_univ K)
    R hR.contDiffOn hRfix hΩ hf hfK hball j
  have ht := MeasureTheory.tendsto_eLpNorm_fderiv_comp_apply_of_ae_tendsto v f R
    (EuclideanSpace.single j 1) G
    (fun n => Filter.Eventually.of_forall fun x => (hv n).differentiable (by simp) x)
    (fun n => Filter.Eventually.of_forall fun x => hR.differentiable (by simp) (v n x))
    hA (fun n => Filter.Eventually.of_forall fun x => hC (v n x)) hAr hdu hG hder
  obtain ⟨O, hO, hKO, hOr⟩ := mem_nhdsSet_iff_exists.mp hReq
  have hind : (Ω.indicator f) =ᵐ[volume.restrict Ω] f := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact Set.indicator_of_mem hx f
  let hfind (i : ι) := DeGiorgi.MemW1pWitness.ofAeEq
    (hind.symm.mono fun x hx => congrArg (fun z : F => z i) hx) (hf i)
  have hkind : ∀ᵐ x ∂volume.restrict Ω, (Ω.indicator f) x ∈ K := by
    filter_upwards [hind, hfK] with x hx hKx
    rwa [hx]
  obtain ⟨ρ, hρ, hmap⟩ := exists_pos_normed_convolution_mem_on_compact hK hO hKO
    hΩ (isCompact_closedBall c a) hball (Ω.indicator f) hfind hkind
  have heq : ∀ᶠ n in atTop, ∀ x ∈ B,
      fderiv ℝ (r ∘ v n) x = fderiv ℝ (R ∘ v n) x := by
    filter_upwards [hε0.eventually (gt_mem_nhds hρ)] with n hn x hx
    have he : (r ∘ v n) =ᶠ[𝓝 x] (R ∘ v n) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      exact (hOr (hmap (φ n) hn.le (hratio n) y (Metric.ball_subset_closedBall hy))).symm
    exact he.fderiv_eq
  apply ht.congr'
  filter_upwards [heq] with n hn
  apply eLpNorm_congr_ae
  filter_upwards [htangent, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
  rw [hn x hxB, hx]

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped ContDiff Topology ENNReal Convolution

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem tendsto_eLpNorm_retracted_convolution_sub_on_compact
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : F → F) (hr : ContDiffOn ℝ ∞ r U) (hfix : ∀ y ∈ K, r y = y)
    {Ω S : Set E} (hΩ : IsOpen Ω) (hS : IsCompact S) (hSΩ : S ⊆ Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x =>
      r (((mollifierBumpEps (d := 2) (hε n)).normed volume
        ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f)) x) - f x)
      2 (volume.restrict S)) atTop (𝓝 0) := by
  obtain ⟨R, hR, hRc, hReq, _, _, _⟩ :=
    Analysis.exists_contDiff_extension_fderiv_bound hK hU hKU r hr
  let φ (n : ℕ) := mollifierBumpEps (d := 2) (hε n)
  let v (n : ℕ) := (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f)
  have hfm : MemLp f 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).memLp
  have hval := tendsto_eLpNorm_normed_convolution_indicator_sub
    hΩ.measurableSet hSΩ hfm hε hε0
  have hfixed : (fun x => R (f x)) =ᵐ[volume.restrict S] f := by
    have hfk : ∀ᵐ x ∂volume.restrict S, f x ∈ K :=
      ae_mono (Measure.restrict_mono_set volume hSΩ) hfK
    filter_upwards [hfk] with x hx
    exact ((hReq.filter_mono (nhds_le_nhdsSet hx)).eq_of_nhds).trans (hfix _ hx)
  obtain ⟨L, hL⟩ := hR.lipschitzWith_of_hasCompactSupport hRc (by simp)
  have hRval := hL.tendsto_eLpNorm_comp_sub_of_fixed_ae v f hfixed hval
  obtain ⟨O, hO, hKO, hOr⟩ := mem_nhdsSet_iff_exists.mp hReq
  have hind : (Ω.indicator f) =ᵐ[volume.restrict Ω] f := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact Set.indicator_of_mem hx f
  let hfind (i : ι) := DeGiorgi.MemW1pWitness.ofAeEq
    (hind.symm.mono fun x hx => congrArg (fun z : F => z i) hx) (hf i)
  have hkind : ∀ᵐ x ∂volume.restrict Ω, (Ω.indicator f) x ∈ K := by
    filter_upwards [hind, hfK] with x hx hKx
    rwa [hx]
  obtain ⟨ρ, hρ, hmap⟩ := exists_pos_normed_convolution_mem_on_compact hK hO hKO
    hΩ hS hSΩ (Ω.indicator f) hfind hkind
  apply hRval.congr'
  filter_upwards [hε0.eventually (gt_mem_nhds hρ)] with n hn
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  have hratio : (φ n).rOut ≤ 2 * (φ n).rIn := by dsimp [φ, mollifierBumpEps]; linarith
  rw [hOr (hmap (φ n) hn.le hratio x hx)]

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {ι : Type*} [Fintype ι]

local notation "F" => EuclideanSpace ℝ ι

theorem exists_pos_contDiffOn_retracted_convolution
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {Ω S : Set V} (hΩ : IsOpen Ω) (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (f : V → F) (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun y => f y i) Ω)
    (hfK : ∀ᵐ y ∂volume.restrict Ω, f y ∈ K)
    (fglobal : LocallyIntegrable f volume) (r : F → F) (hr : ContDiffOn ℝ ∞ r U) :
    ∃ ρ > 0, ∀ (φ : ContDiffBump (0 : V)), φ.rOut ≤ ρ → φ.rOut ≤ 2 * φ.rIn →
      (∀ x ∈ S, (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x ∈ U) ∧
      ContDiffOn ℝ ∞ (r ∘ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f)) S := by
  obtain ⟨ρ, hρ, hmap⟩ := exists_pos_normed_convolution_mem_on_compact hK hU hKU hΩ hS hSΩ
    f hf hfK
  refine ⟨ρ, hρ, ?_⟩
  intro φ hφ hratio
  have hc : ContDiff ℝ ∞ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed fglobal
  exact ⟨hmap φ hφ hratio, hr.comp hc.contDiffOn (hmap φ hφ hratio)⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {ι : Type*} [Fintype ι]

local notation "F" => EuclideanSpace ℝ ι

theorem exists_pos_contDiffOn_retracted_indicator_convolution
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {Ω S : Set V} (hΩ : IsOpen Ω)
    (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (f : V → F) (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun y => f y i) Ω)
    (hfK : ∀ᵐ y ∂volume.restrict Ω, f y ∈ K)
    (r : F → F) (hr : ContDiffOn ℝ ∞ r U) (hrK : MapsTo r U K) :
    ∃ ρ > 0, ∀ (φ : ContDiffBump (0 : V)), φ.rOut ≤ ρ → φ.rOut ≤ 2 * φ.rIn →
      (∀ x ∈ S, (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f)) x ∈ U) ∧
      ContDiffOn ℝ ∞ (r ∘ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f))) S ∧
      MapsTo (r ∘ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f))) S K := by
  classical
  have hm : MemLp f 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).memLp
  have hglobal : LocallyIntegrable (Ω.indicator f) volume :=
    ((memLp_indicator_iff_restrict hΩ.measurableSet).mpr hm).locallyIntegrable (by norm_num)
  have hind : (Ω.indicator f) =ᵐ[volume.restrict Ω] f := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact Set.indicator_of_mem hx f
  let hw (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => (Ω.indicator f x) i) Ω :=
    DeGiorgi.MemW1pWitness.ofAeEq (hind.symm.mono fun x hx => congrArg (fun v : F => v i) hx)
      (hf i)
  have hk : ∀ᵐ y ∂volume.restrict Ω, (Ω.indicator f) y ∈ K := by
    filter_upwards [hind, hfK] with y hy hyK
    rwa [hy]
  obtain ⟨ρ, hρ, hbound⟩ := exists_pos_contDiffOn_retracted_convolution hK hU hKU hΩ hS hSΩ
    (Ω.indicator f) hw hk hglobal r hr
  refine ⟨ρ, hρ, ?_⟩
  intro φ hφ hratio
  obtain ⟨hmap, hsm⟩ := hbound φ hφ hratio
  exact ⟨hmap, hsm, fun x hx => hrK (hmap x hx)⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
