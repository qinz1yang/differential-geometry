import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Localization
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped ENNReal Convolution Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem tendsto_eLpNorm_mollifyEps_sub_of_memLp
    {f : E → ℝ} (hf : MemLp f 2 volume)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x =>
      (mollifyEps (d := d) (hε n) f) x - f x) 2 volume) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨r, hr, hbound⟩ := exists_eLpNorm_convolution_mollifierEps_sub_le
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf hδ
  filter_upwards [hε0.eventually (gt_mem_nhds hr)] with n hn
  have h := hbound (ε n) (hε n) hn.le
  simpa only [mollifyEps_eq_convolution_swap] using h

theorem tendsto_eLpNorm_partial_mollifyEps_sub_weakGrad
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u univ)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (j : Fin d) :
    Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (mollifyEps (d := d) (hε n) u) x (EuclideanSpace.single j 1) -
        hu.weakGrad x j) 2 volume) atTop (𝓝 0) := by
  have hg : MemLp (fun x => hu.weakGrad x j) 2 volume := by
    simpa only [Measure.restrict_univ] using hu.weakGrad_component_memLp j
  have hul : LocallyIntegrable u volume := by
    have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp
    exact huL.locallyIntegrable (by norm_num)
  have heq (n : ℕ) (x : E) :
      fderiv ℝ (mollifyEps (d := d) (hε n) u) x (EuclideanSpace.single j 1) =
        mollifyEps (d := d) (hε n) (fun y => hu.weakGrad y j) x :=
    mollifyEps_partial_eq_mollifyEps_weakPartial (hε n) hul (hu.isWeakGrad j) x
  simp_rw [heq]
  exact tendsto_eLpNorm_mollifyEps_sub_of_memLp hg hε hε0

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem normed_convolution_eq_of_eqOn_closedBall
    (φ : ContDiffBump (0 : E)) {f g : E → F} {x : E}
    (hfg : EqOn f g (Metric.closedBall x φ.rOut)) :
    (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x =
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) x := by
  rw [convolution_def, convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : φ.normed volume y = 0
  · simp only [hy, lsmul_apply, zero_smul]
  · have hyball : y ∈ Metric.ball (0 : E) φ.rOut := by
      change y ∈ Function.support (φ.normed volume) at hy
      rwa [φ.support_normed_eq] at hy
    have hxy : x - y ∈ Metric.closedBall x φ.rOut := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] using
        (by simpa only [Metric.mem_ball, dist_zero_right] using hyball : ‖y‖ < φ.rOut).le
    simp only [lsmul_apply, hfg hxy]

theorem normed_convolution_eventuallyEq_of_eqOn_cthickening
    {S : Set E} {δ : ℝ} (hδ : 0 < δ) (φ : ContDiffBump (0 : E))
    (hφ : φ.rOut ≤ δ / 2) {f g : E → F}
    (hfg : EqOn f g (Metric.cthickening δ S)) {x : E} (hx : x ∈ S) :
    (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) =ᶠ[𝓝 x]
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) := by
  filter_upwards [Metric.ball_mem_nhds x (half_pos hδ)] with z hz
  apply normed_convolution_eq_of_eqOn_closedBall φ
  intro y hy
  apply hfg
  apply Metric.mem_cthickening_of_dist_le y x δ S hx
  have hdist := dist_triangle y z x
  have hyz := Metric.mem_closedBall.mp hy
  have hzx := Metric.mem_ball.mp hz
  linarith

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem tendsto_eLpNorm_partial_mollifyEps_indicator_sub_weakGrad
    {Ω S : Set E} (hΩ : IsOpen Ω) (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (j : Fin d) :
    Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (mollifyEps (d := d) (hε n) (Ω.indicator u)) x
        (EuclideanSpace.single j 1) - hu.weakGrad x j) 2 (volume.restrict S)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hδΩ⟩ := hS.exists_cthickening_subset_open hΩ hSΩ
  obtain ⟨U, hU, _, _, hUf, hUg⟩ := hu.exists_compactly_supported_extension
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ (hS.cthickening (r := δ)) hδΩ
  have hlim := tendsto_eLpNorm_partial_mollifyEps_sub_weakGrad hU hε hε0 j
  have hrestrict : Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (mollifyEps (d := d) (hε n) U) x (EuclideanSpace.single j 1) - hU.weakGrad x j)
      2 (volume.restrict S)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    intro n
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have heq : ∀ᶠ n in atTop, ∀ x ∈ S,
      fderiv ℝ (mollifyEps (d := d) (hε n) (Ω.indicator u)) x =
        fderiv ℝ (mollifyEps (d := d) (hε n) U) x := by
    filter_upwards [hε0.eventually (gt_mem_nhds (half_pos hδ))] with n hn x hx
    have hfg : EqOn (Ω.indicator u) U (Metric.cthickening δ S) := by
      intro y hy
      rw [Set.indicator_of_mem (hδΩ hy) u]
      exact (hUf hy).symm
    exact (normed_convolution_eventuallyEq_of_eqOn_cthickening hδ
      (mollifierBumpEps (d := d) (hε n)) hn.le hfg hx).fderiv_eq
  apply hrestrict.congr'
  filter_upwards [heq] with n hn
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  rw [hn x hx]
  have hg := hUg (Metric.self_subset_cthickening S hx)
  exact congrArg (fun z : E =>
    fderiv ℝ (mollifyEps (d := d) (hε n) U) x (EuclideanSpace.single j 1) - z j) hg

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology ENNReal Convolution ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem normed_convolution_coordinate
    (φ : ContDiffBump (0 : E)) {f : E → F} (hf : LocallyIntegrable f volume) (i : ι) :
    (fun x => (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x i) =
      φ.normed volume ⋆[lsmul ℝ ℝ, volume] (fun x => f x i) := by
  funext x
  have hi : Integrable (fun t => φ.normed volume t • f (x - t)) volume :=
    φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ) φ.continuous_normed hf x
  simpa only [convolution_def, lsmul_apply, map_smul, EuclideanSpace.coe_proj,
    smul_eq_mul] using ((EuclideanSpace.proj i).integral_comp_comm hi).symm

theorem normed_convolution_indicator_coordinate_eq_mollifyEps
    {Ω : Set E} {f : E → F} (hf : LocallyIntegrable (Ω.indicator f) volume)
    {ε : ℝ} (hε : 0 < ε) (i : ι) :
    (fun x => ((mollifierBumpEps (d := d) hε).normed volume
      ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f)) x i) =
      mollifyEps (d := d) hε (Ω.indicator (fun x => f x i)) := by
  rw [normed_convolution_coordinate _ hf]
  have heq : (fun x => (Ω.indicator f x) i) = Ω.indicator (fun x => f x i) := by
    funext x
    by_cases hx : x ∈ Ω <;> simp [hx]
  rw [heq]
  rfl

private theorem norm_le_sum_coordinates (v : F) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  classical
  have hsum : (∑ i, EuclideanSpace.single i (v i)) = v := by ext; simp
  calc
    ‖v‖ = ‖∑ i, EuclideanSpace.single i (v i)‖ := by rw [hsum]
    _ ≤ ∑ i, ‖EuclideanSpace.single i (v i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ := by simp only [PiLp.norm_single]

theorem tendsto_eLpNorm_partial_normed_convolution_indicator_sub_weakGrad
    {Ω S : Set E} (hΩ : IsOpen Ω) (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    {f : E → F} (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) (j : Fin d) :
    Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ ((mollifierBumpEps (d := d) (hε n)).normed volume
        ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f)) x (EuclideanSpace.single j 1) -
      WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) 2 (volume.restrict S)) atTop (𝓝 0) := by
  classical
  let U (n : ℕ) := (mollifierBumpEps (d := d) (hε n)).normed volume
    ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f)
  let G : E → F := fun x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)
  have hfm : MemLp f 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).memLp
  have hglobal : LocallyIntegrable (Ω.indicator f) volume :=
    ((memLp_indicator_iff_restrict hΩ.measurableSet).mpr hfm).locallyIntegrable (by norm_num)
  have hU (n : ℕ) : ContDiff ℝ ∞ (U n) :=
    (mollifierBumpEps (d := d) (hε n)).hasCompactSupport_normed.contDiff_convolution_left
      (lsmul ℝ ℝ) (mollifierBumpEps (d := d) (hε n)).contDiff_normed hglobal
  have heq (n : ℕ) (x : E) (i : ι) :
      (fderiv ℝ (U n) x (EuclideanSpace.single j 1)) i =
        fderiv ℝ (mollifyEps (d := d) (hε n) (Ω.indicator (fun y => f y i))) x
          (EuclideanSpace.single j 1) := by
    have hc : (fun y => U n y i) =
        mollifyEps (d := d) (hε n) (Ω.indicator (fun y => f y i)) :=
      normed_convolution_indicator_coordinate_eq_mollifyEps hglobal (hε n) i
    have hd := ((EuclideanSpace.proj i).hasFDerivAt.comp x
      ((hU n).differentiable (by simp) x).hasFDerivAt).fderiv
    have hd' : fderiv ℝ (fun y => U n y i) x =
        (EuclideanSpace.proj i).comp (fderiv ℝ (U n) x) := hd
    rw [hc] at hd'
    rw [hd']
    rfl
  have hcoord (i : ι) : Tendsto (fun n => eLpNorm (fun x =>
      (fderiv ℝ (U n) x (EuclideanSpace.single j 1)) i - G x i)
        2 (volume.restrict S)) atTop (𝓝 0) := by
    simpa only [heq, G, PiLp.toLp_apply] using
      tendsto_eLpNorm_partial_mollifyEps_indicator_sub_weakGrad hΩ hS hSΩ (hf i) hε hε0 j
  have hm (n : ℕ) (i : ι) : AEStronglyMeasurable
      (fun x => (fderiv ℝ (U n) x (EuclideanSpace.single j 1)) i - G x i)
        (volume.restrict S) := by
    have hmU : Continuous (fun x => (fderiv ℝ (U n) x (EuclideanSpace.single j 1)) i) :=
      (EuclideanSpace.proj i).continuous.comp
        (((hU n).continuous_fderiv (by simp)).clm_apply continuous_const)
    exact hmU.aestronglyMeasurable.sub
      (((hf i).weakGrad_component_memLp j).aestronglyMeasurable.mono_measure
        (Measure.restrict_mono_set volume hSΩ))
  have hsum : Tendsto (fun n => ∑ i, eLpNorm (fun x =>
      (fderiv ℝ (U n) x (EuclideanSpace.single j 1)) i - G x i) 2 (volume.restrict S))
        atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hcoord i)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
  intro n
  calc
    eLpNorm (fun x => fderiv ℝ (U n) x (EuclideanSpace.single j 1) - G x) 2
        (volume.restrict S) ≤ eLpNorm (∑ i, fun x =>
          ‖(fderiv ℝ (U n) x (EuclideanSpace.single j 1)) i - G x i‖) 2
            (volume.restrict S) := by
      refine eLpNorm_mono_real ?_ ?_
      · exact (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp_aestronglyMeasurable
          (aemeasurable_pi_iff.mpr fun i => (hm n i).aemeasurable).aestronglyMeasurable
      intro x
      simpa only [Finset.sum_apply, PiLp.sub_apply] using
        norm_le_sum_coordinates (fderiv ℝ (U n) x (EuclideanSpace.single j 1) - G x)
    _ ≤ ∑ i, eLpNorm (fun x => ‖(fderiv ℝ (U n) x (EuclideanSpace.single j 1)) i - G x i‖)
        2 (volume.restrict S) := eLpNorm_sum_le (by norm_num)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact eLpNorm_norm _ (hm n i)

theorem tendsto_eLpNorm_normed_convolution_indicator_sub
    {Ω S : Set E} (hΩ : MeasurableSet Ω) (hSΩ : S ⊆ Ω)
    {f : E → F} (hf : MemLp f 2 (volume.restrict Ω))
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x =>
      ((mollifierBumpEps (d := d) (hε n)).normed volume
        ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f)) x - f x)
      2 (volume.restrict S)) atTop (𝓝 0) := by
  classical
  let U (n : ℕ) := (mollifierBumpEps (d := d) (hε n)).normed volume
    ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f)
  have hglobal : LocallyIntegrable (Ω.indicator f) volume :=
    ((memLp_indicator_iff_restrict hΩ).mpr hf).locallyIntegrable (by norm_num)
  have hΩae : ∀ᵐ x ∂volume.restrict S, x ∈ Ω :=
    ae_mono (Measure.restrict_mono_set volume hSΩ) (ae_restrict_mem hΩ)
  have hcoord (i : ι) : Tendsto (fun n => eLpNorm (fun x => U n x i - f x i)
      2 (volume.restrict S)) atTop (𝓝 0) := by
    have hi : MemLp (Ω.indicator (fun x => f x i)) 2 volume :=
      (memLp_indicator_iff_restrict hΩ).mpr (hf.eval_piLp i)
    have ht := tendsto_eLpNorm_mollifyEps_sub_of_memLp hi hε hε0
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
    intro n
    have heq : (fun x => U n x i - f x i) =ᵐ[volume.restrict S]
        (fun x => mollifyEps (d := d) (hε n) (Ω.indicator (fun y => f y i)) x -
          Ω.indicator (fun y => f y i) x) := by
      filter_upwards [hΩae] with x hx
      rw [Set.indicator_of_mem hx]
      exact congrArg (fun z => z - f x i)
        (congrFun (normed_convolution_indicator_coordinate_eq_mollifyEps hglobal (hε n) i) x)
    dsimp only
    rw [eLpNorm_congr_ae heq]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hm (n : ℕ) (i : ι) : AEStronglyMeasurable (fun x => U n x i - f x i)
      (volume.restrict S) := by
    have hU : ContDiff ℝ ∞ (U n) :=
      (mollifierBumpEps (d := d) (hε n)).hasCompactSupport_normed.contDiff_convolution_left
        (lsmul ℝ ℝ) (mollifierBumpEps (d := d) (hε n)).contDiff_normed hglobal
    exact ((EuclideanSpace.proj i).continuous.comp hU.continuous).aestronglyMeasurable.sub
      ((hf.eval_piLp i).aestronglyMeasurable.mono_measure
        (Measure.restrict_mono_set volume hSΩ))
  have hsum : Tendsto (fun n => ∑ i, eLpNorm (fun x => U n x i - f x i)
      2 (volume.restrict S)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hcoord i)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
  intro n
  calc
    eLpNorm (fun x => U n x - f x) 2 (volume.restrict S) ≤
        eLpNorm (∑ i, fun x => ‖U n x i - f x i‖) 2 (volume.restrict S) := by
      refine eLpNorm_mono_real ?_ ?_
      · exact (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp_aestronglyMeasurable
          (aemeasurable_pi_iff.mpr fun i => (hm n i).aemeasurable).aestronglyMeasurable
      intro x
      simpa only [Finset.sum_apply, PiLp.sub_apply] using norm_le_sum_coordinates (U n x - f x)
    _ ≤ ∑ i, eLpNorm (fun x => ‖U n x i - f x i‖) 2 (volume.restrict S) :=
      eLpNorm_sum_le (by norm_num)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact eLpNorm_norm _ (hm n i)

theorem memLp_fderiv_normed_convolution_apply_on_compact
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {S : Set E} (hS : IsCompact S) (φ : ContDiffBump (0 : E))
    {f : E → H} (hf : LocallyIntegrable f volume) (a : E) (p : ℝ≥0∞) :
    MemLp (fun x => fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x a)
      p (volume.restrict S) := by
  have hsm : ContDiff ℝ ∞ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed hf
  have hc : Continuous (fun x =>
      fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x a) :=
    (hsm.continuous_fderiv (by simp)).clm_apply continuous_const
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
  obtain ⟨C, hC⟩ := (hS.image hc).isBounded.exists_norm_le
  apply MemLp.of_bound hc.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  exact hC _ (mem_image_of_mem _ hx)

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
