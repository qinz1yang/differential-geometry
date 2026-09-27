import DifferentialGeometry.Analysis.Sobolev.Euclidean.Mollification
import DifferentialGeometry.Analysis.Integration.Lp.Composition
import DifferentialGeometry.Analysis.Integration.Lp.Compact
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative
import Mathlib.Analysis.Calculus.MeanValue
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Compact
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence
import Mathlib.Topology.Algebra.Support

noncomputable section

open Set MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Topology ENNReal Convolution NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ κ

theorem exists_memW1pWitnesses_comp_contDiff_on_ball
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (R : F → H) (hR : ContDiff ℝ 1 R)
    {C : ℝ} (hC : ∀ y, ‖fderiv ℝ R y‖ ≤ C)
    {c : E} {a : ℝ} (hball : Metric.closedBall c a ⊆ Ω) :
    ∃ hw : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => R (f x) k) (Metric.ball c a),
      ∀ k x j, (hw k).weakGrad x j =
        (fderiv ℝ R (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) k := by
  let B := Metric.ball c a
  have hBΩ : B ⊆ Ω := Metric.ball_subset_closedBall.trans hball
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (isCompact_closedBall c a).measure_lt_top).ne
  have hfm : MemLp f 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).memLp
  have hfmB : MemLp f 2 (volume.restrict B) :=
    hfm.mono_measure (Measure.restrict_mono_set volume hBΩ)
  have hglobal : LocallyIntegrable (Ω.indicator f) volume :=
    ((memLp_indicator_iff_restrict hΩ.measurableSet).mpr hfm).locallyIntegrable (by norm_num)
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let φ (n : ℕ) := mollifierBumpEps (d := d) (hε n)
  let u (n : ℕ) := (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f)
  have hu (n : ℕ) : ContDiff ℝ ∞ (u n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left
      (lsmul ℝ ℝ) (φ n).contDiff_normed hglobal
  have hval : Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2
      (volume.restrict B)) atTop (𝓝 0) :=
    tendsto_eLpNorm_normed_convolution_indicator_sub hΩ.measurableSet hBΩ hfm hε hε0
  have hae : ∀ᵐ x ∂volume.restrict B, Tendsto (fun n => u n x) atTop (𝓝 (f x)) := by
    have hφ0 : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := hε0
    have hratio : ∀ᶠ n in atTop, (φ n).rOut ≤ 2 * (φ n).rIn :=
      Filter.Eventually.of_forall fun n => by dsimp [φ, mollifierBumpEps]; linarith
    have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := volume) hφ0 hratio hglobal
    filter_upwards [ae_restrict_of_ae (s := B) h,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
    simpa only [Set.indicator_of_mem (hBΩ hxB) f] using hx
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ R 0)).trans (hC 0)
  let L : ℝ≥0 := ⟨C, hC0⟩
  have hLip : LipschitzWith L R := lipschitzWith_of_nnnorm_fderiv_le
    (hR.differentiable one_ne_zero) (fun y => hC y)
  have hRm : MemLp (fun x => R (f x)) 2 (volume.restrict B) := by
    have hsub : MemLp (fun x => R (f x) - R 0) 2 (volume.restrict B) := by
      apply hfmB.of_le_mul
        ((hR.continuous.comp_aestronglyMeasurable hfmB.aestronglyMeasurable).sub
          aestronglyMeasurable_const)
      exact Filter.Eventually.of_forall fun x => by
        change ‖R (f x) - R 0‖ ≤ (L : ℝ) * ‖f x‖
        simpa only [sub_zero] using hLip.norm_sub_le (f x) 0
    simpa only [Pi.add_def, sub_add_cancel] using hsub.add (memLp_const (R 0))
  have hRval : Tendsto (fun n => eLpNorm (fun x => R (u n x) - R (f x)) 2
      (volume.restrict B)) atTop (𝓝 0) := by
    have hbound (n : ℕ) : eLpNorm (fun x => R (u n x) - R (f x)) 2
        (volume.restrict B) ≤ (L : ℝ≥0∞) *
          eLpNorm (fun x => u n x - f x) 2 (volume.restrict B) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := (L : ℝ)) _ 2
      exact Filter.Eventually.of_forall fun x => hLip.norm_sub_le (u n x) (f x)
    have ht := ENNReal.Tendsto.const_mul (a := (L : ℝ≥0∞)) hval
      (Or.inr ENNReal.coe_ne_top)
    simp only [mul_zero] at ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => zero_le) hbound
  let G (j : Fin d) (x : E) : F := WithLp.toLp 2 (fun i => (hf i).weakGrad x j)
  have hG (j : Fin d) : MemLp (G j) 2 (volume.restrict B) :=
    MemLp.of_eval_piLp fun i => ((hf i).weakGrad_component_memLp j).mono_measure
      (Measure.restrict_mono_set volume hBΩ)
  have htarget (j : Fin d) : MemLp (fun x => fderiv ℝ R (f x) (G j x)) 2
      (volume.restrict B) := MemLp.clm_apply_of_ae_norm_le
    ((hR.continuous_fderiv one_ne_zero).comp_aestronglyMeasurable hfmB.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => hC (f x)) (hG j)
  have hRu (n : ℕ) (k : κ) : ContDiff ℝ 1 (fun x => R (u n x) k) :=
    (EuclideanSpace.proj k : H →L[ℝ] ℝ).contDiff.comp (hR.comp ((hu n).of_le (by simp)))
  have hum (n : ℕ) (k : κ) : MemLp (fun x => R (u n x) k) 2 (volume.restrict B) :=
    ((hRu n k).continuous.continuousOn.memLp_restrict_compact
      (isCompact_closedBall c a) 2).mono_measure
        (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  have hud (n : ℕ) (k : κ) (j : Fin d) : MemLp (fun x =>
      fderiv ℝ (fun y => R (u n y) k) x (EuclideanSpace.single j 1)) 2
      (volume.restrict B) :=
    (MeasureTheory.ContinuousOn.memLp_restrict_compact (isCompact_closedBall c a)
      (((hRu n k).continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
      2).mono_measure
        (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  have hdu (n : ℕ) (j : Fin d) : MemLp (fun x => fderiv ℝ (u n) x
      (EuclideanSpace.single j 1)) 2 (volume.restrict B) :=
    (memLp_fderiv_normed_convolution_apply_on_compact (isCompact_closedBall c a)
      (φ n) hglobal (EuclideanSpace.single j 1) 2).mono_measure
        (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  have hder (j : Fin d) : Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (u n) x (EuclideanSpace.single j 1) - G j x) 2
      (volume.restrict B)) atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_partial_normed_convolution_indicator_sub_weakGrad
      hΩ (isCompact_closedBall c a) hball hf hε hε0 j
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    intro n
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  have hvalc (k : κ) : Tendsto (fun n => eLpNorm (fun x => R (u n x) k - R (f x) k)
      2 (volume.restrict B)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRval (fun _ => zero_le)
    intro n
    exact eLpNorm_mono_ae (Filter.Eventually.of_forall fun x =>
      PiLp.norm_apply_le (R (u n x) - R (f x)) k)
  have hdlim (k : κ) (j : Fin d) : Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (fun y => R (u n y) k) x (EuclideanSpace.single j 1) -
        (fderiv ℝ R (f x) (G j x)) k) 2 (volume.restrict B)) atTop (𝓝 0) := by
    have ht := tendsto_eLpNorm_clm_apply_of_strong_ae_tendsto
      (fun n x => fderiv ℝ R (u n x)) (fun x => fderiv ℝ R (f x))
      (fun n => ((hR.continuous_fderiv one_ne_zero).comp (hu n).continuous).aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall fun x => hC (u n x))
      (hae.mono fun x hx => ((hR.continuous_fderiv one_ne_zero).tendsto (f x)).comp hx)
      (fun n x => fderiv ℝ (u n) x (EuclideanSpace.single j 1)) (G j)
      (fun n => hdu n j) (hG j) (hder j)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
    intro n
    apply eLpNorm_mono_ae
    filter_upwards [] with x
    have hd := ((EuclideanSpace.proj k : H →L[ℝ] ℝ).hasFDerivAt.comp x
      ((hR.differentiable one_ne_zero (u n x)).comp x
        ((hu n).differentiable (by simp) x)).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => R (u n y) k) x =
      (EuclideanSpace.proj k).comp (fderiv ℝ (R ∘ u n) x) at hd
    rw [hd, fderiv_comp x (hR.differentiable one_ne_zero (u n x))
      ((hu n).differentiable (by simp) x)]
    exact PiLp.norm_apply_le
      (fderiv ℝ R (u n x) (fderiv ℝ (u n) x (EuclideanSpace.single j 1)) -
        fderiv ℝ R (f x) (G j x)) k
  let hw (k : κ) : DeGiorgi.MemW1pWitness 2 (fun x => R (f x) k) B :=
    { memLp := hRm.eval_piLp k
      weakGrad := fun x => WithLp.toLp 2 (fun j => (fderiv ℝ R (f x) (G j x)) k)
      weakGrad_component_memLp := fun j => (htarget j).eval_piLp k
      isWeakGrad := fun j => hasWeakPartialDeriv_of_tendsto_eLpNorm (by norm_num) j
        (fun n => hum n k) (fun n => hud n k j) (hRm.eval_piLp k)
        ((htarget j).eval_piLp k)
        (fun n => hasWeakPartialDeriv_of_contDiffOn Metric.isOpen_ball
          (hRu n k).contDiffOn j) (hvalc k) (hdlim k j) }
  exact ⟨hw, fun k x j => rfl⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ κ

theorem exists_memW1pWitnesses_comp_contDiffOn_on_ball
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    {U : Set F} (hU : IsOpen U) (R : F → H) (hR : ContDiffOn ℝ ∞ R U)
    {x₀ : E} {ρ : ℝ} (hball : Metric.closedBall x₀ ρ ⊆ Ω)
    (hfc : ContinuousOn f (Metric.closedBall x₀ ρ))
    (hmaps : MapsTo f (Metric.closedBall x₀ ρ) U) :
    ∃ hcomp : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => R (f x) k) (Metric.ball x₀ ρ),
      ∀ x ∈ Metric.ball x₀ ρ, ∀ j,
        WithLp.toLp 2 (fun k => (hcomp k).weakGrad x j) =
          fderiv ℝ R (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) := by
  let K := f '' Metric.closedBall x₀ ρ
  have hK : IsCompact K := (isCompact_closedBall x₀ ρ).image_of_continuousOn hfc
  have hKU : K ⊆ U := by
    rintro y ⟨x, hx, rfl⟩
    exact hmaps hx
  obtain ⟨T, hT, hTc, hTeq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_compactSupport_extension_on_isCompact hK hU hKU hR
  obtain ⟨C, hC⟩ := (hT.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hTc.fderiv (𝕜 := ℝ))
  obtain ⟨ht, htgrad⟩ := exists_memW1pWitnesses_comp_contDiff_on_ball hΩ hf T
    (hT.of_le (by simp)) hC hball
  have hEq (x : E) (hx : x ∈ Metric.ball x₀ ρ) : T =ᶠ[𝓝 (f x)] R :=
    hTeq.filter_mono (nhds_le_nhdsSet (mem_image_of_mem f (Metric.ball_subset_closedBall hx)))
  let hcomp (k : κ) : DeGiorgi.MemW1pWitness 2 (fun x => R (f x) k) (Metric.ball x₀ ρ) :=
    (ht k).congr (by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      exact congrArg (fun y : H => y k) (hEq x hx).eq_of_nhds)
  refine ⟨hcomp, ?_⟩
  intro x hx j
  have hd := (hEq x hx).fderiv_eq (𝕜 := ℝ)
  apply PiLp.ext
  intro k
  change (ht k).weakGrad x j = _
  rw [htgrad k x j, hd]

theorem exists_memW1pWitnesses_comp_contDiffOn_of_continuousOn
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F} (hfc : ContinuousOn f Ω)
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    {U : Set F} (hU : IsOpen U) (R : F → H) (hR : ContDiffOn ℝ ∞ R U)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) (hfU : f x₀ ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x₀ ρ ⊆ Ω ∧
      MapsTo f (Metric.closedBall x₀ ρ) U ∧
      ∃ hcomp : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => R (f x) k) (Metric.ball x₀ ρ),
        ∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          WithLp.toLp 2 (fun k => (hcomp k).weakGrad x j) =
            fderiv ℝ R (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) := by
  have hopen : IsOpen (Ω ∩ f ⁻¹' U) := hfc.isOpen_inter_preimage hΩ hU
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ⟨hx₀, hfU⟩)
  let ρ := δ / 2
  have hρ : 0 < ρ := half_pos hδ
  have hρsub : Metric.closedBall x₀ ρ ⊆ Ω ∩ f ⁻¹' U :=
    (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hδsub
  have hball : Metric.closedBall x₀ ρ ⊆ Ω := fun x hx => (hρsub hx).1
  have hmaps : MapsTo f (Metric.closedBall x₀ ρ) U := fun x hx => (hρsub hx).2
  obtain ⟨hcomp, hgrad⟩ := exists_memW1pWitnesses_comp_contDiffOn_on_ball
    hΩ hf hU R hR hball (hfc.mono hball) hmaps
  exact ⟨ρ, hρ, hball, hmaps, hcomp, hgrad⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ κ

theorem exists_memW1pWitnesses_smul_comp_contDiff_on_ball
    {Ω : Set E} (hΩ : IsOpen Ω) {z : E → F} (hzc : ContinuousOn z Ω)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) Ω)
    (L : F → H) (hL : ContDiff ℝ 1 L) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ L y‖ ≤ C)
    {c : E} {ρ : ℝ} (hball : Metric.closedBall c ρ ⊆ Ω)
    {ζ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζball : tsupport ζ ⊆ Metric.ball c ρ) :
    Continuous (fun x => ζ x • L (z x)) ∧
    HasCompactSupport (fun x => ζ x • L (z x)) ∧
    tsupport (fun x => ζ x • L (z x)) ⊆ tsupport ζ ∧
    ∃ hφ : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => (ζ x • L (z x)) k) (Metric.ball c ρ),
      ∀ x j, WithLp.toLp 2 (fun k => (hφ k).weakGrad x j) =
        ζ x • fderiv ℝ L (z x) (WithLp.toLp 2 (fun i => (hz i).weakGrad x j)) +
          (fderiv ℝ ζ x (EuclideanSpace.single j 1)) • L (z x) := by
  have hζs : HasCompactSupport ζ :=
    (isCompact_closedBall c ρ).of_isClosed_subset (isClosed_tsupport ζ)
      (hζball.trans Metric.ball_subset_closedBall)
  have hφs : tsupport (fun x => ζ x • L (z x)) ⊆ tsupport ζ :=
    tsupport_smul_subset_left ζ (fun x => L (z x))
  have hφc : Continuous (fun x => ζ x • L (z x)) :=
    (hζ.continuous.continuousOn.smul
      (hL.continuous.comp_continuousOn hzc)).continuous_of_tsupport_subset
      hΩ (hφs.trans (hζball.trans (Metric.ball_subset_closedBall.trans hball)))
  have hφcomp : HasCompactSupport (fun x => ζ x • L (z x)) :=
    hζs.isCompact.of_isClosed_subset (isClosed_tsupport _) hφs
  obtain ⟨hLz, hgrad⟩ := exists_memW1pWitnesses_comp_contDiff_on_ball hΩ hz L hL hC hball
  obtain ⟨B₀, hB₀⟩ := hζs.exists_bound_of_continuous hζ.continuous
  obtain ⟨B₁, hB₁⟩ := (hζs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hζ.continuous_fderiv (by simp))
  let hφ (k : κ) : DeGiorgi.MemW1pWitness 2 (fun x => (ζ x • L (z x)) k) (Metric.ball c ρ) := by
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      (hLz k).mulSmoothBoundedP (by norm_num) Metric.isOpen_ball hζ
        (le_max_right B₀ 0) (le_max_right B₁ 0)
        (fun x => by simpa only [Real.norm_eq_abs] using (hB₀ x).trans (le_max_left B₀ 0))
        (fun x => (hB₁ x).trans (le_max_left B₁ 0))
  refine ⟨hφc, hφcomp, hφs, hφ, ?_⟩
  intro x j
  ext k
  change ζ x * (hLz k).weakGrad x j +
      (fderiv ℝ ζ x (EuclideanSpace.single j 1)) * L (z x) k =
    ζ x * (fderiv ℝ L (z x) (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) k +
      (fderiv ℝ ζ x (EuclideanSpace.single j 1)) * L (z x) k
  rw [hgrad k x j]

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
