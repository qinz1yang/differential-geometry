import DifferentialGeometry.Analysis.Integration.Lp.Cutoff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

omit [NormedSpace ℝ E] in
private theorem memLp_mul_cutoff
    {Ω : Set E} {μ : Measure E} {g η : E → ℝ} {p : ℝ≥0∞}
    (hg : MemLp g p (μ.restrict Ω)) (hη : Continuous η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω) :
    MemLp (fun x => η x * g x) p μ := by
  have hg' : MemLp g p (μ.restrict (tsupport η)) :=
    hg.mono_measure (Measure.restrict_mono_set μ hηs)
  simpa only [smul_eq_mul] using
    hg'.continuous_smul_of_tsupport_subset (isClosed_tsupport η).measurableSet
      hη hηc (Subset.refl _)

private theorem memLp_mul_cutoff_derivative
    {Ω : Set E} {μ : Measure E} {g η : E → ℝ} {p : ℝ≥0∞}
    (hg : MemLp g p (μ.restrict Ω)) (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω) (e : E) :
    MemLp (fun x => fderiv ℝ η x e * g x) p μ :=
  memLp_mul_cutoff hg ((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (hηc.fderiv_apply (𝕜 := ℝ) e) ((tsupport_fderiv_apply_subset ℝ e).trans hηs)

private theorem memLp_mul_cutoff_second_derivative
    {Ω : Set E} {μ : Measure E} {g η : E → ℝ} {p : ℝ≥0∞}
    (hg : MemLp g p (μ.restrict Ω)) (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω) (e₁ e₂ : E) :
    MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ η y e₁) x e₂ * g x) p μ :=
  memLp_mul_cutoff_derivative hg
    ((hη.fderiv_right (by norm_num)).clm_apply contDiff_const)
    (hηc.fderiv_apply (𝕜 := ℝ) e₁) ((tsupport_fderiv_apply_subset ℝ e₁).trans hηs) e₂

theorem memLp_parabolic_cutoff_derivatives
    {Ω : Set E} {μ : Measure E} {u dtU du d2u η : E → ℝ} {p : ℝ≥0∞}
    (hu : MemLp u p (μ.restrict Ω))
    (hdtU : MemLp dtU p (μ.restrict Ω))
    (hdu : MemLp du p (μ.restrict Ω))
    (hd2u : MemLp d2u p (μ.restrict Ω))
    (et ex : E) (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) :
    let v := fun x => η x * u x
    let vt := fun x => η x * dtU x + fderiv ℝ η x et * u x
    let vx := fun x => η x * du x + fderiv ℝ η x ex * u x
    let vxx := fun x => η x * d2u x + 2 * fderiv ℝ η x ex * du x +
      fderiv ℝ (fun y => fderiv ℝ η y ex) x ex * u x
    MemLp v p μ ∧ MemLp vt p μ ∧ MemLp vx p μ ∧ MemLp vxx p μ := by
  dsimp only
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  refine ⟨memLp_mul_cutoff hu hη.continuous hηc hηs,
    (memLp_mul_cutoff hdtU hη.continuous hηc hηs).add
      (memLp_mul_cutoff_derivative hu hη1 hηc hηs et),
    (memLp_mul_cutoff hdu hη.continuous hηc hηs).add
      (memLp_mul_cutoff_derivative hu hη1 hηc hηs ex), ?_⟩
  have hcross := (memLp_mul_cutoff_derivative hdu hη1 hηc hηs ex).const_mul 2
  have hsecond := memLp_mul_cutoff_second_derivative hu hη hηc hηs ex ex
  have hsum := ((memLp_mul_cutoff hd2u hη.continuous hηc hηs).add hcross).add hsecond
  convert hsum using 1
  ext x
  simp only [Pi.add_apply]
  ring

theorem memLp_nondivergence_cutoff
    {Ω : Set E} {μ : Measure E} {u dtU du d2u a f η : E → ℝ} {p : ℝ≥0∞}
    (hu : MemLp u p (μ.restrict Ω))
    (hdtU : MemLp dtU p (μ.restrict Ω))
    (hdu : MemLp du p (μ.restrict Ω))
    (hd2u : MemLp d2u p (μ.restrict Ω))
    (hf : MemLp f p (μ.restrict Ω))
    (ha : MemLp a ∞ (μ.restrict Ω))
    (et ex : E) (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) :
    let v := fun x => η x * u x
    let vt := fun x => η x * dtU x + fderiv ℝ η x et * u x
    let vx := fun x => η x * du x + fderiv ℝ η x ex * u x
    let vxx := fun x => η x * d2u x + 2 * fderiv ℝ η x ex * du x +
      fderiv ℝ (fun y => fderiv ℝ η y ex) x ex * u x
    let residual := fun x => η x * f x + fderiv ℝ η x et * u x -
      a x * (2 * fderiv ℝ η x ex * du x +
        fderiv ℝ (fun y => fderiv ℝ η y ex) x ex * u x)
    MemLp v p μ ∧ MemLp vt p μ ∧ MemLp vx p μ ∧
      MemLp vxx p μ ∧ MemLp residual p μ := by
  dsimp only
  obtain ⟨hv, hvt, hvx, hvxx⟩ :=
    memLp_parabolic_cutoff_derivatives hu hdtU hdu hd2u et ex hη hηc hηs
  refine ⟨hv, hvt, hvx, hvxx, ?_⟩
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have htime := memLp_mul_cutoff_derivative hu hη1 hηc hηs et
  have haCross := (memLp_mul_cutoff_derivative (hdu.mul' (r := p) ha) hη1 hηc hηs ex).const_mul 2
  have haSecond := memLp_mul_cutoff_second_derivative (hu.mul' (r := p) ha) hη hηc hηs ex ex
  have hres := ((memLp_mul_cutoff hf hη.continuous hηc hηs).add htime).sub (haCross.add haSecond)
  convert hres using 1
  ext x
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

end DifferentialGeometry.Analysis.Parabolic
