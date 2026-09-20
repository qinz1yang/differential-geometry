import DifferentialGeometry.Analysis.Integration.Integral.MeanSquareDeviation
import DifferentialGeometry.External.DeGiorgi.Oscillation.Campanato
import DifferentialGeometry.External.DeGiorgi.Poincare
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Campanato
import DifferentialGeometry.Topology.MetricSpace.HolderContinuity
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis

local notation "E" => EuclideanSpace ℝ (Fin 2)


theorem exists_campanato_bound_of_mean_square_decay
    {Ω : Set E} {u : E → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    {x₀ : E} {R α C : ℝ} (hball : Metric.ball x₀ R ⊆ Ω) (hC : 0 ≤ C)
    (henergy : ∀ b : DeGiorgi.CampanatoBall x₀ R,
      (∫ x in Metric.ball b.center b.radius,
        (u x - ⨍ y in Metric.ball b.center b.radius, u y) ^ 2) ≤
        C * b.radius ^ (2 + 2 * α)) :
    ∃ Ccamp : ℝ, 0 ≤ Ccamp ∧ DeGiorgi.HasCampanatoBound u x₀ R α Ccamp := by
  refine ⟨Real.sqrt (C / Real.pi), Real.sqrt_nonneg _, ?_⟩
  intro b
  let r : ℝ := b.radius
  let B : Set E := Metric.ball b.center r
  let μ : Measure E := volume.restrict B
  have hr : 0 < r := b.radius_pos
  have hBΩ : B ⊆ Ω := b.subset_ball.trans hball
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have huLp : MemLp u 2 μ := hu.mono_measure (Measure.restrict_mono_set volume hBΩ)
  have huInt : IntegrableOn u B := huLp.integrable (by norm_num)
  refine ⟨huInt, ?_⟩
  let m : ℝ := ⨍ y in B, u y
  let J : ℝ := ∫ x in B, |u x - m|
  let Q : ℝ := ∫ x in B, (u x - m) ^ 2
  let t : ℝ := r ^ α
  have ht : 0 < t := Real.rpow_pos_of_pos hr α
  have hosc : MemLp (fun x => u x - m) 2 μ := huLp.sub (memLp_const m)
  have hsq : IntegrableOn (fun x => (u x - m) ^ 2) B := hosc.integrable_sq
  have hIone : (∫ x in B, (1 : ℝ)) = volume.real B := by simp
  have hcs : J ^ 2 ≤ volume.real B * Q := by
    have hh := DeGiorgi.weighted_power_mean_setIntegral
      (μ := volume) (s := B) (show MeasurableSet B from Metric.isOpen_ball.measurableSet)
      (p := (2 : ℝ)) (by norm_num)
      (f := fun x => |u x - m|) (w := fun _ => (1 : ℝ))
      (fun x => abs_nonneg _) (fun _ => zero_le_one)
      (by simpa only [Real.norm_eq_abs] using hosc.norm.aemeasurable)
      (show IntegrableOn (fun _ : E => (1 : ℝ)) B from integrable_const 1)
      (by simpa only [Real.rpow_two, mul_one, sq_abs] using hsq)
    simp only [mul_one, Real.rpow_two, sq_abs,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, hIone] at hh
    exact hh
  have hvolume : volume.real B = Real.pi * r ^ 2 := by
    simp only [B, Measure.real, EuclideanSpace.volume_ball_fin_two,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal Real.pi_pos.le]
    ring
  have hrpow : r ^ (2 + 2 * α) = r ^ 2 * t ^ 2 := by
    dsimp only [t]
    rw [Real.rpow_add hr, Real.rpow_two, mul_comm (2 : ℝ) α,
      Real.rpow_mul hr.le, Real.rpow_two]
  have hQ : Q ≤ r ^ 2 * C * t ^ 2 := by
    have hh := henergy b
    change Q ≤ C * r ^ (2 + 2 * α) at hh
    rw [hrpow] at hh
    nlinarith
  have hJnonneg : 0 ≤ J := integral_nonneg fun x => abs_nonneg _
  have hJsq : J ^ 2 ≤
      (Real.sqrt (C / Real.pi) * t * (Real.pi * r ^ 2)) ^ 2 := by
    calc
      J ^ 2 ≤ (Real.pi * r ^ 2) * Q := by simpa only [hvolume] using hcs
      _ ≤ (Real.pi * r ^ 2) *
          (r ^ 2 * C * t ^ 2) :=
        mul_le_mul_of_nonneg_left hQ (mul_nonneg Real.pi_pos.le (sq_nonneg _))
      _ = _ := by
        simp only [mul_pow, Real.sq_sqrt (div_nonneg hC Real.pi_pos.le)]
        field_simp [Real.pi_pos.ne']
  have hJ : J ≤ Real.sqrt (C / Real.pi) * t *
      (Real.pi * r ^ 2) :=
    (sq_le_sq₀ hJnonneg (by positivity)).mp hJsq
  change r⁻¹ ^ α * (⨍ x in B, |u x - m|) ≤
    Real.sqrt (C / Real.pi)
  rw [setAverage_eq, hvolume, smul_eq_mul]
  change r⁻¹ ^ α * ((Real.pi * r ^ 2)⁻¹ * J) ≤ _
  calc
    _ ≤ r⁻¹ ^ α * ((Real.pi * r ^ 2)⁻¹ *
        (Real.sqrt (C / Real.pi) * t * (Real.pi * r ^ 2))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hJ (by positivity))
        (Real.rpow_nonneg (inv_nonneg.mpr hr.le) α)
    _ = Real.sqrt (C / Real.pi) := by
      rw [Real.inv_rpow hr.le α]
      dsimp only [t]
      field_simp [hr.ne', Real.pi_pos.ne', (Real.rpow_pos_of_pos hr α).ne']

end DifferentialGeometry.Analysis

end

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem exists_holder_representative_of_gradient_excess_bound
    {ι : Type*} [Fintype ι] {G : ι → V → V} {x₀ : V} {R α K : ℝ}
    (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (hG : ∀ i, MemLp (G i) 2 (volume.restrict (Metric.ball x₀ R)))
    (hexcess : ∀ b : DeGiorgi.CampanatoBall x₀ R,
      (∑ i, ∫ x in Metric.ball b.center b.radius,
        ‖G i x - ⨍ y in Metric.ball b.center b.radius, G i y‖ ^ 2) ≤
          K * b.radius ^ (2 + 2 * α)) :
    ∃ (g : ι → V → V) (C : ι → ℝ),
      (∀ i, 0 ≤ C i) ∧
      (∀ i, g i =ᵐ[volume.restrict (Metric.ball x₀ R)] G i) ∧
      (∀ i, ContinuousOn (g i) (Metric.ball x₀ (R / 2))) ∧
      ∀ i, ∀ x ∈ Metric.ball x₀ (R / 2), ∀ y ∈ Metric.ball x₀ (R / 2),
        ‖g i x - g i y‖ ≤ C i * ‖x - y‖ ^ α := by
  have hcamp (i : ι) (j : Fin 2) :
      ∃ C : ℝ, DeGiorgi.HasCampanatoBound (fun x => G i x j) x₀ R α C := by
    have hGij : MemLp (fun x => G i x j) 2 (volume.restrict (Metric.ball x₀ R)) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) j).comp_memLp' (hG i)
    have hsq (b : DeGiorgi.CampanatoBall x₀ R) :
        (∫ x in Metric.ball b.center b.radius,
          (G i x j - ⨍ y in Metric.ball b.center b.radius, G i y j) ^ 2) ≤
            K * b.radius ^ (2 + 2 * α) := by
      let : IsFiniteMeasure (volume.restrict (Metric.ball b.center b.radius)) :=
        isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
      have hLp := (hG i).mono_measure (Measure.restrict_mono_set volume b.subset_ball)
      apply (integral_component_sub_average_sq_le_vector_variance hLp j).trans
      apply le_trans _ (hexcess b)
      exact Finset.single_le_sum
        (f := fun k => ∫ x in Metric.ball b.center b.radius,
          ‖G k x - ⨍ y in Metric.ball b.center b.radius, G k y‖ ^ 2)
        (fun k _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ i)
    obtain ⟨C, _, hC⟩ := exists_campanato_bound_of_mean_square_decay hGij Subset.rfl hK hsq
    exact ⟨C, hC⟩
  choose g C hC hae hHolder using fun i =>
    exists_holder_representative_of_component_campanato_bounds hR hα hα1 (hcamp i)
  exact ⟨g, C, hC, hae, fun i => continuousOn_of_norm_sub_le_rpow (hC i) hα (hHolder i),
    hHolder⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_holder_bound_of_continuous_weak_gradient_power_bound
    {z : V → F} {x₀ : V} {R α K : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (Metric.ball x₀ R))
    (hzc : ContinuousOn z (Metric.ball x₀ R)) (hK : 0 ≤ K)
    (hpower : ∀ b : DeGiorgi.CampanatoBall x₀ R,
      (∑ i : ι, ∫ x in Metric.ball b.center b.radius, ‖(hz i).weakGrad x‖ ^ 2) ≤
        K * b.radius ^ (2 * α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.ball x₀ (R / 2), ∀ y ∈ Metric.ball x₀ (R / 2),
      ‖z x - z y‖ ≤ C * ‖x - y‖ ^ α := by
  have hcamp (i : ι) : ∃ C : ℝ, DeGiorgi.HasCampanatoBound (fun x => z x i) x₀ R α C := by
    have hsingle (b : DeGiorgi.CampanatoBall x₀ R) :
        (∫ x in Metric.ball b.center b.radius,
        ‖(hz i).weakGrad x‖ ^ 2) ≤ K * b.radius ^ (2 * α) := by
      have hs : (∫ x in Metric.ball b.center b.radius, ‖(hz i).weakGrad x‖ ^ 2) ≤
          ∑ k : ι, ∫ x in Metric.ball b.center b.radius, ‖(hz k).weakGrad x‖ ^ 2 :=
        Finset.single_le_sum
          (f := fun k =>
          ∫ x in Metric.ball b.center b.radius, ‖(hz k).weakGrad x‖ ^ 2)
          (fun k _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ i)
      exact hs.trans (hpower b)
    obtain ⟨C, _, hC⟩ :=
      exists_campanato_bound_of_weak_gradient_energy (hz i) (Subset.rfl) hK hsingle
    exact ⟨C, hC⟩
  obtain ⟨v, C, hC, hvae, hholder⟩ :=
    exists_holder_representative_of_component_campanato_bounds hR hα hα1 hcamp
  have hsub : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ R := Metric.ball_subset_ball (by linarith)
  have hvc := DifferentialGeometry.Analysis.continuousOn_of_norm_sub_le_rpow hC hα hholder
  have heq : EqOn v z (Metric.ball x₀ (R / 2)) :=
    volume.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hsub hvae)
      Metric.isOpen_ball hvc (hzc.mono hsub)
  refine ⟨C, hC, ?_⟩
  intro x hx y hy
  rw [← heq hx, ← heq hy]
  exact hholder x hx y hy

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
