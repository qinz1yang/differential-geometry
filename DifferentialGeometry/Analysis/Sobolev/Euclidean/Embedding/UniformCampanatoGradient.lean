import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.CampanatoGradient

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set Metric
open scoped Topology ENNReal

universe u

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- Quantitative form of the existing mean-square-to-Campanato estimate. Its body
is the unchanged scalar proof from `CampanatoGradient`, exposing the constant that
is hidden by that theorem's existential conclusion. -/
private theorem campanato_bound_of_mean_square_decay
    {Ω : Set E} {u : E → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    {x₀ : E} {R α C : ℝ} (hball : Metric.ball x₀ R ⊆ Ω) (hC : 0 ≤ C)
    (henergy : ∀ b : DeGiorgi.CampanatoBall x₀ R,
      (∫ x in Metric.ball b.center b.radius,
        (u x - ⨍ y in Metric.ball b.center b.radius, u y) ^ 2) ≤
        C * b.radius ^ (2 + 2 * α)) :
    DeGiorgi.HasCampanatoBound u x₀ R α (Real.sqrt (C / Real.pi)) := by
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

/-- A common cubic excess bound gives a common half-Hölder constant for any family
of continuous representatives. The constant is chosen before the index type and
both families, and the given representatives agree with the original data on the
full ball. No finiteness assumption on the family is needed. -/
theorem exists_uniform_holder_bound_of_continuous_gradient_excess
    {a : E} {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type u) (F G : ι → E → E),
      (∀ i, MemLp (F i) 2 (volume.restrict (ball a R))) →
      (∀ i, G i =ᵐ[volume.restrict (ball a R)] F i) →
      (∀ i, ContinuousOn (G i) (ball a (R / 2))) →
      (∀ i, ∀ b : DeGiorgi.CampanatoBall a R,
        (∫ x in ball b.center b.radius,
          ‖F i x - ⨍ y in ball b.center b.radius, F i y‖ ^ 2) ≤
            K * b.radius ^ 3) →
      ∀ i, ∀ x ∈ ball a (R / 2), ∀ y ∈ ball a (R / 2),
        ‖G i x - G i y‖ ≤ C * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  classical
  let Ccamp : ℝ := Real.sqrt (K / Real.pi)
  let H : ℝ := max (DeGiorgi.CCampanatoHolder 2 (1 / 2) * Ccamp) 0
  let C : ℝ := Real.sqrt (∑ _j : Fin 2, H ^ 2)
  have hH : 0 ≤ H := le_max_right _ _
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  refine ⟨C, hC, ?_⟩
  intro ι F G hF hGF hGc hexcess i
  have hcamp (j : Fin 2) :
      DeGiorgi.HasCampanatoBound (fun x => F i x j) a R (1 / 2) Ccamp := by
    have hFij : MemLp (fun x => F i x j) 2 (volume.restrict (ball a R)) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) j).comp_memLp' (hF i)
    apply campanato_bound_of_mean_square_decay hFij Subset.rfl hK
    intro b
    let : IsFiniteMeasure (volume.restrict (ball b.center b.radius)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hLp := (hF i).mono_measure (Measure.restrict_mono_set volume b.subset_ball)
    apply (integral_component_sub_average_sq_le_vector_variance hLp j).trans
    simpa only [show (2 : ℝ) + 2 * (1 / 2) = 3 by norm_num, Real.rpow_ofNat] using
      hexcess i b
  choose v hvae hvholder using fun j => DeGiorgi.campanato_implies_holder
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hR (hcamp j)
  have hvbound (j : Fin 2) :
      ∀ x ∈ ball a (R / 2), ∀ y ∈ ball a (R / 2),
        ‖v j x - v j y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    intro x hx y hy
    rw [Real.norm_eq_abs]
    exact (hvholder j x hx y hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  have hhalf : ball a (R / 2) ⊆ ball a R := ball_subset_ball (by linarith)
  have heq (j : Fin 2) : EqOn (v j) (fun x => G i x j) (ball a (R / 2)) := by
    have hFGj : (fun x => F i x j) =ᵐ[volume.restrict (ball a R)] (fun x => G i x j) := by
      filter_upwards [(hGF i).symm] with x hx
      exact congrArg (fun z : E => z j) hx
    have hvGj : (v j) =ᵐ[volume.restrict (ball a R)] (fun x => G i x j) :=
      Filter.EventuallyEq.trans (hvae j) hFGj
    have hvc : ContinuousOn (v j) (ball a (R / 2)) :=
      DifferentialGeometry.Analysis.continuousOn_of_norm_sub_le_rpow hH
        (by norm_num : (0 : ℝ) < 1 / 2) (hvbound j)
    have hGjc : ContinuousOn (fun x => G i x j) (ball a (R / 2)) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) j).continuous.comp_continuousOn (hGc i)
    exact volume.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hhalf hvGj)
      isOpen_ball hvc hGjc
  intro x hx y hy
  have hcomponent (j : Fin 2) : |G i x j - G i y j| ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    have hxv : v j x = G i x j := heq j hx
    have hyv : v j y = G i y j := heq j hy
    rw [← hxv, ← hyv]
    simpa only [Real.norm_eq_abs] using hvbound j x hx y hy
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC
    (Real.rpow_nonneg (norm_nonneg _) _))).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ j : Fin 2, (G i x j - G i y j) ^ 2) ≤ (C * ‖x - y‖ ^ (1 / 2 : ℝ)) ^ 2
  calc
    (∑ j : Fin 2, (G i x j - G i y j) ^ 2)
        ≤ ∑ _j : Fin 2, (H * ‖x - y‖ ^ (1 / 2 : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hH
        (Real.rpow_nonneg (norm_nonneg _) _))).mpr (hcomponent j)
      simpa only [sq_abs] using hh
    _ = (C * ‖x - y‖ ^ (1 / 2 : ℝ)) ^ 2 := by
      simp only [mul_pow]
      rw [← Finset.sum_mul]
      dsimp only [C]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg H)]

end DifferentialGeometry.Analysis.Sobolev.Euclidean
