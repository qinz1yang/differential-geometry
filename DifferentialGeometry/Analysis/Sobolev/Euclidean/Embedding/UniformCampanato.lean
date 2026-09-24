import DifferentialGeometry.Analysis.Sobolev.Euclidean.Poincare
import DifferentialGeometry.External.DeGiorgi.Oscillation.Campanato
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import DifferentialGeometry.Analysis.Asymptotics.PowerDecay
import DifferentialGeometry.Topology.MetricSpace.HolderContinuity

section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem campanato_bound_of_weak_gradient_energy
    {Ω : Set E} {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    {x₀ : E} {R α C : ℝ} (hball : Metric.ball x₀ R ⊆ Ω) (hC : 0 ≤ C)
    (henergy : ∀ b : DeGiorgi.CampanatoBall x₀ R,
      (∫ x in Metric.ball b.center b.radius, ‖hu.weakGrad x‖ ^ 2) ≤
        C * b.radius ^ (2 * α)) :
    DeGiorgi.HasCampanatoBound u x₀ R α
      (DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi)) := by
  have hp : 0 ≤ DeGiorgi.CPoincVal 2 :=
    (DeGiorgi.C_poinc_val_pos (by norm_num : 0 < (2 : ℕ))).le
  intro b
  let r : ℝ := b.radius
  let B : Set E := Metric.ball b.center r
  let μ : Measure E := volume.restrict B
  have hr : 0 < r := b.radius_pos
  have hBΩ : B ⊆ Ω := b.subset_ball.trans hball
  let huB : DeGiorgi.MemW1pWitness 2 u B := hu.restrict Metric.isOpen_ball hBΩ
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have huLp : MemLp u 2 μ := huB.memLp
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
  have hrpow : r ^ (2 * α) = t ^ 2 := by
    dsimp only [t]
    rw [mul_comm (2 : ℝ) α, Real.rpow_mul hr.le, Real.rpow_two]
  have hvar := integral_sub_average_sq_le_radius_sq_mul_weakGrad hr huB
  change Q ≤ (DeGiorgi.CPoincVal 2) ^ 2 * r ^ 2 *
    ∫ x in B, ‖hu.weakGrad x‖ ^ 2 at hvar
  have hE : (∫ x in B, ‖hu.weakGrad x‖ ^ 2) ≤ C * t ^ 2 := by
    have h := henergy b
    change (∫ x in B, ‖hu.weakGrad x‖ ^ 2) ≤ C * r ^ (2 * α) at h
    rwa [hrpow] at h
  have hQ : Q ≤ (DeGiorgi.CPoincVal 2) ^ 2 * r ^ 2 * C * t ^ 2 := by
    calc
      Q ≤ (DeGiorgi.CPoincVal 2) ^ 2 * r ^ 2 *
          ∫ x in B, ‖hu.weakGrad x‖ ^ 2 := hvar
      _ ≤ (DeGiorgi.CPoincVal 2) ^ 2 * r ^ 2 * (C * t ^ 2) :=
        mul_le_mul_of_nonneg_left hE (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = _ := by ring
  have hJnonneg : 0 ≤ J := integral_nonneg fun x => abs_nonneg _
  have hJsq : J ^ 2 ≤
      (DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi) * t * (Real.pi * r ^ 2)) ^ 2 := by
    calc
      J ^ 2 ≤ (Real.pi * r ^ 2) * Q := by simpa only [hvolume] using hcs
      _ ≤ (Real.pi * r ^ 2) *
          ((DeGiorgi.CPoincVal 2) ^ 2 * r ^ 2 * C * t ^ 2) :=
        mul_le_mul_of_nonneg_left hQ (mul_nonneg Real.pi_pos.le (sq_nonneg _))
      _ = _ := by
        simp only [mul_pow, Real.sq_sqrt (div_nonneg hC Real.pi_pos.le)]
        field_simp [Real.pi_pos.ne']
  have hJ : J ≤ DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi) * t *
      (Real.pi * r ^ 2) :=
    (sq_le_sq₀ hJnonneg (by positivity)).mp hJsq
  change r⁻¹ ^ α * (⨍ x in B, |u x - m|) ≤
    DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi)
  rw [setAverage_eq, hvolume, smul_eq_mul]
  change r⁻¹ ^ α * ((Real.pi * r ^ 2)⁻¹ * J) ≤ _
  calc
    _ ≤ r⁻¹ ^ α * ((Real.pi * r ^ 2)⁻¹ *
        (DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi) * t * (Real.pi * r ^ 2))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hJ (by positivity))
        (Real.rpow_nonneg (inv_nonneg.mpr hr.le) α)
    _ = DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi) := by
      rw [Real.inv_rpow hr.le α]
      dsimp only [t]
      field_simp [hr.ne', Real.pi_pos.ne', (Real.rpow_pos_of_pos hr α).ne']


end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

noncomputable section

open Filter MeasureTheory Set Metric
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem exists_uniform_local_holder_representative_of_dyadic_energy_bound
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      ∀ (N : ℕ) (B : ℝ), 0 ≤ B → ∀ x₀ : V, ‖x₀‖ < 1 →
        ∃ r H : ℝ, 0 < r ∧ 0 ≤ H ∧ ball x₀ r ⊆ ball (0 : V) 1 ∧
          ∀ (f : V → ℝ) (hw : DeGiorgi.MemW1pWitness 2 f (ball 0 1)),
            (∀ (b : V) (R : ℝ), 0 < R → ‖b‖ + R < 1 → ∀ k : ℕ,
              (∫ x in ball b (R / 2 ^ (N + k)), ‖hw.weakGrad x‖ ^ 2) ≤ θ ^ k * B) →
            ∃ w : V → ℝ, w =ᵐ[volume.restrict (ball x₀ r)] f ∧
              ContinuousOn w (ball x₀ (r / 2)) ∧
              ∀ x ∈ ball x₀ (r / 2), ∀ y ∈ ball x₀ (r / 2),
                ‖w x - w y‖ ≤ H * ‖x - y‖ ^ α := by
  let σ : ℝ := max θ (1 / 2)
  have hσ : 0 < σ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _)
  have hσ1 : σ < 1 := max_lt hθ1 (by norm_num)
  have hloghalf : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  let q : ℝ := Real.log σ / Real.log (1 / 2 : ℝ)
  have hq : 0 < q := div_pos_of_neg_of_neg (Real.log_neg hσ hσ1) hloghalf
  have hq1 : q ≤ 1 := (div_le_one_of_neg hloghalf).mpr
    (Real.log_le_log (by norm_num) (le_max_right _ _))
  have hpow : (1 / 2 : ℝ) ^ q = σ := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have he : Real.log (1 / 2 : ℝ) * q = Real.log σ := by
      dsimp only [q]
      field_simp [hloghalf.ne]
    rw [he, Real.exp_log hσ]
  let α : ℝ := q / 2
  have hα : 0 < α := half_pos hq
  have hα1 : α ≤ 1 := by dsimp only [α]; linarith
  have hαq : 2 * α = q := by dsimp only [α]; ring
  refine ⟨α, hα, hα1, ?_⟩
  intro N B hB x₀ hx₀
  let R₀ : ℝ := (1 - ‖x₀‖) / 4
  have hR₀ : 0 < R₀ := div_pos (sub_pos.mpr hx₀) (by norm_num)
  let S : ℝ := R₀ / 2 ^ N
  have hS : 0 < S := div_pos hR₀ (by positivity)
  have hSR : S ≤ R₀ := div_le_self hR₀.le (one_le_pow₀ (by norm_num))
  have hmargin : ‖x₀‖ + 2 * R₀ < 1 := by dsimp only [R₀]; linarith
  have hbase (b : V) (hb : b ∈ ball x₀ S) : ‖b‖ + R₀ < 1 := by
    have hn : ‖b‖ ≤ dist b x₀ + ‖x₀‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (b - x₀) x₀
    have hd := mem_ball.mp hb
    linarith
  have hball : ball x₀ S ⊆ ball (0 : V) 1 := by
    intro b hb
    rw [mem_ball, dist_zero_right]
    have hh := hbase b hb
    linarith
  let C : ℝ := B / ((1 / 2 : ℝ) * S) ^ q
  have hC : 0 ≤ C := div_nonneg hB (Real.rpow_nonneg (by positivity) q)
  let Ccamp : ℝ := DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi)
  let H : ℝ := max (DeGiorgi.CCampanatoHolder 2 α * Ccamp) 0
  have hH : 0 ≤ H := le_max_right _ _
  refine ⟨S, H, hS, hH, hball, ?_⟩
  intro f hw hdyadic
  have hpower (b : V) (hb : b ∈ ball x₀ S) :
      ∀ s ∈ Ioc (0 : ℝ) S, (∫ x in ball b s, ‖hw.weakGrad x‖ ^ 2) ≤ C * s ^ q := by
    have hbin : ‖b‖ + R₀ < 1 := hbase b hb
    have hsub : ball b S ⊆ ball (0 : V) 1 := by
      intro x hx
      have hn : ‖x‖ ≤ dist x b + ‖b‖ := by
        simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - b) b
      have hd := mem_ball.mp hx
      exact mem_ball.mpr (by rw [dist_zero_right]; linarith)
    have hi0 : IntegrableOn (fun x => ‖hw.weakGrad x‖ ^ 2) (ball (0 : V) 1) :=
      hw.weakGrad_memLp.norm.integrable_sq
    have hi : IntegrableOn (fun x => ‖hw.weakGrad x‖ ^ 2) (ball b S) := hi0.mono_set hsub
    have hmono : MonotoneOn (fun s => ∫ x in ball b s, ‖hw.weakGrad x‖ ^ 2) (Ioc (0 : ℝ) S) := by
      intro a ha c hc hac
      exact setIntegral_mono_set (hi.mono_set (ball_subset_ball hc.2))
        (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall (ball_subset_ball hac))
    have hdec (k : ℕ) : (∫ x in ball b ((1 / 2 : ℝ) ^ k * S), ‖hw.weakGrad x‖ ^ 2) ≤
        ((1 / 2 : ℝ) ^ q) ^ k * B := by
      have hscale : (1 / 2 : ℝ) ^ k * S = R₀ / 2 ^ (N + k) := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow,
          show S = R₀ / 2 ^ N from rfl, pow_add, div_mul_eq_div_div, div_eq_mul_inv]
        ring
      rw [hscale, hpow]
      exact (hdyadic b R₀ hR₀ hbin k).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hθ (le_max_left _ _) k) hB)
    exact DifferentialGeometry.Analysis.radius_power_bound_of_geometric_decay
      (by norm_num) (by norm_num) hS hq.le hB hmono hdec
  have hcamp : DeGiorgi.HasCampanatoBound f x₀ S α Ccamp := by
    apply campanato_bound_of_weak_gradient_energy hw hball hC
    intro b
    have hb : b.center ∈ ball x₀ S := b.subset_ball (mem_ball_self b.radius_pos)
    rw [hαq]
    exact hpower b.center hb b.radius ⟨b.radius_pos, b.radius_le⟩
  obtain ⟨w, hwae, hwholder⟩ := DeGiorgi.campanato_implies_holder hα hα1 hS hcamp
  have hbound : ∀ x ∈ ball x₀ (S / 2), ∀ y ∈ ball x₀ (S / 2),
      ‖w x - w y‖ ≤ H * ‖x - y‖ ^ α := by
    intro x hx y hy
    rw [Real.norm_eq_abs]
    exact (hwholder x hx y hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  exact ⟨w, hwae, DifferentialGeometry.Analysis.continuousOn_of_norm_sub_le_rpow hH hα hbound,
    hbound⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
