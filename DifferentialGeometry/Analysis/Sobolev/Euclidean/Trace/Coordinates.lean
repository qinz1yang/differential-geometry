import DifferentialGeometry.Analysis.Integration.Measure.EuclideanPlane
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests
import Mathlib.MeasureTheory.Function.L2Space
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.DiskLimit

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "μV" => volume.restrict (Metric.ball (0 : V) 1)
private abbrev planarDisk : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
local notation "D" => planarDisk
local notation "μD" => volume.restrict D

private theorem memLp_smul_single {z : V → ℝ} (hz : MemLp z 2 μV) :
    MemLp (fun x => z x • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 2 μV :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))).comp_memLp' hz

private theorem integral_component_mul_eq_inner
    {u : V → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball (0 : V) 1))
    {z : V → ℝ} (hz : MemLp z 2 μV) :
    (∫ x in Metric.ball (0 : V) 1, hu.weakGrad x 1 * z x) =
      inner ℝ (DeGiorgi.gradLpOfWitness hu)
        ((memLp_smul_single hz).toLp
          (fun x => z x • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.weakGrad_memLp.coeFn_toLp,
    (memLp_smul_single hz).coeFn_toLp] with x hux hzx
  change hu.weakGrad x 1 * z x =
    inner ℝ (hu.weakGrad_memLp.toLp hu.weakGrad x)
      ((memLp_smul_single hz).toLp
        (fun x => z x • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) x)
  rw [hux, hzx, inner_smul_right, EuclideanSpace.inner_single_right]
  simp [mul_comm]

theorem tendsto_integral_fderiv_prod_of_weak_gradient
    {f : ℕ → V → ℝ} {v : V → ℝ}
    (hf : ∀ n, DeGiorgi.MemW1pWitness 2 (f n) (Metric.ball (0 : V) 1))
    (hv : DeGiorgi.MemW1pWitness 2 v (Metric.ball (0 : V) 1))
    (hrep : ∀ n, (fun x => (hf n).weakGrad x 1) =ᵐ[μV]
      (fun x => fderiv ℝ (f n) x (EuclideanSpace.single 1 1)))
    (hweak : ∀ z : Lp V 2 μV,
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hf n)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness hv) z)))
    (z : Lp ℝ 2 μD) :
    Tendsto (fun n => ∫ p in D,
      fderiv ℝ (f n ∘ euclideanPlaneProdEquiv.symm) p (0, 1) * z p) atTop
      (𝓝 (∫ p in D, hv.weakGrad (euclideanPlaneProdEquiv.symm p) 1 * z p)) := by
  have hz : MemLp (fun x : V => z (euclideanPlaneProdEquiv x)) 2 μV :=
    (Lp.memLp z).comp_measurePreserving measurePreserving_euclideanPlaneProdEquiv_unit_ball
  have h := hweak ((memLp_smul_single hz).toLp
    (fun x => z (euclideanPlaneProdEquiv x) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  have hn (n : ℕ) : (∫ p in D,
      fderiv ℝ (f n ∘ euclideanPlaneProdEquiv.symm) p (0, 1) * z p) =
      inner ℝ (DeGiorgi.gradLpOfWitness (hf n))
        ((memLp_smul_single hz).toLp
          (fun x => z (euclideanPlaneProdEquiv x) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) := by
    rw [integral_unit_disk_prod_eq_integral_ball]
    simp only [fderiv_comp_euclideanPlaneProdEquiv_symm_snd,
      ContinuousLinearEquiv.symm_apply_apply]
    rw [← integral_component_mul_eq_inner (hf n) hz]
    apply integral_congr_ae
    filter_upwards [hrep n] with x hx
    rw [hx]
  have hlast : (∫ p in D, hv.weakGrad (euclideanPlaneProdEquiv.symm p) 1 * z p) =
      inner ℝ (DeGiorgi.gradLpOfWitness hv)
        ((memLp_smul_single hz).toLp
          (fun x => z (euclideanPlaneProdEquiv x) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) := by
    rw [integral_unit_disk_prod_eq_integral_ball]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    exact integral_component_mul_eq_inner hv hz
  simpa only [hn, hlast] using h

end DifferentialGeometry.Analysis

end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "μV" => volume.restrict (Metric.ball (0 : V) 1)
private abbrev graphDisk : Set (ℝ × ℝ) :=
  regionBetween (fun x : ℝ => -Real.sqrt (1 - x ^ 2))
    (fun x : ℝ => Real.sqrt (1 - x ^ 2)) (Ioo (-1 : ℝ) 1)

private theorem graphDisk_eq_planarDisk : graphDisk = planarDisk := by
  ext p
  change (-1 < p.1 ∧ p.1 < 1) ∧
    (-Real.sqrt (1 - p.1 ^ 2) < p.2 ∧ p.2 < Real.sqrt (1 - p.1 ^ 2)) ↔
      p.1 ^ 2 + p.2 ^ 2 < 1
  constructor
  · intro hp
    have hx : 0 ≤ 1 - p.1 ^ 2 := by nlinarith [hp.1.1, hp.1.2]
    have hsq := Real.sq_sqrt hx
    have hy : p.2 ^ 2 < (Real.sqrt (1 - p.1 ^ 2)) ^ 2 := by nlinarith [hp.2.1, hp.2.2]
    nlinarith
  · intro hp
    have hx : 0 < 1 - p.1 ^ 2 := by nlinarith [sq_nonneg p.2]
    have hsqrt := Real.sqrt_nonneg (1 - p.1 ^ 2)
    have hsq := Real.sq_sqrt hx.le
    exact ⟨⟨by nlinarith [sq_nonneg p.2], by nlinarith [sq_nonneg p.2]⟩,
      ⟨by nlinarith, by nlinarith⟩⟩

private theorem inner_toLp_eq_integral_mul_right
    {P : Type*} [MeasurableSpace P] {μ : Measure P} {f : P → ℝ}
    (hf : MemLp f 2 μ) (z : Lp ℝ 2 μ) :
    inner ℝ (hf.toLp f) z = ∫ x, f x * z x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hfx
  rw [hfx, real_inner_comm]
  rfl

theorem integral_weakGrad_snd_mul_add_eq_boundary_of_tendsto_disk
    {f : ℕ → V → ℝ} {v : V → ℝ} {K : ℕ → ℝ≥0}
    (hLip : ∀ n, LipschitzWith (K n) (f n))
    (hf : ∀ n, DeGiorgi.MemW1pWitness 2 (f n) (Metric.ball (0 : V) 1))
    (hv : DeGiorgi.MemW1pWitness 2 v (Metric.ball (0 : V) 1))
    (hrep : ∀ n, (fun x => (hf n).weakGrad x 1) =ᵐ[μV]
      (fun x => fderiv ℝ (f n) x (EuclideanSpace.single 1 1)))
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x - v x) 2 μV) atTop (𝓝 0))
    (hweak : ∀ z : Lp V 2 μV,
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hf n)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness hv) z)))
    {ηa ηb : ℝ → ℝ}
    (haLim : TendstoUniformlyOn (fun n x => f n (euclideanPlaneProdEquiv.symm
        (x, -Real.sqrt (1 - x ^ 2)))) ηa atTop (Icc (-1 : ℝ) 1))
    (hbLim : TendstoUniformlyOn (fun n x => f n (euclideanPlaneProdEquiv.symm
        (x, Real.sqrt (1 - x ^ 2)))) ηb atTop (Icc (-1 : ℝ) 1))
    {L : ℝ≥0} {g : ℝ × ℝ → ℝ} (hg : LipschitzWith L g) :
    (∫ x in Metric.ball (0 : V) 1,
      hv.weakGrad x 1 * g (euclideanPlaneProdEquiv x) +
        v x * fderiv ℝ g (euclideanPlaneProdEquiv x) (0, 1)) =
      ∫ x in Ioo (-1 : ℝ) 1,
        ηb x * g (x, Real.sqrt (1 - x ^ 2)) - ηa x * g (x, -Real.sqrt (1 - x ^ 2)) := by
  let f' (n : ℕ) := f n ∘ euclideanPlaneProdEquiv.symm
  let v' := v ∘ euclideanPlaneProdEquiv.symm
  let G' := fun p : ℝ × ℝ => hv.weakGrad (euclideanPlaneProdEquiv.symm p) 1
  have hfLip (n : ℕ) : LipschitzWith (K n * ‖euclideanPlaneProdEquiv.symm.toContinuousLinearMap‖₊)
      (f' n) := (hLip n).comp euclideanPlaneProdEquiv.symm.lipschitzWith
  have hv' : MemLp v' 2 (volume.restrict graphDisk) := by
    rw [graphDisk_eq_planarDisk]
    exact hv.memLp.comp_measurePreserving measurePreserving_euclideanPlaneProdEquiv_symm_unit_disk
  have hG' : MemLp G' 2 (volume.restrict graphDisk) := by
    rw [graphDisk_eq_planarDisk]
    exact (hv.weakGrad_component_memLp 1).comp_measurePreserving
      measurePreserving_euclideanPlaneProdEquiv_symm_unit_disk
  have hlim' : Tendsto (fun n => eLpNorm (fun p => f' n p - v' p) 2
      (volume.restrict graphDisk)) atTop (𝓝 0) := by
    rw [graphDisk_eq_planarDisk]
    have heq (n : ℕ) : eLpNorm (fun p => f' n p - v' p) 2 (volume.restrict planarDisk) =
        eLpNorm (fun x => f n x - v x) 2 μV :=
      eLpNorm_comp_euclideanPlaneProdEquiv_symm ((hf n).memLp.sub hv.memLp).aestronglyMeasurable 2
    simpa only [heq] using hlim
  have hDn (n : ℕ) : MemLp (fun p => fderiv ℝ (f' n) p (0, 1)) 2
      (volume.restrict graphDisk) := by
    rw [graphDisk_eq_planarDisk]
    have h := ((hf n).weakGrad_component_memLp 1).comp_measurePreserving
      measurePreserving_euclideanPlaneProdEquiv_symm_unit_disk
    apply h.ae_eq
    filter_upwards [measurePreserving_euclideanPlaneProdEquiv_symm_unit_disk.quasiMeasurePreserving.ae
      (hrep n)] with p hp
    exact hp.trans
      (fderiv_comp_euclideanPlaneProdEquiv_symm_snd (f n) p).symm
  have hweak' (z : Lp ℝ 2 (volume.restrict graphDisk)) :
      Tendsto (fun n => inner ℝ ((hDn n).toLp (fun p => fderiv ℝ (f' n) p (0, 1))) z)
        atTop (𝓝 (inner ℝ (hG'.toLp G') z)) := by
    simp only [inner_toLp_eq_integral_mul_right]
    revert z
    rw [graphDisk_eq_planarDisk]
    intro z
    exact tendsto_integral_fderiv_prod_of_weak_gradient hf hv hrep hweak z
  have h := integral_mul_weak_deriv_snd_add_unit_disk_eq_boundary_of_uniform_limit
    hfLip hv' hG' hlim' hweak' haLim hbLim hg
  change (∫ p in graphDisk, G' p * g p + v' p * fderiv ℝ g p (0, 1)) = _ at h
  rw [graphDisk_eq_planarDisk, integral_unit_disk_prod_eq_integral_ball] at h
  simpa only [G', v', Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using h

end DifferentialGeometry.Analysis

end
