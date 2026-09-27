import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Locality
import DifferentialGeometry.Analysis.Integration.Integral.Comparison
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import Mathlib.MeasureTheory.Integral.Bochner.Set
import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ZeroTraceRange

section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Finite ι]
variable {Ω U : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem weakGrad_columns_ae_eq_of_ae_eq
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hU : IsOpen U) (hsub : U ⊆ Ω)
    {f g : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness p (fun x => f x i) Ω)
    (hg : ∀ i, DeGiorgi.MemW1pWitness p (fun x => g x i) Ω)
    (hfg : f =ᵐ[volume.restrict U] g) :
    ∀ᵐ x ∂volume.restrict U, ∀ j : Fin d,
      WithLp.toLp 2 (fun i => (hf i).weakGrad x j) =
        WithLp.toLp 2 (fun i => (hg i).weakGrad x j) := by
  have heq (i : ι) : (hf i).weakGrad =ᵐ[volume.restrict U] (hg i).weakGrad :=
    DeGiorgi.MemW1pWitness.weakGrad_ae_eq_of_ae_eq hp hU hsub (hf i) (hg i)
      (hfg.mono fun x hx => congrArg (fun z : F => z i) hx)
  filter_upwards [ae_all_iff.mpr heq] with x hx
  intro j
  congr 1
  funext i
  rw [hx i]

theorem quadratic_weakGrad_columns_ae_eq_of_ae_eq
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hU : IsOpen U) (hsub : U ⊆ Ω)
    {f g : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness p (fun x => f x i) Ω)
    (hg : ∀ i, DeGiorgi.MemW1pWitness p (fun x => g x i) Ω)
    (hfg : f =ᵐ[volume.restrict U] g)
    (A : E → F → F →L[ℝ] F →L[ℝ] ℝ) :
    ∀ᵐ x ∂volume.restrict U, ∀ j : Fin d,
      A x (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) =
      A x (g x) (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hg i).weakGrad x j)) := by
  filter_upwards [hfg, weakGrad_columns_ae_eq_of_ae_eq hp hU hsub hf hg hfg] with x hx hgrad
  intro j
  rw [hx, hgrad j]

theorem sum_integral_quadratic_weakGrad_closedBall_le_of_ae_eq_on_collar
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hΩ : IsOpen Ω)
    {f g : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness p (fun x => f x i) Ω)
    (hg : ∀ i, DeGiorgi.MemW1pWitness p (fun x => g x i) Ω)
    (A : E → F → F →L[ℝ] F →L[ℝ] ℝ)
    {c : E} {r R : ℝ} (hrR : r ≤ R) (hball : Metric.closedBall c R ⊆ Ω)
    (hfg : f =ᵐ[volume.restrict (Ω \ Metric.closedBall c r)] g)
    (hfi : ∀ j : Fin d, IntegrableOn
      (fun x => A x (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) (Metric.closedBall c R))
    (hgi : ∀ j : Fin d, IntegrableOn
      (fun x => A x (g x) (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))) (Metric.closedBall c R))
    (hle : (∑ j : Fin d, ∫ x in Metric.closedBall c R,
      A x (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) ≤
      ∑ j : Fin d, ∫ x in Metric.closedBall c R,
        A x (g x) (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))) :
    (∑ j : Fin d, ∫ x in Metric.closedBall c r,
      A x (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) ≤
      ∑ j : Fin d, ∫ x in Metric.closedBall c r,
        A x (g x) (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hg i).weakGrad x j)) := by
  let Ef (j : Fin d) (x : E) := A x (f x)
    (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
  let Eg (j : Fin d) (x : E) := A x (g x)
    (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
  have hsub : Metric.closedBall c r ⊆ Metric.closedBall c R :=
    Metric.closedBall_subset_closedBall hrR
  have hcollar : ∀ᵐ x ∂volume.restrict (Ω \ Metric.closedBall c r),
      ∀ j, Ef j x = Eg j x :=
    quadratic_weakGrad_columns_ae_eq_of_ae_eq hp (hΩ.sdiff Metric.isClosed_closedBall)
      sdiff_subset hf hg hfg A
  have hrestrict : ∀ᵐ x ∂volume.restrict (Metric.closedBall c R \ Metric.closedBall c r),
      ∀ j, Ef j x = Eg j x :=
    ae_restrict_of_ae_restrict_of_subset (sdiff_subset_sdiff_left hball) hcollar
  have hsum : (fun x => ∑ j, Ef j x) =ᵐ[volume.restrict
      (Metric.closedBall c R \ Metric.closedBall c r)] (fun x => ∑ j, Eg j x) :=
    hrestrict.mono fun x hx => Finset.sum_congr rfl fun j _ => hx j
  have hEfR : IntegrableOn (fun x => ∑ j, Ef j x) (Metric.closedBall c R) :=
    integrable_finsetSum _ fun j _ => hfi j
  have hEgR : IntegrableOn (fun x => ∑ j, Eg j x) (Metric.closedBall c R) :=
    integrable_finsetSum _ fun j _ => hgi j
  have hleR : (∫ x in Metric.closedBall c R, ∑ j, Ef j x) ≤
      ∫ x in Metric.closedBall c R, ∑ j, Eg j x := by
    rw [integral_finsetSum _ (fun j _ => hfi j), integral_finsetSum _ (fun j _ => hgi j)]
    exact hle
  have h := setIntegral_le_of_ae_eq_on_sdiff measurableSet_closedBall hsub hEfR hEgR hsum hleR
  rw [integral_finsetSum _ (fun j _ => (hfi j).mono_set hsub),
    integral_finsetSum _ (fun j _ => (hgi j).mono_set hsub)] at h
  exact h

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Finite ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem integrable_quadratic_weakGrad_column_of_compact_range
    {Ω : Set E} {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    {K : Set F} (hK : IsCompact K) (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K) (j : Fin d) :
    IntegrableOn (fun x => A (f x)
      (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) Ω := by
  classical
  let _ := Fintype.ofFinite ι
  have hfm : MemLp f 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).memLp
  have hG : MemLp (fun x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
      2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).weakGrad_component_memLp j
  have hmeas (v w : F) : AEStronglyMeasurable (fun x => A (f x) v w) (volume.restrict Ω) := by
    have hc : ContinuousOn (fun y => A y v w) K :=
      (hA.clm_apply continuousOn_const).clm_apply continuousOn_const
    have hm : Measurable (K.piecewise (fun y => A y v w) (fun _ => 0)) :=
      hc.measurable_piecewise continuousOn_const hK.measurableSet
    have hh := (hm.comp_aemeasurable hfm.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    apply hh.congr
    filter_upwards [hfK] with x hx
    exact piecewise_eq_of_mem _ _ _ hx
  have hAnorm : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hAnorm
  have hbound : ∀ᵐ x ∂volume.restrict Ω, ‖A (f x)‖ ≤ C :=
    hfK.mono fun x hx => hC (mem_image_of_mem (fun y => ‖A y‖) hx)
  exact integrable_bilinear_of_apply_aestronglyMeasurable (fun x => A (f x))
    hmeas hbound hG hG

variable [NeZero d]

theorem quadratic_weakGrad_energy_le_on_ball_of_ae_eq_on_annulus
    {Ω : Set E} {f g : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hg : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => g x i) Ω)
    {K : Set F} (hK : IsCompact K)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    (hgK : ∀ᵐ x ∂volume.restrict Ω, g x ∈ K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K)
    {c : E} {r R : ℝ} (hrR : r ≤ R) (hball : ball c R ⊆ Ω)
    (hfg : f =ᵐ[volume.restrict (ball c R \ closedBall c r)] g)
    (hle : (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball c R,
      A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) ≤
      (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball c R,
        A (g x) (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hg i).weakGrad x j)))) :
    (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball c r,
      A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) ≤
      (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball c r,
        A (g x) (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))) := by
  classical
  let _ := Fintype.ofFinite ι
  let Ef (j : Fin d) (x : E) := A (f x)
    (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
  let Eg (j : Fin d) (x : E) := A (g x)
    (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
  have hfi (j : Fin d) : IntegrableOn (Ef j) (ball c R) :=
    (integrable_quadratic_weakGrad_column_of_compact_range hf hK hfK A hA j).mono_set hball
  have hgi (j : Fin d) : IntegrableOn (Eg j) (ball c R) :=
    (integrable_quadratic_weakGrad_column_of_compact_range hg hK hgK A hA j).mono_set hball
  have hlocal := quadratic_weakGrad_columns_ae_eq_of_ae_eq (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (isOpen_ball.sdiff isClosed_closedBall) (sdiff_subset.trans hball) hf hg hfg (fun _ => A)
  have hsets : ball c R \ ball c r =ᵐ[volume] ball c R \ closedBall c r := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp (Measure.addHaar_sphere volume c r)]
      with x hx
    have hne : dist x c ≠ r := by simpa only [mem_sphere] using hx
    apply propext
    change (dist x c < R ∧ ¬ dist x c < r) ↔ (dist x c < R ∧ ¬ dist x c ≤ r)
    simp only [not_lt, not_le]
    exact and_congr_right fun _ =>
      ⟨fun h => lt_of_le_of_ne h hne.symm, fun h => h.le⟩
  have hcollar : (fun x => ∑ j, Ef j x) =ᵐ[volume.restrict (ball c R \ closedBall c r)]
      (fun x => ∑ j, Eg j x) :=
    hlocal.mono fun x hx => Finset.sum_congr rfl fun j _ => hx j
  have hdiff : (fun x => ∑ j, Ef j x) =ᵐ[volume.restrict (ball c R \ ball c r)]
      (fun x => ∑ j, Eg j x) := by
    have hμ : volume.restrict (ball c R \ ball c r) =
        volume.restrict (ball c R \ closedBall c r) := Measure.restrict_congr_set hsets
    exact hμ.symm ▸ hcollar
  have hEf : IntegrableOn (fun x => ∑ j, Ef j x) (ball c R) :=
    integrable_finsetSum _ fun j _ => hfi j
  have hEg : IntegrableOn (fun x => ∑ j, Eg j x) (ball c R) :=
    integrable_finsetSum _ fun j _ => hgi j
  have hleR : (∫ x in ball c R, ∑ j, Ef j x) ≤ ∫ x in ball c R, ∑ j, Eg j x := by
    rw [integral_finsetSum _ (fun j _ => hfi j), integral_finsetSum _ (fun j _ => hgi j)]
    linarith [hle]
  have hsub : ball c r ⊆ ball c R := ball_subset_ball hrR
  have h := setIntegral_le_of_ae_eq_on_sdiff measurableSet_ball hsub hEf hEg hdiff hleR
  rw [integral_finsetSum _ (fun j _ => (hfi j).mono_set hsub),
    integral_finsetSum _ (fun j _ => (hgi j).mono_set hsub)] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {ι : Type*} [Finite ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem quadratic_weakGrad_energy_le_on_ball_of_ae_eq_on_complement
    {Ω : Set E} {f g : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hg : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => g x i) Ω)
    {K : Set F} (hK : IsCompact K)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    (hgK : ∀ᵐ x ∂volume.restrict Ω, g x ∈ K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K)
    {b c : E} {s R : ℝ} (hsub : ball c s ⊆ ball b R) (hball : ball b R ⊆ Ω)
    (hfg : f =ᵐ[volume.restrict (ball b R \ closedBall c s)] g)
    (hle : (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball b R,
      A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) ≤
      (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball b R,
        A (g x) (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hg i).weakGrad x j)))) :
    (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball c s,
      A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) ≤
      (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball c s,
        A (g x) (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))) := by
  classical
  let _ := Fintype.ofFinite ι
  let Ef (j : Fin d) (x : E) := A (f x)
    (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
  let Eg (j : Fin d) (x : E) := A (g x)
    (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hg i).weakGrad x j))
  have hfi (j : Fin d) : IntegrableOn (Ef j) (ball b R) :=
    (integrable_quadratic_weakGrad_column_of_compact_range hf hK hfK A hA j).mono_set hball
  have hgi (j : Fin d) : IntegrableOn (Eg j) (ball b R) :=
    (integrable_quadratic_weakGrad_column_of_compact_range hg hK hgK A hA j).mono_set hball
  have hlocal := quadratic_weakGrad_columns_ae_eq_of_ae_eq (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (isOpen_ball.sdiff isClosed_closedBall) (sdiff_subset.trans hball) hf hg hfg (fun _ => A)
  have hsets : ball b R \ ball c s =ᵐ[volume] ball b R \ closedBall c s := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp (Measure.addHaar_sphere volume c s)]
      with x hx
    have hne : dist x c ≠ s := by simpa only [mem_sphere] using hx
    apply propext
    change (dist x b < R ∧ ¬ dist x c < s) ↔ (dist x b < R ∧ ¬ dist x c ≤ s)
    simp only [not_lt, not_le]
    exact and_congr_right fun _ =>
      ⟨fun h => lt_of_le_of_ne h hne.symm, fun h => h.le⟩
  have hcollar : (fun x => ∑ j, Ef j x) =ᵐ[volume.restrict (ball b R \ closedBall c s)]
      (fun x => ∑ j, Eg j x) :=
    hlocal.mono fun x hx => Finset.sum_congr rfl fun j _ => hx j
  have hdiff : (fun x => ∑ j, Ef j x) =ᵐ[volume.restrict (ball b R \ ball c s)]
      (fun x => ∑ j, Eg j x) := by
    have hμ : volume.restrict (ball b R \ ball c s) =
        volume.restrict (ball b R \ closedBall c s) := Measure.restrict_congr_set hsets
    exact hμ.symm ▸ hcollar
  have hEf : IntegrableOn (fun x => ∑ j, Ef j x) (ball b R) :=
    integrable_finsetSum _ fun j _ => hfi j
  have hEg : IntegrableOn (fun x => ∑ j, Eg j x) (ball b R) :=
    integrable_finsetSum _ fun j _ => hgi j
  have hleR : (∫ x in ball b R, ∑ j, Ef j x) ≤ ∫ x in ball b R, ∑ j, Eg j x := by
    rw [integral_finsetSum _ (fun j _ => hfi j), integral_finsetSum _ (fun j _ => hgi j)]
    linarith [hle]
  have h := setIntegral_le_of_ae_eq_on_sdiff measurableSet_ball hsub hEf hEg hdiff hleR
  rw [integral_finsetSum _ (fun j _ => (hfi j).mono_set hsub),
    integral_finsetSum _ (fun j _ => (hgi j).mono_set hsub)] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {ι : Type*} [Finite ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem quadratic_weakGrad_energy_le_on_subball_of_concentric_minimality
    {R : ℝ} {z : E → F}
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : E) R))
    {K : Set F} (hK : IsCompact K) (hzK : ∀ᵐ x ∂volume.restrict (ball (0 : E) R), z x ∈ K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K)
    (hmin : ∀ t : ℝ, 0 < t → t < R → ∀ f : E → F,
      ∀ hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) (ball (0 : E) t),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => f x i - z x i) (ball (0 : E) t)) →
      (∀ᵐ x ∂volume.restrict (ball (0 : E) t), f x ∈ K) →
      (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball (0 : E) t,
        A (z x) (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
        (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball (0 : E) t,
          A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))))
    {c : E} {s : ℝ} (hs : 0 < s) (hcs : ‖c‖ + s < R)
    (q : E → F) (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (ball c s))
    (hqz : ∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) (ball c s))
    (hqK : ∀ᵐ x ∂volume.restrict (ball c s), q x ∈ K) :
    (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball c s,
      A (z x) (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
      (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in ball c s,
        A (q x) (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))) := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨t, hct, htR⟩ := exists_between hcs
  have ht : 0 < t := (add_pos_of_nonneg_of_pos (norm_nonneg c) hs).trans hct
  have hclosed : closedBall c s ⊆ ball (0 : E) t := by
    intro x hx
    have hn : ‖x‖ ≤ dist x c + ‖c‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - c) c
    have hd := mem_closedBall.mp hx
    exact mem_ball_zero_iff.mpr (by linarith)
  have hsub : ball c s ⊆ ball (0 : E) t := ball_subset_closedBall.trans hclosed
  have htΩ : ball (0 : E) t ⊆ ball (0 : E) R := ball_subset_ball htR.le
  obtain ⟨f, hf, hfq, hfz, hfK, hgradfq⟩ := exists_weak_extension_mem_set_of_memW01p_sub
    isOpen_ball isOpen_ball (hsub.trans htΩ) hz hq hqz hzK hqK
  have htrace (i : ι) : DeGiorgi.MemW01p 2 (fun x => f x i - z x i) (ball (0 : E) t) := by
    let hd := (((hf i).restrict isOpen_ball htΩ).add
      (((hz i).restrict isOpen_ball htΩ).smul (-1))).congr
        (Eventually.of_forall fun x => by
          change f x i + -1 * z x i = f x i - z x i
          ring)
    have hsupp : tsupport (fun x => f x i - z x i) ⊆ closedBall c s := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      apply ball_subset_closedBall
      by_contra hxout
      exact hx (by
        change f x i - z x i = 0
        rw [hfz hxout, sub_self])
    have hcompact : HasCompactSupport (fun x => f x i - z x i) :=
      (isCompact_closedBall c s).of_isClosed_subset (isClosed_tsupport _) hsupp
    simpa only [ENNReal.ofReal_ofNat] using
      DeGiorgi.memW01p_of_memW1p_of_tsupport_subset isOpen_ball (by norm_num : (1 : ℝ) < 2)
        (by simpa only [ENNReal.ofReal_ofNat] using hd.memW1p) hcompact (hsupp.trans hclosed)
  have hle := hmin t ht htR f (fun i => (hf i).restrict isOpen_ball htΩ) htrace
    (ae_restrict_of_ae_restrict_of_subset htΩ hfK)
  have heq : z =ᵐ[volume.restrict (ball (0 : E) t \ closedBall c s)] f := by
    filter_upwards [ae_restrict_mem (measurableSet_ball.diff measurableSet_closedBall)] with x hx
    exact (hfz (notMem_subset ball_subset_closedBall hx.2)).symm
  have hsmall := quadratic_weakGrad_energy_le_on_ball_of_ae_eq_on_complement
    hz hf hK hzK hfK A hA hsub htΩ heq hle
  have hqeq : (∑ j : Fin d, ∫ x in ball c s,
      A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) =
      ∑ j : Fin d, ∫ x in ball c s,
        A (q x) (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_all_iff.mpr hgradfq] with x hx hgrad
    have hG : (WithLp.toLp 2 (fun i => (hf i).weakGrad x j) : F) =
        WithLp.toLp 2 (fun i => (hq i).weakGrad x j) := by
      ext i
      exact congrArg (fun v : E => v j) (hgrad i)
    rw [hfq hx, hG]
  rwa [hqeq] at hsmall

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
