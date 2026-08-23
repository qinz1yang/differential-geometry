import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace DifferentialGeometry.Integral.L2

private theorem euclidean_weighted_norm_sq {ι : Type*} (K : Finset ι)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (v : ℝ → ι → ℝ) (t : ℝ) :
    ‖(WithLp.toLp 2 (fun i : K => Real.sqrt (w i) * v t i) :
        EuclideanSpace ℝ K)‖ ^ 2 =
      ∑ i : K, w i * (v t i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.norm_eq_abs, sq_abs]
  rw [mul_pow, Real.sq_sqrt (hw i)]

theorem integral_fatou_sq_mass {ι : Type*}
    (S : ℕ → Finset ι) (hS : Tendsto S atTop atTop)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v : ℕ → ℝ → ι → ℝ) (vlim : ℝ → ι → ℝ)
    {T : ℝ}
    (hcont : ∀ N i, ContinuousOn (fun t => v N t i) (Icc (0 : ℝ) T))
    (hconv : ∀ i t, t ∈ Icc (0 : ℝ) T →
      Tendsto (fun N => v N t i) atTop (𝓝 (vlim t i)))
    (B : ℝ)
    (hbound : ∀ N, ∫ t, ∑ i ∈ S N, w i * (v N t i) ^ 2
      ∂(volume.restrict (Icc (0 : ℝ) T)) ≤ B) :
    Summable (fun i => w i * ∫ t, (vlim t i) ^ 2
      ∂(volume.restrict (Icc (0 : ℝ) T))) ∧
      ∑' i, w i * ∫ t, (vlim t i) ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) T)) ≤ B := by
  have hB : 0 ≤ B := by
    refine (integral_nonneg fun t => ?_).trans (hbound 0)
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have hpartial : ∀ K : Finset ι,
      ∑ i ∈ K, w i * ∫ t, (vlim t i) ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) T)) ≤ B := by
    intro K
    let fN : ℕ → ℝ → EuclideanSpace ℝ K := fun N t =>
      WithLp.toLp 2 (fun i : K => Real.sqrt (w i) * v N t i)
    let f : ℝ → EuclideanSpace ℝ K := fun t =>
      WithLp.toLp 2 (fun i : K => Real.sqrt (w i) * vlim t i)
    have hfNcont : ∀ N, ContinuousOn (fN N) (Icc (0 : ℝ) T) := by
      intro N
      apply (PiLp.continuous_toLp 2 _).comp_continuousOn
      rw [continuousOn_pi]
      exact fun i => continuousOn_const.mul (hcont N i)
    have hfNmeas : ∀ N,
        AEStronglyMeasurable (fN N) (volume.restrict (Icc (0 : ℝ) T)) := by
      intro N
      exact (hfNcont N).aestronglyMeasurable measurableSet_Icc
    have hlim : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
        Tendsto (fun N => fN N t) atTop (𝓝 (f t)) := by
      filter_upwards [ae_restrict_mem (μ := volume)
        (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) T))] with t ht
      apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
      rw [tendsto_pi_nhds]
      exact fun i => tendsto_const_nhds.mul (hconv i t ht)
    have hfmeas : AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) T)) :=
      aestronglyMeasurable_of_tendsto_ae atTop hfNmeas hlim
    have hfNmem : ∀ N, MemLp (fN N) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
      intro N
      rw [memLp_two_iff_integrable_sq_norm (hfNmeas N)]
      exact ((hfNcont N).norm.pow 2).integrableOn_Icc
    have hevent : ∀ᶠ N in atTop, K ⊆ S N := hS.eventually_ge_atTop K
    have heLp : ∀ᶠ N in atTop,
        eLpNorm (fN N) 2 (volume.restrict (Icc (0 : ℝ) T)) ≤
          ENNReal.ofReal (Real.sqrt B) := by
      filter_upwards [hevent] with N hKN
      have hpartialN : ∫ t, ‖fN N t‖ ^ 2
          ∂(volume.restrict (Icc (0 : ℝ) T)) ≤ B := by
        have hleft : ∫ t, ‖fN N t‖ ^ 2 ∂(volume.restrict (Icc (0 : ℝ) T)) =
            ∫ t, ∑ i ∈ K, w i * (v N t i) ^ 2
              ∂(volume.restrict (Icc (0 : ℝ) T)) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun t => by
            calc
              ‖fN N t‖ ^ 2 = ∑ i : K, w i * (v N t i) ^ 2 :=
                euclidean_weighted_norm_sq K w hw (v N) t
              _ = ∑ i ∈ K, w i * (v N t i) ^ 2 :=
                (Finset.sum_subtype K (fun _ => Iff.rfl)
                  (fun i => w i * (v N t i) ^ 2)).symm
        rw [hleft]
        refine (integral_mono_ae ?_ ?_ ?_).trans (hbound N)
        · exact (continuousOn_finset_sum K fun i _ =>
            (continuousOn_const.mul ((hcont N i).pow 2))).integrableOn_Icc
        · exact (continuousOn_finset_sum (S N) fun i _ =>
            (continuousOn_const.mul ((hcont N i).pow 2))).integrableOn_Icc
        · exact Filter.Eventually.of_forall fun t =>
            Finset.sum_le_sum_of_subset_of_nonneg hKN
              (fun i _ _ => mul_nonneg (hw i) (sq_nonneg _))
      rw [(hfNmem N).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      norm_num [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt hpartialN
    have hflp : eLpNorm f 2 (volume.restrict (Icc (0 : ℝ) T)) ≤
        ENNReal.ofReal (Real.sqrt B) :=
      Lp.eLpNorm_le_of_ae_tendsto heLp hfNmeas hlim
    have hfmem : MemLp f 2 (volume.restrict (Icc (0 : ℝ) T)) := by
      refine ⟨hfmeas, ?_⟩
      exact hflp.trans_lt (by simp)
    have hnormint : ∫ t, ‖f t‖ ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) T)) ≤ B := by
      rw [(hfmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num))] at hflp
      norm_num [← Real.sqrt_eq_rpow] at hflp
      have hsqrt : Real.sqrt (∫ t, ‖f t‖ ^ 2
          ∂(volume.restrict (Icc (0 : ℝ) T))) ≤ Real.sqrt B := by
        exact hflp
      exact (Real.sqrt_le_sqrt_iff hB).mp hsqrt
    calc
      ∑ i ∈ K, w i * ∫ t, (vlim t i) ^ 2
          ∂(volume.restrict (Icc (0 : ℝ) T)) =
          ∑ i ∈ K, ∫ t, w i * (vlim t i) ^ 2
            ∂(volume.restrict (Icc (0 : ℝ) T)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [integral_const_mul]
      _ = ∫ t, ∑ i ∈ K, w i * (vlim t i) ^ 2
          ∂(volume.restrict (Icc (0 : ℝ) T)) := by
        rw [integral_finset_sum K]
        intro i hi
        have hiLp : MemLp (fun t => f t ⟨i, hi⟩) 2
            (volume.restrict (Icc (0 : ℝ) T)) := by
          apply MemLp.of_le hfmem
          · exact (EuclideanSpace.proj ⟨i, hi⟩).continuous.comp_aestronglyMeasurable hfmem.1
          · exact Filter.Eventually.of_forall fun t => PiLp.norm_apply_le (f t) ⟨i, hi⟩
        refine hiLp.integrable_sq.congr (Filter.Eventually.of_forall fun t => ?_)
        dsimp [f]
        rw [mul_pow, Real.sq_sqrt (hw i)]
      _ = ∫ t, ‖f t‖ ^ 2 ∂(volume.restrict (Icc (0 : ℝ) T)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => by
          calc
            ∑ i ∈ K, w i * (vlim t i) ^ 2 =
                ∑ i : K, w i * (vlim t i) ^ 2 :=
              Finset.sum_subtype K (fun _ => Iff.rfl)
                (fun i => w i * (vlim t i) ^ 2)
            _ = ‖f t‖ ^ 2 := (euclidean_weighted_norm_sq K w hw vlim t).symm
      _ ≤ B := hnormint
  have hnn : ∀ i, 0 ≤ w i * ∫ t, (vlim t i) ^ 2
      ∂(volume.restrict (Icc (0 : ℝ) T)) := by
    intro i
    exact mul_nonneg (hw i) (integral_nonneg fun _ => sq_nonneg _)
  exact ⟨summable_of_sum_le hnn hpartial, Real.tsum_le_of_sum_le hnn hpartial⟩

end DifferentialGeometry.Integral.L2

end
