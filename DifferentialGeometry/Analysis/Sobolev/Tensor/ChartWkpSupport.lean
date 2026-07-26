import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpLimit
import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartAe

/-!
# Support inheritance for tensor chart-Sobolev limits

Every approximating component in `ChartWkpLimit.lean` contains the canonical
partition-of-unity weight of its chart.  This file proves that the chosen
Euclidean Sobolev limit retains the same compact support almost everywhere.
The argument passes from `wkpNorm` convergence to convergence in measure and
then to an almost-everywhere convergent subsequence, exactly as in the scalar
manifold-completeness construction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- A POU-weighted tensor chart component vanishes pointwise, inside the chart
target, off the fixed Euclidean image of the POU kernel. -/
theorem secComp_zero_kernel
    (r s : ℕ) (S : RSTensorSection I M r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ chartImagePOUTsupport (I := I) (M := M) α) :
    secChartComp (I := I) (M := M) r s S α Idx Jdx y = 0 := by
  rw [secComp_apply_mem (I := I) (M := M) r s S α Idx Jdx hy_target]
  have hzero := chartPushed_eq_zero_off_chartImagePOUTsupport
    (I := I) (M := M) α
    (secCompRaw (I := I) (M := M) r s S α Idx Jdx)
    hy_target hy_off
  exact hzero

/-- The chosen component limit vanishes almost everywhere off the same compact
POU kernel as every member of the approximating sequence. -/
theorem secCompLimit_ae_zero
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secCompLimit (I := I) (M := M) g r s k hp hp_top u
        h_cauchy α Idx Jdx =ᵐ[
      (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)] 0 := by
  have h_v := secCompLimit_tendsto (I := I) (M := M)
    g r s k hp hp_top u h_cauchy α Idx Jdx
  have h_eLp : Tendsto
      (fun n => eLpNorm
        (fun y =>
          secChartComp (I := I) (M := M) r s (u n).1 α Idx Jdx y -
            secCompLimit (I := I) (M := M) g r s k hp hp_top u
              h_cauchy α Idx Jdx y)
        p (volume.restrict (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε_pos
    rw [ENNReal.tendsto_atTop_zero] at h_v
    obtain ⟨N, hN⟩ := h_v ε hε_pos
    refine ⟨N, ?_⟩
    intro n hn
    have h_eLp_le_wkp := eLpNorm_iterWeakPartial_le_wkpNorm
      (d := Module.finrank ℝ E) (k := k) p
      (fun y =>
        secChartComp (I := I) (M := M) r s (u n).1 α Idx Jdx y -
          secCompLimit (I := I) (M := M) g r s k hp hp_top u
            h_cauchy α Idx Jdx y)
      (chartTargetEuclid (I := I) (M := M) α) 0 (Nat.zero_le _) ![]
    rw [iterWeakPartial_zero] at h_eLp_le_wkp
    exact h_eLp_le_wkp.trans (hN n hn)
  have hp_zero : p ≠ 0 := by
    intro h
    rw [h] at hp
    exact absurd hp (by norm_num : ¬ ((1 : ℝ≥0∞) ≤ 0))
  have h_aesm_seq : ∀ n, AEStronglyMeasurable
      (secChartComp (I := I) (M := M) r s (u n).1 α Idx Jdx)
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
    fun n => ((u n).2 α Idx Jdx).memLp.aestronglyMeasurable
  have h_aesm_lim : AEStronglyMeasurable
      (secCompLimit (I := I) (M := M) g r s k hp hp_top u
        h_cauchy α Idx Jdx)
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
    (secCompLimit_mem (I := I) (M := M) g r s k hp hp_top u
      h_cauchy α Idx Jdx).memLp.aestronglyMeasurable
  have h_meas : TendstoInMeasure
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α))
      (fun n => secChartComp (I := I) (M := M)
        r s (u n).1 α Idx Jdx)
      atTop
      (secCompLimit (I := I) (M := M) g r s k hp hp_top u
        h_cauchy α Idx Jdx) :=
    tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top hp_zero hp_top
      h_aesm_seq h_aesm_lim h_eLp
  obtain ⟨ns, _hns, h_ae⟩ := h_meas.exists_seq_tendsto_ae
  have h_off_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet.diff
      (chartImagePOUTsupport_isCompact (I := I) (M := M) α).measurableSet
  have h_ae_off :
      ∀ᵐ y ∂(volume : Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α),
        Tendsto
          (fun i => secChartComp (I := I) (M := M)
            r s (u (ns i)).1 α Idx Jdx y)
          atTop
          (𝓝 (secCompLimit (I := I) (M := M) g r s k hp hp_top u
            h_cauchy α Idx Jdx y)) :=
    h_ae.filter_mono
      (ae_mono (Measure.restrict_mono_set volume Set.diff_subset))
  filter_upwards [h_ae_off, ae_restrict_mem h_off_meas] with y hy_tendsto hy_off
  have hzero : ∀ i, secChartComp (I := I) (M := M)
      r s (u (ns i)).1 α Idx Jdx y = 0 := by
    intro i
    exact secComp_zero_kernel (I := I) (M := M)
      r s (u (ns i)).1 α Idx Jdx hy_off.1 hy_off.2
  exact tendsto_nhds_unique hy_tendsto
    (by simpa only [hzero] using tendsto_const_nhds)

/-- The closed-kernel representative is a.e. equal, on the chart target, to
the chosen Sobolev component limit. -/
theorem secCompRep_ae
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    secCompRep (I := I) (M := M) g r s k hp hp_top u
        h_cauchy α Idx Jdx =ᵐ[
      (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      secCompLimit (I := I) (M := M) g r s k hp hp_top u
        h_cauchy α Idx Jdx := by
  unfold secCompRep
  exact compactRep_ae
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).measurableSet
    (secCompLimit_ae_zero (I := I) (M := M)
      g r s k hp hp_top u h_cauchy α Idx Jdx)

/-- The closed-kernel representative remains in the same scalar Sobolev
space as the chosen component limit. -/
theorem secCompRep_mem
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) k p
      (secCompRep (I := I) (M := M) g r s k hp hp_top u
        h_cauchy α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (secCompRep_ae (I := I) (M := M)
      g r s k hp hp_top u h_cauchy α Idx Jdx)).mpr
    (secCompLimit_mem (I := I) (M := M)
      g r s k hp hp_top u h_cauchy α Idx Jdx)

/-- The original component sequence also converges in `wkpNorm` to the
closed-kernel representative. -/
theorem secCompRep_tendsto
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Tendsto
      (fun n => wkpNorm (d := Module.finrank ℝ E) k p
        (fun y =>
          secChartComp (I := I) (M := M) r s (u n).1 α Idx Jdx y -
            secCompRep (I := I) (M := M) g r s k hp hp_top u
              h_cauchy α Idx Jdx y)
        (chartTargetEuclid (I := I) (M := M) α))
      atTop (𝓝 0) := by
  have heq :
      (fun n => wkpNorm (d := Module.finrank ℝ E) k p
        (fun y =>
          secChartComp (I := I) (M := M) r s (u n).1 α Idx Jdx y -
            secCompRep (I := I) (M := M) g r s k hp hp_top u
              h_cauchy α Idx Jdx y)
        (chartTargetEuclid (I := I) (M := M) α)) =
      (fun n => wkpNorm (d := Module.finrank ℝ E) k p
        (fun y =>
          secChartComp (I := I) (M := M) r s (u n).1 α Idx Jdx y -
            secCompLimit (I := I) (M := M) g r s k hp hp_top u
              h_cauchy α Idx Jdx y)
        (chartTargetEuclid (I := I) (M := M) α)) := by
    funext n
    exact wkpNorm_congr_ae (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α) (by
        filter_upwards [secCompRep_ae (I := I) (M := M)
          g r s k hp hp_top u h_cauchy α Idx Jdx] with y hy
        rw [hy])
  rw [heq]
  exact secCompLimit_tendsto (I := I) (M := M)
    g r s k hp hp_top u h_cauchy α Idx Jdx

/-- The closed-kernel representative has pointwise topological support in the
fixed compact POU image. -/
theorem secCompRep_support
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (secCompRep (I := I) (M := M) g r s k hp hp_top u
      h_cauchy α Idx Jdx) ⊆
      chartImagePOUTsupport (I := I) (M := M) α := by
  unfold secCompRep
  exact compactRep_support
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed _

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
