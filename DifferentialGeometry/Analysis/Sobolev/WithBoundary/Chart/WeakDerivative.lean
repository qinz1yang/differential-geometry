import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart.Banach
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevCauchy
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Module.Completion

noncomputable section

open Manifold MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Integral.Measure

variable {k j : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "hp" => (Fact.out : 1 ≤ p)

private noncomputable def chartIterWeakPartialLpLinear
    (hj : j ≤ k) (α : M) (β : Fin j → Fin n) :
    WkpChart (n := n) (M := M) k p hp →ₗ[ℝ]
      Lp ℝ p (volume.restrict (Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α))) where
  toFun u := (Euclidean.iterWeakPartial_memLp_of_memWkp
    ((wkpChartFun_memWkpChart u α).le_of_le hj) β).toLp
      (Euclidean.iterWeakPartial p j β (chartPushed (chartAtlasPOU I_hs M) α
        (wkpChartFun u)) (Euclidean.interiorHalfSpace (chartTargetEuclid α)))
  map_add' u v := by
    apply Lp.ext
    have hu := MemLp.coeFn_toLp (Euclidean.iterWeakPartial_memLp_of_memWkp
      ((wkpChartFun_memWkpChart u α).le_of_le hj) β)
    have hv := MemLp.coeFn_toLp (Euclidean.iterWeakPartial_memLp_of_memWkp
      ((wkpChartFun_memWkpChart v α).le_of_le hj) β)
    have huv := MemLp.coeFn_toLp (Euclidean.iterWeakPartial_memLp_of_memWkp
      ((wkpChartFun_memWkpChart (u + v) α).le_of_le hj) β)
    have hderiv := Euclidean.iterWeakPartial_add_ae hp
      (Euclidean.interiorHalfSpace_isOpen (chartTargetEuclid_isHalfSpaceRelOpen α)) β
      ((wkpChartFun_memWkpChart u α).le_of_le hj)
      ((wkpChartFun_memWkpChart v α).le_of_le hj)
    have hpush : chartPushed (chartAtlasPOU I_hs M) α (wkpChartFun (u + v)) =
        fun y => chartPushed (chartAtlasPOU I_hs M) α (wkpChartFun u) y +
          chartPushed (chartAtlasPOU I_hs M) α (wkpChartFun v) y :=
      chartPushed_add (chartAtlasPOU I_hs M) α (wkpChartFun u) (wkpChartFun v)
    rw [← hpush] at hderiv
    exact huv.trans (hderiv.trans ((hu.add hv).symm.trans
      (Lp.coeFn_add _ _).symm))
  map_smul' c u := by
    apply Lp.ext
    have hu := MemLp.coeFn_toLp (Euclidean.iterWeakPartial_memLp_of_memWkp
      ((wkpChartFun_memWkpChart u α).le_of_le hj) β)
    have hcu := MemLp.coeFn_toLp (Euclidean.iterWeakPartial_memLp_of_memWkp
      ((wkpChartFun_memWkpChart (c • u) α).le_of_le hj) β)
    have hderiv := Euclidean.iterWeakPartial_const_smul_ae hp
      (Euclidean.interiorHalfSpace_isOpen (chartTargetEuclid_isHalfSpaceRelOpen α)) β
      ((wkpChartFun_memWkpChart u α).le_of_le hj) c
    have hpush : chartPushed (chartAtlasPOU I_hs M) α (wkpChartFun (c • u)) =
        fun y => c * chartPushed (chartAtlasPOU I_hs M) α (wkpChartFun u) y := by
      simpa only [wkpChartFun_smul, smul_eq_mul] using
        chartPushed_const_smul (chartAtlasPOU I_hs M) α c (wkpChartFun u)
    rw [← hpush] at hderiv
    exact hcu.trans (hderiv.trans ((hu.fun_comp (fun x : ℝ => c * x)).symm.trans
      (Lp.coeFn_smul c _).symm))

private theorem norm_chartIterWeakPartialLpLinear_le
    (hj : j ≤ k) (α : M) (β : Fin j → Fin n)
    (u : WkpChart (n := n) (M := M) k p hp) :
    ‖chartIterWeakPartialLpLinear hj α β u‖ ≤ ‖u‖ := by
  rw [chartIterWeakPartialLpLinear, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp,
    norm_wkpChart_def]
  apply ENNReal.toReal_mono (wkpNormChart_lt_top_of_memWkpChart hp
    (wkpChartFun_memWkpChart u)).ne
  exact (Euclidean.eLpNorm_iterWeakPartial_le_wkpNorm p
    (chartPushed (chartAtlasPOU I_hs M) α (wkpChartFun u))
    (Euclidean.interiorHalfSpace (chartTargetEuclid α)) j hj β).trans
      (ENNReal.le_tsum α)

noncomputable def chartIterWeakPartialLp
    (hj : j ≤ k) (α : M) (β : Fin j → Fin n) :
    WkpChart (n := n) (M := M) k p hp →L[ℝ]
      Lp ℝ p (volume.restrict (Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α))) :=
  (chartIterWeakPartialLpLinear hj α β).mkContinuous 1
    (fun u => by simpa only [one_mul] using norm_chartIterWeakPartialLpLinear_le hj α β u)

theorem chartIterWeakPartialLp_apply_coeFn
    (hj : j ≤ k) (α : M) (β : Fin j → Fin n)
    (u : WkpChart (n := n) (M := M) k p hp) :
    (chartIterWeakPartialLp hj α β u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[
      volume.restrict (Euclidean.interiorHalfSpace (chartTargetEuclid α))]
      Euclidean.iterWeakPartial p j β (chartPushed (chartAtlasPOU I_hs M) α
        (wkpChartFun u)) (Euclidean.interiorHalfSpace (chartTargetEuclid α)) :=
  MemLp.coeFn_toLp (Euclidean.iterWeakPartial_memLp_of_memWkp
    ((wkpChartFun_memWkpChart u α).le_of_le hj) β)

theorem norm_chartIterWeakPartialLp_apply_le
    (hj : j ≤ k) (α : M) (β : Fin j → Fin n)
    (u : WkpChart (n := n) (M := M) k p hp) :
    ‖chartIterWeakPartialLp hj α β u‖ ≤ ‖u‖ :=
  norm_chartIterWeakPartialLpLinear_le hj α β u

theorem norm_chartIterWeakPartialLp_le
    (hj : j ≤ k) (α : M) (β : Fin j → Fin n) :
    ‖chartIterWeakPartialLp (n := n) (M := M) (p := p) hj α β‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using norm_chartIterWeakPartialLp_apply_le hj α β u

noncomputable def chartIterWeakPartialComplLp
    (hj : j ≤ k) (α : M) (β : Fin j → Fin n) :
    UniformSpace.Completion (WkpChart (n := n) (M := M) k p hp) →L[ℝ]
      Lp ℝ p (volume.restrict (Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α))) :=
  (chartIterWeakPartialLp hj α β).extend UniformSpace.Completion.toComplL

theorem chartIterWeakPartialComplLp_coe
    (hj : j ≤ k) (α : M) (β : Fin j → Fin n)
    (u : WkpChart (n := n) (M := M) k p hp) :
    chartIterWeakPartialComplLp hj α β
      (u : UniformSpace.Completion (WkpChart (n := n) (M := M) k p hp)) =
      chartIterWeakPartialLp hj α β u := by
  apply ContinuousLinearMap.extend_eq
  · simpa only [UniformSpace.Completion.coe_toComplL] using
      UniformSpace.Completion.denseRange_coe
  · simpa only [UniformSpace.Completion.coe_toComplL] using
      UniformSpace.Completion.isUniformInducing_coe (WkpChart (n := n) (M := M) k p hp)

theorem norm_chartIterWeakPartialComplLp_apply_le
    (hj : j ≤ k) (α : M) (β : Fin j → Fin n)
    (u : UniformSpace.Completion (WkpChart (n := n) (M := M) k p hp)) :
    ‖chartIterWeakPartialComplLp hj α β u‖ ≤ ‖u‖ := by
  refine UniformSpace.Completion.induction_on
    (α := WkpChart (n := n) (M := M) k p hp) u
    (isClosed_le (chartIterWeakPartialComplLp (p := p) hj α β).continuous.norm continuous_norm) ?_
  intro v
  have hv := chartIterWeakPartialComplLp_coe hj α β v
  rw [hv, UniformSpace.Completion.norm_coe]
  exact norm_chartIterWeakPartialLp_apply_le hj α β v

theorem norm_chartIterWeakPartialComplLp_le
    (hj : j ≤ k) (α : M) (β : Fin j → Fin n) :
    ‖chartIterWeakPartialComplLp (n := n) (M := M) (p := p) hj α β‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using norm_chartIterWeakPartialComplLp_apply_le hj α β u

end DifferentialGeometry.Analysis.Sobolev.WithBoundary
