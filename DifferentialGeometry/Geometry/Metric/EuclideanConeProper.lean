import DifferentialGeometry.Geometry.Metric.EuclideanCone
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set Metric Filter Topology
open scoped NNReal

namespace Metric.EuclideanCone

variable {Y : Type*} [MetricSpace Y]

theorem continuous_mk : Continuous (fun x : ℝ≥0 × Y => mk x.1 x.2) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hc : Continuous (fun z : ℝ≥0 × Y => ((z.1 : ℝ), z.2)) :=
    (NNReal.continuous_coe.comp continuous_fst).prodMk continuous_snd
  have hpairs : Tendsto
      (fun z : ℝ≥0 × Y => (((z.1 : ℝ), z.2), ((x.1 : ℝ), x.2)))
      (𝓝 x) (𝓝 (((x.1 : ℝ), x.2), ((x.1 : ℝ), x.2))) :=
    hc.continuousAt.tendsto.prodMk_nhds tendsto_const_nhds
  have ht := continuous_coneDistance.continuousAt.tendsto.comp hpairs
  simpa only [Function.comp_def, coneDistance_self, dist_mk] using ht

theorem isCompact_closedBall_tip [CompactSpace Y] (R : ℝ) :
    IsCompact (closedBall (tip : EuclideanCone Y) R) := by
  by_cases hR : 0 ≤ R
  · let f : Icc (0 : ℝ) R × Y → EuclideanCone Y :=
      fun z => mk ⟨z.1.val, z.1.property.1⟩ z.2
    have hc : Continuous (fun z : Icc (0 : ℝ) R × Y =>
        ((⟨z.1.val, z.1.property.1⟩ : ℝ≥0), z.2)) :=
      ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
    have hf : Continuous f := continuous_mk.comp hc
    apply ((isCompact_range hf).insert tip).of_isClosed_subset isClosed_closedBall
    intro x hx
    rcases eq_tip_or_eq_mk x with rfl | ⟨r, u, _, rfl⟩
    · exact mem_insert _ _
    · have hr : (r : ℝ) ≤ R := by
        change dist (mk r u) tip ≤ R at hx
        simpa only [dist_tip, radius_mk] using hx
      exact mem_insert_of_mem _ ⟨(⟨(r : ℝ), ⟨r.property, hr⟩⟩, u), rfl⟩
  · rw [closedBall_of_neg (lt_of_not_ge hR)]
    exact isCompact_empty

instance properSpace [CompactSpace Y] : ProperSpace (EuclideanCone Y) :=
  ProperSpace.of_seq_closedBall (x := tip) (r := fun R : ℝ => R) tendsto_id
    (Eventually.of_forall isCompact_closedBall_tip)

end Metric.EuclideanCone
