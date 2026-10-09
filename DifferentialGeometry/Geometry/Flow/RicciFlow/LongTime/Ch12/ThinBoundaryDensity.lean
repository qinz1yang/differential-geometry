import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryNaturality

/-!
# CH12 C4 (G1): the positive-height points are dense in the cusp domain
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology TopologicalSpace DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

def cuspDomainOpens_C4 : Opens CuspHalfSpace := ⟨cuspDomain, isOpen_cuspDomain_C4⟩

def halfPt_C4 (a : ℝ) : EuclideanHalfSpace 1 := halfPoint (max 0 a) (le_max_left _ _)

theorem halfPt_val_C4 (a : ℝ) : (halfPt_C4 a).val 0 = max 0 a := rfl

theorem continuous_halfPt_C4 : Continuous halfPt_C4 := by
  apply Continuous.subtype_mk
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_const.max continuous_id)

theorem halfPt_self_C4 (q : EuclideanHalfSpace 1) : halfPt_C4 (q.val 0) = q := by
  apply Subtype.ext
  ext i
  fin_cases i
  show max 0 (q.val 0) = q.val 0
  exact max_eq_right q.property

theorem dense_interior_cuspDomain_C4 (x : cuspDomainOpens_C4) :
    x ∈ closure {y : cuspDomainOpens_C4 | 0 < (y : CuspHalfSpace).2.val 0} := by
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  let s : ℝ := (x : CuspHalfSpace).2.val 0
  have hs0 : 0 ≤ s := (x : CuspHalfSpace).2.property
  have hs1 : s < 100 := x.2
  let c : ℝ → CuspHalfSpace := fun r => ((x : CuspHalfSpace).1, halfPt_C4 (s + r * (100 - s) / 2))
  have hc : Continuous c :=
    continuous_const.prodMk (continuous_halfPt_C4.comp (by fun_prop))
  have hc0 : c 0 = (x : CuspHalfSpace) := by
    refine Prod.ext rfl ?_
    have : s + 0 * (100 - s) / 2 = (x : CuspHalfSpace).2.val 0 := by simp [s]
    show halfPt_C4 (s + 0 * (100 - s) / 2) = _
    rw [this, halfPt_self_C4]
  have ht : Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 (x : CuspHalfSpace)) := by
    rw [← hc0]
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr
  have h1 : 0 < s + r * (100 - s) / 2 := by nlinarith [hr.1]
  have h2 : s + r * (100 - s) / 2 < 100 := by nlinarith [hr.2]
  have hz : (c r).2.val 0 = s + r * (100 - s) / 2 := by
    show max 0 (s + r * (100 - s) / 2) = _
    exact max_eq_right h1.le
  refine ⟨⟨c r, by change (c r).2.val 0 < 100; rw [hz]; exact h2⟩, ?_, rfl⟩
  show 0 < (c r).2.val 0
  rw [hz]; exact h1

end GC.LongTime.Ch12
