import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenCoreEnd
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenCoreStretch
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

variable {H : FiniteVolumeHyperbolicModel.{u}} {T : HyperbolicTruncation H}
  {i : Fin T.count} (E : CuspEndChart_CX1 T i)

def compressPair_CX1 (q : Torus × ℝ) : Torus × ℝ :=
  (q.1, compressHeight_CX1 E.radius_pos q.2)

theorem compressPair_source_CX1 {q : Torus × ℝ} (hq : q ∈ E.chart.source) :
    compressPair_CX1 E q ∈ E.chart.source := by
  rw [E.source_eq] at hq ⊢
  exact ⟨trivial, (compressHeight_lower_CX1 E.radius_pos q.2).mpr hq.2⟩

theorem compressPair_injective_CX1 : Injective (compressPair_CX1 E) := by
  intro p q hpq
  apply Prod.ext
  · have h := congrArg (fun z : Torus × ℝ => z.1) hpq
    exact h
  · exact compressHeight_injective_CX1 E.radius_pos (congrArg Prod.snd hpq)

theorem compressPair_local_CX1 :
    IsLocalDiffeomorph signedCollarModel signedCollarModel ∞ (compressPair_CX1 E) :=
  (Diffeomorph.refl torusModel Torus ∞).isLocalDiffeomorph.prodMap
    (compressHeight_local_CX1 E.radius_pos)

/-- Compress one whole end into its negative collar and fix the complement. -/
def endCompression_CX1 (x : H.Carrier) : H.Carrier :=
  open Classical in
  if x ∈ E.chart.target then E.chart (compressPair_CX1 E (E.chart.symm x)) else x

theorem endCompression_on_CX1 {x : H.Carrier} (hx : x ∈ E.chart.target) :
    endCompression_CX1 E x = E.chart (compressPair_CX1 E (E.chart.symm x)) := by
  classical
  exact ite_eq_left hx

theorem endCompression_off_CX1 {x : H.Carrier} (hx : x ∉ E.chart.target) :
    endCompression_CX1 E x = x := by
  classical
  exact ite_eq_right hx

theorem endCompression_target_CX1 {x : H.Carrier} (hx : x ∈ E.chart.target) :
    endCompression_CX1 E x ∈ E.chart.target := by
  rw [endCompression_on_CX1 E hx]
  exact E.chart.map_source (compressPair_source_CX1 E (E.chart.map_target hx))

theorem endCompression_core_CX1 {x : H.Carrier} (hx : x ∈ E.chart.target) :
    endCompression_CX1 E x ∈ T.inclusion '' (T.core.interior : Set T.core.Carrier) := by
  rw [endCompression_on_CX1 E hx]
  exact (E.in_core _ (compressPair_source_CX1 E (E.chart.map_target hx))).mpr
    (compressHeight_lt_zero_CX1 E.radius_pos _)

theorem endCompression_fixed_CX1 {x : H.Carrier} (hx : x ∉ E.support) :
    endCompression_CX1 E x = x := by
  by_cases hxt : x ∈ E.chart.target
  · have hs := E.chart.map_target hxt
    have hheight : (E.chart.symm x).2 < -(3 * E.radius / 4) := by
      by_contra h
      exact hx (E.large_heights ⟨E.chart.symm x, ⟨trivial, le_of_not_gt h⟩,
        E.chart.right_inv' hxt⟩)
    rw [endCompression_on_CX1 E hxt]
    have hc : compressPair_CX1 E (E.chart.symm x) = E.chart.symm x := by
      refine Prod.ext rfl ?_
      exact compressHeight_fixed_CX1 E.radius_pos (by linarith [E.radius_pos])
    rw [hc]
    exact E.chart.right_inv' hxt
  · exact endCompression_off_CX1 E hxt

theorem endCompression_local_CX1 :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (endCompression_CX1 E) := by
  intro x
  by_cases hx : x ∈ E.chart.target
  · have hc := (E.chart.symm.isLocalDiffeomorphAt (𝓡 3) signedCollarModel ∞ hx).comp
      signedCollarModel (Torus × ℝ) (compressPair_local_CX1 E (E.chart.symm x))
    have hf := hc.comp (𝓡 3) H.Carrier
      (E.chart.isLocalDiffeomorphAt signedCollarModel (𝓡 3) ∞
        (compressPair_source_CX1 E (E.chart.map_target hx)))
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _ hf
    filter_upwards [E.chart.open_target.mem_nhds hx] with y hy
    exact endCompression_on_CX1 E hy
  · have hxK : x ∉ E.support := fun h => hx (E.support_subset h)
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _
      ((Diffeomorph.refl (𝓡 3) H.Carrier ∞).isLocalDiffeomorph x)
    filter_upwards [E.support_closed.isOpen_compl.mem_nhds hxK] with y hy
    exact endCompression_fixed_CX1 E hy

theorem endCompression_injective_CX1 : InjOn (endCompression_CX1 E) E.chart.target := by
  intro x hx y hy hxy
  rw [endCompression_on_CX1 E hx, endCompression_on_CX1 E hy] at hxy
  have he := E.chart.toPartialEquiv.injOn
    (compressPair_source_CX1 E (E.chart.map_target hx))
    (compressPair_source_CX1 E (E.chart.map_target hy)) hxy
  have hq := compressPair_injective_CX1 E he
  exact (E.chart.right_inv' hx).symm.trans ((congrArg E.chart hq).trans (E.chart.right_inv' hy))

theorem endCompression_surjective_core_CX1 {y : H.Carrier} (hy : y ∈ E.chart.target)
    (hyc : y ∈ T.inclusion '' (T.core.interior : Set T.core.Carrier)) :
    ∃ x ∈ E.chart.target, endCompression_CX1 E x = y := by
  let q := E.chart.symm y
  have hqs : q ∈ E.chart.source := E.chart.map_target hy
  have hqneg : q.2 < 0 := (E.in_core q hqs).mp ((E.chart.right_inv' hy).symm ▸ hyc)
  have hqlower : -E.radius < q.2 := by rw [E.source_eq] at hqs; exact hqs.2
  obtain ⟨s, hs, hcs⟩ := compressHeight_surjective_negative_CX1 E.radius_pos hqneg hqlower
  have hps : (q.1, s) ∈ E.chart.source := by rw [E.source_eq]; exact ⟨trivial, hs⟩
  refine ⟨E.chart (q.1, s), E.chart.map_source hps, ?_⟩
  rw [endCompression_on_CX1 E (E.chart.map_source hps)]
  have hleft : E.chart.symm (E.chart (q.1, s)) = (q.1, s) := E.chart.left_inv' hps
  rw [hleft]
  have hpq : compressPair_CX1 E (q.1, s) = q := Prod.ext rfl hcs
  rw [hpq]
  exact E.chart.right_inv' hy

theorem cusp_range_subset_chart_CX1 : range (T.cuspMap i) ⊆ E.chart.target := by
  rintro _ ⟨q, rfl⟩
  have hs : (q.1, q.2.val 0) ∈ E.chart.source := by
    rw [E.source_eq]
    exact ⟨trivial, (neg_lt_zero.mpr E.radius_pos).trans_le q.2.property⟩
  have he : E.chart (q.1, q.2.val 0) = T.cuspMap i q := by
    rw [E.on_cusp _ q.2.property]
    congr 1
    refine Prod.ext rfl ?_
    apply Subtype.ext
    ext j
    rw [Subsingleton.elim j 0]
    exact max_eq_left q.2.property
  exact he ▸ E.chart.map_source hs

end GC.LongTime.Ch12
