import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Collar

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.BallChart

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] (e c d : BallChart 3 (𝓡 3) M)

abbrev TriplePunctured := {x : M // x ∉ e.chart '' Metric.ball 0 1 ∧
  x ∉ c.chart '' Metric.ball 0 1 ∧ x ∉ d.chart '' Metric.ball 0 1}

def tripleToFirst (x : e.TriplePunctured c d) : e.Punctured := ⟨x.val, x.property.1⟩

def tripleToPair (x : e.TriplePunctured c d) : c.DoublePunctured d :=
  ⟨x.val, fun h => h.elim x.property.2.1 x.property.2.2⟩

def firstRestriction : Set e.Punctured :=
  {x | x.val ∉ c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1}

def pairRestriction : Set (c.DoublePunctured d) := {x | x.val ∉ e.chart '' Metric.ball 0 1}

theorem isClosed_firstRestriction : IsClosed (firstRestriction e c d) :=
  (c.isOpen_chart_image_ball.union d.isOpen_chart_image_ball).isClosed_compl.preimage continuous_subtype_val

theorem isClosed_pairRestriction : IsClosed (pairRestriction e c d) :=
  e.isOpen_chart_image_ball.isClosed_compl.preimage continuous_subtype_val

def firstRestrictionHomeomorph : firstRestriction e c d ≃ₜ e.TriplePunctured c d where
  toFun x := ⟨x.val.val, x.val.property, (not_or.mp x.property).1, (not_or.mp x.property).2⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, not_or.mpr x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def pairRestrictionHomeomorph : pairRestriction e c d ≃ₜ e.TriplePunctured c d where
  toFun x := ⟨x.val.val, x.property, (not_or.mp x.val.property).1, (not_or.mp x.val.property).2⟩
  invFun x := ⟨⟨x.val, not_or.mpr x.property.2⟩, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable (hec : Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
  (hed : Disjoint (e.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))

def tripleBoundaryFirst (z : S2) : e.TriplePunctured c d :=
  ⟨e.chart z, (e.boundaryMap z).property, chart_sphere_not_mem_other_ball e c hec z,
    chart_sphere_not_mem_other_ball e d hed z⟩

def tripleBoundarySecond (z : S2) : e.TriplePunctured c d :=
  ⟨c.chart z, chart_sphere_not_mem_other_ball c e hec.symm z, (c.boundaryMap z).property,
    chart_sphere_not_mem_other_ball c d hcd z⟩

def tripleBoundaryThird (z : S2) : e.TriplePunctured c d :=
  ⟨d.chart z, chart_sphere_not_mem_other_ball d e hed.symm z,
    chart_sphere_not_mem_other_ball d c hcd.symm z, (d.boundaryMap z).property⟩

theorem continuous_tripleBoundaryFirst : Continuous (tripleBoundaryFirst e c d hec hed) :=
  (e.chart.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val
    (fun z => e.sphere_subset_source z.property)).subtype_mk _

theorem continuous_tripleBoundarySecond : Continuous (tripleBoundarySecond e c d hec hcd) :=
  (c.chart.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val
    (fun z => c.sphere_subset_source z.property)).subtype_mk _

theorem continuous_tripleBoundaryThird : Continuous (tripleBoundaryThird e c d hed hcd) :=
  (d.chart.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val
    (fun z => d.sphere_subset_source z.property)).subtype_mk _

theorem tripleToFirst_boundaryFirst (z : S2) :
    tripleToFirst e c d (tripleBoundaryFirst e c d hec hed z) = e.boundaryMap z := rfl

theorem tripleToPair_boundarySecond (z : S2) :
    tripleToPair e c d (tripleBoundarySecond e c d hec hcd z) = c.firstBoundaryMap d hcd z := rfl

theorem tripleToPair_boundaryThird (z : S2) :
    tripleToPair e c d (tripleBoundaryThird e c d hed hcd z) = c.secondBoundaryMap d hcd z := rfl

end DifferentialGeometry.Topology.BallChart
