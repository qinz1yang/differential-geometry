import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.LocalDiffeomorph

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

structure BallChart (n : ℕ) (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  chart : PartialDiffeomorph (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I
    (EuclideanSpace ℝ (Fin n)) M ∞
  closedBall_subset_source : Metric.closedBall 0 2 ⊆ chart.source

namespace BallChart

variable {n : ℕ} {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (c : BallChart n I M)

theorem ball_subset_source : Metric.ball 0 1 ⊆ c.chart.source := by
  intro x hx
  apply c.closedBall_subset_source
  change dist x 0 ≤ 2
  exact le_trans (le_of_lt (Metric.mem_ball.mp hx)) (by norm_num)

theorem sphere_subset_source : Metric.sphere 0 1 ⊆ c.chart.source := by
  intro x hx
  apply c.closedBall_subset_source
  change dist x 0 ≤ 2
  rw [Metric.mem_sphere.mp hx]
  norm_num

abbrev Punctured := {x : M // x ∉ c.chart '' Metric.ball 0 1}

def boundaryMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : c.Punctured :=
  ⟨c.chart z, by
    rintro ⟨x, hx, h⟩
    have heq : x = (z : EuclideanSpace ℝ (Fin n)) :=
      c.chart.toPartialEquiv.injOn (c.ball_subset_source hx)
        (c.sphere_subset_source z.2) h
    subst x
    have hz := Metric.mem_sphere.mp z.2
    exact (not_lt_of_ge (le_of_eq hz.symm)) hx⟩

@[simp]
theorem boundaryMap_val (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (c.boundaryMap z : M) = c.chart z := rfl

theorem boundaryMap_injective : Function.Injective c.boundaryMap := by
  intro x y h
  apply Subtype.ext
  exact c.chart.toPartialEquiv.injOn (c.sphere_subset_source x.2)
    (c.sphere_subset_source y.2) (congrArg Subtype.val h)

theorem continuous_boundaryMap : Continuous c.boundaryMap := by
  apply Continuous.subtype_mk
  exact c.chart.contMDiffOn_toFun.continuousOn.comp_continuous
    continuous_subtype_val (fun x => c.sphere_subset_source x.2)

theorem continuous_inclusion : Continuous (Subtype.val : c.Punctured → M) :=
  continuous_subtype_val

theorem inclusion_injective : Function.Injective (Subtype.val : c.Punctured → M) :=
  Subtype.val_injective

theorem isOpen_chart_image_ball : IsOpen (c.chart '' Metric.ball 0 1) := by
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ c.chart.toPartialEquiv.source :=
    c.ball_subset_source
  have hcont : ContinuousOn (⇑c.chart.toPartialEquiv.symm) c.chart.toPartialEquiv.target :=
    c.chart.contMDiffOn_invFun.continuousOn
  have hopen : IsOpen (c.chart.toPartialEquiv.target ∩
      (⇑c.chart.toPartialEquiv.symm) ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    hcont.isOpen_inter_preimage c.chart.open_target
      (Metric.isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1))
  rw [PartialEquiv.image_eq_target_inter_inv_preimage _ hsub]
  exact hopen

theorem isClosed_punctured : IsClosed {x : M | x ∉ c.chart '' Metric.ball 0 1} :=
  c.isOpen_chart_image_ball.isClosed_compl

instance instCompactSpacePunctured [CompactSpace M] : CompactSpace c.Punctured :=
  isCompact_iff_compactSpace.mp c.isClosed_punctured.isCompact

end BallChart

end DifferentialGeometry.Topology
