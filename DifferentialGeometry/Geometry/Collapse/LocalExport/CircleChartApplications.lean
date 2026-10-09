import DifferentialGeometry.Geometry.Collapse.LocalExport.CircleChart

/-!
# Consumer of `CircleChart`: the product structure `η⁻¹ B(0, R) ≅ S¹ × B(0, R)`

For an LC83 circle chart on a three-manifold and `0 < R < 100`, the recorded trivialization and the
fibre type combine into a diffeomorphism `S¹ × B(0, R) ≅ η⁻¹ B(0, R)` over `B(0, R)` (the row's
"in particular" clause); applied to the producer `CircleChart.ofLocalModel` this is LC83's product
statement on a complete Riemannian three-manifold.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- LC83 product clause from a circle chart: in dimension three, for `0 < R < 100` there is a
diffeomorphism `S¹ × B(0, R) ≅ η⁻¹ B(0, R)` commuting with the projections to `B(0, R)`. -/
theorem CircleChart.exists_circle_product (c : CircleChart I M) (hdim : Module.finrank ℝ E = 3)
    (R : ℝ) (hR : 0 < R) (hRr : R < 100) :
    let f := diskPreimageMap (ball c.center 200) isOpen_ball c.coord
      c.contMDiffOn_coord.continuousOn 100
    let U : TopologicalSpace.Opens
        (diskPreimageOpens (ball c.center 200) isOpen_ball c.coord
          c.contMDiffOn_coord.continuousOn 100) :=
      ⟨f ⁻¹' planeBallInner 100 R,
        (planeBallInner 100 R).isOpen.preimage (continuous_diskPreimageMap isOpen_ball _ 100)⟩
    ∃ Ψ : Diffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ²)) I (Circle × planeBallInner 100 R) U ∞,
      ∀ q, f (Ψ q).1 = q.2.1 := by
  intro f U
  let := regularFiberChartedSpace f ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
    (contMDiff_diskPreimageMap isOpen_ball c.contMDiffOn_coord 100)
    (fun x _ ↦ surjective_mfderiv_diskPreimageMap isOpen_ball c.contMDiffOn_coord c.rank 100 x)
  obtain ⟨hy, Θ, hΘ, -⟩ := c.trivial R hR hRr
  obtain ⟨e⟩ := c.nonempty_circle_diffeomorph hdim ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
  refine ⟨(Diffeomorph.prodCongr e (Diffeomorph.refl 𝓘(ℝ, ℝ²) (planeBallInner 100 R) ∞)).trans Θ,
    fun q => ?_⟩
  exact hΘ _

end DifferentialGeometry.Geometry.Collapse
