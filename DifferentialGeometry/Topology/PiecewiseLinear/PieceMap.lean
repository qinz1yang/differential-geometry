import DifferentialGeometry.Topology.PiecewiseLinear.Manifold
import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem PLPieceIn.isPLOn_comp {Y : Set X} (T : PLPieceIn E n X Y)
    {f : EuclideanSpace ℝ (Fin m) → E} {P : Set (EuclideanSpace ℝ (Fin m))}
    (hf : IsPiecewiseAffineOn f P) (hmap : MapsTo f P T.complex.space) :
    IsPLOn m n (T.map ∘ f) P := by
  have hcont := T.continuousOn.comp hf.continuousOn hmap
  intro x hx
  apply (StructureGroupoid.liftPropWithinAt_self_source).mpr
  refine ⟨hcont x hx, ?_⟩
  let e := chartAt (EuclideanSpace ℝ (Fin n)) (T.map (f x))
  have hfx : f x ∈ T.complex.space ∩ T.map ⁻¹' e.source :=
    ⟨hmap hx, mem_chart_source _ _⟩
  have hpl := (T.isPiecewiseAffineOn_chart e (chart_mem_atlas _ _) (f x) hfx).comp (hf x hx)
  have hnhds : P ∩ f ⁻¹' (T.complex.space ∩ T.map ⁻¹' e.source) ∈ 𝓝[P] x := by
    have hevent := (hcont x hx).preimage_mem_nhdsWithin
      (e.open_source.mem_nhds (mem_chart_source _ _))
    filter_upwards [self_mem_nhdsWithin, hevent] with y hy hye
    exact ⟨hy, hmap hy, hye⟩
  have hfilter : 𝓝[P] x = 𝓝[P ∩ f ⁻¹' (T.complex.space ∩ T.map ⁻¹' e.source)] x := by
    rw [← nhdsWithin_inter_of_mem' hnhds, inter_eq_right.mpr inter_subset_left]
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hpl
  refine ⟨ι, hι, C, A, fun i =>
    ⟨(hC i).1, (hC i).2.1.trans inter_subset_left, (hC i).2.2⟩, ?_⟩
  rwa [hfilter]

end DifferentialGeometry.Topology.PiecewiseLinear
