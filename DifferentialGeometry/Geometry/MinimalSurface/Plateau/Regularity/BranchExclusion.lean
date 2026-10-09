import DifferentialGeometry.Topology.Covering.FiberContact
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientLeadingPlane
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk

set_option autoImplicit false

noncomputable section

open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

/-- A conditional factor of the original disk restriction through its original-metric
leading projection. Contact rigidity is explicit; no rank, replacement disk, or
extension to the full closed disk is asserted. -/
theorem DifferentialGeometry.Geometry.exists_continuous_factor_of_leading_projection_contact_germs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {T : Type*} [TopologicalSpace T] [PathConnectedSpace T]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (ι : C(T, closedDisk)) (S : Set ℂ) (q : C(T, S))
    (hq : IsCoveringMap q) (hsurj : Function.Surjective q)
    (x₀ : T) (hfinite : (q ⁻¹' {q x₀}).Finite)
    (p : M) (b : Fin (Module.finrank ℝ E) → ℂ) (N : E) (lift : ℂ → E)
    (hchart : ∀ z : T, u (ι z) ∈ (chartAt E p).source)
    (hprojection : ∀ z : T,
      (q z : ℂ) = chartLeadingPlaneProjection g p p b
        (extChartAt 𝓘(ℝ, E) p (u (ι z))))
    (hsplit : ∀ v : E,
      v = lift (chartLeadingPlaneProjection g p p b v) + (chartGramBilin g p p N v) • N)
    (hcontact : ∀ x y : T, q x = q y →
      chartGramBilin g p p N (extChartAt 𝓘(ℝ, E) p (u (ι x))) =
        chartGramBilin g p p N (extChartAt 𝓘(ℝ, E) p (u (ι y))) →
      ∀ᶠ xy : T × T in 𝓝 (x, y), q xy.1 = q xy.2 →
        chartGramBilin g p p N (extChartAt 𝓘(ℝ, E) p (u (ι xy.1))) =
          chartGramBilin g p p N (extChartAt 𝓘(ℝ, E) p (u (ι xy.2)))) :
    ∃ v : C(S, M), v.comp q = u.comp ι ∧ Set.range v = Set.range (u.comp ι) := by
  let X : T → E := fun z => extChartAt 𝓘(ℝ, E) p (u (ι z))
  let Q := chartGramBilin g p p
  let H : T → ℝ := fun z => Q N (X z)
  have hX : Continuous X := by
    apply (continuousOn_extChartAt (I := 𝓘(ℝ, E)) p).comp_continuous (u.comp ι).continuous
    intro z
    simpa only [extChartAt_source, ContinuousMap.comp_apply] using hchart z
  have hH : Continuous H := (Q N).continuous.comp hX
  have hheight : Function.FactorsThrough H q :=
    Covering.factorsThrough_of_finite_fiber_of_contact_germs hq x₀ hfinite H hH hcontact
  have hfactor : Function.FactorsThrough (u.comp ι) q := by
    intro x y hxy
    change u (ι x) = u (ι y)
    have hheight_xy : Q N (X x) = Q N (X y) := hheight hxy
    have hXeq : X x = X y := by
      calc
        X x = lift (chartLeadingPlaneProjection g p p b (X x)) + (Q N (X x)) • N :=
          hsplit _
        _ = lift (chartLeadingPlaneProjection g p p b (X y)) + (Q N (X y)) • N := by
          rw [← hprojection x, ← hprojection y, hxy, hheight_xy]
        _ = X y := (hsplit _).symm
    apply (extChartAt 𝓘(ℝ, E) p).injOn
    · simpa only [extChartAt_source] using hchart x
    · simpa only [extChartAt_source] using hchart y
    · exact hXeq
  let hquot : Topology.IsQuotientMap q := hq.isQuotientMap hsurj
  let v : C(S, M) := hquot.lift (u.comp ι) hfactor
  have hcomp : v.comp q = u.comp ι := hquot.lift_comp _ _
  refine ⟨v, hcomp, ?_⟩
  rw [← hcomp]
  exact (hsurj.range_comp v).symm
