import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianRegularPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
structure Section34MeridianPosition
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    (f : E × ℝ → F) (r : ℝ) (J : Set F) : Prop where
  circle : IsPLSphere 1 J
  boundary : J ⊆ (boundaryComplex 3 M).space
  volumeNull : (⟨inclusion (boundary.trans (boundaryComplex_space_subset 3 M)),
    continuous_inclusion _⟩ : C(J, M.space)).Nullhomotopic
  boundaryEssential : ¬ (⟨inclusion boundary, continuous_inclusion boundary⟩ :
    C(J, (boundaryComplex 3 M).space)).Nullhomotopic
  traceFinite : (J ∩ f '' (D.space ×ˢ {r})).Finite
  heightSides : ∀ x ∈ D.space, f (x, r) ∈ J →
    (x, r) ∈ closure (((D.space ×ˢ Icc (1 / 4) (3 / 4)) ∩ f ⁻¹' J) ∩ {y | y.2 < r}) ∧
    (x, r) ∈ closure (((D.space ×ˢ Icc (1 / 4) (3 / 4)) ∩ f ⁻¹' J) ∩ {y | r < y.2})
  axisCharts : ∀ y ∈ J ∩ f '' ((boundaryComplex 2 D).space ×ˢ {r}),
    ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) (boundaryComplex 3 M).space) (ε : ℝ),
      0 < ε ∧ (e (0, 0) : F) = y ∧ Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
      ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε,
        ((e p : F) ∈ J ↔ p.1 = 0) ∧
        ((e p : F) ∈ f '' ((boundaryComplex 2 D).space ×ˢ {r}) ↔ p.2 = 0)

open Classical in
theorem IsCylindricalDiagram.exists_meridian_position
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    (hdim : Module.finrank ℝ F = 3) {J : Set F} (hJ : IsPLSphere 1 J)
    (hJB : J ⊆ (boundaryComplex 3 M).space)
    (hnull : (⟨inclusion (hJB.trans (boundaryComplex_space_subset 3 M)),
      continuous_inclusion _⟩ : C(J, M.space)).Nullhomotopic)
    (hess : ¬ (⟨inclusion hJB, continuous_inclusion hJB⟩ :
      C(J, (boundaryComplex 3 M).space)).Nullhomotopic) :
    ∃ r ∈ Ioo (1 / 4 : ℝ) (3 / 4), Section34MeridianPosition D M f r J := by
  obtain ⟨r, hr, hfinite, hsides, haxes⟩ :=
    hf.exists_regular_meridian_position D M hD hM hends hdim hJ hJB
  exact ⟨r, hr, hJ, hJB, hnull, hess, hfinite, hsides, haxes⟩

end DifferentialGeometry.Topology.PiecewiseLinear
