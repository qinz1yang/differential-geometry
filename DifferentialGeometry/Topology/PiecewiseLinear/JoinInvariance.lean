import DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.JoinStandard
import DifferentialGeometry.Topology.PiecewiseLinear.JoinTransport
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E E' F F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

theorem exists_isPLHomeomorphOn_joinComplex [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ F'] [DecidableEq E] [DecidableEq E']
    [DecidableEq F] [DecidableEq F'] {K₁ : Geometry.SimplicialComplex ℝ E} [Finite K₁.faces]
    {K₂ : Geometry.SimplicialComplex ℝ E'} [Finite K₂.faces]
    {L₁ : Geometry.SimplicialComplex ℝ F} [Finite L₁.faces]
    {L₂ : Geometry.SimplicialComplex ℝ F'} [Finite L₂.faces] {f : E → E'}
    (hf : IsPLHomeomorphOn f K₁.space K₂.space) {g : F → F'}
    (hg : IsPLHomeomorphOn g L₁.space L₂.space) :
    ∃ h : E × F × ℝ → E' × F' × ℝ,
      IsPLHomeomorphOn h (joinComplex K₁ L₁).space (joinComplex K₂ L₂).space := by
  obtain ⟨K₁', K₂', _, hKsub₁, hKfin₁, hKsub₂, hKfin₂, hKiso, -⟩ :=
    exists_isGlueIso_of_isPLHomeomorphOn K₁ K₂ hf
  obtain ⟨L₁', L₂', _, hLsub₁, hLfin₁, hLsub₂, hLfin₂, hLiso, -⟩ :=
    exists_isGlueIso_of_isPLHomeomorphOn L₁ L₂ hg
  have hK₁' : Finite K₁'.faces := hKfin₁.to_subtype
  have hK₂' : Finite K₂'.faces := hKfin₂.to_subtype
  have hL₁' : Finite L₁'.faces := hLfin₁.to_subtype
  have hL₂' : Finite L₂'.faces := hLfin₂.to_subtype
  have hJ₁ : Finite (joinComplex K₁' L₁').faces := (joinComplex_faces_finite K₁' L₁').to_subtype
  have hJ₂ : Finite (joinComplex K₂' L₂').faces := (joinComplex_faces_finite K₂' L₂').to_subtype
  refine ⟨simplicialMap (joinComplex K₁' L₁') (joinVertexMap f g), ?_⟩
  rw [← (hKsub₁.joinComplex hLsub₁).space_eq, ← (hKsub₂.joinComplex hLsub₂).space_eq]
  exact (hKiso.joinComplex hLiso).isPLHomeomorphOn

theorem exists_simplexComplex_isPLBall (b : ℕ) :
    ∃ (T : Finset (Fin (b + 2) → ℝ)) (hT : AffineIndependent ℝ ((↑) : T → (Fin (b + 2) → ℝ))),
      T.card = b + 1 ∧ IsPLBall b (simplexComplex T hT).space := by
  obtain ⟨v, hv⟩ : (stdVertices b).Nonempty :=
    Finset.card_pos.mp (by rw [card_stdVertices]; omega)
  have hcard : ((stdVertices b).erase v).card = b + 1 := by
    rw [Finset.card_erase_of_mem hv, card_stdVertices]
    omega
  have hne : ((stdVertices b).erase v).Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hindep : AffineIndependent ℝ ((↑) : ((stdVertices b).erase v) → (Fin (b + 2) → ℝ)) :=
    affineIndependent_of_subset (stdVertices_affineIndependent b) (Finset.erase_subset v _)
  refine ⟨(stdVertices b).erase v, hindep, hcard, ?_⟩
  rw [simplexComplex_space _ _ hne]
  exact isPLBall_convexHull_of_affineIndependent _ hindep hcard

theorem exists_isPLHomeomorphOn_simplexBoundary_stdVertices [FiniteDimensional ℝ E] {n : ℕ}
    {P : Set E} (h : IsPLSphere n P) :
    ∃ f : (Fin (n + 2) → ℝ) → E, IsPLHomeomorphOn f
      (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space P := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := isPLSphere_simplexBoundary_std n
  exact ⟨f ∘ Function.invFunOn g (stdSimplexBoundary (n + 1)), hg.symm.trans hf⟩

theorem exists_isPLHomeomorphOn_simplexComplex [FiniteDimensional ℝ E] {n : ℕ} {P : Set E}
    (h : IsPLBall n P) :
    ∃ (T : Finset (Fin (n + 2) → ℝ)) (hT : AffineIndependent ℝ ((↑) : T → (Fin (n + 2) → ℝ)))
      (f : (Fin (n + 2) → ℝ) → E), T.card = n + 1 ∧
        IsPLHomeomorphOn f (simplexComplex T hT).space P := by
  obtain ⟨T, hT, hcard, hball⟩ := exists_simplexComplex_isPLBall n
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := hball
  exact ⟨T, hT, f ∘ Function.invFunOn g (stdSimplex ℝ (Fin (n + 1))), hcard, hg.symm.trans hf⟩

theorem isPLSphere_joinComplex_of_isPLSphere [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [DecidableEq E] [DecidableEq F] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} [Finite L.faces] {a b : ℕ} (hK : IsPLSphere a K.space)
    (hL : IsPLSphere b L.space) : IsPLSphere (a + b + 1) (joinComplex K L).space := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_simplexBoundary_stdVertices hK
  obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_simplexBoundary_stdVertices hL
  have hfinA : Finite (simplexBoundary (stdVertices a) (stdVertices_affineIndependent a)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hfinB : Finite (simplexBoundary (stdVertices b) (stdVertices_affineIndependent b)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  obtain ⟨h, hh⟩ := exists_isPLHomeomorphOn_joinComplex hf hg
  exact (isPLSphere_joinComplex_simplexBoundary_simplexBoundary
    (stdVertices_affineIndependent a) (stdVertices_affineIndependent b) (card_stdVertices a)
    (card_stdVertices b)).of_isPLHomeomorphOn hh

theorem isPLBall_joinComplex_of_isPLSphere_of_isPLBall [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [DecidableEq E] [DecidableEq F]
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {L : Geometry.SimplicialComplex ℝ F} [Finite L.faces] {a b : ℕ} (hK : IsPLSphere a K.space)
    (hL : IsPLBall b L.space) : IsPLBall (a + b + 1) (joinComplex K L).space := by
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_simplexBoundary_stdVertices hK
  obtain ⟨T, hT, g, hTcard, hg⟩ := exists_isPLHomeomorphOn_simplexComplex hL
  have hfinA : Finite (simplexBoundary (stdVertices a) (stdVertices_affineIndependent a)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hfinB : Finite (simplexComplex T hT).faces := (simplexComplex_faces_finite T hT).to_subtype
  obtain ⟨h, hh⟩ := exists_isPLHomeomorphOn_joinComplex hf hg
  exact (isPLBall_joinComplex_simplexBoundary_simplexComplex
    (stdVertices_affineIndependent a) hT (card_stdVertices a) hTcard).of_isPLHomeomorphOn hh

end DifferentialGeometry.Topology.PiecewiseLinear
