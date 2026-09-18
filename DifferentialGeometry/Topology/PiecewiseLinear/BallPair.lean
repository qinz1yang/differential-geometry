import DifferentialGeometry.Topology.PiecewiseLinear.ConePairExtension
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAvoiding
import DifferentialGeometry.Topology.PiecewiseLinear.Gluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsPLBallPair (m k : ℕ) (P Q : Set E) : Prop :=
  ∃ (p : E) (L : Geometry.SimplicialComplex ℝ E) (_ : IsConeBase p L) (f : E → E) (X : Set E),
    L.faces.Finite ∧ X ⊆ L.space ∧ IsPLSphere m L.space ∧ IsPLBall k Q ∧
      IsPLHomeomorphOn f (coneSet p L.space) P ∧ f '' coneSet p X = Q

theorem IsPLBallPair.subset {m k : ℕ} {P Q : Set E} (h : IsPLBallPair m k P Q) : Q ⊆ P := by
  obtain ⟨p, L, -, f, X, -, hXL, -, -, hf, rfl⟩ := h
  rw [← hf.image_eq]
  exact image_mono (coneSet_mono p hXL)

theorem IsPLBallPair.isPLBall_sub {m k : ℕ} {P Q : Set E} (h : IsPLBallPair m k P Q) :
    IsPLBall k Q := by
  obtain ⟨-, -, -, -, -, -, -, -, hball, -, -⟩ := h
  exact hball

theorem IsPLBallPair.isPLBall [FiniteDimensional ℝ E] {m k : ℕ} {P Q : Set E}
    (h : IsPLBallPair m k P Q) : IsPLBall (m + 1) P := by
  classical
  obtain ⟨p, L, hL, f, -, hfin, -, hsph, -, hf, -⟩ := h
  have : Finite L.faces := hfin.to_subtype
  have hcone : IsPLBall (m + 1) (coneSet p L.space) := by
    rw [← coneComplex_space_eq_coneSet hL]
    exact hL.isPLBall_of_isPLSphere hsph
  exact hcone.of_isPLHomeomorphOn hf

theorem IsPLBallPair.of_isPLHomeomorphOn [FiniteDimensional ℝ E] {m k : ℕ} {P Q P' Q' : Set E}
    (h : IsPLBallPair m k P Q) {g : E → E} (hg : IsPLHomeomorphOn g P P') (hgQ : g '' Q = Q') :
    IsPLBallPair m k P' Q' := by
  have hsub := h.subset
  have hQ := h.isPLBall_sub
  obtain ⟨p, L, hL, f, X, hfin, hXL, hsph, -, hf, hfX⟩ := h
  refine ⟨p, L, hL, g ∘ f, X, hfin, hXL, hsph, ?_, hf.trans hg, ?_⟩
  · have hres := hg.restrict hQ.isPolyhedron hsub
    rw [hgQ] at hres
    exact hQ.of_isPLHomeomorphOn hres
  · rw [image_comp, hfX, hgQ]

theorem isPLBallPair_coneSet [FiniteDimensional ℝ E] {m k : ℕ} {p : E}
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L) {X : Set E}
    (hXL : X ⊆ L.space) (hsph : IsPLSphere m L.space) (hball : IsPLBall k (coneSet p X)) :
    IsPLBallPair m k (coneSet p L.space) (coneSet p X) := by
  classical
  have hcfin : Finite (coneComplex hL).faces :=
    (coneComplex_faces_finite hL (Set.toFinite L.faces)).to_subtype
  have hpoly : IsPolyhedron (coneSet p L.space) := by
    rw [← coneComplex_space_eq_coneSet hL]
    exact isPolyhedron_space _
  exact ⟨p, L, hL, id, X, Set.toFinite L.faces, hXL, hsph, hball,
    hpoly.isPLHomeomorphOn_id, Set.image_id _⟩

theorem isPLBallPair_coneSet_of_isPLSphere [FiniteDimensional ℝ E] {m k : ℕ} {p : E}
    {L J : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L)
    (hJL : J.faces ⊆ L.faces) (hsph : IsPLSphere m L.space) (hJsph : IsPLSphere k J.space) :
    IsPLBallPair m (k + 1) (coneSet p L.space) (coneSet p J.space) := by
  classical
  have : Finite J.faces := ((Set.toFinite L.faces).subset hJL).to_subtype
  refine isPLBallPair_coneSet hL (space_mono_of_faces_subset hJL) hsph ?_
  rw [← coneComplex_space_eq_coneSet (hL.of_faces_subset hJL)]
  exact (hL.of_faces_subset hJL).isPLBall_of_isPLSphere hJsph

theorem exists_isPLHomeomorphOn_coneSet_pair [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {p : E} {q : F} {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L)
    {X : Set E} (hXL : X ⊆ L.space) {L' : Geometry.SimplicialComplex ℝ F} [Finite L'.faces]
    (hL' : IsConeBase q L') {f : E → F} (hf : IsPLHomeomorphOn f L.space L'.space) {X' : Set F}
    (hfX : f '' X = X') :
    ∃ g : E → F, IsPLHomeomorphOn g (coneSet p L.space) (coneSet q L'.space) ∧
      EqOn g f L.space ∧ g p = q ∧ g '' coneSet p X = coneSet q X' := by
  classical
  obtain ⟨g, hg, hgf, hgp, -, hpair⟩ := exists_isPLHomeomorphOn_coneComplex_pair hL hL' hf
  rw [coneComplex_space_eq_coneSet hL, coneComplex_space_eq_coneSet hL'] at hg
  exact ⟨g, hg, hgf, hgp, by rw [hpair _ hXL, hfX]⟩

theorem exists_isPLHomeomorphOn_of_isPLSphere_pair [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {m k : ℕ} {p : E} {q : F} {L J : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hL : IsConeBase p L) (hJL : J.faces ⊆ L.faces) (hsph : IsPLSphere m L.space)
    (hJsph : IsPLSphere k J.space) {L' J' : Geometry.SimplicialComplex ℝ F} [Finite L'.faces]
    (hL' : IsConeBase q L') (hJL' : J'.faces ⊆ L'.faces) (hsph' : IsPLSphere m L'.space)
    (hJsph' : IsPLSphere k J'.space) {f : E → F} (hf : IsPLHomeomorphOn f L.space L'.space)
    (hfJ : f '' J.space = J'.space) :
    ∃ g : E → F, IsPLHomeomorphOn g (coneSet p L.space) (coneSet q L'.space) ∧
      EqOn g f L.space ∧ g p = q ∧ g '' coneSet p J.space = coneSet q J'.space ∧
      IsPLBallPair m (k + 1) (coneSet p L.space) (coneSet p J.space) ∧
      IsPLBallPair m (k + 1) (coneSet q L'.space) (coneSet q J'.space) := by
  obtain ⟨g, hg, hgf, hgp, hgJ⟩ :=
    exists_isPLHomeomorphOn_coneSet_pair hL (space_mono_of_faces_subset hJL) hL' hf hfJ
  exact ⟨g, hg, hgf, hgp, hgJ, isPLBallPair_coneSet_of_isPLSphere hL hJL hsph hJsph,
    isPLBallPair_coneSet_of_isPLSphere hL' hJL' hsph' hJsph'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
