import DifferentialGeometry.Topology.PiecewiseLinear.ConePairExtension
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAvoiding
import DifferentialGeometry.Topology.PiecewiseLinear.Gluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsPLBallPair (m k : ℕ) (P Q : Set E) : Prop :=
  ∃ (p : E) (L J : Geometry.SimplicialComplex ℝ E) (_ : IsConeBase p L) (f : E → E),
    L.faces.Finite ∧ J.faces ⊆ L.faces ∧ IsPLSphere m L.space ∧ IsPLBall k Q ∧
      IsPLHomeomorphOn f (coneSet p L.space) P ∧ f '' coneSet p J.space = Q

theorem IsPLBallPair.subset {m k : ℕ} {P Q : Set E} (h : IsPLBallPair m k P Q) : Q ⊆ P := by
  obtain ⟨p, L, J, -, f, -, hJL, -, -, hf, rfl⟩ := h
  rw [← hf.image_eq]
  exact image_mono (coneSet_mono p (space_mono_of_faces_subset hJL))

theorem IsPLBallPair.isPLBall_sub {m k : ℕ} {P Q : Set E} (h : IsPLBallPair m k P Q) :
    IsPLBall k Q := by
  obtain ⟨-, -, -, -, -, -, -, -, hball, -, -⟩ := h
  exact hball

theorem IsPLBallPair.isPLBall [FiniteDimensional ℝ E] {m k : ℕ} {P Q : Set E}
    (h : IsPLBallPair m k P Q) : IsPLBall (m + 1) P := by
  classical
  obtain ⟨p, L, J, hL, f, hfin, -, hsph, -, hf, -⟩ := h
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
  obtain ⟨p, L, J, hL, f, hfin, hJL, hsph, -, hf, hfJ⟩ := h
  refine ⟨p, L, J, hL, g ∘ f, hfin, hJL, hsph, ?_, hf.trans hg, ?_⟩
  · have hres := hg.restrict hQ.isPolyhedron hsub
    rw [hgQ] at hres
    exact hQ.of_isPLHomeomorphOn hres
  · rw [image_comp, hfJ, hgQ]

theorem isPLBallPair_coneSet [FiniteDimensional ℝ E] {m k : ℕ} {p : E}
    {L J : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L)
    (hJL : J.faces ⊆ L.faces) (hsph : IsPLSphere m L.space)
    (hball : IsPLBall k (coneSet p J.space)) :
    IsPLBallPair m k (coneSet p L.space) (coneSet p J.space) := by
  classical
  have hcfin : Finite (coneComplex hL).faces :=
    (coneComplex_faces_finite hL (Set.toFinite L.faces)).to_subtype
  have hpoly : IsPolyhedron (coneSet p L.space) := by
    rw [← coneComplex_space_eq_coneSet hL]
    exact isPolyhedron_space _
  exact ⟨p, L, J, hL, id, Set.toFinite L.faces, hJL, hsph, hball,
    hpoly.isPLHomeomorphOn_id, Set.image_id _⟩

theorem isPLBallPair_coneSet_of_isPLSphere [FiniteDimensional ℝ E] {m k : ℕ} {p : E}
    {L J : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L)
    (hJL : J.faces ⊆ L.faces) (hsph : IsPLSphere m L.space) (hJsph : IsPLSphere k J.space) :
    IsPLBallPair m (k + 1) (coneSet p L.space) (coneSet p J.space) := by
  classical
  have : Finite J.faces := ((Set.toFinite L.faces).subset hJL).to_subtype
  refine isPLBallPair_coneSet hL hJL hsph ?_
  rw [← coneComplex_space_eq_coneSet (hL.of_faces_subset hJL)]
  exact (hL.of_faces_subset hJL).isPLBall_of_isPLSphere hJsph

theorem exists_isPLHomeomorphOn_coneSet_pair [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {p : E} {q : F} {L J : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L)
    (hJL : J.faces ⊆ L.faces) {L' J' : Geometry.SimplicialComplex ℝ F} [Finite L'.faces]
    (hL' : IsConeBase q L') {f : E → F} (hf : IsPLHomeomorphOn f L.space L'.space)
    (hfJ : f '' J.space = J'.space) :
    ∃ g : E → F, IsPLHomeomorphOn g (coneSet p L.space) (coneSet q L'.space) ∧
      EqOn g f L.space ∧ g p = q ∧ g '' coneSet p J.space = coneSet q J'.space := by
  classical
  obtain ⟨g, hg, hgf, hgp, -, hpair⟩ := exists_isPLHomeomorphOn_coneComplex_pair hL hL' hf
  rw [coneComplex_space_eq_coneSet hL, coneComplex_space_eq_coneSet hL'] at hg
  exact ⟨g, hg, hgf, hgp, by rw [hpair _ (space_mono_of_faces_subset hJL), hfJ]⟩

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
  obtain ⟨g, hg, hgf, hgp, hgJ⟩ := exists_isPLHomeomorphOn_coneSet_pair hL hJL hL' hf hfJ
  exact ⟨g, hg, hgf, hgp, hgJ, isPLBallPair_coneSet_of_isPLSphere hL hJL hsph hJsph,
    isPLBallPair_coneSet_of_isPLSphere hL' hJL' hsph' hJsph'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
