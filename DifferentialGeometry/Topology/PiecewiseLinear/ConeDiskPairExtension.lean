import DifferentialGeometry.Topology.PiecewiseLinear.SphereDiskMarked
import DifferentialGeometry.Topology.PiecewiseLinear.BallPair

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_coneSet_pair_of_disk_marked
    {p : E} {Lc J : Geometry.SimplicialComplex ℝ E} [Finite Lc.faces] (hLc : IsConeBase p Lc)
    (hJLc : J.faces ⊆ Lc.faces) (hSph : IsPLSphere 2 Lc.space)
    {q : F} {Lc' J' : Geometry.SimplicialComplex ℝ F} [Finite Lc'.faces] (hLc' : IsConeBase q Lc')
    (hSph' : IsPLSphere 2 Lc'.space)
    {D : Set E} {D' : Set F} (hD : IsPLBall 2 D) (hDS : D ⊆ Lc.space) (hD'S' : D' ⊆ Lc'.space)
    {g : E → F} (hg : IsPLHomeomorphOn g D D')
    {y : E} (hy : y ∈ closure (Lc.space \ D) \ D)
    {y' : F} (hy' : y' ∈ closure (Lc'.space \ D') \ D')
    (hJsplit : J.space = J.space ∩ D ∪ {y}) (hJ'split : J'.space = J'.space ∩ D' ∪ {y'})
    (hgJ : g '' (J.space ∩ D) = J'.space ∩ D') :
    ∃ G : E → F, IsPLHomeomorphOn G (coneSet p Lc.space) (coneSet q Lc'.space) ∧
      EqOn G g D ∧ G p = q ∧ G '' coneSet p J.space = coneSet q J'.space := by
  classical
  obtain ⟨Gs, hGs, hGseq, hGsy⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_isPLSphere_two_marked hSph hSph' hD hDS hg hD'S' hy hy'
  have hGsJ : Gs '' J.space = J'.space := by
    rw [hJsplit, image_union, image_singleton, hGsy,
      (hGseq.mono inter_subset_right).image_eq, hgJ, ← hJ'split]
  obtain ⟨G, hG, hGeq, hGp, hGJ⟩ :=
    exists_isPLHomeomorphOn_coneSet_pair hLc hJLc hLc' hGs hGsJ
  exact ⟨G, hG, (hGeq.mono hDS).trans hGseq, hGp, hGJ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
