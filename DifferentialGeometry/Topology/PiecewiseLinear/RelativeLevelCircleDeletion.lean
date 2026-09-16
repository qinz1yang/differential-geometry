import DifferentialGeometry.Topology.PiecewiseLinear.SingularLevelPolygons

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem levelPolygons_eq_sdiff_of_fiber_eq_sdiff
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ K.vertices) {Q J T : Set E} {f : E → ℝ} {r : ℝ}
    (hQ : Q ⊆ K.space) (hJ : J ∈ levelPolygons Q ℓ (ℓ p))
    (hfiber : T ∩ {x | f x = r} =
      (Q ∩ {x | ℓ x = ℓ p}) \ (J \ {p})) :
    levelPolygons T f r = levelPolygons Q ℓ (ℓ p) \ {J} := by
  classical
  have hJK : J ∈ levelPolygons K.space ℓ (ℓ p) :=
    ⟨hJ.1, fun x hx => ⟨hQ (hJ.2 hx).1, (hJ.2 hx).2⟩⟩
  have hJpunctured : (J \ {p}).Nonempty := by
    obtain ⟨x, hxJ⟩ := hJ.1.nonempty
    by_cases hxp : x = p
    · subst x
      exact (hJ.1.isConnected_sdiff_singleton_one p).nonempty
    · exact ⟨x, hxJ, by simpa only [mem_singleton_iff] using hxp⟩
  ext L
  constructor
  · intro hL
    have hLold : L ∈ levelPolygons Q ℓ (ℓ p) := by
      refine ⟨hL.1, fun x hx => ?_⟩
      exact (hfiber.subset (hL.2 hx)).1
    refine ⟨hLold, ?_⟩
    rw [mem_singleton_iff]
    intro hLJ
    obtain ⟨x, hxJ, hxp⟩ := hJpunctured
    have hxnew := hfiber.subset (hL.2 (hLJ ▸ hxJ))
    exact hxnew.2 ⟨hxJ, hxp⟩
  · rintro ⟨hL, hLJ⟩
    refine ⟨hL.1, fun x hx => hfiber.symm.subset ?_⟩
    refine ⟨hL.2 hx, ?_⟩
    rintro ⟨hxJ, hxp⟩
    have hLK : L ∈ levelPolygons K.space ℓ (ℓ p) :=
      ⟨hL.1, fun y hy => ⟨hQ (hL.2 hy).1, (hL.2 hy).2⟩⟩
    have hxsing := inter_subset_singleton_levelPolygons_of_ne K hK hdimE ℓ hℓ hinj
      hp hLK hJK (by simpa only [mem_singleton_iff] using hLJ) ⟨hx, hxJ⟩
    exact hxp hxsing

end DifferentialGeometry.Topology.PiecewiseLinear
