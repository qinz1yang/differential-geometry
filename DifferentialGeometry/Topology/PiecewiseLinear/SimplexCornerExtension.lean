import DifferentialGeometry.Topology.PiecewiseLinear.ConeAmbientExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexCornerFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_isPLHomeomorphOn_extension_simplex_vertex_star [FiniteDimensional ℝ E] [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    (hspan : affineSpan ℝ (T : Set E) = ⊤) {a : E} (ha : a ∈ T)
    {f : E → E} (hf : IsPLHomeomorphOn f (starComplex (simplexBoundary T hT) a).space
      (starComplex (simplexBoundary T hT) a).space)
    (hfix : EqOn f id
      (simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).space)
    {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧
      h '' convexHull ℝ (T : Set E) = convexHull ℝ (T : Set E) ∧
      EqOn h f (starComplex (simplexBoundary T hT) a).space ∧ EqOn h id Uᶜ := by
  have hfL : IsPLHomeomorphOn f (simplexAvoiding T hT {T.erase a}).space
      (simplexAvoiding T hT {T.erase a}).space := by
    rw [simplexAvoiding_erase_eq_starComplex T hT ha]
    exact hf
  have : Finite (simplexAvoiding T hT {T.erase a}).faces :=
    (simplexAvoiding_faces_finite T hT {T.erase a}).to_subtype
  obtain ⟨p, q, hp, hq, hinter, hpT, hqinter, hNU, hfront⟩ :=
    exists_isConeBase_simplexAvoiding_with_frontier T hT hcard hspan ha hU hTU
  obtain ⟨h, hh, hhf, hhP, -, hhfix⟩ := exists_isPLHomeomorphOn_extension_coneComplex_union
    (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a) hp hq hinter hfront hfL hfix
  have hmemP {x : E} (hx : x ∈ convexHull ℝ (T : Set E))
      (hxN : x ∈ (coneComplex hp).space ∪ (coneComplex hq).space) : x ∈ (coneComplex hp).space := by
    rcases hxN with hxP | hxQ
    · exact hxP
    · exact space_subset_coneComplex_space hp (hqinter ▸ ⟨hxQ, hx⟩)
  refine ⟨h, hh, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      by_cases hxN : x ∈ (coneComplex hp).space ∪ (coneComplex hq).space
      · exact hpT (hhP ▸ ⟨x, hmemP hx hxN, rfl⟩)
      · rwa [hhfix hxN, id_eq]
    · intro y hy
      by_cases hyN : y ∈ (coneComplex hp).space ∪ (coneComplex hq).space
      · have hyP : y ∈ h '' (coneComplex hp).space := hhP.symm ▸ hmemP hy hyN
        obtain ⟨x, hx, hxy⟩ := hyP
        exact ⟨x, hpT hx, hxy⟩
      · exact ⟨y, hy, hhfix hyN⟩
  · rwa [simplexAvoiding_erase_eq_starComplex T hT ha] at hhf
  · intro x hx
    exact hhfix (fun hxN => hx (hNU hxN))

end DifferentialGeometry.Topology.PiecewiseLinear
