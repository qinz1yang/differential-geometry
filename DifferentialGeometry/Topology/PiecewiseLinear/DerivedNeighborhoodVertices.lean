/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodEdge

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_homeomorph_iUnion_derivedNeighborhoodCell_vertices
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (V : Finset E)
    (hV : ∀ v ∈ V, {v} ∈ K.faces) :
    ∃ c : V → (Fin (n + 2) → ℝ) → E,
      (∀ v, IsPLHomeomorphOn (c v) (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)))
        (derivedNeighborhoodCell K {v.val}).space) ∧
      ∃ e : (Σ _ : V, Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) ≃ₜ
          (⋃ v ∈ V, (derivedNeighborhoodCell K {v}).space),
        ∀ v x, (e ⟨v, x⟩ : E) = c v x.val := by
  classical
  have hballs (v : V) : ∃ c : (Fin (n + 2) → ℝ) → E,
      IsPLHomeomorphOn c (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)))
        (derivedNeighborhoodCell K {v.val}).space :=
    hK.isPLBall_derivedNeighborhoodCell (hV v.val v.property)
  choose c hc using hballs
  let f : (Σ _ : V, Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) →
      (⋃ v ∈ V, (derivedNeighborhoodCell K {v}).space) := fun z =>
    ⟨c z.1 z.2.val, mem_iUnion₂.mpr ⟨z.1.val, z.1.property,
      (hc z.1).bijOn.mapsTo z.2.property⟩⟩
  have hfcont : Continuous f := continuous_sigma fun v =>
    (continuousOn_iff_continuous_domRestrict.mp
      (hc v).isPiecewiseAffineOn.continuousOn).subtype_mk _
  have hfinj : Function.Injective f := by
    rintro ⟨v, x⟩ ⟨w, y⟩ heq
    have hxy : c v x.val = c w y.val := congrArg Subtype.val heq
    have hvw : v = w := by
      by_contra hne
      have hdis := disjoint_derivedNeighborhoodCell_of_card_eq K
        (hV v.val v.property) (hV w.val w.property) (by simp)
        (fun h => hne (Subtype.ext (Finset.singleton_injective h)))
      exact disjoint_left.mp hdis ((hc v).bijOn.mapsTo x.property)
        (hxy.symm ▸ (hc w).bijOn.mapsTo y.property)
    subst w
    have hxy' : x = y := Subtype.ext ((hc v).bijOn.injOn x.property y.property hxy)
    subst y
    rfl
  have hfsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hz
    obtain ⟨x, hx, hxz⟩ := (hc ⟨v, hv⟩).bijOn.surjOn hzv
    exact ⟨⟨⟨v, hv⟩, ⟨x, hx⟩⟩, Subtype.ext hxz⟩
  let e := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨hfinj, hfsurj⟩) hfcont
  exact ⟨c, hc, e, fun _ _ => rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
