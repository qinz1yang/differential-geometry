/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_isPLHomeomorphOn_affine_of_equiv [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {s : Finset E} {t : Finset F} (hs : AffineIndependent ℝ ((↑) : s → E))
    (ht : AffineIndependent ℝ ((↑) : t → F)) (e : s ≃ t) :
    ∃ A : E →ᵃ[ℝ] F, IsPLHomeomorphOn A (convexHull ℝ (s : Set E))
      (convexHull ℝ (t : Set F)) ∧ ∀ v : s, A v = e v := by
  classical
  let φ : E → F := fun v => if hv : v ∈ s then (e ⟨v, hv⟩ : F) else 0
  let ψ : F → E := fun w => if hw : w ∈ t then (e.symm ⟨w, hw⟩ : E) else 0
  obtain ⟨A, hA⟩ := exists_affineMap_eqOn hs φ
  obtain ⟨B, hB⟩ := exists_affineMap_eqOn ht ψ
  have hAv (v : s) : A v = (e v : F) := by
    simpa only [φ, dite_eq_left v.property, Subtype.coe_eta] using hA v v.property
  have hBw (w : t) : B w = (e.symm w : E) := by
    simpa only [ψ, dite_eq_left w.property, Subtype.coe_eta] using hB w w.property
  have hBA : EqOn (B.comp A) (AffineMap.id ℝ E) (s : Set E) := by
    intro v hv
    change B (A v) = v
    rw [hAv ⟨v, hv⟩, hBw, e.symm_apply_apply]
  have hinj : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    have hx' := AffineMap.eqOn_affineSpan hBA (convexHull_subset_affineSpan _ hx)
    have hy' := AffineMap.eqOn_affineSpan hBA (convexHull_subset_affineSpan _ hy)
    exact hx'.symm.trans ((congrArg B hxy).trans hy')
  have himage : A '' (s : Set E) = (t : Set F) := by
    apply Subset.antisymm
    · rintro _ ⟨v, hv, rfl⟩
      rw [hAv ⟨v, hv⟩]
      exact (e ⟨v, hv⟩).property
    · intro w hw
      refine ⟨e.symm ⟨w, hw⟩, (e.symm ⟨w, hw⟩).property, ?_⟩
      rw [hAv, e.apply_symm_apply]
  have hconv : A '' convexHull ℝ (s : Set E) = convexHull ℝ (t : Set F) := by
    rw [A.image_convexHull, himage]
  have hbij : BijOn A (convexHull ℝ (s : Set E)) (convexHull ℝ (t : Set F)) :=
    ⟨fun x hx => hconv ▸ (show A x ∈ A '' convexHull ℝ (s : Set E) from ⟨x, hx, rfl⟩),
      hinj, fun y hy => hconv.symm ▸ hy⟩
  refine ⟨A, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    (isHPolytope_convexHull_of_affineIndependent s hs).isPolyhedron
    (isPiecewiseAffineOn_of_affine_of_isHPolytope A
      (isHPolytope_convexHull_of_affineIndependent s hs)) hbij, hAv⟩

theorem exists_isPLHomeomorphOn_affine_of_card_eq [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {s : Finset E} {t : Finset F} (hs : AffineIndependent ℝ ((↑) : s → E))
    (ht : AffineIndependent ℝ ((↑) : t → F)) (hcard : s.card = t.card) :
    ∃ A : E →ᵃ[ℝ] F, IsPLHomeomorphOn A (convexHull ℝ (s : Set E))
      (convexHull ℝ (t : Set F)) := by
  classical
  let e : s ≃ t := Fintype.equivOfCardEq (by simpa using hcard)
  obtain ⟨A, hA, -⟩ := exists_isPLHomeomorphOn_affine_of_equiv hs ht e
  exact ⟨A, hA⟩

end DifferentialGeometry.Topology.PiecewiseLinear
