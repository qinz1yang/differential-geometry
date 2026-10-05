import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutShellChartApplications
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

/-!
# Chapter-14 assembly, L2 COMPARE A6-b, part 1: the fold of the core on the capped carrier

Lane ASM-L2d. For the cut-and-capped data `X : SphereCutCapped W S E` of a sphere seam:

* `SphereCutCapped.coreFold`: the fold `X.fold` read through the inverse of the core embedding, as a
  map on the whole capped carrier (`coreFold_core`: `coreFold ∘ core = fold`);
* `isLocalDiffeomorphAt_fold`, `isLocalDiffeomorphAt_core`, `isLocalDiffeomorphAt_coreFold`: at
  interior points of the cut carrier the fold, the core and `coreFold` are local diffeomorphisms
  (bijective differentials: the orientation field `oriented` of the fold and `core_positive`);
* `coreFold_oriented`: `coreFold` is orientation preserving at the core image of an interior point;
* `SphereCutCapped.boundary_eq_empty` (step 0 of A6): without boundary tori (`n = 0`) the carrier
  `W` has empty boundary — interior points of the cut carrier fold to interior points, and the cut
  spheres fold into the interior collar of the seam.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- The fold of the core, defined on the whole capped carrier (off the core: a fixed value). -/
def coreFold (x : X.Q.Carrier) : W.Carrier :=
  haveI := Classical.propDecidable
  if h : ∃ y, X.capping.core y = x then X.fold h.choose
  else X.fold (X.B.sphere (Fin.cast X.h2.symm 0)
    (ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩, halfZero))

theorem coreFold_core (y : X.C.Carrier) : X.coreFold (X.capping.core y) = X.fold y := by
  have h : ∃ y', X.capping.core y' = X.capping.core y := ⟨y, rfl⟩
  unfold coreFold
  rw [dite_eq_left h]
  exact congrArg X.fold (core_injective X.capping h.choose_spec)

theorem coreFold_comp_core : X.coreFold ∘ X.capping.core = X.fold :=
  funext X.coreFold_core

/-- The differential of the fold is bijective everywhere (orientation field). -/
theorem bijective_mfderiv_fold (x : X.C.Carrier) :
    Bijective (mfderiv X.C.model W.model X.fold x) := by
  obtain ⟨L, hL, -⟩ := X.oriented x
  have he : ⇑(mfderiv X.C.model W.model X.fold x) = ⇑L := funext fun v => (hL v).symm
  rw [he]
  exact L.bijective

theorem isLocalDiffeomorphAt_fold {y : X.C.Carrier} (hy : X.C.model.IsInteriorPoint y) :
    IsLocalDiffeomorphAt X.C.model W.model ∞ X.fold y :=
  isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective X.smooth hy (X.bijective_mfderiv_fold y)

theorem isLocalDiffeomorphAt_core {y : X.C.Carrier} (hy : X.C.model.IsInteriorPoint y) :
    IsLocalDiffeomorphAt X.C.model X.Q.model ∞ X.capping.core y :=
  isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective X.capping.core_embedding.contMDiff hy
    (X.capping.core_positive y hy).1

/-- `coreFold` is a local diffeomorphism at the core image of an interior point. -/
theorem isLocalDiffeomorphAt_coreFold {y : X.C.Carrier} (hy : X.C.model.IsInteriorPoint y) :
    IsLocalDiffeomorphAt X.Q.model W.model ∞ X.coreFold (X.capping.core y) := by
  have h : IsLocalDiffeomorphAt X.C.model W.model ∞ (X.coreFold ∘ X.capping.core) y := by
    rw [X.coreFold_comp_core]
    exact X.isLocalDiffeomorphAt_fold hy
  exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp h (X.isLocalDiffeomorphAt_core hy)

/-- `coreFold` is orientation preserving at the core image of an interior point. -/
theorem coreFold_oriented {y : X.C.Carrier} (hy : X.C.model.IsInteriorPoint y) :
    ∃ L : TangentSpace X.Q.model (X.capping.core y) ≃ₗ[ℝ]
        TangentSpace W.model (X.coreFold (X.capping.core y)),
      (∀ v, L v = mfderiv X.Q.model W.model X.coreFold (X.capping.core y) v) ∧
      Orientation.map (Fin 3) L (X.Q.orientation.orientation (X.capping.core y)) =
        W.orientation.orientation (X.coreFold (X.capping.core y)) := by
  obtain ⟨hbij, hpos⟩ := X.capping.core_positive y hy
  obtain ⟨Lf, hLf, hof⟩ := X.oriented y
  let Lc : TangentSpace X.C.model y ≃ₗ[ℝ] TangentSpace X.Q.model (X.capping.core y) :=
    LinearEquiv.ofBijective (mfderiv X.C.model X.Q.model X.capping.core y).toLinearMap hbij
  have hdg : MDifferentiableAt X.Q.model W.model X.coreFold (X.capping.core y) :=
    (X.isLocalDiffeomorphAt_coreFold hy).mdifferentiableAt (by simp)
  have hdc : MDifferentiableAt X.C.model X.Q.model X.capping.core y :=
    (X.isLocalDiffeomorphAt_core hy).mdifferentiableAt (by simp)
  have hchain : ∀ v, mfderiv X.C.model W.model X.fold y v =
      mfderiv X.Q.model W.model X.coreFold (X.capping.core y)
        (mfderiv X.C.model X.Q.model X.capping.core y v) := by
    intro v
    rw [← X.coreFold_comp_core, mfderiv_comp y hdg hdc]
    rfl
  refine ⟨Lc.symm.trans Lf, fun v => ?_, ?_⟩
  · change Lf (Lc.symm v) = _
    rw [hLf, hchain]
    congr 1
    exact Lc.apply_symm_apply v
  · have h1 : Orientation.map (Fin 3) (Lc.symm.trans Lf)
        (X.Q.orientation.orientation (X.capping.core y)) = W.orientation.orientation (X.fold y) := by
      rw [orientation_map_trans_fin_three, ← hpos]
      change Orientation.map (Fin 3) Lf (Orientation.map (Fin 3) Lc.symm
        (Orientation.map (Fin 3) Lc (X.C.orientation.orientation y))) = _
      rw [← orientation_map_trans_fin_three Lc Lc.symm, LinearEquiv.self_trans_symm,
        Orientation.map_refl]
      exact hof
    have h2 : W.orientation.orientation (X.fold y) =
        W.orientation.orientation (X.coreFold (X.capping.core y)) := by
      rw [X.coreFold_core]
    exact h1.trans h2

end SphereCutCapped

/-- **Step 0 of A6.** Without boundary tori, the carrier has empty boundary. -/
theorem SphereCutCapped.boundary_eq_empty {W : CompactCarrier.{u}} {S : SphereSeam W}
    {E : BoundaryTori W 0} (X : SphereCutCapped W S E) : W.model.boundary W.Carrier = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨x, rfl⟩ := X.surjective w
  have hint : W.model.IsInteriorPoint (X.fold x) := by
    by_cases hx : X.C.model.IsInteriorPoint x
    · exact (X.smooth.mdifferentiableAt (by simp)).isInteriorPoint_of_surjective_mfderiv
        (X.bijective_mfderiv_fold x).2 hx
    · have hb : x ∈ X.C.model.boundary X.C.Carrier :=
        (X.C.model.isInteriorPoint_or_isBoundaryPoint x).resolve_left hx
      rw [X.B.boundary_eq] at hb
      rcases hb with ht | hs
      · obtain ⟨i, -⟩ := mem_iUnion.mp ht
        exact (Fin.cast X.hn i).elim0
      · obtain ⟨i, z, rfl⟩ := mem_iUnion.mp hs
        have hi : i = Fin.cast X.h2.symm (Fin.cast X.h2 i) := by
          ext
          rfl
        have he := X.spheres (Fin.cast X.h2 i) z 0 le_rfl zero_lt_one
        rw [← hi] at he
        change X.fold (X.B.sphere i (z, halfZero)) ∈ W.model.interior W.Carrier
        rw [show halfZero = halfPoint 0 le_rfl from rfl, he]
        apply S.target_interior
        apply S.collar.map_source
        rw [S.source_eq]
        refine ⟨mem_univ _, ?_⟩
        split_ifs <;> norm_num
  exact (W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hint hw

end GC.GraphManifold.Assembly
