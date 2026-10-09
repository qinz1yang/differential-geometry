import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelFold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutDrillBoundary

/-!
# Chapter-14 assembly, relative COMPARE cut data (shared, part 2): the ports of `W`

Lane ASM-L2f, shared cut-data group (for G5 SEP and G6 NONSEP). A regular cut of `W` records ports
`E'` with `∂W = E'.image` (`RegularCutData.external_exhausted`); the assembly uses a recorded shrink
`E.shrink δ` of the ports of the sphere-cut data (`BoundaryTori.shrink_image`). This file proves that
the ports `E` of a sphere-cut-capped carrier exhaust the boundary of `W` (the fold of G1 is a local
diffeomorphism off the caps, the seam sphere is interior, and the boundary of the capped carrier is
its retained ports, which the fold sends onto the ports of `W`).

* `SphereCutCapped.boundary_eq_image`: `∂W = E.image`.
* `SphereCutCapped.capComplementFold_retained_zero`: the fold of a retained port zero section is the
  port zero section of `W`.
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

/-- The fold of a retained port zero section of the capped carrier, read through any fold
partial diffeomorphism `F`, is a port zero section of `W`. -/
theorem capComplementFold_retained_zero
    (F : PartialDiffeomorph X.Q.model W.model X.Q.Carrier W.Carrier ∞)
    (hF : ∀ y, X.capping.core y ∈ F.source → F (X.capping.core y) = X.fold y)
    (j : Fin X.B.torusCount) (τ : Torus)
    (hs : X.capping.retained.collar j (τ, halfZero) ∈ F.source) :
    F (X.capping.retained.collar j (τ, halfZero)) = E.collar (Fin.cast X.hn j) (τ, halfZero) := by
  have hcore : X.capping.retained.collar j (τ, halfZero) =
      X.capping.core (X.B.tori.collar j (τ, halfZero)) :=
    X.capping.retained_collar j _ (zero_mem_halfCollarSource τ)
  rw [hcore] at hs ⊢
  rw [hF _ hs]
  have h := X.tori (Fin.cast X.hn j) (τ, halfZero) (zero_mem_halfCollarSource τ)
  have hj : Fin.cast X.hn.symm (Fin.cast X.hn j) = j := Fin.ext rfl
  rw [hj] at h
  exact h

include X in
/-- **The ports of `W` exhaust its boundary.** -/
theorem boundary_eq_image : W.model.boundary W.Carrier = E.image := by
  obtain ⟨F, hFs, hFt, hF⟩ := X.exists_capComplementFold
  ext y
  constructor
  · intro hy
    have hyt : y ∈ F.target := by
      rw [hFt]
      rintro ⟨z, rfl⟩
      have hzs : (z, (0 : ℝ)) ∈ S.collar.source := by
        rw [S.source_eq]
        exact ⟨by norm_num, by norm_num⟩
      have hi : S.collar (z, 0) ∈ W.interior := S.target_interior (S.collar.map_source hzs)
      exact (W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hi hy
    have hx : F.symm y ∈ F.source := F.map_target hyt
    have hFx : F (F.symm y) = y := F.right_inv hyt
    have hloc := F.isLocalDiffeomorphAt X.Q.model W.model ∞ hx
    have hxb : X.Q.model.IsBoundaryPoint (F.symm y) := by
      rw [hloc.isBoundaryPoint_iff (by simp), hFx]
      exact hy
    have hxr : F.symm y ∈ X.capping.retained.image := by
      rw [← X.capping.boundary_exhausted]
      exact hxb
    obtain ⟨j, τ, hj⟩ := mem_iUnion.mp hxr
    have hs : X.capping.retained.collar j (τ, halfZero) ∈ F.source := by
      change X.capping.retained.torusMap j τ ∈ F.source
      rw [hj]
      exact hx
    rw [← hFx, ← hj]
    change F (X.capping.retained.collar j (τ, halfZero)) ∈ E.image
    rw [X.capComplementFold_retained_zero F hF j τ hs]
    exact mem_iUnion.mpr ⟨Fin.cast X.hn j, τ, rfl⟩
  · intro hy
    obtain ⟨i, τ, rfl⟩ := mem_iUnion.mp hy
    exact E.boundary_zero i τ

end SphereCutCapped

end GC.GraphManifold.Assembly
