import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelFold

/-!
# Consumers of the fold off the caps (relative COMPARE G1)

The three formulas in which the relative comparison uses `SphereCutCapped.capComplementFold`:

* `capComplementFold_retained`: the retained port collars of the capped carrier are carried onto the
  ports of `W` on the whole half collar (`RelativeSphereCapping.retained_collar` + the `tori` field);
  in particular the retained collars lie off the caps (`retained_mem_capComplement`).
* `capComplementFold_sphere`: a point of a cut-sphere half collar off the sphere goes to the signed
  seam collar, with the sign of its side.
* `capComplementFold_mfderiv_bijective`: the differential is bijective on the whole source.
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

/-- The retained port collars lie off the caps. -/
theorem retained_mem_capComplement (i : Fin X.B.torusCount) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    X.capping.retained.collar i p ∈ X.capComplementFold.source := by
  rw [X.capping.retained_collar i p hp]
  intro hcap
  obtain ⟨j, hj⟩ := mem_iUnion.mp hcap
  have hmem : X.capping.core (X.B.tori.collar i p) ∈
      range X.capping.core ∩ range (X.capping.cap j) := ⟨⟨_, rfl⟩, hj⟩
  rw [X.capping.core_cap_intersection j] at hmem
  obtain ⟨z, hz⟩ := hmem
  have he := X.core_injective' hz
  have hsrc : (z, halfZero) ∈ (X.B.sphere j).source := by
    rw [X.B.sphere_source]
    change (0 : ℝ) < 1
    norm_num
  have htor : X.B.tori.collar i p ∈ (X.B.tori.collar i).target :=
    (X.B.tori.collar i).map_source (by rw [X.B.tori.source_eq]; exact hp)
  exact Set.disjoint_left.mp (X.B.cross_disjoint i j) htor (he ▸ (X.B.sphere j).map_source hsrc)

/-- **Ports.** The retained collars are carried onto the ports of `W` on the whole half collar. -/
theorem capComplementFold_retained (i : Fin n) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    X.capComplementFold (X.capping.retained.collar (Fin.cast X.hn.symm i) p) = E.collar i p := by
  rw [X.capping.retained_collar _ p hp, X.capComplementFold_core]
  exact X.tori i p hp

/-- **Sphere collars.** Off the sphere, the half collar of the cut sphere of side `j` goes to the
signed seam collar with the sign of the side. -/
theorem capComplementFold_sphere (j : Fin 2) (z : ClosureSphere.{u}) (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    X.capComplementFold (X.capping.core (X.B.sphere (Fin.cast X.h2.symm j) (z, halfPoint s hs0))) =
      S.collar (z, if j.val = 0 then s else -s) := by
  rw [X.capComplementFold_core]
  exact X.spheres j z s hs0 hs1

/-- The differential of the fold off the caps is bijective on its source. -/
theorem capComplementFold_mfderiv_bijective {x : X.Q.Carrier}
    (hx : x ∈ X.capComplementFold.source) :
    Bijective (mfderiv X.Q.model W.model X.capComplementFold x) := by
  have h := X.isLocalDiffeomorphAt_capFold hx
  have he : (X.capComplementFold : X.Q.Carrier → W.Carrier) = X.capFold := rfl
  rw [he]
  exact ⟨(h.mfderivToContinuousLinearEquiv (by simp)).injective,
    (h.mfderivToContinuousLinearEquiv (by simp)).surjective⟩

end SphereCutCapped

end GC.GraphManifold.Assembly
