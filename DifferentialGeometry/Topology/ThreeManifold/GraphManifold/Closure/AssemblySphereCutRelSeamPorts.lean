import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelSeamWidth
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreCollarAvoidance

/-!
# Chapter-14 assembly, relative COMPARE shared seams: the shrunk ports

Lane ASM-L2e3, shared seam group (for G5 SEP and G6 NONSEP). The ports `R` of the capped carrier
`Q` are shrunk by one `δ` away from a compact subset of the interior (the support of the placement
and the seam bands), and every shrunk port lies in one piece of a finite open partition of `Q`
(its owner). Through a map `g : Q → W` that carries the ports of `Q` onto the ports `E` of `W`, the
same shrink of `E` is the image of the shrunk ports of `Q` (a recorded shrink, boundary image
unchanged).

* `isClosed_of_openPartition`: a piece of a finite open partition is closed.
* `BoundaryTori.exists_partitionOwner`: the owner of every port.
* `BoundaryTori.shrink_collar_map`: shrinking commutes with a map carrying ports onto ports.
* `BoundaryTori.exists_shrink_zero_of_boundary`: a boundary point is a zero-section point of the
  shrunk ports.
* `exists_portShrink`: the shrink with its avoidance and owners.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- A piece of a finite open partition is closed. -/
theorem isClosed_of_openPartition {X : Type*} [TopologicalSpace X] {m : ℕ} {O : Fin m → Set X}
    (hOo : ∀ j, IsOpen (O j)) (hOd : Pairwise (Disjoint on O)) (hOc : ∀ x, ∃ j, x ∈ O j)
    (j : Fin m) : IsClosed (O j) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨j', hj'⟩ := hOc x
  have hne : j' ≠ j := fun h => hx (h ▸ hj')
  exact ⟨O j', fun y hy hyj => disjoint_left.mp (hOd hne) hy hyj, hOo j', hj'⟩

/-- Two pieces of a partition containing one point are equal. -/
theorem eq_of_mem_openPartition {X : Type*} {m : ℕ} {O : Fin m → Set X}
    (hOd : Pairwise (Disjoint on O)) {x : X} {j j' : Fin m} (hj : x ∈ O j) (hj' : x ∈ O j') :
    j = j' := by
  by_contra hne
  exact disjoint_left.mp (hOd hne) hj hj'

end GC.GraphManifold.Assembly

namespace GC.GraphManifold.BoundaryTori

open GC.GraphManifold.Assembly

variable {C : CompactCarrier.{u}} {n : ℕ} (R : BoundaryTori C n)

/-- **The owner of a port.** Every port lies in one piece of a finite open partition. -/
theorem exists_partitionOwner {m : ℕ} {O : Fin m → Set C.Carrier} (hOo : ∀ j, IsOpen (O j))
    (hOd : Pairwise (Disjoint on O)) (hOc : ∀ x, ∃ j, x ∈ O j) :
    ∃ o : Fin n → Fin m, ∀ i p, p ∈ halfCollarSource → R.collar i p ∈ O (o i) := by
  have h : ∀ i, ∃ j, ∀ p, p ∈ halfCollarSource → R.collar i p ∈ O j := by
    intro i
    let τ₀ : Torus := (1, 1)
    obtain ⟨j, hj⟩ := hOc (R.collar i (τ₀, halfZero))
    refine ⟨j, fun p hp => ?_⟩
    have hc : ContinuousOn (R.collar i) halfCollarSource := by
      rw [← R.source_eq i]
      exact (R.collar i).contMDiffOn.continuousOn
    have hcon := isPreconnected_halfCollarSource.image _ hc
    have hsub := hcon.subset_isClopen ⟨isClosed_of_openPartition hOo hOd hOc j, hOo j⟩
      ⟨_, ⟨(τ₀, halfZero), zero_mem_halfCollarSource τ₀, rfl⟩, hj⟩
    exact hsub ⟨p, hp, rfl⟩
  choose o ho using h
  exact ⟨o, ho⟩

/-- **Shrinking commutes with a map carrying the ports of `C` onto the ports `E`.** -/
theorem shrink_collar_map {D : CompactCarrier.{u}} (E : BoundaryTori D n) (g : C.Carrier → D.Carrier)
    (s : Set C.Carrier)
    (hg : ∀ i p, p ∈ halfCollarSource → R.collar i p ∈ s → g (R.collar i p) = E.collar i p)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (i : Fin n) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) (hs : (R.shrink hδ hδ1).collar i p ∈ s) :
    g ((R.shrink hδ hδ1).collar i p) = (E.shrink hδ hδ1).collar i p :=
  hg i (p.1, halfSpaceScale hδ p.2) (halfSpaceScale_mem hδ hδ1 hp) hs

/-- A point of the image of the ports is a zero-section point of every shrink. -/
theorem exists_shrink_zero_of_mem_image {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {x : C.Carrier}
    (hx : x ∈ R.image) : ∃ i τ, x = (R.shrink hδ hδ1).collar i (τ, halfZero) := by
  obtain ⟨i, τ, hτ⟩ := mem_iUnion.mp hx
  refine ⟨i, τ, ?_⟩
  rw [← hτ, ← R.shrink_torusMap hδ hδ1]
  rfl

end GC.GraphManifold.BoundaryTori

namespace GC.GraphManifold.Assembly

/-- **The shrunk ports.** A shrink of the ports away from a compact subset of the interior, with an
owner in a finite open partition for every port. -/
theorem exists_portShrink {C : CompactCarrier.{u}} {n : ℕ} (R : BoundaryTori C n) {K : Set C.Carrier}
    (hK : IsCompact K) (hKI : K ⊆ C.interior) {m : ℕ} {O : Fin m → Set C.Carrier}
    (hOo : ∀ j, IsOpen (O j)) (hOd : Pairwise (Disjoint on O)) (hOc : ∀ x, ∃ j, x ∈ O j) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (o : Fin n → Fin m),
      (∀ i p, p ∈ halfCollarSource → (R.shrink hδ hδ1).collar i p ∉ K) ∧
      ∀ i p, p ∈ halfCollarSource → (R.shrink hδ hδ1).collar i p ∈ O (o i) := by
  obtain ⟨δ, hδ, hδ1, hav⟩ := R.exists_shrink_avoiding_compact hK hKI
  obtain ⟨o, ho⟩ := (R.shrink hδ hδ1).exists_partitionOwner hOo hOd hOc
  exact ⟨δ, hδ, hδ1, o, hav, ho⟩

end GC.GraphManifold.Assembly
