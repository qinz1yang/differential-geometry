import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutDrillWidth

/-!
# Chapter-14 assembly, L2-relative DRILL (b): the ports of a drilled carrier

Lane ASM-L2b, row DRILL. After drilling a regular fibre, the retained carrier `K` embeds in the old
carrier `C` by `ι` (with a partial inverse `O` off the closed unit tube). Its ports are the old ports,
transported through `O` after the recorded shrinking of DRILL-a, plus the new radial torus.

* `transportCollar_source`, `transportCollar_apply`, `transportCollar_target`: an old half collar
  whose target lies in the source of `O`, transported to `K`.
* `isBoundaryPoint_of_image_boundary`: `ι` reflects boundary points.
* `appendBoundaryTori`, `appendBoundaryTori_image`: `n` old ports plus one new port.
* `boundary_eq_of_embedding_relative`: the boundary of `K` is the retained blocks, the transported
  old ports and the new port (the relative form of `fibreRetainedBoundary_exhausted`,
  `Closure/FibreRetainedBoundary.lean`, which assumed a closed carrier).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Transport

variable {C K : CompactCarrier.{u}} (ι : K.Carrier → C.Carrier)
  (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)

/-- An old half collar transported through the partial inverse `O` has the standard source. -/
theorem transportCollar_source
    (c : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hc : c.source = halfCollarSource) (ha : c.target ⊆ O.source) :
    (c.trans O).source = halfCollarSource := by
  ext p
  change (p ∈ c.source ∧ c p ∈ O.source) ↔ p ∈ halfCollarSource
  constructor
  · intro hp
    exact hc ▸ hp.1
  · intro hp
    have hs : p ∈ c.source := hc.symm ▸ hp
    exact ⟨hs, ha (c.map_source hs)⟩

/-- The transported collar is the old collar after `ι`. -/
theorem transportCollar_apply (hO : ∀ x, x ∈ O.source → ι (O x) = x)
    (c : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hc : c.source = halfCollarSource) (ha : c.target ⊆ O.source)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    ι ((c.trans O) p) = c p :=
  hO (c p) (ha (c.map_source (hc.symm ▸ hp)))

/-- The target of the transported collar lies over the old target. -/
theorem transportCollar_target (hO : ∀ x, x ∈ O.source → ι (O x) = x)
    (c : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    {x : K.Carrier} (hx : x ∈ (c.trans O).target) : ι x ∈ c.target := by
  have hx' : x ∈ O.target ∧ O.symm x ∈ c.target := hx
  have hxs : O.symm x ∈ O.source := O.map_target hx'.1
  have he : O (O.symm x) = x := O.right_inv hx'.1
  rw [← he, hO _ hxs]
  exact hx'.2

end Transport

/-- An embedding whose image of the boundary contains the old boundary reflects boundary points. -/
theorem isBoundaryPoint_of_image_boundary {C K : CompactCarrier.{u}} {ι : K.Carrier → C.Carrier}
    (hι : Injective ι) {S : Set C.Carrier}
    (hb : ι '' K.model.boundary K.Carrier = C.model.boundary C.Carrier ∪ S) {y : K.Carrier}
    (hy : C.model.IsBoundaryPoint (ι y)) : K.model.IsBoundaryPoint y := by
  have h : ι y ∈ ι '' K.model.boundary K.Carrier := by
    rw [hb]
    exact Or.inl hy
  obtain ⟨y', hy', he⟩ := h
  exact hι he ▸ hy'

/-- `n` old ports plus one new port. -/
def appendBoundaryTori {K : CompactCarrier.{u}} {n : ℕ}
    (c : Fin n → PartialDiffeomorph halfCollarModel K.model
      (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hcs : ∀ j, (c j).source = halfCollarSource)
    (hcb : ∀ j t, K.model.IsBoundaryPoint (c j (t, halfZero)))
    (hcd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (Γ : PartialDiffeomorph halfCollarModel K.model (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hΓs : Γ.source = halfCollarSource) (hΓb : ∀ t, K.model.IsBoundaryPoint (Γ (t, halfZero)))
    (hΓd : ∀ j, Disjoint (c j).target Γ.target) : BoundaryTori K (n + 1) where
  collar := Fin.lastCases Γ c
  source_eq j := by
    induction j using Fin.lastCases with
    | last => rw [Fin.lastCases_last]; exact hΓs
    | cast j => rw [Fin.lastCases_castSucc]; exact hcs j
  boundary_zero j t := by
    induction j using Fin.lastCases with
    | last => rw [Fin.lastCases_last]; exact hΓb t
    | cast j => rw [Fin.lastCases_castSucc]; exact hcb j t
  disjoint i j hij := by
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact (hij rfl).elim
      | cast j =>
        rw [Fin.lastCases_last, Fin.lastCases_castSucc]
        exact (hΓd j).symm
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.lastCases_last, Fin.lastCases_castSucc]
        exact hΓd i
      | cast j =>
        rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
        exact hcd (fun h => hij (congrArg Fin.castSucc h))

/-- The image of the appended ports. -/
theorem appendBoundaryTori_image {K : CompactCarrier.{u}} {n : ℕ}
    (c : Fin n → PartialDiffeomorph halfCollarModel K.model
      (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hcs : ∀ j, (c j).source = halfCollarSource)
    (hcb : ∀ j t, K.model.IsBoundaryPoint (c j (t, halfZero)))
    (hcd : Pairwise fun i j => Disjoint (c i).target (c j).target)
    (Γ : PartialDiffeomorph halfCollarModel K.model (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hΓs : Γ.source = halfCollarSource) (hΓb : ∀ t, K.model.IsBoundaryPoint (Γ (t, halfZero)))
    (hΓd : ∀ j, Disjoint (c j).target Γ.target) :
    (appendBoundaryTori c hcs hcb hcd Γ hΓs hΓb hΓd).image =
      (⋃ j, range fun t : Torus => c j (t, halfZero)) ∪
        range fun t : Torus => Γ (t, halfZero) := by
  have hl : (appendBoundaryTori c hcs hcb hcd Γ hΓs hΓb hΓd).collar (Fin.last n) = Γ := by
    simp only [appendBoundaryTori, Fin.lastCases_last]
  have hcc : ∀ j, (appendBoundaryTori c hcs hcb hcd Γ hΓs hΓb hΓd).collar (Fin.castSucc j) =
      c j := fun j => by simp only [appendBoundaryTori, Fin.lastCases_castSucc]
  ext x
  simp only [BoundaryTori.image, BoundaryTori.torusMap, mem_iUnion, mem_union, mem_range]
  constructor
  · rintro ⟨j, t, ht⟩
    induction j using Fin.lastCases with
    | last =>
      rw [hl] at ht
      exact Or.inr ⟨t, ht⟩
    | cast j =>
      rw [hcc] at ht
      exact Or.inl ⟨j, t, ht⟩
  · rintro (⟨j, t, ht⟩ | ⟨t, ht⟩)
    · exact ⟨Fin.castSucc j, t, by rw [hcc]; exact ht⟩
    · exact ⟨Fin.last n, t, by rw [hl]; exact ht⟩

/-- **Relative boundary of a drilled carrier.** If the image of the boundary of `K` is the old
boundary plus a new torus, the old boundary is blocks plus old ports, and every block, old port and
new port of `K` lies exactly over its old counterpart, then the boundary of `K` is its blocks, its
transported old ports and its new port. -/
theorem boundary_eq_of_embedding_relative {C K : CompactCarrier.{u}} {ι : K.Carrier → C.Carrier}
    (hι : Injective ι) {m n : ℕ} (BC : Fin m → Set C.Carrier) (BK : Fin m → Set K.Carrier)
    (hblock : ∀ j x, x ∈ BK j ↔ ι x ∈ BC j) (cC : Fin n → Torus → C.Carrier)
    (cK : Fin n → Torus → K.Carrier) (hc : ∀ j t, ι (cK j t) = cC j t)
    (newC : Torus → C.Carrier) (newK : Torus → K.Carrier) (hnew : ∀ t, ι (newK t) = newC t)
    (hbC : C.model.boundary C.Carrier = (⋃ j, BC j) ∪ ⋃ j, range (cC j))
    (hbK : ι '' K.model.boundary K.Carrier = C.model.boundary C.Carrier ∪ range newC) :
    K.model.boundary K.Carrier = (⋃ j, BK j) ∪ ((⋃ j, range (cK j)) ∪ range newK) := by
  rw [hbC] at hbK
  ext x
  constructor
  · intro hx
    have hi : ι x ∈ ι '' K.model.boundary K.Carrier := mem_image_of_mem ι hx
    rw [hbK] at hi
    rcases hi with (hi | hi) | ⟨t, ht⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hi
      exact Or.inl (mem_iUnion.mpr ⟨j, (hblock j x).mpr hj⟩)
    · obtain ⟨j, t, ht⟩ := mem_iUnion.mp hi
      exact Or.inr (Or.inl (mem_iUnion.mpr ⟨j, t, hι ((hc j t).trans ht)⟩))
    · exact Or.inr (Or.inr ⟨t, hι ((hnew t).trans ht)⟩)
  · intro hx
    have hi : ι x ∈ ι '' K.model.boundary K.Carrier := by
      rw [hbK]
      rcases hx with hx | (hx | ⟨t, rfl⟩)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        exact Or.inl (Or.inl (mem_iUnion.mpr ⟨j, (hblock j x).mp hj⟩))
      · obtain ⟨j, t, rfl⟩ := mem_iUnion.mp hx
        exact Or.inl (Or.inr (mem_iUnion.mpr ⟨j, t, (hc j t).symm⟩))
      · exact Or.inr ⟨t, (hnew t).symm⟩
    obtain ⟨y, hy, he⟩ := hi
    exact hι he ▸ hy

end GC.GraphManifold.Assembly
