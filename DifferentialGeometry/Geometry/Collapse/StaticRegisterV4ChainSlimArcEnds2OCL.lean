import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimArcEnds74

/-!
# Draft 74, S0 on the member: the free end datum with the defining function exposed

Lane C14-REG-CHAIN (by S-REG-CHAIN6), G1 (kernel part, suffix `_OCL`). Strengthenings of the G35
kernels `exists_freeEnd74` and `ArcEnds74.exists_of_ends74` (those files are untouched):

* `exists_freeEnd2_OCL`: the free end data of an `X`-side regular defining function `h` on an
  open `U`, with the end function `fn` EXPLICIT: `fn = h ∘ φ⁻¹`;
* `ArcEnds74.exists_of_ends2_OCL`: `ArcEnds74` from end-by-end data together with a property of
  the end function of every free end, which the produced record satisfies.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

variable {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
  {W : CompactCarrier.{0}}

section Free

omit [IsManifold I3 ∞ X] in
/-- **The free end data of a regular defining function, with `fn = h ∘ φ⁻¹`.** An open `U ⊆ X`
with a function `h`, smooth on `U` with onto differential, `{h = 0} ∩ U = Bf` and
`A ∩ U = {h ≤ 0} ∩ U`, gives on a carrier without boundary the open set `φ(U)` and the five
clauses of a free end of an arc for the function `h ∘ φ⁻¹` itself. -/
theorem exists_freeEnd2_OCL (φ : X ≃ₘ⟮I3, W.model⟯ W.Carrier)
    (hW : W.model.boundary W.Carrier = ∅) {U : Set X} {h : X → ℝ} (hU : IsOpen U)
    (hh : ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ h U)
    (hs : ∀ x ∈ U, Surjective (mfderiv I3 𝓘(ℝ, ℝ) h x)) {A Bf : Set X}
    (hlev : {x | x ∈ U ∧ h x = 0} = Bf) (hside : A ∩ U = {x | x ∈ U ∧ h x ≤ 0}) :
    ∃ near : TopologicalSpace.Opens W.Carrier,
      (near : Set W.Carrier) ⊆ W.interior ∧
      ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (h ∘ φ.symm) near ∧
      (∀ x ∈ near, (h ∘ φ.symm) x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) (h ∘ φ.symm) x ≠ 0) ∧
      φ '' Bf = {x | x ∈ near ∧ (h ∘ φ.symm) x = 0} ∧
      φ '' A ∩ near = {x | x ∈ near ∧ (h ∘ φ.symm) x ≤ 0} := by
  have hnear : IsOpen (φ '' U) := φ.toHomeomorph.isOpenMap _ hU
  have hmem : ∀ y, y ∈ φ '' U ↔ φ.symm y ∈ U := fun y => by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨φ.symm y, hy, by simp⟩
  refine ⟨⟨φ '' U, hnear⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro y _
    have : BoundarylessManifold W.model W.Carrier :=
      ModelWithCorners.Boundaryless.of_boundary_eq_empty hW
    exact BoundarylessManifold.isInteriorPoint
  · exact hh.comp φ.symm.contMDiff.contMDiffOn (fun y hy => (hmem y).1 hy)
  · rintro y hy - hz
    have hyU : φ.symm y ∈ U := (hmem y).1 hy
    have h1 : MDifferentiableAt I3 𝓘(ℝ, ℝ) h (φ.symm y) :=
      (hh.contMDiffAt (hU.mem_nhds hyU)).mdifferentiableAt (by simp)
    have h2 : MDifferentiableAt W.model I3 φ.symm y := φ.symm.mdifferentiable (by simp) _
    have hsurj : Surjective (mfderiv W.model 𝓘(ℝ, ℝ) (h ∘ φ.symm) y) := by
      rw [mfderiv_comp y h1 h2, ContinuousLinearMap.coe_comp]
      exact Surjective.comp (hs _ hyU) (mfderiv_diffeo_bijective_R74 φ.symm y).2
    obtain ⟨v, hv⟩ := hsurj 1
    rw [hz] at hv
    exact zero_ne_one (α := ℝ) hv
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ {x | x ∈ U ∧ h x = 0} := hlev ▸ hx
      exact ⟨⟨x, hx'.1, rfl⟩, by simpa using hx'.2⟩
    · rintro ⟨hy, hy0⟩
      have hyU := (hmem y).1 hy
      refine ⟨φ.symm y, hlev ▸ ⟨hyU, hy0⟩, by simp⟩
  · ext y
    constructor
    · rintro ⟨⟨x, hxA, rfl⟩, hy⟩
      have hxU : x ∈ U := by simpa using (hmem _).1 hy
      have : x ∈ {x | x ∈ U ∧ h x ≤ 0} := hside ▸ ⟨hxA, hxU⟩
      exact ⟨hy, by simpa using this.2⟩
    · rintro ⟨hy, hy0⟩
      have hyU := (hmem y).1 hy
      have : φ.symm y ∈ A ∩ U := hside ▸ ⟨hyU, hy0⟩
      exact ⟨⟨φ.symm y, this.1, by simp⟩, hy⟩

end Free

section Arcs

variable {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W} {Cu : CuspCores W E}

/-- **`ArcEnds74` from end-by-end data, with a property of the free end functions**: for each
end `b` a classification, a defining function and a neighbourhood with the clauses of
`ArcEnds74`, and for a free end the property `Q b fn`; the produced record satisfies `Q b` at the
end function of every free end. -/
theorem ArcEnds74.exists_of_ends2_OCL {pieceSet : Set W.Carrier}
    {slice : Bool → Set W.Carrier} (Q : Bool → (W.Carrier → ℝ) → Prop)
    (h : ∀ b : Bool, ∃ (k : Option (NeighbourFace Z Cu)) (fn : W.Carrier → ℝ)
        (near : TopologicalSpace.Opens W.Carrier),
      (∀ F, k = some F → slice b = neighbourSet F) ∧
      (k = none → (near : Set W.Carrier) ⊆ W.interior) ∧
      (k = none → ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ fn near) ∧
      (k = none → ∀ x ∈ near, fn x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) fn x ≠ 0) ∧
      (k = none → slice b = {x | x ∈ near ∧ fn x = 0}) ∧
      (k = none → pieceSet ∩ near = {x | x ∈ near ∧ fn x ≤ 0}) ∧
      (k = none → Q b fn)) :
    ∃ ends : ArcEnds74 Z Cu pieceSet slice, ∀ b, ends.kind b = none → Q b (ends.fn b) := by
  choose k fn near h1 h2 h3 h4 h5 h6 h7 using h
  exact ⟨{
    kind := k
    fn := fn
    near := near
    shared_eq := fun b F hk => h1 b F hk
    near_interior := fun b hk => h2 b hk
    fn_smooth := fun b hk => h3 b hk
    fn_regular := fun b hk => h4 b hk
    fn_level := fun b hk => h5 b hk
    fn_eq := fun b hk => h6 b hk }, fun b hk => h7 b hk⟩

end Arcs

end GC.GraphManifold.Assembly.FC39P0
