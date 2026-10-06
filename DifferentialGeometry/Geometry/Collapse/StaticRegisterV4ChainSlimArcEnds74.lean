import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimPieceExit74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimLoopExitsOfDiffeo74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimArcPieces74

/-!
# Draft 74, S0 on the member: arc exits from a product map and the end data

Lane C14-REG-CHAIN (by S-REG-CHAIN4), G35 (kernel part). Transport of S-ZSP04's arc data to `W`
along the carrier diffeomorphism `φ : X ≃ₘ W` (`M.ψ`, `W` without boundary):

* `SphereArcExit74.ofProduct74` / `TorusArcExit74.ofProduct74`: the exit of the arc `φ ∘ m` of a
  smooth injective full-rank product map `m` into `X` (the record `ends` is an argument);
* `ArcEnds74.exists_of_ends74`: `ArcEnds74` from end-by-end data;
* `exists_freeEnd74`: the free end data (`near`, `fn` and the five clauses) of an `X`-side regular
  defining function `h` on an open `U` (`near = φ(U)`, `fn = h ∘ φ⁻¹`).
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
/-- **The free end data of a regular defining function.** An open `U ⊆ X` with a function `h`,
smooth on `U` with onto differential, `{h = 0} ∩ U = Bf` and `A ∩ U = {h ≤ 0} ∩ U`, gives on a
carrier without boundary the open set `φ(U)` and the function `h ∘ φ⁻¹` with the clauses of a
free end of an arc (`near_interior`, `fn_smooth`, `fn_regular`, `fn_level`, `fn_eq`). -/
theorem exists_freeEnd74 (φ : X ≃ₘ⟮I3, W.model⟯ W.Carrier)
    (hW : W.model.boundary W.Carrier = ∅) {U : Set X} {h : X → ℝ} (hU : IsOpen U)
    (hh : ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ h U)
    (hs : ∀ x ∈ U, Surjective (mfderiv I3 𝓘(ℝ, ℝ) h x)) {A Bf : Set X}
    (hlev : {x | x ∈ U ∧ h x = 0} = Bf) (hside : A ∩ U = {x | x ∈ U ∧ h x ≤ 0}) :
    ∃ (fn : W.Carrier → ℝ) (near : TopologicalSpace.Opens W.Carrier),
      (near : Set W.Carrier) ⊆ W.interior ∧ ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ fn near ∧
      (∀ x ∈ near, fn x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) fn x ≠ 0) ∧
      φ '' Bf = {x | x ∈ near ∧ fn x = 0} ∧
      φ '' A ∩ near = {x | x ∈ near ∧ fn x ≤ 0} := by
  have hnear : IsOpen (φ '' U) := φ.toHomeomorph.isOpenMap _ hU
  have hmem : ∀ y, y ∈ φ '' U ↔ φ.symm y ∈ U := fun y => by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨φ.symm y, hy, by simp⟩
  refine ⟨h ∘ φ.symm, ⟨φ '' U, hnear⟩, ?_, ?_, ?_, ?_, ?_⟩
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

/-- **`ArcEnds74` from end-by-end data**: for each end `b` a classification, a defining function
and a neighbourhood with the clauses of `ArcEnds74`. -/
theorem ArcEnds74.exists_of_ends74 {pieceSet : Set W.Carrier} {slice : Bool → Set W.Carrier}
    (h : ∀ b : Bool, ∃ (k : Option (NeighbourFace Z Cu)) (fn : W.Carrier → ℝ)
        (near : TopologicalSpace.Opens W.Carrier),
      (∀ F, k = some F → slice b = neighbourSet F) ∧
      (k = none → (near : Set W.Carrier) ⊆ W.interior) ∧
      (k = none → ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ fn near) ∧
      (k = none → ∀ x ∈ near, fn x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) fn x ≠ 0) ∧
      (k = none → slice b = {x | x ∈ near ∧ fn x = 0}) ∧
      (k = none → pieceSet ∩ near = {x | x ∈ near ∧ fn x ≤ 0})) :
    Nonempty (ArcEnds74 Z Cu pieceSet slice) := by
  choose k fn near h1 h2 h3 h4 h5 h6 using h
  exact ⟨{
    kind := k
    fn := fn
    near := near
    shared_eq := fun b F hk => h1 b F hk
    near_interior := fun b hk => h2 b hk
    fn_smooth := fun b hk => h3 b hk
    fn_regular := fun b hk => h4 b hk
    fn_level := fun b hk => h5 b hk
    fn_eq := fun b hk => h6 b hk }⟩

omit [IsManifold I3 ∞ X] in
/-- **The sphere arc exit of a product map**: `φ ∘ m` with the given end data. -/
def SphereArcExit74.ofProduct74 (φ : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier)
    (m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → X)
    (hm : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ m)
    (hmi : ∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) m z)) (hinj : Injective m)
    (ends : ArcEnds74 Z Cu (range (φ ∘ m)) fun b => range fun z => (φ ∘ m) (z, iccEnd b)) :
    SphereArcExit74 Z Cu where
  F := φ ∘ m
  smooth := φ.contMDiff.comp hm
  injective := φ.injective.comp hinj
  fullRank := fun z => (sphereArc_bijective_comp_R74 φ hm hmi z).1
  ends := ends

omit [IsManifold I3 ∞ X] in
/-- **The torus arc exit of a product map**: `φ ∘ m` with the given end data. -/
def TorusArcExit74.ofProduct74 (φ : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier)
    (m : Torus × Icc (0 : ℝ) 1 → X)
    (hm : ContMDiff (torusModel.prod (𝓡∂ 1)) (𝓡 3) ∞ m)
    (hmi : ∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) (𝓡 3) m z)) (hinj : Injective m)
    (ends : ArcEnds74 Z Cu (range (φ ∘ m)) fun b => range fun z => (φ ∘ m) (z, iccEnd b)) :
    TorusArcExit74 Z Cu where
  F := φ ∘ m
  smooth := φ.contMDiff.comp hm
  injective := φ.injective.comp hinj
  fullRank := fun z => (torusArc_bijective_comp_R74 φ hm hmi z).1
  ends := ends

end Arcs

section Product

open DifferentialGeometry.Topology.Ehresmann

variable {F : Type*} [TopologicalSpace F] {EF HF : Type*} [NormedAddCommGroup EF]
  [NormedSpace ℝ EF] [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} [ChartedSpace HF F]
  {ι : Type*} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {Bs : Set H}
  {Pr : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) X ι Bs} {γ : SmoothEmbeddedBaseArc_EFE Bs}

omit [IsManifold I3 ∞ X] in
/-- **The end slices of an interval product are the whole end fibres.** -/
theorem wholeProduct_range_end74
    {F₀ : StandardWholeSurfaceFibre_EFE Pr IF F (γ.toFun 0)}
    (Wp : WholeSurfaceIntervalProduct_EFE Pr γ F₀) (b : Bool) :
    range (fun z : F => Wp.map (z, iccEnd b)) = Pr.toFun ⁻¹' {γ.toFun (iccEnd b)} := by
  cases b
  · change range (fun x => Wp.map (x, ⟨0, left_mem_Icc.mpr zero_le_one⟩)) = _
    rw [funext Wp.start_eq]
    exact F₀.range_eq
  · exact Wp.end_range

omit [IsManifold I3 ∞ X] in
/-- The end slice of the carried product map is the `φ`-image of the whole end fibre. -/
theorem wholeProduct_range_end_comp74
    {F₀ : StandardWholeSurfaceFibre_EFE Pr IF F (γ.toFun 0)}
    (Wp : WholeSurfaceIntervalProduct_EFE Pr γ F₀) (φ : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier)
    (b : Bool) :
    range (fun z : F => (φ ∘ Wp.map) (z, iccEnd b)) =
      φ '' (Pr.toFun ⁻¹' {γ.toFun (iccEnd b)}) := by
  rw [← wholeProduct_range_end74 Wp b, ← range_comp]
  rfl

omit [IsManifold I3 ∞ X] in
/-- The range of the carried product map is the `φ`-image of the whole preimage of the arc. -/
theorem wholeProduct_range_comp74
    {F₀ : StandardWholeSurfaceFibre_EFE Pr IF F (γ.toFun 0)}
    (Wp : WholeSurfaceIntervalProduct_EFE Pr γ F₀) (φ : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) :
    range (φ ∘ Wp.map) = φ '' (Pr.toFun ⁻¹' (γ.toFun '' Icc 0 1)) := by
  rw [range_comp, Wp.range_eq]

end Product

end GC.GraphManifold.Assembly.FC39P0
