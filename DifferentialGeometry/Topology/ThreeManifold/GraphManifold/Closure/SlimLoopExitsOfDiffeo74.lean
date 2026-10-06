import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimLoopModel74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransport74
import DifferentialGeometry.Topology.Embedding.CrossModelHalfSpaceOCX
import DifferentialGeometry.Topology.Manifold.SubmersionOpenMap

/-!
# Draft 74, S1 (loops): the loop exits of the slim stage from the source side

Lane C14-REG-CHAIN (by S-REG-CHAIN3), G33. S-ZSP04's circle branch (`slim_loop_circle_ZSP35`, S1)
lives on the original source `X` (model `𝓘(ℝ, E3)`): over a loop of `D₃` the whole preimage `O`
is open and compact, `p : X → S¹` is smooth with onto differential on `O`, and the fibre over `1`
is the range of a standard `S²` / `T²`. This file moves it to the member `W` along the carrier
diffeomorphism `ψ : X ≃ W` (`M.ψ`) and produces the exit records of S-JUNCTIONS (G4):

* `isPreconnected_of_circleSubmersion74` (X-side): an open compact `O` with a circle-valued
  submersion `p` whose fibre over `1` is preconnected is preconnected (the image of the
  complementary clopen part under `p` would be a proper clopen subset of `S¹`);
* `isSmoothEmbedding_sphere_comp_carrier74` / `…_torus_…`: a smooth embedding of the standard
  surface into `X` followed by `ψ` (a carrier of either kind; O-CROSS' `…toHalfSpace_OCX`);
* `loopRegionOfDiffeo74`, `SphereLoopExit74.ofDiffeo74`, `TorusLoopExit74.ofDiffeo74`: the region
  `ψ(O)`, `p ∘ ψ⁻¹`, the fibre `ψ ∘ emb`, on a carrier with empty boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

section Connected

variable {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]

omit [IsManifold I3 ∞ X] in
/-- **Connectedness from a circle-valued submersion** (X-side): an open compact `O ⊆ X` with
`p : X → S¹` smooth on `O` with onto differential and preconnected fibre `{x ∈ O | p x = 1}` is
preconnected. -/
theorem isPreconnected_of_circleSubmersion74 {O : Set X} (hO : IsOpen O) (hc : IsCompact O)
    {p : X → Circle} (hp : ContMDiffOn I3 (𝓡 1) ∞ p O)
    (hsub : ∀ x ∈ O, Surjective (mfderiv I3 (𝓡 1) p x))
    (hF : IsPreconnected {x | x ∈ O ∧ p x = 1}) : IsPreconnected O := by
  have hopen := (isOpenMap_of_mfderiv_surjective (hp.of_le (by norm_num)) hO hsub).1
  -- the image of a compact open part is clopen in the circle
  have key : ∀ u v : Set X, IsOpen u → IsOpen v → O ⊆ u ∪ v → O ∩ (u ∩ v) = ∅ →
      {x | x ∈ O ∧ p x = 1} ⊆ u → O ⊆ u := by
    intro u v hu hv hcov hdis hFu
    set A : Set X := O ∩ vᶜᶜ with hA
    have hAeq : O ∩ v = O \ u := by
      ext x
      constructor
      · rintro ⟨hxO, hxv⟩
        refine ⟨hxO, fun hxu => ?_⟩
        have : x ∈ O ∩ (u ∩ v) := ⟨hxO, hxu, hxv⟩
        rw [hdis] at this
        exact this
      · rintro ⟨hxO, hxu⟩
        exact ⟨hxO, (hcov hxO).resolve_left hxu⟩
    have hAopen : IsOpen (O ∩ v) := hO.inter hv
    have hAcomp : IsCompact (O ∩ v) := by
      rw [hAeq]
      exact hc.diff hu
    -- `p` maps `O ∩ v` onto a clopen subset of the circle
    have himg : IsOpen (p '' (O ∩ v)) := by
      have h1 : IsOpen ((Subtype.val : O → X) ⁻¹' (O ∩ v)) := hAopen.preimage continuous_subtype_val
      have h2 := hopen _ h1
      have h3 : (O.domRestrict p) '' ((Subtype.val : O → X) ⁻¹' (O ∩ v)) = p '' (O ∩ v) := by
        ext y
        constructor
        · rintro ⟨⟨x, hxO⟩, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨x, hx.1⟩, hx, rfl⟩
      rwa [h3] at h2
    have hclosed : IsClosed (p '' (O ∩ v)) := by
      have hcp : ContinuousOn p (O ∩ v) :=
        (hp.continuousOn).mono inter_subset_left
      exact (hAcomp.image_of_continuousOn hcp).isClosed
    rcases isClopen_iff.mp ⟨hclosed, himg⟩ with hempty | huniv
    · intro x hx
      rcases hcov hx with hxu | hxv
      · exact hxu
      · have : p x ∈ p '' (O ∩ v) := ⟨x, ⟨hx, hxv⟩, rfl⟩
        rw [hempty] at this
        exact this.elim
    · exfalso
      have h1 : (1 : Circle) ∈ p '' (O ∩ v) := by rw [huniv]; trivial
      obtain ⟨a, ⟨haO, hav⟩, hap⟩ := h1
      have hau : a ∈ u := hFu ⟨haO, hap⟩
      have : a ∈ O ∩ (u ∩ v) := ⟨haO, hau, hav⟩
      rw [hdis] at this
      exact this
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdis
  by_cases hFu : {x | x ∈ O ∧ p x = 1} ⊆ u
  · exact Or.inl (key u v hu hv hcov hdis hFu)
  · have hFv : {x | x ∈ O ∧ p x = 1} ⊆ v := by
      rcases isPreconnected_iff_subset_of_disjoint.mp hF u v hu hv (fun x hx => hcov hx.1) (by
        rw [← subset_empty_iff]
        intro x hx
        have : x ∈ O ∩ (u ∩ v) := ⟨hx.1.1, hx.2⟩
        rw [hdis] at this
        exact this) with h | h
      · exact absurd h hFu
      · exact h
    exact Or.inr (key v u hv hu (by rwa [union_comm]) (by rwa [inter_comm v u]) hFv)

end Connected

section Transport

variable {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
  {W : CompactCarrier.{0}}

omit [IsManifold I3 ∞ X] in
/-- **A boundaryless-modelled embedding followed by the carrier diffeomorphism** (either carrier
kind; the source model needs one nonzero range-preserving translation `s₀`). -/
theorem isSmoothEmbedding_comp_carrier_shift74 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] (s₀ : E)
    (hs₀ : s₀ ≠ 0) (hs₀I : ∀ v, v + s₀ ∈ range I ↔ v ∈ range I)
    (ψ : X ≃ₘ⟮I3, W.model⟯ W.Carrier) {φ : M → X} (hφ : IsSmoothEmbedding I I3 ∞ φ) :
    IsSmoothEmbedding I W.model ∞ (ψ ∘ φ) := by
  cases W with
  | mk k C o =>
    cases k
    · exact hφ.diffeomorph_comp ψ
    · exact hφ.diffeomorph_comp_toHalfSpace_OCX s₀ hs₀ hs₀I ψ

omit [IsManifold I3 ∞ X] in
/-- The standard sphere embedded in `X` followed by `ψ` is a smooth embedding into `W`. -/
theorem isSmoothEmbedding_sphere_comp_carrier74 (ψ : X ≃ₘ⟮I3, W.model⟯ W.Carrier)
    {φ : ClosureSphere.{0} → X} (hφ : IsSmoothEmbedding (𝓡 2) I3 ∞ φ) :
    IsSmoothEmbedding (𝓡 2) W.model ∞ (ψ ∘ φ) :=
  isSmoothEmbedding_comp_carrier_shift74 (EuclideanSpace.single 0 1)
    (by
      intro h
      have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
      simp at h1)
    (fun v => modelWithCornersSelf_shift_range_OCX _) ψ hφ

omit [IsManifold I3 ∞ X] in
/-- The standard torus embedded in `X` followed by `ψ` is a smooth embedding into `W`. -/
theorem isSmoothEmbedding_torus_comp_carrier74 (ψ : X ≃ₘ⟮I3, W.model⟯ W.Carrier)
    {φ : Torus → X} (hφ : IsSmoothEmbedding torusModel I3 ∞ φ) :
    IsSmoothEmbedding torusModel W.model ∞ (ψ ∘ φ) :=
  isSmoothEmbedding_comp_carrier_shift74
    ((EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)), 0)
    (by
      intro h
      have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
        v.1 0) h
      simp at h1)
    (fun v => prod_shift_range_OCX (fun w => modelWithCornersSelf_shift_range_OCX _)) ψ hφ

variable (ψ : X ≃ₘ⟮I3, W.model⟯ W.Carrier) (hW : W.model.boundary W.Carrier = ∅)

/-- **The loop region `ψ(O)`** of an open compact preconnected `O ⊆ X` on a carrier with empty
boundary. -/
def loopRegionOfDiffeo74 {O : Set X} (hO : IsOpen O) (hc : IsCompact O)
    (hconn : IsPreconnected O) : LoopRegion74 W where
  O := ψ '' O
  isClopen := ⟨(hc.image ψ.continuous).isClosed, ψ.toHomeomorph.isOpenMap _ hO⟩
  interior := fun y _ => by
    have : BoundarylessManifold W.model W.Carrier :=
      ModelWithCorners.Boundaryless.of_boundary_eq_empty hW
    exact BoundarylessManifold.isInteriorPoint
  connected := hconn.image _ ψ.continuous.continuousOn

omit [IsManifold I3 ∞ X] in
/-- The circle map `p ∘ ψ⁻¹` is smooth with onto differential on `ψ(O)`. -/
theorem loopProjOfDiffeo74_smooth {O : Set X} {p : X → Circle}
    (hp : ContMDiffOn I3 (𝓡 1) ∞ p O) :
    ContMDiffOn W.model (𝓡 1) ∞ (p ∘ ψ.symm) (ψ '' O) :=
  hp.comp ψ.symm.contMDiff.contMDiffOn (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx)

omit [IsManifold I3 ∞ X] in
theorem loopProjOfDiffeo74_sub {O : Set X} (hO : IsOpen O) {p : X → Circle}
    (hp : ContMDiffOn I3 (𝓡 1) ∞ p O) (hsub : ∀ x ∈ O, Surjective (mfderiv I3 (𝓡 1) p x))
    (y : W.Carrier) (hy : y ∈ ψ '' O) :
    Surjective (mfderiv W.model (𝓡 1) (p ∘ ψ.symm) y) := by
  have hyO : ψ.symm y ∈ O := by
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  have h1 : MDifferentiableAt I3 (𝓡 1) p (ψ.symm y) :=
    (hp.contMDiffAt (hO.mem_nhds hyO)).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt W.model I3 ψ.symm y := ψ.symm.mdifferentiable (by simp) _
  rw [mfderiv_comp y h1 h2, ContinuousLinearMap.coe_comp]
  exact Surjective.comp (hsub _ hyO) (mfderiv_diffeo_bijective_R74 ψ.symm y).2

/-- **The sphere loop exit from the source side.** -/
def SphereLoopExit74.ofDiffeo74 {O : Set X} (hO : IsOpen O) (hc : IsCompact O)
    (hconn : IsPreconnected O) {p : X → Circle} (hp : ContMDiffOn I3 (𝓡 1) ∞ p O)
    (hsub : ∀ x ∈ O, Surjective (mfderiv I3 (𝓡 1) p x)) {emb : ClosureSphere.{0} → X}
    (hemb : IsSmoothEmbedding (𝓡 2) I3 ∞ emb) (hrange : range emb = {x | x ∈ O ∧ p x = 1}) :
    SphereLoopExit74 W where
  region := loopRegionOfDiffeo74 ψ hW hO hc hconn
  p := p ∘ ψ.symm
  fibre := ψ ∘ emb
  p_smooth := loopProjOfDiffeo74_smooth ψ hp
  p_sub := loopProjOfDiffeo74_sub ψ hO hp hsub
  fibre_embedding := isSmoothEmbedding_sphere_comp_carrier74 ψ hemb
  fibre_range := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      have hz : emb z ∈ {x | x ∈ O ∧ p x = 1} := hrange ▸ mem_range_self z
      exact ⟨⟨emb z, hz.1, rfl⟩, by simpa using hz.2⟩
    · rintro ⟨⟨x, hxO, rfl⟩, hp1⟩
      have hx : x ∈ range emb := by
        rw [hrange]
        exact ⟨hxO, by simpa using hp1⟩
      obtain ⟨z, rfl⟩ := hx
      exact ⟨z, rfl⟩

/-- **The torus loop exit from the source side.** -/
def TorusLoopExit74.ofDiffeo74 {O : Set X} (hO : IsOpen O) (hc : IsCompact O)
    (hconn : IsPreconnected O) {p : X → Circle} (hp : ContMDiffOn I3 (𝓡 1) ∞ p O)
    (hsub : ∀ x ∈ O, Surjective (mfderiv I3 (𝓡 1) p x)) {emb : Torus → X}
    (hemb : IsSmoothEmbedding torusModel I3 ∞ emb) (hrange : range emb = {x | x ∈ O ∧ p x = 1}) :
    TorusLoopExit74 W where
  region := loopRegionOfDiffeo74 ψ hW hO hc hconn
  p := p ∘ ψ.symm
  fibre := ψ ∘ emb
  p_smooth := loopProjOfDiffeo74_smooth ψ hp
  p_sub := loopProjOfDiffeo74_sub ψ hO hp hsub
  fibre_embedding := isSmoothEmbedding_torus_comp_carrier74 ψ hemb
  fibre_range := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      have hz : emb z ∈ {x | x ∈ O ∧ p x = 1} := hrange ▸ mem_range_self z
      exact ⟨⟨emb z, hz.1, rfl⟩, by simpa using hz.2⟩
    · rintro ⟨⟨x, hxO, rfl⟩, hp1⟩
      have hx : x ∈ range emb := by
        rw [hrange]
        exact ⟨hxO, by simpa using hp1⟩
      obtain ⟨z, rfl⟩ := hx
      exact ⟨z, rfl⟩

omit [IsManifold I3 ∞ X] in
/-- The region of the sphere loop exit is `ψ(O)`. -/
theorem SphereLoopExit74.ofDiffeo74_O {O : Set X} (hO : IsOpen O) (hc : IsCompact O)
    (hconn : IsPreconnected O) {p : X → Circle} (hp : ContMDiffOn I3 (𝓡 1) ∞ p O)
    (hsub : ∀ x ∈ O, Surjective (mfderiv I3 (𝓡 1) p x)) {emb : ClosureSphere.{0} → X}
    (hemb : IsSmoothEmbedding (𝓡 2) I3 ∞ emb) (hrange : range emb = {x | x ∈ O ∧ p x = 1}) :
    (SphereLoopExit74.ofDiffeo74 ψ hW hO hc hconn hp hsub hemb hrange).region.O = ψ '' O :=
  rfl

omit [IsManifold I3 ∞ X] in
/-- The region of the torus loop exit is `ψ(O)`. -/
theorem TorusLoopExit74.ofDiffeo74_O {O : Set X} (hO : IsOpen O) (hc : IsCompact O)
    (hconn : IsPreconnected O) {p : X → Circle} (hp : ContMDiffOn I3 (𝓡 1) ∞ p O)
    (hsub : ∀ x ∈ O, Surjective (mfderiv I3 (𝓡 1) p x)) {emb : Torus → X}
    (hemb : IsSmoothEmbedding torusModel I3 ∞ emb) (hrange : range emb = {x | x ∈ O ∧ p x = 1}) :
    (TorusLoopExit74.ofDiffeo74 ψ hW hO hc hconn hp hsub hemb hrange).region.O = ψ '' O :=
  rfl

end Transport

end GC.GraphManifold.Assembly
