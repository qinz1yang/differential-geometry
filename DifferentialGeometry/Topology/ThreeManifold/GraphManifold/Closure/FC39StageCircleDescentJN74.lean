import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryH74

/-!
# Draft 74, descent of fibre-constant smooth functions along a circle bundle

Lane S-JUNCTIONS (by S-JUNCTIONS3), G16 (suffix `_JN74`). A smooth function `f` on the tube
`R.tube N` of a circle bundle which is constant on the fibres of `R.proj` over `N` is
`hb ∘ R.proj` for a smooth `hb` on `N` (the section is the local trivialization at `1 ∈ S¹`):
`exists_descended_of_fibreConst_JN74`. This is the form in which `T − 4Δ` and the face function
`h_F` descend to the circle base in `CornerDescent74` (layer 1 of D74-14) once their fibre-constancy
is known.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

/-- The local section of a circle bundle at `1 ∈ S¹` in a trivialization over the neighbourhood of
`c`. -/
def CircleBundle.sectionAt_JN74 (R : CircleBundle W) (c : R.Base) :
    R.neighborhood c → W.Carrier :=
  fun b => (((R.trivialization c).symm (b, (1 : Circle))).1 : R.domain).1

theorem CircleBundle.proj_sectionAt_JN74 (R : CircleBundle W) (c : R.Base) (b : R.neighborhood c) :
    ∃ h : R.sectionAt_JN74 c b ∈ R.domain, R.proj ⟨R.sectionAt_JN74 c b, h⟩ = b.1 := by
  refine ⟨((R.trivialization c).symm (b, (1 : Circle))).1.2, ?_⟩
  have h := R.projection_trivialization c ((R.trivialization c).symm (b, (1 : Circle)))
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm

theorem CircleBundle.contMDiff_sectionAt_JN74 (R : CircleBundle W) (c : R.Base) :
    ContMDiff (𝓡 2) W.model ∞ (R.sectionAt_JN74 c) := by
  have h1 : ContMDiff (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞
      (fun b : R.neighborhood c => ((b, (1 : Circle)) : R.neighborhood c × Circle)) :=
    contMDiff_id.prodMk contMDiff_const
  have h2 := (R.trivialization c).symm.contMDiff.comp h1
  exact (contMDiff_subtype_val (I := W.model)).comp
    ((contMDiff_subtype_val (I := W.model)).comp h2)

/-- **A smooth fibre-constant function on the tube descends to a smooth function of the base.** -/
theorem exists_descended_of_fibreConst_JN74 (R : CircleBundle W)
    (N : TopologicalSpace.Opens R.Base) (f : W.Carrier → ℝ)
    (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f (R.tube (N : Set R.Base)))
    (hconst : ∀ x y : R.domain, R.proj x ∈ N → R.proj y = R.proj x → f x.1 = f y.1) :
    ∃ hb : R.Base → ℝ, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ hb N ∧
      ∀ x : R.domain, R.proj x ∈ N → f x.1 = hb (R.proj x) := by
  classical
  let hb : R.Base → ℝ := fun b =>
    if h : ∃ x : R.domain, R.proj x = b then f (Classical.choose h).1 else 0
  have hspec : ∀ x : R.domain, R.proj x ∈ N → f x.1 = hb (R.proj x) := by
    intro x hx
    have h : ∃ y : R.domain, R.proj y = R.proj x := ⟨x, rfl⟩
    change f x.1 = if h : ∃ y : R.domain, R.proj y = R.proj x then f (Classical.choose h).1
      else 0
    simp only [h, ↓reduceDIte]
    exact hconst x _ hx (Classical.choose_spec h)
  refine ⟨hb, ?_, hspec⟩
  refine contMDiffOn_of_locally_contMDiffOn fun b₀ hb₀ => ?_
  refine ⟨(R.neighborhood b₀ : Set R.Base), (R.neighborhood b₀).isOpen, R.mem_neighborhood b₀, ?_⟩
  intro b hb'
  refine ContMDiffAt.contMDiffWithinAt ?_
  have hopen : IsOpen (R.tube (N : Set R.Base)) :=
    R.domain.isOpen.isOpenMap_subtype_val _ (N.isOpen.preimage R.proj.continuous)
  have hsm : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x : R.neighborhood b₀ => f (R.sectionAt_JN74 b₀ x))
      ⟨b, hb'.2⟩ := by
    obtain ⟨h, hproj⟩ := R.proj_sectionAt_JN74 b₀ ⟨b, hb'.2⟩
    have hmem : R.sectionAt_JN74 b₀ ⟨b, hb'.2⟩ ∈ R.tube (N : Set R.Base) :=
      ⟨⟨_, h⟩, by
        change R.proj ⟨_, h⟩ ∈ N
        rw [hproj]
        exact hb'.1, rfl⟩
    exact ((hf.contMDiffAt (hopen.mem_nhds hmem)).comp _
      ((R.contMDiff_sectionAt_JN74 b₀) ⟨b, hb'.2⟩))
  have hev : (fun x : R.neighborhood b₀ => f (R.sectionAt_JN74 b₀ x)) =ᶠ[nhds ⟨b, hb'.2⟩]
      fun x : R.neighborhood b₀ => hb x := by
    have hN : IsOpen {x : R.neighborhood b₀ | x.1 ∈ N} := N.isOpen.preimage continuous_subtype_val
    filter_upwards [hN.mem_nhds hb'.1] with x hx
    obtain ⟨h, hproj⟩ := R.proj_sectionAt_JN74 b₀ x
    have := hspec ⟨_, h⟩ (by
      rw [hproj]
      exact hx)
    rw [this]
    change hb (R.proj ⟨_, h⟩) = hb x.1
    rw [hproj]
  exact contMDiffAt_subtype_iff.mp (hsm.congr_of_eventuallyEq hev.symm)

section Corner

variable {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A}

/-- **`T − 4Δ` descends to the circle base where it is fibre-constant** (consumer: the `Tb` part of
`CornerDescent74`, layer 1 of D74-14): over an open patch `N` of the circle base whose preimage lies
in the edge source and on whose fibres `cornerT` is constant, `cornerT = Tb ∘ proj` for a smooth
`Tb`. -/
theorem cornerT_descends_JN74 (R : StageCutRows74 A D) (N : TopologicalSpace.Opens R.circle.Base)
    (hsrc : ∀ x : R.circle.domain, R.circle.proj x ∈ N → (x : W.Carrier) ∈ R.edge.source)
    (hconst : ∀ x y : R.circle.domain, R.circle.proj x ∈ N → R.circle.proj y = R.circle.proj x →
      R.cornerT x = R.cornerT y) :
    ∃ Tb : R.circle.Base → ℝ, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ Tb N ∧
      ∀ x : R.circle.domain, R.circle.proj x ∈ N → R.cornerT x = Tb (R.circle.proj x) := by
  classical
  let f : W.Carrier → ℝ := fun z =>
    if hz : z ∈ R.edge.source then R.edge.height ⟨z, hz⟩ - R.edge.level else 0
  have hcT : ∀ x : R.circle.domain, (x : W.Carrier) ∈ R.edge.source →
      R.cornerT x = f x.1 := fun x hx => by
    simp only [StageCutRows74.cornerT, f, hx, ↓reduceDIte]
  have hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f (R.circle.tube (N : Set R.circle.Base)) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxs := hsrc x hx
    refine ContMDiffAt.contMDiffWithinAt ?_
    have hsm : ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ (fun y : R.edge.source => f y) ⟨x.1, hxs⟩ := by
      have : (fun y : R.edge.source => f y) =
          fun y => R.edge.height y - R.edge.level := funext fun y => by
        simp only [f, y.2, ↓reduceDIte]
      rw [this]
      exact ((R.edge.height_smooth ⟨x.1, hxs⟩).sub contMDiffAt_const)
    exact (contMDiffAt_subtype_iff (U := R.edge.source) (x := ⟨x.1, hxs⟩)).mp hsm
  obtain ⟨Tb, hTb, hdesc⟩ := exists_descended_of_fibreConst_JN74 R.circle N f hf
    (fun x y hx hy => by
      rw [← hcT x (hsrc x hx), ← hcT y (hsrc y (by rw [hy]; exact hx))]
      exact hconst x y hx hy)
  exact ⟨Tb, hTb, fun x hx => by rw [hcT x (hsrc x hx)]; exact hdesc x hx⟩

end Corner

end GC.GraphManifold.Assembly.FC39P0
