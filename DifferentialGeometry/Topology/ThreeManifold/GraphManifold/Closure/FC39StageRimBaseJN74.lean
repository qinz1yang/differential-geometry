import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryH74

/-!
# Draft 74, the labelled rim base (fields `rimBase`, `rim_fibre` of `JunctionRimFacts74`)

Lane S-JUNCTIONS (by S-JUNCTIONS3), G13 (suffix `_JN74`). A plain-data transport of EDP06's
equality "the whole rim over a point of `C₂` is a whole circle fibre" to the rows' bundles:

* `edgeBundle74_rim_eq_JN74`: the rim of the restricted edge bundle over `c` is
  `ψ({q₁ = ι c, H = level})`, from the identification of the edge stage with `q₁`
  (`ι ∘ proj = q₁ ∘ ψ⁻¹` on the parent, `ι` injective, points below the level over the edge base
  lie in the parent);
* `circleBundle74_fibre_eq_JN74`: the circle fibre over `b` is `ψ(q₀⁻¹(ι b))`;
* **`exists_rimBase_JN74`**: if over every point of `C₂` the rim set `{q₁ = ι c, H = level}` is a
  whole fibre `q₀⁻¹(ι b)` (EDP06, G5's `edp06_rim_eq_whole_fibre_EFE`), there is a map `rimBase`
  with `rim c = fibre (rimBase c)` on `cbase`; for `C₂ = ∅` the edge base is empty so no choice is
  needed.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
  {A : SmoothStageGeometry74 W E} (D : StageCutChoice74 A)
  {X Bs : Type*} (ψ : X ≃ W.Carrier) (q1 q0 : X → Bs) (ιe : A.edge.Base → Bs)
  (ιc : A.circle.Base → Bs) (H : X → ℝ)

/-- **The rim of the restricted edge bundle over `c` is `ψ({q₁ = ι c, H = level})`.** -/
theorem edgeBundle74_rim_eq_JN74 (F : EdgeCutFacts74 A D)
    (hproj : ∀ x : A.edge.parent, ιe (A.edge.proj x) = q1 (ψ.symm x))
    (hinj : Function.Injective ιe)
    (hpar : ∀ y, q1 y ∈ ιe '' (D.edgeBaseOpen : Set A.edge.Base) → H y ≤ A.edge.level →
      (ψ y) ∈ A.edge.parent)
    (hH : ∀ x : A.edge.parent, A.edge.height x = H (ψ.symm x)) (c : D.edgeBaseOpen) :
    (edgeBundle74 A D F).rim c = ψ '' {y | q1 y = ιe c.1 ∧ H y = A.edge.level} := by
  ext z
  constructor
  · rintro ⟨x, ⟨hp, hh⟩, rfl⟩
    have hxp : (x : W.Carrier) ∈ A.edge.parent := A.edge.restrictParent_le _ x.2
    have h1 : A.edge.proj ⟨x, hxp⟩ = c.1 := congrArg Subtype.val hp
    have h2 : A.edge.height ⟨x, hxp⟩ = A.edge.level := hh
    refine ⟨ψ.symm x, ⟨?_, ?_⟩, ψ.apply_symm_apply x⟩
    · rw [← hproj ⟨x, hxp⟩, h1]
    · rw [← hH ⟨x, hxp⟩]
      exact h2
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    have hpy : ψ y ∈ A.edge.parent :=
      hpar y (h1 ▸ ⟨c.1, c.2, rfl⟩) (le_of_eq h2)
    have hproj' : A.edge.proj ⟨ψ y, hpy⟩ = c.1 := by
      apply hinj
      rw [hproj ⟨ψ y, hpy⟩, ψ.symm_apply_apply, h1]
    have hsrc : ψ y ∈ D.edgeSource :=
      A.edge.mem_restrictParent_of hpy (by rw [hproj']; exact c.2)
    refine ⟨⟨ψ y, hsrc⟩, ⟨Subtype.ext hproj', ?_⟩, rfl⟩
    change A.edge.height ⟨ψ y, hpy⟩ = A.edge.level
    rw [hH ⟨ψ y, hpy⟩, ψ.symm_apply_apply]
    exact h2

/-- **The circle fibre of the restricted circle bundle over `b` is `ψ(q₀⁻¹(ι b))`.** -/
theorem circleBundle74_fibre_eq_JN74 (G : CircleCutFacts74 A D)
    (hproj : ∀ x : A.circle.parent, ιc (A.circle.proj x) = q0 (ψ.symm x))
    (hinj : Function.Injective ιc)
    (hpar : ∀ y, q0 y ∈ range ιc → ψ y ∈ A.circle.parent) (b : D.circleBaseOpen) :
    (circleBundle74 A D G).fibre b = ψ '' (q0 ⁻¹' {ιc b.1}) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxp : (x : W.Carrier) ∈ A.circle.parent := A.circle.restrictParent_le _ x.2
    have h1 : A.circle.proj ⟨x, hxp⟩ = b.1 := congrArg Subtype.val hx
    refine ⟨ψ.symm x, ?_, ψ.apply_symm_apply x⟩
    rw [mem_preimage, mem_singleton_iff, ← hproj ⟨x, hxp⟩, h1]
  · rintro ⟨y, hy, rfl⟩
    have hy' : q0 y = ιc b.1 := hy
    have hpy : ψ y ∈ A.circle.parent := hpar y (hy' ▸ ⟨b.1, rfl⟩)
    have hproj' : A.circle.proj ⟨ψ y, hpy⟩ = b.1 := by
      apply hinj
      rw [hproj ⟨ψ y, hpy⟩, ψ.symm_apply_apply, hy']
    have hsrc : ψ y ∈ D.circleSource :=
      A.circle.mem_restrictParent_of hpy (by rw [hproj']; exact b.2)
    exact ⟨⟨ψ y, hsrc⟩, Subtype.ext hproj', rfl⟩

/-- **The labelled rim base**: if over every point of `C₂` the rim `{q₁ = ι c, H = level}` is a
whole `q₀`-fibre `q₀⁻¹(ι b)` with `b` in the circle base, there is `rimBase` with
`rim c = fibre (rimBase c)` for `c ∈ cbase`. -/
theorem exists_rimBase_JN74 (F : EdgeCutFacts74 A D) (G : CircleCutFacts74 A D)
    (hprojE : ∀ x : A.edge.parent, ιe (A.edge.proj x) = q1 (ψ.symm x))
    (hinjE : Function.Injective ιe)
    (hparE : ∀ y, q1 y ∈ ιe '' (D.edgeBaseOpen : Set A.edge.Base) → H y ≤ A.edge.level →
      (ψ y) ∈ A.edge.parent)
    (hH : ∀ x : A.edge.parent, A.edge.height x = H (ψ.symm x))
    (hprojC : ∀ x : A.circle.parent, ιc (A.circle.proj x) = q0 (ψ.symm x))
    (hinjC : Function.Injective ιc)
    (hparC : ∀ y, q0 y ∈ range ιc → ψ y ∈ A.circle.parent)
    (hrim : ∀ c : D.edgeBaseOpen, c.1 ∈ D.C₂ → ∃ b : D.circleBaseOpen,
      {y | q1 y = ιe c.1 ∧ H y = A.edge.level} = q0 ⁻¹' {ιc b.1}) :
    ∃ rimBase : (edgeBundle74 A D F).Base → (circleBundle74 A D G).Base,
      ∀ c ∈ (edgeBundle74 A D F).cbase,
        (edgeBundle74 A D F).rim c = (circleBundle74 A D G).fibre (rimBase c) := by
  classical
  by_cases hC : D.C₂ = ∅
  · have hbot := D.edgeBaseOpen_empty hC
    have hE : IsEmpty D.edgeBaseOpen := by
      refine ⟨fun c => ?_⟩
      obtain ⟨z, hz⟩ := c
      rw [hbot] at hz
      exact hz
    have : IsEmpty (edgeBundle74 A D F).Base := hE
    exact ⟨fun c => isEmptyElim c, fun c => isEmptyElim c⟩
  · obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.2 hC
    obtain ⟨b₀, -⟩ := hrim ⟨w, D.C₂_sub hw⟩ hw
    refine ⟨fun c => if h : c.1 ∈ D.C₂ then Classical.choose (hrim c h) else b₀, fun c hc => ?_⟩
    have hc' : c.1 ∈ D.C₂ := hc
    have hdef : (if h : c.1 ∈ D.C₂ then Classical.choose (hrim c h) else b₀) =
        Classical.choose (hrim c hc') := by
      simp only [hc', ↓reduceDIte]
    have h1 := edgeBundle74_rim_eq_JN74 D ψ q1 ιe H F hprojE hinjE hparE hH c
    have h2 := circleBundle74_fibre_eq_JN74 D ψ q0 ιc G hprojC hinjC hparC
      (Classical.choose (hrim c hc'))
    have h3 : {y | q1 y = ιe c.1 ∧ H y = A.edge.level} =
        q0 ⁻¹' {ιc (Classical.choose (hrim c hc')).1} := Classical.choose_spec (hrim c hc')
    refine h1.trans ?_
    rw [h3]
    refine h2.symm.trans ?_
    exact congrArg (circleBundle74 A D G).fibre hdef.symm

end GC.GraphManifold.Assembly.FC39P0
