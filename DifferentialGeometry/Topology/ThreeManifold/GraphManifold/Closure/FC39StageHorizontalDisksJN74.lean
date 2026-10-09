import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRimBaseJN74

/-!
# Draft 74, the horizontal disks of the restricted edge bundle

Lane S-JUNCTIONS (by S-JUNCTIONS3), G17 (suffix `_JN74`). Plain-data identification
(same hypotheses as `edgeBundle74_rim_eq_JN74`):

* `edgeBundle74_disk_eq_JN74`: the disk over `c` is `ψ({q₁ = ι c, H ≤ level})`;
* `edgeBundle74_horizontalDisks_eq_JN74`: the horizontal disks `⋃_{e ∈ ∂C₂} disk e` are
  `ψ({q₁ ∈ ι(∂C₂), H ≤ level})`, `∂C₂` the frontier of `cbase` in the good open edge base.
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

/-- **The disk of the restricted edge bundle over `c` is `ψ({q₁ = ι c, H ≤ level})`.** -/
theorem edgeBundle74_disk_eq_JN74 (F : EdgeCutFacts74 A D)
    (hproj : ∀ x : A.edge.parent, ιe (A.edge.proj x) = q1 (ψ.symm x))
    (hinj : Function.Injective ιe)
    (hpar : ∀ y, q1 y ∈ ιe '' (D.edgeBaseOpen : Set A.edge.Base) → H y ≤ A.edge.level →
      (ψ y) ∈ A.edge.parent)
    (hH : ∀ x : A.edge.parent, A.edge.height x = H (ψ.symm x)) (c : D.edgeBaseOpen) :
    (edgeBundle74 A D F).disk c = ψ '' {y | q1 y = ιe c.1 ∧ H y ≤ A.edge.level} := by
  ext z
  constructor
  · rintro ⟨x, ⟨hp, hh⟩, rfl⟩
    have hxp : (x : W.Carrier) ∈ A.edge.parent := A.edge.restrictParent_le _ x.2
    have h1 : A.edge.proj ⟨x, hxp⟩ = c.1 := congrArg Subtype.val hp
    have h2 : A.edge.height ⟨x, hxp⟩ ≤ A.edge.level := hh
    refine ⟨ψ.symm x, ⟨?_, ?_⟩, ψ.apply_symm_apply x⟩
    · rw [← hproj ⟨x, hxp⟩, h1]
    · rw [← hH ⟨x, hxp⟩]
      exact h2
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    have hpy : ψ y ∈ A.edge.parent :=
      hpar y (h1 ▸ ⟨c.1, c.2, rfl⟩) h2
    have hproj' : A.edge.proj ⟨ψ y, hpy⟩ = c.1 := by
      apply hinj
      rw [hproj ⟨ψ y, hpy⟩, ψ.symm_apply_apply, h1]
    have hsrc : ψ y ∈ D.edgeSource :=
      A.edge.mem_restrictParent_of hpy (by rw [hproj']; exact c.2)
    refine ⟨⟨ψ y, hsrc⟩, ⟨Subtype.ext hproj', ?_⟩, rfl⟩
    change A.edge.height ⟨ψ y, hpy⟩ ≤ A.edge.level
    rw [hH ⟨ψ y, hpy⟩, ψ.symm_apply_apply]
    exact h2

/-- **The horizontal disks are `ψ({q₁ ∈ ι(∂C₂), H ≤ level})`.** -/
theorem edgeBundle74_horizontalDisks_eq_JN74 (F : EdgeCutFacts74 A D)
    (hproj : ∀ x : A.edge.parent, ιe (A.edge.proj x) = q1 (ψ.symm x))
    (hinj : Function.Injective ιe)
    (hpar : ∀ y, q1 y ∈ ιe '' (D.edgeBaseOpen : Set A.edge.Base) → H y ≤ A.edge.level →
      (ψ y) ∈ A.edge.parent)
    (hH : ∀ x : A.edge.parent, A.edge.height x = H (ψ.symm x)) :
    (edgeBundle74 A D F).horizontalDisks = ψ '' {y | (∃ c : D.edgeBaseOpen,
      c ∈ frontier (edgeBundle74 A D F).cbase ∧ q1 y = ιe c.1) ∧ H y ≤ A.edge.level} := by
  ext z
  constructor
  · rintro ⟨_, ⟨e, rfl⟩, hz⟩
    have hz' := (Set.ext_iff.1 (edgeBundle74_disk_eq_JN74 D ψ q1 ιe H F hproj hinj hpar hH e.1)
      z).1 hz
    obtain ⟨y, ⟨h1, h2⟩, rfl⟩ := hz'
    exact ⟨y, ⟨⟨e.1, e.2, h1⟩, h2⟩, rfl⟩
  · rintro ⟨y, ⟨⟨c, hc, h1⟩, h2⟩, rfl⟩
    refine mem_iUnion.mpr ⟨⟨c, hc⟩, ?_⟩
    exact (Set.ext_iff.1 (edgeBundle74_disk_eq_JN74 D ψ q1 ιe H F hproj hinj hpar hH c) _).2
      ⟨y, ⟨h1, h2⟩, rfl⟩

end GC.GraphManifold.Assembly.FC39P0
