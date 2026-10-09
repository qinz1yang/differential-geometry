/- Ported for the team Lake library; proof bodies and declaration names retained.
Module imports, diagnostic #print commands, and original autoImplicit setting adapted. See docs/geometrization/BASELINE_PROVENANCE.json. -/
/- GC revision197 compatibility port: restore legacy definitional transparency for Lean4.33.1. Original commit c918a72c5170503c98fd66a0f3116b7bfcd1250c; Apache-2.0. -/
import DifferentialGeometry.External.GraphCoveringTheory.KuroshPathRelation

-- Preserve the original standalone port elaboration setting.
set_option autoImplicit true
open Set Function
open CategoryTheory
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
universe u v
namespace GraphCoveringTheory.Kurosh

theorem catStep {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a b c d : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj
        ((coverPrefunctor G H).symmetrify.obj
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b)
    (e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) b c)
    (q : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj b ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj d) :
    let ep : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj b ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj c := e.toPath
      let en : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj c ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b :=
      (Quiver.reverse e).toPath
    (test_coverPathLiftData G H
      (catPathToRaw G (p ≫ (𝟙 _ ≫ q)))).x =
      (test_coverPathLiftData G H
        (catPathToRaw G (p ≫ (ep ≫ en) ≫ q))).x := by
  dsimp only
  let ep : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj b ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj c := e.toPath
  let en : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj c ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b :=
      (Quiver.reverse e).toPath
  have hb := test_coverPathLiftData_backtrack_endpoint G H
    (catPathToRaw G p) e
  have ha := test_coverPathLiftData_append_endpoint G H
    (catPathToRaw G p)
    (((catPathToRaw G p).comp e.toPath).cons (Quiver.reverse e)) hb.symm
    (catPathToRaw G q)
  have hleft : catPathToRaw G (p ≫ (𝟙 _ ≫ q)) =
      (catPathToRaw G p).comp (catPathToRaw G q) := by
    simp only [Category.id_comp]
    rfl
  have hright : catPathToRaw G (p ≫ (ep ≫ en) ≫ q) =
      (((catPathToRaw G p).comp e.toPath).cons
        (Quiver.reverse e)).comp (catPathToRaw G q) := by
    -- The category-path expression is the same raw path after reassociation.
    rw [← Category.assoc p (ep ≫ en) q, ← Category.assoc p ep en]
    have hcomp : catPathToRaw G (((p ≫ ep) ≫ en) ≫ q) =
        (catPathToRaw G ((p ≫ ep) ≫ en)).comp
          (catPathToRaw G q) := by
      rfl
    have hpe : catPathToRaw G (p ≫ ep) =
        (catPathToRaw G p).cons e := by
      change p ≫ ep = Quiver.Path.cons p e
      rfl
    have hpen0 : catPathToRaw G ((p ≫ ep) ≫ en) =
        (catPathToRaw G (p ≫ ep)).cons (Quiver.reverse e) := by
      change (p ≫ ep) ≫ en =
        Quiver.Path.cons (p ≫ ep) (Quiver.reverse e)
      rfl
    rw [hcomp, hpen0, hpe]
    rfl
  rw [hleft, hright]
  exact ha

theorem catEqv {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p q : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj
        ((coverPrefunctor G H).symmetrify.obj
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) ⟶
      (CategoryTheory.Paths.of
        (Quiver.Symmetrify (RawBassSerreVertex G))).obj a)
    (h : Relation.EqvGen
      (@CategoryTheory.HomRel.CompClosure
        (CategoryTheory.Paths (Quiver.Symmetrify (RawBassSerreVertex G))) _
        (@Quiver.FreeGroupoid.redStep (RawBassSerreVertex G)
          (rawBassSerreQuiver G)) _ _)
      p q) :
    (test_coverPathLiftData G H (catPathToRaw G p)).x =
      (test_coverPathLiftData G H (catPathToRaw G q)).x := by
  induction h with
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ih₁ ih₂ => exact ih₁.trans ih₂
  | rel x y hxy =>
      rcases hxy with ⟨A, B, f, m₁, m₂, g, hstep⟩
      cases hstep with
      | step X Z e =>
          exact catStep (a := a) G H f e g

end GraphCoveringTheory.Kurosh
