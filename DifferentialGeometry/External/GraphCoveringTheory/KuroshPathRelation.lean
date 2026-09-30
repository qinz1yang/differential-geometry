/- Ported for the team Lake library; proof bodies and declaration names retained.
Module imports, diagnostic #print commands, and original autoImplicit setting adapted. See docs/geometrization/BASELINE_PROVENANCE.json. -/
/- GC revision197 compatibility port: restore legacy definitional transparency for Lean4.33.1. Original commit c918a72c5170503c98fd66a0f3116b7bfcd1250c; Apache-2.0. -/
import DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverLift

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

def catPathToRaw {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    {a b : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj a ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b) :
    @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) a b := p

example {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    (H : Subgroup (FreeProduct G))
    {a : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj
        ((coverPrefunctor G H).symmetrify.obj
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) ⟶
      (CategoryTheory.Paths.of
        (Quiver.Symmetrify (RawBassSerreVertex G))).obj a) :
    (test_coverPathLiftData G H p).x =
      (test_coverPathLiftData G H (catPathToRaw G p)).x := by
  rfl

example {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    {a b c : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj a ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b)
    (q : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj b ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj c) :
    catPathToRaw G (p ≫ q) =
      (catPathToRaw G p).comp (catPathToRaw G q) := by
  rfl

example {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    {a b c d : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj a ⟶
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
    catPathToRaw G (p ≫ (ep ≫ en) ≫ q) =
      (((catPathToRaw G p).comp e.toPath).cons (Quiver.reverse e)).comp
        (catPathToRaw G q) := by
  let ep : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj b ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj c := e.toPath
  let en : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj c ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b :=
      (Quiver.reverse e).toPath
  change catPathToRaw G (p ≫ (ep ≫ en) ≫ q) = _
  have hpe : catPathToRaw G (p ≫ ep) =
      (catPathToRaw G p).cons e := by
    change p ≫ ep = Quiver.Path.cons p e
    rfl
  have hpen0 : catPathToRaw G ((p ≫ ep) ≫ en) =
      (catPathToRaw G (p ≫ ep)).cons (Quiver.reverse e) := by
    change (p ≫ ep) ≫ en = Quiver.Path.cons (p ≫ ep) (Quiver.reverse e)
    rfl
  have hpen : catPathToRaw G ((p ≫ ep) ≫ en) =
      ((catPathToRaw G p).cons e).cons (Quiver.reverse e) := by
    rw [hpen0, hpe]
  have hcomp : catPathToRaw G
        (((p ≫ ep) ≫ en) ≫ q) =
      (catPathToRaw G ((p ≫ ep) ≫ en)).comp
        (catPathToRaw G q) := by
    rfl
  rw [← Category.assoc p (ep ≫ en) q, ← Category.assoc p ep en]
  rw [hcomp, hpen]
  rfl

end GraphCoveringTheory.Kurosh
