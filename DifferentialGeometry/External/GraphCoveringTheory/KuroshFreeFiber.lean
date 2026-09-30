/- Ported for the team Lake library; proof bodies and declaration names retained.
Module imports, diagnostic #print commands, and original autoImplicit setting adapted. See docs/geometrization/BASELINE_PROVENANCE.json. -/
/- GC revision197 compatibility port: restore legacy definitional transparency for Lean4.33.1. Original commit c918a72c5170503c98fd66a0f3116b7bfcd1250c; Apache-2.0. -/
import DifferentialGeometry.External.GraphCoveringTheory.KuroshRawPathValue

-- Preserve the original standalone port elaboration setting.
set_option autoImplicit true
open Set Function
open CategoryTheory
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

namespace GraphCoveringTheory.Kurosh

theorem test_coverFreeGroupoidPathHom_eq_quotient_map {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b) :
    coverFreeGroupoidPathHom G H p =
      (CategoryTheory.Quotient.functor
        (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H))).map p := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      simp only [coverFreeGroupoidPathHom, Prefunctor.mapPath]
      rw [ih]
      cases e using Sum.rec <;> rfl

theorem test_coverFreePath_exists {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (z : @Quiver.Hom (Quiver.FreeGroupoid (RawBassSerreOrbitVertex G H)) _
      ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj a)
      ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj b)) :
    ∃ p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) a b,
      coverFreeGroupoidPathHom G H p = z := by
  obtain ⟨p, hp⟩ :=
    (CategoryTheory.Quotient.full_functor
      (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))).map_surjective z
  refine ⟨p, ?_⟩
  rw [test_coverFreeGroupoidPathHom_eq_quotient_map]
  exact hp

end GraphCoveringTheory.Kurosh
