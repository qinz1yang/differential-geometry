/- Ported for the team Lake library; proof bodies and declaration names retained.
Module imports, diagnostic #print commands, and original autoImplicit setting adapted. See docs/geometrization/BASELINE_PROVENANCE.json. -/
/- GC revision197 compatibility port: restore legacy definitional transparency for Lean4.33.1. Original commit c918a72c5170503c98fd66a0f3116b7bfcd1250c; Apache-2.0. -/
import DifferentialGeometry.External.GraphCoveringTheory.KuroshRawPathValue
import Mathlib.Combinatorics.Quiver.Covering

-- Preserve the original standalone port elaboration setting.
set_option autoImplicit true
open Set Function
open CategoryTheory
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

namespace GraphCoveringTheory.Kurosh

open Monoid.CoprodI

theorem test_rightCosetMk_mul_out_mk {P : Type u} [Group P]
    (K : Subgroup P) (p r : P) :
    rightCosetMk K (p * Quotient.out (rightCosetMk K r)) =
      rightCosetMk K (p * r) := by
  have hc : rightCosetMk K (Quotient.out (rightCosetMk K r)) =
      rightCosetMk K r := Quotient.out_eq _
  rcases (rightCosetMk_eq_iff K _ _).1 hc with ⟨k, hk⟩
  apply (rightCosetMk_eq_iff K _ _).2
  refine ⟨k, ?_⟩
  calc
    p * Quotient.out (rightCosetMk K r) * (k : P) =
        p * (Quotient.out (rightCosetMk K r) * (k : P)) := by
          rw [mul_assoc]
    _ = p * r := by rw [hk]

theorem test_coverEdgeSource_smul {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p q : CoverSource G H) (e : CoverEdge G H) :
    coverEdgeSource G H (p * q, e) =
      p • coverEdgeSource G H (q, e) := by
  apply congrArg (Sigma.mk e.1)
  change rightCosetMk
      (MonoidHom.range (treeKuroshVertexInclusion G H e.1)) (p * q) =
    rightCosetMk (MonoidHom.range
      (treeKuroshVertexInclusion G H e.1))
      (p * Quotient.out (rightCosetMk
        (MonoidHom.range (treeKuroshVertexInclusion G H e.1)) q))
  exact (test_rightCosetMk_mul_out_mk _ _ _).symm

theorem test_coverEdgeTarget_smul {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p q : CoverSource G H) (e : CoverEdge G H) :
    coverEdgeTarget G H (p * q, e) =
      p • coverEdgeTarget G H (q, e) := by
  apply congrArg (Sigma.mk e.2.1)
  change rightCosetMk
      (MonoidHom.range (treeKuroshVertexInclusion G H e.2.1))
      ((p * q) * (coverEdgeLetter G H e)⁻¹) =
    rightCosetMk (MonoidHom.range
      (treeKuroshVertexInclusion G H e.2.1))
      (p * Quotient.out (rightCosetMk
        (MonoidHom.range (treeKuroshVertexInclusion G H e.2.1))
        (q * (coverEdgeLetter G H e)⁻¹)))
  rw [mul_assoc]
  exact (test_rightCosetMk_mul_out_mk _ _ _).symm

noncomputable def test_coverEdgeAction {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) {x y : CoverVertex G H}
    (d : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) x y) :
    @Quiver.Hom (CoverVertex G H) (coverQuiver G H) (p • x) (p • y) := by
  refine ⟨(p * d.1.1, d.1.2), ?_, ?_⟩
  · calc
      coverEdgeSource G H (p * d.1.1, d.1.2) =
          p • coverEdgeSource G H d.1 :=
        test_coverEdgeSource_smul G H p d.1.1 d.1.2
      _ = p • x := congrArg (fun z => p • z) d.2.1
  · calc
      coverEdgeTarget G H (p * d.1.1, d.1.2) =
          p • coverEdgeTarget G H d.1 :=
        test_coverEdgeTarget_smul G H p d.1.1 d.1.2
      _ = p • y := congrArg (fun z => p • z) d.2.2

noncomputable def test_coverActionPrefunctor {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) : CoverVertex G H ⥤q CoverVertex G H where
  obj := fun x => p • x
  map := test_coverEdgeAction G H p

noncomputable def test_coverActionSymmPrefunctor {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) :
    Quiver.Symmetrify (CoverVertex G H) ⥤q
      Quiver.Symmetrify (CoverVertex G H) :=
  (test_coverActionPrefunctor G H p).symmetrify

noncomputable def test_coverPathAction {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) {x y : CoverVertex G H}
    (q : @Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _ x y) :
    @Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _ (p • x) (p • y) :=
  (test_coverActionSymmPrefunctor G H p).mapPath q

theorem test_coverPathAction_nil {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) (x : CoverVertex G H) :
    test_coverPathAction G H p
      (Quiver.Path.nil : @Quiver.Path
        (Quiver.Symmetrify (CoverVertex G H)) _ x x) = Quiver.Path.nil := by
  rfl

theorem test_coverVertex_action_root {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) :
    p • coverVertexMk G H (rawBassSerreOrbitRoot G H) 1 =
      coverVertexMk G H (rawBassSerreOrbitRoot G H) p := by
  apply congrArg (Sigma.mk (rawBassSerreOrbitRoot G H))
  change rightCosetMk
      (MonoidHom.range (treeKuroshVertexInclusion G H
        (rawBassSerreOrbitRoot G H)))
      (p * Quotient.out (rightCosetMk
        (MonoidHom.range (treeKuroshVertexInclusion G H
          (rawBassSerreOrbitRoot G H))) 1)) =
    rightCosetMk (MonoidHom.range (treeKuroshVertexInclusion G H
      (rawBassSerreOrbitRoot G H))) p
  simpa using test_rightCosetMk_mul_out_mk
    (MonoidHom.range (treeKuroshVertexInclusion G H
      (rawBassSerreOrbitRoot G H))) p 1

theorem test_coverVertexRange_action_one {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H)
    (k : treeVertexStabilizer G H a) :
    treeKuroshVertexInclusion G H a k • coverVertexMk G H a 1 =
      coverVertexMk G H a 1 := by
  apply congrArg (Sigma.mk a)
  change rightCosetMk (MonoidHom.range
      (treeKuroshVertexInclusion G H a))
      (treeKuroshVertexInclusion G H a k * Quotient.out
        (rightCosetMk (MonoidHom.range
          (treeKuroshVertexInclusion G H a)) 1)) =
    rightCosetMk (MonoidHom.range
      (treeKuroshVertexInclusion G H a)) 1
  rw [test_rightCosetMk_mul_out_mk]
  apply (rightCosetMk_eq_iff
    (MonoidHom.range (treeKuroshVertexInclusion G H a)) _ _).2
  let kk : MonoidHom.range (treeKuroshVertexInclusion G H a) :=
    ⟨treeKuroshVertexInclusion G H a k, ⟨k, rfl⟩⟩
  refine ⟨kk⁻¹, ?_⟩
  change treeKuroshVertexInclusion G H a k * (↑kk : CoverSource G H)⁻¹ = 1
  have hkk : (↑kk : CoverSource G H) =
      treeKuroshVertexInclusion G H a k := rfl
  rw [hkk, mul_inv_cancel]

theorem test_coverFactorLoopPath {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H)
    (k : treeVertexStabilizer G H a) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
      (coverVertexMk G H (rawBassSerreOrbitRoot G H)
        (treeKuroshVertexInclusion G H a k))) := by
  let q := rawTreePathMap G H (rawTreePathAtRoot G H a)
  let lp := coverPathLift G H (1 : CoverSource G H) q
  have hr : lp.1 = 1 := by
    dsimp [lp, q]
    rw [coverPathLift_value, test_coverPathValue_rawTree]
    simp
  let p₀ : @Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
      (coverVertexMk G H a 1) :=
    lp.2.cast rfl (congrArg (coverVertexMk G H a) hr)
  let s : CoverSource G H := treeKuroshVertexInclusion G H a k
  let p₁ := test_coverPathAction G H s p₀.reverse
  have hs : s • coverVertexMk G H a 1 = coverVertexMk G H a 1 := by
    exact test_coverVertexRange_action_one G H a k
  have hroot : s • coverVertexMk G H (rawBassSerreOrbitRoot G H) 1 =
      coverVertexMk G H (rawBassSerreOrbitRoot G H) s := by
    exact test_coverVertex_action_root G H s
  refine ⟨p₀.comp (p₁.cast hs hroot)⟩

theorem test_coverFactorLoopPath_value {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H)
    (k : treeVertexStabilizer G H a) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
      (coverVertexMk G H (rawBassSerreOrbitRoot G H)
        (treeKuroshVertexInclusion G H a k))) :=
  test_coverFactorLoopPath G H a k

end GraphCoveringTheory.Kurosh
