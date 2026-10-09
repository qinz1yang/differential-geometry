/- Ported for the team Lake library; proof bodies and declaration names retained.
Module imports, diagnostic #print commands, and original autoImplicit setting adapted. See docs/geometrization/BASELINE_PROVENANCE.json. -/
/- GC revision197 compatibility port: restore legacy definitional transparency for Lean4.33.1. Original commit c918a72c5170503c98fd66a0f3116b7bfcd1250c; Apache-2.0. -/
import DifferentialGeometry.External.GraphCoveringTheory.KuroshCoverAction
import DifferentialGeometry.External.GraphCoveringTheory.KuroshFreeFiber

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

theorem test_coverFreeFactorLoopPath {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : KuroshFreePart G H) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
    (coverVertexMk G H (rawBassSerreOrbitRoot G H)
        (treeKuroshFreeInclusion G H x))) := by
  let z : KuroshFreePart G H := x⁻¹
  obtain ⟨q, hq⟩ := test_coverFreePath_exists G H
    (a := rawBassSerreOrbitRoot G H)
    (b := rawBassSerreOrbitRoot G H) z
  have hloop : coverPathFreeLoop G H q = x⁻¹ := by
    unfold coverPathFreeLoop
    rw [coverQuotientTreePathHom_root]
    simp only [Groupoid.inv_eq_inv]
    simp
    exact hq
  have hvalue : coverPathValue G H q =
      treeKuroshFreeInclusion G H x := by
    calc
      coverPathValue G H q =
          (treeKuroshFreeInclusion G H
            (coverPathFreeLoop G H q))⁻¹ :=
        coverPathValue_formula G H q
      _ = (treeKuroshFreeInclusion G H (x⁻¹))⁻¹ := by rw [hloop]
      _ = treeKuroshFreeInclusion G H x := by simp
  let lp := coverPathLift G H (1 : CoverSource G H) q
  have hp : lp.1 = treeKuroshFreeInclusion G H x := by
    dsimp [lp]
    rw [coverPathLift_value, hvalue]
    simp
  refine ⟨lp.2.cast rfl (congrArg
    (coverVertexMk G H (rawBassSerreOrbitRoot G H)) hp)⟩

theorem test_coverFactorLoopPath_rawTree {ι : Type v}
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

theorem test_coverRootFiberPath {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) p)) := by
  induction p using Monoid.CoprodI.induction_on with
  | one =>
      exact ⟨Quiver.Path.nil⟩
  | of i m =>
      cases i with
      | inl a =>
          cases m with
          | up k =>
              simpa [treeKuroshVertexInclusion] using
                test_coverFactorLoopPath_rawTree G H a k
      | inr i =>
          cases i
          cases m with
          | up x =>
              simpa [treeKuroshFreeInclusion] using
                test_coverFreeFactorLoopPath G H x
  | mul x y hx hy =>
      rcases hx with ⟨px⟩
      rcases hy with ⟨py⟩
      have hstart :
          x • coverVertexMk G H (rawBassSerreOrbitRoot G H) 1 =
            coverVertexMk G H (rawBassSerreOrbitRoot G H) x := by
        exact test_coverVertex_action_root G H x
      have htarget :
          x • coverVertexMk G H (rawBassSerreOrbitRoot G H) y =
            coverVertexMk G H (rawBassSerreOrbitRoot G H) (x * y) := by
        calc
          x • coverVertexMk G H (rawBassSerreOrbitRoot G H) y =
              x • (y • coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) := by
                rw [test_coverVertex_action_root G H y]
          _ = (x * y) •
              coverVertexMk G H (rawBassSerreOrbitRoot G H) 1 :=
            (mul_smul x y _).symm
          _ = coverVertexMk G H (rawBassSerreOrbitRoot G H) (x * y) :=
            test_coverVertex_action_root G H (x * y)
      exact ⟨px.comp ((test_coverPathAction G H x py).cast hstart htarget)⟩

theorem test_coverSource_rootedConnected {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Quiver.RootedConnected
      (show Quiver.Symmetrify (CoverVertex G H) from
        coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) := by
  constructor
  intro x
  cases x with
  | mk a c =>
      let q := rawTreePathMap G H (rawTreePathAtRoot G H a)
      let p : CoverSource G H := Quotient.out c
      let lp := coverPathLift G H p q
      have hcoord : lp.1 = p := by
        dsimp [lp, q]
        rw [coverPathLift_value, test_coverPathValue_rawTree]
        simp [p]
      have hend : coverVertexMk G H a lp.1 = ⟨a, c⟩ := by
        apply congrArg (Sigma.mk a)
        rw [hcoord]
        exact Quotient.out_eq c
      rcases test_coverRootFiberPath G H p with ⟨rp⟩
      exact ⟨rp.comp (lp.2.cast rfl hend)⟩

end GraphCoveringTheory.Kurosh
