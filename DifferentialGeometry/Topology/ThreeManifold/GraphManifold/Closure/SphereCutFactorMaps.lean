import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutComponents
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapPuncturedFactors

/-!
The two actual pieces of a signed spherical cut map into the original ambient carrier.
Their maps are injective and cover it, with exactly the common signed zero sphere as overlap.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable {W : CompactCarrier.{u}} (c : SphereCutSignedCollars W)
  (hs : ∀ j, (c j).source = sphereSignedCollarSource)
  (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
  (A : Bool → Set W.Carrier)
  (hconnected : ∀ b, IsConnected (A b)) (hopen : ∀ b, IsOpen (A b))
  (hdisjoint : Disjoint (A false) (A true))
  (hcover : (sphereCutAmbientZero c)ᶜ = A false ∪ A true)
  (hgerm : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ ∀ b z s, 0 < s → s < η →
    c 0 (z, sphereCutSign b s) ∈ A b)

local notation "D" => sphereCutComponents c hs hd A hconnected hopen hdisjoint hcover hgerm

def sphereCutPieceFactorMap (i : Fin 2) (x : (D).piece i) : W.Carrier :=
  sphereCutFold c x.val

def sphereCutPieceFactorZero (i : Fin 2) (z : ClosureSphere.{u}) : (D).piece i :=
  ⟨sphereCutZero c 0 (sphereCutBoundarySide i) z,
    (sphereCutComponents_zero_mem c hs hd A hconnected hopen hdisjoint hcover hgerm
      i (sphereCutBoundarySide i) z).mpr rfl⟩

theorem sphereCutPieceFactorMap_continuous (i : Fin 2) :
    Continuous (sphereCutPieceFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm i) :=
  (sphereCutFold_continuous c).comp continuous_subtype_val

private theorem factor_zero_not_mem (i : Fin 2) (z : ClosureSphere.{u}) :
    sphereCutZero c 0 (!(sphereCutBoundarySide i)) z ∉ (D).piece i := by
  rw [sphereCutComponents_zero_mem]
  simp only [Bool.not_eq_self, not_false_eq_true]

theorem sphereCutPieceFactorMap_injective (i : Fin 2) :
    Injective (sphereCutPieceFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm i) := by
  intro x y he
  have hx := x.property
  have hy := y.property
  rcases (sphereCutFold_fibre_relation c hs hd x.val y.val).mp he with hxy | ⟨z, h | h⟩
  · exact Subtype.ext hxy
  · rw [h.1] at hx
    rw [h.2] at hy
    fin_cases i
    · exact (factor_zero_not_mem c hs hd A hconnected hopen hdisjoint hcover hgerm 0 z hy).elim
    · exact (factor_zero_not_mem c hs hd A hconnected hopen hdisjoint hcover hgerm 1 z hx).elim
  · rw [h.1] at hx
    rw [h.2] at hy
    fin_cases i
    · exact (factor_zero_not_mem c hs hd A hconnected hopen hdisjoint hcover hgerm 0 z hx).elim
    · exact (factor_zero_not_mem c hs hd A hconnected hopen hdisjoint hcover hgerm 1 z hy).elim

section PieceCross

variable {c hs hd A hconnected hopen hdisjoint hcover hgerm}

theorem sphereCutPieceFactorMap_cross {x : (D).piece (0 : Fin 2)} {y : (D).piece (1 : Fin 2)} :
    sphereCutPieceFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm 0 x =
      sphereCutPieceFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm 1 y ↔
    ∃ z, x = sphereCutPieceFactorZero c hs hd A hconnected hopen hdisjoint hcover hgerm 0 z ∧
      y = sphereCutPieceFactorZero c hs hd A hconnected hopen hdisjoint hcover hgerm 1 z := by
  constructor
  · intro he
    have hx := x.property
    have hy := y.property
    rcases (sphereCutFold_fibre_relation c hs hd x.val y.val).mp he with hxy | ⟨z, h | h⟩
    · exact (disjoint_left.mp ((D).disjoint (by decide : (0 : Fin 2) ≠ 1))
        hx (hxy.symm ▸ hy)).elim
    · exact ⟨z, Subtype.ext h.1, Subtype.ext h.2⟩
    · rw [h.1] at hx
      exact (factor_zero_not_mem c hs hd A hconnected hopen hdisjoint hcover hgerm 0 z hx).elim
  · rintro ⟨z, rfl, rfl⟩
    change sphereCutFold c (sphereCutZero c 0 false z) =
      sphereCutFold c (sphereCutZero c 0 true z)
    rw [sphereCutZero_fold, sphereCutZero_fold]

end PieceCross

theorem sphereCutPieceFactorMap_covers (y : W.Carrier) :
    (∃ x : (D).piece (0 : Fin 2),
      sphereCutPieceFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm 0 x = y) ∨
    ∃ x : (D).piece (1 : Fin 2),
      sphereCutPieceFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm 1 x = y := by
  obtain ⟨x, hx⟩ := sphereCut_projection_surjective c y
  have hm : x ∈ ⋃ i, ((D).piece i : Set (sphereCutCarrier c hs hd).Carrier) :=
    (D).covers.symm ▸ mem_univ x
  obtain ⟨i, hi⟩ := mem_iUnion.mp hm
  fin_cases i
  · exact Or.inl ⟨⟨x, hi⟩, hx⟩
  · exact Or.inr ⟨⟨x, hi⟩, hx⟩

variable (B : MixedBoundaryCertificate (sphereCutCarrier c hs hd))

def sphereCutPuncturedFactorMap (i : Fin 2)
    (x : B.sphereCapPuncturedFactor (D) i) : W.Carrier :=
  sphereCutPieceFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm i
    ((B.sphereCapPuncturedFactorHomeomorph (D) i).symm x)

def sphereCutPuncturedFactorZero (i : Fin 2) (z : ClosureSphere.{u}) :
    B.sphereCapPuncturedFactor (D) i :=
  B.sphereCapPuncturedFactorHomeomorph (D) i
    (sphereCutPieceFactorZero c hs hd A hconnected hopen hdisjoint hcover hgerm i z)

theorem sphereCutPuncturedFactorMap_continuous (i : Fin 2) :
    Continuous
      (sphereCutPuncturedFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm B i) :=
  (sphereCutPieceFactorMap_continuous c hs hd A hconnected hopen hdisjoint hcover hgerm i).comp
    (B.sphereCapPuncturedFactorHomeomorph (D) i).symm.continuous

theorem sphereCutPuncturedFactorMap_injective (i : Fin 2) :
    Injective
      (sphereCutPuncturedFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm B i) :=
  (sphereCutPieceFactorMap_injective c hs hd A hconnected hopen hdisjoint hcover hgerm i).comp
    (B.sphereCapPuncturedFactorHomeomorph (D) i).symm.injective

section PuncturedCross

variable {c hs hd A hconnected hopen hdisjoint hcover hgerm B}

theorem sphereCutPuncturedFactorMap_cross
    {x : B.sphereCapPuncturedFactor (D) (0 : Fin 2)}
    {y : B.sphereCapPuncturedFactor (D) (1 : Fin 2)} :
    sphereCutPuncturedFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm B 0 x =
      sphereCutPuncturedFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm B 1 y ↔
    ∃ z,
      x = sphereCutPuncturedFactorZero c hs hd A hconnected hopen hdisjoint hcover hgerm B 0 z ∧
      y = sphereCutPuncturedFactorZero c hs hd A hconnected hopen hdisjoint hcover hgerm B 1 z := by
  let e0 := B.sphereCapPuncturedFactorHomeomorph (D) (0 : Fin 2)
  let e1 := B.sphereCapPuncturedFactorHomeomorph (D) (1 : Fin 2)
  change sphereCutPieceFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm 0
    (e0.symm x) = sphereCutPieceFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm 1
      (e1.symm y) ↔ _
  rw [sphereCutPieceFactorMap_cross]
  apply exists_congr
  intro z
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨(e0.apply_symm_apply x).symm.trans (congrArg e0 hx),
      (e1.apply_symm_apply y).symm.trans (congrArg e1 hy)⟩
  · rintro ⟨hx, hy⟩
    exact ⟨(congrArg e0.symm hx).trans (e0.symm_apply_apply _),
      (congrArg e1.symm hy).trans (e1.symm_apply_apply _)⟩

end PuncturedCross

theorem sphereCutPuncturedFactorMap_covers (y : W.Carrier) :
    (∃ x : B.sphereCapPuncturedFactor (D) (0 : Fin 2),
      sphereCutPuncturedFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm B 0 x = y) ∨
    ∃ x : B.sphereCapPuncturedFactor (D) (1 : Fin 2),
      sphereCutPuncturedFactorMap c hs hd A hconnected hopen hdisjoint hcover hgerm B 1 x = y := by
  rcases sphereCutPieceFactorMap_covers c hs hd A hconnected hopen hdisjoint hcover hgerm y with
    ⟨x, hx⟩ | ⟨x, hx⟩
  · refine Or.inl ⟨B.sphereCapPuncturedFactorHomeomorph (D) (0 : Fin 2) x, ?_⟩
    simpa only [sphereCutPuncturedFactorMap, Homeomorph.symm_apply_apply] using hx
  · refine Or.inr ⟨B.sphereCapPuncturedFactorHomeomorph (D) (1 : Fin 2) x, ?_⟩
    simpa only [sphereCutPuncturedFactorMap, Homeomorph.symm_apply_apply] using hx

end GC.GraphManifold
