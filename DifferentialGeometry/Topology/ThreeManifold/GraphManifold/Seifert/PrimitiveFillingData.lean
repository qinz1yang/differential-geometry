import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Adapters

/-!
# Actual primitive filling data

The product host and the filling solids have complete piece and port correspondences. Filling
slopes are arbitrary primitive slopes, including the fibre slope. The boundary correction goes
from the original solid coordinates through the host map to the target solid coordinates.
-/

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u

namespace GC.Seifert

structure PrimitiveFillingPresentation (W : CompactCarrier.{u}) (n r : ℕ) where
  presentation : TorusPresentation W
  piece : Option (Fin n) ≃ Fin presentation.components.count
  product : ProductFibredPiece presentation (piece none) (r + n)
  solid : (m : Fin n) → SolidTorusPiece presentation (piece (some m))
  port : Fin r ⊕ Fin n ≃ Fin (r + n)
  seam : Fin n ≃ Fin presentation.pairing.count
  free : Fin r ≃ Fin presentation.externalCount
  free_port : ∀ a, (product.port (port (.inl a))).val = .inr (.inr (free a))
  filled_port : ∀ m, (product.port (port (.inr m))).val = .inr (.inl (seam m))
  solid_port : ∀ m, ((solid m).port 0).val = .inl (seam m)
  slope : Fin n → PrimitiveSlope
  slope_eq : ∀ m, torusUnit (presentation.pairing.matching (seam m)) • meridianSlope = slope m

structure PrimitiveFillingPieces (C : CompactCarrier.{u}) (D : C.Components)
    (P : TorusPairing C) {r : ℕ} (E : BoundaryTori C r) (n : ℕ) where
  piece : Option (Fin n) ≃ Fin D.count
  base : PlanarBase.{u} (r + n)
  host : (base.surface.Carrier × Circle) ≃ₘ⟮
    (SurfaceModel.model base.surface.kind).prod (𝓡 1), C.model⟯ D.piece (piece none)
  solidBase : Fin n → PlanarBase.{u} 1
  solid : (m : Fin n) → ((solidBase m).surface.Carrier × Circle) ≃ₘ⟮
    (SurfaceModel.model (solidBase m).surface.kind).prod (𝓡 1), C.model⟯
      D.piece (piece (some m))
  port : Fin r ⊕ Fin n ≃ Fin (r + n)
  seam : Fin n ≃ Fin P.count
  host_free : ∀ a p, p ∈ halfCollarSource → E.collar a p =
    (host (base.collar (port (.inl a)) (p.1.1, p.2), p.1.2)).val
  host_filled : ∀ m p, p ∈ halfCollarSource → P.rightCollar (seam m) p =
    (host (base.collar (port (.inr m)) (p.1.1, p.2), p.1.2)).val
  solid_collar : ∀ m p, p ∈ halfCollarSource → P.leftCollar (seam m) p =
    (solid m ((solidBase m).collar 0 (p.1.1, p.2), p.1.2)).val
  slope : Fin n → PrimitiveSlope
  slope_eq : ∀ m, torusUnit (P.matching (seam m)) • meridianSlope = slope m
  boundary_exhausted : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image
  external_disjoint : Disjoint (⋃ j, P.gluing.block j) E.image

def primitiveFillingCorrection
    (φ φ' ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  (φ.trans ψ).trans φ'.symm

theorem primitiveFillingCorrection_square
    (φ φ' ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (t : Torus) :
    φ' (primitiveFillingCorrection φ φ' ψ t) = ψ (φ t) :=
  φ'.apply_symm_apply (ψ (φ t))

private theorem primitiveFillingUnit_trans
    (φ ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    torusUnit (φ.trans ψ) = torusUnit ψ * torusUnit φ := by
  apply Units.ext
  exact torusMatrix_trans φ ψ

private theorem primitiveFillingUnit_symm
    (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    torusUnit φ.symm = (torusUnit φ)⁻¹ := by
  apply Units.ext
  rfl

theorem primitiveFillingCorrection_preserves_meridian
    (φ φ' ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (α α' : PrimitiveSlope) (hφ : torusUnit φ • meridianSlope = α)
    (hφ' : torusUnit φ' • meridianSlope = α') (hψ : torusUnit ψ • α = α') :
    torusUnit (primitiveFillingCorrection φ φ' ψ) • meridianSlope = meridianSlope := by
  rw [primitiveFillingCorrection, primitiveFillingUnit_trans, primitiveFillingUnit_trans,
    primitiveFillingUnit_symm, mul_smul, mul_smul, hφ, hψ, ← hφ']
  exact inv_smul_smul (torusUnit φ') meridianSlope

namespace PrimitiveFillingPresentation

variable {W : CompactCarrier.{u}} {n r : ℕ} (B : PrimitiveFillingPresentation W n r)

theorem components_count : B.presentation.components.count = n + 1 := by
  rw [← Fintype.card_fin B.presentation.components.count, ← Fintype.card_congr B.piece,
    Fintype.card_option, Fintype.card_fin]

theorem pairing_count : B.presentation.pairing.count = n :=
  (Fin.equiv_iff_eq.mp ⟨B.seam⟩).symm

theorem external_count : B.presentation.externalCount = r :=
  (Fin.equiv_iff_eq.mp ⟨B.free⟩).symm

theorem correction_preserves_meridian {W' : CompactCarrier.{u}}
    (B' : PrimitiveFillingPresentation W' n r)
    (ψ : Fin r ⊕ Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (hψ : ∀ m, torusUnit (ψ (.inr m)) • B.slope m = B'.slope m) (m : Fin n) :
    torusUnit (primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
      (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m))) • meridianSlope =
        meridianSlope :=
  primitiveFillingCorrection_preserves_meridian _ _ _ _ _ (B.slope_eq m) (B'.slope_eq m)
    (hψ m)

end PrimitiveFillingPresentation

namespace PrimitiveFillingPieces

variable {C : CompactCarrier.{u}} {D : C.Components} {P : TorusPairing C} {n r : ℕ}
  {E : BoundaryTori C r} (A : PrimitiveFillingPieces C D P E n)

theorem left_owned (j : Fin P.count) :
    P.gluing.left j ⊆ D.piece (A.piece (some (A.seam.symm j))) := by
  intro x hx
  obtain ⟨t, ht⟩ := (P.leftParam j).surjective ⟨x, hx⟩
  have hm : P.leftCollar (A.seam (A.seam.symm j)) (t, halfZero) ∈
      D.piece (A.piece (some (A.seam.symm j))) := by
    rw [A.solid_collar (A.seam.symm j) (t, halfZero) (zero_mem_halfCollarSource t)]
    exact Subtype.property _
  rw [Equiv.apply_symm_apply, P.left_zero, ht] at hm
  exact hm

theorem right_owned (j : Fin P.count) : P.gluing.right j ⊆ D.piece (A.piece none) := by
  intro x hx
  obtain ⟨t, ht⟩ := (P.rightParam j).surjective ⟨x, hx⟩
  have hm : P.rightCollar (A.seam (A.seam.symm j)) (t, halfZero) ∈
      D.piece (A.piece none) := by
    rw [A.host_filled (A.seam.symm j) (t, halfZero) (zero_mem_halfCollarSource t)]
    exact Subtype.property _
  rw [Equiv.apply_symm_apply, P.right_zero, ht] at hm
  exact hm

theorem external_owned (a : Fin r) : range (E.torusMap a) ⊆ D.piece (A.piece none) := by
  rintro x ⟨t, rfl⟩
  change E.collar a (t, halfZero) ∈ D.piece (A.piece none)
  rw [A.host_free a (t, halfZero) (zero_mem_halfCollarSource t)]
  exact Subtype.property _

end PrimitiveFillingPieces

end GC.Seifert
