import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusPresentation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Data
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Slope
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SolidTorus
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Irreducible

/-!
# Seifert blocks

Chapter 6, S1 and S4 (packet K06). The planar base `Pₖ`, `k ∈ {1, 2, 3}`, is modelled on
`planarModel k ⊆ ℂ`: the closed disc of radius `3` minus the open discs of radius `1/2` about `0`
(`k = 2`) or about `±3/2` (`k = 3`). Its boundary circle `j : Fin k` is parametrised by
`planarCircleMap k j`: `j = 0` is the outer circle, counterclockwise, the others are clockwise,
so every circle carries the boundary orientation. A `PlanarBase k` is a compact surface with half
collars of `k` boundary circles exhausting its boundary and a smooth embedding into `ℂ` onto
`planarModel k` sending circle `j` to `planarCircleMap k j`.

A `ProductFibredPiece T i k` (S1) is one diffeomorphism `Φ : Pₖ × S¹ ≃ piece i` of a torus
presentation with a bijection from the boundary circles to the sides owned by the piece, such that
every port collar equals `Φ ∘ (base collar × id)` on the collar source (an equality, as
`marked_collar`). The first torus coordinate of a port is the base circle `s`, the second the
fiber `f`; `fibration` is the induced circle fibration. A `SolidTorusPiece` is a product piece
over `P₁`, whose first port coordinate is the meridian.

A `SeifertBlock W d` (S4) is a torus presentation of `W` whose pieces are indexed by
`Option (Fin d.fillingCount)`: `none` is product-fibred over `P_{d.k}`, `some m` is a solid torus.
The ports of the product piece are the `d.ports` free ports, which are the external tori of `W`,
and the fillings (`fillingSlope`: cones, then normals `(1, q)`, in the order of
`SeifertData.retwist`). Filling `m` is seam `m`, solid torus on the left and product piece on the
right, and `matching` sends the meridian to the slope `(p, q)` of the filling in the basis
`(s, f)`: the first column of `torusMatrix` is `±(p, q)` and `Δ(image, fiber) = p`.

`t2IntervalData` is `T² × I` (`k = 2`, two ports) and `twistedIBundleData` is `D²(2, 2)`
(`k = 3`, one port, cones `(2, 1)`, `(2, -1)`, a twist of `(2, 1)`, `(2, 1)` absorbed by the free
port); both are `.euclidean` in the open table. `IsGoodBlock` asks the external tori to be
incompressible. `IsIrreducibleCarrier` asks every smoothly embedded sphere in the interior to bound
a smooth ball; on closed manifolds it is `IsIrreducible`. Orientation compatibility of `Φ` with the
piece is not imposed; it only fixes the overall sign of the Euler number.
-/

set_option autoImplicit false

noncomputable section
open Set Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

def planarCenter (k : ℕ) (j : Fin k) : ℝ :=
  if k = 2 then 0 else if j.val = 1 then 3 / 2 else if j.val = 2 then -(3 / 2) else 0

def planarRadius {k : ℕ} (j : Fin k) : ℝ := if j.val = 0 then 3 else 1 / 2

def planarModel (k : ℕ) : Set ℂ :=
  {z | ‖z‖ ≤ 3 ∧ ∀ j : Fin k, j.val ≠ 0 → 1 / 2 ≤ ‖z - planarCenter k j‖}

def planarCircleMap (k : ℕ) (j : Fin k) (t : Circle) : ℂ :=
  planarCenter k j + planarRadius j * (if j.val = 0 then (t : ℂ) else conj (t : ℂ))

theorem planarModel_one : planarModel 1 = closedBall 0 3 := by
  ext z
  simp [planarModel]

theorem norm_planarCircleMap_sub (k : ℕ) (j : Fin k) (t : Circle) :
    ‖planarCircleMap k j t - planarCenter k j‖ = planarRadius j := by
  unfold planarCircleMap planarRadius
  rw [add_sub_cancel_left, norm_mul]
  split_ifs <;> simp

theorem planarCircleMap_mem_planarModel {k : ℕ} (hk : k ≤ 3) (j : Fin k) (t : Circle) :
    planarCircleMap k j t ∈ planarModel k := by
  have hz := norm_planarCircleMap_sub k j t
  refine ⟨?_, fun j' hj' => ?_⟩
  · have h := norm_add_le (planarCenter k j : ℂ) (planarCircleMap k j t - planarCenter k j)
    rw [add_sub_cancel, hz, Complex.norm_real, Real.norm_eq_abs] at h
    refine h.trans ?_
    interval_cases k <;> fin_cases j <;> norm_num [planarCenter, planarRadius]
  · have h := abs_norm_sub_norm_le ((planarCenter k j : ℂ) - planarCenter k j')
      ((planarCenter k j : ℂ) - planarCircleMap k j t)
    rw [sub_sub_sub_cancel_left, norm_sub_rev _ (planarCircleMap k j t), hz,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    refine le_trans ?_ h
    interval_cases k <;> fin_cases j <;> fin_cases j' <;>
      first | exact absurd rfl hj' | norm_num [planarCenter, planarRadius]

abbrev circleCollarModel := (𝓡 1).prod (𝓡∂ 1)

def circleCollarSource : Set (Circle × EuclideanHalfSpace 1) := {p | p.2.val 0 < 1}

structure PlanarBase (k : ℕ) where
  surface : CompactSurface.{u}
  collar : Fin k → PartialDiffeomorph circleCollarModel (SurfaceModel.model surface.kind)
    (Circle × EuclideanHalfSpace 1) surface.Carrier ∞
  source_eq : ∀ j, (collar j).source = circleCollarSource
  boundary_zero : ∀ j t,
    (SurfaceModel.model surface.kind).IsBoundaryPoint (collar j (t, halfZero))
  disjoint : Pairwise fun i j => Disjoint (collar i).target (collar j).target
  boundary_exhausted : (SurfaceModel.model surface.kind).boundary surface.Carrier =
    ⋃ j, range fun t => collar j (t, halfZero)
  embedding : surface.Carrier → ℂ
  isSmoothEmbedding :
    Manifold.IsSmoothEmbedding (SurfaceModel.model surface.kind) 𝓘(ℝ, ℂ) ∞ embedding
  range_embedding : range embedding = planarModel k
  embedding_collar : ∀ j t, embedding (collar j (t, halfZero)) = planarCircleMap k j t

structure ProductFibredPiece {W : CompactCarrier.{u}} (T : TorusPresentation.{u} W)
    (i : Fin T.components.count) (k : ℕ) where
  base : PlanarBase.{u} k
  port : Fin k ≃ T.OwnedSide i
  trivialization : (base.surface.Carrier × Circle) ≃ₘ⟮
    (SurfaceModel.model base.surface.kind).prod (𝓡 1), T.cutCarrier.model⟯ T.components.piece i
  collar_eq : ∀ j p, p ∈ halfCollarSource →
    T.pieceCollar i (port j) p = trivialization (base.collar j (p.1.1, p.2), p.1.2)

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}
  {k : ℕ}

def fibration (P : ProductFibredPiece T i k) :
    CircleFibration T.cutCarrier (T.components.piece i) :=
  CircleFibration.ofProductDiffeomorph P.base.surface P.trivialization.symm

theorem fibration_projection_pieceCollar (P : ProductFibredPiece T i k) (j : Fin k)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    P.fibration.projection (T.pieceCollar i (P.port j) p) = P.base.collar j (p.1.1, p.2) := by
  change (P.trivialization.symm _).1 = _
  rw [P.collar_eq j p hp, Diffeomorph.symm_apply_apply]

theorem card_ownedSide (P : ProductFibredPiece T i k) : Fintype.card (T.OwnedSide i) = k := by
  rw [← Fintype.card_congr P.port, Fintype.card_fin]

end ProductFibredPiece

abbrev SolidTorusPiece {W : CompactCarrier.{u}} (T : TorusPresentation.{u} W)
    (i : Fin T.components.count) :=
  ProductFibredPiece T i 1

namespace SeifertData

abbrev fillingCount (d : SeifertData) : ℕ := d.cones.length + d.normals.length

theorem ports_add_fillingCount (d : SeifertData) : d.ports + d.fillingCount = d.k :=
  (add_assoc _ _ _).symm.trans d.ports_add_length_add_length

def fillingSlope (d : SeifertData) : Fin d.fillingCount → ℤ × ℤ :=
  Fin.append (fun c : Fin d.cones.length => ((d.cones[c].1 : ℤ), d.cones[c].2))
    (fun n : Fin d.normals.length => (1, d.normals[n]))

theorem isPrimitive_fillingSlope (d : SeifertData) (m : Fin d.fillingCount) :
    IsPrimitive (d.fillingSlope m) := by
  induction m using Fin.addCases with
  | left c =>
    rw [fillingSlope, Fin.append_left]
    exact d.gcd_eq_one_of_mem_cones _ (List.getElem_mem _)
  | right n =>
    rw [fillingSlope, Fin.append_right]
    exact Int.gcd_one_left _

theorem fillingSlope_fst_pos (d : SeifertData) (m : Fin d.fillingCount) :
    0 < (d.fillingSlope m).1 := by
  induction m using Fin.addCases with
  | left c =>
    rw [fillingSlope, Fin.append_left]
    have := d.two_le_of_mem_cones d.cones[c] (List.getElem_mem _)
    dsimp only
    omega
  | right n =>
    rw [fillingSlope, Fin.append_right]
    exact one_pos

end SeifertData

def meridianSlope : PrimitiveSlope := PrimitiveSlope.mk (1, 0) (by decide)

def fiberSlope : PrimitiveSlope := PrimitiveSlope.mk (0, 1) (by decide)

structure SeifertBlock (W : CompactCarrier.{u}) (d : SeifertData) where
  presentation : TorusPresentation.{u} W
  piece : Option (Fin d.fillingCount) ≃ Fin presentation.components.count
  product : ProductFibredPiece presentation (piece none) d.k
  solid : (m : Fin d.fillingCount) → SolidTorusPiece presentation (piece (some m))
  port : Fin d.ports ⊕ Fin d.fillingCount ≃ Fin d.k
  seam : Fin d.fillingCount ≃ Fin presentation.pairing.count
  free : Fin d.ports ≃ Fin presentation.externalCount
  free_port : ∀ r, (product.port (port (.inl r))).val = .inr (.inr (free r))
  filled_port : ∀ m, (product.port (port (.inr m))).val = .inr (.inl (seam m))
  solid_port : ∀ m, ((solid m).port 0).val = .inl (seam m)
  slope : ∀ m, torusUnit (presentation.pairing.matching (seam m)) • meridianSlope =
    PrimitiveSlope.mk (d.fillingSlope m) (d.isPrimitive_fillingSlope m)

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem components_count (B : SeifertBlock W d) :
    B.presentation.components.count = d.fillingCount + 1 := by
  rw [← Fintype.card_fin B.presentation.components.count, ← Fintype.card_congr B.piece,
    Fintype.card_option, Fintype.card_fin]

theorem pairing_count (B : SeifertBlock W d) :
    B.presentation.pairing.count = d.fillingCount :=
  (Fin.equiv_iff_eq.mp ⟨B.seam⟩).symm

theorem externalCount_eq (B : SeifertBlock W d) : B.presentation.externalCount = d.ports :=
  (Fin.equiv_iff_eq.mp ⟨B.free⟩).symm

theorem torusMatrix_meridian (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    (torusMatrix (B.presentation.pairing.matching (B.seam m)) 0 0,
        torusMatrix (B.presentation.pairing.matching (B.seam m)) 1 0) = d.fillingSlope m ∨
      (torusMatrix (B.presentation.pairing.matching (B.seam m)) 0 0,
        torusMatrix (B.presentation.pairing.matching (B.seam m)) 1 0) = -d.fillingSlope m := by
  have h := B.slope m
  rw [meridianSlope, PrimitiveSlope.smul_mk, PrimitiveSlope.mk_eq_mk_iff] at h
  simp only [smulVec, val_torusUnit, mul_one, mul_zero, add_zero] at h
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

theorem delta_fiberSlope (B : SeifertBlock W d) (m : Fin d.fillingCount) :
    PrimitiveSlope.delta (torusUnit (B.presentation.pairing.matching (B.seam m)) • meridianSlope)
      fiberSlope = (d.fillingSlope m).1.natAbs := by
  rw [B.slope m, fiberSlope, PrimitiveSlope.delta_mk]
  simp [slopeDet]

def IsGoodBlock (B : SeifertBlock W d) : Prop := B.presentation.external.incompressible

theorem isGoodBlock_iff (B : SeifertBlock W d) : B.IsGoodBlock ↔ ∀ r x, Function.Injective
    (FundamentalGroup.map (B.presentation.external.boundaryMap (B.free r)) x) := by
  refine ⟨fun h r => h (B.free r), fun h e => ?_⟩
  have := h (B.free.symm e)
  rwa [Equiv.apply_symm_apply] at this

theorem isGoodBlock_of_ports_eq_zero (B : SeifertBlock W d) (h : d.ports = 0) :
    B.IsGoodBlock := by
  intro e
  exact absurd (B.free.symm e).isLt (by omega)

end SeifertBlock

def t2IntervalData : SeifertData :=
  ⟨2, 2, [], [], by norm_num, by norm_num, by decide, by decide, rfl⟩

def twistedIBundleData : SeifertData :=
  ⟨3, 1, [(2, 1), (2, -1)], [], by norm_num, le_rfl, by decide, by decide, rfl⟩

theorem twistedIBundleData_eq_retwist : twistedIBundleData = SeifertData.retwist
    ⟨3, 1, [(2, 1), (2, 1)], [], by norm_num, le_rfl, by decide, by decide, rfl⟩ ![0, 1] := by
  simp [twistedIBundleData, SeifertData.retwist, List.ofFn_succ]

abbrev T2Interval (W : CompactCarrier.{u}) := SeifertBlock W t2IntervalData

abbrev TwistedIBundle (W : CompactCarrier.{u}) := SeifertBlock W twistedIBundleData

theorem not_isSolidTorus_t2IntervalData : ¬ t2IntervalData.IsSolidTorus := by
  simp [SeifertData.IsSolidTorus, t2IntervalData]

theorem not_isSolidTorus_twistedIBundleData : ¬ twistedIBundleData.IsSolidTorus := by
  simp [SeifertData.IsSolidTorus, twistedIBundleData]

theorem openModelOf_t2IntervalData :
    t2IntervalData.openModelOf (by decide) not_isSolidTorus_t2IntervalData = .euclidean :=
  (SeifertData.openModelOf_eq_euclidean_iff _ _ _).2 (Or.inl ⟨rfl, rfl⟩)

theorem openModelOf_twistedIBundleData :
    twistedIBundleData.openModelOf (by decide) not_isSolidTorus_twistedIBundleData =
      .euclidean :=
  (SeifertData.openModelOf_eq_euclidean_iff _ _ _).2 (Or.inr ⟨rfl, rfl⟩)

def SphereBoundsBallIn (W : CompactCarrier.{u})
    (e : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → W.Carrier) : Prop :=
  ∃ G : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞,
    closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ G.source ∧
      G '' sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 = range e

def IsIrreducibleCarrier (W : CompactCarrier.{u}) : Prop :=
  ∀ e : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → W.Carrier,
    Manifold.IsSmoothEmbedding (𝓡 2) W.model ∞ e → range e ⊆ W.interior →
      SphereBoundsBallIn W e

theorem isIrreducibleCarrier_carrier_iff (P : ConnectedClosedOrientedManifold.{u} 3) :
    IsIrreducibleCarrier (NoCuts.carrier P) ↔ IsIrreducible P :=
  ⟨fun h e he => h e he fun _ _ => BoundarylessManifold.isInteriorPoint,
    fun h e he _ => h e he⟩

end GC.Seifert
