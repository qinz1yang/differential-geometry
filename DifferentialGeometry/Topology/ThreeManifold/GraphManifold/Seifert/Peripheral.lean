import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Blocks
import DifferentialGeometry.Topology.FundamentalGroup.Product
import DifferentialGeometry.Topology.FundamentalGroup.Retraction

/-!
# Peripheral subgroups of product-fibred pieces

Chapter 6, packet K10, first tier. `PlanarBase.boundaryCircle B j` is the inclusion of boundary
circle `j` of a planar base. For `2 ≤ k` it has a continuous left inverse `boundaryRetraction`
read off the model in `ℂ`: about a hole `j ≠ 0` it normalises `conj (z - c_j)`; on the outer
circle it normalises `(3 - c) z - c (3 - ‖z‖)`, `c = planarHoleCenter k` the centre of hole `1`,
which vanishes only at `c`, outside the model. Hence `planarBase_boundary_injective` at every
basepoint. For `k = 1` (the disc under a solid torus) the circle bounds, so `2 ≤ k` is needed.

For a product-fibred piece `P` with `Φ : Pₖ × S¹ ≃ piece`, `fundamentalGroupEquiv` is
`π₁(piece, Φ (b, u)) ≃* π₁(Pₖ, b) × π₁(S¹, u)`, the inverse of `Φ₊` followed by
`fundamentalGroupProdEquiv`. Port `j` is `portMap j = Φ ∘ (boundaryCircle j × id)`; it is the
boundary-torus map of the piece's own boundary tori (`pieceBoundaryTori_boundaryMap`), and
`fundamentalGroupEquiv_map_portMap` is the naturality square: on `π₁` the port is the
boundary-circle inclusion times the identity. For `2 ≤ k` every port has the continuous left
inverse `portRetraction`, so `pieceBoundaryTori_incompressible` holds in the form of
`BoundaryTori.incompressible` (every port, every basepoint), as `(T.ofPiece i).external` too.

For a Seifert block, `external_boundaryMap_free` writes free port `r` as the product port pushed
into `W` by the reconstruction. Without fillings that map is a homeomorphism from the product
piece onto `W`, so the block is good (`isGoodBlock_of_fillingCount_eq_zero`, hence
`t2Interval_isGoodBlock`). Filled blocks are only stated: `FilledBlockGoodness` (a block with a
free port that is not a solid torus is good) is a named proposition, not proved here; it needs
the amalgam over the filling tori and the orbifold fundamental group of the base.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

def planarHoleCenter (k : ℕ) : ℝ := if k = 2 then 0 else 3 / 2

def planarRetractionVector (k : ℕ) (j : Fin k) (z : ℂ) : ℂ :=
  if j.val = 0 then
    (3 - planarHoleCenter k : ℝ) * z - (planarHoleCenter k : ℝ) * (3 - ‖z‖ : ℝ)
  else conj (z - planarCenter k j)

theorem continuous_planarRetractionVector (k : ℕ) (j : Fin k) :
    Continuous (planarRetractionVector k j) := by
  unfold planarRetractionVector
  split_ifs
  · fun_prop
  · fun_prop

theorem planarHoleCenter_nonneg (k : ℕ) : 0 ≤ planarHoleCenter k := by
  unfold planarHoleCenter
  split_ifs <;> norm_num

theorem planarHoleCenter_lt (k : ℕ) : planarHoleCenter k < 3 := by
  unfold planarHoleCenter
  split_ifs <;> norm_num

theorem planarCenter_one_eq {k : ℕ} (hk : 2 ≤ k) :
    planarCenter k ⟨1, hk⟩ = planarHoleCenter k := by
  simp [planarCenter, planarHoleCenter]

theorem planarRetractionVector_ne_zero {k : ℕ} (hk : 2 ≤ k) (j : Fin k) {z : ℂ}
    (hz : z ∈ planarModel k) : planarRetractionVector k j z ≠ 0 := by
  intro h
  unfold planarRetractionVector at h
  split_ifs at h with hj
  · have hd := hz.2 ⟨1, hk⟩ one_ne_zero
    rw [planarCenter_one_eq hk] at hd
    have hs0 := planarHoleCenter_nonneg k
    have hs3 := planarHoleCenter_lt k
    have hne : ((3 - planarHoleCenter k : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (by linarith)
    have hz' :
        z = ((planarHoleCenter k * (3 - ‖z‖) / (3 - planarHoleCenter k) : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, Complex.ofReal_mul, eq_div_iff hne, mul_comm]
      exact sub_eq_zero.1 h
    have hn : ‖z‖ = planarHoleCenter k * (3 - ‖z‖) / (3 - planarHoleCenter k) := by
      conv_lhs => rw [hz']
      rw [Complex.norm_real, Real.norm_of_nonneg
        (div_nonneg (mul_nonneg hs0 (by linarith [hz.1])) (by linarith))]
    have hzs : ‖z‖ = planarHoleCenter k := by
      rw [eq_div_iff (by linarith)] at hn
      linarith
    have hzc : z = (planarHoleCenter k : ℂ) := by rw [hz', ← hn, hzs]
    rw [hzc, sub_self, norm_zero] at hd
    norm_num at hd
  · have hd := hz.2 j hj
    have hn := congrArg (fun w => ‖w‖) h
    simp only [Complex.norm_conj, norm_zero] at hn
    linarith

theorem planarRetractionVector_planarCircleMap (k : ℕ) (j : Fin k) (t : Circle) :
    ∃ a : ℝ, 0 < a ∧ planarRetractionVector k j (planarCircleMap k j t) = (a : ℂ) * t := by
  unfold planarRetractionVector planarCircleMap
  by_cases hj : j.val = 0
  · have hc : planarCenter k j = 0 := by simp [planarCenter, hj]
    have hr : planarRadius j = 3 := by simp [planarRadius, hj]
    refine ⟨3 * (3 - planarHoleCenter k), by linarith [planarHoleCenter_lt k], ?_⟩
    have hn : ‖((0 : ℝ) : ℂ) + ((3 : ℝ) : ℂ) * t‖ = 3 := by
      rw [Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_real, Circle.norm_coe]
      norm_num
    simp only [hj, ↓reduceIte, hc, hr, hn]
    push_cast
    ring
  · have hr : planarRadius j = 1 / 2 := by simp [planarRadius, hj]
    refine ⟨1 / 2, by norm_num, ?_⟩
    simp only [hj, ↓reduceIte, hr, add_sub_cancel_left, map_mul, Complex.conj_ofReal,
      Complex.conj_conj]

namespace PlanarBase

variable {k : ℕ}

theorem collar_zero_mem_source (B : PlanarBase.{u} k) (j : Fin k) (t : Circle) :
    (t, halfZero) ∈ (B.collar j).source := by
  rw [B.source_eq]
  change (0 : ℝ) < 1
  norm_num

def boundaryCircle (B : PlanarBase.{u} k) (j : Fin k) : C(Circle, B.surface.Carrier) :=
  ⟨fun t => B.collar j (t, halfZero),
    (B.collar j).contMDiffOn.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      (B.collar_zero_mem_source j)⟩

theorem embedding_mem (B : PlanarBase.{u} k) (x : B.surface.Carrier) :
    B.embedding x ∈ planarModel k :=
  B.range_embedding ▸ mem_range_self x

def boundaryRetraction (B : PlanarBase.{u} k) (hk : 2 ≤ k) (j : Fin k) :
    C(B.surface.Carrier, Circle) where
  toFun x := ⟨planarRetractionVector k j (B.embedding x) /
      (‖planarRetractionVector k j (B.embedding x)‖ : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2
      (planarRetractionVector_ne_zero hk j (B.embedding_mem x)))])⟩
  continuous_toFun := by
    have hc := (continuous_planarRetractionVector k j).comp
      B.isSmoothEmbedding.isEmbedding.continuous
    refine Continuous.subtype_mk (hc.div (Complex.continuous_ofReal.comp hc.norm) fun x => ?_) _
    exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2
      (planarRetractionVector_ne_zero hk j (B.embedding_mem x)))

theorem boundaryRetraction_leftInverse (B : PlanarBase.{u} k) (hk : 2 ≤ k) (j : Fin k) :
    Function.LeftInverse (B.boundaryRetraction hk j) (B.boundaryCircle j) := by
  intro t
  apply Circle.coe_injective
  change planarRetractionVector k j (B.embedding (B.collar j (t, halfZero))) /
      (‖planarRetractionVector k j (B.embedding (B.collar j (t, halfZero)))‖ : ℂ) = t
  obtain ⟨a, ha, h⟩ := planarRetractionVector_planarCircleMap k j t
  rw [B.embedding_collar, h, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg ha.le, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.2 ha.ne')]

theorem boundary_injective (B : PlanarBase.{u} k) (hk : 2 ≤ k) (j : Fin k) (t : Circle) :
    Function.Injective (FundamentalGroup.map (B.boundaryCircle j) t) :=
  injective_fundamentalGroup_map_of_leftInverse _ _ (B.boundaryRetraction_leftInverse hk j) t

end PlanarBase

theorem planarBase_boundary_injective {k : ℕ} (hk : 2 ≤ k) (B : PlanarBase.{u} k) (j : Fin k)
    (t : Circle) : Function.Injective (FundamentalGroup.map (B.boundaryCircle j) t) :=
  B.boundary_injective hk j t

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}
  {k : ℕ}

def trivializationMap (P : ProductFibredPiece T i k) :
    C(P.base.surface.Carrier × Circle, T.components.piece i) :=
  P.trivialization.toHomeomorph

def trivializationInv (P : ProductFibredPiece T i k) :
    C(T.components.piece i, P.base.surface.Carrier × Circle) :=
  P.trivialization.toHomeomorph.symm

theorem trivializationInv_leftInverse (P : ProductFibredPiece T i k) :
    Function.LeftInverse P.trivializationInv P.trivializationMap :=
  P.trivialization.symm_apply_apply

theorem bijective_map_trivializationMap (P : ProductFibredPiece T i k)
    (y : P.base.surface.Carrier × Circle) :
    Function.Bijective (FundamentalGroup.map P.trivializationMap y) :=
  bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse
    P.trivialization.toHomeomorph.symm.toHomotopyEquiv _ P.trivializationInv_leftInverse y

def fundamentalGroupEquiv (P : ProductFibredPiece T i k) (b : P.base.surface.Carrier)
    (u : Circle) :
    FundamentalGroup (T.components.piece i) (P.trivialization (b, u)) ≃*
      FundamentalGroup P.base.surface.Carrier b × FundamentalGroup Circle u :=
  (MulEquiv.ofBijective _ (P.bijective_map_trivializationMap (b, u))).symm.trans
    (fundamentalGroupProdEquiv b u)

def portMap (P : ProductFibredPiece T i k) (j : Fin k) : C(Torus, T.components.piece i) :=
  P.trivializationMap.comp ((P.base.boundaryCircle j).prodMap (ContinuousMap.id Circle))

theorem portMap_apply (P : ProductFibredPiece T i k) (j : Fin k) (x : Torus) :
    P.portMap j x = P.trivialization (P.base.boundaryCircle j x.1, x.2) :=
  rfl

theorem fundamentalGroupEquiv_map_portMap (P : ProductFibredPiece T i k) (j : Fin k)
    (x : Torus) (g : FundamentalGroup Torus x) :
    P.fundamentalGroupEquiv (P.base.boundaryCircle j x.1) x.2
        (FundamentalGroup.map (P.portMap j) x g) =
      Prod.map (FundamentalGroup.map (P.base.boundaryCircle j) x.1) id
        (fundamentalGroupProdEquiv x.1 x.2 g) := by
  have h : FundamentalGroup.map (P.portMap j) x g =
      MulEquiv.ofBijective _
        (P.bijective_map_trivializationMap (P.base.boundaryCircle j x.1, x.2))
        (FundamentalGroup.map ((P.base.boundaryCircle j).prodMap (ContinuousMap.id Circle)) x
          g) := by
    induction g using Path.Homotopic.Quotient.ind with
    | mk p => rfl
  have h' : (MulEquiv.ofBijective _
      (P.bijective_map_trivializationMap (P.base.boundaryCircle j x.1, x.2))).symm
      (FundamentalGroup.map (P.portMap j) x g) =
      FundamentalGroup.map ((P.base.boundaryCircle j).prodMap (ContinuousMap.id Circle)) x g := by
    rw [h]
    exact MulEquiv.symm_apply_apply _ _
  refine (congrArg (fundamentalGroupProdEquiv _ _) h').trans ?_
  induction g using Path.Homotopic.Quotient.ind with
  | mk p => rfl

theorem pieceBoundaryTori_boundaryMap (P : ProductFibredPiece T i k) (j : Fin k) :
    (T.pieceBoundaryTori i).boundaryMap (Fintype.equivFin _ (P.port j)) = P.portMap j := by
  ext t : 1
  change T.pieceCollar i ((Fintype.equivFin _).symm (Fintype.equivFin _ (P.port j)))
      (t, halfZero) = P.trivialization (P.base.collar j (t.1, halfZero), t.2)
  rw [Equiv.symm_apply_apply, P.collar_eq j _ (zero_mem_halfCollarSource t)]

def portRetraction (P : ProductFibredPiece T i k) (hk : 2 ≤ k) (j : Fin k) :
    C(T.components.piece i, Torus) :=
  ((P.base.boundaryRetraction hk j).prodMap (ContinuousMap.id Circle)).comp P.trivializationInv

theorem portRetraction_leftInverse (P : ProductFibredPiece T i k) (hk : 2 ≤ k) (j : Fin k) :
    Function.LeftInverse (P.portRetraction hk j) (P.portMap j) := by
  intro y
  change ((P.base.boundaryRetraction hk j).prodMap (ContinuousMap.id Circle))
    (P.trivialization.symm (P.trivialization (P.base.boundaryCircle j y.1, y.2))) = y
  rw [Diffeomorph.symm_apply_apply]
  exact Prod.ext (P.base.boundaryRetraction_leftInverse hk j y.1) rfl

theorem portMap_injective (P : ProductFibredPiece T i k) (hk : 2 ≤ k) (j : Fin k) (x : Torus) :
    Function.Injective (FundamentalGroup.map (P.portMap j) x) :=
  injective_fundamentalGroup_map_of_leftInverse _ _ (P.portRetraction_leftInverse hk j) x

theorem pieceBoundaryTori_incompressible (P : ProductFibredPiece T i k) (hk : 2 ≤ k) :
    (T.pieceBoundaryTori i).incompressible := by
  intro e x
  obtain ⟨j, rfl⟩ : ∃ j, Fintype.equivFin _ (P.port j) = e :=
    ⟨P.port.symm ((Fintype.equivFin _).symm e), by simp⟩
  rw [P.pieceBoundaryTori_boundaryMap]
  exact P.portMap_injective hk j x

theorem ofPiece_external_incompressible (P : ProductFibredPiece T i k) (hk : 2 ≤ k) :
    (T.ofPiece i).external.incompressible :=
  P.pieceBoundaryTori_incompressible hk

end ProductFibredPiece

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem product_incompressible (B : SeifertBlock W d) (hk : 2 ≤ d.k) :
    (B.presentation.pieceBoundaryTori (B.piece none)).incompressible :=
  B.product.pieceBoundaryTori_incompressible hk

def productToCarrier (B : SeifertBlock W d) :
    C(B.presentation.components.piece (B.piece none), W.Carrier) :=
  ⟨fun y => B.presentation.reconstruction (B.presentation.pairing.quotientMap y.val),
    B.presentation.quotient_smooth.continuous.comp continuous_subtype_val⟩

theorem external_boundaryMap_free (B : SeifertBlock W d) (r : Fin d.ports) :
    B.presentation.external.boundaryMap (B.free r) =
      B.productToCarrier.comp (B.product.portMap (B.port (.inl r))) := by
  ext t : 1
  have hc := B.product.collar_eq (B.port (.inl r)) _ (zero_mem_halfCollarSource t)
  change B.presentation.external.collar (B.free r) (t, halfZero) =
    B.presentation.reconstruction (B.presentation.pairing.quotientMap
      (B.product.trivialization (B.product.base.collar (B.port (.inl r)) (t.1, halfZero),
        t.2)).val)
  rw [← hc, B.presentation.pieceCollar_apply _ _ (zero_mem_halfCollarSource t), B.free_port r]
  exact (B.presentation.marked_collar _ _ (zero_mem_halfCollarSource t)).symm

theorem productToCarrier_injective (B : SeifertBlock W d) (h0 : d.fillingCount = 0) :
    Function.Injective B.productToCarrier := by
  intro y y' h
  have h' := Quotient.exact (B.presentation.reconstruction.injective h)
  rcases h' with h' | ⟨m, _⟩
  · exact Subtype.ext h'
  · have hm := m.isLt
    have hc := B.pairing_count
    omega

theorem productToCarrier_surjective (B : SeifertBlock W d) (h0 : d.fillingCount = 0) :
    Function.Surjective B.productToCarrier := by
  intro w
  obtain ⟨x, hx⟩ := Quotient.mk''_surjective (B.presentation.reconstruction.symm w)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (B.presentation.components.covers.symm ▸ Set.mem_univ x)
  have hn : B.piece.symm i = none := by
    rcases hm : B.piece.symm i with _ | m
    · rfl
    · have := m.isLt
      omega
  rw [← B.piece.apply_symm_apply i, hn] at hi
  refine ⟨⟨x, hi⟩, ?_⟩
  change B.presentation.reconstruction (Quotient.mk'' x) = w
  rw [hx, Homeomorph.apply_symm_apply]

theorem isGoodBlock_of_fillingCount_eq_zero (B : SeifertBlock W d) (hk : 2 ≤ d.k)
    (h0 : d.fillingCount = 0) : B.IsGoodBlock := by
  have : CompactSpace (B.presentation.components.piece (B.piece none)) :=
    isCompact_iff_compactSpace.mp (B.presentation.components.piece_compact _)
  let e := B.productToCarrier.continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _
      ⟨B.productToCarrier_injective h0, B.productToCarrier_surjective h0⟩)
  refine B.isGoodBlock_iff.2 fun r x => ?_
  rw [B.external_boundaryMap_free r]
  refine injective_fundamentalGroup_map_of_leftInverse _
    ((B.product.portRetraction hk (B.port (.inl r))).comp (e.symm : C(W.Carrier, _)))
    (fun t => ?_) x
  change B.product.portRetraction hk _ (e.symm (e (B.product.portMap _ t))) = t
  rw [Homeomorph.symm_apply_apply]
  exact B.product.portRetraction_leftInverse hk _ t

end SeifertBlock

theorem t2Interval_isGoodBlock {W : CompactCarrier.{u}} (B : T2Interval W) : B.IsGoodBlock :=
  B.isGoodBlock_of_fillingCount_eq_zero le_rfl rfl

def FilledBlockGoodness : Prop :=
  ∀ (W : CompactCarrier.{u}) (d : SeifertData) (B : SeifertBlock W d), 0 < d.ports →
    ¬ d.IsSolidTorus → B.IsGoodBlock

end GC.Seifert
