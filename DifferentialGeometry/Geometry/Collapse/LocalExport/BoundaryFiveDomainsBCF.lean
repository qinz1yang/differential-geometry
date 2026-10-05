import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCompactSlimFacesSatBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceCorollaries

/-!
# BCF03, first sentence: the five domains cover `W` with disjoint ambient interiors
(lane B-BCF134)

Blueprint `master207B.tex`, BCF03 (B:9834–9884): "The five domains `Z, C, S, P, R` cover `M`, with
disjoint ambient interiors and the actual face identities above." On the saturated cores
`Z : BoundaryInitialCoresSpecSat C Bs` (lead decision 13:4x) and
`Kc : BoundaryCompactSlimChoice Bs Z.toBoundaryInitialCoresSpec`, with `P_e = Kc.edgePiece`,
`R_c = Kc.remainder`:

* `BoundaryCompactSlimChoice.five_domains_cover_BCF03`: `Z ∪ C_∂ ∪ S ∪ P_e ∪ R_c = W`
  (BIFACE's `cover_BIF` and `M₂_eq_edgePiece_union_remainder_BIF`);
* `five_domains_interiors_BCF03`: the interiors of `Z ∪ C_∂`, `S`, `P_e`, `R_c` are pairwise
  disjoint (`S ⊆ M₁` from the saturated cores; `P_e, R_c ⊆ M₂`; `int P_e ⊆ int_{M₂} P_e`);
* `BoundaryInitialCoresSpec.disjoint_interior_core_BCF03`: distinct zero cores have disjoint
  interiors.

The separation of the zero cores from the cusp cores `C_b` (and of distinct `C_b`) is BCG06's
separated-branch output (`cuspCore_BIF_disjoint_initialCores_BCG6K`), not an interface fact; the
face partition (BCF03.a) and the cusp dichotomy need BCF02's horizontal disks and circle-bundle
faces (see `build-logs/resume/state-B-BCF134.md`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02Bases C}

/-- Distinct zero cores have disjoint interiors. -/
theorem BoundaryInitialCoresSpec.disjoint_interior_core_BCF03 (ZC : BoundaryInitialCoresSpec C)
    {k l : Fin ZC.count} (hkl : k ≠ l) : Disjoint (interior (ZC.core k)) (interior (ZC.core l)) :=
  (ZC.pairwise_disjoint hkl).mono interior_subset interior_subset

namespace BoundaryCompactSlimChoice

section Plain

variable {ZC : BoundaryInitialCoresSpec C} (Kc : BoundaryCompactSlimChoice Bs ZC)

/-- `P_e ⊆ M₂`. -/
theorem edgePiece_subset_M₂_BCF03 : Kc.edgePiece ⊆ Kc.M₂ :=
  inter_subset_left

/-- `R_c ⊆ M₂`. -/
theorem remainder_subset_M₂_BCF03 : Kc.remainder ⊆ Kc.M₂ :=
  sdiff_subset

/-- **The five domains cover `W`**: `Z ∪ C_∂ ∪ S ∪ P_e ∪ R_c = W`. -/
theorem five_domains_cover_BCF03 :
    ZC.union ∪ C.cuspCores_BIF ∪ Kc.piece ∪ Kc.edgePiece ∪ Kc.remainder = univ := by
  rw [union_assoc _ Kc.edgePiece, ← Kc.M₂_eq_edgePiece_union_remainder_BIF]
  exact Kc.cover_BIF

/-- `P_e` and `R_c` have disjoint interiors. -/
theorem disjoint_interior_edgePiece_remainder_BCF03 :
    Disjoint (interior Kc.edgePiece) (interior Kc.remainder) := by
  refine Set.disjoint_left.mpr fun x hxP hxR => (interior_subset hxR).2 ?_
  exact mem_relInterior_iff_BCF.mpr ⟨(interior_subset hxR).1, interior Kc.edgePiece,
    isOpen_interior, hxP, fun _ hy => interior_subset hy.1⟩

end Plain

variable {Z : BoundaryInitialCoresSpecSat C Bs}
  (Kc : BoundaryCompactSlimChoice Bs Z.toBoundaryInitialCoresSpec)

/-- **The five domains have pairwise disjoint ambient interiors** (`Z ∪ C_∂`, `S`, `P_e`, `R_c`),
on the saturated cores. -/
theorem five_domains_interiors_BCF03 :
    Disjoint (interior (Z.union ∪ C.cuspCores_BIF)) (interior Kc.piece) ∧
      Disjoint (interior (Z.union ∪ C.cuspCores_BIF)) (interior Kc.edgePiece) ∧
      Disjoint (interior (Z.union ∪ C.cuspCores_BIF)) (interior Kc.remainder) ∧
      Disjoint (interior Kc.piece) (interior Kc.edgePiece) ∧
      Disjoint (interior Kc.piece) (interior Kc.remainder) ∧
      Disjoint (interior Kc.edgePiece) (interior Kc.remainder) :=
  ⟨Kc.disjoint_interior_union_piece_BCF01,
    Kc.disjoint_interior_union_M₂_BCF01.mono_right (interior_mono Kc.edgePiece_subset_M₂_BCF03),
    Kc.disjoint_interior_union_M₂_BCF01.mono_right (interior_mono Kc.remainder_subset_M₂_BCF03),
    Kc.disjoint_interior_piece_M₂_BCF01.mono_right (interior_mono Kc.edgePiece_subset_M₂_BCF03),
    Kc.disjoint_interior_piece_M₂_BCF01.mono_right (interior_mono Kc.remainder_subset_M₂_BCF03),
    Kc.disjoint_interior_edgePiece_remainder_BCF03⟩

end BoundaryCompactSlimChoice

end DifferentialGeometry.Geometry.Collapse
