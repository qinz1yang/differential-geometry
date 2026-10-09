import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimArcExitOBDd

/-!
# The slim arc exit with the end data in the exit's own vocabulary and the GLOBAL free-end form
(lane S-BD2d2, suffix `_OBDd`), group G10g

Lane O-BD1 (by S-BD2d2), hlift, `SlimCutPieces74`. `exists_slimArcExit_OBDd` (G10e) with the
`rel3` data stated through the API of `SlimPieceExit74` (`slice`, `endKind`, `endFn`) instead of the
sphere / torus structures, and the defining function of every free end in the GLOBAL form
`endFn b y = a (f₃ y)` with `a` smooth on the whole ambient base space:

* `BoundaryGaf02ChainE.exists_slimArcExit_glob_OBDd`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- `ClosureSphere` is connected. -/
local instance closureSphereConnectedGlob_OBDd : ConnectedSpace ClosureSphere.{0} :=
  have hS : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
  Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **The slim exit of a sphere interval product over a base arc**, `rel3` data in the exit's own
vocabulary, free ends in the global form. -/
theorem sphereArcExitGlob_of_product_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (P : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) (W.pieceInterior ⊤)
      (dec.bases.base 2) (dec.bases.base 2))
    (hP : ∀ x, P.toFun x = C.slimF_OBDd x) {k₀ : ℕ} {E : BoundaryTori W k₀} {Z : ZeroDomains W}
    {Cu : CuspCores W E}
    (hface : ∀ y ∈ C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2),
      IsPreconnected (dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y}) →
      ∃ F : NeighbourFace Z Cu,
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y} = neighbourSet F)
    (γ' : SmoothEmbeddedBaseArc_EFE (dec.bases.base 2))
    (m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → W.Carrier)
    (hm : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) W.model ∞ m) (hinj : Injective m)
    (hfr : ∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) W.model m z))
    (hrange : range m = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ'.toFun '' Icc 0 1))
    (hends : ∀ b, range (fun z => m (z, iccEnd b)) =
      dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)}) :
    ∃ x : SlimPieceExit74 Z Cu,
      range x.piece.map = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ'.toFun '' Icc 0 1) ∧
      ∃ hI : slimModelIsInterval x.model, ∀ b : Bool,
        x.slice b = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)} ∧
        (x.endKind b hI = none ↔ γ'.toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
          (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∧
        (x.endKind b hI = none → ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA
          (Fin S.packet.cusp.count) → ℝ, ContDiff ℝ ∞ a ∧
            ∀ y, x.endFn b hI y = a (C.toChain.stageMap 2 y)) := by
  have hmc : Continuous m := hm.continuous
  have hconn : ∀ b, IsPreconnected (range fun z => m (z, iccEnd b)) := fun b =>
    isPreconnected_range (hmc.comp (continuous_id.prodMk continuous_const))
  obtain ⟨ends, hfree, hiff⟩ := C.exists_arcEnds_OBDd dec P hP hface γ'
    (pieceSet := range m) (slice := fun b => range fun z => m (z, iccEnd b)) hrange hends hconn
  let a : SphereArcExit74 Z Cu := ⟨m, hm, hinj, hfr, ends⟩
  exact ⟨.sphereArc a, (range_sphereIntervalPiece a.F a.smooth
    (sphereArc_bijective74 a) a.injective).trans hrange, trivial,
    fun b => ⟨hends b, hiff b, hfree b⟩⟩

include C in
/-- **The slim exit of a torus interval product over a base arc**, `rel3` data in the exit's own
vocabulary, free ends in the global form. -/
theorem torusArcExitGlob_of_product_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (P : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) (W.pieceInterior ⊤)
      (dec.bases.base 2) (dec.bases.base 2))
    (hP : ∀ x, P.toFun x = C.slimF_OBDd x) {k₀ : ℕ} {E : BoundaryTori W k₀} {Z : ZeroDomains W}
    {Cu : CuspCores W E}
    (hface : ∀ y ∈ C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2),
      IsPreconnected (dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y}) →
      ∃ F : NeighbourFace Z Cu,
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y} = neighbourSet F)
    (γ' : SmoothEmbeddedBaseArc_EFE (dec.bases.base 2))
    (m : Torus × Icc (0 : ℝ) 1 → W.Carrier)
    (hm : ContMDiff (torusModel.prod (𝓡∂ 1)) W.model ∞ m) (hinj : Injective m)
    (hfr : ∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) W.model m z))
    (hrange : range m = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ'.toFun '' Icc 0 1))
    (hends : ∀ b, range (fun z => m (z, iccEnd b)) =
      dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)}) :
    ∃ x : SlimPieceExit74 Z Cu,
      range x.piece.map = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ'.toFun '' Icc 0 1) ∧
      ∃ hI : slimModelIsInterval x.model, ∀ b : Bool,
        x.slice b = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)} ∧
        (x.endKind b hI = none ↔ γ'.toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
          (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∧
        (x.endKind b hI = none → ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA
          (Fin S.packet.cusp.count) → ℝ, ContDiff ℝ ∞ a ∧
            ∀ y, x.endFn b hI y = a (C.toChain.stageMap 2 y)) := by
  have hmc : Continuous m := hm.continuous
  have hconn : ∀ b, IsPreconnected (range fun z => m (z, iccEnd b)) := fun b =>
    isPreconnected_range (hmc.comp (continuous_id.prodMk continuous_const))
  obtain ⟨ends, hfree, hiff⟩ := C.exists_arcEnds_OBDd dec P hP hface γ'
    (pieceSet := range m) (slice := fun b => range fun z => m (z, iccEnd b)) hrange hends hconn
  let a : TorusArcExit74 Z Cu := ⟨m, hm, hinj, hfr, ends⟩
  exact ⟨.torusArc a, (range_torusIntervalPiece a.F a.smooth
    (torusArc_bijective74 a) a.injective).trans hrange, trivial,
    fun b => ⟨hends b, hiff b, hfree b⟩⟩

include C in
/-- **The slim exit over a base arc, `rel3` data in the exit's own vocabulary, free ends in the
global form** (`endFn b y = a (f₃ y)`, `a` smooth). -/
theorem exists_slimArcExit_glob_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (P : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) (W.pieceInterior ⊤)
      (dec.bases.base 2) (dec.bases.base 2))
    (hP : ∀ x, P.toFun x = C.slimF_OBDd x) {k₀ : ℕ} {E : BoundaryTori W k₀} {Z : ZeroDomains W}
    {Cu : CuspCores W E}
    (hface : ∀ y ∈ C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2),
      IsPreconnected (dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y}) →
      ∃ F : NeighbourFace Z Cu,
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {y} = neighbourSet F)
    (γ' : SmoothEmbeddedBaseArc_EFE (dec.bases.base 2)) :
    ∃ x : SlimPieceExit74 Z Cu,
      range x.piece.map = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ'.toFun '' Icc 0 1) ∧
      ∃ hI : slimModelIsInterval x.model, ∀ b : Bool,
        x.slice b = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)} ∧
        (x.endKind b hI = none ↔ γ'.toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
          (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∧
        (x.endKind b hI = none → ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA
          (Fin S.packet.cusp.count) → ℝ, ContDiff ℝ ∞ a ∧
            ∀ y, x.endFn b hI y = a (C.toChain.stageMap 2 y)) := by
  rcases C.exists_arcProduct_OBDd dec P hP γ' with
    ⟨m, hm, hinj, hfr, -, hrange, hends⟩ | ⟨m, hm, hinj, hfr, -, hrange, hends⟩
  · exact C.sphereArcExitGlob_of_product_OBDd dec P hP hface γ' m hm hinj hfr hrange hends
  · exact C.torusArcExitGlob_of_product_OBDd dec P hP hface γ' m hm hinj hfr hrange hends

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
