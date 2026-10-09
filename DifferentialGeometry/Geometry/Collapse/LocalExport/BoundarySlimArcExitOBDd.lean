import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimArcEndsOBDd

/-!
# The slim piece exit over a base arc, with the end data of `rel3` (lane S-BD2d2, `_OBDd`), G10e

Lane O-BD1 (by S-BD2d2), hlift, `SlimCutPieces74`. Boundary twin of `exists_slimArcExit3_OCL`
(closed route): over ANY smooth embedded base arc `γ` of `B₃` the slim piece exit of the whole
preimage `X₃ ∩ f₃⁻¹(γ [0, 1])`, a sphere or torus arc exit `a` with

* the projection identity `f₃ (a.F z) = γ z.2` and both end slices the whole end fibres
  `X₃ ∩ f₃⁻¹{γ (iccEnd b)}`;
* (rel3, clause 1) for every free end `b` (`a.ends.kind b = none`) a smooth `e` on an open `Ne ∋`
  `f₃ y` (`y ∈ a.ends.near b`) with `a.ends.fn b y = e (f₃ y)` (here `Ne = univ`);
* (rel3, clause 3) the end `b` is free iff the end value is not a face point
  `f₃(∂M₁ ∩ X₃)` (zero faces and cusp fronts).
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
local instance closureSphereConnected_OBDd : ConnectedSpace ClosureSphere.{0} :=
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
/-- **The slim exit of a sphere interval product over a base arc** with the `rel3` end data. -/
theorem sphereArcExit_of_product_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
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
    (hproj : ∀ z, C.toChain.stageMap 2 (m z) = γ'.toFun z.2)
    (hrange : range m = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ'.toFun '' Icc 0 1))
    (hends : ∀ b, range (fun z => m (z, iccEnd b)) =
      dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)}) :
    ∃ x : SlimPieceExit74 Z Cu,
      range x.piece.map = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ'.toFun '' Icc 0 1) ∧
      ((∃ a : SphereArcExit74 Z Cu, x = .sphereArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = γ'.toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) =
            dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            γ'.toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∨
        (∃ a : TorusArcExit74 Z Cu, x = .torusArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = γ'.toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) =
            dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            γ'.toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))) := by
  have hconn : ∀ b, IsPreconnected (range fun z => m (z, iccEnd b)) := fun b =>
    isPreconnected_range (hm.continuous.comp (continuous_id.prodMk continuous_const))
  obtain ⟨ends, hfree, hiff⟩ := C.exists_arcEnds_OBDd dec P hP hface γ'
    (pieceSet := range m) (slice := fun b => range fun z => m (z, iccEnd b)) hrange hends hconn
  let a : SphereArcExit74 Z Cu := ⟨m, hm, hinj, hfr, ends⟩
  refine ⟨.sphereArc a, (range_sphereIntervalPiece a.F a.smooth (sphereArc_bijective74 a)
    a.injective).trans hrange, Or.inl ⟨a, rfl, hproj, hends, fun b hk => ?_, hiff⟩⟩
  obtain ⟨e', he, hfe⟩ := hfree b hk
  exact ⟨univ, e', isOpen_univ, he.contDiffOn, fun _ _ => trivial, fun y _ => hfe y⟩

include C in
/-- **The torus arc exit of a torus interval product over a base arc** with the `rel3` end data. -/
theorem torusArcExit_of_product_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
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
    (hproj : ∀ z, C.toChain.stageMap 2 (m z) = γ'.toFun z.2)
    (hrange : range m = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ'.toFun '' Icc 0 1))
    (hends : ∀ b, range (fun z => m (z, iccEnd b)) =
      dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)}) :
    ∃ x : SlimPieceExit74 Z Cu,
      range x.piece.map = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ'.toFun '' Icc 0 1) ∧
      ((∃ a : SphereArcExit74 Z Cu, x = .sphereArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = γ'.toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) =
            dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            γ'.toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∨
        (∃ a : TorusArcExit74 Z Cu, x = .torusArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = γ'.toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) =
            dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            γ'.toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))) := by
  have hmc : Continuous m := hm.continuous
  have hconn : ∀ b, IsPreconnected (range fun z => m (z, iccEnd b)) := fun b =>
    isPreconnected_range (hmc.comp (continuous_id.prodMk continuous_const))
  obtain ⟨ends, hfree, hiff⟩ := C.exists_arcEnds_OBDd dec P hP hface γ'
    (pieceSet := range m) (slice := fun b => range fun z => m (z, iccEnd b)) hrange hends hconn
  let a : TorusArcExit74 Z Cu := ⟨m, hm, hinj, hfr, ends⟩
  refine ⟨.torusArc a, (range_torusIntervalPiece a.F a.smooth (torusArc_bijective74 a)
    a.injective).trans hrange, Or.inr ⟨a, rfl, hproj, hends, fun b hk => ?_, hiff⟩⟩
  obtain ⟨e', he, hfe⟩ := hfree b hk
  exact ⟨univ, e', isOpen_univ, he.contDiffOn, fun _ _ => trivial, fun y _ => hfe y⟩

include C in
/-- **The slim piece exit over a base arc** (sphere or torus arc exit), with the `rel3` end data. -/
theorem exists_slimArcExit_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
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
      ((∃ a : SphereArcExit74 Z Cu, x = .sphereArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = γ'.toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) =
            dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            γ'.toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2)) ∨
        (∃ a : TorusArcExit74 Z Cu, x = .torusArc a ∧
          (∀ z, C.toChain.stageMap 2 (a.F z) = γ'.toFun z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) =
            dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ'.toFun (iccEnd b)}) ∧
          (∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
              (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier), a.ends.fn b y = e (C.toChain.stageMap 2 y)) ∧
          ∀ b : Bool, a.ends.kind b = none ↔
            γ'.toFun (iccEnd b) ∉ C.toChain.stageMap 2 ''
              (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))) := by
  rcases C.exists_arcProduct_OBDd dec P hP γ' with
    ⟨m, hm, hinj, hfr, hproj, hrange, hends⟩ | ⟨m, hm, hinj, hfr, hproj, hrange, hends⟩
  · exact C.sphereArcExit_of_product_OBDd dec P hP hface γ' m hm hinj hfr hproj hrange hends
  · exact C.torusArcExit_of_product_OBDd dec P hP hface γ' m hm hinj hfr hproj hrange hends

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
