import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimArcEnds74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimDomainComponents74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimFullRowZSP35
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimEndFaceZSP35

/-!
# Draft 74, S0 on the chain: the slim piece exit over an arc of any `D₃`

Lane C14-REG-CHAIN (by S-REG-CHAIN5), G39. For a chain `C` on the final family (`K ≥ 5`,
`εr < 1/2`), the carrier identification `φ : X ≃ₘ W` (`W` without boundary), the `K₃, D₃` of a
cut choice (with `zsp04`'s regularity data) and every arc `k` of `D₃`, a slim piece exit over the
arc with range `φ(f₃⁻¹(arc k [0, 1]))`:

* `slim_arcEnd74`: the end datum of one end `y = arc k (iccEnd b)`: a ZERO-FACE end
  (`slim_arc_end_kinds_ZSP35`, first alternative) is a whole neighbour face by the argument
  `hz` (G38 supplies it on the closed route); a FREE end uses `slim_free_end_tube_ZSP35`, whose
  tube `U` is shrunk to `U ∩ f₃⁻¹(Rᶜ)` with `R` the union of all other components of `D₃`
  (compact, `isClosed_others74`) so that `M^slim ∩ U'` is the preimage of THIS arc only;
* `slim_arc_exit74`: the exit, from the whole interval product of `slim_arc_product_EFE`
  (sphere or torus) carried by `φ` (`SphereArcExit74.ofProduct74`), the end data of both ends
  (the end fibres are connected: images of the standard whole fibre).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.GraphManifold GC.Endpoint
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- `ClosureSphere` is connected. -/
local instance closureSphereConnected_R74b : ConnectedSpace ClosureSphere.{0} :=
  have hS : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
  Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous

/-- The `ArcEnds74` of an arc exit from end-by-end data given on plain sets. -/
theorem arcEnds_of_sets74 {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n}
    {Z : ZeroDomains W} {Cu : CuspCores W E} {pieceSet A : Set W.Carrier}
    {slice : Bool → Set W.Carrier} (S : Bool → Set W.Carrier) (hp : pieceSet = A)
    (hs : ∀ b, slice b = S b)
    (h : ∀ b : Bool, ∃ (k : Option (NeighbourFace Z Cu)) (fn : W.Carrier → ℝ)
        (near : TopologicalSpace.Opens W.Carrier),
      (∀ F, k = some F → S b = neighbourSet F) ∧
      (k = none → (near : Set W.Carrier) ⊆ W.interior) ∧
      (k = none → ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ fn near) ∧
      (k = none → ∀ x ∈ near, fn x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) fn x ≠ 0) ∧
      (k = none → S b = {x | x ∈ near ∧ fn x = 0}) ∧
      (k = none → A ∩ near = {x | x ∈ near ∧ fn x ≤ 0})) :
    Nonempty (ArcEnds74 Z Cu pieceSet slice) := by
  subst hp
  refine ArcEnds74.exists_of_ends74 fun b => ?_
  rw [hs b]
  exact h b

namespace Gaf02ChainEJA

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The end datum of one end of an arc of `D₃`**: a zero-face end is a whole neighbour face
(by `hz`), a free end carries a defining function `fn` on `near = φ(U')`. -/
theorem slim_arcEnd74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) {W : CompactCarrier.{0}} (φ : X ≃ₘ⟮𝓘(ℝ, E3), W.model⟯ W.Carrier)
    (hW : W.model.boundary W.Carrier = ∅) {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W}
    {Cu : CuspCores W E} (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hSD : C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier)
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \
            Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hfz : C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 =
      C.slimMap_ZSP35 ⁻¹' (K₃.carrier ∩ C.slimFacePoints_ZSP35))
    (hfp : frontier (C.slimPiece_ZSP35 K₃.carrier) = C.slimMap_ZSP35 ⁻¹' (D₃.carrier \
      Subtype.val '' interior (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hz : ∀ y ∈ C.slimFacePoints_ZSP35,
      IsPreconnected (φ '' (C.slimMap_ZSP35 ⁻¹' {y})) →
      (φ '' (C.slimMap_ZSP35 ⁻¹' {y})).Nonempty →
      ∃ F : NeighbourFace Z Cu, φ '' (C.slimMap_ZSP35 ⁻¹' {y}) = neighbourSet F)
    (k : Fin D₃.m) (b : Bool)
    (hconn : IsPreconnected (φ '' (C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)})))
    (hne : (φ '' (C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)})).Nonempty) :
    ∃ (kd : Option (NeighbourFace Z Cu)) (fn : W.Carrier → ℝ)
      (near : TopologicalSpace.Opens W.Carrier),
      (∀ F, kd = some F → φ '' (C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)}) = neighbourSet F) ∧
      (kd = none → (near : Set W.Carrier) ⊆ W.interior) ∧
      (kd = none → ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ fn near) ∧
      (kd = none → ∀ x ∈ near, fn x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) fn x ≠ 0) ∧
      (kd = none → φ '' (C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)}) =
        {x | x ∈ near ∧ fn x = 0}) ∧
      (kd = none → φ '' (C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1)) ∩ near =
        {x | x ∈ near ∧ fn x ≤ 0}) := by
  have hyk : D₃.arc k (iccEnd b) = D₃.arc k 0 ∨ D₃.arc k (iccEnd b) = D₃.arc k 1 := by
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hyS : D₃.arc k (iccEnd b) ∈ ({D₃.arc k 0, D₃.arc k 1} :
      Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) := hyk
  rcases C.slim_arc_end_kinds_ZSP35 K₃ D₃ hKF hSD hdD hfz hfp k hyS with
    ⟨hyF, -, -⟩ | ⟨-, hyC, -, -⟩
  · obtain ⟨F, hF⟩ := hz _ hyF hconn hne
    exact ⟨some F, fun _ => 0, ⊥, fun F' hF' => (Option.some.inj hF') ▸ hF,
      fun h => absurd h (Option.some_ne_none _), fun h => absurd h (Option.some_ne_none _),
      fun h => absurd h (Option.some_ne_none _), fun h => absurd h (Option.some_ne_none _),
      fun h => absurd h (Option.some_ne_none _)⟩
  · obtain ⟨U, h, hUo, hfU, -, -, hh, hsurj, hlev, hside⟩ :=
      C.slim_free_end_tube_ZSP35 hεr D₃ ⟨k, hyk⟩ hyC
    have hRc : IsClosed (⋃ i' ∈ ({Sum.inl k}ᶜ : Set (Fin D₃.m ⊕ Fin D₃.l)), D₃.piece74 i') :=
      D₃.isClosed_others74 (Sum.inl k)
    have hyR : D₃.arc k (iccEnd b) ∉
        ⋃ i' ∈ ({Sum.inl k}ᶜ : Set (Fin D₃.m ⊕ Fin D₃.l)), D₃.piece74 i' := by
      intro hyR
      obtain ⟨i', hmem, hy'⟩ := mem_iUnion₂.mp hyR
      have hyk' : D₃.arc k (iccEnd b) ∈ D₃.piece74 (Sum.inl k) := ⟨iccEnd b, (iccEnd b).2, rfl⟩
      exact Set.disjoint_left.mp (D₃.disjoint_piece74 (Ne.symm hmem)) hyk' hy'
    have hU'o : IsOpen (U ∩ C.slimMap_ZSP35 ⁻¹'
        (⋃ i' ∈ ({Sum.inl k}ᶜ : Set (Fin D₃.m ⊕ Fin D₃.l)), D₃.piece74 i')ᶜ) :=
      hUo.inter (hRc.isOpen_compl.preimage C.continuous_slimMap_ZSP35)
    have hfU' : C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)} ⊆ U ∩ C.slimMap_ZSP35 ⁻¹'
        (⋃ i' ∈ ({Sum.inl k}ᶜ : Set (Fin D₃.m ⊕ Fin D₃.l)), D₃.piece74 i')ᶜ := fun x hx =>
      ⟨hfU hx, by
        have hxy : C.slimMap_ZSP35 x = D₃.arc k (iccEnd b) := hx
        rw [mem_preimage, hxy]
        exact hyR⟩
    have hlev' : {x | x ∈ (U ∩ C.slimMap_ZSP35 ⁻¹'
        (⋃ i' ∈ ({Sum.inl k}ᶜ : Set (Fin D₃.m ⊕ Fin D₃.l)), D₃.piece74 i')ᶜ) ∧ h x = 0} =
        C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)} := by
      ext x
      constructor
      · rintro ⟨hxU', hx0⟩
        rw [← hlev]
        exact ⟨hxU'.1, hx0⟩
      · intro hx
        have hx' : x ∈ {x | x ∈ U ∧ h x = 0} := hlev ▸ hx
        exact ⟨hfU' hx, hx'.2⟩
    have hside' : C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1) ∩ (U ∩ C.slimMap_ZSP35 ⁻¹'
        (⋃ i' ∈ ({Sum.inl k}ᶜ : Set (Fin D₃.m ⊕ Fin D₃.l)), D₃.piece74 i')ᶜ) =
        {x | x ∈ (U ∩ C.slimMap_ZSP35 ⁻¹'
          (⋃ i' ∈ ({Sum.inl k}ᶜ : Set (Fin D₃.m ⊕ Fin D₃.l)), D₃.piece74 i')ᶜ) ∧ h x ≤ 0} := by
      ext x
      constructor
      · rintro ⟨hxA, hxU'⟩
        have hxD : C.slimMap_ZSP35 x ∈ D₃.carrier := by
          rw [D₃.carrier_eq_iUnion_piece74]
          exact mem_iUnion.mpr ⟨Sum.inl k, hxA⟩
        have hmem : x ∈ U ∩ C.slimMap_ZSP35 ⁻¹' D₃.carrier := ⟨hxU'.1, hxD⟩
        rw [hside] at hmem
        exact ⟨hxU', hmem.2⟩
      · rintro ⟨hxU', hx0⟩
        have hmem : x ∈ {x | x ∈ U ∧ h x ≤ 0} := ⟨hxU'.1, hx0⟩
        rw [← hside] at hmem
        have hxD := hmem.2
        rw [D₃.carrier_eq_iUnion_piece74] at hxD
        obtain ⟨i', hi'⟩ := mem_iUnion.mp hxD
        by_cases hii : i' = Sum.inl k
        · subst hii
          exact ⟨hi', hxU'⟩
        · exact absurd (mem_biUnion (show i' ∈ ({Sum.inl k}ᶜ : Set _) from hii) hi') hxU'.2
    obtain ⟨fn, near, h1, h2, h3, h4, h5⟩ := exists_freeEnd74 φ hW hU'o
      (hh.mono inter_subset_left) (fun x hx => hsurj x hx.1) hlev' hside'
    exact ⟨none, fn, near, fun F hF => absurd hF.symm (Option.some_ne_none F), fun _ => h1,
      fun _ => h2, fun _ => h3, fun _ => h4, fun _ => h5⟩

/-- **The end data of an arc exit from a whole interval product** (sphere and torus alike): the
end fibres are the images of the connected standard fibre. -/
theorem slim_arcEnds_of_product74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) {W : CompactCarrier.{0}} (φ : X ≃ₘ⟮𝓘(ℝ, E3), W.model⟯ W.Carrier)
    (hW : W.model.boundary W.Carrier = ∅) {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W}
    {Cu : CuspCores W E} (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hKF : Disjoint (K₃.carrier \
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hSD : C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier)
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hfz : C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 =
      C.slimMap_ZSP35 ⁻¹' (K₃.carrier ∩ C.slimFacePoints_ZSP35))
    (hfp : frontier (C.slimPiece_ZSP35 K₃.carrier) = C.slimMap_ZSP35 ⁻¹' (D₃.carrier \
      Subtype.val '' interior (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hz : ∀ y ∈ C.slimFacePoints_ZSP35,
      IsPreconnected (φ '' (C.slimMap_ZSP35 ⁻¹' {y})) →
      (φ '' (C.slimMap_ZSP35 ⁻¹' {y})).Nonempty →
      ∃ F : NeighbourFace Z Cu, φ '' (C.slimMap_ZSP35 ⁻¹' {y}) = neighbourSet F)
    (k : Fin D₃.m) {F : Type} [TopologicalSpace F] [ConnectedSpace F] {EF HF : Type*}
    [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
    {IF : ModelWithCorners ℝ EF HF} [ChartedSpace HF F]
    {F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE IF F (D₃.arc k 0)}
    (Wp : WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE (D₃.arc_EFE k) F₀) :
    Nonempty (ArcEnds74 Z Cu (range (φ ∘ Wp.map))
      fun b => range fun z => (φ ∘ Wp.map) (z, iccEnd b)) := by
  have hcont : ∀ b : Bool, Continuous fun z : F => (φ ∘ Wp.map) (z, iccEnd b) := fun b =>
    φ.continuous.comp (Wp.smooth.continuous.comp (continuous_id.prodMk continuous_const))
  have hrange : ∀ b : Bool, range (fun z : F => (φ ∘ Wp.map) (z, iccEnd b)) =
      φ '' (C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)}) := fun b =>
    wholeProduct_range_end_comp74 Wp φ b
  refine arcEnds_of_sets74 (A := φ '' (C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1)))
    (fun b => φ '' (C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)}))
    (wholeProduct_range_comp74 Wp φ) hrange fun b => ?_
  exact C.slim_arcEnd74 hεr φ hW K₃ D₃ hKF hSD hdD hfz hfp hz k b
    (by rw [← hrange b]; exact isPreconnected_range (hcont b))
    (by rw [← hrange b]; exact range_nonempty _)

/-- **The slim piece exit over an arc of `D₃`** (S0 in `W`-form, review 78 D78-6): the exit of the
arc `k` is a sphere or torus arc exit `a` (the full interval product `φ ∘ m`, smooth injective
full rank by the fields of `a`) with image `φ(f₃⁻¹(arc k [0, 1]))`, the projection identity
`f₃(φ⁻¹(a.F (z, t))) = arc k t`, both end slices the whole end fibres
`φ(f₃⁻¹{arc k (iccEnd b)})`, and the end data of `a.ends` (zero-face ends: whole neighbour faces;
free ends: regular defining functions). -/
theorem slim_arc_exit74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hK : 5 ≤ K) {W : CompactCarrier.{0}}
    (φ : X ≃ₘ⟮𝓘(ℝ, E3), W.model⟯ W.Carrier) (hW : W.model.boundary W.Carrier = ∅) {n : ℕ}
    {E : BoundaryTori W n} {Z : ZeroDomains W} {Cu : CuspCores W E}
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hz : ∀ y ∈ C.slimFacePoints_ZSP35,
      IsPreconnected (φ '' (C.slimMap_ZSP35 ⁻¹' {y})) →
      (φ '' (C.slimMap_ZSP35 ⁻¹' {y})).Nonempty →
      ∃ F : NeighbourFace Z Cu, φ '' (C.slimMap_ZSP35 ⁻¹' {y}) = neighbourSet F)
    (k : Fin D₃.m) :
    ∃ x : SlimPieceExit74 Z Cu,
      range x.piece.map = φ '' (C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1)) ∧
      ((∃ a : SphereArcExit74 Z Cu, x = .sphereArc a ∧
          (∀ z, C.slimMap_ZSP35 (φ.symm (a.F z)) = D₃.arc k z.2) ∧
          ∀ b, range (fun z => a.F (z, iccEnd b)) =
            φ '' (C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)})) ∨
        (∃ a : TorusArcExit74 Z Cu, x = .torusArc a ∧
          (∀ z, C.slimMap_ZSP35 (φ.symm (a.F z)) = D₃.arc k z.2) ∧
          ∀ b, range (fun z => a.F (z, iccEnd b)) =
            φ '' (C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)}))) := by
  obtain ⟨hSD, -, -, -, -, -, hfz, -, hfp⟩ := C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg
  rcases C.slim_arc_product_EFE hK (D₃.arc_EFE k) with ⟨F₀, ⟨Wp⟩⟩ | ⟨F₀, ⟨Wp⟩⟩
  · obtain ⟨ends⟩ := C.slim_arcEnds_of_product74 hεr φ hW K₃ D₃ hKF hSD hdD hfz hfp hz k Wp
    let a := SphereArcExit74.ofProduct74 φ Wp.map Wp.smooth Wp.fullRank Wp.injective ends
    refine ⟨.sphereArc a, (range_sphereIntervalPiece a.F a.smooth (sphereArc_bijective74 a)
      a.injective).trans (wholeProduct_range_comp74 Wp φ), Or.inl ⟨a, rfl, fun z => ?_,
      fun b => wholeProduct_range_end_comp74 Wp φ b⟩⟩
    change C.slimMap_ZSP35 (φ.symm (φ (Wp.map z))) = _
    rw [φ.symm_apply_apply]
    exact Wp.proj_eq z
  · obtain ⟨ends⟩ := C.slim_arcEnds_of_product74 hεr φ hW K₃ D₃ hKF hSD hdD hfz hfp hz k Wp
    let a := TorusArcExit74.ofProduct74 φ Wp.map Wp.smooth Wp.fullRank Wp.injective ends
    refine ⟨.torusArc a, (range_torusIntervalPiece a.F a.smooth (torusArc_bijective74 a)
      a.injective).trans (wholeProduct_range_comp74 Wp φ), Or.inr ⟨a, rfl, fun z => ?_,
      fun b => wholeProduct_range_end_comp74 Wp φ b⟩⟩
    change C.slimMap_ZSP35 (φ.symm (φ (Wp.map z))) = _
    rw [φ.symm_apply_apply]
    exact Wp.proj_eq z

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
