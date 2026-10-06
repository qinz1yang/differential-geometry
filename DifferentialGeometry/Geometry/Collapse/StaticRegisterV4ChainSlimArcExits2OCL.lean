import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimArcExits74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimArcEnds2OCL
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeSlimDescentEFE

/-!
# Draft 74, S0 on the chain: the slim arc exit with the end coordinate of every free end

Lane C14-REG-CHAIN (by S-REG-CHAIN6), G1 (chain part, suffix `_OCL`). The G39 arc exit
(`slim_arc_exit74`, untouched) rebuilt with the DESCENT tube over a free end
(`slim_free_end_tube_descent_EFE`: `h = a ∘ f₃` with `a` smooth on the block space), so that the
end function of a free end is `fn = h ∘ φ⁻¹ = a ∘ f₃ ∘ φ⁻¹` by definition:

* `slim_arcEnd2_OCL`: the end datum of one end (zero-face ends exactly as in `slim_arcEnd74`);
* `slim_arcEnds_of_product2_OCL`: the `ArcEnds74` of an arc exit from a whole interval product,
  with the descent clause of every free end;
* `slim_arc_exit2_OCL`: the exit; every free end `b` of the arc carries a smooth `e` on an open
  `Ne` with `a.ends.fn b y = e (f₃ (φ⁻¹ y))` on `a.ends.near b`.
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

/-- **The end datum of one end of an arc of `D₃`, with the descent clause**: as
`slim_arcEnd74` (a zero-face end is a whole neighbour face by `hz`; a free end carries a defining
function `fn` on `near = φ(U')`), and for a free end `fn = a ∘ f₃ ∘ φ⁻¹` with `a` smooth on the
block space. -/
theorem slim_arcEnd2_OCL
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
        {x | x ∈ near ∧ fn x ≤ 0}) ∧
      (kd = none → ∃ a : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ,
        ContDiff ℝ ∞ a ∧ ∀ y, fn y = a (C.slimMap_ZSP35 (φ.symm y))) := by
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
      fun h => absurd h (Option.some_ne_none _), fun h => absurd h (Option.some_ne_none _)⟩
  · obtain ⟨U, h, a, hUo, hfU, -, hh, hsurj, hlev, hside, ha, hha⟩ :=
      C.slim_free_end_tube_descent_EFE hεr D₃ ⟨k, hyk⟩ hyC
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
    obtain ⟨near, h1, h2, h3, h4, h5⟩ := exists_freeEnd2_OCL φ hW hU'o
      (hh.mono inter_subset_left) (fun x hx => hsurj x hx.1) hlev' hside'
    exact ⟨none, h ∘ φ.symm, near, fun F hF => absurd hF.symm (Option.some_ne_none F),
      fun _ => h1, fun _ => h2, fun _ => h3, fun _ => h4, fun _ => h5,
      fun _ => ⟨a, ha, fun y => hha _⟩⟩

/-- **The end data of an arc exit from a whole interval product, with the descent clause** (sphere
and torus alike): the end fibres are the images of the connected standard fibre, and the end
function of every free end is `a ∘ f₃ ∘ φ⁻¹` for a smooth `a` on the block space. -/
theorem slim_arcEnds_of_product2_OCL
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
    ∃ ends : ArcEnds74 Z Cu (range (φ ∘ Wp.map))
        (fun b => range fun z => (φ ∘ Wp.map) (z, iccEnd b)),
      ∀ b, ends.kind b = none →
        ∃ a : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ,
          ContDiff ℝ ∞ a ∧ ∀ y, ends.fn b y = a (C.slimMap_ZSP35 (φ.symm y)) := by
  have hcont : ∀ b : Bool, Continuous fun z : F => (φ ∘ Wp.map) (z, iccEnd b) := fun b =>
    φ.continuous.comp (Wp.smooth.continuous.comp (continuous_id.prodMk continuous_const))
  have hrange : ∀ b : Bool, range (fun z : F => (φ ∘ Wp.map) (z, iccEnd b)) =
      φ '' (C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)}) := fun b =>
    wholeProduct_range_end_comp74 Wp φ b
  have hp : range (φ ∘ Wp.map) = φ '' (C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1)) :=
    wholeProduct_range_comp74 Wp φ
  refine ArcEnds74.exists_of_ends2_OCL (fun _ fn => ∃ a : BlockSpace
    (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ,
    ContDiff ℝ ∞ a ∧ ∀ y, fn y = a (C.slimMap_ZSP35 (φ.symm y))) fun b => ?_
  obtain ⟨kd, fn, near, h1, h2, h3, h4, h5, h6, h7⟩ := C.slim_arcEnd2_OCL hεr φ hW K₃ D₃ hKF hSD
    hdD hfz hfp hz k b (by rw [← hrange b]; exact isPreconnected_range (hcont b))
    (by rw [← hrange b]; exact range_nonempty _)
  exact ⟨kd, fn, near, fun F' hF' => (hrange b).trans (h1 F' hF'), h2, h3, h4,
    fun h => (hrange b).trans (h5 h), fun h => hp ▸ h6 h, h7⟩

/-- **The slim piece exit over an arc of `D₃`, with the end coordinate of every free end**
(`slim_arc_exit74` of G39 and, for every free end `b` of the arc, a smooth `e` on an open `Ne`
with `a.ends.fn b y = e (f₃ (φ⁻¹ y))` on `a.ends.near b`; the `e` is the descent coordinate
`a` of the tube `slim_free_end_tube_descent_EFE`, here with `Ne` the whole block space). -/
theorem slim_arc_exit2_OCL
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
          (∀ b, range (fun z => a.F (z, iccEnd b)) =
            φ '' (C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)})) ∧
          ∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
              (e : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.slimMap_ZSP35 (φ.symm y) ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier),
                a.ends.fn b y = e (C.slimMap_ZSP35 (φ.symm y))) ∨
        (∃ a : TorusArcExit74 Z Cu, x = .torusArc a ∧
          (∀ z, C.slimMap_ZSP35 (φ.symm (a.F z)) = D₃.arc k z.2) ∧
          (∀ b, range (fun z => a.F (z, iccEnd b)) =
            φ '' (C.slimMap_ZSP35 ⁻¹' {D₃.arc k (iccEnd b)})) ∧
          ∀ b : Bool, a.ends.kind b = none →
            ∃ (Ne : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
              (e : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ),
              IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
              (∀ y ∈ (a.ends.near b : Set W.Carrier), C.slimMap_ZSP35 (φ.symm y) ∈ Ne) ∧
              ∀ y ∈ (a.ends.near b : Set W.Carrier),
                a.ends.fn b y = e (C.slimMap_ZSP35 (φ.symm y)))) := by
  obtain ⟨hSD, -, -, -, -, -, hfz, -, hfp⟩ := C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg
  rcases C.slim_arc_product_EFE hK (D₃.arc_EFE k) with ⟨F₀, ⟨Wp⟩⟩ | ⟨F₀, ⟨Wp⟩⟩
  · obtain ⟨ends, hends⟩ := C.slim_arcEnds_of_product2_OCL hεr φ hW K₃ D₃ hKF hSD hdD hfz hfp
      hz k Wp
    let a := SphereArcExit74.ofProduct74 φ Wp.map Wp.smooth Wp.fullRank Wp.injective ends
    refine ⟨.sphereArc a, (range_sphereIntervalPiece a.F a.smooth (sphereArc_bijective74 a)
      a.injective).trans (wholeProduct_range_comp74 Wp φ), Or.inl ⟨a, rfl, fun z => ?_,
      fun b => wholeProduct_range_end_comp74 Wp φ b, fun b hb => ?_⟩⟩
    · change C.slimMap_ZSP35 (φ.symm (φ (Wp.map z))) = _
      rw [φ.symm_apply_apply]
      exact Wp.proj_eq z
    · obtain ⟨e, he, hfe⟩ := hends b hb
      exact ⟨univ, e, isOpen_univ, he.contDiffOn, fun y _ => mem_univ _, fun y _ => hfe y⟩
  · obtain ⟨ends, hends⟩ := C.slim_arcEnds_of_product2_OCL hεr φ hW K₃ D₃ hKF hSD hdD hfz hfp
      hz k Wp
    let a := TorusArcExit74.ofProduct74 φ Wp.map Wp.smooth Wp.fullRank Wp.injective ends
    refine ⟨.torusArc a, (range_torusIntervalPiece a.F a.smooth (torusArc_bijective74 a)
      a.injective).trans (wholeProduct_range_comp74 Wp φ), Or.inr ⟨a, rfl, fun z => ?_,
      fun b => wholeProduct_range_end_comp74 Wp φ b, fun b hb => ?_⟩⟩
    · change C.slimMap_ZSP35 (φ.symm (φ (Wp.map z))) = _
      rw [φ.symm_apply_apply]
      exact Wp.proj_eq z
    · obtain ⟨e, he, hfe⟩ := hends b hb
      exact ⟨univ, e, isOpen_univ, he.contDiffOn, fun y _ => mem_univ _, fun y _ => hfe y⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
