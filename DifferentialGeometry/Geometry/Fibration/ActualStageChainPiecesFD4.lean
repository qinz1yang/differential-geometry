import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimFullRowZSP35
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroFacesStandard

/-!
# FDC04, clause "smooth compact pieces + finite lists": the zero and slim pieces (G1, part 1)

Lane S-FDC04 (`_FD4`), group G1. Blueprint `master207B.tex`, FDC04 (B:7367-7435): "They are finite
unions of compact embedded pieces". On the final family `LocalChartPacketsC14Z`:

* `Gaf02ChainE.zero_pieces_FD4` (zero pieces, ZSP02's strong row): the zero domains `Z_k` are a
  FINITE list (`P.zero.finite_centres.toFinset`), each compact and the ambient-diffeomorphic image
  of the model sublevel with standard smooth face (the strong row, quoted by `type_of%`), pairwise
  disjoint; their union `Z` is compact and `∂Z = ⋃_k ∂Z_k`.
* `Gaf02ChainEJA.slim_pieces_FD4` (slim pieces, ZSP04's full row for an ARBITRARY admissible
  `K₃, D₃`, i.e. any pair with the five properties of `zsp04_D3_ZSP35` -- the pair the edge rows
  (FC37 / FDC02) and the cover are stated for; `zsp04_full_row_ZSP35` chooses its own pair): the
  slim piece `M^slim = f₃⁻¹(D₃)` is the union of the finitely many compact pieces over the arcs and
  loops of `D₃` (`D₃.m` arcs, `D₃.l` loops, pairwise disjoint), with the interval products
  `S² × I` / `T² × I` over the arcs (S0), the end classification and the circle-valued submersion
  over the loops.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.GraphManifold GC.Endpoint
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **The zero pieces of FDC04** (see the module docstring). -/
theorem Gaf02ChainE.zero_pieces_FD4
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) :
    Finite P.zero.finite_centres.toFinset ∧
    Ĉ.zeroUnion_ZSP35 = ⋃ k : P.zero.finite_centres.toFinset,
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
    IsCompact Ĉ.zeroUnion_ZSP35 ∧
    frontier Ĉ.zeroUnion_ZSP35 = ⋃ k : P.zero.finite_centres.toFinset,
      frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
    (∀ k : P.zero.finite_centres.toFinset,
      IsCompact (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) =
        zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
    (∀ k k' : P.zero.finite_centres.toFinset, k ≠ k' →
      Disjoint (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
        (zspDomain_ZSP35 P.toLocalChartFamily P.zero k' Ĉ.E)) ∧
    type_of% (Ĉ.zsp02_row_strong_ZSP35 hεr) := by
  have hcpt : ∀ k : P.zero.finite_centres.toFinset,
      IsCompact (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) := fun k =>
    (Ĉ.zsp02_domain_ZSP35 hεr k).1
  have hdisj : ∀ k k' : P.zero.finite_centres.toFinset, k ≠ k' →
      Disjoint (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
        (zspDomain_ZSP35 P.toLocalChartFamily P.zero k' Ĉ.E) := fun k k' hkk =>
    Ĉ.zsp02_disjoint_ZSP35 hεr hkk
  obtain ⟨-, hfr⟩ := frontier_disjoint_iUnion_ZSP35
    (fun k : P.zero.finite_centres.toFinset => zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
    (fun k => (hcpt k).isClosed) hdisj
  refine ⟨inferInstance, rfl, isCompact_iUnion hcpt, hfr, fun k => ⟨hcpt k, ?_⟩, hdisj,
    Ĉ.zsp02_row_strong_ZSP35 hεr⟩
  obtain ⟨-, -, hfk, -⟩ := (Ĉ.zsp02_row_strong_ZSP35 hεr).1.1 k
  exact hfk

namespace Gaf02ChainEJA

section Slim

variable {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The slim pieces of FDC04 for an admissible `K₃, D₃`** (see the module docstring): ZSP04's
full row (`zsp04_full_row_ZSP35`, clause by clause) for ANY pair `K₃, D₃` with the properties of
`zsp04_D3_ZSP35`, and the decomposition of `M^slim = f₃⁻¹(D₃)` into the compact pieces over the
finitely many arcs and loops of `D₃`. -/
theorem slim_pieces_FD4
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hK : 5 ≤ K) (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
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
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35)) :
    C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier ∧
      C.slimPiece_ZSP35 K₃.carrier =
        (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' K₃.carrier ∧
      IsCompact (C.slimPiece_ZSP35 K₃.carrier) ∧
      closure (interior (C.slimPiece_ZSP35 K₃.carrier)) = C.slimPiece_ZSP35 K₃.carrier ∧
      C.slimMap_ZSP35 '' C.slimPiece_ZSP35 K₃.carrier = D₃.carrier ∧
      zsp04SlimSlabs_ZSP35 P.toLocalChartPackets ∩ (interior C.zeroUnion_ZSP35)ᶜ ⊆
        C.slimPiece_ZSP35 K₃.carrier ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier (interior C.zeroUnion_ZSP35)ᶜ ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier :
          Set ↥(interior C.zeroUnion_ZSP35)ᶜ) ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 =
        C.slimMap_ZSP35 ⁻¹' (K₃.carrier ∩ C.slimFacePoints_ZSP35) ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 =
        ⋃ k ∈ {k : P.zero.finite_centres.toFinset |
            (frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∩
              C.slimPiece_ZSP35 K₃.carrier).Nonempty},
          frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∧
      frontier (C.slimPiece_ZSP35 K₃.carrier) = C.slimMap_ZSP35 ⁻¹' (D₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)) ∧
      (P.slim.centres = ∅ → C.slimPiece_ZSP35 K₃.carrier = ∅) ∧
      (∀ k : Fin D₃.m,
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0}
            (D₃.arc k 0),
          Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE (D₃.arc_EFE k) F₀)) ∨
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus
            (D₃.arc k 0),
          Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE (D₃.arc_EFE k) F₀))) ∧
      (∀ k : Fin D₃.m, ∀ y ∈ ({D₃.arc k 0, D₃.arc k 1} :
          Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))),
        (y ∈ C.slimFacePoints_ZSP35 ∧
            y ∈ Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
            C.slimMap_ZSP35 ⁻¹' {y} ⊆ C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35) ∨
          (y ∈ K₃.carrier \
              Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
            y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) ∧
            C.slimMap_ZSP35 ⁻¹' {y} ⊆ frontier (C.slimPiece_ZSP35 K₃.carrier) ∧
            Disjoint (C.slimMap_ZSP35 ⁻¹' {y}) (frontier C.zeroUnion_ZSP35))) ∧
      (∀ j : Fin D₃.l,
        C.slimMap_ZSP35 ⁻¹' range (D₃.loop j) ⊆ interior (C.slimPiece_ZSP35 K₃.carrier) ∧
        IsOpen (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
        IsCompact (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
        ∃ p : X → Circle,
          ContMDiffOn 𝓘(ℝ, E3) (𝓡 1) ∞ p (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
          (∀ x ∈ C.slimMap_ZSP35 ⁻¹' range (D₃.loop j),
            Surjective (mfderiv 𝓘(ℝ, E3) (𝓡 1) p x)) ∧
          (∀ x ∈ C.slimMap_ZSP35 ⁻¹' range (D₃.loop j), ∀ t : ℝ,
            p x = Circle.exp (2 * Real.pi * t) ↔ C.slimMap_ZSP35 x = D₃.loop j t) ∧
          ((∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0}
              (D₃.loop j 0),
            range F₀.emb = {x | x ∈ C.slimMap_ZSP35 ⁻¹' range (D₃.loop j) ∧ p x = 1}) ∨
          (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus
              (D₃.loop j 0),
            range F₀.emb = {x | x ∈ C.slimMap_ZSP35 ⁻¹' range (D₃.loop j) ∧ p x = 1}))) ∧
    C.slimPiece_ZSP35 K₃.carrier =
      (⋃ k : Fin D₃.m, C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1)) ∪
        ⋃ j : Fin D₃.l, C.slimMap_ZSP35 ⁻¹' range (D₃.loop j) ∧
    (∀ k : Fin D₃.m, IsCompact (C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1))) ∧
    (∀ j : Fin D₃.l, IsCompact (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j))) ∧
    Pairwise (Disjoint on fun k : Fin D₃.m => C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1)) ∧
    Pairwise (Disjoint on fun j : Fin D₃.l => C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) ∧
    (∀ (k : Fin D₃.m) (j : Fin D₃.l), Disjoint (C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1))
      (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j))) := by
  obtain ⟨hSD, hSeq, hSc, hreg, himg, hcollar, h4, hfaces, hfp⟩ :=
    C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg
  have hcont := C.continuous_slimMap_ZSP35
  have harcc : ∀ k : Fin D₃.m, IsCompact (C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1)) := fun k =>
    ((isCompact_Icc.image_of_continuousOn (D₃.arc_smooth k).continuousOn).isClosed.preimage
      hcont).isCompact
  have hloopc : ∀ j : Fin D₃.l, IsCompact (C.slimMap_ZSP35 ⁻¹' range (D₃.loop j)) := fun j => by
    refine (IsCompact.isClosed ?_ |>.preimage hcont).isCompact
    rw [← (D₃.loop_periodic j).image_Icc one_pos 0]
    exact isCompact_Icc.image (D₃.loop_smooth j).continuous
  refine ⟨hSD, hSeq, hSc, hreg, himg, C.slim_piece_slab_ZSP35 K₃ hKs hSeq, hcollar, h4, hfaces,
    hfp, C.slim_piece_empty_ZSP35 hεr K₃.carrier,
    fun k => C.slim_arc_product_EFE hK (D₃.arc_EFE k),
    fun k y hy => C.slim_arc_end_kinds_ZSP35 K₃ D₃ hKF hSD hdD h4 hfp k hy,
    fun j => ⟨C.slim_loop_preimage_interior_ZSP35 hK K₃ D₃ hSD j,
      C.slim_loop_circle_ZSP35 hK D₃ j⟩, ?_, harcc, hloopc, ?_, ?_, ?_⟩
  · rw [hSD, D₃.carrier_eq, preimage_union, preimage_iUnion, preimage_iUnion]
  · intro k k' hkk
    exact (D₃.arc_disjoint hkk).preimage _
  · intro j j' hjj
    exact (D₃.loop_disjoint hjj).preimage _
  · intro k j
    exact (D₃.arc_loop_disjoint k j).preimage _

end Slim

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
