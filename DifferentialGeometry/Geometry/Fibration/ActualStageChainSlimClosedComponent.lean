import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimBaseDomain

/-!
# ZSP04/ZSP05 on one `K₃`: the whole closed decomposition, and closed slim components

Lane C14-ZSP35d. Blueprint `master207B.tex`, ZSP04 (B:6531–6595) and ZSP05 (B:6597–6640), last
clause of ZSP05: "A closed connected zero or slim component, if present, is the entire connected
carrier `M`" (slim part; the zero part is G6's `zsp05_closed_zero_component_ZSP35`).

* `Gaf02ChainEJA.zsp05_closed_slim_component_ZSP35` (connected carrier): the whole preimage of a
  LOOP component of `D₃` is open and closed and nonempty, hence all of `M` — then `M^slim = M`.
* `Gaf02ChainEJA.zsp0405_row_ZSP35`: for ONE `K₃` (with `D₃ = K₃ ∩ C₃` a compact smooth
  one-dimensional domain): (SK), `∂D₃` classification, `M^slim` compact / regular / saturated /
  onto `D₃` with the collar and the shared faces `M^slim ∩ ∂Z = f⁻¹(K₃ ∩ ∂C₃)`, `∂M^slim =
  f⁻¹(∂D₃)`, and ZSP05's `M = Z ∪ M^slim ∪ M₂` with `M₂` compact.

Consumer: `zsp0405_row_C14Z_ZSP35`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

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
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **ZSP05, a closed slim component is the whole connected carrier** (B:6616–6617, slim part):
for a compact smooth one-dimensional `D ⊆ C₃` (e.g. ZSP04's `D₃`) and a LOOP component of `D`,
its whole preimage `f⁻¹(loop)` is open (the loop is relatively open in `Bs`), closed (compact,
properness) and nonempty, so on a connected carrier it is all of `M`. -/
theorem zsp05_closed_slim_component_ZSP35 [ConnectedSpace X]
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (D : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hDC : D.carrier ⊆ C.slimC3_ZSP35) (j : Fin D.l) :
    C.slimMap_ZSP35 ⁻¹' range (D.loop j) = univ := by
  have hfc := C.continuous_slimMap_ZSP35
  obtain ⟨G, hG, hGB⟩ := D.loop_relOpen j
  have hsub : range (D.loop j) ⊆ D.carrier := by
    rw [D.carrier_eq]
    exact subset_union_of_subset_right (subset_iUnion (fun j => range (D.loop j)) j) _
  have hopen : IsOpen (C.slimMap_ZSP35 ⁻¹' range (D.loop j)) := by
    have heq : C.slimMap_ZSP35 ⁻¹' range (D.loop j) =
        C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 ∩ C.slimMap_ZSP35 ⁻¹' G := by
      rw [← preimage_inter, inter_comm, hGB]
    rw [heq]
    exact C.isOpen_slimSource_ZSP35.inter (hG.preimage hfc)
  have hcpt : IsCompact (range (D.loop j)) := by
    rw [← (D.loop_periodic j).image_Icc one_pos 0]
    exact isCompact_Icc.image (D.loop_smooth j).continuous
  have hclosed : IsClosed (C.slimMap_ZSP35 ⁻¹' range (D.loop j)) :=
    hcpt.isClosed.preimage hfc
  have hne : (C.slimMap_ZSP35 ⁻¹' range (D.loop j)).Nonempty := by
    obtain ⟨p, -, hp⟩ := hDC (hsub ⟨0, rfl⟩)
    exact ⟨p, ⟨0, hp.symm⟩⟩
  rcases isClopen_iff.mp ⟨hclosed, hopen⟩ with h | h
  · exact absurd h hne.ne_empty
  · exact h

/-- **ZSP04 and ZSP05 for one `K₃`** (B:6531–6640): there are compact smooth one-dimensional
`K₃ ⊇ D₃ = K₃ ∩ C₃` (arcs and loops) with (SK) and `∂K₃ ∩ ∂C₃ = ∅`; the slim piece
`M^slim = f⁻¹(D₃) = M₁ ∩ f⁻¹(K₃)` is compact, regular closed, maps onto `D₃`, contains its
relative collar along `∂M₁`, meets `∂Z` exactly in `f⁻¹(K₃ ∩ ∂C₃)`, and has frontier
`f⁻¹(∂D₃)`; the remainder `M₂ = M₁ ∖ int_{M₁} M^slim` is compact and `M = Z ∪ M^slim ∪ M₂`. -/
theorem zsp0405_row_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    ∃ K₃ D₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
      Disjoint (K₃.carrier \
          Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
        C.slimFacePoints_ZSP35 ∧
      C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier ∧
      C.slimPiece_ZSP35 K₃.carrier =
        (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' K₃.carrier ∧
      IsCompact (C.slimPiece_ZSP35 K₃.carrier) ∧
      closure (interior (C.slimPiece_ZSP35 K₃.carrier)) = C.slimPiece_ZSP35 K₃.carrier ∧
      C.slimMap_ZSP35 '' C.slimPiece_ZSP35 K₃.carrier = D₃.carrier ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier (interior C.zeroUnion_ZSP35)ᶜ ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier :
          Set ↥(interior C.zeroUnion_ZSP35)ᶜ) ∧
      C.slimPiece_ZSP35 K₃.carrier ∩ frontier C.zeroUnion_ZSP35 =
        C.slimMap_ZSP35 ⁻¹' (K₃.carrier ∩ C.slimFacePoints_ZSP35) ∧
      frontier (C.slimPiece_ZSP35 K₃.carrier) = C.slimMap_ZSP35 ⁻¹' (D₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)) ∧
      IsCompact ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
        (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) ∧
      C.zeroUnion_ZSP35 ∪ C.slimPiece_ZSP35 K₃.carrier ∪
        ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
          (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) =
        univ := by
  obtain ⟨K₃, D₃, hD, hKs, hKF, hDreg, -⟩ := C.zsp04_D3_ZSP35 hεr
  obtain ⟨-, hbd⟩ := C.zsp03_slim_boundary_eq_ZSP35 hεr
  have hreg' : K₃.carrier ∩ C.slimC3_ZSP35 ⊆ closure (Subtype.val '' interior
      (Subtype.val ⁻¹' (K₃.carrier ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35)) := hD ▸ hDreg
  obtain ⟨hSeq, hSc, hreg, himg, hcollar, -, hM₂, hcov, -⟩ :=
    C.slimPiece_spec_ZSP35 hεr K₃.isCompact_carrier_BCF K₃.subset_base
      (subset_union_right.trans hKs) hreg'
  obtain ⟨-, -, h3, h4⟩ := C.zsp04_SF_ZSP35 hεr K₃.isCompact_carrier_BCF K₃.subset_base hKF
  rw [hbd] at h4
  refine ⟨K₃, D₃, hD, hKs, hKF, by rw [hD]; rfl, hSeq, hSc, hreg, hD ▸ himg, hcollar, h4, ?_,
    hM₂, hcov⟩
  rw [h3, hD]

end Gaf02ChainEJA

/-- **Consumer: the closed decomposition on the final family, slim components** (connected
carrier): with the `K₃, D₃` of `zsp0405_row_ZSP35`, `M = Z ∪ M^slim ∪ M₂`, and if `D₃` has a
loop component then `M^slim` is all of `M`. -/
theorem zsp0405_row_C14Z_ZSP35 [ConnectedSpace X] {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    ∃ K₃ D₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      C.zeroUnion_ZSP35 ∪ C.slimPiece_ZSP35 K₃.carrier ∪
        ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
          (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier : Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) =
        univ ∧
      (0 < D₃.l → C.slimPiece_ZSP35 K₃.carrier = univ) := by
  obtain ⟨K₃, D₃, hD, -, -, hSD, -, -, -, -, -, -, -, -, hcov⟩ := C.zsp0405_row_ZSP35 hεr
  refine ⟨K₃, D₃, hD, hcov, fun hl => ?_⟩
  have hDC : D₃.carrier ⊆ C.slimC3_ZSP35 := by
    rw [hD]
    exact inter_subset_right
  have h := C.zsp05_closed_slim_component_ZSP35 D₃ hDC ⟨0, hl⟩
  rw [hSD]
  refine eq_univ_of_univ_subset fun x _ => ?_
  have hx : x ∈ C.slimMap_ZSP35 ⁻¹' range (D₃.loop ⟨0, hl⟩) := by
    rw [h]
    exact mem_univ x
  refine (show range (D₃.loop ⟨0, hl⟩) ⊆ D₃.carrier from ?_) hx
  rw [D₃.carrier_eq]
  exact subset_union_of_subset_right (subset_iUnion (fun j => range (D₃.loop j)) _) _

end DifferentialGeometry.Geometry.Collapse
