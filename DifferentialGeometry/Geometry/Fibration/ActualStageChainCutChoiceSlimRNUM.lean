import DifferentialGeometry.Geometry.Fibration.ActualStageChainCutChoice
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimPiece
import DifferentialGeometry.Topology.Manifold.OneManifold.SmoothCompactOneDomainBCF
import DifferentialGeometry.Topology.Maps.RelativeInteriorRemoval

/-!
# ZSP05's slim facts for EVERY cut choice (D74-18, `Htail` for an arbitrary `D`)

Lane S-REG-NUM (`_RNUM`), G2. A cut choice `D : CutChoiceOn74 C` keeps `K₃`, `D₃ = K₃ ∩ C₃` (a
compact smooth one-dimensional domain: arcs and loops), (SK) and `∂K₃ ∩ F₃ = ∅`. ZSP05's
`slimPiece_spec_ZSP35` needs only: `K₃` compact in `Bs`, `F₃ ⊆ int K₃`, and the REGULARITY of
`K₃ ∩ C₃`. The regularity is a property of every `SmoothCompactOneDomain_BCF` (loops are
relatively open; an arc interior is relatively open and the arc is the closure of its interior), so
`slimPiece_spec_ZSP35` applies to EVERY cut choice, not only the one `exists_cutChoice_R74` builds
(whose `hSeq`, regularity and collar are not recorded in the structure):

* `SmoothCompactOneDomain_BCF.subset_closure_relInterior_RNUM`: `D₃ ⊆ closure (relint D₃)`;
* `Gaf02ChainEJA.cutChoice_slim_spec_RNUM`: for every `D : CutChoiceOn74 C` (`ε_r < 1/2`):
  `slimSet = M₁ ∩ f⁻¹(K₃)`, compact, regular closed, with its relative collar along `∂M₁`, and
  `Z ∪ slimSet ∪ M₂ = M`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

namespace SmoothCompactOneDomain_BCF

variable {Bs : Set H} (D : SmoothCompactOneDomain_BCF Bs)

/-- **Regularity of a compact smooth one-dimensional domain**: its carrier lies in the closure of
its relative interior in `Bs` (loops are relatively open; an arc interior is relatively open and
the arc is the closure of its interior). -/
theorem subset_closure_relInterior_RNUM :
    D.carrier ⊆ closure (Subtype.val '' interior (Subtype.val ⁻¹' D.carrier : Set Bs)) := by
  have hrel : ∀ x, (∃ G : Set H, IsOpen G ∧ x ∈ G ∧ G ∩ Bs ⊆ D.carrier) → x ∈ Bs →
      x ∈ Subtype.val '' interior (Subtype.val ⁻¹' D.carrier : Set Bs) := by
    rintro x ⟨G, hG, hxG, hGC⟩ hxB
    exact mem_image_interior_preimage_val_iff.mpr ⟨hxB, G, hG, hxG, hGC⟩
  have harc : ∀ k, D.arc k '' Ioo 0 1 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' D.carrier : Set Bs) := by
    intro k x hx
    obtain ⟨G, hG, hGB⟩ := D.arc_interior_relOpen k
    have hxG : x ∈ G ∩ Bs := by rw [hGB]; exact hx
    refine hrel x ⟨G, hG, hxG.1, fun y hy => ?_⟩ hxG.2
    rw [hGB] at hy
    rw [D.carrier_eq]
    obtain ⟨t, ht, rfl⟩ := hy
    exact Or.inl (mem_iUnion.mpr ⟨k, ⟨t, Ioo_subset_Icc_self ht, rfl⟩⟩)
  intro x hx
  rw [D.carrier_eq] at hx
  rcases hx with hx | hx
  · obtain ⟨k, t, ht, rfl⟩ := mem_iUnion.mp hx
    have hcl : D.arc k '' Icc 0 1 ⊆ closure (D.arc k '' Ioo 0 1) := by
      have h1 : D.arc k '' closure (Ioo (0 : ℝ) 1) ⊆ closure (D.arc k '' Ioo 0 1) :=
        ContinuousOn.image_closure
          (by rw [closure_Ioo zero_ne_one]; exact (D.arc_smooth k).continuousOn)
      rwa [closure_Ioo zero_ne_one] at h1
    exact closure_mono (harc k) (hcl ⟨t, ht, rfl⟩)
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    obtain ⟨G, hG, hGB⟩ := D.loop_relOpen j
    have hmem : x ∈ G ∩ Bs := by rw [hGB]; exact hj
    refine subset_closure (hrel x ⟨G, hG, hmem.1, fun y hy => ?_⟩ hmem.2)
    rw [hGB] at hy
    rw [D.carrier_eq]
    exact Or.inr (mem_iUnion.mpr ⟨j, hy⟩)

end SmoothCompactOneDomain_BCF

end DifferentialGeometry.Topology

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

/-- **ZSP05's slim facts for EVERY cut choice** (`ε_r < 1/2`): for `D : CutChoiceOn74 C`,
`slimSet = M₁ ∩ f⁻¹(K₃)` (`M₁ = (int Z)ᶜ`), compact, regular closed, containing its relative collar
along `∂M₁`, and `Z ∪ slimSet ∪ M₂ = M`. -/
theorem cutChoice_slim_spec_RNUM
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (D : CutChoiceOn74 C.toGaf02ChainE) :
    D.slimSet = (interior C.zeroUnion_ZSP35)ᶜ ∩ C.slimMap_ZSP35 ⁻¹' D.K₃.carrier ∧
      IsCompact D.slimSet ∧ closure (interior D.slimSet) = D.slimSet ∧
      D.slimSet ∩ frontier (interior C.zeroUnion_ZSP35)ᶜ ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' D.slimSet :
          Set ↥(interior C.zeroUnion_ZSP35)ᶜ) ∧
      C.zeroUnion_ZSP35 ∪ D.slimSet ∪ D.M₂ = univ := by
  have hreg : D.K₃.carrier ∩ C.slimC3_ZSP35 ⊆ closure (Subtype.val '' interior
      (Subtype.val ⁻¹' (D.K₃.carrier ∩ C.slimC3_ZSP35) : Set C.slimBs_ZSP35)) := by
    rw [← D.D₃_eq]
    exact D.D₃.subset_closure_relInterior_RNUM
  obtain ⟨hSeq, hSc, hSreg, -, hcollar, -, -, hcov, -⟩ := C.slimPiece_spec_ZSP35 hεr
    D.K₃.isCompact_carrier_BCF D.K₃.subset_base (subset_union_right.trans D.K₃_req) hreg
  rw [← D.slimSet_eq] at hSeq hSc hSreg hcollar hcov
  refine ⟨hSeq, hSc, hSreg, hcollar, ?_⟩
  rw [D.M₂_eq]
  exact hcov

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
