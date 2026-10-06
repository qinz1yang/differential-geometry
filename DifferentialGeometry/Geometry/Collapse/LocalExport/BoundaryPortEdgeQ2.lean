import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimQ3
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList

/-!
# The edge stage subspace `Q₂` of the ported global block map (lane B-PORT-EDGEb)

The part of `Fibration/ActualCloudPackets.lean` (`cgpInQ2`, `cgpQ2Tags`) that EGP06's (EG) reads,
and the zero meeting list of `Fibration/ActualActiveSupportPacket.lean` (`zeroMeetingList`,
`ncard_zeroMeetingList_le_one`), on B-PORT-A's accepted `CGPTag_BAUGP L Z`
(`L : LocalPacketsOnB … U₁ U₂ Ue₁ Ue₂`, `Z : ZeroModelFamilyOn … U₁ U₂`). Hand-written copies under
the suffix `_BPE` (lane B-PORT-A's own ports of the two closed files, `BoundaryPortCloudPackets` and
`BoundaryPortActiveSupportPacket`, are not delivered; the names here are distinct). The projection
`π_t ∘ 𝓔⁰` is lane B-PORT-SLIMb's accepted `cgpProjMap_BPS`.

* `cgpInQ2_BPE`, `cgpQ2Tags_BPE`: the tags of `Q₂ = H₀ ⊕ H_s ⊕ H_e` (slim, edge and zero blocks);
* `cgpQ2Tags_slim_mem_BPE`, `cgpQ2Tags_edge_mem_BPE`, `cgpQ2Tags_zero_mem_BPE`;
* `zeroMeetingList_BPE`, `ncard_zeroMeetingList_le_one_BPE` (FC09: at most one zero support meets
  `B(p, ℓρ(p))`).
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

section Tags

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

variable (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs U₁ U₂ Ue₁ Ue₂)
  (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)

/-- Membership of a tag of `𝓔⁰` in `Q₂ = H₀ ⊕ H_s ⊕ H_e` (FC01, B:109; closed `cgpInQ2`). -/
def cgpInQ2_BPE : CGPTag_BAUGP L Z → Bool
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr (.inl _))) => true
  | .inr (.inr (.inr (.inr _))) => false

/-- The tags of `Q₂`: slim, edge and zero blocks (closed `cgpQ2Tags`). -/
def cgpQ2Tags_BPE : Finset (CGPTag_BAUGP L Z) :=
  Finset.univ.filter fun t => cgpInQ2_BPE L Z t = true

theorem cgpQ2Tags_slim_mem_BPE (j : L.slim.finite_centres.toFinset) :
    (.inr (.inl j) : CGPTag_BAUGP L Z) ∈ cgpQ2Tags_BPE L Z :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

theorem cgpQ2Tags_edge_mem_BPE (j : L.edgeB.finite_centres.toFinset) :
    (.inr (.inr (.inl j)) : CGPTag_BAUGP L Z) ∈ cgpQ2Tags_BPE L Z :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

theorem cgpQ2Tags_zero_mem_BPE (k : Z.finite_centres.toFinset) :
    (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP L Z) ∈ cgpQ2Tags_BPE L Z :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

end Tags

section ZeroList

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X} {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ} {U₁ U₂ : Set X}

/-- The zero centres whose LC31 cutoff support meets `B(p, ℓρ(p))` (closed `zeroMeetingList`). -/
def zeroMeetingList_BPE (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (p : X) (ℓ : ℝ) : Set X :=
  {k | ∃ hk : k ∈ Z.centres, (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
    ((Z.zero k hk).radial y)) ∩ ball p (ℓ * ρ p)).Nonempty}

/-- At most one zero support meets `B(p, ℓρ(p))` (FC09 from slow variation; closed
`ncard_zeroMeetingList_le_one`). -/
theorem ncard_zeroMeetingList_le_one_BPE
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) {Λ : NNReal}
    (hρL : LipschitzWith Λ ρ) (he : e < 1 / 40) (hT : 0 < T) (p : X) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hsmall : 2 * (ℓ / T) + 2 * (ℓ * Λ) ≤ 1 / 40) :
    (zeroMeetingList_BPE Z p ℓ).ncard ≤ 1 := by
  have huniq := (zero_supports_meeting_ball_shell_BAUGP Z hρL he hT p hℓ hsmall).1
  have hfin : (zeroMeetingList_BPE Z p ℓ).Finite :=
    Z.finite_centres.subset fun k hk => hk.choose
  refine (Set.ncard_le_one hfin).mpr ?_
  rintro k₁ ⟨hk₁, h₁⟩ k₂ ⟨hk₂, h₂⟩
  exact huniq k₁ hk₁ k₂ hk₂ h₁ h₂

end ZeroList

end DifferentialGeometry.Geometry.Collapse
