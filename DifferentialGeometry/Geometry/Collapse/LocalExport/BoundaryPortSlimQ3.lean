import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMap

/-!
# The slim stage subspace `Q₃` of the ported global block map (lane B-PORT-SLIMb)

The part of `Fibration/ActualCloudPackets.lean` (`cgpInQ3`, `cgpQ3Tags`, `cgpProjMap`,
`cgpProjMap_apply_of_mem`) that SGP04's (SG) reads, on B-PORT-A's accepted `CGPTag_BAUGP L Z`
(`L : LocalPacketsOnB … U₁ U₂ Ue₁ Ue₂`, `Z : ZeroModelFamilyOn … U₁ U₂`). Hand-written copy under
the suffix `_BPS` (lane B-PORT-A's own port of the whole cloud file, `BoundaryPortCloudPackets`, is
not delivered; the names here are distinct).

* `cgpInQ3_BPS`, `cgpQ3Tags_BPS`: the tags of `Q₃ = H₀ ⊕ H_s` (slim and zero blocks);
* `cgpProjMap_BPS L Z t = π_t ∘ 𝓔⁰` and `cgpProjMap_apply_of_mem_BPS`;
* `cgpQ3Tags_slim_mem_BPS`, `cgpQ3Tags_zero_mem_BPS`, `cgpProjMap_apply_of_notMem_BPS`.
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

/-- Membership of a tag of `𝓔⁰` in `Q₃ = H₀ ⊕ H_s` (FC01, B:110; closed `cgpInQ3`). -/
def cgpInQ3_BPS : CGPTag_BAUGP L Z → Bool
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => false
  | .inr (.inr (.inr (.inl _))) => true
  | .inr (.inr (.inr (.inr _))) => false

/-- The tags of `Q₃`: slim and zero blocks (closed `cgpQ3Tags`). -/
def cgpQ3Tags_BPS : Finset (CGPTag_BAUGP L Z) :=
  Finset.univ.filter fun t => cgpInQ3_BPS L Z t = true

open Classical in
/-- `π_t 𝓔⁰`: the ported map followed by the orthogonal projection onto the blocks with tags in
`t` (closed `cgpProjMap`). -/
def cgpProjMap_BPS (t : Finset (CGPTag_BAUGP L Z)) (p : X) :
    BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²) :=
  blockRestrict t (cgpGlobalMap_BAUGP L Z p)

theorem cgpProjMap_apply_of_mem_BPS {t : Finset (CGPTag_BAUGP L Z)} {a : CGPTag_BAUGP L Z}
    (ha : a ∈ t) (p : X) : cgpProjMap_BPS L Z t p a = cgpGlobalMap_BAUGP L Z p a := by
  simp only [cgpProjMap_BPS, blockRestrict_apply, ha, ite_true]

theorem cgpProjMap_apply_of_notMem_BPS {t : Finset (CGPTag_BAUGP L Z)} {a : CGPTag_BAUGP L Z}
    (ha : a ∉ t) (p : X) : cgpProjMap_BPS L Z t p a = 0 := by
  simp only [cgpProjMap_BPS, blockRestrict_apply, ha, ite_false]

theorem cgpQ3Tags_slim_mem_BPS (j : L.slim.finite_centres.toFinset) :
    (.inr (.inl j) : CGPTag_BAUGP L Z) ∈ cgpQ3Tags_BPS L Z :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

theorem cgpQ3Tags_zero_mem_BPS (k : Z.finite_centres.toFinset) :
    (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP L Z) ∈ cgpQ3Tags_BPS L Z :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

end DifferentialGeometry.Geometry.Collapse
