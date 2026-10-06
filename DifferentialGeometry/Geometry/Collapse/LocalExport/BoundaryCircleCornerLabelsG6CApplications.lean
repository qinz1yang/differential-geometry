import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornerLabelsG6C

/-!
# Consumers of the G6c labels (lane O-G6C, G1)

On ONE v2b decomposition `dec` (with G6's conjuncts `R_c ⊆ X₁` and saturation of `R_c`):

* `circleLabels_package_G6C`: at every point of the ACTUAL circle-base image `f₁(R_c)` the whole
  fibre is non-empty and inside `R_c`, the label set `circleLabelsAt_G6C` has at most two labels
  and contains every label whose face contains the whole fibre (one witness, D80-8);
* `circleLabels_independent_G6C`: at a corner fibre (a point of the fibre on `X₂ ∩ {T = 4Δ}` where
  `h_ℓ ∘ f₂` vanishes, the fibre inside the face of `ℓ`) the descended face functions of the WHOLE
  label set have jointly surjective differentials through `f₁`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
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
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The label package at every point of the actual circle-base image** (D80-8: non-empty whole
fibre, at most two labels, completeness by construction). -/
theorem circleLabels_package_G6C (dec : BoundaryActualDecompositionV2b C.toChain) {rd : ℝ}
    (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (hrem : dec.slim.remainder ⊆ dec.bases.source 0)
    (hsat : dec.slim.remainder = dec.bases.source 0 ∩
      C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' dec.slim.remainder)) :
    ∀ y ∈ C.toChain.stageMap 0 '' dec.slim.remainder, (dec.bases.fibre 0 y).Nonempty ∧
      dec.bases.fibre 0 y ⊆ dec.slim.remainder ∧ (circleLabelsAt_G6C dec.slim y).card ≤ 2 ∧
      ∀ f : CircleFaceLabel74 dec.slim, dec.bases.fibre 0 y ⊆ circleFaceSet74 dec.slim f →
        f ∈ circleLabelsAt_G6C dec.slim y := by
  intro y hy
  exact ⟨circleFibre_nonempty_G6C hrem hy, circleFibre_subset_remainder_G6C hsat hy,
    (C.card_circleLabelsAt_le_two_G6C dec.zero hrd hrd4 hrdc hprem hθ dec.slim hrem hsat hy).2.2,
    fun f hf => mem_circleLabelsAt_G6C.mpr hf⟩

/-- **Independence on the whole label set at a corner fibre.** -/
theorem circleLabels_independent_G6C (dec : BoundaryActualDecompositionV2b C.toChain) {rd : ℝ}
    (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (hrem : dec.slim.remainder ⊆ dec.bases.source 0)
    (hsat : dec.slim.remainder = dec.bases.source 0 ∩
      C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' dec.slim.remainder))
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 0 '' dec.slim.remainder) {ℓ : dec.slim.EdgeFaceLabel_BIFc}
    (hℓ : dec.bases.fibre 0 y ⊆ dec.slim.edgeFaceSet_BIFc ℓ) {p : W.Carrier}
    (hp : p ∈ dec.bases.source 1) (hz : dec.edge.faceFun ℓ (C.toChain.stageMap 1 p) = 0)
    (hT : C.toChain.heightRatio p = 4 * Δ) :
    Surjective fun v : TangentSpace W.model p => fun f : circleLabelsAt_G6C dec.slim y =>
      mvfderiv W.model (fun q => C.circleFaceFun_G6C dec.edge f (C.toChain.stageMap 0 q)) p v := by
  refine C.circleFaceFuns_surjective_G6C dec.edge (fun f hf => ?_) hp hz hT
  rw [mem_circleLabelsAt_G6C] at hf
  rcases f with ℓ' | u
  · exact Or.inl (congrArg Sum.inl (C.horizontalLabel_unique_of_mem_image_G6C dec.zero hrd hrd4
      hrdc hprem hθ dec.slim hrem hsat hy hf hℓ))
  · exact Or.inr rfl

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
