import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimFibreEqualityBGR

/-!
# Consumer of F5 / F5z: `f₃(∂M₁ ∩ X₃)` is finite (lane S-BCG-ROWS)

`frontier_M₁_image_finite_BGR`: F4c (`∂M₁ = ⋃ (ZF)_k ∪ ⋃ H_b`) with F5 / F5z gives finitely many
base values — input (a) of BCF01's G1a (`exists_slimChartIntervals_BCF01`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

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

/-- **`f₃(∂M₁ ∩ X₃)` is finite** (F4c + F5 + F5z: each of the finitely many zero faces and cusp
fronts meeting `X₃` is one whole slim fibre, so it has ONE `f₃`-value) — the input (a) of BCF01's
G1a. -/
theorem frontier_M₁_image_finite_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    (C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2)).Finite := by
  have hF := C.frontier_M₁_BGR Z hrd hrd4 hrdc hprem hθ
  have hpiece : ∀ T : Set W.Carrier, (T ∩ Bs.source 2).Nonempty →
      (∃ y ∈ Bs.base 2, T = Bs.fibre 2 y) → (C.toChain.stageMap 2 '' (T ∩ Bs.source 2)).Finite :=
    fun T _ ⟨y, _, hy⟩ => by
      refine (Set.finite_singleton y).subset ?_
      rintro _ ⟨q, ⟨hqT, hqX⟩, rfl⟩
      rw [hy] at hqT
      exact hqT.2
  have hz : ∀ k : S.ZeroIdx_BAUGC,
      (C.toChain.stageMap 2 '' (C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2)).Finite :=
    fun k => by
    by_cases hne : (C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2).Nonempty
    · exact hpiece _ hne (C.zeroFace_eq_slimFibre_BGR WF Z hrd hrd4 hrdc hprem hθ k hne)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, image_empty]
      exact Set.finite_empty
  have hc : ∀ i : Fin S.packet.cusp.count,
      (C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2)).Finite := fun i => by
    by_cases hne : (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty
    · exact hpiece _ hne (C.cuspFront_eq_slimFibre_BGR WF Z hrd hrd4 hrdc hprem hθ i hne)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, image_empty]
      exact Set.finite_empty
  rw [hF, Set.union_inter_distrib_right, Set.iUnion_inter, Set.iUnion_inter, image_union,
    image_iUnion, image_iUnion]
  exact (Set.finite_iUnion hz).union (Set.finite_iUnion hc)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
