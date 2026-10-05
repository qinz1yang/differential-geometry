import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceDecomposition
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementOriginalBCF2K

/-!
# BCF02: two consequences of `q ∈ M₂` on the actual decomposition (lane BCF2-K, G5a)

The strict replacement (Repl_∂) reads `q ∈ M₂` through ORIGINAL-coordinate facts (G1). Two of them
follow from the definitions of lane BIFACE's interface (`LE/BoundaryInterfaceDecomposition`):

* `BoundaryCompactSlimChoice.M₂_subset_D35_BCF2K`: `M₂ ⊆ {D ≥ 35}` — a point at boundary distance
  `< 35` lies in the OPEN neighbourhood `N₃₅(∂_b W)` of a boundary component (the components cover
  `∂W`), which is contained in the cusp core `C_b = N₃₅(∂_b W) ∪ {…}` of the SAME chain; so it lies
  in `int(Z ∪ C_∂)` and not in `M₁ ⊇ M₂`.
* `BoundaryCompactSlimChoice.M₂_original_consequences_BCF2K`: both, in the premise shape of
  (Repl_∂).
* `BoundaryCompactSlimChoice.slim_exclusion_of_mem_M₂_BCF2K` (the premise hS of (Repl_∂)): a point
  of `M₂` is outside every selected slim region `{d(q, k) < 9Δρ_k, |η_k(q)| < 10Δ}` — the region is
  open, lies in the original closed slab of `k`, hence in `X₃` (`slim_original_subset`) with image
  in `K₃` (BCF01's (K) for ALL original closed slabs, `slabs_subset`); on `M₁` it lies in
  `S = X₃ ∩ f₃⁻¹(K₃ ∩ D₃)`, so the point is in `int_{M₁} S`, removed from `M₂`. No continuity of the
  chain is used.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
  {Bs : BoundaryGaf02Bases C} {ZC : BoundaryInitialCoresSpec C}

namespace BoundaryCompactSlimChoice

/-- **`M₂ ⊆ {D ≥ 35}`**: a point at boundary distance `< 35` lies in the open `35`-neighbourhood of
a boundary component, which is part of the cusp core of that component; so it is in
`int(Z ∪ C_∂)`, outside `M₁ ⊇ M₂`. -/
theorem M₂_subset_D35_BCF2K (Kc : BoundaryCompactSlimChoice Bs ZC) :
    Kc.M₂ ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p} := by
  intro x hx
  by_contra h35
  have hlt : distanceToBoundary W g x < ENNReal.ofReal 35 := not_le.mp h35
  obtain ⟨q, hq⟩ := iInf_lt_iff.mp hlt
  have hqb : (q : W.Carrier) ∈ ⋃ i, S.packet.toBoundaryCollarPacket.cusp.component i := by
    rw [S.packet.toBoundaryCollarPacket.cusp.covers]
    exact q.2
  obtain ⟨i, hi⟩ := mem_iUnion.mp hqb
  -- the open neighbourhood `N₃₅(∂_i W)` of the component
  set N : Set W.Carrier := S.packet.toBoundaryCollarPacket.cuspNbhd35_BCG6K i with hN
  have hNopen : IsOpen N := by
    have hU : N = ⋃ y ∈ S.packet.toBoundaryCollarPacket.cusp.component i,
        {z | riemannianEDistOf g y z < ENNReal.ofReal 35} := by
      ext z
      simp only [hN, BoundaryCollarPacket.cuspNbhd35_BCG6K, mem_ofPred_eq, mem_iUnion,
        exists_prop]
    rw [hU]
    exact isOpen_biUnion fun y _ => isOpen_lt (continuous_riemannianEDist g y) continuous_const
  have hxN : x ∈ N := by
    refine ⟨q, hi, ?_⟩
    rw [riemannianEDistOf_comm]
    exact hq
  have hNsub : N ⊆ ZC.union ∪ C.cuspCores_BIF := by
    intro z hz
    refine Or.inr (mem_iUnion.mpr ⟨i, ?_⟩)
    exact Or.inl hz
  have hint : x ∈ interior (ZC.union ∪ C.cuspCores_BIF) :=
    interior_maximal hNsub hNopen hxN
  exact hx.1 hint

/-- **The slim exclusion on `M₂`** (premise hS of (Repl_∂), from BCF01's (K)): for `0 ≤ Δ`,
`0 ≤ σs`, a point `q` of `W°` with `q ∈ M₂` is outside every selected slim region:
`d(q, k) < 9Δρ_k` forces `|η_k(q)| ≥ 10Δ`. -/
theorem slim_exclusion_of_mem_M₂_BCF2K (Kc : BoundaryCompactSlimChoice Bs ZC) (hΔ : 0 ≤ Δ)
    (hσs : 0 ≤ σs) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    ∀ q : W.pieceInterior ⊤, q.val ∈ Kc.M₂ →
      ∀ k (hk : k ∈ S.family.slim.centres), dist q k < 9 * Δ * S.rho k →
        10 * Δ ≤ |(S.family.slim.centre k hk).coord_BCG2 q| := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro q hqM k hk hqk
  by_contra hη
  push Not at hη
  have hrk := S.rho_pos k
  -- the open slim region `R` around `q`
  set R : Set (W.pieceInterior ⊤) := {p | dist p k < 9 * Δ * S.rho k ∧
    |(S.family.slim.centre k hk).coord_BCG2 p| < 10 * Δ} with hR
  have hcoord : Continuous (S.family.slim.centre k hk).coord_BCG2 := by
    have hc0 : 0 ≤ (1 + σs) * (S.rho k)⁻¹ := by positivity
    have hL : LipschitzWith (Real.toNNReal ((1 + σs) * (S.rho k)⁻¹))
        (S.family.slim.centre k hk).coord_BCG2 :=
      LipschitzWith.of_dist_le_mul fun y z => by
        rw [Real.coe_toNNReal _ hc0, Real.dist_eq]
        exact (S.family.slim.centre k hk).abs_coord_sub_le_BCF2K hσs y z
    exact hL.continuous
  have hRopen : IsOpen R :=
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
      (isOpen_lt (continuous_abs.comp hcoord) continuous_const)
  have hqR : q ∈ R := ⟨hqk, hη⟩
  -- `R` lies in the slab of `k`, so in `X₃`, with image in `K₃`
  have hkc : k ∈ S.stageCentres_BIF 2 := hk
  have hslab : ∀ p ∈ R, p ∈ S.slimSlabs_BIF := by
    rintro p ⟨hp1, hp2⟩
    refine ⟨k, hkc, ?_, ?_⟩
    · have : 9 * Δ * S.rho k ≤ 1000000 * Δ * S.rho k := by nlinarith
      linarith
    · have he : S.slimEta_BIF k p = (S.family.slim.centre k hk).coord_BCG2 p := by
        unfold BoundarySupplyCore.slimEta_BIF
        rw [dite_eq_left hk]
      rw [he]
      linarith
  have hX₃ : ∀ p ∈ R, p.val ∈ Bs.source 2 := by
    intro p hp
    obtain ⟨j, hj, hpj, hpη⟩ := hslab p hp
    exact Bs.slim_original_subset p j hj hpj hpη
  have hK₃ : ∀ p ∈ R, C.stageMap 2 p.val ∈ Kc.K₃ := by
    intro p hp
    have h := Kc.slabs_subset ⟨p.val, ⟨p, hslab p hp, rfl⟩, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := h
    rw [← hyeq]
    have hy' := interior_subset hy
    exact hy'
  -- on `M₁`, `R` lies in the slim piece `S`
  have hRS : ∀ p ∈ R, p.val ∈ ZC.M₁ → p.val ∈ Kc.piece := by
    intro p hp hpM
    refine ⟨hX₃ p hp, hK₃ p hp, ⟨p.val, ⟨hpM, hX₃ p hp⟩, rfl⟩⟩
  -- `R` is open in `W`
  have hRW : IsOpen (Subtype.val '' R : Set W.Carrier) :=
    (W.pieceInterior ⊤).isOpen.isOpenMap_subtype_val R hRopen
  have hqM₁ : q.val ∈ ZC.M₁ := hqM.1
  have hrel : q.val ∈ relInterior_BIF ZC.M₁ Kc.piece := by
    refine ⟨⟨q.val, hqM₁⟩, ?_, rfl⟩
    refine mem_interior.mpr ⟨Subtype.val ⁻¹' (Subtype.val '' R), ?_,
      hRW.preimage continuous_subtype_val, ⟨q, hqR, rfl⟩⟩
    rintro ⟨y, hyM⟩ ⟨p, hp, hpy⟩
    have hpy' : p.val = y := hpy
    change y ∈ Kc.piece
    subst hpy'
    exact hRS p hp hyM
  exact hqM.2 hrel

/-- **Two original-coordinate consequences of `q ∈ M₂`** in the exact shape of the premises of
(Repl_∂) (consumer of the two lemmas above): `D(q) ≥ 35` and `q` outside every selected slim
region. -/
theorem M₂_original_consequences_BCF2K (Kc : BoundaryCompactSlimChoice Bs ZC) (hΔ : 0 ≤ Δ)
    (hσs : 0 ≤ σs) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    ∀ q : W.pieceInterior ⊤, q.val ∈ Kc.M₂ →
      ENNReal.ofReal 35 ≤ distanceToBoundary W g q ∧
      ∀ k (hk : k ∈ S.family.slim.centres), dist q k < 9 * Δ * S.rho k →
        10 * Δ ≤ |(S.family.slim.centre k hk).coord_BCG2 q| := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro q hq
  exact ⟨Kc.M₂_subset_D35_BCF2K hq, Kc.slim_exclusion_of_mem_M₂_BCF2K hΔ hσs q hq⟩

end BoundaryCompactSlimChoice

end DifferentialGeometry.Geometry.Collapse
