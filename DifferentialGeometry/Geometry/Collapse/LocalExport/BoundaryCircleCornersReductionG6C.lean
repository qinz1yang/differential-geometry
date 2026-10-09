import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornerLabelsG6C
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleFibreTubeG6C

/-!
# G6c reduction: the V32 corner record from a local description along each whole fibre

Lane O-G6C, G2 step "reduction" (review 77 R9 / D77-2, D80-8). With the label set
`L = circleLabelsAt_G6C Kc y` (completeness by construction, at most two labels by G1) and the
tube lemma (`exists_open_circleFibre_subset_G6C`), `CircleBaseCornersV32 Kc` follows from ONE local
datum per boundary point `y` of the circle base: an open `U ⊇` whole fibre of `y`, an open `O ∋ y`
of the ambient base space and functions `φ` on it, smooth with `φ f y = 0`, such that on `X₁ ∩ U`
the remainder is `{φ ∘ f₁ ≤ 0 on L}`, on `R_c ∩ U` each face of `L` is `{φ_f ∘ f₁ = 0}`, and the
differentials through `f₁` are independent on the fibre
(`circleBaseCornersV32_of_localDescription_G6C`). The clause `1 ≤ L.card` is DERIVED: with no
label the local description puts a neighbourhood of `y` in the base inside `f₁(R_c)`.
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

/-- **The V32 corner record from local descriptions along the whole fibres.** -/
theorem circleBaseCornersV32_of_localDescription_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (hrem : Kc.remainder ⊆ Bs.source 0)
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    (hloc : ∀ y ∈ C.toChain.stageMap 0 '' Kc.remainder,
      y ∉ relInterior_BIF (Bs.base 0) (C.toChain.stageMap 0 '' Kc.remainder) →
      ∃ (U : Set W.Carrier) (O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
        (φ : CircleFaceLabel74 Kc →
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
        IsOpen U ∧ Bs.fibre 0 y ⊆ U ∧ IsOpen O ∧ y ∈ O ∧
        (∀ f ∈ circleLabelsAt_G6C Kc y, ContDiffOn ℝ ∞ (φ f) O ∧ φ f y = 0) ∧
        (∀ p ∈ Bs.source 0 ∩ U, p ∈ Kc.remainder ↔
          ∀ f ∈ circleLabelsAt_G6C Kc y, φ f (C.toChain.stageMap 0 p) ≤ 0) ∧
        (∀ f ∈ circleLabelsAt_G6C Kc y, ∀ p ∈ Kc.remainder ∩ U,
          p ∈ circleFaceSet74 Kc f ↔ φ f (C.toChain.stageMap 0 p) = 0) ∧
        (∀ p ∈ Bs.fibre 0 y, Surjective fun v : TangentSpace W.model p =>
          fun f : circleLabelsAt_G6C Kc y =>
            mvfderiv W.model (fun q => φ f (C.toChain.stageMap 0 q)) p v)) :
    CircleBaseCornersV32 Kc := by
  intro y hy hyr
  obtain ⟨U, O₂, φ, hU, hfibU, hO₂, hyO₂, hsm, hdesc, hface, hsurj⟩ := hloc y hy hyr
  have hB : ∀ {y'}, y' ∈ C.toChain.stageMap 0 '' Kc.remainder → y' ∈ Bs.base 0 := fun hy' =>
    Bs.image_eq 0 ▸ image_mono hrem hy'
  obtain ⟨O₁, hO₁, hyO₁, htube⟩ := C.exists_open_circleFibre_subset_G6C WF (hB hy) hU hfibU
  have hX : ∀ {p}, C.toChain.stageMap 0 p ∈ Bs.base 0 → p ∈ Bs.source 0 := fun hp => by
    rw [Bs.circle_source_eq]
    exact hp
  have hinU : ∀ {p}, C.toChain.stageMap 0 p ∈ O₁ → C.toChain.stageMap 0 p ∈ Bs.base 0 →
      p ∈ U := fun hpO hpB => htube _ ⟨hpO, hpB⟩ ⟨hX hpB, rfl⟩
  have hcard := C.card_circleLabelsAt_le_two_G6C Z hrd hrd4 hrdc hprem hθ Kc hrem hsat hy
  refine ⟨O₁ ∩ O₂, circleLabelsAt_G6C Kc y, φ, hO₁.inter hO₂, ⟨hyO₁, hyO₂⟩, ?_, hcard.2.2,
    fun f hf => ⟨(hsm f hf).1.mono inter_subset_right, (hsm f hf).2, ?_⟩, hsurj, ?_,
    fun f hf => mem_circleLabelsAt_G6C.mpr hf⟩
  · -- `1 ≤ L.card`: otherwise `y` is in the relative interior
    by_contra hlt
    have hL : circleLabelsAt_G6C Kc y = ∅ := Finset.card_eq_zero.mp (by omega)
    apply hyr
    refine mem_relInterior_iff_BCF.mpr ⟨hB hy, O₁, hO₁, hyO₁, fun y' ⟨hy'O, hy'B⟩ => ?_⟩
    have hy'X : y' ∈ C.toChain.stageMap 0 '' Bs.source 0 := (Bs.image_eq 0).symm ▸ hy'B
    obtain ⟨p, hpX, rfl⟩ := hy'X
    refine ⟨p, (hdesc p ⟨hpX, hinU hy'O hy'B⟩).mpr ?_, rfl⟩
    rw [hL]
    intro f hf
    exact absurd hf (Finset.notMem_empty f)
  · -- the zero set of `φ_f` in `C₁` is the set of base points whose whole fibre is in the face
    ext y'
    constructor
    · rintro ⟨hy'O, hy'C, hz⟩
      refine ⟨hy'O, hy'C, fun q hq => ?_⟩
      have hqy : C.toChain.stageMap 0 q = y' := hq.2
      have hqU : q ∈ U := hinU (hqy ▸ hy'O.1) (hqy ▸ hB hy'C)
      have hqR : q ∈ Kc.remainder := circleFibre_subset_remainder_G6C hsat hy'C hq
      exact (hface f hf q ⟨hqR, hqU⟩).mpr (by rw [hqy]; exact hz)
    · rintro ⟨hy'O, hy'C, hsub⟩
      refine ⟨hy'O, hy'C, ?_⟩
      obtain ⟨q, hq⟩ := circleFibre_nonempty_G6C hrem hy'C
      have hqy : C.toChain.stageMap 0 q = y' := hq.2
      have hqU : q ∈ U := hinU (hqy ▸ hy'O.1) (hqy ▸ hB hy'C)
      have hqR : q ∈ Kc.remainder := circleFibre_subset_remainder_G6C hsat hy'C hq
      have := (hface f hf q ⟨hqR, hqU⟩).mp (hsub hq)
      rw [hqy] at this
      exact this
  · -- `C₁ ∩ O = {φ ≤ 0 on L}` near `y`
    ext y'
    constructor
    · rintro ⟨⟨p, hpR, rfl⟩, hpO⟩
      have hpB : C.toChain.stageMap 0 p ∈ Bs.base 0 := hB ⟨p, hpR, rfl⟩
      exact ⟨⟨hpO, hpB⟩, (hdesc p ⟨hrem hpR, hinU hpO.1 hpB⟩).mp hpR⟩
    · rintro ⟨⟨hy'O, hy'B⟩, hle⟩
      have hy'X : y' ∈ C.toChain.stageMap 0 '' Bs.source 0 := (Bs.image_eq 0).symm ▸ hy'B
      obtain ⟨p, hpX, rfl⟩ := hy'X
      exact ⟨⟨p, (hdesc p ⟨hpX, hinU hy'O.1 hy'B⟩).mpr hle, rfl⟩, hy'O⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
