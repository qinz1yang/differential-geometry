import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimFibreEqualityBGR

/-!
# BCG07 F5 without the zero-domain structure: a cusp front meeting `X₃` is ONE whole slim fibre
(S-BCG-ROWS2 G28)

G19 / G23 proved F5 (`cuspFront_eq_slimFibre_BGR`) with the structure
`Z : BoundaryActualZeroDomains_BIFc` as an input, only because the whole slim fibre through a front
point was shown to lie in the front through the saturation of `∂M₁` (`Z.face_saturated`). The front
is saturated along EVERY stage map directly (BCG07: every `π_j` retains the WHOLE physical boundary
block; `cuspFront_saturated_BIF`, BIFACE G3), so the fibre lies in the front with no input from the
zero domains. This file restates F5 on that route:

* **`cuspFront_fibre_subset_direct_BGR`**: the whole slim fibre through a front point lies in the
  front;
* **`cuspFront_eq_slimFibre_direct_BGR`**: F5 — inputs only the v2 bases `Bs`, the whole-fibre
  layer `WF` and E4's premises (no `Z`, no `face_param`, no `hεr`).
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

/-- **The whole slim fibre through a front point of `X₃` lies in the front** (direct: `π_j` retains
the whole boundary block). -/
theorem cuspFront_fibre_subset_direct_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (i : Fin S.packet.cusp.count) {p : W.Carrier} (hp : p ∈ C.toChain.cuspFront_BIF i) :
    Bs.fibre 2 (C.toChain.stageMap 2 p) ⊆ C.toChain.cuspFront_BIF i :=
  fun _ hq => C.toChain.cuspFront_saturated_BIF 2 i hp hq.2

/-- **F5 without `Z`: a cusp front meeting `X₃` is ONE whole slim fibre** (frozen v3.1 F5 with the
premises of E4; the zero domains of `C.E` do not occur). -/
theorem cuspFront_eq_slimFibre_direct_BGR {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
      ∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y := by
  rintro i ⟨p, hp, hpX⟩
  obtain ⟨hsm, hfeq, hreg⟩ := C.cuspFront_level_data_BGR hrd hrd4 hrdc hprem hθ i
  have hSX : C.toChain.cuspFront_BIF i ∩ Bs.source 2 = Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹'
      (C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2)) := by
    ext q
    constructor
    · rintro ⟨hq, hqX⟩
      exact ⟨hqX, q, ⟨hq, hqX⟩, rfl⟩
    · rintro ⟨hqX, p', ⟨hp', hpX'⟩, hpq⟩
      exact ⟨C.toChain.cuspFront_saturated_BIF 2 i hp' hpq.symm, hqX⟩
  have hfibsub := C.cuspFront_fibre_subset_direct_BGR (Bs := Bs) i hp
  obtain ⟨O, hO, hOD⟩ := C.slim_isolation_BGR WF hsm hpX (cc := 40)
    (fun q hq hqp => by
      have h : q ∈ C.toChain.cuspFront_BIF i := hfibsub ⟨hq, hqp⟩
      rw [hfeq] at h
      exact h)
    (fun q hq q' hq' hqq' hq0 => by
      have hqf : q ∈ C.toChain.cuspFront_BIF i ∩ Bs.source 2 :=
        ⟨by rw [hfeq]; exact hq0, hq⟩
      have h : q' ∈ C.toChain.cuspFront_BIF i ∩ Bs.source 2 := by
        rw [hSX]
        exact ⟨hq', q, hqf, hqq'⟩
      have h' : q' ∈ C.toChain.cuspFront_BIF i := h.1
      rw [hfeq] at h'
      exact h')
    (hreg p hp)
  rw [← hfeq] at hOD
  refine ⟨C.toChain.stageMap 2 p, Bs.image_eq 2 ▸ mem_image_of_mem _ hpX, ?_⟩
  exact DifferentialGeometry.Topology.eq_fiber_of_isPreconnected_of_isolated
    (C.toChain.stageMap 2) (Bs.source 2) (C.toChain.cuspFront_BIF i)
    (C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2))
    (Bs.isOpen_source 2 (by decide)) (Bs.continuousOn_stageMap_BCF 2)
    (C.isPreconnected_cuspFront_BGR hrd hrd4 hrdc hprem hθ i) hSX ⟨O, hO, hOD⟩
    (Bs.proper 2 {C.toChain.stageMap 2 p}
      (singleton_subset_iff.mpr (Bs.image_eq 2 ▸ mem_image_of_mem _ hpX)) isCompact_singleton)
    ⟨p, hpX, rfl⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
