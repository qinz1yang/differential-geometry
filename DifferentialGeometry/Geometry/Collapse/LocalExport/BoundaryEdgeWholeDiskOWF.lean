import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeHomotopyRankOWF
import DifferentialGeometry.Topology.Ehresmann.WholeDiskTransport

/-!
# O-WF G6b: EDP04 on the boundary chain — the whole adjusted edge fibre is a smooth disk

**`BoundaryGaf02ChainE.edge_wholeDisk_OWF`**: for an `edgeB` centre `j`, `|a| < 4.05Δ` and a
level shift `0 ≤ δ ≤ Δ/10`, the whole adjusted fibre `{q ∈ Y_j : g(q) = a, T(q) ≤ 4Δ + δ}` of
the original source `Y_j = S.edgeSource_OWF j ⊆ W°` (`g = λ_j ∘ E ∘ val`, `T = A/s ∘ val`) is the
range of a smooth embedding `ClosedCell 2 → W°`, with boundary circle onto the rim
`{q ∈ Y_j : g = a, T = 4Δ + δ}` (`δ = 0`: the BASES fibre; `δ > 0`: used for the parent clause
`hsub`).

E0 (`wholeDisk_of_compact_transverse_trace_opens_EFC`) is applied ONCE, to the family
`h_θ = (1 − θ)η_j + θ(g − a)`, `T_θ = (1 − θ)H₀ + θ(T − δ)` at level `(0, 4Δ)` on the open source
`Y_j`: time `0` is the ORIGINAL ZERO fibre `{η_j = 0, H₀ ≤ 4Δ}` (`edge_zeroDisk_OWF`), time `1`
the adjusted fibre at level `a`. The whole trace lies in EDP03's compact buffer
(`edge_trace_OWF`, `edge_buffer_OWF`), `dh_θ ≠ 0` (`homotopy_reg_OWF`) and the pair has rank two
on the rim (`homotopy_face_OWF`). Closed twin: `Gaf02Chain.edp04_whole_disk_EFE` (which goes
through the original disk at level `a`).
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

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **EDP04 on the boundary chain: the whole adjusted edge fibre is a smooth disk** (see the
module docstring). -/
theorem edge_wholeDisk_OWF (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (j : S.EdgeIdx_BAUGD) {a δ : ℝ} (ha : |a| < 81 / 20 * Δ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ Δ / 10) :
    ∃ φ : ClosedCell 2 → W.pieceInterior ⊤, IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ φ ∧
      range φ = {q | q ∈ S.edgeSource_OWF j ∧ S.edgeRatio_BAUGD j (C.toChain.E q.val) = a ∧
        C.toChain.heightRatio q.val - δ ≤ 4 * Δ} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {q | q ∈ S.edgeSource_OWF j ∧
        S.edgeRatio_BAUGD j (C.toChain.E q.val) = a ∧
        C.toChain.heightRatio q.val - δ = 4 * Δ} := by
  obtain ⟨hΛ, hΔ0, -, -, -, -, -, -, -, hΔ1, hLΛ, -⟩ := C.std
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by nlinarith
  have hb8 : b * (1000 * Δ) ≤ 1 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 1000 * Δ)).mp hb
    linarith
  obtain ⟨-, hηs, hHs, -, Q, hQc, hQY, hQi⟩ := S.edge_buffer_OWF hΔ1 hμ hτ hlam hσc hb8 j
  obtain ⟨φ₀, hφ₀, hφ₀r, hφ₀b⟩ := S.edge_zeroDisk_OWF hΔ0 j
  set Y := S.edgeSource_OWF j with hYdef
  set η := S.edgeEta_BIF j.1 with hηdef
  set H₀ := S.edgeH0_OWF with hH₀def
  set gq : W.pieceInterior ⊤ → ℝ := fun z => S.edgeRatio_BAUGD j (C.toChain.E z.val) with hgq
  set Tq : W.pieceInterior ⊤ → ℝ := fun z => C.toChain.heightRatio z.val - δ with hTq
  have hYo : IsOpen Y := S.isOpen_edgeSource_OWF j
  let O : TopologicalSpace.Opens (W.pieceInterior ⊤) := ⟨Y, hYo⟩
  have hfst : ContMDiff ((𝓡 3).prod 𝓘(ℝ)) (𝓡 3) ∞
      (Prod.fst : W.pieceInterior ⊤ × ℝ → W.pieceInterior ⊤) := contMDiff_fst
  have hsnd : ContMDiff ((𝓡 3).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (Prod.snd : W.pieceInterior ⊤ × ℝ → ℝ) := contMDiff_snd
  have hgs : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (fun z => gq z - a) :=
    (C.edgeAdjusted_contMDiff_OWF j).sub contMDiff_const
  have hTs : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ Tq :=
    C.heightRatio_interior_contMDiff_OWF.sub contMDiff_const
  have hh : ContMDiffOn ((𝓡 3).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun x : W.pieceInterior ⊤ × ℝ => (1 - x.2) * η x.1 + x.2 * (gq x.1 - a))
      ((O : Set (W.pieceInterior ⊤)) ×ˢ univ) :=
    ((contMDiff_const.sub hsnd).contMDiffOn.mul
      (hηs.comp hfst.contMDiffOn (fun x hx => hx.1))).add
      (hsnd.contMDiffOn.mul (hgs.comp hfst).contMDiffOn)
  have hT : ContMDiffOn ((𝓡 3).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun x : W.pieceInterior ⊤ × ℝ => (1 - x.2) * H₀ x.1 + x.2 * Tq x.1)
      ((O : Set (W.pieceInterior ⊤)) ×ˢ univ) :=
    ((contMDiff_const.sub hsnd).contMDiffOn.mul
      (hHs.comp hfst.contMDiffOn (fun x hx => hx.1))).add
      (hsnd.contMDiffOn.mul (hTs.comp hfst).contMDiffOn)
  have hreg : ∀ τ' ∈ Icc (0 : ℝ) 1, ∀ y ∈ (O : Set (W.pieceInterior ⊤)),
      (1 - τ') * η y + τ' * (gq y - a) = 0 → (1 - τ') * H₀ y + τ' * Tq y ≤ 4 * Δ →
      Surjective (mfderiv (𝓡 3) 𝓘(ℝ) (fun z => (1 - τ') * η z + τ' * (gq z - a)) y) :=
    fun τ' hτ' y hy _ _ => C.homotopy_reg_OWF hμ hτ hσc hb hc j a hτ' hy
  have hface : ∀ τ' ∈ Icc (0 : ℝ) 1, ∀ y ∈ (O : Set (W.pieceInterior ⊤)),
      (1 - τ') * η y + τ' * (gq y - a) = 0 → (1 - τ') * H₀ y + τ' * Tq y = 4 * Δ →
      Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ × ℝ) (fun z =>
        ((1 - τ') * η z + τ' * (gq z - a), (1 - τ') * H₀ z + τ' * Tq z)) y) :=
    fun τ' hτ' y hy hfib hrim =>
      C.homotopy_face_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1 j ha hτ' hδ0 hδ hy hfib hrim
  have hloc : ∀ τ' ∈ Icc (0 : ℝ) 1, ∀ y ∈ (O : Set (W.pieceInterior ⊤)),
      (1 - τ') * η y + τ' * (gq y - a) = 0 → (1 - τ') * H₀ y + τ' * Tq y ≤ 4 * Δ → y ∈ Q := by
    intro τ' hτ' y hy hfib hH
    obtain ⟨hη41, ht42, -⟩ := C.edge_trace_OWF hc hC j ha hτ' hδ0 hδ hy hfib hH
    exact interior_subset (hQi ⟨hy.1, by linarith, ht42⟩)
  have hmemY : ∀ q, (letI := inducedMetricSpace S.completion.metric
      dist q j.1 < 100 * Δ * S.rho j.1) → η q = 0 → H₀ q ≤ 4 * Δ → q ∈ Y := by
    intro q hq hη hH
    have h5 : |η q| < 5 * Δ := by rw [hη, abs_zero]; positivity
    refine ⟨hq, h5, ?_⟩
    have := (edgeRowHeight_le_iff (F := S.edgeSmoothing_BAUGD) (ρ := fun x => S.rho x.val)
      hΔ0).mp hH
    change S.edgeSmoothing_BAUGD q / S.rho q.val < 5 * Δ
    linarith
  have hφ₀r' : range φ₀ = {y | y ∈ (O : Set (W.pieceInterior ⊤)) ∧
      (1 - 0) * η y + 0 * (gq y - a) = 0 ∧ (1 - 0) * H₀ y + 0 * Tq y ≤ 4 * Δ} := by
    rw [hφ₀r]
    ext q
    simp only [mem_ofPred_eq, sub_zero, one_mul, zero_mul, add_zero]
    constructor
    · rintro ⟨hq, hη, hH⟩
      exact ⟨hmemY q hq hη hH, hη, hH⟩
    · rintro ⟨hq, hη, hH⟩
      exact ⟨hq.1, hη, hH⟩
  have hφ₀b' : range (φ₀ ∘ cellBoundaryInclusion 2) =
      {y | y ∈ (O : Set (W.pieceInterior ⊤)) ∧ (1 - 0) * η y + 0 * (gq y - a) = 0 ∧
        (1 - 0) * H₀ y + 0 * Tq y = 4 * Δ} := by
    rw [hφ₀b]
    ext q
    simp only [mem_ofPred_eq, sub_zero, one_mul, zero_mul, add_zero]
    constructor
    · rintro ⟨hq, hη, hH⟩
      exact ⟨hmemY q hq hη hH.le, hη, hH⟩
    · rintro ⟨hq, hη, hH⟩
      exact ⟨hq.1, hη, hH⟩
  obtain ⟨φ, hφ, hr, hb', -⟩ :=
    wholeDisk_of_compact_transverse_trace_opens_EFC (I := 𝓡 3) O
      (fun x : W.pieceInterior ⊤ × ℝ => (1 - x.2) * η x.1 + x.2 * (gq x.1 - a))
      (fun x : W.pieceInterior ⊤ × ℝ => (1 - x.2) * H₀ x.1 + x.2 * Tq x.1)
      hh hT 0 (4 * Δ) hreg hface hQc hQY hloc hφ₀ hφ₀r' hφ₀b'
  refine ⟨φ, hφ, ?_, ?_⟩
  · rw [hr]
    ext q
    simp only [mem_ofPred_eq, sub_self, zero_mul, one_mul, zero_add, sub_eq_zero]
    rfl
  · rw [hb']
    ext q
    simp only [mem_ofPred_eq, sub_self, zero_mul, one_mul, zero_add, sub_eq_zero]
    rfl

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
