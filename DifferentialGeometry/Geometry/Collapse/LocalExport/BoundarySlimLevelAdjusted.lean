import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimLevelStandard

/-!
# O-WF G3d: FC34 on the slim chart — whole adjusted slim levels are standard `S²` or `T²`

**`BoundaryGaf02ChainE.slim_level_standard_OWF`** (closed twin `gaf07_slim_level_standard_GAFC`):
for `K ≥ 5`, EITHER every whole adjusted level `{q ∈ Y_j | κ_j(f₂ q) = a}`, `|a| < 4·10⁵Δ`, is the
image of a smooth embedding of the standard `ClosureSphere`, OR every one of the standard `Torus`:
S-BAUG-D2's `exists_embedding_adjusted_level_BAUGD` (FC34a) with the value / derivative clauses,
the right inverse of gauge `4/3`, the compact slab and the standard original levels.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic GC.GraphManifold
open scoped ENNReal

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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The whole adjusted slim levels are standard `S²` or `T²`** (see the module docstring). -/
theorem slim_level_standard_OWF (hc : c 2 < 1 / 1000) (hK : 5 ≤ K) (j : S.SlimIdx_BAUGD) :
    (∀ a : ℝ, |a| < 4 * (10 ^ 5 * Δ) → ∃ ψ : ClosureSphere.{0} → W.pieceInterior ⊤,
      IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ ψ ∧
        range ψ = {q | q ∈ S.slimY_OWF j ∧
          S.slimKappa_BBP j (C.toChain.stageMap 2 q.val) = a}) ∨
    (∀ a : ℝ, |a| < 4 * (10 ^ 5 * Δ) → ∃ ψ : Torus → W.pieceInterior ⊤,
      IsSmoothEmbedding torusModel (𝓡 3) ∞ ψ ∧
        range ψ = {q | q ∈ S.slimY_OWF j ∧
          S.slimKappa_BBP j (C.toChain.stageMap 2 q.val) = a}) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have : LocallyCompactSpace (W.pieceInterior ⊤) :=
    Manifold.locallyCompact_of_finiteDimensional (𝓡 3)
  obtain ⟨-, hΔ, -, -, -, -, -, -, -, h1Δ, -⟩ := C.std
  have hj : j.1 ∈ S.family.slim.centres := (Set.Finite.mem_toFinset _).mp j.2
  obtain ⟨H, hH0, hH1, hder⟩ := C.slim_final_deriv_close_OWF hc
  have hU := S.isOpen_slimY_OWF j
  have h56 : ∀ y ∈ S.slimY_OWF j, |S.slimEta_BIF j.1 y| < 6 * (10 ^ 5 * Δ) := fun y hy => by
    have := hy.2
    nlinarith
  have hη : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (S.slimEta_BIF j.1) (S.slimY_OWF j) := by
    rw [S.slimEta_eq_coord_fun_BBP j]
    refine (S.family.slim.centre j.1 hj).contMDiffOn_coord_BAUGA.mono fun q hq => ?_
    have h := hq.1
    convert h using 2
    norm_num
  have hg : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun q : W.pieceInterior ⊤ => S.slimKappa_BBP j (C.toChain.stageMap 2 q.val))
      (S.slimY_OWF j) := (C.slim_adjusted_contMDiff_OWF j).contMDiffOn
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  have hgη : ∀ y ∈ S.slimY_OWF j,
      ‖S.slimKappa_BBP j (C.toChain.stageMap 2 y.val) - S.slimEta_BIF j.1 y‖ < 1 / 800 :=
    fun y hy => by
      rw [Real.norm_eq_abs]
      exact C.slim_final_value_close_OWF hc j hy.1 (h56 y hy)
  have hright : ∀ y ∈ S.slimY_OWF j, ∃ R : ℝ →L[ℝ] E3,
      (show E3 →L[ℝ] ℝ from mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (S.slimEta_BIF j.1) y).comp R =
        ContinuousLinearMap.id ℝ ℝ ∧
        ∀ w, (fun (q : W.pieceInterior ⊤) (v : E3) =>
          (S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q v v)) y (R w) ≤ 4 / 3 * ‖w‖ :=
    fun y hy => C.slim_right_inverse_OWF j hy.1 (h56 y hy)
  have hDg : ∀ y ∈ S.slimY_OWF j, ∀ v : E3,
      ‖(show E3 →L[ℝ] ℝ from mfderiv (𝓡 3) 𝓘(ℝ, ℝ)
          (fun q : W.pieceInterior ⊤ => S.slimKappa_BBP j (C.toChain.stageMap 2 q.val)) y) v -
        (show E3 →L[ℝ] ℝ from mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (S.slimEta_BIF j.1) y) v‖ ≤
        H * (fun (q : W.pieceInterior ⊤) (v : E3) =>
          (S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q v v)) y v :=
    fun y hy v => hder j hy.1 (h56 y hy) v
  have hQ := C.slim_slab_compact_OWF j
  have hcK : H * (4 / 3) < 1 := by linarith
  rcases C.slim_original_standard_OWF hK j with h | h
  · refine Or.inl fun a ha => ?_
    obtain ⟨e₀, he₀, hr⟩ := h a ha
    exact exists_embedding_adjusted_level_BAUGD (by simp) hU hη hg hℓ
      (by rw [Real.norm_eq_abs]; exact ha) hgη _ hH0 hcK hright hDg hQ (𝓡 2) e₀ he₀ hr
  · refine Or.inr fun a ha => ?_
    obtain ⟨e₀, he₀, hr⟩ := h a ha
    exact exists_embedding_adjusted_level_BAUGD (by simp) hU hη hg hℓ
      (by rw [Real.norm_eq_abs]; exact ha) hgη _ hH0 hcK hright hDg hQ torusModel e₀ he₀ hr

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
