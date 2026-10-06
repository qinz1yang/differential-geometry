import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainPlacementBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainRatioKernelBGR
import DifferentialGeometry.Topology.Manifold.InteriorZeroExtension

/-!
# BCG07 F3, step Z4 (part): the linearized defining function of the actual zero domain on `W`
(lane B-BCG-ROWS)

Blueprint `master207B.tex`, ZSP02 (B:6390–6393) in the boundary setting: the global linearized
definer `H_k = ψ(η_k) + χ(η_k)(q − η_k)` of (ZH) at `τ = 1` (ported `zspDefiner_ZSP35_BGR`, with
`f = pr_int ∘ C.E ∘ val`) lives on `W°`; it equals `1/2` wherever `η_k ≥ 1/2`, hence off a
compact subset of `W°`, and `H_k − .4` is extended by the constant `1/10` to `W` (its smoothness on
`W` is the next step: `Manifold.contMDiff_extend_zero_pieceInterior_BAUGA` with the compact
`val '' B̄_ĝ(c_k, (.5 + e)R_k)`).

* `BoundaryGaf02Chain.zeroDefinerW_BGR C k : W.Carrier → ℝ` (the extension), `…_val_BGR`,
  `…_of_notMem_BGR`;
* **`zeroDefinerW_le_iff_BGR`**, **`zeroDefinerW_eq_zero_iff_BGR`**: `{F ≤ 0} = Z_k(C.E)`,
  `{F = 0} = (ZF)(C.E)` — BIFACEc's `domain_eq` / `face_eq` for this linearized `F` (no derivative
  input). The regularity at the face, `frontier_eq` and the ratio normal form (`ratio_near`, via
  `exists_ratioCompatible_global_definer_ZSP35` with `a = v_k/R_k`) need A3c's derivative bound.
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
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

namespace BoundaryGaf02Chain

variable (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)

/-- **The linearized defining function of the actual zero domain on `W`**: `H_k − .4` on `W°`
(with `f = pr_int ∘ C.E ∘ val`), the constant `1/10` at the points of `∂W`. -/
def zeroDefinerW_BGR (k : S.ZeroIdx_BAUGC) : W.Carrier → ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  fun p => 1 / 10 + Subtype.val.extend (fun x : W.pieceInterior ⊤ =>
    zspDefiner_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k C.zeroBindMap_BGR x - 1 / 2)
    0 p

theorem zeroDefinerW_val_BGR (k : S.ZeroIdx_BAUGC) (x : W.pieceInterior ⊤) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    C.zeroDefinerW_BGR k x.val =
      zspDefiner_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k C.zeroBindMap_BGR x -
        2 / 5 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  unfold zeroDefinerW_BGR
  rw [Subtype.val_injective.extend_apply]
  ring

theorem zeroDefinerW_of_notMem_BGR (k : S.ZeroIdx_BAUGC) {p : W.Carrier}
    (hp : ¬ ∃ x : W.pieceInterior ⊤, x.val = p) : C.zeroDefinerW_BGR k p = 1 / 10 := by
  unfold zeroDefinerW_BGR
  rw [Function.extend_apply' _ _ _ (fun ⟨x, hx⟩ => hp ⟨x, hx⟩)]
  simp

/-- **`domain_eq` for the linearized definer**: `{F ≤ 0} = Z_k(C.E)` on `W` (ZSP02's sublevel
identity on `W°`, G12's identification, and `F = 1/10` on `∂W`). -/
theorem zeroDefinerW_le_iff_BGR (hΔ : 1 ≤ Δ) (hT : 1600 * (1000000 * Δ) ≤ T) (he : e < 1 / 40)
    (k : S.ZeroIdx_BAUGC) :
    {p | C.zeroDefinerW_BGR k p ≤ 0} = C.actualZeroDomain_BIFc k := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hT1 : 1 ≤ T := by nlinarith only [hT, hΔ]
  have hT0 : 0 < T := by linarith only [hT1]
  obtain ⟨hsub, -⟩ := zsp_sublevel_eq_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
    C.zeroBindMap_BGR (C.delta_zero_lt_BGR hΔ hT) (C.zeroBind_ZE_BGR hT0 he k) he
  rw [C.actualZeroDomain_eq_image_BGR hT1 he k]
  ext p
  constructor
  · intro hp
    by_cases hx : ∃ x : W.pieceInterior ⊤, x.val = p
    · obtain ⟨x, rfl⟩ := hx
      have hv := C.zeroDefinerW_val_BGR k x
      have hp' : C.zeroDefinerW_BGR k x.val ≤ 0 := hp
      rw [hv] at hp'
      refine ⟨x, ?_, rfl⟩
      rw [← hsub]
      have h : zspDefiner_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k C.zeroBindMap_BGR x
          ≤ 2 / 5 := by linarith
      exact h
    · have h1 := C.zeroDefinerW_of_notMem_BGR k hx
      have hp' : C.zeroDefinerW_BGR k p ≤ 0 := hp
      rw [h1] at hp'
      norm_num at hp'
  · rintro ⟨x, hx, rfl⟩
    rw [← hsub] at hx
    have h : zspDefiner_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k C.zeroBindMap_BGR x
        ≤ 2 / 5 := hx
    change C.zeroDefinerW_BGR k x.val ≤ 0
    rw [C.zeroDefinerW_val_BGR k x]
    linarith

/-- **`face_eq` for the linearized definer**: `{F = 0} = (ZF)(C.E)` on `W`. -/
theorem zeroDefinerW_eq_zero_iff_BGR (hΔ : 1 ≤ Δ) (hT : 1600 * (1000000 * Δ) ≤ T)
    (he : e < 1 / 40) (k : S.ZeroIdx_BAUGC) :
    {p | C.zeroDefinerW_BGR k p = 0} = C.actualZeroFace_BIFc k := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hT1 : 1 ≤ T := by nlinarith only [hT, hΔ]
  have hT0 : 0 < T := by linarith only [hT1]
  obtain ⟨-, hlev⟩ := zsp_sublevel_eq_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
    C.zeroBindMap_BGR (C.delta_zero_lt_BGR hΔ hT) (C.zeroBind_ZE_BGR hT0 he k) he
  rw [C.actualZeroFace_eq_image_BGR hT1 he k]
  ext p
  constructor
  · intro hp
    by_cases hx : ∃ x : W.pieceInterior ⊤, x.val = p
    · obtain ⟨x, rfl⟩ := hx
      have hv := C.zeroDefinerW_val_BGR k x
      have hp' : C.zeroDefinerW_BGR k x.val = 0 := hp
      rw [hv] at hp'
      refine ⟨x, ?_, rfl⟩
      rw [← hlev]
      have h : zspDefiner_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k C.zeroBindMap_BGR x
          = 2 / 5 := by linarith
      exact h
    · have h1 := C.zeroDefinerW_of_notMem_BGR k hx
      have hp' : C.zeroDefinerW_BGR k p = 0 := hp
      rw [h1] at hp'
      norm_num at hp'
  · rintro ⟨x, hx, rfl⟩
    rw [← hlev] at hx
    have h : zspDefiner_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k C.zeroBindMap_BGR x
        = 2 / 5 := hx
    change C.zeroDefinerW_BGR k x.val = 0
    rw [C.zeroDefinerW_val_BGR k x]
    linarith

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
