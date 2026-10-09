import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimLevelChain

/-!
# O-WF G3c: the whole adjusted slim levels are standard `S²` or `T²` (FC34 on `W°`)

`BoundaryGaf02ChainE.slim_right_inverse_OWF` (LFR20.1: a right inverse of `Dη_j` of gauge size
`≤ 4/3`), `BoundaryGaf02ChainE.slim_slab_compact_OWF`, and **`slim_level_standard_OWF`**: for
`K ≥ 5`, EITHER every whole adjusted slim level `{q ∈ Y_j | κ_j(f₂ q) = a}`, `|a| < 4·10⁵Δ`, is
the image of a smooth embedding of the standard `ClosureSphere`, OR every one of the standard
`Torus` (closed twin `gaf07_slim_level_standard_GAFC`).
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

include C in
/-- **LFR20.1's right inverse** of `Dη_j` at a slim plateau point, of gauge size `≤ 4/3`. -/
theorem slim_right_inverse_OWF (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) :
    ∃ R : ℝ →L[ℝ] E3,
      (show E3 →L[ℝ] ℝ from mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (S.slimEta_BIF j.1) q).comp R =
        ContinuousLinearMap.id ℝ ℝ ∧
      ∀ w, (S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q (R w) (R w)) ≤ 4 / 3 * ‖w‖ := by
  have hr := S.rho_pos j.1
  obtain ⟨u, hu1, hu2⟩ := S.slim_derivative_lower_BBP j hq hη C.std.2.1.le
  set r := mvfderiv (𝓡 3) (S.slimEta_BIF j.1) q u with hrdef
  have hr0 : 0 < r := by linarith
  have hI : S.completion.metric.inner q u u = S.rho j.1 ^ 2 := by
    field_simp at hu1
    linarith
  have hsu : (S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q u u) = 1 := by
    rw [hI, Real.sqrt_sq hr.le, inv_mul_cancel₀ hr.ne']
  refine ⟨ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (r⁻¹ • u), ?_, fun t => ?_⟩
  · refine ContinuousLinearMap.ext fun t => ?_
    change mvfderiv (𝓡 3) (S.slimEta_BIF j.1) q (t • r⁻¹ • u) = t
    rw [map_smul, map_smul, ← hrdef, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ hr0.ne', mul_one]
  · change (S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q (t • r⁻¹ • u)
      (t • r⁻¹ • u)) ≤ 4 / 3 * ‖t‖
    have hin : S.completion.metric.inner q (t • r⁻¹ • u) (t • r⁻¹ • u) =
        (t * r⁻¹) ^ 2 * S.completion.metric.inner q u u := by
      rw [smul_smul]
      simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hin, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    have h1 : (S.rho j.1)⁻¹ * (|t * r⁻¹| * Real.sqrt (S.completion.metric.inner q u u)) =
        |t * r⁻¹| := by
      rw [mul_left_comm, hsu, mul_one]
    rw [h1, abs_mul, abs_of_pos (inv_pos.mpr hr0), Real.norm_eq_abs]
    have h2 : r⁻¹ ≤ 4 / 3 := by
      rw [inv_le_comm₀ hr0 (by norm_num)]
      linarith
    nlinarith [abs_nonneg t]

include C in
/-- **The compact slab of `Y_j`**: `{y ∈ Y_j | ‖η_j y‖ ≤ 4.01·10⁵Δ}` is compact. -/
theorem slim_slab_compact_OWF (j : S.SlimIdx_BAUGD) :
    IsCompact {y | y ∈ S.slimY_OWF j ∧ ‖S.slimEta_BIF j.1 y‖ ≤ 401 / 100 * (10 ^ 5 * Δ)} := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ := C.std.2.1
  have hj : j.1 ∈ S.family.slim.centres := (Set.Finite.mem_toFinset _).mp j.2
  have h := (S.family.slim.centre j.1 hj).isCompact_slab_OWF
    (a := 401 / 100 * (10 ^ 5 * Δ)) (by nlinarith)
  have e := S.slimEta_eq_coord_fun_BBP j
  convert h using 1
  ext x
  constructor
  · rintro ⟨⟨hx, -⟩, hxa⟩
    refine ⟨by convert hx using 2; norm_num, ?_⟩
    rw [← Real.norm_eq_abs, ← congrFun e x]
    exact hxa
  · rintro ⟨hx, hxa⟩
    have hxa' : ‖S.slimEta_BIF j.1 x‖ ≤ 401 / 100 * (10 ^ 5 * Δ) := by
      rw [congrFun e x, Real.norm_eq_abs]
      exact hxa
    refine ⟨⟨by convert hx using 2; norm_num, ?_⟩, hxa'⟩
    rw [← Real.norm_eq_abs]
    have : 401 / 100 * (10 ^ 5 * Δ) < 5 * (10 ^ 5 * Δ) := by nlinarith
    linarith

include C in
/-- **The standard original slim levels on `Y_j`** (from the regional centre's standard type). -/
theorem slim_original_standard_OWF (hK : 5 ≤ K) (j : S.SlimIdx_BAUGD) :
    (∀ a : ℝ, |a| < 4 * (10 ^ 5 * Δ) → ∃ e₀ : ClosureSphere.{0} → W.pieceInterior ⊤,
      IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀ ∧
        range e₀ = {y | y ∈ S.slimY_OWF j ∧ S.slimEta_BIF j.1 y = a}) ∨
    (∀ a : ℝ, |a| < 4 * (10 ^ 5 * Δ) → ∃ e₀ : Torus → W.pieceInterior ⊤,
      IsSmoothEmbedding torusModel (𝓡 3) ∞ e₀ ∧
        range e₀ = {y | y ∈ S.slimY_OWF j ∧ S.slimEta_BIF j.1 y = a}) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨-, hΔ, -, -, -, -, -, -, -, h1Δ, -⟩ := C.std
  have hj : j.1 ∈ S.family.slim.centres := (Set.Finite.mem_toFinset _).mp j.2
  have e := S.slimEta_eq_coord_fun_BBP j
  have hset : ∀ a : ℝ, |a| < 4 * (10 ^ 5 * Δ) →
      {x | x ∈ ball j.1 (10 ^ 6 * Δ * S.rho j.1) ∧
        (S.family.slim.centre j.1 hj).coord_BCG2 x = a} =
      {y | y ∈ S.slimY_OWF j ∧ S.slimEta_BIF j.1 y = a} := by
    intro a ha
    ext x
    constructor
    · rintro ⟨hx, hxa⟩
      have hxa' : S.slimEta_BIF j.1 x = a := (congrFun e x).trans hxa
      refine ⟨⟨by convert hx using 2; norm_num, ?_⟩, hxa'⟩
      rw [hxa']
      linarith
    · rintro ⟨⟨hx, -⟩, hxa⟩
      exact ⟨by convert hx using 2; norm_num, (congrFun e x).symm.trans hxa⟩
  have h4 : 4 * (10 ^ 5 * Δ) ≤ 905 * 10 ^ 3 * Δ := by nlinarith
  rcases (S.family.slim.centre j.1 hj).standard_level_embedding_OWF hK h1Δ oM with h | h
  · refine Or.inl fun a ha => ?_
    obtain ⟨e₀, he₀, hr⟩ := h a (ha.trans_le h4)
    exact ⟨e₀, he₀, hr.trans (hset a ha)⟩
  · refine Or.inr fun a ha => ?_
    obtain ⟨e₀, he₀, hr⟩ := h a (ha.trans_le h4)
    exact ⟨e₀, he₀, hr.trans (hset a ha)⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
