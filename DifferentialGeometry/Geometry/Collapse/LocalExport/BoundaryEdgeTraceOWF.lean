import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeBufferSupplyOWF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeRimSurjective
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesEdgeParentData

/-!
# O-WF G6b (part 1): EDP04's whole time trace on the boundary chain

For the homotopy `h_θ = (1 − θ)η_j + θ(g − a)`, `T_θ = (1 − θ)H₀ + θ(T − δ)` (`θ ∈ [0, 1]`,
`0 ≤ δ ≤ Δ/10` the shift of the level `4Δ + δ`,
`g = λ_j ∘ E`, `T = A/s`; level `0`, so that time `0` is the ORIGINAL ZERO fibre and time `1`
the adjusted fibre `{g = a}`), on the original source `Y_j`:

* `edge_height_band_numbers_OWF`, `edge_trace_numbers_OWF`: the pure-real cores.
* `BoundaryGaf02ChainE.edge_height_band_OWF` (EDP03's (EH) and the low band on `W°`):
  `t ≤ 2Δ ⟹ T < 2Δ + 10⁻³` and `t ≥ 2Δ ⟹ |T − t| < 10⁻³`.
* `BoundaryGaf02ChainE.edge_value_close_OWF`: `|g − η_j| ≤ 1/400` on the cutoff plateau.
* `BoundaryGaf02ChainE.edge_trace_OWF`: on the trace (`h_θ = 0`, `T_θ ≤ 4Δ`, `|a| < 4.05Δ`):
  `|η_j| < 4.1Δ`, `t < 4.2Δ`, and on its rim (`T_θ = 4Δ`) `3.8Δ < t < 4.2Δ`.

Register premises: `c₃ < 10⁻⁵`, `C_ρΛΔ < 10⁻⁶` (N76-9).
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **The height band, pure-real core**: with `|s − ρ| ≤ κρ`, `|A − A_F| < c₃ρ`, `A_F ≤ P`
(`= P` once `t = P/ρ ≥ .3Δ`), `t < 6Δ`, `κΔ < 10⁻⁶`, `c₃ < 10⁻⁵`: `t ≤ 2Δ ⟹ A/s < 2Δ + 10⁻³`
and `t ≥ 2Δ ⟹ |A/s − t| < 10⁻³`. -/
theorem edge_height_band_numbers_OWF {ρq P A s AF c₃ κ Δ : ℝ} (hρq : 0 < ρq)
    (hs : |s - ρq| ≤ κ * ρq) (hAerr : |A - AF| < c₃ * ρq) (hAP : AF ≤ P)
    (hAFeq : 3 / 10 * Δ ≤ P / ρq → AF = P) (ht6 : P / ρq < 6 * Δ) (hΔ : 1 ≤ Δ)
    (hκ : 0 ≤ κ) (hϑ : κ * Δ < 1 / 1000000) (hc₃ : c₃ < 1 / 100000) :
    (P / ρq ≤ 2 * Δ → A / s < 2 * Δ + 1 / 1000) ∧
      (2 * Δ ≤ P / ρq → |A / s - P / ρq| < 1 / 1000) := by
  have hκ1 : κ < 1 / 1000000 := by nlinarith
  have hsl : (1 - κ) * ρq ≤ s := by
    have := (abs_le.mp hs).1
    linarith
  have hspos : 0 < s := by nlinarith
  have hϑρ : κ * Δ * ρq ≤ 1 / 1000000 * ρq := mul_le_mul_of_nonneg_right hϑ.le hρq.le
  have hκρ : κ * ρq ≤ 1 / 1000000 * ρq := mul_le_mul_of_nonneg_right hκ1.le hρq.le
  have hc₃ρ : c₃ * ρq ≤ 1 / 100000 * ρq := mul_le_mul_of_nonneg_right hc₃.le hρq.le
  constructor
  · intro h2
    have hP : P ≤ 2 * Δ * ρq := by rwa [div_le_iff₀ hρq] at h2
    have hA : A < P + c₃ * ρq := by
      have := (abs_lt.mp hAerr).2
      linarith
    rw [div_lt_iff₀ hspos]
    have h1 : (2 * Δ + 1 / 1000) * ((1 - κ) * ρq) ≤ (2 * Δ + 1 / 1000) * s :=
      mul_le_mul_of_nonneg_left hsl (by positivity)
    have h3 : (2 * Δ + 1 / 1000) * ((1 - κ) * ρq) =
        2 * Δ * ρq + 1 / 1000 * ρq - 2 * (κ * Δ * ρq) - 1 / 1000 * (κ * ρq) := by ring
    nlinarith
  · intro h2
    have h3 : 3 / 10 * Δ ≤ P / ρq := by linarith
    rw [hAFeq h3] at hAerr
    have ht0 : 0 ≤ P / ρq := by linarith
    have hkey : A / s - P / ρq = ((A - P) - P / ρq * (s - ρq)) / s := by
      field_simp
      ring
    rw [hkey, abs_div, abs_of_pos hspos, div_lt_iff₀ hspos]
    have hn1 : |(A - P) - P / ρq * (s - ρq)| ≤ |A - P| + P / ρq * |s - ρq| := by
      calc _ ≤ |A - P| + |P / ρq * (s - ρq)| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg ht0]
    have hn2 : P / ρq * |s - ρq| ≤ 6 * Δ * (κ * ρq) :=
      mul_le_mul ht6.le hs (abs_nonneg _) (by linarith)
    have hn3 : 6 * Δ * (κ * ρq) = 6 * (κ * Δ * ρq) := by ring
    have hs1 : 1 / 1000 * ((1 - κ) * ρq) ≤ 1 / 1000 * s :=
      mul_le_mul_of_nonneg_left hsl (by norm_num)
    nlinarith

/-- **The trace, pure-real core** (see the module docstring), at the shifted level `4Δ + δ`,
`0 ≤ δ ≤ Δ/10` (`T_θ = (1 − θ)H₀ + θ(T − δ)`). -/
theorem edge_trace_numbers_OWF {Δ θ η g a H T t δ : ℝ} (hΔ : 1 ≤ Δ) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ Δ / 10) (hgη : |g - η| ≤ 1 / 400) (ha : |a| < 81 / 20 * Δ)
    (hlow : t ≤ 2 * Δ → T < 2 * Δ + 1 / 1000) (hhigh : 2 * Δ ≤ t → |T - t| < 1 / 1000)
    (hH2 : t ≤ 2 * Δ → H ≤ 2 * Δ) (hHt : 2 * Δ ≤ t → H = t)
    (hfib : (1 - θ) * η + θ * (g - a) = 0) (hHle : (1 - θ) * H + θ * (T - δ) ≤ 4 * Δ) :
    |η| < 41 / 10 * Δ ∧ t < 21 / 5 * Δ ∧
      ((1 - θ) * H + θ * (T - δ) = 4 * Δ → 19 / 5 * Δ < t ∧ t < 21 / 5 * Δ) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hηe : η = θ * (η - g) + θ * a := by linarith
  have hb1 : |θ * (η - g)| ≤ 1 / 400 := by
    rw [abs_mul, abs_of_nonneg hθ0, abs_sub_comm]
    calc θ * |g - η| ≤ 1 * (1 / 400) := mul_le_mul hθ1 hgη (abs_nonneg _) zero_le_one
      _ = 1 / 400 := one_mul _
  have hb2 : |θ * a| ≤ |a| := by
    rw [abs_mul, abs_of_nonneg hθ0]
    exact mul_le_of_le_one_left (abs_nonneg _) hθ1
  have hη : |η| < 41 / 10 * Δ := by
    rw [hηe]
    calc |θ * (η - g) + θ * a| ≤ |θ * (η - g)| + |θ * a| := abs_add_le _ _
      _ < 41 / 10 * Δ := by linarith
  have hθT : ∀ x : ℝ, θ * x ≤ |x| := fun x =>
    (mul_le_mul_of_nonneg_left (le_abs_self x) hθ0).trans
      (mul_le_of_le_one_left (abs_nonneg x) hθ1)
  have hθδ : θ * δ ≤ δ := mul_le_of_le_one_left hδ0 hθ1
  have hθδ0 : 0 ≤ θ * δ := mul_nonneg hθ0 hδ0
  refine ⟨hη, ?_, fun hrim => ?_⟩
  · rcases le_or_gt t (2 * Δ) with h2 | h2
    · linarith
    · have hE := hhigh h2.le
      rw [hHt h2.le] at hHle
      have h1 : t - 4 * Δ ≤ θ * (t - T) + θ * δ := by linarith
      have h3 := hθT (t - T)
      rw [abs_sub_comm] at h3
      linarith
  · have h2 : 2 * Δ < t := by
      by_contra hcon
      rw [not_lt] at hcon
      have hA := hH2 hcon
      have hB := hlow hcon
      have e1 : (1 - θ) * H ≤ (1 - θ) * (2 * Δ) := mul_le_mul_of_nonneg_left hA (by linarith)
      have e2 : θ * T ≤ θ * (2 * Δ + 1 / 1000) := mul_le_mul_of_nonneg_left hB.le hθ0
      nlinarith
    have hE := hhigh h2.le
    rw [hHt h2.le] at hrim
    have heq : t - 4 * Δ = θ * (t - T) + θ * δ := by linarith
    have h3 := hθT (t - T)
    have h4 := hθT (T - t)
    rw [abs_sub_comm] at h3
    have h5 := (abs_lt.mp hE)
    constructor
    · nlinarith
    · nlinarith

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
/-- **EDP03's (EH) and the low band on `W°`** (see the module docstring). -/
theorem edge_height_band_OWF (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 8 * Δ) (ht : S.edgeHeightRaw q < 6 * Δ) :
    (S.edgeHeightRaw q ≤ 2 * Δ → C.toChain.heightRatio q.val < 2 * Δ + 1 / 1000) ∧
      (2 * Δ ≤ S.edgeHeightRaw q →
        |C.toChain.heightRatio q.val - S.edgeHeightRaw q| < 1 / 1000) := by
  obtain ⟨hΛ, hΔ0, -, -, -, -, -, -, -, hΔ1, -, -⟩ := C.std
  have hρq := S.rho_pos q.val
  have hs := (C.scale_edp01_BAUGD.2 q.val).2.1
  have hκ : 0 ≤ 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ :=
    mul_nonneg (by linarith [C.scale_edp01_BAUGD.1]) hΛ
  have hAF := C.stage_error_lt_BAUGD 2 q.val
  have hAerr : |C.toChain.height q.val - S.heightCoord_BIF (S.boundaryOriginalMap q.val)| <
      c 2 * S.rho q.val := by
    have h1 := S.abs_heightFun_le_BAUGD (C.toChain.E q.val - S.boundaryOriginalMap q.val)
    rw [map_sub] at h1
    exact h1.trans_lt hAF
  have hAP := S.heightCoord_boundaryOriginalMap_le_BAUGD q
  have hAFeq : 3 / 10 * Δ ≤ S.edgeSmoothing_BAUGD q / S.rho q.val →
      S.heightCoord_BIF (S.boundaryOriginalMap q.val) = S.edgeSmoothing_BAUGD q := fun h3 => by
    have hm := S.edgeBMarker_eq_one_BAUGD hΔ0 j q hd hη h3 (by
      change S.edgeSmoothing_BAUGD q / S.rho q.val ≤ 8 * Δ
      rw [← S.edgeHeightRaw_eq_BAUGD]
      linarith)
    rw [S.heightCoord_boundaryOriginalMap_BAUGD, hm, one_mul]
    rfl
  have ht6 : S.edgeSmoothing_BAUGD q / S.rho q.val < 6 * Δ := by
    rw [← S.edgeHeightRaw_eq_BAUGD]; exact ht
  have h := edge_height_band_numbers_OWF hρq hs hAerr hAP hAFeq ht6 hΔ1 hκ hC hc
  rw [← S.edgeHeightRaw_eq_BAUGD] at h
  exact h

include C in
/-- **`g` is close to `η_j` on the cutoff plateau**: `|λ_j(E q) − η_j(q)| ≤ 1/400`. -/
theorem edge_value_close_OWF (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 8 * Δ) (ht : S.edgeHeightRaw q ≤ 8 * Δ) :
    |S.edgeRatio_BAUGD j (C.toChain.E q.val) - S.edgeEta_BIF j.1 q| ≤ 1 / 400 := by
  obtain ⟨-, hΔ0, -⟩ := C.std
  have hone := S.edgeCutoff_eq_one_BAUGD hΔ0 j q hd hη ht
  have hF : S.edgeRatio_BAUGD j (S.boundaryOriginalMap q.val) = S.edgeEta_BIF j.1 q := by
    rw [S.edgeRatio_boundaryOriginalMap_BAUGD, hone, one_mul, S.edgeEta_eq_coord_BAUGP2 j q]
  have hζ : 0 < S.markerCutoffW_BAUGD (Sum.inr (Sum.inr j)) q.val := by
    change 0 < S.edgeCutoffW_BAUGP2 j q.val
    rw [hone]
    exact one_pos
  have herr : ‖C.toChain.E q.val - S.boundaryOriginalMap q.val‖ ≤ S.rho j.1 / 400 :=
    C.final_err_le_BBP (Sum.inr (Sum.inr j)) hζ
  have h := S.abs_edgeRatio_le_BAUGD j (C.toChain.E q.val - S.boundaryOriginalMap q.val)
  rw [map_sub, hF] at h
  have hrj := S.rho_pos j.1
  calc _ ≤ ‖C.toChain.E q.val - S.boundaryOriginalMap q.val‖ / S.rho j.1 := h
    _ ≤ S.rho j.1 / 400 / S.rho j.1 := div_le_div_of_nonneg_right herr hrj.le
    _ = 1 / 400 := by field_simp

include C in
/-- **EDP04's whole time trace on `W°`** (see the module docstring). -/
theorem edge_trace_OWF (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (j : S.EdgeIdx_BAUGD) {a θ δ : ℝ} (ha : |a| < 81 / 20 * Δ) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ Δ / 10) {q : W.pieceInterior ⊤} (hq : q ∈ S.edgeSource_OWF j)
    (hfib : (1 - θ) * S.edgeEta_BIF j.1 q +
      θ * (S.edgeRatio_BAUGD j (C.toChain.E q.val) - a) = 0)
    (hH : (1 - θ) * S.edgeH0_OWF q + θ * (C.toChain.heightRatio q.val - δ) ≤ 4 * Δ) :
    |S.edgeEta_BIF j.1 q| < 41 / 10 * Δ ∧ S.edgeHeightRaw q < 21 / 5 * Δ ∧
      ((1 - θ) * S.edgeH0_OWF q + θ * (C.toChain.heightRatio q.val - δ) = 4 * Δ →
        19 / 5 * Δ < S.edgeHeightRaw q ∧ S.edgeHeightRaw q < 21 / 5 * Δ) := by
  obtain ⟨-, hΔ0, -, -, -, -, -, -, -, hΔ1, -, -⟩ := C.std
  obtain ⟨hd, hη5, ht5⟩ := hq
  have hη8 : |S.edgeEta_BIF j.1 q| < 8 * Δ := by linarith
  obtain ⟨hlow, hhigh⟩ := C.edge_height_band_OWF hc hC j hd hη8 (by linarith)
  have hgη := C.edge_value_close_OWF j hd hη8 (by linarith)
  have hH2 : S.edgeHeightRaw q ≤ 2 * Δ → S.edgeH0_OWF q ≤ 2 * Δ := fun h2 =>
    edgeRowHeight_le_two_EDP3 (F := S.edgeSmoothing_BAUGD) (ρ := fun x => S.rho x.val) hΔ0 h2
  have hHt : 2 * Δ ≤ S.edgeHeightRaw q → S.edgeH0_OWF q = S.edgeHeightRaw q := fun h2 =>
    edgeRowHeight_eq_self_EDP3 (F := S.edgeSmoothing_BAUGD) (ρ := fun x => S.rho x.val) hΔ0 h2
  exact edge_trace_numbers_OWF hΔ1 hθ hδ0 hδ hgη ha hlow hhigh hH2 hHt hfib hH

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
