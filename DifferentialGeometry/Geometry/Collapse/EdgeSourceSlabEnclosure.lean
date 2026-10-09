import DifferentialGeometry.Geometry.Collapse.EdgeSourceHeights
import DifferentialGeometry.Geometry.Metric.Approximation.CoarseBorderDistance
import DifferentialGeometry.Geometry.Metric.Approximation.CoarseBorderEnclosure

/-!
# LFR28 B5: the whole source slab lies in the model image, and is proper

Blueprint 207A, LFR28 (A:27223), proof step 3 ("Strict-radius coverage now puts the entire source
slab in `j_i(B_N(p, 6.1Δ))`. Its preimage has `|t| < 4.01Δ` ... and `r < 4.02Δ` ... Thus it is in
`U`") and the properness sentence of step 4 ("proper by the compact closed slab").

* `eventually_edgeSourceSlab_mem_image` (**B5, enclosure**): on every late index, every source point
  `y ∈ B(p_i, 100Δ)` with `|f_i y| ≤ 4Δ` and `η_i y = F_i y/ρ_i y ≤ 4Δ` is `j_i x` for a model point
  `x ∈ B(q, 6.5Δ)` with `|t(x)| < 5Δ` and `r(x) < 5Δ` — inside LFR24's cylinder. Inputs: (LFR28.6)
  `coarseBorder_source_slab_subset_ball`, the EXACT strict-radius coverage of the L-CONS merge
  (lane LFR28-B12), the axis convergence of the first chart coordinate, (LFR28.2)
  `eventually_abs_height_sub_axisDist_le` and (LFR25.2) `coarseBorder_abs_infDist_sub_height_le`.
* `isCompact_slab_preimage_of_subset_compact` (**B5, properness**): if the slab
  `{|f| < β, H ≤ e}` of an open `O` lies in a compact `C ⊆ O` on which `f, H` are continuous, its
  part over every compact `K ⊆ (-β, β)` is compact in `O`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped NNReal

namespace DifferentialGeometry.Geometry.Collapse

open GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian.Geodesic

/-- **LFR28 B5 (enclosure).** On every late index every point of the source slab
`{y ∈ B(p_i, 100Δ) : |f_i y| ≤ 4Δ, F_i y/ρ_i y ≤ 4Δ}` is the image `j_i x` of a model point with
`d(x, q) < 6.5Δ`, `|t(x)| < 5Δ` and `r(x) < 5Δ`. -/
theorem eventually_edgeSourceSlab_mem_image
    {N : Type*} [MetricSpace N] {M : ℕ → Type*} [∀ i, MetricSpace (M i)]
    {W : Type*} [MetricSpace W] (j : ∀ i, N → M i) (q : N)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcovx : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop, ball (j i q) a ⊆ j i '' ball q b)
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {z₀ : W} (hΦq : Φ q = WithLp.toLp 2 ((0 : ℝ), z₀))
    {Δ μ τ h l : ℝ} {Λ : ℝ≥0} (hΔ : 0 < Δ) (hμ1 : μ ≤ 1 / 1000) (hτ : 0 ≤ τ)
    (hτ1 : τ ≤ 1 / 10000) (hl1 : l ≤ 1 / 1000) (hh : 20 * Real.sqrt τ < h)
    (hh1 : h ≤ 1 / 10) (hΛ : 100 * Δ * (Λ : ℝ) ≤ l)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (A : ∀ i, Set (M i)) (F f ρ : ∀ i, M i → ℝ)
    (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ),
      ∀ y ∈ ball (j i q) (200 * Δ), |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hcoord : TendstoUniformlyOn (fun i x => (Q i (j i x)).fst)
      (fun x => (Φ x).fst) atTop (closedBall q (100 * Δ)))
    (hpA : ∀ i, j i q ∈ A i)
    (hborder : ∀ i, ∀ a ∈ A i ∩ ball (j i q) (190 * Δ), (Q i a).snd ≤ τ * Δ)
    (hbordercover : ∀ i, ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A i ∩ ball (j i q) (190 * Δ),
        dist (Q i a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hF : ∀ i x, |F i x - infDist x (A i)| ≤ μ * Δ)
    (hf : ∀ i, ∀ x ∈ ball (j i q) (100 * Δ), |f i x - (Q i x).fst| ≤ μ * Δ)
    (hρ : ∀ i, LipschitzWith Λ (ρ i)) (hρp : ∀ i, ρ i (j i q) = 1) :
    ∀ᶠ i in atTop, ∀ y ∈ ball (j i q) (100 * Δ), |f i y| ≤ 4 * Δ → F i y / ρ i y ≤ 4 * Δ →
      ∃ x ∈ ball q (13 / 2 * Δ), j i x = y ∧ |(Φ x).fst| < 5 * Δ ∧
        dist (Φ x).snd z₀ < 5 * Δ := by
  have hτ1' : τ ≤ 1 := by linarith
  have hheightTail := eventually_abs_height_sub_axisDist_le j q hdist Φ hΦq hΔ hτ hτ1' Q hQp
    hQdist hheight hcoord h hh
  filter_upwards [hcovx (6 * Δ) (13 / 2 * Δ) (by positivity) (by linarith), hheightTail,
    Metric.tendstoUniformlyOn_iff.mp hcoord (Δ / 1000) (by positivity)] with i hci hhi hco
  intro y hy hfy hηy
  -- the scale is close to one on the ball
  have hρy : ∀ x ∈ ball (j i q) (100 * Δ), 0 < ρ i x ∧ ρ i x ≤ 1 + l := by
    intro x hx
    have h1 := (hρ i).dist_le_mul x (j i q)
    rw [Real.dist_eq, hρp i] at h1
    have hx' : dist x (j i q) < 100 * Δ := hx
    have h2 : (Λ : ℝ) * dist x (j i q) ≤ Λ * (100 * Δ) :=
      mul_le_mul_of_nonneg_left hx'.le Λ.coe_nonneg
    have h3 : (Λ : ℝ) * (100 * Δ) = 100 * Δ * Λ := by ring
    have h4 := abs_le.mp (h1.trans (h2.trans (h3.le.trans hΛ)))
    constructor <;> linarith [h4.1, h4.2]
  -- (LFR28.6): the slab point is within `6Δ` of the base point
  have hy6 : dist y (j i q) < 6 * Δ :=
    coarseBorder_source_slab_subset_ball hΔ hτ1 (by linarith) (by linarith) (hQp i) (hQdist i)
      (hheight i) (hpA i) (hborder i) (hf i) (fun x _ => hF i x) (hρy) hy hfy hηy
  -- exact strict-radius coverage
  obtain ⟨x, hx, hxy⟩ := hci (mem_ball.mpr hy6)
  subst hxy
  have hxq : dist x q < 13 / 2 * Δ := hx
  have hx100 : x ∈ ball q (100 * Δ) := mem_ball.mpr (by linarith)
  refine ⟨x, hx, rfl, ?_, ?_⟩
  · -- the time coordinate
    have hc := hco x (mem_closedBall.mpr (by linarith))
    rw [Real.dist_eq] at hc
    have h1 := abs_le.mp (hf i (j i x) hy)
    have h2 := abs_le.mp hfy
    have hμΔ : μ * Δ ≤ Δ / 1000 := by nlinarith
    have h3 := abs_lt.mp hc
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  · -- the radius
    have hht := abs_le.mp (hhi x hx100)
    have hy70 : j i x ∈ ball (j i q) (70 * Δ) := mem_ball.mpr (by linarith)
    have hdb := abs_le.mp (coarseBorder_abs_infDist_sub_height_le hΔ hτ1' (hQp i) (hQdist i)
      (hheight i) (hpA i) (hborder i) (hbordercover i) hy70)
    obtain ⟨hρ0, hρ1⟩ := hρy (j i x) hy
    have hFy : F i (j i x) ≤ 4 * Δ * (1 + l) := by
      rw [div_le_iff₀ hρ0] at hηy
      nlinarith
    have hFA := abs_le.mp (hF i (j i x))
    have hμΔ : μ * Δ ≤ Δ / 1000 := by nlinarith
    have hτΔ : τ * Δ ≤ Δ / 10000 := by nlinarith
    have hhΔ : h * Δ ≤ Δ / 10 := by nlinarith
    have hlΔ : 4 * Δ * l ≤ 4 * Δ / 1000 := by nlinarith
    nlinarith

/-- **LFR28 B5 (properness).** If the slab `{|f| < β, H ≤ e}` of an open `O` lies in a compact
`C ⊆ O` on which `f` and `H` are continuous, then its part over every compact `K ⊆ (-β, β)` is
compact in `O`. -/
theorem isCompact_slab_preimage_of_subset_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    {O : TopologicalSpace.Opens X} {C : Set X} (hC : IsCompact C) (hCO : C ⊆ O)
    {f H : X → ℝ} (hf : ContinuousOn f C) (hH : ContinuousOn H C) {β e : ℝ}
    (hsub : ∀ y ∈ O, |f y| < β → H y ≤ e → y ∈ C) :
    ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-β) β →
      IsCompact ((fun y : O => f y) ⁻¹' K ∩ {y : O | 0 ≤ e - H y}) := by
  intro K hK hKβ
  have h1 : IsClosed (C ∩ f ⁻¹' K) := hf.preimage_isClosed_of_isClosed hC.isClosed hK.isClosed
  have h2 : IsClosed ((C ∩ f ⁻¹' K) ∩ H ⁻¹' Iic e) :=
    (hH.mono inter_subset_left).preimage_isClosed_of_isClosed h1 isClosed_Iic
  have hT : IsCompact ((C ∩ f ⁻¹' K) ∩ H ⁻¹' Iic e) :=
    hC.of_isClosed_subset h2 (fun y hy => hy.1.1)
  rw [Subtype.isCompact_iff]
  convert hT using 1
  ext y
  constructor
  · rintro ⟨y', ⟨hyK, hyH⟩, rfl⟩
    have hβ := hKβ hyK
    refine ⟨⟨hsub y' y'.2 (abs_lt.mpr ⟨hβ.1, hβ.2⟩) (by linarith [show 0 ≤ e - H y' from hyH]),
      hyK⟩, ?_⟩
    change H y' ≤ e
    linarith [show 0 ≤ e - H y' from hyH]
  · rintro ⟨⟨hyC, hyK⟩, hyH⟩
    refine ⟨⟨y, hCO hyC⟩, ⟨hyK, ?_⟩, rfl⟩
    change 0 ≤ e - H y
    have : H y ≤ e := hyH
    linarith

end DifferentialGeometry.Geometry.Collapse
