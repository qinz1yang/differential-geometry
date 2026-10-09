import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacketComparison

/-!
# Consumers of the LC84 item 4 comparison

* `EdgeProductModel.dist_Θ_eq`: the model distance in product coordinates, `√(t² + d²)` (through
  the tree's `WithLp.prod_dist_sq_eq_add_sq`).
* `EdgeProductModel.completeSpace_S`, `EdgeProductModel.connectedSpace_S`: the factor `Z = S` is a
  COMPLETE connected surface (LC84 item 4: "`Z` a complete orientable nonnegative surface"; the
  orientation and `sec ≥ 0` are fields).
* `EdgeProductModel.dist_base_lt_of_slab`: the residual coordinate of the model: every point of the
  source slab is `j x` for a model point `x` within `8Δ` of the base point (`√(25 + 25) < 8`).
* `EdgeProductModel.dist_center_lt_of_slab` (207B FC12's "actual local product map and its residual
  coordinate, with the map distortion charged"): if the embedding is `δ`-close to an isometry on
  the buffer `B̄(Θ(0, s₀), R)` with `R ≥ 8Δ` (clause (iii) of
  `exists_edgeDiskPacket_comparison_threshold`), the whole source slab lies in `B(center, 8Δ + δ)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Metric WithLp Manifold
open scoped Topology ContDiff Manifold ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] EdgeProductModel.instMetricN EdgeProductModel.instChartedN
  EdgeProductModel.instManifoldN EdgeProductModel.instProperN EdgeProductModel.instConnectedN
  EdgeProductModel.instBundleN EdgeProductModel.instRiemannianN EdgeProductModel.instMetricS
  EdgeProductModel.instChartedS EdgeProductModel.instManifoldS EdgeProductModel.instBundleS
  EdgeProductModel.instRiemannianS

local instance nezero_finrank_euclidean_three_productModelApp_LFR28ROW2 :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

variable {M : Type*} [mM : MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M} {hEnorm : IsMetricNorm g}
  {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ} {c : EdgeChart g hEnorm Δ σ μ b γ β A ρ F} {K : ℕ}

namespace EdgeProductModel

/-- The model distance in product coordinates. -/
theorem dist_Θ_eq (Z : EdgeProductModel c K) (a b : ℝ × Z.S) :
    dist (Z.Θ a) (Z.Θ b) = Real.sqrt ((a.1 - b.1) ^ 2 + dist a.2 b.2 ^ 2) := by
  have h := WithLp.prod_dist_sq_eq_add_sq (toLp 2 a) (toLp 2 b)
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sq_abs] at h
  rw [Z.dist_Θ, ← h, Real.sqrt_sq dist_nonneg]

/-- **The factor is complete.** -/
theorem completeSpace_S (Z : EdgeProductModel c K) : CompleteSpace Z.S := by
  have hiso : Isometry (fun s : Z.S => Z.Θ ((0 : ℝ), s)) := by
    refine Isometry.of_dist_eq fun a b => ?_
    rw [Z.dist_Θ_eq]
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
    exact Real.sqrt_sq dist_nonneg
  have hrange : range (fun s : Z.S => Z.Θ ((0 : ℝ), s)) =
      Z.Θ '' ({(0 : ℝ)} ×ˢ (univ : Set Z.S)) := by
    ext x
    simp only [mem_range, mem_image, mem_prod, mem_singleton_iff, mem_univ, and_true]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨(0, s), rfl, rfl⟩
    · rintro ⟨⟨t, s⟩, ht, rfl⟩
      exact ⟨s, by simp only at ht; rw [ht]⟩
  have hclosed : IsClosed (range (fun s : Z.S => Z.Θ ((0 : ℝ), s))) := by
    rw [hrange]
    exact Z.Θ.toHomeomorph.isClosedMap _ (isClosed_singleton.prod isClosed_univ)
  exact (completeSpace_iff_isComplete_range hiso.isUniformInducing).mpr hclosed.isComplete

/-- **The factor is connected.** -/
theorem connectedSpace_S (Z : EdgeProductModel c K) : ConnectedSpace Z.S := by
  have hsurj : Function.Surjective (fun x : Z.N => (Z.Θ.symm x).2) := fun s =>
    ⟨Z.Θ (0, s), by simp only [Diffeomorph.symm_apply_apply]⟩
  exact hsurj.connectedSpace (continuous_snd.comp Z.Θ.symm.continuous)

/-- **The residual coordinate of the slab.** Every slab point is `j x` for a model point `x`
within `8Δ` of the base point. -/
theorem dist_base_lt_of_slab (Z : EdgeProductModel c K) (hΔ : 0 < Δ) {y : M}
    (hy : y ∈ ball c.center (100 * Δ)) (hf : |c.coord y| ≤ 4 * Δ)
    (hH : edgeRowHeight Δ F ρ y ≤ 4 * Δ) :
    ∃ x ∈ Z.j.source, Z.j x = y ∧ dist x (Z.Θ (0, Z.s₀)) < 8 * Δ := by
  obtain ⟨s, ht, hs, hsrc, hjs⟩ := Z.slab y hy hf hH
  refine ⟨Z.Θ s, hsrc, hjs, ?_⟩
  rw [Z.dist_Θ_eq, Real.sqrt_lt' (by positivity)]
  have h1 : (s.1 - 0) ^ 2 < (5 * Δ) ^ 2 := by
    rw [sub_zero, ← sq_abs]
    exact pow_lt_pow_left₀ ht (abs_nonneg _) (by norm_num)
  have h2 : dist s.2 Z.s₀ ^ 2 < (5 * Δ) ^ 2 := pow_lt_pow_left₀ hs dist_nonneg (by norm_num)
  nlinarith

/-- **FC12's residual control through the product map.** With the distortion clause of
`exists_edgeDiskPacket_comparison_threshold` on a buffer of radius `R ≥ 8Δ`, the whole source slab
lies in `B(center, 8Δ + δ)`. -/
theorem dist_center_lt_of_slab (Z : EdgeProductModel c K) (hΔ : 0 < Δ) {δ R : ℝ}
    (hR : 8 * Δ ≤ R)
    (hdist : ∀ x ∈ closedBall (Z.Θ (0, Z.s₀)) R, ∀ y ∈ closedBall (Z.Θ (0, Z.s₀)) R,
      |dist (Z.j x) (Z.j y) - dist x y| < δ) {y : M}
    (hy : y ∈ ball c.center (100 * Δ)) (hf : |c.coord y| ≤ 4 * Δ)
    (hH : edgeRowHeight Δ F ρ y ≤ 4 * Δ) :
    dist y c.center < 8 * Δ + δ := by
  obtain ⟨x, -, hjx, hx⟩ := Z.dist_base_lt_of_slab hΔ hy hf hH
  have hxR : x ∈ closedBall (Z.Θ (0, Z.s₀)) R := mem_closedBall.mpr (hx.le.trans hR)
  have hqR : Z.Θ (0, Z.s₀) ∈ closedBall (Z.Θ (0, Z.s₀)) R :=
    mem_closedBall_self ((by positivity : (0 : ℝ) ≤ 8 * Δ).trans hR)
  have h := hdist x hxR _ hqR
  rw [hjx, Z.j_base] at h
  have h' := (abs_lt.mp h).2
  linarith

end EdgeProductModel

end DifferentialGeometry.Geometry.Collapse
