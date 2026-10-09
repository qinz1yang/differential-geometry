import DifferentialGeometry.Geometry.Metric.ChartDistanceComparison
import DifferentialGeometry.Geometry.Metric.EuclideanChart
import DifferentialGeometry.Analysis.Calculus.DistanceSmoothing.SeminormMollification

/-!
# Local Lipschitz smoothing up to the boundary (foundation F-d, local part)

Every statement here holds on an arbitrary smooth manifold with corners (no `Boundaryless`, no
metric-space instance, no connectedness); distances are the extended `g`-length distance
`riemannianEDistOf g`.

* `exists_open_chart_euclidean_comparison`: near `b`, the chart `φ = extChartAt I b` followed by
  the linear isometry `A = metricChartEuclideanEquiv g b` onto `EuclideanSpace` is a
  `κ`-bi-Lipschitz map for the `g`-distance (from the two-sided chart comparison
  `exists_open_riemannianEDistOf_comparison`).
* `exists_nhds_lipschitz_of_contMDiff` (F-d.1): a `C¹` function is Lipschitz near every point;
  `exists_uniform_local_lipschitz_of_contMDiff`: on a compact manifold one constant serves near
  every point.
* `exists_local_lipschitz_approximation_of_corners` (F-d.2): a `K`-Lipschitz function is, near every
  point, uniformly approximable by smooth `K κ²`-Lipschitz functions. The proof extends
  `f ∘ (A ∘ φ)⁻¹` from the chart image to the whole Euclidean space by McShane's extension (this
  replaces the half-chart reflection of the blueprint and works for every model with corners) and
  mollifies.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Analysis.Calculus
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Collapse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Near `b`, the chart at `b` followed by the `g_b`-orthonormal identification
`metricChartEuclideanEquiv g b` is `κ`-bi-Lipschitz for the `g`-distance (corners allowed). -/
theorem exists_open_chart_euclidean_comparison [RegularSpace M]
    (g : SmoothRiemannianMetric I M) (b : M) {κ : ℝ} (hκ : 1 < κ) :
    ∃ U : Set M, IsOpen U ∧ b ∈ U ∧ U ⊆ (chartAt H b).source ∧ ∀ x ∈ U, ∀ y ∈ U,
      ENNReal.ofReal ‖metricChartEuclideanEquiv g b (extChartAt I b y) -
          metricChartEuclideanEquiv g b (extChartAt I b x)‖ ≤
        ENNReal.ofReal κ * riemannianEDistOf g x y ∧
      riemannianEDistOf g x y ≤ ENNReal.ofReal κ *
        ENNReal.ofReal ‖metricChartEuclideanEquiv g b (extChartAt I b y) -
          metricChartEuclideanEquiv g b (extChartAt I b x)‖ := by
  obtain ⟨U, hbU, hUs, hcmp⟩ := exists_open_riemannianEDistOf_comparison g b hκ
  refine ⟨U, U.isOpen, hbU, hUs, fun x hx y hy => ?_⟩
  have h := hcmp x hx y hy
  dsimp only at h
  rw [← map_sub, metricChartEuclideanEquiv_norm]
  exact h

/-- F-d.1: a `C¹` function is Lipschitz for the `g`-distance near every point (corners allowed). -/
theorem exists_nhds_lipschitz_of_contMDiff [RegularSpace M] (g : SmoothRiemannianMetric I M)
    {ψ : M → ℝ} (hψ : ContMDiff I 𝓘(ℝ, ℝ) 1 ψ) (b : M) :
    ∃ C : ℝ≥0, ∃ V ∈ 𝓝 b, ∀ x ∈ V, ∀ y ∈ V,
      ENNReal.ofReal |ψ x - ψ y| ≤ C * riemannianEDistOf g x y := by
  obtain ⟨U, hUo, hbU, hUs, hcmp⟩ := exists_open_chart_euclidean_comparison g b one_lt_two
  set φ := extChartAt I b with hφ
  set A := metricChartEuclideanEquiv g b with hA
  have hk : ContDiffWithinAt ℝ 1 (ψ ∘ φ.symm) (range I) (φ b) := by
    have h := (contMDiffAt_iff.mp (hψ b)).2
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] using h
  obtain ⟨L, t, ht, hlip⟩ := hk.exists_lipschitzOnWith I.convex_range
  set B : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E := A.symm.toContinuousLinearMap
    with hB
  set c : ℝ := L * ‖B‖ with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨Real.toNNReal (c * 2), φ ⁻¹' t ∩ U,
    inter_mem (extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (mem_extChartAt_source b) ht)
      (hUo.mem_nhds hbU), ?_⟩
  rintro x ⟨hxt, hxU⟩ y ⟨hyt, hyU⟩
  have hxs : x ∈ φ.source := by rw [hφ, extChartAt_source]; exact hUs hxU
  have hys : y ∈ φ.source := by rw [hφ, extChartAt_source]; exact hUs hyU
  have hreal : |ψ x - ψ y| ≤ c * ‖A (φ y) - A (φ x)‖ := by
    have h1 := hlip.dist_le_mul (φ x) hxt (φ y) hyt
    simp only [Function.comp_apply, φ.left_inv hxs, φ.left_inv hys,
      dist_eq_norm] at h1
    have h2 : ‖φ x - φ y‖ ≤ ‖B‖ * ‖A (φ y) - A (φ x)‖ := by
      have h3 : φ x - φ y = B (A (φ x) - A (φ y)) := by
        simp [hB]
      rw [h3, norm_sub_rev (A (φ y))]
      exact ContinuousLinearMap.le_opNorm _ _
    calc |ψ x - ψ y| ≤ L * ‖φ x - φ y‖ := h1
      _ ≤ L * (‖B‖ * ‖A (φ y) - A (φ x)‖) :=
          mul_le_mul_of_nonneg_left h2 L.coe_nonneg
      _ = c * ‖A (φ y) - A (φ x)‖ := by rw [hc]; ring
  have hd := (hcmp x hxU y hyU).1
  calc ENNReal.ofReal |ψ x - ψ y| ≤ ENNReal.ofReal (c * ‖A (φ y) - A (φ x)‖) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal c * ENNReal.ofReal ‖A (φ y) - A (φ x)‖ := ENNReal.ofReal_mul hc0
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal 2 * riemannianEDistOf g x y) := by gcongr
    _ = ENNReal.ofReal (c * 2) * riemannianEDistOf g x y := by
        rw [ENNReal.ofReal_mul hc0, mul_assoc]
    _ = (Real.toNNReal (c * 2) : ℝ≥0∞) * riemannianEDistOf g x y := rfl

/-- On a compact manifold (corners allowed) a `C¹` function has one constant `C` such that every
point has a neighbourhood on which the function is `C`-Lipschitz for the `g`-distance. -/
theorem exists_uniform_local_lipschitz_of_contMDiff [RegularSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {ψ : M → ℝ} (hψ : ContMDiff I 𝓘(ℝ, ℝ) 1 ψ) :
    ∃ C : ℝ≥0, ∀ b : M, ∃ V ∈ 𝓝 b, ∀ x ∈ V, ∀ y ∈ V,
      ENNReal.ofReal |ψ x - ψ y| ≤ C * riemannianEDistOf g x y := by
  classical
  choose C V hV hlip using exists_nhds_lipschitz_of_contMDiff g hψ
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun b => interior (V b))
    (fun b _ => interior_mem_nhds.mpr (hV b))
  refine ⟨∑ b ∈ t, C b, fun x => ?_⟩
  obtain ⟨b, hbt, hxb⟩ := mem_iUnion₂.mp (ht.2 (mem_univ x))
  refine ⟨interior (V b), isOpen_interior.mem_nhds hxb, fun y hy z hz => ?_⟩
  refine (hlip b y (interior_subset hy) z (interior_subset hz)).trans ?_
  have hCb : (C b : ℝ≥0∞) ≤ ((∑ b ∈ t, C b : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast Finset.single_le_sum (f := C) (fun _ _ => bot_le) hbt
  exact mul_le_mul_left hCb _

/-- F-d.2: a `K`-Lipschitz function (for the `g`-distance) is, near every point `b` of a manifold
with corners, uniformly approximable by functions smooth near `b` and `K κ²`-Lipschitz there. The
neighbourhood does not depend on the approximation error. -/
theorem exists_local_lipschitz_approximation_of_corners [RegularSpace M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {K : ℝ≥0}
    (hf : ∀ x y, ENNReal.ofReal |f x - f y| ≤ K * riemannianEDistOf g x y)
    {κ : ℝ} (hκ : 1 < κ) (b : M) :
    ∃ V : Set M, IsOpen V ∧ b ∈ V ∧ ∀ η > 0, ∃ f' : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f' V ∧ (∀ x ∈ V, |f' x - f x| ≤ η) ∧
      ∀ x ∈ V, ∀ y ∈ V,
        ENNReal.ofReal |f' x - f' y| ≤ ENNReal.ofReal (K * κ ^ 2) * riemannianEDistOf g x y := by
  obtain ⟨U, hUo, hbU, hUs, hcmp⟩ := exists_open_chart_euclidean_comparison g b hκ
  set φ := extChartAt I b with hφ
  set A := metricChartEuclideanEquiv g b with hA
  have hκ0 : 0 < κ := zero_lt_one.trans hκ
  set a : ℝ := (K : ℝ) * κ with ha
  have ha0 : 0 ≤ a := by positivity
  let h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := fun z => f (φ.symm (A.symm z))
  have hhΨ : ∀ x ∈ U, h (A (φ x)) = f x := by
    intro x hx
    have hxs : x ∈ φ.source := by rw [hφ, extChartAt_source]; exact hUs hx
    simp only [h, ContinuousLinearEquiv.symm_apply_apply, φ.left_inv hxs]
  have hlipS : LipschitzOnWith (Real.toNNReal a) h ((fun x => A (φ x)) '' U) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hhΨ x hx, hhΨ y hy, Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ ha0,
      norm_sub_rev]
    have h1 := hf x y
    have h2 := (hcmp x hx y hy).2
    have h3 : ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal (a * ‖A (φ y) - A (φ x)‖) := by
      calc ENNReal.ofReal |f x - f y| ≤ K * riemannianEDistOf g x y := h1
        _ ≤ K * (ENNReal.ofReal κ * ENNReal.ofReal ‖A (φ y) - A (φ x)‖) := by gcongr
        _ = ENNReal.ofReal (a * ‖A (φ y) - A (φ x)‖) := by
            rw [ha, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul K.coe_nonneg,
              ENNReal.ofReal_coe_nnreal, mul_assoc]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
  obtain ⟨G, hGlip, hGeq⟩ := hlipS.extend_real
  have hG : ∀ y ∈ (univ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))), ∀ y' ∈ univ,
      |G y - G y'| ≤ a * normSeminorm ℝ _ (y - y') := by
    intro y _ y' _
    have := hGlip.dist_le_mul y y'
    rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ ha0] at this
  refine ⟨U, hUo, hbU, fun η hη => ?_⟩
  set r : ℝ := η / (a + 1) with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨h', hsmooth, hl, hv⟩ := exists_contDiff_seminorm_lipschitz_approx
    (normSeminorm ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) (C := 1)
    (fun v => by simp) ha0 hG hr0 (δ := r) (fun z hz => by simpa using hz)
  have har : a * r ≤ η := by
    rw [hr, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨fun x => h' (A (φ x)), ?_, ?_, ?_⟩
  · have hs : ContDiff ℝ ∞ (fun y : E => h' (A y)) := hsmooth.comp A.contDiff
    exact hs.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt.mono hUs)
  · intro x hx
    have h1 := hv (A (φ x)) (subset_univ _)
    have hGx : G (A (φ x)) = f x := (hGeq ⟨x, hx, rfl⟩).symm.trans (hhΨ x hx)
    rw [hGx] at h1
    exact h1.trans har
  · intro x hx y hy
    have h1 := hl (A (φ x)) (A (φ y)) (subset_univ _) (subset_univ _)
    rw [coe_normSeminorm, norm_sub_rev] at h1
    have h2 := (hcmp x hx y hy).1
    calc ENNReal.ofReal |h' (A (φ x)) - h' (A (φ y))|
        ≤ ENNReal.ofReal (a * ‖A (φ y) - A (φ x)‖) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal a * ENNReal.ofReal ‖A (φ y) - A (φ x)‖ := ENNReal.ofReal_mul ha0
      _ ≤ ENNReal.ofReal a * (ENNReal.ofReal κ * riemannianEDistOf g x y) := by gcongr
      _ = ENNReal.ofReal ((K : ℝ) * κ ^ 2) * riemannianEDistOf g x y := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul ha0, ha]
          congr 2
          ring

end DifferentialGeometry.Geometry.Collapse
