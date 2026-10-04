import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Assembly

/-!
# Smoothing of Lipschitz functions on Riemannian manifolds (KL Cor. 3.15 type; LC28, tier T2)

* `exists_local_lipschitz_approximation`: near every point a `K`-Lipschitz function is
  approximated, uniformly to any accuracy, by functions smooth on a fixed neighbourhood that are
  `K κ²`-Lipschitz there (`κ > 1` arbitrary); chartwise mollification plus the two chart
  comparisons.
* `exists_localized_lipschitz_smoothing`: for `U` open and `C ⊆ U` compact, a `K`-Lipschitz `f`
  has, for all `e, ε > 0`, an `F` smooth near `C`, `e`-close to `f`, equal to `f` off `U`, and
  `(K + ε)`-Lipschitz.
* `exists_contMDiff_lipschitz_approx`: the closed-manifold form requested by lane W3-F1 (LC02's
  smooth tier), in the aligned-metric instance block: a `K`-Lipschitz `f` has, for every `η > 0`, a
  globally smooth `ρ` with `|ρ - f| < η` and `Lip ρ ≤ K + η`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

section RiemannianBlock

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- Local chartwise smoothing of a Lipschitz function. -/
theorem exists_local_lipschitz_approximation (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {f : M → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {κ : ℝ}
    (hκ : 1 < κ) {U : Set M} (hU : IsOpen U) {b : M} (hb : b ∈ U) :
    ∃ W : Set M, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ η > 0, ∃ f' : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f' W ∧ (∀ x ∈ W, |f' x - f x| ≤ η) ∧
        (∀ x ∈ W, ∀ x' ∈ W,
          |(f' x - f x) - (f' x' - f x')| ≤ (K * κ ^ 2 + K) * dist x x') ∧
        (∀ x ∈ W, ∀ x' ∈ W, |f' x - f' x'| ≤ K * κ ^ 2 * dist x x') := by
  have : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  have hκpos : 0 < κ := lt_trans zero_lt_one hκ
  set N := metricSeminormAt g b with hN
  set φ := extChartAt I b with hφ
  obtain ⟨ρ₀, hρ₀, hρ₀t, hinv⟩ := exists_ball_dist_chart_symm_le g hEnorm b hκ
  obtain ⟨r₁, hr₁, hr₁src, hchart⟩ := exists_ball_metricSeminormAt_chart_sub_le g hEnorm b hκ
  set B : Set E := Metric.ball (φ b) ρ₀ with hB
  set a : ℝ := K * κ with ha
  have ha0 : 0 ≤ a := mul_nonneg K.coe_nonneg hκpos.le
  let h : E → ℝ := fun y => f (φ.symm y)
  have hlip : ∀ y ∈ B, ∀ y' ∈ B, |h y - h y'| ≤ a * N (y - y') := by
    intro y hy y' hy'
    have h1 : |f (φ.symm y) - f (φ.symm y')| ≤ K * dist (φ.symm y) (φ.symm y') := by
      rw [← Real.dist_eq]; exact hf.dist_le_mul _ _
    calc |h y - h y'| ≤ K * dist (φ.symm y) (φ.symm y') := h1
      _ ≤ K * (κ * N (y - y')) := mul_le_mul_of_nonneg_left (hinv y hy y' hy') K.coe_nonneg
      _ = a * N (y - y') := by rw [ha]; ring
  refine ⟨(chartAt H b).source ∩ φ ⁻¹' Metric.ball (φ b) (ρ₀ / 2) ∩ Metric.ball b r₁ ∩ U,
    (((isOpen_extChartAt_preimage b Metric.isOpen_ball).inter Metric.isOpen_ball).inter hU),
    ⟨⟨⟨mem_chart_source H b, Metric.mem_ball_self (by positivity)⟩, Metric.mem_ball_self hr₁⟩,
      hb⟩, inter_subset_right, ?_, ?_⟩
  · exact (isCompact_closedBall b r₁).of_isClosed_subset isClosed_closure
      ((closure_mono (inter_subset_left.trans inter_subset_right)).trans
        Metric.closure_ball_subset_closedBall)
  · intro η hη
    set C : ℝ := Real.sqrt ‖metricFormAt g b‖ with hC
    have hC0 : 0 ≤ C := Real.sqrt_nonneg _
    set r : ℝ := min (ρ₀ / 2) (η / (a * C + 1)) with hr
    have hrpos : 0 < r := lt_min (by positivity) (by positivity)
    have hδ : ∀ z : E, ‖z‖ ≤ r → N z ≤ C * r := fun z hz =>
      (metricSeminormAt_le_mul_norm g b z).trans (mul_le_mul_of_nonneg_left hz hC0)
    obtain ⟨h', hsmooth, hl, hv⟩ := exists_contDiff_seminorm_lipschitz_approx N
      (metricSeminormAt_le_mul_norm g b) ha0 hlip hrpos hδ
    have haδ : a * (C * r) ≤ η := by
      have hr2 : r ≤ η / (a * C + 1) := min_le_right _ _
      have h1 : a * C * r ≤ a * C * (η / (a * C + 1)) :=
        mul_le_mul_of_nonneg_left hr2 (by positivity)
      have h2 : a * C * (η / (a * C + 1)) ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      nlinarith
    have hsub : ∀ x ∈ (chartAt H b).source ∩ φ ⁻¹' Metric.ball (φ b) (ρ₀ / 2) ∩
        Metric.ball b r₁ ∩ U, Metric.closedBall (φ x) r ⊆ B := by
      intro x hx y hy
      rw [Metric.mem_closedBall] at hy
      have h1 : dist (φ x) (φ b) < ρ₀ / 2 := hx.1.1.2
      have h2 : r ≤ ρ₀ / 2 := min_le_left _ _
      rw [hB, Metric.mem_ball]
      linarith [dist_triangle y (φ x) (φ b)]
    have hhx : ∀ x ∈ (chartAt H b).source, h (φ x) = f x := by
      intro x hx
      have hxs : x ∈ φ.source := by rw [hφ, extChartAt_source]; exact hx
      simp only [h, φ.left_inv hxs]
    refine ⟨fun x => h' (φ x), ?_, ?_, ?_, ?_⟩
    · exact hsmooth.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt.mono
        (fun x hx => hx.1.1.1))
    · intro x hx
      have := hv (φ x) (hsub x hx)
      rw [hhx x hx.1.1.1] at this
      exact this.trans haδ
    · intro x hx x' hx'
      have h1 := hl (φ x) (φ x') (hsub x hx) (hsub x' hx')
      have h3 := hchart x' hx'.1.2 x hx.1.2
      rw [dist_comm x' x] at h3
      have hf' : |f x - f x'| ≤ K * dist x x' := by
        rw [← Real.dist_eq]; exact hf.dist_le_mul x x'
      have h4 : |h' (φ x) - h' (φ x')| ≤ K * κ ^ 2 * dist x x' := by
        calc |h' (φ x) - h' (φ x')| ≤ a * N (φ x - φ x') := h1
          _ ≤ a * (κ * dist x x') := mul_le_mul_of_nonneg_left h3 ha0
          _ = K * κ ^ 2 * dist x x' := by rw [ha]; ring
      calc |(h' (φ x) - f x) - (h' (φ x') - f x')|
          = |(h' (φ x) - h' (φ x')) - (f x - f x')| := by ring_nf
        _ ≤ |h' (φ x) - h' (φ x')| + |f x - f x'| := abs_sub _ _
        _ ≤ K * κ ^ 2 * dist x x' + K * dist x x' := add_le_add h4 hf'
        _ = (K * κ ^ 2 + K) * dist x x' := by ring
    · intro x hx x' hx'
      have h1 := hl (φ x) (φ x') (hsub x hx) (hsub x' hx')
      have h3 := hchart x' hx'.1.2 x hx.1.2
      rw [dist_comm x' x] at h3
      calc |h' (φ x) - h' (φ x')| ≤ a * N (φ x - φ x') := h1
        _ ≤ a * (κ * dist x x') := mul_le_mul_of_nonneg_left h3 ha0
        _ = K * κ ^ 2 * dist x x' := by rw [ha]; ring

/-- Localized smoothing of a `K`-Lipschitz function with Lipschitz constant `K + ε`. -/
theorem exists_localized_lipschitz_smoothing (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {f : M → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {U C : Set M} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U) {e ε : ℝ} (he : 0 < e)
    (hε : 0 < ε) :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, |F x - f x| < e) ∧ (∀ x, x ∉ U → F x = f x) ∧
      ∀ x y, |F x - F y| ≤ (K + ε) * dist x y := by
  set κ : ℝ := Real.sqrt (1 + ε / (2 * (K + 1))) with hκdef
  have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
  have hq : 0 < ε / (2 * (K + 1)) := by positivity
  have hκ2 : κ ^ 2 = 1 + ε / (2 * (K + 1)) := Real.sq_sqrt (by positivity)
  have hκ : 1 < κ := by
    rw [hκdef, Real.lt_sqrt zero_le_one]; linarith
  have hKκ : (K : ℝ) * κ ^ 2 ≤ K + ε / 2 := by
    rw [hκ2, mul_add, mul_one]
    have : (K : ℝ) * (ε / (2 * (K + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  obtain ⟨F, O, hO, hCO, hFO, hclose, hout, -, hlipF⟩ :=
    exists_smoothing_of_local_approximations g hEnorm hf hU hC hCU
      (Ld := K * κ ^ 2 + K) (La := K * κ ^ 2) (by positivity)
      (fun b hb => exists_local_lipschitz_approximation g hEnorm hf hκ hU hb) he
      (half_pos hε)
  refine ⟨F, O, hO, hCO, hFO, hclose, hout, fun x y => (hlipF x y).trans ?_⟩
  have hmax : max (K : ℝ) (K * κ ^ 2) = K * κ ^ 2 := by
    apply max_eq_right
    have : (1 : ℝ) ≤ κ ^ 2 := by rw [hκ2]; linarith
    nlinarith
  rw [hmax]
  exact mul_le_mul_of_nonneg_right (by linarith) dist_nonneg

end RiemannianBlock

section Closed

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- Smoothing of Lipschitz functions on a closed Riemannian manifold (KL Cor. 3.15 type), in the
aligned-metric instance block: for every `η > 0` a `K`-Lipschitz `f` has a smooth `η`-close
approximation with Lipschitz constant `K + η`. -/
theorem exists_contMDiff_lipschitz_approx
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {f : M → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {η : ℝ} (hη : 0 < η) :
    ∃ ρ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ p, |ρ p - f p| < η) ∧
      LipschitzWith (K + ⟨η, hη.le⟩) ρ := by
  rcases eq_or_ne (Module.finrank ℝ E) 0 with hdim | hdim
  · -- zero-dimensional model: every function is smooth
    have : Subsingleton E := Module.finrank_zero_iff.mp hdim
    refine ⟨f, ?_, fun p => by simpa using hη, ?_⟩
    · rw [contMDiff_iff]
      refine ⟨hf.continuous, fun x y => ?_⟩
      exact (contDiff_const (c := (extChartAt 𝓘(ℝ, ℝ) y ∘ f ∘ (extChartAt I x).symm)
        (0 : E))).contDiffOn.congr fun z _ => by rw [Subsingleton.elim z 0]
    · exact hf.weaken le_self_add
  have : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  have : IsRiemannianManifold I M := by
    constructor
    intro a b
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]
  have hEnorm : IsMetricNorm (I := I) g := isMetricNorm_of_riemannianBundle g
  have : CompleteSpace M := complete_of_compact
  obtain ⟨F, O, hO, hCO, hFO, hclose, -, hlip⟩ :=
    exists_localized_lipschitz_smoothing g hEnorm hf isOpen_univ isCompact_univ
      (subset_refl _) hη hη
  refine ⟨F, ?_, hclose, ?_⟩
  · have hOu : O = univ := eq_univ_of_univ_subset hCO
    rw [hOu] at hFO
    exact contMDiffOn_univ.mp hFO
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hc : ((K + ⟨η, hη.le⟩ : ℝ≥0) : ℝ) = K + η := rfl
    rw [Real.dist_eq, hc]
    exact hlip x y

end Closed

end DifferentialGeometry.Geometry.Collapse
