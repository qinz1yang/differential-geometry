import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83StrainerKE_O8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83AlmostOrthonormal_O8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83OpenMin_O8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83BallMeasure_O8
import DifferentialGeometry.Topology.MetricSpace.DistanceCoordinates
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffVolume

/-!
# CH12-CX7, package P4: sharp strainer volume (SSV)

A paired packet of quality `δ` on `B(q, 2r)` in a complete Riemannian 3-manifold with
`sec ≥ -1` (on a buffer) has distance coordinates `f = distanceCoordinates 2 a` which are
`(1 + θ)`-Lipschitz on `B(q, s)` and satisfy `f(B(q, s)) ⊇ B(f q, (1 - 2θ) s)` for small `s`;
hence `𝓗³(B(q, s)) ≥ (1 - 9θ) ω₃ s³` (`strainer_volume_CX7`).
-/

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold Real Metric
open scoped Manifold ContDiff ENNReal NNReal InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Collapse

namespace GC.LongTime.Ch12

theorem euclidean_norm_three_CX7 (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ = Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

theorem norm_le_sqrt3_of_abs_le_CX7 (v : EuclideanSpace ℝ (Fin 3)) {m : ℝ}
    (h : ∀ j, |v j| ≤ m) : ‖v‖ ≤ Real.sqrt 3 * m := by
  have hm : 0 ≤ m := (abs_nonneg _).trans (h 0)
  rw [euclidean_norm_three_CX7]
  have h3 : Real.sqrt 3 * m = Real.sqrt (3 * m ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hm]
  rw [h3]
  apply Real.sqrt_le_sqrt
  have hj : ∀ j, v j ^ 2 ≤ m ^ 2 := fun j => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
  linarith [hj 0, hj 1, hj 2]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

section Packet

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g) (o : M)
  {R δ a₀ A₀ : ℝ} {W : Set M} {a b : Fin 3 → M}

/-- Minimizing unit directions toward the three `a j` from a point of `W`. -/
theorem exists_dirs_CX7
    (hbounds : ∀ z ∈ W, ∀ j, dist z (a j) ∈ Icc a₀ A₀ ∧ dist z (b j) ∈ Icc a₀ A₀)
    (ha₀ : 0 < a₀) {x : M} (hx : x ∈ W) :
    ∃ U : Fin 3 → TangentSpace I x, ∀ j, g.inner x (U j) (U j) = 1 ∧
      intrinsicGeodesic g hEnorm x (U j) (dist x (a j)) = a j := by
  have h : ∀ j, ∃ U : TangentSpace I x, g.inner x U U = 1 ∧
      intrinsicGeodesic g hEnorm x U (dist x (a j)) = a j := fun j =>
    exists_unit_dir_O8 g hEnorm x (a j) (ne_a_of_mem_O8 hbounds ha₀ hx j).symm
  choose U hU using h
  exact ⟨U, hU⟩

include hEnorm in
/-- **Sharp Lipschitz bound** for distance coordinates. -/
theorem lip_CX7
    (hpacket : PairedComparisonPacket δ W a b) (hWo : W ⊆ Metric.ball o R)
    (hao : ∀ j, a j ∈ Metric.ball o R) (hbo : ∀ j, b j ∈ Metric.ball o R)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-(1 : ℝ) ^ 2))
    (hbounds : ∀ z ∈ W, ∀ j, dist z (a j) ∈ Icc a₀ A₀ ∧ dist z (b j) ∈ Icc a₀ A₀)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10)
    {x y : M} (hx : x ∈ W) (hy : y ∈ W) (ht1 : dist x y ≤ 1) (hta : dist x y ≤ a₀ / 2) :
    dist (distanceCoordinates 2 a y) (distanceCoordinates 2 a x) ≤
      (Real.sqrt (1 + 4 * δ) + Real.sqrt 3 * (2 * δ + 3 * (4 * cosh (A₀ + 1) / sinh a₀) *
        dist x y)) * dist x y := by
  set K := 4 * cosh (A₀ + 1) / sinh a₀ with hK
  have hKpos : 0 ≤ K := div_nonneg (by positivity) (Real.sinh_pos_iff.mpr ha₀).le
  by_cases hyx : y = x
  · subst hyx; simp
  set t := dist x y with ht
  have ht0 : 0 ≤ t := dist_nonneg
  obtain ⟨V, hV, hVy⟩ := exists_unit_dir_O8 g hEnorm x y (Ne.symm hyx)
  obtain ⟨U, hU⟩ := exists_dirs_CX7 g hEnorm hbounds ha₀ hx
  have hke : ∀ j, |dist y (a j) - dist x (a j) + t * g.inner x (U j) V| ≤
      2 * δ * t + 3 * K * t ^ 2 := fun j =>
    ke_O8 g hEnorm o hpacket hWo hao hbo hsec hbounds ha₀ hδ hδ1 hx hy j ht1 hta (U j) V
      (hU j).1 hV (hU j).2 hVy
  -- vectors
  let cv : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun j => t * g.inner x (U j) V)
  let ev : EuclideanSpace ℝ (Fin 3) :=
    WithLp.toLp 2 (fun j => dist y (a j) - dist x (a j) + t * g.inner x (U j) V)
  have hsplit : distanceCoordinates 2 a y - distanceCoordinates 2 a x = ev - cv := by
    ext j; simp [ev, cv]
  have hev : ‖ev‖ ≤ Real.sqrt 3 * (2 * δ * t + 3 * K * t ^ 2) :=
    norm_le_sqrt3_of_abs_le_CX7 ev (fun j => by simpa [ev] using hke j)
  -- `‖cv‖ ≤ t √(1 + 4δ)` from the upper Bessel bound
  have hUn : ∀ j, ‖U j‖ = 1 := fun j => by
    have h : ‖U j‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hEnorm.inner_eq, (hU j).1]
    have := norm_nonneg (U j); nlinarith
  have hoff : ∀ j k, j ≠ k → |(⟪U j, U k⟫_ℝ)| ≤ 2 * δ := fun j k hjk => by
    rw [hEnorm.inner_eq]
    exact cross_abs_le_O8 g hEnorm o hpacket hWo hao hbo hsec hbounds ha₀ hδ hδ1 hx j k hjk
      (U j) (U k) (hU j).1 (hU k).1 (hU j).2 (hU k).2
  have hVn : ‖V‖ = 1 := by
    have h : ‖V‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hEnorm.inner_eq, hV]
    have := norm_nonneg V; nlinarith
  have hbes := sum_inner_sq_le_O8 U hUn hoff V
  rw [hVn] at hbes
  have hcv : ‖cv‖ ≤ t * Real.sqrt (1 + 4 * δ) := by
    rw [euclidean_norm_three_CX7]
    have he : ∀ j, (cv j) = t * ⟪U j, V⟫_ℝ := fun j => by simp [cv, hEnorm.inner_eq]
    rw [he 0, he 1, he 2]
    have hsum : (t * ⟪U 0, V⟫_ℝ) ^ 2 + (t * ⟪U 1, V⟫_ℝ) ^ 2 + (t * ⟪U 2, V⟫_ℝ) ^ 2 ≤
        (t * Real.sqrt (1 + 4 * δ)) ^ 2 := by
      rw [mul_pow t (Real.sqrt _), Real.sq_sqrt (by linarith)]
      simp only [Fin.sum_univ_three] at hbes
      have e : (t * ⟪U 0, V⟫_ℝ) ^ 2 + (t * ⟪U 1, V⟫_ℝ) ^ 2 + (t * ⟪U 2, V⟫_ℝ) ^ 2 =
          t ^ 2 * (⟪U 0, V⟫_ℝ ^ 2 + ⟪U 1, V⟫_ℝ ^ 2 + ⟪U 2, V⟫_ℝ ^ 2) := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
      linarith
    calc Real.sqrt _ ≤ Real.sqrt ((t * Real.sqrt (1 + 4 * δ)) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = t * Real.sqrt (1 + 4 * δ) := Real.sqrt_sq (by positivity)
  rw [dist_eq_norm, hsplit]
  calc ‖ev - cv‖ ≤ ‖ev‖ + ‖cv‖ := norm_sub_le _ _
    _ ≤ Real.sqrt 3 * (2 * δ * t + 3 * K * t ^ 2) + t * Real.sqrt (1 + 4 * δ) :=
        add_le_add hev hcv
    _ = (Real.sqrt (1 + 4 * δ) + Real.sqrt 3 * (2 * δ + 3 * K * t)) * t := by ring

include hEnorm in
/-- **Local descent** for `‖f z - w‖`. -/
theorem descent_CX7 (hdim : Module.finrank ℝ E = 3)
    (hpacket : PairedComparisonPacket δ W a b) (hWo : W ⊆ Metric.ball o R)
    (hao : ∀ j, a j ∈ Metric.ball o R) (hbo : ∀ j, b j ∈ Metric.ball o R)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-(1 : ℝ) ^ 2))
    (hbounds : ∀ z ∈ W, ∀ j, dist z (a j) ∈ Icc a₀ A₀ ∧ dist z (b j) ∈ Icc a₀ A₀)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10)
    {κ : ℝ} (hκ : κ + Real.sqrt 3 * (2 * δ) < Real.sqrt (1 - 4 * δ))
    {z : M} {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hball : Metric.ball z ε₀ ⊆ W)
    {w : EuclideanSpace ℝ (Fin 3)} (hw : distanceCoordinates 2 a z ≠ w) :
    ∃ y ∈ Metric.ball z ε₀,
      ‖distanceCoordinates 2 a y - w‖ + κ * dist z y < ‖distanceCoordinates 2 a z - w‖ := by
  set K := 4 * cosh (A₀ + 1) / sinh a₀ with hK
  have hKpos : 0 ≤ K := div_nonneg (by positivity) (Real.sinh_pos_iff.mpr ha₀).le
  have hz : z ∈ W := hball (mem_ball_self hε₀)
  set f := distanceCoordinates (X := M) 2 a with hf
  set Rv : EuclideanSpace ℝ (Fin 3) := w - f z with hRv
  have hR0 : Rv ≠ 0 := by
    intro h; apply hw; rw [hRv, sub_eq_zero] at h; exact h.symm
  have hRpos : 0 < ‖Rv‖ := norm_pos_iff.mpr hR0
  obtain ⟨U, hU⟩ := exists_dirs_CX7 g hEnorm hbounds ha₀ hz
  have hUn : ∀ j, ‖U j‖ = 1 := fun j => by
    have h : ‖U j‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hEnorm.inner_eq, (hU j).1]
    have := norm_nonneg (U j); nlinarith
  have hoff : ∀ j k, j ≠ k → |(⟪U j, U k⟫_ℝ)| ≤ 2 * δ := fun j k hjk => by
    rw [hEnorm.inner_eq]
    exact cross_abs_le_O8 g hEnorm o hpacket hWo hao hbo hsec hbounds ha₀ hδ hδ1 hz j k hjk
      (U j) (U k) (hU j).1 (hU k).1 (hU j).2 (hU k).2
  have hdimT : Module.finrank ℝ (TangentSpace I z) = 3 := hdim
  obtain ⟨V₀, hV₀, hV₀n⟩ := exists_inner_eq_O8 U hUn (by linarith) hoff hdimT (fun j => -Rv j)
  have hsumR : ∑ j, (-Rv j) ^ 2 = ‖Rv‖ ^ 2 := by
    rw [euclidean_norm_three_CX7, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_three]
  rw [hsumR] at hV₀n
  have hq : 0 < 1 - 4 * δ := by linarith
  have hV₀ne : V₀ ≠ 0 := by
    intro h
    have h0 := hV₀ 0
    have h1 := hV₀ 1
    have h2 := hV₀ 2
    rw [h, inner_zero_right] at h0 h1 h2
    have : Rv 0 = 0 ∧ Rv 1 = 0 ∧ Rv 2 = 0 := ⟨by linarith, by linarith, by linarith⟩
    apply hR0
    ext j; fin_cases j <;> simp [this.1, this.2.1, this.2.2]
  have hV₀pos : 0 < ‖V₀‖ := norm_pos_iff.mpr hV₀ne
  set N := ‖V₀‖ with hN
  -- `N √(1-4δ) ≤ ‖R‖`
  have hNR : N * Real.sqrt (1 - 4 * δ) ≤ ‖Rv‖ := by
    have h1 : (N * Real.sqrt (1 - 4 * δ)) ^ 2 ≤ ‖Rv‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hq.le]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h1
  set V : TangentSpace I z := N⁻¹ • V₀ with hVdef
  have hV : g.inner z V V = 1 := by
    rw [← hEnorm.inner_eq, hVdef, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    have hNne : N ≠ 0 := hV₀pos.ne'
    change N⁻¹ * (N⁻¹ * N ^ 2) = 1
    field_simp
  have hUV : ∀ j, g.inner z (U j) V = -Rv j / N := fun j => by
    rw [← hEnorm.inner_eq, hVdef, real_inner_smul_right, hV₀ j]; ring
  obtain ⟨ρz, hρz, hsmall⟩ := exists_geodesic_dist_eq_small_O8 g hEnorm z
  set gap := Real.sqrt (1 - 4 * δ) - Real.sqrt 3 * (2 * δ) - κ with hgap
  have hgap0 : 0 < gap := by linarith
  set m := min (min (min ρz ε₀) (min 1 (a₀ / 2))) (min N (gap / (3 * Real.sqrt 3 * K + 1)))
    with hm
  have hden : 0 < 3 * Real.sqrt 3 * K + 1 := by positivity
  have hm0 : 0 < m := by
    have : 0 < gap / (3 * Real.sqrt 3 * K + 1) := div_pos hgap0 hden
    have h1 : (0 : ℝ) < a₀ / 2 := by linarith
    simp only [hm, lt_min_iff]
    exact ⟨⟨⟨hρz, hε₀⟩, ⟨zero_lt_one, h1⟩⟩, ⟨hV₀pos, this⟩⟩
  set s := m / 2 with hs
  have hs0 : 0 < s := by positivity
  have hsle : s ≤ m := by linarith
  have hslt : s < m := by linarith
  have hsρ : s < ρz :=
    lt_of_lt_of_le hslt ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hsε : s < ε₀ :=
    lt_of_lt_of_le hslt ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hs1 : s ≤ 1 := hsle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsa : s ≤ a₀ / 2 :=
    hsle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsN : s ≤ N := hsle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsg : s ≤ gap / (3 * Real.sqrt 3 * K + 1) :=
    hsle.trans ((min_le_right _ _).trans (min_le_right _ _))
  set y := intrinsicGeodesic g hEnorm z V s with hy
  have hzy : dist z y = s := hsmall V hV s hs0.le hsρ
  have hyball : y ∈ Metric.ball z ε₀ := by rw [mem_ball, dist_comm, hzy]; exact hsε
  have hyW : y ∈ W := hball hyball
  have hVy : intrinsicGeodesic g hEnorm z V (dist z y) = y := by rw [hzy]
  have hke : ∀ j, |dist y (a j) - dist z (a j) + dist z y * g.inner z (U j) V| ≤
      2 * δ * dist z y + 3 * K * dist z y ^ 2 := fun j =>
    ke_O8 g hEnorm o hpacket hWo hao hbo hsec hbounds ha₀ hδ hδ1 hz hyW j (hzy ▸ hs1)
      (hzy ▸ hsa) (U j) V (hU j).1 hV (hU j).2 hVy
  rw [hzy] at hke
  set lam := s / N with hlam
  have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hV₀pos]; exact hsN
  have hlam0 : 0 ≤ lam := by positivity
  -- decomposition `f y - w = ev - (1 - lam) • Rv`
  let ev : EuclideanSpace ℝ (Fin 3) :=
    WithLp.toLp 2 (fun j => dist y (a j) - dist z (a j) + s * g.inner z (U j) V)
  have hdec : f y - w = ev - (1 - lam) • Rv := by
    ext j
    simp only [ev, hf, hRv, PiLp.sub_apply, PiLp.smul_apply, distanceCoordinates_apply,
      smul_eq_mul, hUV j, hlam]
    field_simp
    ring
  have hev : ‖ev‖ ≤ Real.sqrt 3 * (2 * δ * s + 3 * K * s ^ 2) :=
    norm_le_sqrt3_of_abs_le_CX7 ev (fun j => by simpa [ev] using hke j)
  have hfz : ‖f z - w‖ = ‖Rv‖ := by rw [hRv]; exact norm_sub_rev _ _
  have hlamR : s * Real.sqrt (1 - 4 * δ) ≤ lam * ‖Rv‖ := by
    calc s * Real.sqrt (1 - 4 * δ) = lam * (N * Real.sqrt (1 - 4 * δ)) := by
           rw [hlam]; field_simp
         _ ≤ lam * ‖Rv‖ := mul_le_mul_of_nonneg_left hNR hlam0
  refine ⟨y, hyball, ?_⟩
  rw [hdec, hfz, hzy]
  have hn : ‖ev - (1 - lam) • Rv‖ ≤ ‖ev‖ + (1 - lam) * ‖Rv‖ := by
    calc ‖ev - (1 - lam) • Rv‖ ≤ ‖ev‖ + ‖(1 - lam) • Rv‖ := norm_sub_le _ _
      _ = ‖ev‖ + (1 - lam) * ‖Rv‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  -- `3√3 K s ≤ gap * (3√3K)/(3√3K+1) < gap`
  have hKs : 3 * Real.sqrt 3 * K * s < gap := by
    have hden : 0 < 3 * Real.sqrt 3 * K + 1 := by positivity
    have := (le_div_iff₀ hden).mp hsg
    nlinarith only [this, hs0]
  have hsq3 : Real.sqrt 3 * (3 * K * s ^ 2) = (3 * Real.sqrt 3 * K * s) * s := by ring
  have hstrict := mul_lt_mul_of_pos_right hKs hs0
  dsimp only [gap] at hstrict
  nlinarith only [hn, hev, hlamR, hstrict]

/-- The explicit constants in the sharp strainer estimate. -/
theorem strainer_constants_CX7 {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 10)
    (hδ : 0 < δ) (hδθ : δ ≤ θ / 10) :
    Real.sqrt (1 + 4 * δ) ≤ 1 + 2 * δ ∧
    1 - 2 * θ + Real.sqrt 3 * (2 * δ) < Real.sqrt (1 - 4 * δ) ∧
    (1 - 9 * θ) * (1 + θ) ^ 3 ≤ (1 - 2 * θ) ^ 3 := by
  have hs3 : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hslo : 1 - 4 * δ ≤ Real.sqrt (1 - 4 * δ) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - 4 * δ by linarith)
    have hn := Real.sqrt_nonneg (1 - 4 * δ)
    nlinarith [sq_nonneg (4 * δ)]
  refine ⟨(Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith [sq_nonneg δ]⟩, ?_, ?_⟩
  · have : Real.sqrt 3 * (2 * δ) ≤ 4 * δ := by nlinarith
    linarith
  · have hid : (1 - 2 * θ) ^ 3 - (1 - 9 * θ) * (1 + θ) ^ 3 =
        9 * θ ^ 2 * (θ ^ 2 + 2 * θ + 4) := by ring
    have hp : 0 ≤ 9 * θ ^ 2 * (θ ^ 2 + 2 * θ + 4) := by positivity
    linarith

include hEnorm in
/-- **Sharp strainer volume bound.** The packet is uniform on a neighborhood of the
closed ball. Its anchor bounds and the smallness of `s` make the image radius and
Lipschitz constant arbitrarily close to one. -/
theorem strainer_volume_CX7 (hdim : Module.finrank ℝ E = 3)
    (hpacket : PairedComparisonPacket δ W a b) (hWo : W ⊆ Metric.ball o R)
    (hao : ∀ j, a j ∈ Metric.ball o R) (hbo : ∀ j, b j ∈ Metric.ball o R)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-(1 : ℝ) ^ 2))
    (hbounds : ∀ z ∈ W, ∀ j, dist z (a j) ∈ Icc a₀ A₀ ∧ dist z (b j) ∈ Icc a₀ A₀)
    (ha₀ : 0 < a₀) {q : M} {s θ : ℝ}
    (hs : 0 < s) (hball : Metric.ball q (2 * s) ⊆ W)
    (hcompact : IsCompact (Metric.closedBall q s))
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 10) (hδ : 0 < δ) (hδθ : δ ≤ θ / 10)
    (hs1 : 2 * s ≤ 1) (hsa : 2 * s ≤ a₀ / 2)
    (hsK : (4 * cosh (A₀ + 1) / sinh a₀) * s ≤ θ / 42) :
    ENNReal.ofReal ((1 - 9 * θ) * euclideanUnitBallVolume 3 * s ^ 3) ≤
      ballVolume g q s := by
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  let f := distanceCoordinates (X := M) 2 a
  let K := 4 * cosh (A₀ + 1) / sinh a₀
  have hK : 0 ≤ K := div_nonneg (by positivity) (Real.sinh_pos_iff.mpr ha₀).le
  have hδ1 : δ ≤ 1 / 10 := by linarith
  obtain ⟨hupper, hdes, hratio⟩ := strainer_constants_CX7 hθ hθ1 hδ hδθ
  have hs3 : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsub : Metric.ball q s ⊆ W := (Metric.ball_subset_ball (by linarith)).trans hball
  have hlip : LipschitzOnWith ⟨1 + θ, by positivity⟩ f (Metric.ball q s) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have ht : dist y x ≤ 2 * s := by
      have hx' := mem_ball.mp hx
      have hy' := mem_ball.mp hy
      have htri := dist_triangle y q x
      rw [dist_comm q x] at htri
      linarith
    have h := lip_CX7 g hEnorm o hpacket hWo hao hbo hsec hbounds ha₀ hδ hδ1
      (hsub hy) (hsub hx) (ht.trans hs1) (ht.trans hsa)
    have hc : Real.sqrt (1 + 4 * δ) + Real.sqrt 3 * (2 * δ + 3 * K * dist y x) ≤ 1 + θ := by
      have he : Real.sqrt 3 * (2 * δ + 3 * K * dist y x) ≤
          2 * (2 * δ + 3 * K * dist y x) := by
        gcongr
      have hd : K * dist y x ≤ 2 * (K * s) := by nlinarith
      change K * s ≤ θ / 42 at hsK
      linarith
    change dist (f x) (f y) ≤ (1 + θ) * dist x y
    rw [dist_comm x y]
    exact h.trans (mul_le_mul_of_nonneg_right hc dist_nonneg)
  have himage : Metric.ball (f q) ((1 - 2 * θ) * s) ⊆ f '' Metric.ball q s := by
    intro w hw
    have hκ : 0 < 1 - 2 * θ := by linarith
    have hstart : ‖f q - w‖ < (1 - 2 * θ) * s := by
      rw [← dist_eq_norm, dist_comm]
      exact mem_ball.mp hw
    have hdesc : ∀ z ∈ Metric.ball q s, f z ≠ w →
        ∃ y ∈ Metric.ball q s, ‖f y - w‖ + (1 - 2 * θ) * dist z y < ‖f z - w‖ := by
      intro z hz hne
      have hε : 0 < s - dist z q := sub_pos.mpr (mem_ball.mp hz)
      have hzsub : Metric.ball z (s - dist z q) ⊆ Metric.ball q s := by
        intro y hy
        rw [mem_ball] at hy ⊢
        have := dist_triangle y z q
        linarith
      obtain ⟨y, hy, hdrop⟩ := descent_CX7 g hEnorm o hdim hpacket hWo hao hbo hsec hbounds
        ha₀ hδ hδ1 hdes hε (hzsub.trans hsub) hne
      exact ⟨y, hzsub hy, hdrop⟩
    obtain ⟨z, hz, hfz, -⟩ := exists_preimage_of_local_descent_O8 hκ hcompact
      (lipschitzWith_distanceCoordinates_two a).continuous.continuousOn hstart hdesc
    exact ⟨z, hz, hfz⟩
  have hκ0 : 0 ≤ 1 - 2 * θ := by linarith
  have hmeasure := ball_le_normalizedHausdorffMeasure_three_O8 hlip
    (show 0 < (⟨1 + θ, by positivity⟩ : ℝ≥0) from by exact_mod_cast (show 0 < 1 + θ by linarith))
    (show 0 ≤ (1 - 2 * θ) * s by positivity) himage
  have hvol : MeasureTheory.normalizedHausdorffMeasure 3 (Metric.ball q s) = ballVolume g q s := by
    rw [DifferentialGeometry.Geometry.Metric.normalizedHausdorffMeasure_three_eq_riemannianVolumeMeasure
      g hEnorm hdim]
    rw [ballVolume, DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm g hEnorm]
  rw [hvol] at hmeasure
  refine le_trans ?_ hmeasure
  have hω := euclideanUnitBallVolume_pos 3
  have hreal : (1 - 9 * θ) * euclideanUnitBallVolume 3 * s ^ 3 ≤
      euclideanUnitBallVolume 3 * ((1 - 2 * θ) * s) ^ 3 / (1 + θ) ^ 3 := by
    apply (le_div_iff₀ (by positivity : 0 < (1 + θ) ^ 3)).mpr
    have := mul_le_mul_of_nonneg_right hratio (show 0 ≤ euclideanUnitBallVolume 3 * s ^ 3 by positivity)
    nlinarith
  calc ENNReal.ofReal ((1 - 9 * θ) * euclideanUnitBallVolume 3 * s ^ 3)
      ≤ ENNReal.ofReal (euclideanUnitBallVolume 3 * ((1 - 2 * θ) * s) ^ 3 / (1 + θ) ^ 3) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity)]
      congr 2
      exact ENNReal.ofReal_eq_coe_nnreal (show 0 ≤ 1 + θ by positivity)

end Packet

end GC.LongTime.Ch12
