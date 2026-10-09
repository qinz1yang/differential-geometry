import DifferentialGeometry.Geometry.Comparison.Toponogov.RankTwoProductAnchors
import DifferentialGeometry.Geometry.Collapse.RankTwoCoordinateKernel
import DifferentialGeometry.Geometry.Collapse.EdgeScaledSmoothing
import DifferentialGeometry.Analysis.Integration.Measure.EuclideanPlane

/-!
# Smooth adapted coordinates for an actual rank-two splitting

The same two splitting coordinates choose source-ball anchors. Their genuine
minimizing directions control both smoothed gradients and the mixed Gram matrix.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold RealInnerProductSpace
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Analysis
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

private def pairedCoordinates {M : Type*} (f : Fin 2 → M → ℝ) :
    M → EuclideanSpace ℝ (Fin 2) :=
  fun x => euclideanPlaneProdEquiv.symm (f 0 x, f 1 x)

private theorem pairedCoordinates_apply {M : Type*} (f : Fin 2 → M → ℝ)
    (x : M) (j : Fin 2) : pairedCoordinates f x j = f j x := by
  fin_cases j <;> simp [pairedCoordinates]

private theorem rankTwo_norm_le {v : EuclideanSpace ℝ (Fin 2)} {a : ℝ}
    (ha : 0 ≤ a) (h : ∀ j, |v j| ≤ a) : ‖v‖ ≤ 2 * a := by
  have hs : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs]
  have h0 := sq_le_sq₀ (abs_nonneg (v 0)) ha |>.mpr (h 0)
  have h1 := sq_le_sq₀ (abs_nonneg (v 1)) ha |>.mpr (h 1)
  rw [sq_abs] at h0 h1
  nlinarith [norm_nonneg v]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem pairedCoordinates_smooth {f : Fin 2 → M → ℝ} {U : Set M}
    (hf : ∀ j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f j) U) :
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ (pairedCoordinates f) U := by
  exact euclideanPlaneProdEquiv.symm.contDiff.contMDiff.comp_contMDiffOn
    ((contMDiffOn_prod_module_iff _).mpr ⟨hf 0, hf 1⟩)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem pairedCoordinates_deriv {f : Fin 2 → M → ℝ} {x : M}
    (hf : ∀ j, MDifferentiableAt I 𝓘(ℝ, ℝ) (f j) x)
    (w : TangentSpace I x) (j : Fin 2) :
    mvfderiv (I := I) (pairedCoordinates f) x w j =
      mvfderiv (I := I) (f j) x w := by
  let p : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun i : Fin 2 => ℝ) j
  have hη : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (pairedCoordinates f) x :=
    euclideanPlaneProdEquiv.symm.differentiableAt.mdifferentiableAt.comp x
      ((hf 0).prodMk_space (hf 1))
  have heq : p ∘ pairedCoordinates f = f j := by
    funext y
    exact pairedCoordinates_apply f y j
  have hh := _root_.mvfderiv_comp_apply x p.differentiableAt.mdifferentiableAt hη w
  rw [heq, mvfderiv_eq_fderiv, p.fderiv] at hh
  exact hh.symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem pairedCoordinates_curve {f : Fin 2 → M → ℝ} {c : ℝ → M} {t : ℝ}
    (hf : ∀ j, MDifferentiableAt I 𝓘(ℝ, ℝ) (f j) (c t))
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
    HasDerivAt (fun s => pairedCoordinates f (c s))
      (mvfderiv (I := I) (pairedCoordinates f) (c t)
        (mfderiv 𝓘(ℝ, ℝ) I c t (realTangentOne t))) t := by
  have hd := euclideanPlaneProdEquiv.symm.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_comp_mfderiv_along I (f 0) c t (hf 0) hc).prodMk
      (hasDerivAt_comp_mfderiv_along I (f 1) c t (hf 1) hc))
  apply hd.congr_deriv
  ext j
  rw [pairedCoordinates_deriv hf]
  fin_cases j <;> simp [mvfderiv]

private theorem pairedCoordinates_lipschitz
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {q : M} {f : Fin 2 → M → ℝ} {L : ℝ}
    (hf : ∀ j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f j) (Metric.ball q 3))
    (hD : ∀ x ∈ Metric.ball q 3, ∀ w : TangentSpace I x,
      ‖mvfderiv (I := I) (pairedCoordinates f) x w‖ ≤ L * ‖w‖)
    {x y : M} (hx : x ∈ Metric.ball q 1) (hy : y ∈ Metric.ball q 1) :
    ‖pairedCoordinates f x - pairedCoordinates f y‖ ≤ L * dist x y := by
  by_cases hxy : x = y
  · simp [hxy]
  have hlen : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨u, hu, hend⟩ := soul_unit_minimizing_initial g hEnorm x y hlen
  let c := intrinsicGeodesic g hEnorm x u
  have hc := intrinsicGeodesic_contMDiff g hEnorm x u
  have hc0 : c 0 = x := intrinsicGeodesic_zero g hEnorm x u
  have hcL : c (dist x y) = y := hend
  have hcball : ∀ t ∈ Icc (0 : ℝ) (dist x y), c t ∈ Metric.ball q 3 := by
    intro t ht
    have hd := (lipschitzWith_one_intrinsicGeodesic g hEnorm x u hu).dist_le_mul t 0
    simp only [intrinsicGeodesic_zero, NNReal.coe_one, one_mul, Real.dist_eq,
      sub_zero, abs_of_nonneg ht.1] at hd
    have hxy2 : dist x y < 2 := by
      have htri := dist_triangle x q y
      rw [dist_comm q y] at htri
      linarith [Metric.mem_ball.mp hx, Metric.mem_ball.mp hy]
    have htri := dist_triangle (c t) x q
    change dist (c t) x ≤ t at hd
    exact Metric.mem_ball.mpr (by linarith [Metric.mem_ball.mp hx, ht.2])
  let d : ℝ → EuclideanSpace ℝ (Fin 2) := fun t =>
    mvfderiv (I := I) (pairedCoordinates f) (c t)
      (mfderiv 𝓘(ℝ, ℝ) I c t (realTangentOne t))
  have hd : ∀ t ∈ Icc (0 : ℝ) (dist x y),
      HasDerivWithinAt (fun s => pairedCoordinates f (c s)) (d t) (Icc 0 (dist x y)) t := by
    intro t ht
    exact (pairedCoordinates_curve (fun j =>
      ((hf j) (c t) (hcball t ht)).contMDiffAt
        (Metric.isOpen_ball.mem_nhds (hcball t ht)) |>.mdifferentiableAt (by simp))
      (hc.contMDiffAt.mdifferentiableAt (by simp))).hasDerivWithinAt
  have hb : ∀ t ∈ Ico (0 : ℝ) (dist x y), ‖d t‖ ≤ L := by
    intro t ht
    have hs : ‖mfderiv 𝓘(ℝ, ℝ) I c t (realTangentOne t)‖ = 1 := by
      rw [norm_tangent_eq_sqrt_gInner hEnorm]
      change Real.sqrt (g.inner (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1)
        (mfderiv 𝓘(ℝ, ℝ) I c t 1)) = 1
      rw [intrinsicGeodesic_speedSq_eq g hEnorm x u t, hu, Real.sqrt_one]
    simpa only [d, hs, mul_one] using hD (c t) (hcball t (Ico_subset_Icc_self ht))
      (mfderiv 𝓘(ℝ, ℝ) I c t (realTangentOne t))
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hd hb
    (dist x y) (right_mem_Icc.mpr hlen.le)
  simpa only [hcL, hc0, norm_sub_rev, sub_zero] using hh

private theorem smoothed_rankTwo_anchors
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {q : M} {ε τ R : ℝ} {Φ : M → EuclideanSpace ℝ (Fin 2)}
    (A : Fin 2 → M) (hε : 0 < ε) (hε1 : ε < 1) (hτ : 0 < τ)
    (hsmall : τ + 4 * ε < 1) (hτgrad : τ < ε ^ 2 / 20)
    (haway : ∀ j, A j ∉ Metric.ball q 4)
    (hvalue : ∀ j, ∀ x ∈ Metric.ball q R,
      |(dist q (A j) - dist x (A j)) - Φ x j| < τ)
    (hdiam : ∀ j, ∀ x ∈ Metric.ball q 4,
      ∀ u ∈ minimizingDirectionsTo g hEnorm {A j} x,
      ∀ v ∈ minimizingDirectionsTo g hEnorm {A j} x,
      Real.sqrt (g.inner x (u - v) (u - v)) ≤ τ)
    (hgram : ∀ x ∈ Metric.ball q 4,
      ∀ u ∈ minimizingDirectionsTo g hEnorm {A 0} x,
      ∀ v ∈ minimizingDirectionsTo g hEnorm {A 1} x, |g.inner x u v| ≤ τ)
    (htest : ∀ j, ∀ x ∈ Metric.ball q 4, ∀ z ∈ Metric.ball q R,
      1 < dist x z → ∀ u ∈ minimizingDirectionsTo g hEnorm {A j} x,
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x z) = z →
      |g.inner x u w - (Φ z j - Φ x j) / dist x z| < τ) :
    ∃ f : Fin 2 → M → ℝ,
      (∀ j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f j) (Metric.ball q 3)) ∧
      (∀ j, f j q = 0) ∧
      (∀ x ∈ Metric.ball q 3,
        Function.Surjective (mvfderiv (I := I) (pairedCoordinates f) x) ∧
        ∀ w : TangentSpace I x,
          ‖mvfderiv (I := I) (pairedCoordinates f) x w‖ ≤
            (Real.sqrt (1 + τ) + Real.sqrt 2 * ε) * ‖w‖) ∧
      (∀ x ∈ Metric.ball q R, ∀ j,
        |f j x - Φ x j| < ε * dist x q + τ) ∧
      ∀ x ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q R, 1 < dist x z →
        ∀ w : TangentSpace I x, g.inner x w w = 1 →
        intrinsicGeodesic g hEnorm x w (dist x z) = z →
        ‖mvfderiv (I := I) (pairedCoordinates f) x w -
          (dist x z)⁻¹ • (Φ z - Φ x)‖ ≤ 2 * (ε + τ) := by
  let : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  have hsmooth (j : Fin 2) : ∃ F : M → ℝ, ∃ O : Set M,
      IsOpen O ∧ Metric.closedBall q 3 ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x y, |(F x - dist x (A j)) - (F y - dist y (A j))| ≤ ε * dist x y) ∧
      ∀ x ∈ Metric.closedBall q 3,
        ∀ v ∈ minimizingDirectionsTo g hEnorm {A j} x, ‖gradFun g F x + v‖ < ε := by
    have hUA : Metric.ball q 4 ⊆ ({A j} : Set M)ᶜ := by
      intro x hx hxa
      exact haway j ((mem_singleton_iff.mp hxa) ▸ hx)
    obtain ⟨F, O, hO, hCO, hFO, hclose, hout, hdiff, hFl, hgrad⟩ :=
      exists_distance_smoothing_with_gradient g hEnorm hε hε1 isClosed_singleton
        (singleton_nonempty (A j)) Metric.isOpen_ball hUA (hdiam j) hτgrad
        (isCompact_closedBall q 3)
        (fun x hx => Metric.mem_ball.mpr
          (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by norm_num : (3 : ℝ) < 4)))
        (e := 1) zero_lt_one
    refine ⟨F, O, hO, hCO, hFO, by simpa only [Metric.infDist_singleton] using hdiff, ?_⟩
    intro x hx v hv
    simpa only [norm_tangent_eq_sqrt_gInner hEnorm] using hgrad x hx v hv
  choose F O hO hCO hFO hdiff hgrad using hsmooth
  let f : Fin 2 → M → ℝ := fun j x => F j q - F j x
  have hf : ∀ j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f j) (Metric.ball q 3) := by
    intro j
    exact (contMDiffOn_const.sub (hFO j)).mono
      (fun x hx => hCO j (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le))
  have hfder (j : Fin 2) (x : M) (hx : x ∈ Metric.ball q 3)
      (w : TangentSpace I x) : mvfderiv (I := I) (f j) x w =
        g.inner x (-gradFun g (F j) x) w := by
    have hFx := (hFO j x (hCO j (Metric.mem_closedBall.mpr
      (Metric.mem_ball.mp hx).le))).contMDiffAt ((hO j).mem_nhds (hCO j
        (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le)))
    change mvfderiv (I := I) ((fun y : M => F j q) - F j) x w = _
    rw [_root_.mvfderiv_sub mdifferentiableAt_const
      (hFx.mdifferentiableAt (by simp)), _root_.mvfderiv_const]
    rw [zero_sub]
    change (-mvfderiv (I := I) (F j) x) w = _
    have hg := inner_gradFun g (F j) x w
    change g.inner x (gradFun g (F j) x) w = mvfderiv (I := I) (F j) x w at hg
    rw [neg_apply, ← hg]
    simp only [map_neg, neg_apply]
  have hdir (j : Fin 2) (x : M) (hx : x ∈ Metric.ball q 3) :
      ∃ u, u ∈ minimizingDirectionsTo g hEnorm {A j} x := by
    have hx4 : x ∈ Metric.ball q 4 := Metric.ball_subset_ball (by norm_num) hx
    have hpos : 0 < dist x (A j) := dist_pos.mpr (by
      intro he
      exact haway j (he ▸ hx4))
    obtain ⟨u, hu, hend⟩ := soul_unit_minimizing_initial g hEnorm x (A j) hpos
    exact ⟨u, hu, by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hend⟩
  refine ⟨f, hf, by intro j; simp [f], ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨u₀, hu₀⟩ := hdir 0 x hx
    obtain ⟨u₁, hu₁⟩ := hdir 1 x hx
    have hn (j : Fin 2) (u : TangentSpace I x)
        (hu : u ∈ minimizingDirectionsTo g hEnorm {A j} x) :
        ‖-gradFun g (F j) x - u‖ ≤ ε := by
      have he : -gradFun g (F j) x - u = -(gradFun g (F j) x + u) := by abel
      rw [he, norm_neg]
      exact (hgrad j x (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le) u hu).le
    have hu0 : ‖u₀‖ = 1 := by rw [norm_tangent_eq_sqrt_gInner hEnorm, hu₀.1, Real.sqrt_one]
    have hu1 : ‖u₁‖ = 1 := by rw [norm_tangent_eq_sqrt_gInner hEnorm, hu₁.1, Real.sqrt_one]
    have hgr : |inner ℝ u₀ u₁| ≤ τ := by
      rw [hEnorm.inner_eq]
      exact hgram x (Metric.ball_subset_ball (by norm_num) hx) u₀ hu₀ u₁ hu₁
    apply rankTwo_norm_of_almostOrthonormal hu0 hu1 hε.le (hn 0 u₀ hu₀) (hn 1 u₁ hu₁)
      hgr hsmall
      (mvfderiv (I := I) (pairedCoordinates f) x).toLinearMap
    intro w
    have hmd (j : Fin 2) := (((hf j) x hx).contMDiffAt
      (Metric.isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp)
    constructor
    · change mvfderiv (I := I) (pairedCoordinates f) x w 0 = _
      rw [pairedCoordinates_deriv hmd, hfder 0 x hx w, hEnorm.inner_eq]
    · change mvfderiv (I := I) (pairedCoordinates f) x w 1 = _
      rw [pairedCoordinates_deriv hmd, hfder 1 x hx w, hEnorm.inner_eq]
  · intro x hx j
    have hd := hdiff j q x
    rw [dist_comm q x] at hd
    have hfa : |f j x - (dist q (A j) - dist x (A j))| ≤ ε * dist x q := by
      convert hd using 1
      congr 1
      dsimp [f]
      ring
    exact (abs_sub_le (f j x) (dist q (A j) - dist x (A j)) (Φ x j)).trans_lt
      (add_lt_add_of_le_of_lt hfa (hvalue j x hx))
  · intro x hx z hz hxz w hw hwz
    have hx3 : x ∈ Metric.ball q 3 := Metric.ball_subset_ball (by norm_num) hx
    have hmd (j : Fin 2) := (((hf j) x hx3).contMDiffAt
      (Metric.isOpen_ball.mem_nhds hx3)).mdifferentiableAt (by simp)
    apply rankTwo_norm_le (by positivity)
    intro j
    obtain ⟨u, hu⟩ := hdir j x hx3
    have hn := hgrad j x (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx3).le) u hu
    have hcs := abs_inner_le_sqrt_mul_sqrt g x (gradFun g (F j) x + u) w
    rw [hw, Real.sqrt_one, mul_one] at hcs
    have ht := htest j x (Metric.ball_subset_ball (by norm_num) hx) z hz hxz u hu w hw hwz
    rw [PiLp.sub_apply, pairedCoordinates_deriv hmd, hfder j x hx3 w, PiLp.smul_apply]
    change |g.inner x (-gradFun g (F j) x) w -
      (dist x z)⁻¹ * (Φ z j - Φ x j)| ≤ ε + τ
    have hnear : |g.inner x (-gradFun g (F j) x) w - g.inner x u w| < ε := by
      have he : g.inner x (-gradFun g (F j) x) w - g.inner x u w =
          -g.inner x (gradFun g (F j) x + u) w := by
        simp only [map_add, add_apply, map_neg, neg_apply]
        ring
      rw [he, abs_neg]
      exact hcs.trans_lt (by simpa only [norm_tangent_eq_sqrt_gInner hEnorm] using hn)
    have he : (dist x z)⁻¹ * (Φ z j - Φ x j) = (Φ z j - Φ x j) / dist x z := by ring
    rw [he]
    exact ((abs_sub_le _ (g.inner x u w) _).trans_lt (add_lt_add hnear ht)).le

universe uE uH u v

theorem exists_rankTwo_adapted_coordinate_parameters {γ R : ℝ}
    (hγ : 0 < γ) (hγone : γ < 1 / 10) (hR : max 2 γ⁻¹ < R) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ν₀ < min γ (1 / 4) ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type v) [MetricSpace Y] (q : M) (y₀ : Y)
        (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), y₀)) ν),
        (∀ y ∈ Metric.ball q ν⁻¹, SectionalBoundedBelowAt g y (-ν ^ 2)) →
        ∃ η : M → EuclideanSpace ℝ (Fin 2),
          ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ η (Metric.ball q 3) ∧ η q = 0 ∧
          (∀ x ∈ Metric.ball q 1, Function.Surjective (mvfderiv (I := I) η x)) ∧
          (∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q 1,
            ‖η x - η y‖ ≤ (1 + γ) * dist x y) ∧
          (∀ x ∈ Metric.ball q 1, ‖η x - (F.toFun x).fst‖ < γ / 8) ∧
          (∀ x ∈ Metric.ball q 1,
            Metric.infDist (η x) (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) < γ) ∧
          (∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
            ∃ x ∈ Metric.ball q 1, ‖η x - y‖ < γ) ∧
          ∀ x ∈ Metric.ball q 1, ∀ z ∈ Metric.ball q R, 1 < dist x z →
            ∀ w : TangentSpace I x, g.inner x w w = 1 →
            intrinsicGeodesic g hEnorm x w (dist x z) = z →
            ‖mvfderiv (I := I) η x w -
              (dist x z)⁻¹ • ((F.toFun z).fst - (F.toFun x).fst)‖ < γ := by
  let ε : ℝ := γ / 1000
  let τ : ℝ := min (γ / 100) (ε ^ 2 / 100)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 := by dsimp [ε]; linarith
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτγ : τ ≤ γ / 100 := min_le_left _ _
  have hτε : τ ≤ ε ^ 2 / 100 := min_le_right _ _
  have hτgrad : τ < ε ^ 2 / 20 := by nlinarith
  have hsmall : τ + 4 * ε < 1 := by dsimp [ε] at *; linarith
  have hR4 : 4 < R := by
    have hinv : 10 < γ⁻¹ := (lt_inv_comm₀ (by norm_num) hγ).mpr (by linarith)
    have hh := (le_max_right (2 : ℝ) γ⁻¹).trans_lt hR
    linarith
  obtain ⟨s, hs, νStar, hνStar, hparameters⟩ :=
    exists_rankTwo_anchor_parameters (by norm_num : (2 : ℝ) ≤ 4) hR4 hτ
  let ν₀ : ℝ := min νStar (γ / 100) / 2
  have hν₀ : 0 < ν₀ := by dsimp [ν₀]; positivity
  have hν₀Star : ν₀ < νStar := by
    have hm := min_le_left νStar (γ / 100)
    dsimp [ν₀]
    linarith
  have hν₀γ : ν₀ < γ / 100 := by
    have hm := min_le_right νStar (γ / 100)
    dsimp [ν₀]
    linarith
  refine ⟨ν₀, hν₀, lt_min (by linarith) (by linarith), ?_⟩
  intro ν hν hνsmall E instNorm instSpace instFinite instNe H instTop I instBoundary
    M instMetric instChart instManifold instSigma instComplete instRB instRiem instContinuous
    g hEnorm Y instY q y₀ F hsec
  have hνs : ν < νStar := hνsmall.trans_lt hν₀Star
  have hνγ : ν < γ / 100 := hνsmall.trans_lt hν₀γ
  have hνone : ν < 1 := F.error_lt_one
  obtain ⟨hbuffer, hanchors⟩ := hparameters ν hν hνs
  have hs0 : 0 < s := by linarith
  have hcov : s < ν⁻¹ - ν := by linarith
  have hac (t : ℝ) (ht : |t| = s) (j : Fin 2) :
      ∃ a ∈ Metric.ball q ν⁻¹, dist (F.toFun a) (rankTwoAxisPoint j t y₀) < 2 * ν := by
    have hd : dist (rankTwoAxisPoint j t y₀)
        (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), y₀)) = s := by
      rw [← (rankTwoRegroup Y j).dist_eq, rankTwoRegroup_axisPoint, rankTwoRegroup_zero,
        (WithLp.isometry_prodMk_right (E := ℝ) (WithLp.toLp 2 ((0 : ℝ), y₀))).dist_eq]
      simpa only [Real.dist_eq, sub_zero] using ht
    obtain ⟨a, ha, hfa⟩ := F.coverage_witness (rankTwoAxisPoint j t y₀)
      (by rw [hd]; exact hcov)
    exact ⟨a, ha, by rwa [dist_comm]⟩
  choose A hA hFA using hac s (abs_of_pos hs0)
  choose B hB hFB using hac (-s) (by rw [abs_neg, abs_of_pos hs0])
  obtain ⟨hper, hgram⟩ := hanchors E H I M g hEnorm Y q y₀ F A B hsec hA hB hFA hFB
  have haway (j : Fin 2) : A j ∉ Metric.ball q 4 := by
    intro hx
    have hr := (F.coordinateSplitting j).supplied_anchor_radius_error (A j) (hA j)
      (by simpa only [KleinerLottApprox.coordinateSplitting_anchor_dist] using hFA j)
    rw [abs_of_pos hs0] at hr
    have hd := Metric.mem_ball.mp hx
    rw [dist_comm] at hd
    linarith [(abs_lt.mp hr).1]
  have hdiam (j : Fin 2) : ∀ x ∈ Metric.ball q 4,
      ∀ u ∈ minimizingDirectionsTo g hEnorm {A j} x,
      ∀ v ∈ minimizingDirectionsTo g hEnorm {A j} x,
      Real.sqrt (g.inner x (u - v) (u - v)) ≤ τ := by
    obtain ⟨θ, hθ, hθτ, hdiam⟩ := (hper j).2.2.2.1
    intro x hx u hu v hv
    exact ((hdiam x hx u v hu.1 hv.1
      (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hu.2)
      (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hv.2)).2).trans hθτ.le
  obtain ⟨f, hf, hfq, hD, hvalue, htest⟩ := smoothed_rankTwo_anchors g hEnorm
    A hε hε1 hτ hsmall hτgrad haway (fun j => (hper j).2.2.1) hdiam
    (fun x hx u hu v hv => (hgram x hx u v hu.1 hv.1
      (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hu.2)
      (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hv.2)).le)
    (fun j x hx z hz hxz u hu w hw hwz => (hper j).2.2.2.2 x hx z hz hxz u w hu.1 hw
      (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hu.2) hwz)
  let η := pairedCoordinates f
  have hηq : η q = 0 := by
    ext j
    rw [pairedCoordinates_apply, hfq]
    rfl
  have hnormConst : Real.sqrt (1 + τ) + Real.sqrt 2 * ε ≤ 1 + γ / 4 := by
    have hsτ : Real.sqrt (1 + τ) ≤ 1 + τ := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · linarith
      · nlinarith
    have hs2 : Real.sqrt 2 ≤ 2 := by norm_num
    have hm := mul_le_mul_of_nonneg_right hs2 hε.le
    dsimp [ε] at *
    linarith
  have hDbound : ∀ x ∈ Metric.ball q 3, ∀ w : TangentSpace I x,
      ‖mvfderiv (I := I) η x w‖ ≤ (1 + γ / 4) * ‖w‖ := by
    intro x hx w
    exact ((hD x hx).2 w).trans (mul_le_mul_of_nonneg_right hnormConst (norm_nonneg w))
  have hLip : ∀ x ∈ Metric.ball q 1, ∀ y ∈ Metric.ball q 1,
      ‖η x - η y‖ ≤ (1 + γ / 4) * dist x y := by
    intro x hx y hy
    exact pairedCoordinates_lipschitz g hEnorm hf hDbound hx hy
  have hclose : ∀ x ∈ Metric.ball q 1, ‖η x - (F.toFun x).fst‖ < γ / 8 := by
    intro x hx
    have hxR : x ∈ Metric.ball q (R + 3) := Metric.ball_subset_ball (by linarith) hx
    have hh : ‖η x - (F.toFun x).fst‖ ≤ 2 * (ε + τ) := by
      apply rankTwo_norm_le (by positivity)
      intro j
      rw [PiLp.sub_apply, pairedCoordinates_apply]
      have hv := hvalue x hxR j
      exact hv.le.trans (by
        have hd := Metric.mem_ball.mp hx
        nlinarith)
    exact hh.trans_lt (by dsimp [ε] at *; linarith)
  refine ⟨η, pairedCoordinates_smooth hf, hηq, ?_, ?_, hclose, ?_, ?_, ?_⟩
  · intro x hx
    exact (hD x (Metric.ball_subset_ball (by norm_num) hx)).1
  · intro x hx y hy
    exact (hLip x hx y hy).trans
      (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
  · intro x hx
    have hq1 : q ∈ Metric.ball q 1 := Metric.mem_ball_self zero_lt_one
    have hr := hLip x hx q hq1
    rw [hηq, sub_zero] at hr
    have hnorm : ‖η x‖ < 1 + γ / 4 := by
      have hd := Metric.mem_ball.mp hx
      nlinarith [norm_nonneg (η x)]
    let y := (1 + γ / 4)⁻¹ • η x
    have hden : 0 < 1 + γ / 4 := by linarith
    have hy : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hden]
      rw [inv_mul_lt_iff₀ hden]
      simpa using hnorm
    have heq : η x - y = (γ / 4 / (1 + γ / 4)) • η x := by
      have hc : 1 - (1 + γ / 4)⁻¹ = γ / 4 / (1 + γ / 4) := by
        field_simp
        ring
      calc η x - y = (1 - (1 + γ / 4)⁻¹) • η x := by
             rw [sub_smul, one_smul]
        _ = _ := by rw [hc]
    have hdist : dist (η x) y < γ := by
      rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < γ / 4 / (1 + γ / 4))]
      have hh := mul_lt_mul_of_pos_left hnorm
        (by positivity : 0 < γ / 4 / (1 + γ / 4))
      have hc : (γ / 4 / (1 + γ / 4)) * (1 + γ / 4) = γ / 4 :=
        div_mul_cancel₀ _ hden.ne'
      rw [hc] at hh
      linarith
    exact (Metric.infDist_le_dist_of_mem hy).trans_lt hdist
  · exact exists_mem_ball_near_of_splitting F (by linarith) (by linarith) hclose
  · intro x hx z hz hxz w hw hwz
    exact (htest x hx z (Metric.ball_subset_ball (by linarith) hz) hxz w hw hwz).trans_lt
      (by dsimp [ε] at *; linarith)

end DifferentialGeometry.Geometry.Collapse
