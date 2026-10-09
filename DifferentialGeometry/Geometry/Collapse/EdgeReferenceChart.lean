import DifferentialGeometry.Geometry.Comparison.Toponogov.LongRankTwoAnchors
import DifferentialGeometry.Geometry.Collapse.EdgeScaledSmoothing
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Gradient
import DifferentialGeometry.Geometry.Comparison.VectorAdaptedStability
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Smooth reference coordinates from the actual prescribed long anchors

The distance smoothings use the same supplied rank-two anchors. Their gradients
are close to every genuine minimizing direction throughout the closed buffer,
and their values and derivatives retain the original splitting coordinates.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold
open scoped Manifold ContDiff ENNReal Topology RealInnerProductSpace
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_smooth_long_reference_parameters {b ρ ε R : ℝ}
    (hb : 0 < b) (hρ : 2 ≤ ρ) (hbρ : b < ρ) (hρR : ρ < R)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ s₀ > 2 * (R + 3) + 10, ∃ ν₀ > 0, ∀ s, s₀ ≤ s → ∃ k₀ > 0,
      ∀ ν k, 0 < ν → ν < ν₀ → 0 < k → k ≤ k₀ →
      ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type*) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type*) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type*) [MetricSpace Y] (o : M) (y₀ : Y)
        (F : KleinerLottApprox o (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), y₀)) ν)
        (A B : Fin 2 → M),
      (∀ y ∈ Metric.ball o (8 * (s + R + 4)),
        SectionalBoundedBelowAt g y (-k ^ 2)) →
      (∀ j, A j ∈ Metric.ball o ν⁻¹) → (∀ j, B j ∈ Metric.ball o ν⁻¹) →
      (∀ j, dist (F.toFun (A j)) (rankTwoAxisPoint j s y₀) < 2 * ν) →
      (∀ j, dist (F.toFun (B j)) (rankTwoAxisPoint j (-s) y₀) < 2 * ν) →
      ∃ f : Fin 2 → M → ℝ,
        (∀ j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f j) (Metric.ball o b)) ∧
        (∀ j, f j o = 0) ∧
        (∀ j, ∀ x ∈ Metric.ball o b,
          ∀ v ∈ minimizingDirectionsTo g hEnorm {A j} x,
          Real.sqrt (g.inner x (gradFun g (f j) x - v) (gradFun g (f j) x - v)) < ε) ∧
        (∀ j, ∀ x ∈ Metric.ball o (R + 3),
          |f j x - (F.toFun x).fst j| < ε * dist x o + ε ^ 2 / 40) ∧
        (∀ j, ∀ x ∈ Metric.ball o b, ∀ z ∈ Metric.ball o (R + 3),
          1 / 2 < dist x z → ∀ W : TangentSpace I x, g.inner x W W = 1 →
          intrinsicGeodesic g hEnorm x W (dist x z) = z →
          |mvfderiv (I := I) (f j) x W -
            ((F.toFun z).fst j - (F.toFun x).fst j) / dist x z| < ε + ε ^ 2 / 40) ∧
        ∀ x ∈ Metric.ball o b, ∀ i j : Fin 2,
          |g.inner x (gradFun g (f i) x) (gradFun g (f j) x) -
            (if i = j then 1 else 0)| < ε ^ 2 / 40 + 2 * ε + ε ^ 2
    := by
  let τ := ε ^ 2 / 40
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨s₀, hs₀, ν₀, hν₀, hparameters⟩ :=
    exists_long_rankTwo_anchor_parameters hρ hρR hτ
  refine ⟨s₀, hs₀, ν₀, hν₀, ?_⟩
  intro s hs
  obtain ⟨k₀, hk₀, hproduce⟩ := hparameters s hs
  refine ⟨k₀, hk₀, ?_⟩
  intro ν k hν hνsmall hk hksmall E hnorm hspace hfinite hne H htop I hboundary
    M hdist hcharts hmanifold hsigma hcomplete hRB hRiem hcontinuous g hEnorm
    Y hY o y₀ F A B hsec hA hB hFA hFB
  obtain ⟨hper, hgram⟩ := hproduce ν k hν hνsmall hk hksmall
    E H I M g hEnorm Y o y₀ F A B hsec hA hB hFA hFB
  let : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  have haway (j : Fin 2) : A j ∉ Metric.ball o ρ := by
    have hr := (F.coordinateSplitting j).supplied_anchor_radius_error
      (A j) (hA j) (by
        simpa only [KleinerLottApprox.coordinateSplitting_anchor_dist] using hFA j)
    rw [abs_of_pos (by linarith : 0 < s)] at hr
    intro ha
    have hd : dist o (A j) < ρ := by simpa only [dist_comm] using Metric.mem_ball.mp ha
    linarith [(abs_lt.mp hr).1, F.error_lt_one]
  have hsmoothing (j : Fin 2) : ∃ D : M → ℝ, ∃ O : Set M,
      IsOpen O ∧ Metric.closedBall o b ⊆ O ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ D O ∧
      (∀ x y, |(D x - dist x (A j)) - (D y - dist y (A j))| ≤ ε * dist x y) ∧
      ∀ x ∈ Metric.closedBall o b,
        ∀ v ∈ minimizingDirectionsTo g hEnorm {A j} x,
        Real.sqrt (g.inner x (gradFun g D x + v) (gradFun g D x + v)) < ε := by
    obtain ⟨θ, hθ, hθsmall, hd⟩ := (hper j).2.1
    have hUA : Metric.ball o ρ ⊆ ({A j} : Set M)ᶜ := by
      intro x hx hxa
      exact haway j ((mem_singleton_iff.mp hxa) ▸ hx)
    have hdiam : ∀ x ∈ Metric.ball o ρ,
        ∀ U ∈ minimizingDirectionsTo g hEnorm {A j} x,
        ∀ V ∈ minimizingDirectionsTo g hEnorm {A j} x,
        Real.sqrt (g.inner x (U - V) (U - V)) ≤ θ := by
      intro x hx U hU V hV
      apply hd x hx U V hU.1 hV.1
      · simpa only [Metric.infDist_singleton, mem_singleton_iff] using hU.2
      · simpa only [Metric.infDist_singleton, mem_singleton_iff] using hV.2
    obtain ⟨D, O, hO, hCO, hDO, hclose, hout, hdiff, hLip, hgrad⟩ :=
      exists_distance_smoothing_with_gradient g hEnorm hε hε1 isClosed_singleton
        (singleton_nonempty (A j)) Metric.isOpen_ball hUA hdiam
        (hθsmall.trans (by dsimp [τ]; nlinarith [sq_pos_of_pos hε]))
        (isCompact_closedBall o b)
        (fun x hx => Metric.mem_ball.mpr
          (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) hbρ))
        (e := b) hb
    exact ⟨D, O, hO, hCO, hDO, by simpa only [Metric.infDist_singleton] using hdiff, hgrad⟩
  choose D O hO hCO hDO hdiff hgrad using hsmoothing
  let f : Fin 2 → M → ℝ := fun j x => D j o - D j x
  have hball (x : M) (hx : x ∈ Metric.ball o b) :
      x ∈ Metric.closedBall o b :=
    Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le
  have hdiffD (j : Fin 2) (x : M) (hx : x ∈ Metric.ball o b) :
      MDifferentiableAt I 𝓘(ℝ, ℝ) (D j) x :=
    ((hDO j).contMDiffAt ((hO j).mem_nhds (hCO j (hball x hx)))).mdifferentiableAt
      (by simp)
  have hgf (j : Fin 2) (x : M) (hx : x ∈ Metric.ball o b) :
      gradFun g (f j) x = -gradFun g (D j) x := by
    change gradFun g (fun y => D j o - D j y) x = _
    rw [DifferentialGeometry.Geometry.Connection.gradFun_sub g
      mdifferentiableAt_const (hdiffD j x hx),
      DifferentialGeometry.Geometry.Connection.gradFun_const, zero_sub]
  have hfgrad (j : Fin 2) (x : M) (hx : x ∈ Metric.ball o b)
      (v : TangentSpace I x) (hv : v ∈ minimizingDirectionsTo g hEnorm {A j} x) :
      ‖gradFun g (f j) x - v‖ < ε := by
    rw [hgf j x hx, show -gradFun g (D j) x - v = -(gradFun g (D j) x + v) by abel,
      norm_neg]
    simpa only [norm_tangent_eq_sqrt_gInner hEnorm] using hgrad j x (hball x hx) v hv
  have hdir (j : Fin 2) (x : M) (hx : x ∈ Metric.ball o b) :
      ∃ v, v ∈ minimizingDirectionsTo g hEnorm {A j} x := by
    have hx4 := Metric.ball_subset_ball hbρ.le hx
    have hpos : 0 < dist x (A j) := dist_pos.mpr (by
      intro heq
      exact haway j (heq ▸ hx4))
    obtain ⟨v, hv, hend⟩ := soul_unit_minimizing_initial g hEnorm x (A j) hpos
    exact ⟨v, hv, by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hend⟩
  have hn {x : M} (v : TangentSpace I x) (hv : g.inner x v v = 1) : ‖v‖ = 1 := by
    rw [norm_tangent_eq_sqrt_gInner hEnorm, hv, Real.sqrt_one]
  refine ⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (contMDiffOn_const.sub (hDO j)).mono (fun x hx => hCO j (hball x hx))
  · intro j
    simp only [f, sub_self]
  · intro j x hx v hv
    simpa only [norm_tangent_eq_sqrt_gInner hEnorm] using hfgrad j x hx v hv
  · intro j x hx
    have hh := hdiff j o x
    have ht := (hper j).1 x hx
    have he : |f j x - (dist o (A j) - dist x (A j))| ≤ ε * dist x o := by
      convert hh using 1
      · congr 1
        dsimp [f]
        ring
      · rw [dist_comm]
    exact (abs_sub_le (f j x) (dist o (A j) - dist x (A j))
      ((F.toFun x).fst j)).trans_lt (add_lt_add_of_le_of_lt he ht)
  · intro j x hx z hz hxz W hW hWz
    have hx301 := hx
    obtain ⟨v, hv⟩ := hdir j x hx
    have ht := (hper j).2.2 x (Metric.ball_subset_ball hbρ.le hx) z hz
      hxz v W hv.1 hW
      (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using hv.2) hWz
    have hg := inner_gradFun g (f j) x W
    have he := abs_real_inner_le_norm (gradFun g (f j) x - v) W
    rw [hn W hW, mul_one, inner_sub_left, hEnorm.inner_eq, hEnorm.inner_eq] at he
    change g.inner x (gradFun g (f j) x) W = mvfderiv (I := I) (f j) x W at hg
    rw [hg] at he
    exact (abs_sub_le (mvfderiv (I := I) (f j) x W) (g.inner x v W)
      (((F.toFun z).fst j - (F.toFun x).fst j) / dist x z)).trans_lt
        (add_lt_add (he.trans_lt (hfgrad j x hx301 v hv)) ht)
  · intro x hx i j
    have hx301 := hx
    choose v hv using fun j : Fin 2 => hdir j x hx
    have hnear (j : Fin 2) : ‖gradFun g (f j) x - v j‖ < ε :=
      hfgrad j x hx301 (v j) (hv j)
    have hvnorm (j : Fin 2) : ‖v j‖ = 1 := hn (v j) (hv j).1
    have hw (j : Fin 2) : ‖gradFun g (f j) x‖ < 1 + ε := by
      have hh := norm_le_norm_sub_add (gradFun g (f j) x) (v j)
      rw [hvnorm] at hh
      linarith [hnear j]
    have hmixed : |g.inner x (v 0) (v 1)| ≤ τ :=
      (hgram x (Metric.ball_subset_ball hbρ.le hx) (v 0) (v 1)
        (hv 0).1 (hv 1).1
        (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using (hv 0).2)
        (by simpa only [Metric.infDist_singleton, mem_singleton_iff] using (hv 1).2)).le
    have hgeometry : |g.inner x (v i) (v j) - (if i = j then 1 else 0)| ≤ τ := by
      fin_cases i <;> fin_cases j
      · change |g.inner x (v 0) (v 0) - 1| ≤ τ
        rw [(hv 0).1, sub_self, abs_zero]
        exact hτ.le
      · change |g.inner x (v 0) (v 1) - 0| ≤ τ
        simpa only [sub_zero] using hmixed
      · change |g.inner x (v 1) (v 0) - 0| ≤ τ
        rw [sub_zero, g.symm x (v 1) (v 0)]
        exact hmixed
      · change |g.inner x (v 1) (v 1) - 1| ≤ τ
        rw [(hv 1).1, sub_self, abs_zero]
        exact hτ.le
    have herror : |g.inner x (gradFun g (f i) x) (gradFun g (f j) x) -
        g.inner x (v i) (v j)| < 2 * ε + ε ^ 2 := by
      have heq : inner ℝ (gradFun g (f i) x) (gradFun g (f j) x) -
          inner ℝ (v i) (v j) =
          inner ℝ (gradFun g (f i) x - v i) (gradFun g (f j) x) +
            inner ℝ (v i) (gradFun g (f j) x - v j) := by
        simp only [inner_sub_left, inner_sub_right]
        ring
      rw [← hEnorm.inner_eq, ← hEnorm.inner_eq, heq]
      have h1 := abs_real_inner_le_norm (gradFun g (f i) x - v i) (gradFun g (f j) x)
      have h2 := abs_real_inner_le_norm (v i) (gradFun g (f j) x - v j)
      rw [hvnorm i, one_mul] at h2
      have hp : ‖gradFun g (f i) x - v i‖ * ‖gradFun g (f j) x‖ < ε * (1 + ε) :=
        mul_lt_mul'' (hnear i) (hw j) (norm_nonneg _) (norm_nonneg _)
      exact (abs_add_le _ _).trans_lt (by nlinarith [hnear j])
    exact (abs_sub_le (g.inner x (gradFun g (f i) x) (gradFun g (f j) x))
      (g.inner x (v i) (v j)) (if i = j then 1 else 0)).trans_lt
        (by dsimp [τ] at hgeometry; linarith)

section LinearGram

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

private theorem rankTwo_adjoint_apply (L : V →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : Fin 2 → V) (hL : ∀ v i, L v i = inner ℝ (w i) v)
    (y : EuclideanSpace ℝ (Fin 2)) : L.adjoint y = y 0 • w 0 + y 1 • w 1 := by
  apply ext_inner_right ℝ
  intro v
  rw [L.adjoint_inner_left, PiLp.inner_apply, Fin.sum_univ_two,
    _root_.inner_add_left, real_inner_smul_left, real_inner_smul_left]
  simp only [RCLike.inner_apply, conj_trivial, hL]
  ring

private theorem rankTwo_gram_apply (L : V →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : Fin 2 → V) (hL : ∀ v i, L v i = inner ℝ (w i) v)
    (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    (L.comp L.adjoint - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) y i =
      y 0 * (inner ℝ (w i) (w 0) - (if i = 0 then 1 else 0)) +
        y 1 * (inner ℝ (w i) (w 1) - (if i = 1 then 1 else 0)) := by
  have hy : y i = y 0 * (if i = 0 then 1 else 0) + y 1 * (if i = 1 then 1 else 0) := by
    fin_cases i <;> simp
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, PiLp.sub_apply, hL, rankTwo_adjoint_apply L w hL y,
    _root_.inner_add_right, real_inner_smul_right]
  rw [hy]
  ring

theorem rankTwo_gram_operator_bound (L : V →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : Fin 2 → V) {c : ℝ} (hc : 0 ≤ c)
    (hL : ∀ v i, L v i = inner ℝ (w i) v)
    (hgram : ∀ i j, |inner ℝ (w i) (w j) - (if i = j then 1 else 0)| ≤ c) :
    ‖L.comp L.adjoint - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖ ≤ 4 * c := by
  let A := L.comp L.adjoint - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))
  have hbound (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : |A y i| ≤ 2 * c * ‖y‖ := by
    rw [rankTwo_gram_apply L w hL]
    have h0 : |y 0| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y 0
    have h1 : |y 1| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y 1
    exact (abs_add_le _ _).trans (by
      rw [abs_mul, abs_mul]
      have t0 := mul_le_mul h0 (hgram i 0) (abs_nonneg _) (norm_nonneg _)
      have t1 := mul_le_mul h1 (hgram i 1) (abs_nonneg _) (norm_nonneg _)
      nlinarith)
  have hn := DifferentialGeometry.Geometry.Comparison.opNorm_le_of_components
    (L := A) (by positivity : 0 ≤ 2 * c) (fun y => hbound y 0) (fun y => hbound y 1)
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  exact hn.trans (by nlinarith)

theorem rankTwo_operator_bound_of_gram (L : V →L[ℝ] EuclideanSpace ℝ (Fin 2))
    {c : ℝ} (hc : 0 ≤ c)
    (hgram : ‖L.comp L.adjoint -
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖ ≤ c) :
    ‖L‖ ≤ Real.sqrt (1 + c) := by
  have hnorm := ContinuousLinearMap.norm_adjoint_comp_self L.adjoint
  rw [ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map] at hnorm
  have htri := norm_le_norm_sub_add (L.comp L.adjoint)
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))
  have hid : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + c)
  nlinarith [Real.sqrt_nonneg (1 + c), norm_nonneg L]


end LinearGram

section Packing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

def edgeReferenceCoordinates (f : Fin 2 → M → ℝ) : M → EuclideanSpace ℝ (Fin 2) :=
  fun x => WithLp.toLp 2 (fun j => f j x)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem edgeReferenceCoordinates_smooth {f : Fin 2 → M → ℝ} {U : Set M}
    (hf : ∀ j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f j) U) :
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ (edgeReferenceCoordinates f) U :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _j : Fin 2 => ℝ)).symm.contDiff.contMDiff.comp_contMDiffOn
    ((contMDiffOn_pi_space).2 hf)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem edgeReferenceCoordinates_derivative {f : Fin 2 → M → ℝ} {x : M}
    (hf : ∀ j, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (f j) x)
    (v : TangentSpace I x) (j : Fin 2) :
    mvfderiv (I := I) (edgeReferenceCoordinates f) x v j =
      mvfderiv (I := I) (f j) x v := by
  let projection : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _i : Fin 2 => ℝ) j
  have hχ : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (edgeReferenceCoordinates f) x :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _i : Fin 2 => ℝ)).symm.differentiableAt.mdifferentiableAt
      |>.comp x (((contMDiffAt_pi_space).2 hf).mdifferentiableAt (by simp))
  have hprojection : projection ∘ edgeReferenceCoordinates f = f j := rfl
  have hh := _root_.mvfderiv_comp_apply x projection.differentiableAt.mdifferentiableAt hχ v
  rw [hprojection, mvfderiv_eq_fderiv, projection.fderiv] at hh
  exact hh.symm

end Packing

section Covector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

theorem edgeReferenceCoordinates_operator_bound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {f : Fin 2 → M → ℝ} {x : M} {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ j, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (f j) x)
    (hgram : ∀ i j, |g.inner x (gradFun g (f i) x) (gradFun g (f j) x) -
      (if i = j then 1 else 0)| ≤ c) :
    ‖mvfderiv (I := I) (edgeReferenceCoordinates f) x‖ ≤ Real.sqrt (1 + 4 * c) := by
  apply rankTwo_operator_bound_of_gram _ (by positivity)
  apply rankTwo_gram_operator_bound _ (fun j => gradFun g (f j) x) hc
  · intro v i
    rw [edgeReferenceCoordinates_derivative hf]
    have hg := inner_gradFun g (f i) x v
    change g.inner x (gradFun g (f i) x) v = mvfderiv (I := I) (f i) x v at hg
    exact hg.symm.trans (hEnorm.inner_eq x _ _).symm
  · intro i j
    simpa only [hEnorm.inner_eq] using hgram i j

theorem edgeReferenceCoordinates_covector_gradient
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {f : Fin 2 → M → ℝ} {x : M}
    (hf : ∀ j, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (f j) x)
    (e : EuclideanSpace ℝ (Fin 2)) :
    gradFun g (fun y => inner ℝ e (edgeReferenceCoordinates f y)) x =
      (mvfderiv (I := I) (edgeReferenceCoordinates f) x).adjoint e := by
  let P : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := innerSL ℝ e
  have hχ : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (edgeReferenceCoordinates f) x :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _i : Fin 2 => ℝ)).symm.differentiableAt.mdifferentiableAt
      |>.comp x (((contMDiffAt_pi_space).2 hf).mdifferentiableAt (by simp))
  apply (DifferentialGeometry.Geometry.Connection.gradFun_unique g _ ?_).symm
  intro v
  have hh := _root_.mvfderiv_comp_apply x P.differentiableAt.mdifferentiableAt hχ v
  rw [mvfderiv_eq_fderiv, P.fderiv] at hh
  change mvfderiv (I := I) (fun y => inner ℝ e (edgeReferenceCoordinates f y)) x v =
    inner ℝ e (mvfderiv (I := I) (edgeReferenceCoordinates f) x v) at hh
  change g.inner x ((mvfderiv (I := I) (edgeReferenceCoordinates f) x).adjoint e) v = _
  rw [← hEnorm.inner_eq, ContinuousLinearMap.adjoint_inner_left]
  exact hh.symm

end Covector

end DifferentialGeometry.Geometry.Collapse
