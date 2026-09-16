import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.SmoothSolutions

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold Topology ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless]

omit [I.Boundaryless] in
private theorem quadratic_difference_low (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (t : Real) (x : M) :
    lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x)
        (fun i j k l =>
          (forwardUniquenessBRm (I := I) g₁ t x i j k l - forwardUniquenessBRm (I := I) g₂ t x i j k l) -
              (forwardUniquenessBRm (I := I) g₁ t x i j l k - forwardUniquenessBRm (I := I) g₂ t x i j l k) +
            (forwardUniquenessBRm (I := I) g₁ t x i k j l - forwardUniquenessBRm (I := I) g₂ t x i k j l) -
              (forwardUniquenessBRm (I := I) g₁ t x i l j k - forwardUniquenessBRm (I := I) g₂ t x i l j k)) =
      curvatureQuadraticCombination (I := I) (g₁ t) (forwardUniquenessTf (I := I) g₁ t) x -
        curvatureQuadraticCombination (I := I) (g₂ t) (forwardUniquenessTf (I := I) g₂ t) x := by
  rw [← forwardUniquenessB_low (I := I) g₁ g₁ t x, ← forwardUniquenessB_low (I := I) g₁ g₂ t x]
  apply lowOfComp_ext (I := I)
  intro i j k l
  change
    Tensor0SSpace.eval (lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x) _)
        (vec4 (I := I) (coordBasisAt (I := I) x i) (coordBasisAt (I := I) x j)
          (coordBasisAt (I := I) x k) (coordBasisAt (I := I) x l)) -
      Tensor0SSpace.eval (lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x) _)
        (vec4 (I := I) (coordBasisAt (I := I) x i) (coordBasisAt (I := I) x j)
          (coordBasisAt (I := I) x k) (coordBasisAt (I := I) x l)) = _
  rw [lowOfComp_eval, lowOfComp_eval]
  ring

private theorem drift_difference_low (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (t : Real) (x : M) :
    lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x)
        (fun i j k l =>
          riemann04RicciDriftInFrame (forwardUniquenessRicUp (I := I) g₁) (forwardUniquenessRm04 (I := I) g₁)
              t x i j k l -
            riemann04RicciDriftInFrame (forwardUniquenessRicUp (I := I) g₂) (forwardUniquenessRm04 (I := I) g₂)
              t x i j k l) =
      ricciDrift04 (I := I) (g₁ t) x - ricciDrift04 (I := I) (g₂ t) x := by
  rw [← forwardUniquenessDrift_low (I := I) g₁ g₁ t x, ← forwardUniquenessDrift_low (I := I) g₁ g₂ t x]
  apply lowOfComp_ext (I := I)
  intro i j k l
  change
    Tensor0SSpace.eval (lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x) _)
        (vec4 (I := I) (coordBasisAt (I := I) x i) (coordBasisAt (I := I) x j)
          (coordBasisAt (I := I) x k) (coordBasisAt (I := I) x l)) -
      Tensor0SSpace.eval (lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x) _)
        (vec4 (I := I) (coordBasisAt (I := I) x i) (coordBasisAt (I := I) x j)
          (coordBasisAt (I := I) x k) (coordBasisAt (I := I) x l)) = _
  rw [lowOfComp_eval, lowOfComp_eval]

private theorem lower_riemann_cross
    (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    lowerTri (I := I) (metricTensorField (I := I) g₁ x)
        (riemannOp (metricCov (I := I) g₂) x) =
      CovariantDerivative.riemannCurvature04At (I := I) g₁
        (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  have hv : v = vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  calc
    lowerTri (I := I) (metricTensorField (I := I) g₁ x)
        (riemannOp (metricCov (I := I) g₂) x)
        (vec4 (I := I) (v 0) (v 1) (v 2) (v 3)) =
      metricTensorField (I := I) g₁ x
        (fun a : Fin 2 =>
          if a = 0 then
            riemannOp (metricCov (I := I) g₂) x (v 0) (v 1) (v 2)
          else v 3) :=
      lowerTri_apply (I := I) (metricTensorField (I := I) g₁ x)
        (riemannOp (metricCov (I := I) g₂) x)
        (vec4 (I := I) (v 0) (v 1) (v 2) (v 3))
    _ = g₁.inner x (riemannOp (metricCov (I := I) g₂) x (v 0) (v 1) (v 2))
        (v 3) := by
      rw [metricTensorField_apply]
      simp
    _ = CovariantDerivative.riemannCurvature04At (I := I) g₁
        (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x
          (vec4 (I := I) (v 0) (v 1) (v 2) (v 3)) :=
      (rm04mix_inner (I := I) g₁ g₂ x (v 0) (v 1) (v 2) (v 3)).symm

private lemma sq_le_sq_of_nonneg {x y : Real} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 :=
  pow_le_pow_left₀ hx hxy 2

private lemma remainder_kq_factor
    (n BP BR1 BR2 Λ BH d : Real) :
    16 * (4 * n ^ 14 * ((2 + 2 * n ^ 6 * BP) * d) * (BR1 + BR2) +
        2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) *
          d * BR2 ^ 2) =
      (16 * (4 * n ^ 14 * (2 + 2 * n ^ 6 * BP) * (BR1 + BR2) +
        2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) *
          BR2 ^ 2)) * d := by
  ring

private lemma remainder_kd_factor (n BR1 BRic d : Real) :
    32 * n ^ 6 * ((n ^ 4 * d) * BR1 + BRic * d) =
      (32 * n ^ 6 * (n ^ 4 * BR1 + BRic)) * d := by
  ring

private lemma remainder_kr0_factor (n B5 Λ B6 KQ KD d : Real) :
    4 * (50 * n ^ 12 * d * B5 + 2 * n ^ 10 * Λ ^ 2 * d * B6) +
        16 * (KQ * d) + 2 * (KD * d) =
      (200 * n ^ 12 * B5 + 8 * n ^ 10 * Λ ^ 2 * B6 +
        16 * KQ + 2 * KD) * d := by
  ring

private lemma remainder_rg_factor (n BP d : Real) :
    n ^ 6 * ((n ^ 4 * d) * BP) = n ^ 10 * BP * d := by
  ring

private lemma remainder_kg_factor (n BP Ce BSpeed d : Real) :
    2 * (4 * (n ^ 10 * BP * d)) +
        2 * (Ce ^ 6 * n ^ 6 * BSpeed * d) =
      (8 * n ^ 10 * BP + 2 * Ce ^ 6 * n ^ 6 * BSpeed) * d := by
  ring

private lemma remainder_kl_factor (n BP d : Real) :
    n ^ 6 * ((n ^ 6 * BP) * d) = n ^ 12 * BP * d := by
  ring

private lemma remainder_pair_factor (n BP Background d : Real) :
    n ^ 8 * (BP * (4 * n ^ 3 * Background * d)) =
      4 * n ^ 11 * BP * Background * d := by
  ring

private lemma remainder_trace_factor (n BP Background d : Real) :
    n ^ 6 * (4 * n ^ 11 * BP * Background * d) =
      4 * n ^ 17 * BP * Background * d := by
  ring

private lemma remainder_four_term_bound
    {R G L T RG RGL : Real}
    (hRG : RG ≤ 2 * R + 2 * G)
    (hRGL : RGL ≤ 2 * RG + 2 * L) :
    2 * RGL + 2 * T ≤ 8 * R + 8 * G + 4 * L + 2 * T := by
  linarith

private lemma remainder_four_term_mono
    {R G L T KR KG KL KT d : Real}
    (hR : R ≤ KR * d) (hG : G ≤ KG * d)
    (hL : L ≤ KL * d) (hT : T ≤ KT * d) :
    8 * R + 8 * G + 4 * L + 2 * T ≤
      8 * (KR * d) + 8 * (KG * d) + 4 * (KL * d) + 2 * (KT * d) := by
  linarith

private lemma remainder_total_factor (KR KG KL KT d : Real) :
    8 * (KR * d) + 8 * (KG * d) + 4 * (KL * d) + 2 * (KT * d) =
      (8 * KR + 8 * KG + 4 * KL + 2 * KT) * d := by
  ring

theorem forward_uniqueness_remainder_norm_sq_le
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M)
    {Λ Ce BH BR1 BR2 BP BRic21 B5 B6 BP1 BP2 BR2g2 BRic2g2 B6g2 Background : ℝ}
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v)
    (hCe : 1 ≤ Ce)
    (hEquiv : ∀ v : TangentSpace I x,
      Ce⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ Ce * (g₁ t).inner x v v)
    (hBH : metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ BH)
    (hBR1 : normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ BR1)
    (hBR2 : normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ BR2)
    (hBP : normSq0S (I := I) (g₁ t) x 4
      (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t)
        (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) x) ≤ BP)
    (hBRic21 : normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₂ t) x) ≤ BRic21)
    (hB5 : normSq0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t))) x) ≤ B5)
    (hB6 : normSq0S (I := I) (g₁ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)))) x) ≤ B6)
    (hBP1 : normSq0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₁ t)
        (CovariantDerivative.rm04Section (I := I) (g₁ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t))) x) ≤ BP1)
    (hBP2 : normSq0S (I := I) (g₁ t) x 6
      (metricNabla0S (I := I) (g₁ t) (metricNabla0S (I := I) (g₁ t)
        (CovariantDerivative.rm04Section (I := I) (g₁ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)))) x) ≤ BP2)
    (hBR2g2 : normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ BR2g2)
    (hBRic2g2 : normSq0S (I := I) (g₂ t) x 2 (metricRicciAt (I := I) (g₂ t) x) ≤ BRic2g2)
    (hB6g2 : normSq0S (I := I) (g₂ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)))) x) ≤ B6g2)
    (hBackground : normSq0S (I := I) (g₁ t) x 2 (metricTensorField (I := I) (g₂ t) x) ≤ Background) :
    let n : Real := Module.finrank Real E
    let KQ : Real :=
      16 * (4 * n ^ 14 * (2 + 2 * n ^ 6 * BP) * (BR1 + BR2) +
          2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) * BR2 ^ 2)
    let KD : Real := 32 * n ^ 6 * (n ^ 4 * BR1 + BRic21)
    let KR0 : Real :=
      200 * n ^ 12 * B5 + 8 * n ^ 10 * Λ ^ 2 * B6 + 16 * KQ + 2 * KD
    let BSpeed : Real :=
      8 * n ^ 6 * B6g2 + 512 * n ^ 14 * BR2g2 ^ 2 +
          72 * n ^ 6 * (BRic2g2 * BR2g2)
    let KG : Real := 8 * n ^ 10 * BP + 2 * Ce ^ 6 * n ^ 6 * BSpeed
    let KL : Real := n ^ 12 * BP2
    let KT : Real := 4 * n ^ 17 * BP1 * Background
    let C_rem : Real := 8 * KR0 + 8 * KG + 4 * KL + 2 * KT
    normSq0S (I := I) (g₁ t) x 4 (forwardUniquenessRem (I := I) g₁ g₂ t x) ≤
      C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have hBH0 : 0 ≤ BH := by
    rw [metricDiffSq_def] at hBH
    exact (normSq0S_nonneg (I := I) (g₁ t) x 2 _).trans hBH
  have hBR10 : 0 ≤ BR1 := (normSq0S_nonneg (I := I) (g₁ t) x 4 _).trans hBR1
  have hBR20 : 0 ≤ BR2 := (normSq0S_nonneg (I := I) (g₁ t) x 4 _).trans hBR2
  have hBP0 : 0 ≤ BP := (normSq0S_nonneg (I := I) (g₁ t) x 4 _).trans hBP
  have hBRic210 : 0 ≤ BRic21 := (normSq0S_nonneg (I := I) (g₁ t) x 2 _).trans hBRic21
  have hB50 : 0 ≤ B5 := (normSq0S_nonneg (I := I) (g₁ t) x 5 _).trans hB5
  have hB60 : 0 ≤ B6 := (normSq0S_nonneg (I := I) (g₁ t) x 6 _).trans hB6
  have hBP10 : 0 ≤ BP1 := (normSq0S_nonneg (I := I) (g₁ t) x 5 _).trans hBP1
  have hBP20 : 0 ≤ BP2 := (normSq0S_nonneg (I := I) (g₁ t) x 6 _).trans hBP2
  have hBR2g20 : 0 ≤ BR2g2 := (normSq0S_nonneg (I := I) (g₂ t) x 4 _).trans hBR2g2
  have hBRic2g20 : 0 ≤ BRic2g2 := (normSq0S_nonneg (I := I) (g₂ t) x 2 _).trans hBRic2g2
  have hB6g20 : 0 ≤ B6g2 := (normSq0S_nonneg (I := I) (g₂ t) x 6 _).trans hB6g2
  let n : Real := Module.finrank Real E
  let KQ : Real :=
    16 * (4 * n ^ 14 * (2 + 2 * n ^ 6 * BP) * (BR1 + BR2) +
      2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) * BR2 ^ 2)
  let KD : Real := 32 * n ^ 6 * (n ^ 4 * BR1 + BRic21)
  let KR0 : Real :=
    200 * n ^ 12 * B5 + 8 * n ^ 10 * Λ ^ 2 * B6 + 16 * KQ + 2 * KD
  let BSpeed : Real :=
    8 * n ^ 6 * B6g2 + 512 * n ^ 14 * BR2g2 ^ 2 +
      72 * n ^ 6 * (BRic2g2 * BR2g2)
  let KG : Real := 8 * n ^ 10 * BP + 2 * Ce ^ 6 * n ^ 6 * BSpeed
  let KL : Real := n ^ 12 * BP2
  let KT : Real := 4 * n ^ 17 * BP1 * Background
  let C_rem : Real := 8 * KR0 + 8 * KG + 4 * KL + 2 * KT
  let d : Real := forwardUniqueDensity (I := I) g₁ g₂ t x
  let P : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4 :=
    forwardUniquenessTf (I := I) g₁ t - forwardUniquenessSfield (I := I) g₁ g₂ t
  let R0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x)
      (rmDotRem (I := I) (g₁ t) (g₂ t) (forwardUniquenessTf (I := I) g₂ t)
        (forwardUniquenessRm04 (I := I) g₁) (forwardUniquenessRm04 (I := I) g₂)
        (forwardUniquenessBRm (I := I) g₁) (forwardUniquenessBRm (I := I) g₂)
        (forwardUniquenessRicUp (I := I) g₁) (forwardUniquenessRicUp (I := I) g₂)
        (fun m z => coordBasisAt (I := I) z m) t x)
  let V₂ :
      TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
        TangentSpace I x :=
    uhlRm2Vec (I := I) g₂ (coordBasisAt (I := I))
      (forwardUniquenessRm04 (I := I) g₂) (forwardUniquenessLapRm (I := I) g₂) (forwardUniquenessBRm (I := I) g₂)
      (forwardUniquenessRicUp (I := I) g₂) t x
  let G : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    gapDot (I := I) (g₁ t) (g₂ t) V₂
  let L : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    (reLower (I := I) (g₂ t) (g₁ t) (roughLap0SField (I := I) (g₁ t) P) -
      roughLap0SField (I := I) (g₁ t) P) x
  let K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
    lapDiffFlux (I := I) (g₁ t) (g₂ t) (metricTensorField (I := I) (g₂ t))
  let T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    metricTraceFirstTwoField (I := I) (M := M) (s := 4) (g₁ t)
      (reLowerPair (I := I) (g₁ t) (metricNabla0S (I := I) (g₁ t) P) K) x
  have hR0 : normSq0S (I := I) (g₁ t) x 4 R0 ≤ KR0 * d := by
    have hn : 0 ≤ n := by
      dsimp only [n]
      positivity
    have hd : 0 ≤ d := by
      simpa only [d] using density_nonneg (I := I) g₁ g₂ t x
    have hmetric :
        metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ d := by
      simpa only [d] using metricDiffSq_le_dens (I := I) g₁ g₂ t x
    have hconn :
        connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x ≤ d := by
      simpa only [d] using connectionDifferenceSq_le_dens (I := I) g₁ g₂ t x
    have hrm :
        rmDiffSq (I := I) (g₁ t) (g₂ t) x ≤ d := by
      simpa only [d] using rmDiffSq_le_dens (I := I) g₁ g₂ t x
    have hTf1 :
        normSq0S (I := I) (g₁ t) x 4 (forwardUniquenessTf (I := I) g₁ t x) ≤ BR1 := by
      simpa only [forwardUniquenessTf_apply, metricRm04At] using hBR1
    have hTf2 :
        normSq0S (I := I) (g₁ t) x 4 (forwardUniquenessTf (I := I) g₂ t x) ≤ BR2 := by
      simpa only [forwardUniquenessTf_apply, metricRm04At] using hBR2
    have hown0 := ownRmDiffSq_le (I := I) (g₁ t) (g₂ t) x (hBP)
    have hown :
        normSq0S (I := I) (g₁ t) x 4
            (forwardUniquenessTf (I := I) g₁ t x - forwardUniquenessTf (I := I) g₂ t x) ≤
          (2 + 2 * n ^ 6 * BP) * d := by
      calc
        normSq0S (I := I) (g₁ t) x 4
            (forwardUniquenessTf (I := I) g₁ t x - forwardUniquenessTf (I := I) g₂ t x) ≤
            2 * rmDiffSq (I := I) (g₁ t) (g₂ t) x +
              2 * n ^ 6 * BP * metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
          simpa only [forwardUniquenessTf_apply, metricRm04At, n] using hown0
        _ ≤ 2 * d + 2 * n ^ 6 * BP * d := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hrm (by norm_num))
            (mul_le_mul_of_nonneg_left hmetric
              (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hn 6)) hBP0))
        _ = (2 + 2 * n ^ 6 * BP) * d := by rw [add_mul]
    have hsum :
        normSq0S (I := I) (g₁ t) x 4 (forwardUniquenessTf (I := I) g₁ t x) +
            normSq0S (I := I) (g₁ t) x 4 (forwardUniquenessTf (I := I) g₂ t x) ≤
          BR1 + BR2 :=
      add_le_add hTf1 hTf2
    have hTf20 :
        0 ≤ normSq0S (I := I) (g₁ t) x 4 (forwardUniquenessTf (I := I) g₂ t x) :=
      normSq0S_nonneg (I := I) (g₁ t) x 4 _
    have hTf10 :
        0 ≤ normSq0S (I := I) (g₁ t) x 4 (forwardUniquenessTf (I := I) g₁ t x) :=
      normSq0S_nonneg (I := I) (g₁ t) x 4 _
    have hTf2sq :
        normSq0S (I := I) (g₁ t) x 4 (forwardUniquenessTf (I := I) g₂ t x) ^ 2 ≤ BR2 ^ 2 := by
      exact sq_le_sq_of_nonneg hTf20 hTf2
    have hQ0 := curvatureQuadraticCombination_difference_norm_sq_le (I := I) (g₁ t) (g₂ t)
      (forwardUniquenessTf (I := I) g₁ t) (forwardUniquenessTf (I := I) g₂ t) x hΛ0
      (hΛ) (hBH)
    have hQ :
        normSq0S (I := I) (g₁ t) x 4
            (lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x)
              (fun i j k l =>
                (forwardUniquenessBRm (I := I) g₁ t x i j k l - forwardUniquenessBRm (I := I) g₂ t x i j k l) -
                    (forwardUniquenessBRm (I := I) g₁ t x i j l k -
                      forwardUniquenessBRm (I := I) g₂ t x i j l k) +
                  (forwardUniquenessBRm (I := I) g₁ t x i k j l -
                    forwardUniquenessBRm (I := I) g₂ t x i k j l) -
                    (forwardUniquenessBRm (I := I) g₁ t x i l j k -
                      forwardUniquenessBRm (I := I) g₂ t x i l j k))) ≤
          KQ * d := by
      rw [quadratic_difference_low (I := I) g₁ g₂ t x]
      let ND := normSq0S (I := I) (g₁ t) x 4
        (forwardUniquenessTf (I := I) g₁ t x - forwardUniquenessTf (I := I) g₂ t x)
      let N1 := normSq0S (I := I) (g₁ t) x 4 (forwardUniquenessTf (I := I) g₁ t x)
      let N2 := normSq0S (I := I) (g₁ t) x 4 (forwardUniquenessTf (I := I) g₂ t x)
      let HM := metricDiffSq (I := I) (g₁ t) (g₂ t) x
      have hQ0' :
          normSq0S (I := I) (g₁ t) x 4
              (curvatureQuadraticCombination (I := I) (g₁ t) (forwardUniquenessTf (I := I) g₁ t) x -
                curvatureQuadraticCombination (I := I) (g₂ t) (forwardUniquenessTf (I := I) g₂ t) x) ≤
            16 * (4 * n ^ 14 * ND * (N1 + N2) +
              2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) *
                HM * N2 ^ 2) := by
        simpa only [ND, N1, N2, HM, n] using hQ0
      have hND : ND ≤ (2 + 2 * n ^ 6 * BP) * d := by
        simpa only [ND] using hown
      have hNsum : N1 + N2 ≤ BR1 + BR2 := by
        simpa only [N1, N2] using hsum
      have hNsum0 : 0 ≤ N1 + N2 := by
        simpa only [N1, N2] using add_nonneg hTf10 hTf20
      have hCD0 : 0 ≤ (2 + 2 * n ^ 6 * BP) * d := by
        exact mul_nonneg (by positivity) hd
      have hprod1 :
          ND * (N1 + N2) ≤ ((2 + 2 * n ^ 6 * BP) * d) * (BR1 + BR2) :=
        mul_le_mul hND hNsum hNsum0 hCD0
      have hterm1 :
          4 * n ^ 14 * ND * (N1 + N2) ≤
            4 * n ^ 14 * ((2 + 2 * n ^ 6 * BP) * d) * (BR1 + BR2) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hprod1 (mul_nonneg (by norm_num) (pow_nonneg hn 14))
      have hN2sq : N2 ^ 2 ≤ BR2 ^ 2 := by
        simpa only [N2] using hTf2sq
      have hHM : HM ≤ d := by
        simpa only [HM] using hmetric
      have hprod2 : HM * N2 ^ 2 ≤ d * BR2 ^ 2 :=
        mul_le_mul hHM hN2sq (sq_nonneg _) hd
      have hcoef2 :
          0 ≤ 2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) := by
        positivity
      have hterm2 :
          2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) * HM * N2 ^ 2 ≤
            2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) * d *
              BR2 ^ 2 := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod2 hcoef2
      refine hQ0'.trans ?_
      dsimp only [KQ]
      calc
        _ ≤ 16 * (4 * n ^ 14 * ((2 + 2 * n ^ 6 * BP) * d) * (BR1 + BR2) +
            2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) *
              d * BR2 ^ 2) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)
        _ = (16 * (4 * n ^ 14 * (2 + 2 * n ^ 6 * BP) * (BR1 + BR2) +
              2 * (6 * n ^ 18 * Λ ^ 2 + 4 * n ^ 22 * Λ ^ 4 * BH) *
                BR2 ^ 2)) * d :=
          remainder_kq_factor n BP BR1 BR2 Λ BH d
    have hD0 := ricciDriftSq_le (I := I) (g₁ t) (g₂ t) x
    have hRicDiff := ricciSlabLe (I := I) g₁ g₂ t x
    have hRicDiffUpper0 : 0 ≤ n ^ 4 * d :=
      mul_nonneg (pow_nonneg hn 4) hd
    have hRic2zero :
        0 ≤ normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₂ t) x) :=
      normSq0S_nonneg (I := I) (g₁ t) x 2 _
    have hrm0 : 0 ≤ rmDiffSq (I := I) (g₁ t) (g₂ t) x := by
      rw [rmDiffSq_def]
      exact normSq0S_nonneg (I := I) (g₁ t) x 4 _
    have hDprod1 :
        normSq0S (I := I) (g₁ t) x 2
              (metricRicciAt (I := I) (g₁ t) x -
                metricRicciAt (I := I) (g₂ t) x) *
            normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤
          (n ^ 4 * d) * BR1 := by
      have hRm1 :
          normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤
            BR1 := by
        simpa only [forwardUniquenessTf_apply] using hTf1
      exact mul_le_mul hRicDiff hRm1
        (normSq0S_nonneg (I := I) (g₁ t) x 4 _) hRicDiffUpper0
    have hDprod2 :
        normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₂ t) x) *
            rmDiffSq (I := I) (g₁ t) (g₂ t) x ≤
          BRic21 * d :=
      mul_le_mul (hBRic21) hrm hrm0 hBRic210
    have hD :
        normSq0S (I := I) (g₁ t) x 4
            (lowOfComp (I := I) (g₁ t) (coordBasisAt (I := I) x)
              (fun i j k l =>
                riemann04RicciDriftInFrame (forwardUniquenessRicUp (I := I) g₁)
                    (forwardUniquenessRm04 (I := I) g₁) t x i j k l -
                  riemann04RicciDriftInFrame (forwardUniquenessRicUp (I := I) g₂)
                    (forwardUniquenessRm04 (I := I) g₂) t x i j k l)) ≤
          KD * d := by
      rw [drift_difference_low (I := I) g₁ g₂ t x]
      refine hD0.trans ?_
      dsimp only [KD]
      calc
        _ ≤ 32 * n ^ 6 *
            ((n ^ 4 * d) * BR1 + BRic21 * d) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hDprod1 hDprod2)
            (mul_nonneg (by norm_num) (pow_nonneg hn 6))
        _ = (32 * n ^ 6 * (n ^ 4 * BR1 + BRic21)) * d :=
          remainder_kd_factor n BR1 BRic21 d
    have hR0raw := rmDotRemSq_le (I := I) (g₁ t) (g₂ t)
      (forwardUniquenessTf (I := I) g₂ t) (coordBasisAt (I := I))
      (forwardUniquenessRm04 (I := I) g₁) (forwardUniquenessRm04 (I := I) g₂)
      (forwardUniquenessBRm (I := I) g₁) (forwardUniquenessBRm (I := I) g₂)
      (forwardUniquenessRicUp (I := I) g₁) (forwardUniquenessRicUp (I := I) g₂) t x
      hΛ0 (hΛ) (hB5) (hB6) hQ hD
    dsimp only [R0]
    refine hR0raw.trans ?_
    have hspace1 :
        50 * n ^ 12 * connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x * B5 ≤
          50 * n ^ 12 * d * B5 := by
      have h := mul_le_mul_of_nonneg_right hconn hB50
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num) (pow_nonneg hn 12))
    have hspace2 :
        2 * n ^ 10 * Λ ^ 2 * metricDiffSq (I := I) (g₁ t) (g₂ t) x * B6 ≤
          2 * n ^ 10 * Λ ^ 2 * d * B6 := by
      have h := mul_le_mul_of_nonneg_right hmetric hB60
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left h
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hn 10)) (sq_nonneg Λ))
    have hspace :
        4 * (50 * n ^ 12 * connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x * B5 +
            2 * n ^ 10 * Λ ^ 2 * metricDiffSq (I := I) (g₁ t) (g₂ t) x * B6) ≤
          4 * (50 * n ^ 12 * d * B5 + 2 * n ^ 10 * Λ ^ 2 * d * B6) :=
      mul_le_mul_of_nonneg_left (add_le_add hspace1 hspace2) (by norm_num)
    dsimp only [KR0]
    calc
      _ ≤ 4 * (50 * n ^ 12 * d * B5 + 2 * n ^ 10 * Λ ^ 2 * d * B6) +
          16 * (KQ * d) + 2 * (KD * d) := by
        exact add_le_add (add_le_add hspace (le_refl _)) (le_refl _)
      _ = (200 * n ^ 12 * B5 + 8 * n ^ 10 * Λ ^ 2 * B6 +
          16 * KQ + 2 * KD) * d :=
        remainder_kr0_factor n B5 Λ B6 KQ KD d
  have hG : normSq0S (I := I) (g₁ t) x 4 G ≤ KG * d := by
    have hn : 0 ≤ n := by
      dsimp only [n]
      positivity
    have hd : 0 ≤ d := by
      simpa only [d] using density_nonneg (I := I) g₁ g₂ t x
    have hmetric :
        metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ d := by
      simpa only [d] using metricDiffSq_le_dens (I := I) g₁ g₂ t x
    have hmetric0 : 0 ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
      rw [metricDiffSq_def]
      exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
    let Rg : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
      lowerTri (I := I)
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)
        (riemannOp (metricCov (I := I) (g₂ t)) x)
    let Hg : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
      lowerTri (I := I) (metricDiffAt (I := I) (g₁ t) (g₂ t) x) V₂
    have hGsplit : G = (2 : Real) • Rg - Hg := rfl
    have hRg0 := lowerTriSq_le (I := I) (g₁ t)
      (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)
      (riemannOp (metricCov (I := I) (g₂ t)) x)
    rw [lower_riemann_cross (I := I) (g₁ t) (g₂ t) x] at hRg0
    have hRicDiff := ricciSlabLe (I := I) g₁ g₂ t x
    have hCross0 :
        0 ≤ normSq0S (I := I) (g₁ t) x 4
          (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t)
            (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) x) :=
      normSq0S_nonneg (I := I) (g₁ t) x 4 _
    have hRicUpper0 : 0 ≤ n ^ 4 * d := mul_nonneg (pow_nonneg hn 4) hd
    have hprodR :
        normSq0S (I := I) (g₁ t) x 2
              (metricRicciAt (I := I) (g₁ t) x -
                metricRicciAt (I := I) (g₂ t) x) *
            normSq0S (I := I) (g₁ t) x 4
              (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t)
                (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) x) ≤
          (n ^ 4 * d) * BP :=
      mul_le_mul hRicDiff (hBP) hCross0 hRicUpper0
    have hRg :
        normSq0S (I := I) (g₁ t) x 4 Rg ≤ n ^ 10 * BP * d := by
      refine hRg0.trans ?_
      calc
        _ ≤ n ^ 6 * ((n ^ 4 * d) * BP) :=
          mul_le_mul_of_nonneg_left hprodR (pow_nonneg hn 6)
        _ = n ^ 10 * BP * d := remainder_rg_factor n BP d
    have h2Rg_eq :
        normSq0S (I := I) (g₁ t) x 4 ((2 : Real) • Rg) =
          4 * normSq0S (I := I) (g₁ t) x 4 Rg := by
      calc
        normSq0S (I := I) (g₁ t) x 4 ((2 : Real) • Rg) =
            (2 : Real) ^ 2 * normSq0S (I := I) (g₁ t) x 4 Rg :=
          Tensor0SBundle.normSq0S_smul (I := I) (g₁ t) (2 : Real) Rg
        _ = 4 * normSq0S (I := I) (g₁ t) x 4 Rg := by norm_num
    have h2Rg :
        normSq0S (I := I) (g₁ t) x 4 ((2 : Real) • Rg) ≤
          4 * (n ^ 10 * BP * d) := by
      rw [h2Rg_eq]
      exact mul_le_mul_of_nonneg_left hRg (by norm_num)
    have hNabla2 :
        normSq0S (I := I) (g₂ t) x 6
            (metricNabla0S (I := I) (g₂ t)
              (metricNabla0S (I := I) (g₂ t) (forwardUniquenessTf (I := I) g₂ t)) x) ≤
          B6g2 := by
      simpa only [forwardUniquenessTf, metricRm04] using hB6g2
    have hRm2 :
        normSq0S (I := I) (g₂ t) x 4 (forwardUniquenessTf (I := I) g₂ t x) ≤ BR2g2 := by
      simpa only [forwardUniquenessTf_apply, metricRm04At] using hBR2g2
    have hRm20 :
        0 ≤ normSq0S (I := I) (g₂ t) x 4 (forwardUniquenessTf (I := I) g₂ t x) :=
      normSq0S_nonneg (I := I) (g₂ t) x 4 _
    have hRm2sq :
        normSq0S (I := I) (g₂ t) x 4 (forwardUniquenessTf (I := I) g₂ t x) ^ 2 ≤
          BR2g2 ^ 2 := by
      exact sq_le_sq_of_nonneg hRm20 hRm2
    have hRicRm :
        normSq0S (I := I) (g₂ t) x 2 (metricRicciAt (I := I) (g₂ t) x) *
            normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤
          BRic2g2 * BR2g2 := by
      have hRm2' :
          normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤
            BR2g2 := by
        simpa only [forwardUniquenessTf_apply] using hRm2
      exact mul_le_mul (hBRic2g2) hRm2'
        (normSq0S_nonneg (I := I) (g₂ t) x 4 _) hBRic2g20
    have hSpeed0 := uhlSpeedSq_le (I := I) (g₂ t) (forwardUniquenessTf (I := I) g₂ t) x
    have hSpeed :
        normSq0S (I := I) (g₂ t) x 4
            (uhlSpeed04 (I := I) (g₂ t) (forwardUniquenessTf (I := I) g₂ t) x) ≤
          BSpeed := by
      have hS1 :
          8 * n ^ 6 *
              normSq0S (I := I) (g₂ t) x 6
                (metricNabla0S (I := I) (g₂ t)
                  (metricNabla0S (I := I) (g₂ t) (forwardUniquenessTf (I := I) g₂ t)) x) ≤
            8 * n ^ 6 * B6g2 :=
        mul_le_mul_of_nonneg_left hNabla2
          (mul_nonneg (by norm_num) (pow_nonneg hn 6))
      have hS2 :
          512 * n ^ 14 *
              normSq0S (I := I) (g₂ t) x 4 (forwardUniquenessTf (I := I) g₂ t x) ^ 2 ≤
            512 * n ^ 14 * BR2g2 ^ 2 :=
        mul_le_mul_of_nonneg_left hRm2sq
          (mul_nonneg (by norm_num) (pow_nonneg hn 14))
      have hS3 :
          72 * n ^ 6 *
              (normSq0S (I := I) (g₂ t) x 2 (metricRicciAt (I := I) (g₂ t) x) *
                normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x)) ≤
            72 * n ^ 6 * (BRic2g2 * BR2g2) :=
        mul_le_mul_of_nonneg_left hRicRm
          (mul_nonneg (by norm_num) (pow_nonneg hn 6))
      have hSpeed0' :
          normSq0S (I := I) (g₂ t) x 4
              (uhlSpeed04 (I := I) (g₂ t) (forwardUniquenessTf (I := I) g₂ t) x) ≤
            8 * n ^ 6 *
                normSq0S (I := I) (g₂ t) x 6
                  (metricNabla0S (I := I) (g₂ t)
                    (metricNabla0S (I := I) (g₂ t) (forwardUniquenessTf (I := I) g₂ t)) x) +
              512 * n ^ 14 *
                  normSq0S (I := I) (g₂ t) x 4 (forwardUniquenessTf (I := I) g₂ t x) ^ 2 +
                72 * n ^ 6 *
                  (normSq0S (I := I) (g₂ t) x 2
                      (metricRicciAt (I := I) (g₂ t) x) *
                    normSq0S (I := I) (g₂ t) x 4
                      (metricRm04At (I := I) (g₂ t) x)) := by
        simpa only [n] using hSpeed0
      refine hSpeed0'.trans ?_
      dsimp only [BSpeed]
      exact add_le_add (add_le_add hS1 hS2) hS3
    have hBSpeed0 : 0 ≤ BSpeed := by
      dsimp only [BSpeed]
      positivity
    have hVlow :
        lowerTri (I := I) (metricTensorField (I := I) (g₂ t) x) V₂ =
          uhlSpeed04 (I := I) (g₂ t) (forwardUniquenessTf (I := I) g₂ t) x := by
      simpa only [V₂] using forwardUniquenessSpeed_low (I := I) g₂ t x
    have hswap := lowerTriSwapSq_le (I := I) (g₁ t) (g₂ t) V₂ hCe
      (hEquiv)
    rw [hVlow] at hswap
    have hSpeedMetric :
        normSq0S (I := I) (g₂ t) x 4
              (uhlSpeed04 (I := I) (g₂ t) (forwardUniquenessTf (I := I) g₂ t) x) *
            metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤
          BSpeed * d :=
      mul_le_mul hSpeed hmetric hmetric0 hBSpeed0
    have hHg : normSq0S (I := I) (g₁ t) x 4 Hg ≤
        Ce ^ 6 * n ^ 6 * BSpeed * d := by
      refine hswap.trans ?_
      calc
        _ ≤ Ce ^ 6 * n ^ 6 * (BSpeed * d) :=
          mul_le_mul_of_nonneg_left hSpeedMetric
            (mul_nonneg (pow_nonneg (le_trans (by norm_num) hCe) 6) (pow_nonneg hn 6))
        _ = Ce ^ 6 * n ^ 6 * BSpeed * d := by simp only [mul_assoc]
    rw [hGsplit]
    refine (normSq0S_sub_le (I := I) (g₁ t) x 4 ((2 : Real) • Rg) Hg).trans ?_
    dsimp only [KG]
    calc
      _ ≤ 2 * (4 * (n ^ 10 * BP * d)) +
          2 * (Ce ^ 6 * n ^ 6 * BSpeed * d) :=
        add_le_add
          (mul_le_mul_of_nonneg_left h2Rg (by norm_num))
          (mul_le_mul_of_nonneg_left hHg (by norm_num))
      _ = (8 * n ^ 10 * BP + 2 * Ce ^ 6 * n ^ 6 * BSpeed) * d :=
        remainder_kg_factor n BP Ce BSpeed d
  have hPfield :
      P = CovariantDerivative.rm04Section (I := I) (g₁ t)
        (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) := by
    refine DFunLike.ext _ _ fun y => ?_
    simpa only [P, CovariantDerivative.rm04Section_apply] using
      forwardUniquenessP_eq (I := I) g₁ g₂ t y
  have hL : normSq0S (I := I) (g₁ t) x 4 L ≤ KL * d := by
    have hn : 0 ≤ n := by
      dsimp only [n]
      positivity
    have hd : 0 ≤ d := by
      simpa only [d] using density_nonneg (I := I) g₁ g₂ t x
    have hmetric :
        metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ d := by
      simpa only [d] using metricDiffSq_le_dens (I := I) g₁ g₂ t x
    have hmetric0 : 0 ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
      rw [metricDiffSq_def]
      exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
    have hDeriv :
        normSq0S (I := I) (g₁ t) x 6
            (metricNabla0S (I := I) (g₁ t)
              (metricNabla0S (I := I) (g₁ t) P) x) ≤
          BP2 := by
      rw [hPfield]
      exact hBP2
    have hLap0 := roughLapSq_le (I := I) (s := 4) (g₁ t) P x
    have hLap :
        normSq0S (I := I) (g₁ t) x 4
            (roughLap0SField (I := I) (g₁ t) P x) ≤
          n ^ 6 * BP2 := by
      refine hLap0.trans ?_
      simpa only [n] using
        mul_le_mul_of_nonneg_left hDeriv (pow_nonneg hn 6)
    have hLapUpper0 : 0 ≤ n ^ 6 * BP2 :=
      mul_nonneg (pow_nonneg hn 6) hBP20
    have hprod :
        normSq0S (I := I) (g₁ t) x 4
              (roughLap0SField (I := I) (g₁ t) P x) *
            metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤
          (n ^ 6 * BP2) * d :=
      mul_le_mul hLap hmetric hmetric0 hLapUpper0
    have hDef0 := reLowerDefSq_le (I := I) (s := 3) (g₁ t) (g₂ t)
      (roughLap0SField (I := I) (g₁ t) P) x
    have hDef :
        normSq0S (I := I) (g₁ t) x 4 L ≤
          n ^ 6 *
            (normSq0S (I := I) (g₁ t) x 4
                (roughLap0SField (I := I) (g₁ t) P x) *
              metricDiffSq (I := I) (g₁ t) (g₂ t) x) := by
      simpa only [L, ContMDiffSection.coe_sub, Pi.sub_apply, n] using hDef0
    refine hDef.trans ?_
    dsimp only [KL]
    calc
      _ ≤ n ^ 6 * ((n ^ 6 * BP2) * d) :=
        mul_le_mul_of_nonneg_left hprod (pow_nonneg hn 6)
      _ = n ^ 12 * BP2 * d := remainder_kl_factor n BP2 d
  have hT : normSq0S (I := I) (g₁ t) x 4 T ≤ KT * d := by
    have hn : 0 ≤ n := by
      dsimp only [n]
      positivity
    have hd : 0 ≤ d := by
      simpa only [d] using density_nonneg (I := I) g₁ g₂ t x
    have hconn :
        connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x ≤ d := by
      simpa only [d] using connectionDifferenceSq_le_dens (I := I) g₁ g₂ t x
    have hMetricField0 :
        0 ≤ normSq0S (I := I) (g₁ t) x 2
          (metricTensorField (I := I) (g₂ t) x) :=
      normSq0S_nonneg (I := I) (g₁ t) x 2 _
    have hGradP :
        normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) P x) ≤ BP1 := by
      rw [hPfield]
      exact hBP1
    have hFluxProd :
        connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x *
            normSq0S (I := I) (g₁ t) x 2
              (metricTensorField (I := I) (g₂ t) x) ≤
          d * Background :=
      mul_le_mul hconn (hBackground) hMetricField0 hd
    have hFlux0 := fluxNormSq_le (I := I) (s := 2) (g₁ t) (g₂ t)
      (metricTensorField (I := I) (g₂ t)) x
    have hFlux : normSq0S (I := I) (g₁ t) x 3 (K x) ≤
        4 * n ^ 3 * Background * d := by
      dsimp only [K]
      refine hFlux0.trans ?_
      calc
        _ = (2 : Real) ^ 2 * n ^ 3 *
            (connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x *
              normSq0S (I := I) (g₁ t) x 2
                (metricTensorField (I := I) (g₂ t) x)) := by ring
        _ ≤ (2 : Real) ^ 2 * n ^ 3 * (d * Background) :=
          mul_le_mul_of_nonneg_left hFluxProd
            (mul_nonneg (sq_nonneg (2 : Real)) (pow_nonneg hn 3))
        _ = 4 * n ^ 3 * Background * d := by ring
    have hFluxNorm0 : 0 ≤ normSq0S (I := I) (g₁ t) x 3 (K x) :=
      normSq0S_nonneg (I := I) (g₁ t) x 3 _
    have hPairProd :
        normSq0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) P x) *
            normSq0S (I := I) (g₁ t) x 3 (K x) ≤
          BP1 * (4 * n ^ 3 * Background * d) :=
      mul_le_mul hGradP hFlux hFluxNorm0 hBP10
    have hPair0 := reLowerPairSq_le (I := I) (s := 4) (g₁ t)
      (metricNabla0S (I := I) (g₁ t) P) K x
    have hPair :
        normSq0S (I := I) (g₁ t) x 6
            (reLowerPair (I := I) (g₁ t)
              (metricNabla0S (I := I) (g₁ t) P) K x) ≤
          4 * n ^ 11 * BP1 * Background * d := by
      refine hPair0.trans ?_
      calc
        _ ≤ n ^ 8 * (BP1 * (4 * n ^ 3 * Background * d)) :=
          mul_le_mul_of_nonneg_left hPairProd (pow_nonneg hn 8)
        _ = 4 * n ^ 11 * BP1 * Background * d := remainder_pair_factor n BP1 Background d
    have hTrace0 := traceNormSq_le (I := I) (s := 4) (g₁ t) x
      (reLowerPair (I := I) (g₁ t) (metricNabla0S (I := I) (g₁ t) P) K x)
    have hTrace :
        normSq0S (I := I) (g₁ t) x 4 T ≤
          n ^ 6 *
            normSq0S (I := I) (g₁ t) x 6
              (reLowerPair (I := I) (g₁ t)
                (metricNabla0S (I := I) (g₁ t) P) K x) := by
      simpa only [T, metricTraceFirstTwoField_apply, n] using hTrace0
    refine hTrace.trans ?_
    dsimp only [KT]
    calc
      _ ≤ n ^ 6 * (4 * n ^ 11 * BP1 * Background * d) :=
        mul_le_mul_of_nonneg_left hPair (pow_nonneg hn 6)
      _ = 4 * n ^ 17 * BP1 * Background * d := remainder_trace_factor n BP1 Background d
  have hAB := normSq0S_add_le (I := I) (g₁ t) x 4 R0 G
  have hABC := normSq0S_sub_le (I := I) (g₁ t) x 4 (R0 + G) L
  have hABCD := normSq0S_sub_le (I := I) (g₁ t) x 4 ((R0 + G) - L) T
  change normSq0S (I := I) (g₁ t) x 4 (((R0 + G) - L) - T) ≤ C_rem * d
  calc
    normSq0S (I := I) (g₁ t) x 4 (((R0 + G) - L) - T) ≤
        2 * normSq0S (I := I) (g₁ t) x 4 ((R0 + G) - L) +
          2 * normSq0S (I := I) (g₁ t) x 4 T := hABCD
    _ ≤ 8 * normSq0S (I := I) (g₁ t) x 4 R0 +
          8 * normSq0S (I := I) (g₁ t) x 4 G +
          4 * normSq0S (I := I) (g₁ t) x 4 L +
          2 * normSq0S (I := I) (g₁ t) x 4 T := by
      exact remainder_four_term_bound hAB hABC
    _ ≤ 8 * (KR0 * d) + 8 * (KG * d) + 4 * (KL * d) + 2 * (KT * d) := by
      exact remainder_four_term_mono hR0 hG hL hT
    _ = C_rem * d := by
      dsimp only [C_rem]
      exact remainder_total_factor KR0 KG KL KT d

end DifferentialGeometry.PDE.RicciFlow
