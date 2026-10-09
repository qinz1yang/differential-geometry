import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CheegerGromovLimit
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CurvatureScale

/-!
# LFR14 consumer adapter (d): signed lower bounds for LFR49's curvature scale

The external review of the LFR14 design (`build-logs/inbox/review-lfr14.md` §7, item 5(d) of the
dispositions) notes that T2 (`exists_finite_cheeger_gromov_limit_with_nonneg_sectional`) accepts
`sec_{gᵢ} ≥ -ηᵢ` with `ηᵢ → 0` of ANY sign, while LFR49's first step
(`Collapse.exists_curvature_scale_of_ball_lower_bounds`, blueprint A:29096) asks for `0 ≤ εᵢ`.
The bridge is the weakening `ηᵢ ↦ max ηᵢ 0`.

* `sectionalBoundedBelowAt_neg_max_zero`: `sec ≥ -η` implies `sec ≥ -max η 0`.
* `exists_curvature_scale_of_signed_ball_lower_bounds`: LFR49's curvature scale without the sign
  hypothesis.
* `exists_finite_cheeger_gromov_limit_with_nonneg_sectional_and_curvature_scale`: T0 + T2 with,
  on the SAME subsequence, the curvature scale `Hᵢ → ∞` of LFR49's first step.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian

universe u

section Weakening

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- **The `max (η, 0)` weakening.** A lower bound `-η` of the sectional curvature at a point
gives the lower bound `-max η 0`. -/
theorem sectionalBoundedBelowAt_neg_max_zero
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {g : SmoothRiemannianMetric I M} {y : M} {η : ℝ} (h : SectionalBoundedBelowAt g y (-η)) :
    SectionalBoundedBelowAt g y (-max η 0) :=
  h.mono (neg_le_neg (le_max_left η 0))

/-- **LFR49, curvature scale for signed lower bounds.** Bounds `sec_{gᵢ} ≥ -ηᵢ` on `B(pᵢ, Lᵢ)`
with `Lᵢ → ∞` and `ηᵢ → 0` (no sign condition) give scales `Hᵢ → ∞`, `Hᵢ ≤ Lᵢ`, with
`sec_{gᵢ} ≥ -Hᵢ⁻²` on `B(pᵢ, Hᵢ)`. -/
theorem exists_curvature_scale_of_signed_ball_lower_bounds
    {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
    [∀ i, IsManifold I ∞ (X i)]
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (p : ∀ i, X i) {L η : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hη : Tendsto η atTop (𝓝 0))
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i)) :
    ∃ Hs : ℕ → ℝ, Tendsto Hs atTop atTop ∧ (∀ i, Hs i ≤ L i) ∧
      ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (Hs i),
        SectionalBoundedBelowAt (g i) y (-(Hs i ^ 2)⁻¹) := by
  have hmax : Tendsto (fun i => max (η i) 0) atTop (𝓝 0) := by
    simpa only [max_self] using hη.max (tendsto_const_nhds (x := (0 : ℝ)))
  exact Collapse.exists_curvature_scale_of_ball_lower_bounds g p hL
    (fun i => le_max_right (η i) 0) hmax
    (fun i y hy => sectionalBoundedBelowAt_neg_max_zero (hsec i y hy))

end Weakening

/-- **LFR14 with the curvature sign and LFR49's curvature scale (T0 + T2 + LFR49 step 1).**
Under the hypotheses of `exists_finite_cheeger_gromov_limit_with_nonneg_sectional` (signed
`ηᵢ → 0`), the package of T0 and T2 holds, and on the SAME subsequence `φ` the curvature scale
`Hᵢ → ∞` with `Hᵢ ≤ L_{φ i}` and `sec_{g_{φ i}} ≥ -Hᵢ⁻²` on `B(p_{φ i}, Hᵢ)` exists. -/
theorem exists_finite_cheeger_gromov_limit_with_nonneg_sectional_and_curvature_scale
    (n K : ℕ) (hn : 2 ≤ n) (hK : 3 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) (hA : ∀ R > 0, 0 < A R)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ i, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
        (q : N)
        (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
          ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N) ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
        (∀ (x : N) (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
          L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
          MapCPConvergenceOn L (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) ∧
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
          0 ≤ G.sectionalCurvature x v w) ∧
        ∃ Hs : ℕ → ℝ, Tendsto Hs atTop atTop ∧ (∀ i, Hs i ≤ L (φ i)) ∧
          ∀ i, ∀ y ∈ riemannianBallOf (g (φ i)) (p (φ i)) (Hs i),
            SectionalBoundedBelowAt (g (φ i)) y (-(Hs i ^ 2)⁻¹) := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hsecG⟩ := exists_finite_cheeger_gromov_limit_with_nonneg_sectional n K hn hK hr hv A
    hA g hmetric p hvol hcurv hη hL hsec
  obtain ⟨Hs, hHs, hHL, hHsec⟩ := exists_curvature_scale_of_signed_ball_lower_bounds
    (fun i => g (φ i)) (fun i => p (φ i)) (hL.comp hφ.tendsto_atTop)
    (hη.comp hφ.tendsto_atTop) (fun i => hsec (φ i))
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist, hcov,
    hsecG, Hs, hHs, hHL, hHsec⟩

end DifferentialGeometry.CheegerGromovCompactness
