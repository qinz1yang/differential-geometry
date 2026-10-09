import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Curvature
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CoefficientChart
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.SectionalTransition
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientField
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# LFR14, clause T2: the curvature sign passes to the finite limit

Blueprint LFR14 (master207A.tex:25869), last paragraph of the proof (A:26085–26090): "curvature
is a continuous expression in the metric, its inverse, and its first two derivatives ... the
additional expanding-ball lower sectional bound therefore passes to `g`".

* `coefficientRm04_lower_of_isLocalDiffeomorphAt`: along any `C^k` (`k ≥ 3`) local
  diffeomorphism `φ : E → M` into a smooth Riemannian manifold whose sectional curvature is
  `≥ κ` on an open set containing `φ w`, the coefficient numerator of `φ^* h` at `w` is
  `≥ κ · Gram`. (Smooth chart: `coefficientRm04_lower_bound_of_sectionalBoundedBelowAt`; change
  of coordinates: `coefficientRm04_lower_bound_of_pullback`.)
* `sectionalCurvature_nonneg_of_finite_comparison`: the frozen statement T2 of
  `build-logs/scratch/D-LFR14/Target.lean`, without the instance
  `[∀ i, SigmaCompactSpace (X i)]`, which the argument does not use. The verbatim frozen
  statement is recorded as an `example` at the end of the file.
* Consumer `sectionalCurvature_nonneg_of_finite_comparison_of_nonneg`: sources with
  `sec ≥ 0` everywhere.

Pattern: `coefficientRm04_nonneg_of_normal_chart_limit`
(Geometry/Compactness/CheegerGromov/Limit/FiniteMetricCurvatureSign.lean).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis (coefficientRm04)

universe u

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- **Lower curvature bound along a finite-order local diffeomorphism.** If `φ : E → M` is a `C^k`
local diffeomorphism (`3 ≤ k`) at every point of an open `U₀ ∋ w` and the smooth metric `h` has
`sec ≥ κ` on an open `O ∋ φ w`, then the coefficient numerator of `φ^* h` at `w` is
`≥ κ · Gram`. -/
theorem coefficientRm04_lower_of_isLocalDiffeomorphAt
    (h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {k : ℕ} (hk : 3 ≤ k) {φ : E → M}
    {U₀ : Set E} (hU₀ : IsOpen U₀)
    (hφ : ∀ y ∈ U₀, IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) k φ y)
    {w : E} (hw : w ∈ U₀) {O : Set M} (hO : IsOpen O) (hφO : φ w ∈ O) {κ : ℝ}
    (hsec : ∀ z ∈ O, SectionalBoundedBelowAt h z κ) (v u : E) :
    κ * (pullbackMetricCoefficients h φ w v v * pullbackMetricCoefficients h φ w u u -
        (pullbackMetricCoefficients h φ w v u) ^ 2) ≤
      coefficientRm04 (pullbackMetricCoefficients h φ) w v u u v := by
  have hk0 : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hφc : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) k φ U₀ :=
    fun y hy => (hφ y hy).contMDiffAt.contMDiffWithinAt
  let ψ := DifferentialGeometry.PartialDiffeomorph.extChartAt 𝓘(ℝ, E) ∞ (φ w)
  let Ψ := ψ.symm
  let c := pullbackMetricCoefficients h Ψ
  let V : Set E := Ψ.source ∩ Ψ ⁻¹' O
  have hV : IsOpen V := Ψ.contMDiffOn.continuousOn.isOpen_inter_preimage Ψ.open_source hO
  let U : Set E := U₀ ∩ φ ⁻¹' (ψ.source ∩ O)
  have hU : IsOpen U := hφc.continuousOn.isOpen_inter_preimage hU₀ (ψ.open_source.inter hO)
  have hwU : w ∈ U := ⟨hw, mem_extChartAt_source (φ w), hφO⟩
  let Φ : E → E := ψ ∘ φ
  have hc : ContDiffOn ℝ 2 c V :=
    ((contDiffOn_pullback_metric_coefficients h Ψ.open_source Ψ.contMDiffOn).mono
      inter_subset_left).of_le ENat.LEInfty.out
  have hcsymm : ∀ z ∈ V, ∀ a b : E, c z a b = c z b a := fun z _ a b => h.symm _ _ _
  have hcco : ∀ z ∈ V, IsCoercive (c z) := by
    intro z hz
    apply ContinuousLinearMap.isCoercive_of_posDef
    intro a ha
    apply pullbackMetricCoefficients_pos h _ ha
    obtain ⟨e, he⟩ :=
      (Ψ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ hz.1).isInvertible_mfderiv (by simp)
    rw [← he]
    exact e.injective
  have hΦ : ContDiffOn ℝ 3 Φ U := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (ψ.contMDiffOn.of_le ENat.LEInfty.out).comp
      ((hφc.mono inter_subset_left).of_le (by exact_mod_cast hk)) (fun y hy => hy.2.1)
  have hΦUV : MapsTo Φ U V := by
    intro y hy
    refine ⟨ψ.map_source hy.2.1, ?_⟩
    change Ψ (ψ (φ y)) ∈ O
    rw [show Ψ (ψ (φ y)) = φ y from ψ.left_inv hy.2.1]
    exact hy.2.2
  have hΦinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible := by
    intro y hy
    have h1 : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) k Φ y :=
      (hφ y hy.1).comp 𝓘(ℝ, E) E
        ((DifferentialGeometry.PartialDiffeomorph.ofLE ψ
          (by exact_mod_cast le_top)).isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) k hy.2.1)
    have h2 := h1.isInvertible_mfderiv hk0
    rw [mfderiv_eq_fderiv] at h2
    exact h2
  have hpull : ∀ y ∈ U, ∀ a b : E, pullbackMetricCoefficients h φ y a b =
      c (Φ y) (fderiv ℝ Φ y a) (fderiv ℝ Φ y b) := by
    intro y hy a b
    have hφd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) φ y := (hφ y hy.1).mdifferentiableAt hk0
    exact (pullbackMetricCoefficients_fderiv_symm h Ψ hφd hy.2.1 a b).symm
  have hκ : ∀ z ∈ V, ∀ a b : E,
      κ * (c z a a * c z b b - (c z a b) ^ 2) ≤ coefficientRm04 c z a b b a :=
    fun z hz a b =>
      DifferentialGeometry.Geometry.Curvature.coefficientRm04_lower_bound_of_sectionalBoundedBelowAt
        h Ψ hz.1 (hsec _ hz.2) a b
  exact DifferentialGeometry.Analysis.coefficientRm04_lower_bound_of_pullback hU hV hc hcsymm
    hcco hΦ hΦUV hΦinv hpull κ hκ w hwU v u

end Kernel

/-- **T2 — LFR14 curvature-sign clause, kernel form.** It consumes only output clauses of T0/T1
(stated for the already extracted sequence): `C²` chart convergence (`3 ≤ K`), pointedness,
exhaustion and distortion, plus `sec_{gᵢ} ≥ -εᵢ` on `B(pᵢ,Lᵢ)` with `εᵢ → 0`, `Lᵢ → ∞`.
(Frozen statement without the unused `SigmaCompactSpace` instances.) -/
theorem sectionalCurvature_nonneg_of_finite_comparison
    {n K : ℕ} (hK : 3 ≤ K)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    {N : Type*} [MetricSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
      (EuclideanSpace ℝ (Fin n)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
    (q : N)
    (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X i) K)
    (hbase : ∀ i, q ∈ (j i).source ∧ j i q = p i)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
      L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
      MapCPConvergenceOn L (K - 1)
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → X i) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    {ε L : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-ε i)) :
    ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
      0 ≤ G.sectionalCurvature x v w := by
  have hn2 : (2 : ℕ∞ω) ≤ ((K - 1 : ℕ) : ℕ∞ω) := by exact_mod_cast (show 2 ≤ K - 1 by omega)
  refine (sectionalCurvature_nonneg_iff_chart_numerator_nonneg (g := G) hn2).2 ?_
  intro x₀ x' hx' V W
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x₀
  let w : EuclideanSpace ℝ (Fin n) := e x'
  have hwt : w ∈ e.target := e.map_source hx'
  have hex' : e.symm w = x' := e.left_inv hx'
  obtain ⟨r, hr, hrt⟩ : ∃ r > 0, closedBall w r ⊆ e.target :=
    nhds_basis_closedBall.mem_iff.mp ((isOpen_extChartAt_target x₀).mem_nhds hwt)
  have hballt : ball w r ⊆ e.target := ball_subset_closedBall.trans hrt
  have hCc : IsCompact (e.symm '' closedBall w r) :=
    (isCompact_closedBall _ _).image_of_continuousOn ((continuousOn_extChartAt_symm x₀).mono hrt)
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp (hexh _ hCc)
  let B : ℕ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun k =>
    pullbackMetricCoefficients (g (k + k₁)) ((j (k + k₁) : N → X (k + k₁)) ∘ e.symm)
  have hmaps (k : ℕ) : MapsTo e.symm (ball w r) (j (k + k₁)).source := fun y hy =>
    hk₁ (k + k₁) (Nat.le_add_left k₁ k) ⟨y, ball_subset_closedBall hy, rfl⟩
  have hB (k : ℕ) : ContDiffOn ℝ 2 (B k) (ball w r) :=
    Bundle.ContMDiffRiemannianMetric.contDiffOn_pullback_inner (g (k + k₁))
      (r := (2 : ℕ∞ω)) (s := (3 : ℕ∞ω)) ENat.LEInfty.out (by norm_num) isOpen_ball
      (((j (k + k₁)).contMDiffOn.of_le (by exact_mod_cast hK)).comp
        ((contMDiffOn_extChartAt_symm x₀).mono hballt) (hmaps k))
  have hb : ContDiffOn ℝ 2 (chartCoeff G x₀) (ball w r) :=
    (contDiffOn_chartCoeff G hn2 x₀).mono hballt
  have hwD : ({w} : Set (EuclideanSpace ℝ (Fin n))) ⊆ ball w r :=
    singleton_subset_iff.mpr (mem_ball_self hr)
  have hconvB : MapCPConvergenceOn {w} 2 B (chartCoeff G x₀) :=
    ((hconv x₀ {w} isCompact_singleton (singleton_subset_iff.mpr hwt)).mono_order
      (show 2 ≤ K - 1 by omega)).comp_tendsto_atTop (tendsto_add_atTop_nat k₁)
  have hpos : ∀ y ∈ ({w} : Set (EuclideanSpace ℝ (Fin n))), ∀ v : EuclideanSpace ℝ (Fin n),
      v ≠ 0 → 0 < chartCoeff G x₀ y v v := by
    rintro y rfl v hv
    exact chartCoeff_pos G x₀ hwt hv
  -- the lower bound at `w`, for the unshifted sequence
  have hlow₀ : ∀ᶠ i in atTop, ∀ a b : EuclideanSpace ℝ (Fin n),
      -ε i * (pullbackMetricCoefficients (g i) ((j i : N → X i) ∘ e.symm) w a a *
          pullbackMetricCoefficients (g i) ((j i : N → X i) ∘ e.symm) w b b -
          (pullbackMetricCoefficients (g i) ((j i : N → X i) ∘ e.symm) w a b) ^ 2) ≤
        coefficientRm04 (pullbackMetricCoefficients (g i) ((j i : N → X i) ∘ e.symm)) w a b b a := by
    filter_upwards [hexh {x'} isCompact_singleton, hdist (dist x' q + 1) 1 one_pos,
      hL.eventually_ge_atTop (dist x' q + 1)] with i hi₁ hi₂ hi₃ a b
    have hx'src : x' ∈ (j i).source := hi₁ (mem_singleton x')
    have hjx : dist (j i x') (p i) < L i := by
      have hd := hi₂ x' (mem_ball.mpr (by linarith)) q
        (mem_ball_self (by linarith [dist_nonneg (x := x') (y := q)]))
      rw [(hbase i).2] at hd
      linarith [(abs_sub_lt_iff.mp hd).1]
    have hU₀ : IsOpen (e.target ∩ e.symm ⁻¹' (j i).source) :=
      (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage (isOpen_extChartAt_target x₀)
        (j i).open_source
    have hφ : ∀ y ∈ e.target ∩ e.symm ⁻¹' (j i).source,
        IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) K
          ((j i : N → X i) ∘ e.symm) y := fun y hy =>
      ((DifferentialGeometry.PartialDiffeomorph.ofLE
          (DifferentialGeometry.PartialDiffeomorph.extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ x₀)
          (by exact_mod_cast le_top)).symm.isLocalDiffeomorphAt
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) K hy.1).comp
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i)
        ((j i).isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) K hy.2)
    have hwU₀ : w ∈ e.target ∩ e.symm ⁻¹' (j i).source := by
      refine ⟨hwt, ?_⟩
      change e.symm w ∈ (j i).source
      rw [hex']
      exact hx'src
    have hφO : ((j i : N → X i) ∘ e.symm) w ∈ ball (p i) (L i) := by
      rw [Function.comp_apply, hex', mem_ball]
      exact hjx
    have hsecO : ∀ z ∈ ball (p i) (L i), SectionalBoundedBelowAt (g i) z (-ε i) := by
      intro z hz
      apply hsec i z
      have hz' : dist z (p i) < L i := mem_ball.mp hz
      change riemannianEDistOf (g i) (p i) z < ENNReal.ofReal (L i)
      rw [hmetric, dist_comm]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg hz')).mpr hz'
    exact coefficientRm04_lower_of_isLocalDiffeomorphAt (g i) hK hU₀ hφ hwU₀ isOpen_ball hφO
      hsecO a b
  have hlow : ∀ᶠ k in atTop, ∀ y ∈ ({w} : Set (EuclideanSpace ℝ (Fin n))),
      ∀ a b : EuclideanSpace ℝ (Fin n),
      -ε (k + k₁) * (B k y a a * B k y b b - (B k y a b) ^ 2) ≤
        coefficientRm04 (B k) y a b b a := by
    filter_upwards [(tendsto_add_atTop_nat k₁).eventually hlow₀] with k hk y hy a b
    rw [mem_singleton_iff] at hy
    subst hy
    exact hk a b
  exact DifferentialGeometry.Analysis.nonneg_coefficientRm04_of_eventual_sectional_lower_bound
    isOpen_ball hwD hB hb hconvB hpos (hε.comp (tendsto_add_atTop_nat k₁)) hlow w
    (mem_singleton w) V W

/-- Consumer: sources of nonnegative sectional curvature everywhere give a limit metric of
nonnegative sectional curvature. -/
theorem sectionalCurvature_nonneg_of_finite_comparison_of_nonneg
    {n K : ℕ} (hK : 3 ≤ K)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    {N : Type*} [MetricSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
      (EuclideanSpace ℝ (Fin n)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
    (q : N)
    (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X i) K)
    (hbase : ∀ i, q ∈ (j i).source ∧ j i q = p i)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
      L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
      MapCPConvergenceOn L (K - 1)
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → X i) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hsec : ∀ i (y : X i), SectionalBoundedBelowAt (g i) y 0) :
    ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
      0 ≤ G.sectionalCurvature x v w :=
  sectionalCurvature_nonneg_of_finite_comparison hK g hmetric p G q j hbase hexh hconv hdist
    (ε := fun _ => 0) (L := fun i => (i : ℝ)) tendsto_const_nhds tendsto_natCast_atTop_atTop
    (fun i y _ => by
      rw [neg_zero]
      exact hsec i y)

/-- The verbatim frozen statement T2 (`Target.lean`), with the `SigmaCompactSpace` instances. -/
example
    {n K : ℕ} (hK : 3 ≤ K)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    {N : Type*} [MetricSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
      (EuclideanSpace ℝ (Fin n)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
    (q : N)
    (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X i) K)
    (hbase : ∀ i, q ∈ (j i).source ∧ j i q = p i)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set (EuclideanSpace ℝ (Fin n))), IsCompact L →
      L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
      MapCPConvergenceOn L (K - 1)
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → X i) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    {ε L : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-ε i)) :
    ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
      0 ≤ G.sectionalCurvature x v w :=
  sectionalCurvature_nonneg_of_finite_comparison hK g hmetric p G q j hbase hexh hconv hdist hε hL
    hsec

end DifferentialGeometry.CheegerGromovCompactness
