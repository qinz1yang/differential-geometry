import DifferentialGeometry.Analysis.Calculus.PartialDerivative.Parameter
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.Bounds
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.Product
import DifferentialGeometry.Geometry.Metric.Comparison.CompactLowerBound
import DifferentialGeometry.Geometry.Metric.Product.ChartBounds
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import DifferentialGeometry.Topology.Manifold.FiniteChartBalls

open Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_chartGram_jet_bound_on_compact
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJreg : J ⊆ D.regular) (hJc : IsCompact J)
    {ι : Type*} [Finite ι] (α : ι → M) (K : ι → Set E)
    (hK : ∀ i, IsCompact (K i)) (hKt : ∀ i, K i ⊆ interior (extChartAt I (α i)).target)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b i j t, t ∈ J → ∀ x ∈ K b,
      ‖iteratedFDeriv ℝ k (chartGramOnE (g t) (α b) i j) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := DifferentialGeometry.Analysis.exists_bound_spatial_iteratedFDeriv_on_compact
    (G := fun (b : ι × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) t x =>
      chartGramOnE (g t) (α b.1) b.2.1 b.2.2 x)
    (V := fun b => interior (extChartAt I (α b.1)).target) (K := fun b => K b.1)
    (fun _ => isOpen_interior) hJc (fun b => hK b.1) (fun b => hKt b.1)
    (fun b => chartGramOnE_contDiffOn hg hJreg (α b.1) b.2.1 b.2.2) k
    (by exact_mod_cast le_top)
  exact ⟨C, hC, fun b i j t ht x hx => hbound (b, i, j) t ht x hx⟩

theorem exists_chartChristoffel_jet_bound_on_compact
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (hJc : IsCompact J)
    {ι : Type*} [Finite ι] (α : ι → M) (K : ι → Set E)
    (hK : ∀ i, IsCompact (K i)) (hKt : ∀ i, K i ⊆ interior (extChartAt I (α i)).target)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b i j l t, t ∈ J → ∀ x ∈ K b,
      ‖iteratedFDeriv ℝ k (chartChristoffel (g t) (α b) i j l) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := DifferentialGeometry.Analysis.exists_bound_spatial_iteratedFDeriv_on_compact
    (G := fun (b : ι × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E)) t x =>
      chartChristoffel (g t) (α b.1) b.2.1 b.2.2.1 b.2.2.2 x)
    (V := fun b => interior (extChartAt I (α b.1)).target) (K := fun b => K b.1)
    (fun _ => isOpen_interior) hJc (fun b => hK b.1) (fun b => hKt b.1)
    (fun b => chartChristoffelOnE_contDiffOn hg hJreg hJ (α b.1) b.2.1 b.2.2.1 b.2.2.2) k
    (by exact_mod_cast le_top)
  exact ⟨C, hC, fun b i j l t ht x hx => hbound (b, i, j, l) t ht x hx⟩

theorem exists_finite_extChartAt_jet_bounds [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (hJc : IsCompact J) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ S : Finset M, ∃ K : M → Set E,
      (∀ p ∈ S, IsCompact (K p) ∧ K p ⊆ (extChartAt I p).target) ∧
      (∀ q, ∃ p ∈ S, q ∈ (extChartAt I p).source ∧
        Metric.closedBall (extChartAt I p q) ρ ⊆ K p) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
        (∀ p ∈ S, ∀ i j t, t ∈ J → ∀ x ∈ K p,
          ‖iteratedFDeriv ℝ k (chartGramOnE (g t) p i j) x‖ ≤ C) ∧
        (∀ p ∈ S, ∀ i j l t, t ∈ J → ∀ x ∈ K p,
          ‖iteratedFDeriv ℝ k (chartChristoffel (g t) p i j l) x‖ ≤ C) := by
  obtain ⟨ρ, hρ, S, K, hK, hcover⟩ :=
    DifferentialGeometry.Topology.exists_finite_extChartAt_cover_with_margin (I := I) (M := M)
  have hKt (p : S) : K p ⊆ interior (extChartAt I (p : M)).target := by
    rw [(isOpen_extChartAt_target (I := I) (p : M)).interior_eq]
    exact (hK p p.property).2
  refine ⟨ρ, hρ, S, K, hK, hcover, fun k => ?_⟩
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_chartGram_jet_bound_on_compact hg hJreg hJc
    (fun p : S => (p : M)) (fun p => K p) (fun p => (hK p p.property).1) hKt k
  obtain ⟨C₂, _, hb₂⟩ := exists_chartChristoffel_jet_bound_on_compact hg hJreg hJ hJc
    (fun p : S => (p : M)) (fun p => K p) (fun p => (hK p p.property).1) hKt k
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _), ?_, ?_⟩
  · exact fun p hp i j t ht x hx => (hb₁ ⟨p, hp⟩ i j t ht x hx).trans (le_max_left _ _)
  · exact fun p hp i j l t ht x hx => (hb₂ ⟨p, hp⟩ i j l t ht x hx).trans (le_max_right _ _)

theorem exists_finite_extChartAt_metric_bounds [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (hJc : IsCompact J) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∃ S : Finset M, ∃ K : M → Set E,
      (∀ p ∈ S, IsCompact (K p) ∧ K p ⊆ (extChartAt I p).target) ∧
      (∀ q, ∃ p ∈ S, q ∈ (extChartAt I p).source ∧
        Metric.closedBall (extChartAt I p q) ρ ⊆ K p) ∧
      (∀ p ∈ S, ∀ t ∈ J, ∀ q ∈ (extChartAt I p).source, extChartAt I p q ∈ K p →
        ∀ v : TangentSpace I q,
          Real.sqrt ((g t).inner q v v) ≤ C *
            ‖(trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ q v‖ ∧
          ‖(trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ q v‖ ≤
            C * Real.sqrt ((g t).inner q v v)) ∧
      ∀ k : ℕ, ∃ B : ℝ, 0 < B ∧
        (∀ p ∈ S, ∀ i j t, t ∈ J → ∀ x ∈ K p,
          ‖iteratedFDeriv ℝ k (chartGramOnE (g t) p i j) x‖ ≤ B) ∧
        (∀ p ∈ S, ∀ i j l t, t ∈ J → ∀ x ∈ K p,
          ‖iteratedFDeriv ℝ k (chartChristoffel (g t) p i j l) x‖ ≤ B) := by
  obtain ⟨ρ, hρ, S, K, hK, hcover, hjets⟩ := exists_finite_extChartAt_jet_bounds hg hJreg hJ hJc
  obtain ⟨C, hC, hcomp⟩ := hg.exists_chart_norm_comparison_on_compact hJreg hJc
    (fun p : S => (p : M)) (fun p => K p)
    (fun p => (hK p p.property).2) (fun p => (hK p p.property).1)
  refine ⟨ρ, C, hρ, hC, S, K, hK, hcover, ?_, hjets⟩
  intro p hp t ht q hq hKq v
  let e := trivializationAt E (TangentSpace I) p
  have he : q ∈ e.baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
  have h := hcomp ⟨p, hp⟩ t ht (extChartAt I p q) hKq (e.continuousLinearMapAt ℝ q v)
  dsimp only at h
  rw [(extChartAt I p).left_inv hq] at h
  rw [e.symmL_continuousLinearMapAt he] at h
  exact h

theorem exists_finite_extChartAt_prod_euclidean_norm_comparison [I.Boundaryless] [CompactSpace M]
    [T2Space M] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJreg : J ⊆ D.regular) (hJc : IsCompact J) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∃ S : Finset M, ∃ K : M → Set E,
      (∀ p ∈ S, IsCompact (K p) ∧ K p ⊆ (extChartAt I p).target) ∧
      (∀ q, ∃ p ∈ S, q ∈ (extChartAt I p).source ∧
        Metric.closedBall (extChartAt I p q) ρ ⊆ K p) ∧
      ∀ p ∈ S, ∀ t ∈ J, ∀ q ∈ (extChartAt I p).source, extChartAt I p q ∈ K p →
        ∀ z₀ z : V, ∀ v : TangentSpace (I.prod 𝓘(ℝ, V)) (q, z),
          Real.sqrt (((g t).prod (euclideanMetric (E := V))).inner (q, z) v v) ≤ C *
            ‖(trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) (p, z₀)).continuousLinearMapAt
              ℝ (q, z) v‖ ∧
          ‖(trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) (p, z₀)).continuousLinearMapAt
              ℝ (q, z) v‖ ≤
            C * Real.sqrt (((g t).prod (euclideanMetric (E := V))).inner (q, z) v v) := by
  obtain ⟨ρ, hρ, S, K, hK, hcover⟩ :=
    DifferentialGeometry.Topology.exists_finite_extChartAt_cover_with_margin (I := I) (M := M)
  obtain ⟨C, hC, hcomp⟩ := hg.exists_chart_norm_comparison_on_compact hJreg hJc
    (fun p : S => (p : M)) (fun p => K p)
    (fun p => (hK p p.property).2) (fun p => (hK p p.property).1)
  refine ⟨ρ, C + 1, hρ, by linarith only [hC], S, K, hK, hcover, ?_⟩
  intro p hp t ht q hq hKq z₀ z v
  let e := trivializationAt E (TangentSpace I) p
  have he : q ∈ e.baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]
  apply (g t).prod_euclidean_chart_norm_comparison (p, z₀) he hC.le
  intro w
  have h := hcomp ⟨p, hp⟩ t ht (extChartAt I p q) hKq (e.continuousLinearMapAt ℝ q w)
  dsimp only at h
  rw [(extChartAt I p).left_inv hq, e.symmL_continuousLinearMapAt he] at h
  exact h

theorem exists_chartChristoffelContraction_bound_on_compact
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (hJc : IsCompact J)
    {ι : Type*} [Finite ι] (α : ι → M) (K : ι → Set E)
    (hK : ∀ i, IsCompact (K i)) (hKt : ∀ i, K i ⊆ interior (extChartAt I (α i)).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ b t, t ∈ J → ∀ x ∈ K b, ∀ u v : E,
      ‖chartChristoffelContraction (g t) (α b) u v x‖ ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨B, hB, hb⟩ := exists_chartChristoffel_jet_bound_on_compact hg hJreg hJ hJc α K hK hKt 0
  let C := B * (∑ i, ‖((chartModelBasis E).coord i).toContinuousLinearMap‖) ^ 2 *
    (∑ k, ‖chartModelBasis E k‖)
  have hC : 0 ≤ C := by positivity
  refine ⟨C + 1, by positivity, ?_⟩
  intro b t ht x hx u v
  have hb' (i j k) : ‖chartChristoffel (g t) (α b) i j k x‖ ≤ B := by
    simpa only [norm_iteratedFDeriv_zero] using hb b i j k t ht x hx
  exact (norm_chartChristoffelContraction_le (g t) (α b) x u v hB.le hb').trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith : C ≤ C + 1) (norm_nonneg u)) (norm_nonneg v))


theorem exists_finite_extChartAt_prod_euclidean_bounds [I.Boundaryless] [CompactSpace M]
    [T2Space M] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (hJc : IsCompact J) :
    ∃ ρ C B : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < B ∧ ∃ S : Finset M, ∃ K : M → Set E,
      (∀ p ∈ S, IsCompact (K p) ∧ K p ⊆ (extChartAt I p).target) ∧
      (∀ q, ∃ p ∈ S, q ∈ (extChartAt I p).source ∧
        Metric.closedBall (extChartAt I p q) ρ ⊆ K p) ∧
      (∀ p ∈ S, ∀ t ∈ J, ∀ q ∈ (extChartAt I p).source, extChartAt I p q ∈ K p →
        ∀ z₀ z : V, ∀ v : TangentSpace (I.prod 𝓘(ℝ, V)) (q, z),
          Real.sqrt (((g t).prod (euclideanMetric (E := V))).inner (q, z) v v) ≤ C *
            ‖(trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) (p, z₀)).continuousLinearMapAt
              ℝ (q, z) v‖ ∧
          ‖(trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) (p, z₀)).continuousLinearMapAt
              ℝ (q, z) v‖ ≤
            C * Real.sqrt (((g t).prod (euclideanMetric (E := V))).inner (q, z) v v)) ∧
      (∀ p ∈ S, ∀ t ∈ J, ∀ q ∈ (extChartAt I p).source, extChartAt I p q ∈ K p →
        ∀ z₀ z : V, ∀ u v : E × V,
          ‖chartChristoffelContraction ((g t).prod (euclideanMetric (E := V))) (p, z₀) u v
            (extChartAt I p q, z)‖ ≤ B * ‖u‖ * ‖v‖) := by
  obtain ⟨ρ, C, hρ, hC, S, K, hK, hcover, hnorm⟩ :=
    exists_finite_extChartAt_prod_euclidean_norm_comparison (V := V) hg hJreg hJc
  have hKt (p : S) : K p ⊆ interior (extChartAt I (p : M)).target := by
    rw [(isOpen_extChartAt_target (I := I) (p : M)).interior_eq]
    exact (hK p p.property).2
  obtain ⟨B, hB, hΓ⟩ := exists_chartChristoffelContraction_bound_on_compact hg hJreg hJ hJc
    (fun p : S => (p : M)) (fun p => K p) (fun p => (hK p p.property).1) hKt
  refine ⟨ρ, C, B, hρ, hC, hB, S, K, hK, hcover, hnorm, ?_⟩
  intro p hp t ht q hq hx z₀ z u v
  have hgood : q ∈ chartLeviCivitaGoodSet (I := I) p := by
    rwa [chartLeviCivitaGoodSet_eq_extChartAt_source]
  rw [chartChristoffelContraction_prod_euclideanMetric (g t) p hgood,
    Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  exact (hΓ ⟨p, hp⟩ t ht (extChartAt I p q) hx u.1 v.1).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (norm_fst_le u) hB.le)
      (norm_fst_le v) (norm_nonneg _) (mul_nonneg hB.le (norm_nonneg u)))

theorem exists_finite_extChartAt_prod_euclidean_linear_bounds [I.Boundaryless] [CompactSpace M]
    [T2Space M] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (A : (E × V) ≃L[ℝ] F)
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (hJc : IsCompact J) :
    ∃ ρ C B : ℝ, 0 < ρ ∧ 0 < C ∧ 0 < B ∧ ∃ S : Finset M, ∃ K : M → Set E,
      (∀ p ∈ S, IsCompact (K p) ∧ K p ⊆ (extChartAt I p).target) ∧
      (∀ q, ∃ p ∈ S, q ∈ (extChartAt I p).source ∧
        Metric.closedBall (extChartAt I p q) ρ ⊆ K p) ∧
      (∀ p ∈ S, ∀ t ∈ J, ∀ q ∈ (extChartAt I p).source, extChartAt I p q ∈ K p →
        ∀ z₀ z : V, ∀ v : TangentSpace (I.prod 𝓘(ℝ, V)) (q, z),
          Real.sqrt (((g t).prod (euclideanMetric (E := V))).inner (q, z) v v) ≤ C *
            ‖A ((trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) (p, z₀)).continuousLinearMapAt
              ℝ (q, z) v)‖ ∧
          ‖A ((trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) (p, z₀)).continuousLinearMapAt
              ℝ (q, z) v)‖ ≤
            C * Real.sqrt (((g t).prod (euclideanMetric (E := V))).inner (q, z) v v)) ∧
      (∀ p ∈ S, ∀ t ∈ J, ∀ q ∈ (extChartAt I p).source, extChartAt I p q ∈ K p →
        ∀ z₀ z : V, ∀ u v : E × V,
          ‖A (chartChristoffelContraction ((g t).prod (euclideanMetric (E := V))) (p, z₀) u v
            (extChartAt I p q, z))‖ ≤ B * ‖A u‖ * ‖A v‖) := by
  obtain ⟨ρ, C, B, hρ, hC, hB, S, K, hK, hcover, hnorm, hΓ⟩ :=
    exists_finite_extChartAt_prod_euclidean_bounds (V := V) hg hJreg hJ hJc
  let a := ‖A.toContinuousLinearMap‖
  let b := ‖A.symm.toContinuousLinearMap‖
  let d := a + b + 1
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have had : a ≤ d := by dsimp [d]; linarith
  have hbd : b ≤ d := by dsimp [d]; linarith
  have hA (v : E × V) : ‖A v‖ ≤ a * ‖v‖ := A.toContinuousLinearMap.le_opNorm v
  have hAi (v : E × V) : ‖v‖ ≤ b * ‖A v‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, A.symm_apply_apply] using
      A.symm.toContinuousLinearMap.le_opNorm (A v)
  refine ⟨ρ, C * d, a * B * b ^ 2 + 1, hρ, mul_pos hC hd, by positivity,
    S, K, hK, hcover, ?_, ?_⟩
  · intro p hp t ht q hq hx z₀ z v
    let w := (trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) (p, z₀)).continuousLinearMapAt
      ℝ (q, z) v
    obtain ⟨hlow, hupp⟩ := hnorm p hp t ht q hq hx z₀ z v
    constructor
    · calc
        _ ≤ C * ‖w‖ := hlow
        _ ≤ C * (b * ‖A w‖) := mul_le_mul_of_nonneg_left (hAi w) hC.le
        _ ≤ C * d * ‖A w‖ := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hbd (norm_nonneg (A w))) hC.le
    · calc
        ‖A w‖ ≤ a * ‖w‖ := hA w
        _ ≤ a * (C * Real.sqrt _) := mul_le_mul_of_nonneg_left hupp ha
        _ ≤ C * d * Real.sqrt _ := by
          nlinarith only [mul_le_mul_of_nonneg_right had
            (mul_nonneg hC.le (Real.sqrt_nonneg (((g t).prod euclideanMetric).inner (q, z) v v)))]
  · intro p hp t ht q hq hx z₀ z u v
    have h := mul_le_mul_of_nonneg_left (hΓ p hp t ht q hq hx z₀ z u v) ha
    have hprod := mul_le_mul (hAi u) (hAi v) (norm_nonneg _) (mul_nonneg hb (norm_nonneg _))
    have hprod' := mul_le_mul_of_nonneg_left hprod (mul_nonneg ha hB.le)
    calc
      _ ≤ a * ‖chartChristoffelContraction ((g t).prod euclideanMetric) (p, z₀) u v
          (extChartAt I p q, z)‖ := hA _
      _ ≤ a * (B * ‖u‖ * ‖v‖) := h
      _ ≤ (a * B * b ^ 2 + 1) * ‖A u‖ * ‖A v‖ := by
        nlinarith only [hprod', mul_nonneg (norm_nonneg (A u)) (norm_nonneg (A v))]

theorem exists_uniform_extChartAt_prod_euclidean_bounds [I.Boundaryless] [CompactSpace M] [T2Space M]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : (E × V) ≃L[ℝ] F) {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ}
    (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn ℝ J) (hJc : IsCompact J) :
    ∃ R C B : ℝ, 0 < R ∧ 1 ≤ C ∧ 0 ≤ B ∧ ∀ x : M × V, ∃ β : M × V,
      let e := (chartAt (ModelProd H V) β).transHomeomorph
        (((I.prod 𝓘(ℝ, V)).toHomeomorph).trans A.toHomeomorph)
      let U := e.symm '' Metric.closedBall (e x) R
      x ∈ e.source ∧ Metric.closedBall (e x) R ⊆ e.target ∧
      (∀ t ∈ J, ∀ z ∈ U, ∀ v : TangentSpace (I.prod 𝓘(ℝ, V)) z,
        Real.sqrt (((g t).prod (euclideanMetric (E := V))).inner z v v) ≤ C *
          ‖A ((trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) β).continuousLinearMapAt ℝ z v)‖ ∧
        ‖A ((trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) β).continuousLinearMapAt ℝ z v)‖ ≤
          C * Real.sqrt (((g t).prod (euclideanMetric (E := V))).inner z v v)) ∧
      (∀ t ∈ J, ∀ z ∈ U, ∀ v w : E × V,
        ‖A (chartChristoffelContraction ((g t).prod (euclideanMetric (E := V))) β v w
          (extChartAt (I.prod 𝓘(ℝ, V)) β z))‖ ≤ B * ‖A v‖ * ‖A w‖) := by
  obtain ⟨ρ, C, B, hρ, hC, hB, S, K, hK, hcover, hnorm, hΓ⟩ :=
    hg.exists_finite_extChartAt_prod_euclidean_linear_bounds A hJreg hJ hJc
  let d := ‖A.symm.toContinuousLinearMap‖ + 1
  let R := ρ / (2 * d)
  have hd : 0 < d := by dsimp [d]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have had : ‖A.symm.toContinuousLinearMap‖ ≤ d := by dsimp [d]; linarith
  refine ⟨R, C + 1, B, hR, by linarith only [hC], hB.le, ?_⟩
  intro x
  obtain ⟨p, hp, hxp, hball⟩ := hcover x.1
  let β : M × V := (p, 0)
  let e := (chartAt (ModelProd H V) β).transHomeomorph
    (((I.prod 𝓘(ℝ, V)).toHomeomorph).trans A.toHomeomorph)
  have heval (z : M × V) : e z = A (extChartAt I p z.1, z.2) := by
    change A (extChartAt (I.prod 𝓘(ℝ, V)) β z) = _
    rw [extChartAt_prod]
    rfl
  have hsource (z : M × V) : z ∈ e.source ↔ z.1 ∈ (extChartAt I p).source := by
    change (z.1 ∈ (chartAt H p).source ∧ z.2 ∈ (univ : Set V)) ↔ _
    simp only [mem_univ, and_true, extChartAt_source]
  have hcoords : A.symm (e x) = (extChartAt I p x.1, x.2) := by rw [heval, A.symm_apply_apply]
  have hbase (w : F) (hw : w ∈ Metric.closedBall (e x) R) : (A.symm w).1 ∈ K p := by
    apply hball
    change dist (A.symm w).1 (extChartAt I p x.1) ≤ ρ
    have hwn : ‖w - e x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    calc
      dist (A.symm w).1 (extChartAt I p x.1) = ‖(A.symm (w - e x)).1‖ := by
        rw [map_sub, hcoords, dist_eq_norm]
        rfl
      _ ≤ ‖A.symm (w - e x)‖ := norm_fst_le _
      _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖w - e x‖ := A.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ d * R := mul_le_mul had hwn (norm_nonneg _) hd.le
      _ = ρ / 2 := by dsimp only [R]; field_simp
      _ ≤ ρ := by linarith only [hρ]
  have htarget : Metric.closedBall (e x) R ⊆ e.target := by
    intro w hw
    have hwt : (A.symm w).1 ∈ (extChartAt I p).target := (hK p hp).2 (hbase w hw)
    let z : M × V := ((extChartAt I p).symm (A.symm w).1, (A.symm w).2)
    have hz : z ∈ e.source := (hsource z).mpr ((extChartAt I p).map_target hwt)
    have heq : e z = w := by
      rw [heval]
      change A (extChartAt I p ((extChartAt I p).symm (A.symm w).1), (A.symm w).2) = w
      rw [(extChartAt I p).right_inv hwt]
      exact A.apply_symm_apply w
    rw [← heq]
    exact e.map_source hz
  have hregion (z : M × V) (hz : z ∈ e.symm '' Metric.closedBall (e x) R) :
      z.1 ∈ (extChartAt I p).source ∧ extChartAt I p z.1 ∈ K p := by
    obtain ⟨w, hw, rfl⟩ := hz
    have hs := e.map_target (htarget hw)
    have heq := congrArg (fun v => (A.symm v).1) (e.right_inv (htarget hw))
    rw [heval, A.symm_apply_apply] at heq
    refine ⟨(hsource _).mp hs, ?_⟩
    change extChartAt I p (e.symm w).1 = (A.symm w).1 at heq
    rw [heq]
    exact hbase w hw
  refine ⟨β, (hsource x).mpr hxp, htarget, ?_, ?_⟩
  · intro t ht z hz v
    obtain ⟨hzs, hzk⟩ := hregion z hz
    obtain ⟨hlow, hupp⟩ := hnorm p hp t ht z.1 hzs hzk (0 : V) z.2 v
    constructor
    · exact hlow.trans (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) (norm_nonneg _))
    · exact hupp.trans (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) (Real.sqrt_nonneg _))
  · intro t ht z hz v w
    obtain ⟨hzs, hzk⟩ := hregion z hz
    have hh := hΓ p hp t ht z.1 hzs hzk (0 : V) z.2 v w
    change ‖A (chartChristoffelContraction ((g t).prod (euclideanMetric (E := V))) β v w
      (extChartAt (I.prod 𝓘(ℝ, V)) β z))‖ ≤ _
    rw [extChartAt_prod]
    exact hh

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
