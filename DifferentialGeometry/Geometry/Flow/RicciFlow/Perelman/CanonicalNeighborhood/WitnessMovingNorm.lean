import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessNormalizedNormConvergence


set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance movingNormC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

omit [CompleteSpace E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem exists_compact_chart_sequence (p : M)
    {V : Set E} (hV : IsOpen V) (hpV : extChartAt I p p ∈ V)
    (y : ℕ → M) (hy : Tendsto y atTop (𝓝 p)) :
    ∃ (K : Set E) (z : ℕ → E), IsCompact K ∧ K ⊆ V ∧ extChartAt I p p ∈ K ∧
      (∀ n, z n ∈ K) ∧ Tendsto z atTop (𝓝 (extChartAt I p p)) ∧
      ∀ᶠ n in atTop, (extChartAt I p).symm (z n) = y n := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  let K := Metric.closedBall (extChartAt I p p) (r / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKV : K ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hpK : extChartAt I p p ∈ K := Metric.mem_closedBall_self (by linarith)
  have hchart : Tendsto (fun n => extChartAt I p (y n)) atTop (𝓝 (extChartAt I p p)) :=
    (continuousAt_extChartAt (I := I) p).tendsto.comp hy
  have hnear : ∀ᶠ n in atTop, extChartAt I p (y n) ∈ K :=
    hchart (Metric.closedBall_mem_nhds _ (by linarith))
  let z (n : ℕ) := if extChartAt I p (y n) ∈ K then extChartAt I p (y n)
    else extChartAt I p p
  have hzK (n : ℕ) : z n ∈ K := by
    dsimp only [z]
    split_ifs with hn
    · exact hn
    · exact hpK
  have heq : z =ᶠ[atTop] (fun n => extChartAt I p (y n)) := by
    filter_upwards [hnear] with n hn
    exact if_pos hn
  have hz := (tendsto_congr' heq).2 hchart
  refine ⟨K, z, hK, hKV, hpK, hzK, hz, ?_⟩
  filter_upwards [heq, hy (extChartAt_source_mem_nhds (I := I) p)] with n hn hsrc
  rw [hn, (extChartAt I p).left_inv hsrc]


theorem weighted_error_covariant_norm_tendsto_at_point
    (g : ℝ → SmoothRiemannianMetric I M)
    (A B : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2) (p : M)
    {V : Set E} (hV : IsOpen V) (hpV : extChartAt I p p ∈ V)
    (hVt : V ⊆ (extChartAt I p).target)
    {J L : Set ℝ}
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartGramOnE (I := I) (g z.1) p i j z.2) (L ×ˢ V))
    (hA : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => A z.1 ((extChartAt I p).symm z.2)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z.2))) (J ×ˢ V))
    (hB : ∀ slots : Fin 2 → Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : ℝ × E => B z.1 ((extChartAt I p).symm z.2)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z.2))) (L ×ˢ V))
    (tau upsilon : ℕ → ℝ) (htau : ∀ n, tau n ∈ J) (hupsilon : ∀ n, upsilon n ∈ L)
    {t u : ℝ} (ht : t ∈ J) (hu : u ∈ L)
    (htlim : Tendsto tau atTop (𝓝 t)) (hulim : Tendsto upsilon atTop (𝓝 u))
    (c alpha beta : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    {c₀ alpha₀ beta₀ : ℝ} (hc₀ : 0 < c₀)
    (hclim : Tendsto c atTop (𝓝 c₀))
    (halim : Tendsto alpha atTop (𝓝 alpha₀)) (hblim : Tendsto beta atTop (𝓝 beta₀))
    (y : ℕ → M) (hy : Tendsto y atTop (𝓝 p)) (a : ℕ) :
    Tendsto (fun n => tensor02CovDerivNormWith (I := I) a
      (alpha n • A (tau n) - beta n • B (upsilon n))
      (scaleMetric (c n) (hc n) (g (upsilon n)))
      (scaleMetric (c n) (hc n) (g (upsilon n))) (y n))
      atTop (𝓝 (tensor02CovDerivNormWith (I := I) a
        (alpha₀ • A t - beta₀ • B u)
        (scaleMetric c₀ hc₀ (g u)) (scaleMetric c₀ hc₀ (g u)) p)) := by
  obtain ⟨K, z, hK, hKV, hpK, hzK, hz, heq⟩ := exists_compact_chart_sequence p hV hpV y hy
  have hn := weighted_error_covariant_norm_tendsto g A B p hV hVt hgram hA hB
    tau upsilon htau hupsilon ht hu htlim hulim c alpha beta hc hc₀ hclim halim hblim
    hK hKV z hzK hpK hz a
  rw [(extChartAt I p).left_inv (mem_extChartAt_source p)] at hn
  apply hn.congr'
  filter_upwards [heq] with n hn
  rw [hn]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
