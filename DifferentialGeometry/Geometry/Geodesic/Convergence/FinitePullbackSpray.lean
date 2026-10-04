import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteMetricFlow
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients

/-!
# LC50′, field step: sprays of pulled-back coefficients on a tangent chart

For partial diffeomorphisms `j i : N → M i` whose sources eventually contain every compact set and
whose pulled-back chart coefficients `pullbackMetricCoefficients (g i) (j i ∘ φ⁻¹)` converge in
`C¹` on the compact subsets of every extended chart target to the coefficients of a `C^{r+1}`
metric `G` (`1 ≤ r`), the metric sprays converge uniformly on every compact subset of the target of
a tangent-bundle chart. The coefficients of `j i` need to be `C¹` only on a neighbourhood of the
compact set, which holds for a tail of the sequence; this is why CM-L4's
`tendstoUniformlyOn_metricSpray_of_mapCPConvergenceOn` is applied to a shifted sequence.

* `tendstoUniformlyOn_metricSpray_pullback`: the field clause of the first-exit kernel
  `eventually_mapsTo_chart_of_coordinate_ODE` for the lifted curves of LC50′.
* `contDiffOn_metricSpray_chartCoeff`: the limit field is `C¹` on the tangent chart target.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.MetricKoszul
open DifferentialGeometry.Geometry.MetricSmoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]

private local instance pullbackSprayDual : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

omit [FiniteDimensional ℝ E] in
private theorem two_le_succ_order {r : ℕ∞} (hr : 1 ≤ r) : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
  have h1 : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
  calc (2 : ℕ∞ω) = 1 + 1 := one_add_one_eq_two.symm
    _ ≤ (r : ℕ∞ω) + 1 := add_le_add_left h1 1

/-- The limit spray `metricSpray (chartCoeff G x₀)` of a `C^{r+1}` metric, `1 ≤ r`, is `C¹` on
`(extChartAt I x₀).target ×ˢ univ`, the target of every tangent chart over `x₀`'s chart. -/
theorem contDiffOn_metricSpray_chartCoeff {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _)) (x₀ : N) :
    ContDiffOn ℝ 1 (metricSpray (chartCoeff G x₀)) ((extChartAt I x₀).target ×ˢ univ) :=
  metricSpray_contDiffOn_succ (n := 1) (isOpen_extChartAt_target x₀)
    ((contDiffOn_chartCoeff G (two_le_succ_order hr) x₀).of_le (by norm_num))
    (fun _ hy => DifferentialGeometry.Analysis.isCoercive_of_pos_diagonal _ fun _ hv =>
      chartCoeff_pos G x₀ hy hv)

/-- **Field convergence for LC50′.** `C¹` convergence of the pulled-back chart coefficients in
every extended chart (LFR14's clause, at order one) and exhausting sources give uniform convergence
of the metric sprays on every compact subset of `(extChartAt I x₀).target ×ˢ univ`. -/
theorem tendstoUniformlyOn_metricSpray_pullback {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (g : ∀ i, SmoothRiemannianMetric I (M i)) {K : ℕ} (hK : 2 ≤ K)
    (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (x₀ : N) {C : Set (E × E)} (hC : IsCompact C)
    (hCt : C ⊆ (extChartAt I x₀).target ×ˢ univ) :
    TendstoUniformlyOn
      (fun i => metricSpray
        (pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x₀).symm)))
      (metricSpray (chartCoeff G x₀)) atTop C := by
  have hKle : ((K : ℕ) : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  set φ := extChartAt I x₀ with hφ
  have hU : IsOpen φ.target := isOpen_extChartAt_target x₀
  have hK₀ : IsCompact (Prod.fst '' C) := hC.image continuous_fst
  have hK₀U : Prod.fst '' C ⊆ φ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hCt hz).1
  obtain ⟨V, hVo, hK₀V, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK₀ hU hK₀U
  have hW : IsCompact (φ.symm '' closure V) :=
    hVc.image_of_continuousOn ((continuousOn_extChartAt_symm x₀).mono hVU)
  obtain ⟨i₁, hi₁⟩ := eventually_atTop.1 (hexh _ hW)
  have hshift : StrictMono (fun i : ℕ => i + i₁) := fun a b hab => Nat.add_lt_add_right hab i₁
  let b : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ := fun i =>
    pullbackMetricCoefficients (g (i + i₁)) ((j (i + i₁) : N → M (i + i₁)) ∘ φ.symm)
  have hb : ∀ i, ContDiffOn ℝ 1 (b i) V := by
    intro i
    have hF : ContMDiffOn 𝓘(ℝ, E) I K ((j (i + i₁) : N → M (i + i₁)) ∘ φ.symm) V :=
      (j (i + i₁)).contMDiffOn.comp
        (((contMDiffOn_extChartAt_symm x₀).of_le hKle).mono (subset_closure.trans hVU))
        (fun y hy => hi₁ (i + i₁) (Nat.le_add_left i₁ i) ⟨y, subset_closure hy, rfl⟩)
    exact Bundle.ContMDiffRiemannianMetric.contDiffOn_pullback_inner (g (i + i₁)) (r := 1) (s := (K : ℕ∞ω)) (by exact_mod_cast le_top)
      (by exact_mod_cast hK) hVo hF
  have hbInf : ContDiffOn ℝ 1 (chartCoeff G x₀) V :=
    ((contDiffOn_chartCoeff G (two_le_succ_order hr) x₀).of_le (by norm_num)).mono
      (subset_closure.trans hVU)
  have hco : ∀ y ∈ V, IsCoercive (chartCoeff G x₀ y) := fun y hy =>
    DifferentialGeometry.Analysis.isCoercive_of_pos_diagonal _ fun _ hv =>
      chartCoeff_pos G x₀ (hVU (subset_closure hy)) hv
  have hconvV : ∀ L : Set E, IsCompact L → L ⊆ V → MapCPConvergenceOn L 1 b (chartCoeff G x₀) :=
    fun L hL hLV => (hconv x₀ L hL (hLV.trans (subset_closure.trans hVU))).comp_subseq hshift
  have hmain := tendstoUniformlyOn_metricSpray_of_mapCPConvergenceOn hVo b (chartCoeff G x₀)
    hb hbInf hco hconvV hC (fun z hz => ⟨hK₀V ⟨z, hz, rfl⟩, trivial⟩)
  rw [Metric.tendstoUniformlyOn_iff] at hmain ⊢
  intro ε hε
  obtain ⟨a, ha⟩ := eventually_atTop.1 (hmain ε hε)
  refine eventually_atTop.2 ⟨a + i₁, fun i hi z hz => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, i = k + i₁ := ⟨i - i₁, by omega⟩
  exact ha k (by omega) z hz

end DifferentialGeometry.Geometry.Riemannian.Geodesic
