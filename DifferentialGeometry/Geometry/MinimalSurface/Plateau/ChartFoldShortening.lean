import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SourceChartReplacement
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.FoldShortening

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology ContDiff Manifold NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- Apply the strict folded-patch variation to the literal disk in local
source coordinates, then paste the improvement into its chart image. -/
theorem exists_disk_area_lt_of_chart_fold_divergence_neg
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {L : ℝ≥0} (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    {n : WithTop ℕ∞} (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ n)
    (hn : 1 ≤ n) (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    (hinside : e '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    {W : Set M} (huW : Set.range u ⊆ W) :
    let d := diskThroughSourceChart u e hsrc
    ∀ (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (_hΦ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (_hΦzero : ∀ x, Φ 0 x = x)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (_hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x)))
    (_hvelocity : ∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => Φ t x) 0 1 = Y x)
    (p r : ℝ)
    (_hpr : ‖(p : ℂ)‖ + r < 1)
    (_hfix : ∀ t z, z ∈ Metric.sphere (p : ℂ) r →
      Φ t (diskExtension d z) = diskExtension d z)
    (_hΦW : ∀ t, MapsTo (Φ t) W W)
    (_hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension d)
      (Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (_hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension d ∘ conj)
      (Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (_hi : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d) z))
    (_hir : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ conj) z))
    (_hnegative :
      (∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
        ambientDivergenceWithin g (diskExtension d) (closedHalfDisk p r) Y z) +
      (∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
        ambientDivergenceWithin g (diskExtension d ∘ conj) (closedHalfDisk p r) Y z) < 0),
    ∃ (v : C(closedDisk, M)) (K : ℝ≥0),
      (∀ z w, riemannianEDistOf g (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      riemannianDiskArea g v < riemannianDiskArea g u := by
  dsimp only
  intro Φ hΦ hΦzero Y hY hvelocity p r hpr hfix hΦW hU hUr hi hir hnegative
  let d := diskThroughSourceChart u e hsrc
  obtain ⟨C, hdLip⟩ := diskThroughSourceChart_lipschitz g u huLip e hn hsrc
  have hdW : Set.range d ⊆ W := diskThroughSourceChart_range u e hsrc huW
  obtain ⟨d', K, hd'Lip, hd'trace, hd'W, hd'area⟩ :=
    exists_disk_area_lt_of_fold_divergence_neg g d hdLip Φ hΦ hΦzero Y hY hvelocity
      p r hpr hfix hdW hΦW hU hUr hi hir hnegative
  exact exists_disk_area_lt_of_sourceChart_competitor g u d' huLip hd'Lip e hn hsrc hinside
    hd'trace huW hd'W hd'area

end DifferentialGeometry.Geometry
