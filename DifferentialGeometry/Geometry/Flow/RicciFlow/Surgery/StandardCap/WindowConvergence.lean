import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

universe u
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem metricCInfConvergenceOnCompacts_of_insertion_windows
    (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace H (P n)]
    [∀ n, IsManifold I ∞ (P n)] [∀ n, T2Space (P n)]
    (g : ∀ n, SmoothRiemannianMetric I (P n)) (x : ∀ n, P n)
    (delta : ℕ → ℝ) (order m : ℕ → ℕ)
    (datum : ∀ n, normalizedDatum (g n) (x n) (delta n) (order n))
    (A radius error : ℕ → ℝ) (hA : ∀ n, 0 < A n)
    (w : ∀ n, CanonicalStaticInsertionWitness (datum n) (A n) (hA n)
      (radius n) (m n) (error n))
    (hm : Tendsto m atTop atTop) (hradius : Tendsto radius atTop atTop)
    (herror : Tendsto error atTop (𝓝 0))
    (D : ℝ) (hD : ∀ n, D ≤ radius n) :
    MetricCInfConvergenceOnCompacts
      (fun n => (w n).windowMetric.restrictOpenOfSubset
        (fun _ hx => hx.trans_le (add_le_add (hD n) (le_refl 1)) :
          standardCapWindow D ≤ standardCapWindow (radius n)))
      (metric.restrictOpen (standardCapWindow D)) (metric.restrictOpen (standardCapWindow D)) := by
  let _ (n : ℕ) : SigmaCompactSpace (standardCapWindow (radius n)) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow (radius n)).isOpen)
  intro K _ p e he
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (((hm.eventually_ge_atTop p).and (hradius.eventually_ge_atTop (D + 1))).and
      (herror.eventually (Iio_mem_nhds he)))
  refine ⟨N,fun n hn => ?_⟩
  let hsub : standardCapWindow D ≤ standardCapWindow (radius n) :=
    fun _ hx => hx.trans_le (add_le_add (hD n) (le_refl 1))
  apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall K p _ _ _ (error n)
    (w n).accuracy_pos.le ?_) (hN n hn).2
  intro j hj y _
  have hnorm := metricDerivNorm_flat hsub (w n).windowMetric
    (metric.restrictOpen (standardCapWindow (radius n)))
    (metric.restrictOpen (standardCapWindow (radius n))) j y
  rw [SmoothRiemannianMetric.restrictOpen_flat] at hnorm
  rw [hnorm]
  have hclose := (w n).properties.window_close
  change metricDerivENormSupOn
    {z : standardCapWindow (radius n) | (riemannianEDistOf metric 0 z.val).toReal < radius n}
    (m n) (w n).windowMetric (metric.restrictOpen (standardCapWindow (radius n)))
      (metric.restrictOpen (standardCapWindow (radius n))) < ENNReal.ofReal (error n) at hclose
  simp only [distance_zero] at hclose
  exact (metricDerivNorm_lt_of_sup_lt _ _ _ _ _ hclose (hj.trans (hN n hn).1.1)
    (y.property.trans_le (hN n hn).1.2)).le

theorem metricCInfConvergenceOnCompacts_of_compatible_insertion_windows
    (P : ℕ → ℕ → Type u) [∀ n i, TopologicalSpace (P n i)] [∀ n i, ChartedSpace H (P n i)]
    [∀ n i, IsManifold I ∞ (P n i)] [∀ n i, T2Space (P n i)]
    (g : ∀ n i, SmoothRiemannianMetric I (P n i)) (x : ∀ n i, P n i)
    (delta : ℕ → ℕ → ℝ) (order m : ℕ → ℕ → ℕ)
    (datum : ∀ n i, normalizedDatum (g n i) (x n i) (delta n i) (order n i))
    (A error : ℕ → ℕ → ℝ) (hA : ∀ n i, 0 < A n i)
    (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
    (w : ∀ n i, CanonicalStaticInsertionWitness (datum n i) (A n i) (hA n i)
      (radius n) (m n i) (error n i))
    (hm : ∀ n, Tendsto (m n) atTop atTop)
    (herror : ∀ n, Tendsto (error n) atTop (𝓝 0))
    (N : ℕ → ℕ)
    (hcompat : ∀ n l, ∀ᶠ i in atTop,
      ((w n (i - N n)).windowMetric).restrictOpenOfSubset
        (inf_le_left : standardCapWindow (radius n) ⊓ standardCapWindow (radius l) ≤ _) =
      ((w l (i - N l)).windowMetric).restrictOpenOfSubset
        (inf_le_right : standardCapWindow (radius n) ⊓ standardCapWindow (radius l) ≤ _)) :
    ∀ n, MetricCInfConvergenceOnCompacts (fun i => (w n i).windowMetric)
      (metric.restrictOpen (standardCapWindow (radius n)))
      (metric.restrictOpen (standardCapWindow (radius n))) := by
  let _ (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)
  intro n K hK p e he
  obtain ⟨l, hl⟩ := (hradius.eventually_gt_atTop (radius n + 1)).exists
  have hsub : standardCapWindow (radius n) ≤ standardCapWindow (radius l) := by
    intro y hy
    change ‖y‖ < radius l + 1
    change ‖y‖ < radius n + 1 at hy
    linarith
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp
    (((hm l).eventually_ge_atTop p).and ((herror l).eventually (Iio_mem_nhds he)))
  obtain ⟨j₁, hj₁⟩ := eventually_atTop.mp (hcompat n l)
  refine ⟨j₀ + j₁ + N l, ?_⟩
  intro i hi
  let k := i + N n - N l
  have hk : j₀ ≤ k := by dsimp only [k]; omega
  have heq := hj₁ (i + N n) (by omega)
  rw [Nat.add_sub_cancel] at heq
  have hmet : (w n i).windowMetric = (w l k).windowMetric.restrictOpenOfSubset hsub := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v z
    let y' : (standardCapWindow (radius n) ⊓ standardCapWindow (radius l) : TopologicalSpace.Opens ThreeSpace) :=
      ⟨y.val, y.property, hsub y.property⟩
    exact congrArg (fun G => G.inner y' v z) heq
  dsimp only
  rw [hmet]
  apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall K p _ _ _ (error l k)
    (w l k).accuracy_pos.le ?_) (hj₀ k hk).2
  intro j hj y _
  have hnorm := metricDerivNorm_flat hsub (w l k).windowMetric
    (metric.restrictOpen (standardCapWindow (radius l)))
    (metric.restrictOpen (standardCapWindow (radius l))) j y
  rw [SmoothRiemannianMetric.restrictOpen_flat] at hnorm
  rw [hnorm]
  have hclose := (w l k).properties.window_close
  change metricDerivENormSupOn
    {z : standardCapWindow (radius l) | (riemannianEDistOf metric 0 z.val).toReal < radius l}
    (m l k) (w l k).windowMetric (metric.restrictOpen (standardCapWindow (radius l)))
      (metric.restrictOpen (standardCapWindow (radius l))) < ENNReal.ofReal (error l k) at hclose
  simp only [distance_zero] at hclose
  exact (metricDerivNorm_lt_of_sup_lt _ _ _ _ _ hclose (hj.trans (hj₀ k hk).1)
    (y.property.trans hl)).le

end DifferentialGeometry.PDE.RicciFlow.StandardCap
