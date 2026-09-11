import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.RoundingJets
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private theorem collar_subset {A B : ℝ} (hAB : 2 * A < B) :
    insertionCylinder A B ≤ DifferentialGeometry.Geometry.Neck.openCylinder B := by
  intro q hq
  change -2 * A < q.2 ∧ q.2 < B at hq
  change -B < q.2 ∧ q.2 < B
  exact ⟨by linarith [hq.1], hq.2⟩

theorem insertionMap_isLocalDiffeomorph {A B : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) :
    IsLocalDiffeomorph IC (𝓡 3) ∞ (insertionMap hA hAB) :=
  isLocalDiffeomorph_of_injective_mfderiv (insertionMap hA hAB)
    (contMDiff_insertionMap hA hAB) (insertionMap_mfderiv_injective hA hAB) (by simp)

def insertedPullbackMetric {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    SmoothRiemannianMetric IC (insertionCylinder A B) :=
  pullbackMetricOfInjectiveLocalDiffeomorph (insertedMetric hA hAB hη h)
    (insertionMap hA hAB) (insertionMap_isLocalDiffeomorph hA hAB)
    (injective_insertionMap hA hAB)

theorem insertedPullbackMetric_inner {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (v w : TangentSpace IC q) :
    (insertedPullbackMetric hA hAB hη h).inner q v w =
      (insertedMetric hA hAB hη h).inner (insertionMap hA hAB q)
        (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v)
        (mfderiv IC (𝓡 3) (insertionMap hA hAB) q w) :=
  pullbackMetricOfInjectiveLocalDiffeomorph_inner _ _ _ _ _ _ _

theorem insertedPullbackMetric_rounded_inner {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (hq : -5 * A / 4 ≤ q.val.2)
    (v w : TangentSpace IC q) :
    (insertedPullbackMetric hA hAB hη h).inner q v w =
      Real.exp (2 * conformalFactor q.val.2) *
        (h.restrictOpenOfSubset (collar_subset hAB)).inner q v w := by
  have hc : insertionCutoff A q.val.2 = 1 := by
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hA).mpr
    linarith
  rw [insertedPullbackMetric_inner, insertedMetric_interpolation, hc]
  simp only [one_mul, sub_self, zero_mul, add_zero]
  rfl

theorem insertedPullbackMetric_metricCovDeriv_at_height_zero {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (gRef : SmoothRiemannianMetric IC (insertionCylinder A B))
    (q : insertionCylinder A B) (hq : q.val.2 = 0) (m : ℕ) :
    metricCovDeriv (insertedPullbackMetric hA hAB hη h) gRef m q =
      metricCovDeriv (h.restrictOpenOfSubset (collar_subset hAB)) gRef m q := by
  let : SigmaCompactSpace (insertionCylinder A B) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC (insertionCylinder A B).isOpen)
  let W : Opens (insertionCylinder A B) :=
    ⟨{y | -5 * A / 4 < y.val.2},
      isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)⟩
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC W.isOpen)
  let h₀ := h.restrictOpenOfSubset (collar_subset hAB)
  let r := conformalMetricOfContDiff h₀
    (fun y : insertionCylinder A B => conformalFactor y.val.2)
    (contDiff_conformalFactor.contMDiff.comp
      (contMDiff_snd.comp (contMDiff_subtype_val (I := IC) (U := insertionCylinder A B))))
  have hW : q ∈ W := by change -5 * A / 4 < q.val.2; rw [hq]; linarith
  have heq : ∀ y : insertionCylinder A B, y ∈ W →
      ∀ v w : TangentSpace IC y,
        (insertedPullbackMetric hA hAB hη h).inner y v w = r.inner y v w := by
    intro y hy v w
    rw [conformalMetricOfContDiff_inner]
    exact insertedPullbackMetric_rounded_inner hA hAB hη h y (show -5 * A / 4 ≤ y.val.2 from (show -5 * A / 4 < y.val.2 from hy).le) v w
  have hjet : metricCovDeriv (insertedPullbackMetric hA hAB hη h) gRef m q =
      metricCovDeriv r gRef m q := by
    ext slots
    exact metricCovDeriv_eq_of_eqOn _ _ gRef W heq m ⟨q, hW⟩ slots
  exact hjet.trans (metricCovDeriv_conformalFactor_eq_at_height_zero
    (insertionCylinder A B) h₀ gRef q hq m)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
