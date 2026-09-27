import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import DifferentialGeometry.Geometry.Metric.Path.Length

noncomputable section

open scoped Bundle ContDiff Manifold Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_contMDiff_curve_endpoints [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p y : M) {a b : ℝ} (hab : a ≠ b) :
    ∃ alpha : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha a = p ∧ alpha b = y := by
  let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  obtain ⟨path, hpath, _⟩ :=
    Manifold.exists_path_isContMDiffWithSittingInstants_of_riemannianEDist_lt
      (I := I) (Manifold.riemannianEDist_lt_top (I := I) p y)
  let alpha : ℝ → M := fun t ↦ path.extend ((t - a) / (b - a))
  have halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha := by
    apply hpath.contMDiff.comp
    rw [contMDiff_iff_contDiff]
    fun_prop
  refine ⟨alpha, halpha, ?_, ?_⟩
  · simp only [alpha, sub_self, zero_div, Path.extend_zero]
  · simp only [alpha, div_self (sub_ne_zero.mpr hab.symm), Path.extend_one]

end DifferentialGeometry
