import DifferentialGeometry.Geometry.Metric.LipschitzApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.LocalLipschitz
import DifferentialGeometry.Geometry.Metric.Distance.Lipschitz
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Bundle.FiberBundleHausdorff

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_contMDiff_approx_of_riemannian_lipschitz
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ∀ x y, edist (f x) (f y) ≤ riemannianEDistOf g x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : C^∞⟮I, M; ℝ⟯, (∀ x, |F x - f x| ≤ ε) ∧
      ∀ x, ∀ v : TangentSpace I x,
        |mvfderiv I F x v| ≤ 3 * Real.sqrt (g.inner x v v) := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  have hlocal (x : M) := exists_contMDiffOn_approx_of_riemannian_lipschitz g hf x
  obtain ⟨F, hF, happrox, hderiv⟩ :=
    Operator.exists_contMDiff_approx_with_mvfderiv_bound_of_local g f 2 (fun x => by
      obtain ⟨U, hx, hu⟩ := hlocal x
      refine ⟨U, U.isOpen, hx, ?_⟩
      intro δ hδ
      obtain ⟨u, hs, ha, hd⟩ := hu δ hδ
      exact ⟨u, hs, fun y hy => (ha y hy).le, hd⟩) hε
  exact ⟨⟨F, hF⟩, happrox, by norm_num at hderiv ⊢; exact hderiv⟩


theorem exists_contMDiff_riemannianDistance_approx
    [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : C^∞⟮I, M; ℝ⟯,
      (∀ x, |ρ x - (riemannianEDistOf g p x).toReal| ≤ ε) ∧
      (∀ x, ∀ v : TangentSpace I x,
        |mvfderiv I ρ x v| ≤ 3 * Real.sqrt (g.inner x v v)) ∧
      ∀ x, Real.sqrt (g.inner x (Operator.gradFun g ρ x) (Operator.gradFun g ρ x)) ≤ 3 := by
  obtain ⟨ρ, happ, hd⟩ := exists_contMDiff_approx_of_riemannian_lipschitz g
    (riemannianDistance_toReal_lipschitz g p) hε
  exact ⟨ρ, happ, hd, fun x => grad_norm_le_of_mvfderiv_bound g (by norm_num) (hd x)⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiff_riemannianDistance_approx_isCompact_sublevel
    [PreconnectedSpace M] [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (p : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : C^∞⟮I, M; ℝ⟯,
      (∀ x, |ρ x - (riemannianEDistOf g p x).toReal| ≤ ε) ∧
      (∀ x, ∀ v : TangentSpace I x,
        |mvfderiv I ρ x v| ≤ 3 * Real.sqrt (g.inner x v v)) ∧
      (∀ x, Real.sqrt (g.inner x (Operator.gradFun g ρ x) (Operator.gradFun g ρ x)) ≤ 3) ∧
      ∀ R : ℝ, IsCompact {x : M | ρ x ≤ R} := by
  obtain ⟨ρ, happ, hd, hgrad⟩ := exists_contMDiff_riemannianDistance_approx g p hε
  refine ⟨ρ, happ, hd, hgrad, ?_⟩
  intro R
  apply (hg.closedEBall_isCompact p (R + ε)).of_isClosed_subset
    (isClosed_le ρ.contMDiff.continuous continuous_const)
  intro x hx
  have hdist : (riemannianEDistOf g p x).toReal ≤ R + ε := by
    have habs := (abs_le.mp (happ x)).1
    change ρ x ≤ R at hx
    linarith
  change riemannianEDistOf g p x ≤ ENNReal.ofReal (R + ε)
  rw [← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top g p x)]
  exact ENNReal.ofReal_le_ofReal hdist

end DifferentialGeometry.Geometry.Metric
