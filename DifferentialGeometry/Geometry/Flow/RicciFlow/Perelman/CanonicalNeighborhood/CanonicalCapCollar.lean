import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone

set_option autoImplicit false
open scoped ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D}
  {eps C1 C2 alpha : ℝ} {x : M} {t : ℝ}

def CanonicalWitness.capTubeHasNeckChart
    (K : CanonicalWitness S eps C1 C2 x t) (alpha : ℝ) : Prop :=
  ∀ (cap : LocalCap S eps x t K.domain.carrier)
    (depth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y),
    K.alternative = CanonicalAlternative.cap cap depth →
      ∃ (v : M) (nk : StrongNeck S alpha v t), ∀ z, cap.tubeMap z = nk.map z

theorem CanonicalWitness.capTubeHasNeckChart.enlarge_constants
    {K : CanonicalWitness S eps C1 C2 x t}
    (h : K.capTubeHasNeckChart alpha) {C1' C2' : ℝ}
    (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2') :
    (K.enlargeConstants hC1 hC2).capTubeHasNeckChart alpha := by
  intro cap depth heq
  change K.alternative.monoConstant
    (zero_lt_one.trans_le K.one_le_comparison_constant) hC2 K.Q_pos.le =
      CanonicalAlternative.cap cap depth at heq
  cases halt : K.alternative with
  | neck data =>
    rw [halt] at heq
    cases heq
  | cap data deep =>
    rw [halt] at heq
    change CanonicalAlternative.cap data deep = CanonicalAlternative.cap cap depth at heq
    cases heq
    exact h _ _ halt
  | positive whole data sec =>
    rw [halt] at heq
    cases heq
  | round whole data =>
    rw [halt] at heq
    cases heq

theorem CanonicalWitness.capTubeHasNeckChart.mono_eps
    {K : CanonicalWitness S eps C1 C2 x t}
    (h : K.capTubeHasNeckChart alpha) {eps' : ℝ}
    (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    (K.monoEps heps hsmall).capTubeHasNeckChart alpha := by
  intro cap depth heq
  change K.alternative.monoEps K.eps_pos heps hsmall =
    CanonicalAlternative.cap cap depth at heq
  cases halt : K.alternative with
  | neck data =>
    rw [halt] at heq
    cases heq
  | cap data deep =>
    rw [halt] at heq
    change CanonicalAlternative.cap (data.monoEps heps hsmall) deep =
      CanonicalAlternative.cap cap depth at heq
    cases heq
    exact h _ _ halt
  | positive whole data sec =>
    rw [halt] at heq
    cases heq
  | round whole data =>
    rw [halt] at heq
    cases heq

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
