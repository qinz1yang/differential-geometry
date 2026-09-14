import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ProductLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Descent

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M]

theorem exists_quotientProduct_ricciBackground_on_regular [I.Boundaryless]
    (A : QuotientProductAtlas I M) {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) :
    ∃ D' : RealTimeInterval, D'.carrier = D.regular ∧ D'.regular = D.regular ∧
      ∀ lambda : ℝ, ∀ hlambda : 0 < lambda,
        letI := A.charts
        letI := A.smoothManifold
        ∃ Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) D' a b,
          Bhat.family = quotientProductFamily A B.family lambda hlambda ∧
          Bhat.B₀ = B.B₀ ∧ Bhat.B₁ = B.B₁ ∧ Bhat.B₂ = B.B₂ ∧ Bhat.C = B.C := by
  let D' : RealTimeInterval := {
    carrier := D.regular
    regular := D.regular
    initial := a
    initial_mem := B.regular ⟨le_rfl, B.lt.le⟩
    regular_subset := Subset.rfl
    regular_isOpen := D.regular_isOpen
    regular_mem_nhds := fun ht => D.regular_isOpen.mem_nhds ht }
  let S : SolutionOn (I := I) (M := M) D' := ⟨B.family⟩
  have hD : UniqueDiffOn ℝ D'.carrier := D.regular_isOpen.uniqueDiffOn
  have hgj : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (B.family.metric p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (D'.carrier ×ˢ univ) := fun p hp =>
    (B.smooth.metricCLMSmoothAt (D.regular_isOpen.mem_nhds hp.1)).contMDiffWithinAt
  have hS : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn S := by
    apply isSolutionOn_of_joint_metric D' hD B.family.metric hgj
    intro t ht x v w
    simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor,
      SolutionOn.family_metric] using
      (metricDerivAt (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩)
        B.equation ⟨t, ht⟩ x v w).hasDerivWithinAt (s := D'.carrier)
  refine ⟨D', rfl, rfl, ?_⟩
  intro lambda hlambda
  let _ := A.charts
  let _ := A.smoothManifold
  let P := S.prod (SolutionOn.const (DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ))
    (lambda ^ 2) (pow_pos hlambda 2) (DifferentialGeometry.euclideanMetric (E := ℝ))) D')
  have hP : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn P :=
    isSolutionOn_prod_scaleMetric_euclideanMetric S hS (lambda ^ 2) (pow_pos hlambda 2)
  have hpj : ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ)))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
      (fun p : ℝ × (M × ℝ) => (⟨p.2, (P.family.metric p.1).inner p.2⟩ :
        TotalSpace ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
          (fun x => TangentSpace (I.prod 𝓘(ℝ, ℝ)) x →L[ℝ]
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) x →L[ℝ] ℝ)))
      (D'.carrier ×ˢ univ) := fun p hp =>
    (hP.smoothMetric.metricCLMSmoothAt (D.regular_isOpen.mem_nhds hp.1)).contMDiffWithinAt
  have hd := isSolutionOn_descendedMetric P hP (productCoverProjection (M := M))
    (isLocalDiffeomorph_productCoverProjection A) (surjective_productCoverProjection (M := M))
    hD hpj (fun t => metricFiberCompatible_coverProductMetric A (B.family.metric t) lambda hlambda)
  let Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) D' a b := {
    family := quotientProductFamily A B.family lambda hlambda
    smooth := hd.smoothMetric
    lt := B.lt
    regular := B.regular
    equation := hd
    B₀ := B.B₀
    B₁ := B.B₁
    B₂ := B.B₂
    B₀_nonneg := B.B₀_nonneg
    B₁_nonneg := B.B₁_nonneg
    B₂_nonneg := B.B₂_nonneg
    ricci_bound := by
      intro t ht q
      have hn := (quotientProduct_iterCov_normSq A (B.family.metric t) lambda hlambda 0 q).2
      simpa only [iterCov, Nat.rec_zero, Nat.add_zero, metricRicci_apply, SolutionFamily.ricciAt,
        quotientProductFamily] using hn.trans_le (B.ricci_bound t ht q.1)
    riemann_bound := by
      intro t ht q
      have hn := (quotientProduct_iterCov_normSq A (B.family.metric t) lambda hlambda 0 q).1
      simpa only [iterCov, Nat.rec_zero, Nat.add_zero, metricRm04_apply, SolutionFamily.rm04At,
        quotientProductFamily] using hn.trans_le (B.riemann_bound t ht q.1)
    nablaRicci_bound := by
      intro t ht q
      have hn := (quotientProduct_iterCov_normSq A (B.family.metric t) lambda hlambda 1 q).2
      have he := hn.trans_le (B.nablaRicci_bound t ht q.1)
      change normSq0S (quotientProductMetric A (B.family.metric t) lambda hlambda) q 3
        (covStep (quotientProductMetric A (B.family.metric t) lambda hlambda) 2
          (metricRicci (quotientProductMetric A (B.family.metric t) lambda hlambda)) q) ≤ B.B₂ ^ 2 at he
      simpa only [covStep_apply, SolutionFamily.connection, SolutionFamily.ricci,
        quotientProductFamily] using he }
  exact ⟨Bhat, rfl, rfl, rfl, rfl, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
