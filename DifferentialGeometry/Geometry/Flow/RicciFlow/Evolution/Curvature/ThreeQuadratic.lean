import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem coord_metric_spacetime_of_carrier_eq_regular
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hD : D.carrier = D.regular) (x₀ : M) :
    MetricFrameSpacetimeRegularityInFrameOnLocal S (coordInv S x₀)
      (coordInvDt S x₀) (coordinateFrameAt (I := I) x₀)
      (coordinateFrameSet (I := I) x₀) := by
  refine
    { metricSmooth := ?_
      nondegenerateGram := coordInvLocal S x₀
      inverseMetricDerivative := coordInvDerivLocal S hS x₀
      uniqueTimeDerivatives := fun t =>
        uniqueDiffWithinAt_of_mem_nhds (D.regular_mem_nhds t.2)
      frameMetricSpacetimeSmooth := ?_
      frameMetricExtDerivTimeDerivative := ?_ }
  · intro x hx i j
    rw [hD]
    intro t ht
    have h := (coordMetricSmoothAt S hS x₀ ⟨t, ht⟩ x hx i j).comp t
      (contMDiffAt_id.prodMk contMDiffAt_const)
    rw [contMDiffAt_iff_contDiffAt] at h
    exact h.contDiffWithinAt
  · intro i j
    rw [hD]
    exact hS.smoothMetric.frameCompSmooth _
      (coordinateFrameAt_isLocalFrame (I := I) x₀) i j
  · intro t x hx d a b
    have h := coordMetricDeriv S hS x₀ a b t t.2 x hx
      (coordinateFrameAt (I := I) x₀ d x)
    convert h using 1
    rw [mvfderiv_const_mul (I := I) (-2 : ℝ) (coordRicciMdiff S x₀ t x hx a b)]
    rfl

theorem riemann_hasDerivAt_three_quadratic_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (x₀ : M) (t : D.RegularTime)
    (m : Fin 4 → CoordinateIdx (𝕜 := ℝ) E) :
    HasDerivAt
      (fun s : ℝ => solutionCurvatureComponents S x₀ s x₀ m)
      (rmLap (coordInv S x₀ t x₀) (nab2RmComp S x₀ t x₀)
          (m 0) (m 1) (m 2) (m 3) +
        rmQuad (coordInv S x₀ t x₀) (rmComp S x₀ t x₀)
          (m 0) (m 1) (m 2) (m 3) -
        rmDrift (ricciOneUpCompInFrame S (coordInv S x₀)
          (coordinateFrameAt (I := I) x₀) t x₀) (rmComp S x₀ t x₀)
          (m 0) (m 1) (m 2) (m 3)) t := by
  let D' : RealTimeInterval :=
    { carrier := D.regular
      regular := D.regular
      initial := t
      initial_mem := t.2
      regular_subset := Set.Subset.rfl
      regular_isOpen := D.regular_isOpen
      regular_mem_nhds := fun ht => D.regular_isOpen.mem_nhds ht }
  let S' := S.timeRestrict D'
  have hS' : IsSolutionOn S' := isSoln_timeRestrict hS D.regular_subset Set.Subset.rfl
  have hreg := coord_metric_spacetime_of_carrier_eq_regular S' hS' rfl x₀
  have h := (rm04Evol_at S' hS' x₀ (coordInvDt S' x₀) hreg ⟨t, t.2⟩ m).hasDerivAt
    (D.regular_isOpen.mem_nhds t.2)
  refine h.congr_deriv ?_
  rw [rmQuad_eq_b _ (rm04SymmOfSol S x₀ t x₀)
    (coordInvSymmOn S x₀ t (coordinateFrameAt_mem (I := I) x₀))]
  simp only [neg_mul, sub_eq_add_neg]
  rfl

theorem riemann_hasDerivAt_three_quadratic_raised_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (x₀ : M) (t : D.RegularTime)
    (m : Fin 4 → CoordinateIdx (𝕜 := ℝ) E) :
    HasDerivAt
      (fun s : ℝ => S.base.rm04 s x₀ (fun q => coordBasisAt (I := I) x₀ (m q)))
      (roughLap0SField
          (S.family.metric t) (S.base.rm04 t) x₀
          (fun q => coordBasisAt (I := I) x₀ (m q)) +
        (∑ p, ∑ q, ∑ r, coordInv S x₀ t x₀ p q *
          (christoffelCurvCoeffAt (S.family.connection t) x₀ (m 0) (m 1) p r *
              rmComp S x₀ t x₀ r q (m 2) (m 3) -
            2 * christoffelCurvCoeffAt (S.family.connection t) x₀ p (m 0) (m 2) r *
              rmComp S x₀ t x₀ (m 1) q r (m 3) +
            2 * rmComp S x₀ t x₀ p (m 0) r (m 3) *
              christoffelCurvCoeffAt (S.family.connection t) x₀ (m 1) q (m 2) r)) -
        ((∑ p, ricciOneUpCompInFrame S (coordInv S x₀)
            (coordinateFrameAt (I := I) x₀) t x₀ (m 0) p *
              rmComp S x₀ t x₀ p (m 1) (m 2) (m 3)) +
          (∑ p, ricciOneUpCompInFrame S (coordInv S x₀)
            (coordinateFrameAt (I := I) x₀) t x₀ (m 1) p *
              rmComp S x₀ t x₀ (m 0) p (m 2) (m 3)) +
          (∑ p, ricciOneUpCompInFrame S (coordInv S x₀)
            (coordinateFrameAt (I := I) x₀) t x₀ (m 2) p *
              rmComp S x₀ t x₀ (m 0) (m 1) p (m 3)) +
          (∑ p, ricciOneUpCompInFrame S (coordInv S x₀)
            (coordinateFrameAt (I := I) x₀) t x₀ (m 3) p *
              rmComp S x₀ t x₀ (m 0) (m 1) (m 2) p))) t := by
  have h := riemann_hasDerivAt_three_quadratic_of_solution S hS x₀ t m
  have hlap := rm04LapFam_real S (t : ℝ) x₀ (m 0) (m 1) (m 2) (m 3)
  have hvec : vec4 (I := I)
      (coordBasisAt (I := I) x₀ (m 0)) (coordBasisAt (I := I) x₀ (m 1))
      (coordBasisAt (I := I) x₀ (m 2)) (coordBasisAt (I := I) x₀ (m 3)) =
      fun q => coordBasisAt (I := I) x₀ (m q) := by
    funext q
    fin_cases q <;> rfl
  rw [hvec] at hlap
  change rmLap _ _ _ _ _ _ = _ at hlap
  rw [hlap, rmQuad_eq_sum_raised _ _ _ (rmRaise S x₀ t)] at h
  simpa only [solutionCurvatureComponents_apply, coordBasisAt_coe, rmDrift] using h

end DifferentialGeometry.PDE.RicciFlow
