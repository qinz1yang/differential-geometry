import DifferentialGeometry.Analysis.Schauder.ParabolicChartRegularity
import DifferentialGeometry.Analysis.Schauder.ParabolicChartOperator

noncomputable section

open Matrix Set
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic.Euclidean

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

private abbrev EuclN (E : Type uE) [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] :=
  EuclideanSpace Real (Fin (Module.finrank Real E))

def parabolicChartPrincipalCoefficientExtension
    (center : EuclN E) (r R : Real)
    (g : Real → SmoothRiemannianMetric I M) (chartCenter : M)
    (p0 : ParabolicPoint (EuclN E))
    (i j : Fin (Module.finrank Real E)) :
    ParabolicPoint (EuclN E) → Real :=
  parabolicBallCutoffExtension center r R
    (parabolicChartPrincipalCoefficient (I := I) g chartCenter i j p0)
    (parabolicChartPrincipalCoefficient (I := I) g chartCenter i j)

def parabolicChartDriftCoefficientExtension
    (center : EuclN E) (r R : Real)
    (g : Real → SmoothRiemannianMetric I M) (chartCenter : M)
    (p0 : ParabolicPoint (EuclN E))
    (k : Fin (Module.finrank Real E)) :
    ParabolicPoint (EuclN E) → Real :=
  parabolicBallCutoffExtension center r R
    (parabolicChartDriftCoefficient (I := I) g chartCenter k p0)
    (parabolicChartDriftCoefficient (I := I) g chartCenter k)

def parabolicChartPotentialCoefficientExtension
    (center : EuclN E) (r R : Real)
    (V : Real → M → Real) (chartCenter : M)
    (p0 : ParabolicPoint (EuclN E)) :
    ParabolicPoint (EuclN E) → Real :=
  parabolicBallCutoffExtension center r R
    (parabolicChartPotentialCoefficient (I := I) V chartCenter p0)
    (parabolicChartPotentialCoefficient (I := I) V chartCenter)

theorem parabolicNondivergenceOperator_coefficientExtension_eq
    (center : EuclN E) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (g : Real → SmoothRiemannianMetric I M) (V : Real → M → Real)
    (chartCenter : M) (p0 : ParabolicPoint (EuclN E))
    (u : Real → EuclN E → Real) (p : ParabolicPoint (EuclN E))
    (hpSpace : p.space ∈ Metric.closedBall center r) :
    parabolicNondivergenceOperator
        (parabolicChartPrincipalCoefficientExtension (I := I)
          center r R g chartCenter p0)
        (parabolicChartDriftCoefficientExtension (I := I)
          center r R g chartCenter p0)
        (parabolicChartPotentialCoefficientExtension (I := I)
          center r R V chartCenter p0) u p =
      parabolicNondivergenceOperator
        (parabolicChartPrincipalCoefficient (I := I) g chartCenter)
        (parabolicChartDriftCoefficient (I := I) g chartCenter)
        (parabolicChartPotentialCoefficient (I := I) V chartCenter) u p := by
  have ha : ∀ i j,
      parabolicChartPrincipalCoefficientExtension (I := I)
          center r R g chartCenter p0 i j p =
        parabolicChartPrincipalCoefficient (I := I) g chartCenter i j p := by
    intro i j
    exact parabolicBallCutoffExtension_eq_of_mem_closedBall
      center hr hrR _ _ p hpSpace
  have hb : ∀ k,
      parabolicChartDriftCoefficientExtension (I := I)
          center r R g chartCenter p0 k p =
        parabolicChartDriftCoefficient (I := I) g chartCenter k p := by
    intro k
    exact parabolicBallCutoffExtension_eq_of_mem_closedBall
      center hr hrR _ _ p hpSpace
  have hc : parabolicChartPotentialCoefficientExtension (I := I)
        center r R V chartCenter p0 p =
      parabolicChartPotentialCoefficient (I := I) V chartCenter p :=
    parabolicBallCutoffExtension_eq_of_mem_closedBall
      center hr hrR _ _ p hpSpace
  have haAt : (fun i j ↦
      parabolicChartPrincipalCoefficientExtension (I := I)
        center r R g chartCenter p0 i j p) =
      fun i j ↦ parabolicChartPrincipalCoefficient (I := I)
        g chartCenter i j p := by
    funext i j
    exact ha i j
  unfold parabolicNondivergenceOperator parabolicVariableMatrixOperator
    parabolicVariableMatrixLap parabolicLowerOrderTerm
    parabolicDriftTerm parabolicPotentialTerm
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [haAt]
  simp_rw [hb, hc]

theorem parabolicNondivergenceOperator_coefficientExtension_eq_intrinsic_in_euclideanChart
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    (center : EuclN E) {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    (g : Real → SmoothRiemannianMetric I M) (V : Real → M → Real)
    (chartCenter : M) (p0 : ParabolicPoint (EuclN E))
    (u : Real → M → Real) (p : ParabolicPoint (EuclN E))
    (hu : ContMDiff I 𝓘(Real, Real) ∞ (u p.time))
    (hpSpace : p.space ∈ Metric.closedBall center r)
    (hpChart : (toEuclidean (E := E)).symm p.space ∈
      (extChartAt I chartCenter).target) :
    parabolicNondivergenceOperator
        (parabolicChartPrincipalCoefficientExtension (I := I)
          center r R g chartCenter p0)
        (parabolicChartDriftCoefficientExtension (I := I)
          center r R g chartCenter p0)
        (parabolicChartPotentialCoefficientExtension (I := I)
          center r R V chartCenter p0)
        (parabolicEuclideanChartRepresentation I chartCenter u) p =
      fderiv Real (fun t ↦
          u t (euclideanChartPoint (I := I) chartCenter p)) p.time 1 -
        laplacian (I := I) (LeviCivita (I := I) (g p.time)) (g p.time)
          (u p.time) (euclideanChartPoint (I := I) chartCenter p) -
        V p.time (euclideanChartPoint (I := I) chartCenter p) *
          u p.time (euclideanChartPoint (I := I) chartCenter p) := by
  rw [parabolicNondivergenceOperator_coefficientExtension_eq
    (I := I) center hr hrR g V chartCenter p0
      (parabolicEuclideanChartRepresentation I chartCenter u) p hpSpace]
  exact parabolicNondivergenceOperator_eq_intrinsic_in_euclideanChart
    (I := I) g V chartCenter u p hu hpChart

end DifferentialGeometry.Analysis.Schauder

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

open DifferentialGeometry.Analysis.Schauder

universe v vE vH

variable {E : Type vE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type vH} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type v} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

private abbrev EuclM (E : Type vE) [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] :=
  EuclideanSpace Real (Fin (Module.finrank Real E))

theorem exists_parabolic_chart_nondivergence_operator_coefficient_extension_schauder_bounds
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {a b : Real} (hab : a < b) (habreg : Set.Icc a b ⊆ D.regular)
    (chartCenter : M) (center : EuclM E) {R Rext : Real}
    (hR : 0 ≤ R) (hRRext : R < Rext)
    (hchart : ((toEuclidean (E := E)).symm : EuclM E → E) ''
      Metric.closedBall center Rext ⊆
        interior (extChartAt I chartCenter).target)
    (V : Real → M → Real)
    (hV : ContDiffOn Real 1
      (fun p : Real × E ↦ V p.1 ((extChartAt I chartCenter).symm p.2))
      (Set.Icc a b ×ˢ
        (((toEuclidean (E := E)).symm : EuclM E → E) ''
          Metric.closedBall center Rext)))
    {alpha : NNReal} (halpha : alpha ≤ 1)
    (p0 : ParabolicPoint (EuclM E))
    (hp0Time : p0.time ∈ Set.Icc a b)
    (hp0Space : p0.space ∈ Metric.closedBall center R) :
    ∃ A Ka : Fin (Module.finrank Real E) →
          Fin (Module.finrank Real E) → NNReal,
      ∃ Bb Kb : Fin (Module.finrank Real E) → NNReal,
      ∃ Bc Kc : NNReal,
      (∀ i j p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
        ‖parabolicChartPrincipalCoefficientExtension (I := I)
          center R Rext G.metric chartCenter p0 i j p‖ ≤ A i j) ∧
      (∀ i j, HolderWith (Ka i j) alpha
        ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
          (parabolicChartPrincipalCoefficientExtension (I := I)
            center R Rext G.metric chartCenter p0 i j))) ∧
      (Matrix.of fun i j : Fin (Module.finrank Real E) =>
        parabolicChartPrincipalCoefficientExtension (I := I)
          center R Rext G.metric chartCenter p0 i j p0).PosDef ∧
      (∀ i j p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
        ‖parabolicChartPrincipalCoefficientExtension (I := I)
            center R Rext G.metric chartCenter p0 i j p0 -
          parabolicChartPrincipalCoefficientExtension (I := I)
            center R Rext G.metric chartCenter p0 i j p‖ ≤
          A i j + A i j) ∧
      (∀ i j p, p.space ∈ Metric.closedBall center R →
        parabolicChartPrincipalCoefficientExtension (I := I)
            center R Rext G.metric chartCenter p0 i j p =
          parabolicChartPrincipalCoefficient (I := I) G.metric
            chartCenter i j p) ∧
      (∀ k p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
        ‖parabolicChartDriftCoefficientExtension (I := I)
          center R Rext G.metric chartCenter p0 k p‖ ≤ Bb k) ∧
      (∀ k, HolderWith (Kb k) alpha
        ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
          (parabolicChartDriftCoefficientExtension (I := I)
            center R Rext G.metric chartCenter p0 k))) ∧
      (∀ k p, p.space ∈ Metric.closedBall center R →
        parabolicChartDriftCoefficientExtension (I := I)
            center R Rext G.metric chartCenter p0 k p =
          parabolicChartDriftCoefficient (I := I) G.metric
            chartCenter k p) ∧
      (∀ p, p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
        ‖parabolicChartPotentialCoefficientExtension (I := I)
          center R Rext V chartCenter p0 p‖ ≤ Bc) ∧
      HolderWith Kc alpha
        ((parabolicCylinder (Set.Icc a b) Set.univ).restrict
          (parabolicChartPotentialCoefficientExtension (I := I)
            center R Rext V chartCenter p0)) ∧
      ∀ p, p.space ∈ Metric.closedBall center R →
        parabolicChartPotentialCoefficientExtension (I := I)
            center R Rext V chartCenter p0 p =
          parabolicChartPotentialCoefficient (I := I) V chartCenter p := by
  obtain ⟨Apr, Kapr, Bbpr, Kbpr, Bcpr, Kcpr,
      hAnorm, ha, hpos, hbnorm, hb, hcnorm, hc⟩ :=
    exists_parabolic_chart_nondivergence_operator_coefficient_schauder_bounds_on_closedBall
      hG hab habreg chartCenter center Rext hchart V hV halpha
  let apr : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → ParabolicPoint (EuclM E) → Real :=
    parabolicChartPrincipalCoefficient (I := I) G.metric chartCenter
  let bpr : Fin (Module.finrank Real E) →
      ParabolicPoint (EuclM E) → Real :=
    parabolicChartDriftCoefficient (I := I) G.metric chartCenter
  let cpr : ParabolicPoint (EuclM E) → Real :=
    parabolicChartPotentialCoefficient (I := I) V chartCenter
  let A : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → NNReal := fun i j ↦
    parabolicBallCutoffExtensionSupConst (Apr i j) (apr i j p0)
  let Ka : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → NNReal := fun i j ↦
    parabolicBallCutoffExtensionHolderConst R Rext
      (Kapr i j) (Apr i j) (apr i j p0)
  let Bb : Fin (Module.finrank Real E) → NNReal := fun k ↦
    parabolicBallCutoffExtensionSupConst (Bbpr k) (bpr k p0)
  let Kb : Fin (Module.finrank Real E) → NNReal := fun k ↦
    parabolicBallCutoffExtensionHolderConst R Rext
      (Kbpr k) (Bbpr k) (bpr k p0)
  let Bc : NNReal := parabolicBallCutoffExtensionSupConst Bcpr (cpr p0)
  let Kc : NNReal := parabolicBallCutoffExtensionHolderConst R Rext
    Kcpr Bcpr (cpr p0)
  have hball : parabolicCylinder (Set.Icc a b) (Metric.ball center Rext) ⊆
      parabolicCylinder (Set.Icc a b) (Metric.closedBall center Rext) := by
    intro p hp
    exact ⟨hp.1, Metric.ball_subset_closedBall hp.2⟩
  have hglobalA : ∀ i j p,
      p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖parabolicBallCutoffExtension center R Rext
        (apr i j p0) (apr i j) p‖ ≤ A i j := by
    intro i j
    exact norm_parabolicBallCutoffExtension_le center hR hRRext
      (apr i j p0) (apr i j)
        (fun p hp ↦ hAnorm i j p (hball hp))
  have hglobalB : ∀ k p,
      p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖parabolicBallCutoffExtension center R Rext
        (bpr k p0) (bpr k) p‖ ≤ Bb k := by
    intro k
    exact norm_parabolicBallCutoffExtension_le center hR hRRext
      (bpr k p0) (bpr k)
        (fun p hp ↦ hbnorm k p (hball hp))
  have hglobalC : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) Set.univ →
      ‖parabolicBallCutoffExtension center R Rext
        (cpr p0) cpr p‖ ≤ Bc :=
    norm_parabolicBallCutoffExtension_le center hR hRRext
      (cpr p0) cpr (fun p hp ↦ hcnorm p (hball hp))
  refine ⟨A, Ka, Bb, Kb, Bc, Kc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [parabolicChartPrincipalCoefficientExtension, apr, A] using hglobalA
  · intro i j
    simpa only [parabolicChartPrincipalCoefficientExtension, apr, Ka] using
      (parabolicBallCutoffExtension_holderWith (alpha := alpha)
        (zero_le alpha) halpha center hR hRRext (apr i j p0) (apr i j)
        (((HolderWith.restrict_iff.mp (ha i j)).mono hball).holderWith)
        (fun p hp ↦ hAnorm i j p (hball hp)))
  · have hp0Outer : p0 ∈ parabolicCylinder (Set.Icc a b)
        (Metric.closedBall center Rext) :=
      ⟨hp0Time, Metric.closedBall_subset_closedBall hRRext.le hp0Space⟩
    simpa only [parabolicChartPrincipalCoefficientExtension, apr,
      parabolicBallCutoffExtension_eq_of_mem_closedBall center hR hRRext
        (apr _ _ p0) (apr _ _) p0 hp0Space] using hpos p0 hp0Outer
  · intro i j p hp
    exact (norm_sub_le _ _).trans
      (add_le_add (hglobalA i j p0 ⟨hp0Time, Set.mem_univ p0.space⟩)
        (hglobalA i j p hp))
  · intro i j p hp
    exact parabolicBallCutoffExtension_eq_of_mem_closedBall
      center hR hRRext (apr i j p0) (apr i j) p hp
  · simpa only [parabolicChartDriftCoefficientExtension, bpr, Bb] using hglobalB
  · intro k
    simpa only [parabolicChartDriftCoefficientExtension, bpr, Kb] using
      (parabolicBallCutoffExtension_holderWith (alpha := alpha)
        (zero_le alpha) halpha center hR hRRext (bpr k p0) (bpr k)
        (((HolderWith.restrict_iff.mp (hb k)).mono hball).holderWith)
        (fun p hp ↦ hbnorm k p (hball hp)))
  · intro k p hp
    exact parabolicBallCutoffExtension_eq_of_mem_closedBall
      center hR hRRext (bpr k p0) (bpr k) p hp
  · simpa only [parabolicChartPotentialCoefficientExtension, cpr, Bc] using hglobalC
  · simpa only [parabolicChartPotentialCoefficientExtension, cpr, Kc] using
      (parabolicBallCutoffExtension_holderWith (alpha := alpha)
        (zero_le alpha) halpha center hR hRRext (cpr p0) cpr
        (((HolderWith.restrict_iff.mp hc).mono hball).holderWith)
        (fun p hp ↦ hcnorm p (hball hp)))
  · intro p hp
    exact parabolicBallCutoffExtension_eq_of_mem_closedBall
      center hR hRRext (cpr p0) cpr p hp

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

end
