import DifferentialGeometry.Geometry.Operator.MetricFamilyJointRegularity
import DifferentialGeometry.Geometry.Metric.Family.PairSmoothness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

namespace MetricFamilySmoothOn

omit [CompleteSpace E] in
private theorem metric_joint_contMDiffOn
    {D : RealTimeInterval} {g : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    {J : Set Real} (hJreg : J ⊆ D.regular) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (Set.univ : Set M)) := by
  intro p hp
  exact (hG.metricCLMSmoothAt (t := p.1) (x := p.2)
    (D.regular_isOpen.mem_nhds (hJreg hp.1))).contMDiffWithinAt

omit [CompleteSpace E] in
theorem chartGramMatrix_contDiffOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJ : J ⊆ D.regular) (α : M)
    (i j : Fin (Module.finrank Real E)) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => chartGramMatrix (I := I) (G.metric p.1) α p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  exact chartGramMatrix_joint_contMDiffOn G.metric J (metric_joint_contMDiffOn hG hJ) α i j

omit [CompleteSpace E] in
theorem chartGramMatrix_continuousOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJ : J ⊆ D.regular) (α : M)
    (i j : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × M => chartGramMatrix (I := I) (G.metric p.1) α p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  exact (chartGramMatrix_contDiffOn hG hJ α i j).continuousOn

omit [CompleteSpace E] in
theorem chartGramOnE_contDiffOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJ : J ⊆ D.regular) (α : M)
    (i j : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E => chartGramOnE (I := I) (G.metric p.1) α i j p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  exact DifferentialGeometry.Geometry.Curvature.chartGramOnE_contDiffOn_of_contMDiffOn
    G.metric (metric_joint_contMDiffOn hG hJ) α i j

omit [CompleteSpace E] in
theorem chartGram_jet_continuousOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) {S : Set (Real × M)}
    (hS : S ⊆ J ×ˢ chartLeviCivitaGoodSet (I := I) α)
    (k : Nat) (hk : k ≤ 2) (i j : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun q : Real × M =>
        iteratedFDeriv Real k
          (chartGramOnE (I := I) (G.metric q.1) α i j)
          (extChartAt I α q.2)) S := by
  exact DifferentialGeometry.Geometry.Curvature.chartGram_jet_continuousOn_of_contMDiffOn
    G.metric (metric_joint_contMDiffOn hG hJreg) hJ α hS k hk i j

omit [CompleteSpace E] in
theorem chartGramPartialOnE_contDiffOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) (m i j : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E =>
        partialDeriv (E := E) m (chartGramOnE (I := I) (G.metric p.1) α i j) p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  exact DifferentialGeometry.Geometry.Curvature.chartGramPartialOnE_contDiffOn_of_contMDiffOn
    G.metric (metric_joint_contMDiffOn hG hJreg) hJ α m i j

omit [CompleteSpace E] in
theorem chartInvGramOnE_contDiffOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (α : M)
    (a b : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E => chartInvGramOnE (I := I) (G.metric p.1) α a b p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  exact DifferentialGeometry.Geometry.Curvature.chartInvGramOnE_contDiffOn_of_contMDiffOn
    G.metric (metric_joint_contMDiffOn hG hJreg) α a b

omit [CompleteSpace E] in
theorem chartInvGramOnE_continuousOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (α : M)
    (a b : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × E => chartInvGramOnE (I := I) (G.metric p.1) α a b p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  exact DifferentialGeometry.Geometry.Curvature.chartInvGramOnE_continuousOn_of_contMDiffOn
    G.metric (metric_joint_contMDiffOn hG hJreg) α a b

omit [CompleteSpace E] in
theorem chartChristoffelOnE_contDiffOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) (i j k : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E => chartChristoffel (I := I) (G.metric p.1) α i j k p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  exact DifferentialGeometry.Geometry.Curvature.chartChristoffelOnE_contDiffOn_of_contMDiffOn
    G.metric (metric_joint_contMDiffOn hG hJreg) hJ α i j k

omit [CompleteSpace E] in
theorem chartChristoffelOnE_continuousOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) (i j k : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × E => chartChristoffel (I := I) (G.metric p.1) α i j k p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  exact DifferentialGeometry.Geometry.Curvature.chartChristoffelOnE_continuousOn_of_contMDiffOn
    G.metric (metric_joint_contMDiffOn hG hJreg) hJ α i j k

omit [CompleteSpace E] in
theorem gradient_continuousOn [I.Boundaryless]
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    {ρ : M → Real}
    (hρ : ContMDiff I (modelWithCornersSelf Real Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        (TotalSpace.mk' E p.2
          (gradFun (I := I) (G.metric p.1) ρ p.2) : TangentBundle I M))
      (J ×ˢ (Set.univ : Set M)) := by
  exact DifferentialGeometry.Geometry.Curvature.gradient_continuousOn_of_contMDiffOn
    G.metric (metric_joint_contMDiffOn hG hJreg) hρ

omit [CompleteSpace E] in
theorem gradient_norm_sq_continuousOn [I.Boundaryless]
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) ρ p.2)
          (gradientFun (I := I) (G.metric p.1) ρ p.2))
      (J ×ˢ (Set.univ : Set M)) := by
  exact DifferentialGeometry.Geometry.Curvature.gradient_norm_sq_continuousOn_of_contMDiffOn
    G.metric (metric_joint_contMDiffOn hG hJreg) hρ

omit [CompleteSpace E] in
theorem leviCivitaLaplacian_continuousOn [I.Boundaryless] [T2Space M]
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        laplacian (I := I) (LeviCivita (I := I) (G.metric p.1))
          (G.metric p.1) ρ p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  exact DifferentialGeometry.Geometry.Curvature.leviCivitaLaplacian_continuousOn_of_contMDiffOn
    G.metric (metric_joint_contMDiffOn hG hJreg) hJ hρ

end MetricFamilySmoothOn

namespace MetricConnectionFamily

omit [CompleteSpace E] in
theorem gradientAt_continuousOn [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    {ρ : M → Real}
    (hρ : ContMDiff I (modelWithCornersSelf Real Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        (TotalSpace.mk' E p.2
          (gradientAt (I := I) G p.1 ρ p.2) : TangentBundle I M))
      (J ×ˢ (Set.univ : Set M)) := by
  have h := MetricFamilySmoothOn.gradient_continuousOn
    (I := I) (G := G.restrict D) hG hJreg hρ
  have hfun : (fun p : Real × M =>
      (TotalSpace.mk' E p.2 (gradientAt (I := I) G p.1 ρ p.2) : TangentBundle I M)) =
      fun p : Real × M =>
        (TotalSpace.mk' E p.2 (gradFun (I := I) (G.metric p.1) ρ p.2) : TangentBundle I M) := by
    funext p
    congr 1
  rw [hfun]
  simpa only [MetricConnectionFamily.restrict_metric] using h

omit [CompleteSpace E] in
theorem gradient_norm_sq_continuousOn [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) ρ p.2)
          (gradientFun (I := I) (G.metric p.1) ρ p.2))
      (J ×ˢ (Set.univ : Set M)) := by
  simpa only [MetricConnectionFamily.restrict_metric] using
    MetricFamilySmoothOn.gradient_norm_sq_continuousOn
      (I := I) (G := G.restrict D) hG hJreg hρ

omit [CompleteSpace E] in
theorem laplacianAt_continuousOn [I.Boundaryless] [T2Space M]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (hconn : ∀ t ∈ J,
      G.connection t = LeviCivita (I := I) (G.metric t))
    {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn (fun p : Real × M => laplacianAt (I := I) G p.1 ρ p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  have hlevi := MetricFamilySmoothOn.leviCivitaLaplacian_continuousOn
    (I := I) (G := G.restrict D) hG hJreg hJ hρ
  refine hlevi.congr ?_
  intro p hp
  simp only [MetricConnectionFamily.restrict_metric]
  rw [laplacianAt_eq, hconn p.1 hp.1]

omit [CompleteSpace E] in
theorem heatOperatorWithDrift_continuousOn [I.Boundaryless] [T2Space M]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (hconn : ∀ t ∈ J,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (X : Real → (x : M) → TangentSpace I x)
    {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ)
    (hdrift : ContinuousOn (fun p : Real × M =>
      driftTerm (I := I) G p.1 (X p.1) ρ p.2)
      (J ×ˢ (Set.univ : Set M))) :
    ContinuousOn (fun p : Real × M =>
      heatOperatorWithDrift (I := I) G p.1 (X p.1) ρ p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  have h := (G.laplacianAt_continuousOn hG hJreg hJ hconn hρ).add hdrift
  change ContinuousOn (fun p : Real × M =>
    laplacianAt (I := I) G p.1 ρ p.2 + driftTerm (I := I) G p.1 (X p.1) ρ p.2)
      (J ×ˢ (Set.univ : Set M)) at h
  exact h

omit [CompleteSpace E] in
theorem driftTerm_continuousOn [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJreg : J ⊆ D.regular)
    (X : ℝ → (x : M) → TangentSpace I x)
    (hX : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (J ×ˢ (Set.univ : Set M)))
    {rho : M → ℝ} (hrho : ContMDiff I 𝓘(ℝ, ℝ) ∞ rho) :
    ContinuousOn (fun p : ℝ × M =>
      driftTerm (I := I) G p.1 (X p.1) rho p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  intro p hp
  have hmetric := (hG.metricCLMSmoothAt (t := p.1) (x := p.2)
    (D.regular_isOpen.mem_nhds (hJreg hp.1))).continuousAt.continuousWithinAt (s := J ×ˢ (Set.univ : Set M))
  have hgrad := G.gradientAt_continuousOn hG hJreg hrho p hp
  have hpair : ContinuousWithinAt
      (fun q : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) q.2
        ((G.metric q.1).inner q.2 (X q.1 q.2)
          (gradientAt (I := I) G q.1 rho q.2)))
      (J ×ˢ (Set.univ : Set M)) p :=
    hmetric.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (hX p hp) hgrad
  simp only [FiberBundle.continuousWithinAt_totalSpace] at hpair
  exact hpair.2

end MetricConnectionFamily

end DifferentialGeometry.Geometry.Curvature
