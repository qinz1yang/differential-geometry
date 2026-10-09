import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampGlobalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.PreparedRampFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductFamilyContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductLiftInvariants

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E H Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [T2Space Q] [CompactSpace Q]
  {P : Type*} [TopologicalSpace P] [CompactSpace P]
  {D : RealTimeInterval} {a b : ℝ}

theorem exists_continuous_prepared_ramp_family_on_Icc
    (B : RicciBackground (I := I) (M := Q) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda)
    {N : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) N)
    (prepared : RegularFamily (I := I) (Q := Q) P)
    (hsmooth : HasContinuousSmoothLoopJets e prepared) :
    ∃ solutions : P → ProductCurve Q,
      @Continuous P (ProductCurve Q) inferInstance
        (smoothProductCylinderTopology e (Icc a b)) solutions ∧
      ∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
        (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
        (solutions p).degree = 1 ∧
        ∀ z, (solutions p).map z a = ((prepared p).1 z, z) := by
  obtain ⟨d, had, hdb, seed, hseed, hseedsol, _, _⟩ :=
    exists_continuous_prepared_ramp_family_curvature_bound B lambda hlambda e prepared hsmooth
  choose solutions hsol hramp hagree using fun p =>
    (seed p).exists_ramp_solution_on_Icc B lambda hlambda had hdb
      (hseedsol p).1 (hseedsol p).2.1
  have htrace (p : P) (z : Surgery.Topology.Circle) :
      (solutions p).map z a = (seed p).map z a := hagree p z a ⟨le_rfl, had.le⟩
  refine ⟨solutions, continuous_product_solution_family_of_initial_agreement B lambda hlambda
    had e seed hseed (fun p => (hseedsol p).1) solutions hsol htrace, ?_⟩
  intro p
  have hycont : Continuous (fun x => (solutions p).y x a) :=
    (contDiffOn_univ.mp ((hsol p).smooth.2.comp
      (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun x _ => ⟨mem_univ x, le_rfl, B.lt.le⟩))).continuous
  have hseedcont : Continuous (fun x => (seed p).y x a) :=
    (contDiffOn_univ.mp ((hseedsol p).1.smooth.2.comp
      (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun x _ => ⟨mem_univ x, le_rfl, had.le⟩))).continuous
  have hdegree : (solutions p).degree = 1 :=
    ((solutions p).degree_eq_of_snd_map_eq (seed p) hycont.continuousOn hseedcont.continuousOn
      (fun z => congrArg Prod.snd (htrace p z))).trans (hseedsol p).2.2.1
  exact ⟨hsol p, hramp p, hdegree, fun z => (htrace p z).trans ((hseedsol p).2.2.2 z)⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
