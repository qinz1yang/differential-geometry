import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTensorContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.IntrinsicDerivation
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BoundaryDerivLimit

noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab

universe u
variable {P : OrientedThreeStage.{u}} {a b : ℝ} (G : P.ClosedSlab a b)

theorem scalar_gradient_norm_sq_continuousOn :
    ContinuousOn (fun p : ℝ × P.Carrier => (G.flow.base.metric p.1).inner p.2
      (gradientFun (G.flow.base.metric p.1) (G.flow.scalar p.1) p.2)
      (gradientFun (G.flow.base.metric p.1) (G.flow.scalar p.1) p.2))
      (Icc a b ×ˢ univ) :=
  scalar_gradient_norm_sq_continuousOn_of_joint_metric G.flow.base.metric
    G.smoothUpTo.jointContMDiffOn

theorem scalar_evolution_rhs_continuousOn :
    ContinuousOn (fun p : ℝ × P.Carrier =>
      laplacianAt (flowG G.flow) p.1 (G.flow.scalar p.1) p.2 +
        2 * normSq0S (G.flow.base.metric p.1) p.2 2 (G.flow.ricci p.1 p.2))
      (Icc a b ×ˢ univ) := by
  have hlap := scalar_laplacian_continuousOn_of_joint_metric G.flow.base.metric
    G.smoothUpTo.jointContMDiffOn
  have hric := P.tensorFamily_normSq_continuousOn
    G.equation.smoothMetric.metricTensor_cont G.equation.ricciCont
  exact hlap.add (continuousOn_const.mul hric)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable {P : OrientedThreeStage.{u}} {a b : ℝ}

private theorem ClosedSlab.scalar_hasDerivWithinAt_Ici_of_continuous_evolution
    (G : P.ClosedSlab a b)
    (hJ : ContinuousOn (fun p : ℝ × P.Carrier =>
      laplacianAt (flowG G.flow) p.1 (G.flow.scalar p.1) p.2 +
        2 * normSq0S (G.flow.base.metric p.1) p.2 2 (G.flow.ricci p.1 p.2))
      (Icc a b ×ˢ univ)) {t : ℝ} (ht : t ∈ Ico a b) (x : P.Carrier) :
    HasDerivWithinAt (fun r => G.flow.scalar r x)
      (laplacianAt (flowG G.flow) t (G.flow.scalar t) x +
        2 * normSq0S (G.flow.base.metric t) x 2 (G.flow.ricci t x)) (Ici t) t := by
  have hf : ContinuousOn (fun r => G.flow.scalar r x) (Icc a b) := by
    have hc : ContinuousOn (fun p : ℝ × P.Carrier => G.flow.scalar p.1 p.2)
        (Icc a b ×ˢ (univ : Set P.Carrier)) := G.equation.scalarCont
    exact hc.comp (f := fun r : ℝ => (r,x))
      (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨hr,mem_univ x⟩)
  have hj : ContinuousOn (fun r => laplacianAt (flowG G.flow) r (G.flow.scalar r) x +
      2 * normSq0S (G.flow.base.metric r) x 2 (G.flow.ricci r x)) (Icc a b) :=
    hJ.comp (f := fun r : ℝ => (r,x)) (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨hr,mem_univ x⟩)
  have hd (r : ℝ) (hr : r ∈ Ioo a b) : HasDerivAt (fun v => G.flow.scalar v x)
      (laplacianAt (flowG G.flow) r (G.flow.scalar r) x +
        2 * normSq0S (G.flow.base.metric r) x 2 (G.flow.ricci r x)) r := by
    exact (scalarEvolution_of_isSolution G.flow G.equation (flowG G.flow)
      (fun _ => rfl) (fun _ => rfl) ⟨r,hr⟩ x).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  exact (DifferentialGeometry.Analysis.Calculus.SmoothExtension.hasDerivWithinAt_Icc_of_hasDerivAt_Ioo
    hf hj hd ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

private theorem ClosedSlab.continuousOn_scalar_derivWithin_Ici_of_continuous_evolution
    (G : P.ClosedSlab a b)
    (hJ : ContinuousOn (fun p : ℝ × P.Carrier =>
      laplacianAt (flowG G.flow) p.1 (G.flow.scalar p.1) p.2 +
        2 * normSq0S (G.flow.base.metric p.1) p.2 2 (G.flow.ricci p.1 p.2))
      (Icc a b ×ˢ univ)) {c : ℝ} (hc : c < b) :
    ContinuousOn (fun p : ℝ × P.Carrier =>
      derivWithin (fun t => G.flow.scalar t p.2) (Ici p.1) p.1) (Icc a c ×ˢ univ) := by
  apply (hJ.mono (prod_mono (Icc_subset_Icc le_rfl hc.le) Subset.rfl)).congr
  intro p hp
  exact (G.scalar_hasDerivWithinAt_Ici_of_continuous_evolution hJ
    ⟨hp.1.1,hp.1.2.trans_lt hc⟩ p.2).derivWithin (uniqueDiffWithinAt_Ici p.1)

theorem ClosedSlab.scalar_hasDerivWithinAt_Ici
    (G : P.ClosedSlab a b) {t : ℝ} (ht : t ∈ Ico a b) (x : P.Carrier) :
    HasDerivWithinAt (fun r => G.flow.scalar r x)
      (laplacianAt (flowG G.flow) t (G.flow.scalar t) x +
        2 * normSq0S (G.flow.base.metric t) x 2 (G.flow.ricci t x)) (Ici t) t :=
  G.scalar_hasDerivWithinAt_Ici_of_continuous_evolution G.scalar_evolution_rhs_continuousOn ht x

theorem ClosedSlab.scalar_derivWithin_Ici_eq
    (G : P.ClosedSlab a b) {t : ℝ} (ht : t ∈ Ico a b) (x : P.Carrier) :
    derivWithin (fun r => G.flow.scalar r x) (Ici t) t =
      laplacianAt (flowG G.flow) t (G.flow.scalar t) x +
        2 * normSq0S (G.flow.base.metric t) x 2 (G.flow.ricci t x) :=
  (G.scalar_hasDerivWithinAt_Ici ht x).derivWithin (uniqueDiffWithinAt_Ici t)

theorem ClosedSlab.scalar_derivWithin_Ici_continuousOn
    (G : P.ClosedSlab a b) {c : ℝ} (hc : c < b) :
    ContinuousOn (fun p : ℝ × P.Carrier =>
      derivWithin (fun t => G.flow.scalar t p.2) (Ici p.1) p.1) (Icc a c ×ˢ univ) :=
  G.continuousOn_scalar_derivWithin_Ici_of_continuous_evolution G.scalar_evolution_rhs_continuousOn hc

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab

universe u
variable {P : OrientedThreeStage.{u}} {a b : ℝ}

theorem eventually_birth_scalar_derivative_bounds
    (G : P.ClosedSlab a b) (x : P.Carrier) {C : ℝ}
    (hQ : 0 < G.flow.scalar a x)
    (hgrad : (G.flow.base.metric a).inner x
      (gradientFun (G.flow.base.metric a) (G.flow.scalar a) x)
      (gradientFun (G.flow.base.metric a) (G.flow.scalar a) x) < C ^ 2 * G.flow.scalar a x ^ 3)
    (hJ : |laplacianAt (flowG G.flow) a (G.flow.scalar a) x +
        2 * normSq0S (G.flow.base.metric a) x 2 (G.flow.ricci a x)| < C * G.flow.scalar a x ^ 2) :
    ∃ (c : ℝ) (hac : a < c), c < b ∧
      ∀ᶠ p : Icc a c × P.Carrier in 𝓝 (⟨a,le_rfl,hac.le⟩,x),
      0 < G.flow.scalar p.1.val p.2 ∧
      (G.flow.base.metric p.1.val).inner p.2
        (gradientFun (G.flow.base.metric p.1.val) (G.flow.scalar p.1.val) p.2)
        (gradientFun (G.flow.base.metric p.1.val) (G.flow.scalar p.1.val) p.2) <
          C ^ 2 * G.flow.scalar p.1.val p.2 ^ 3 ∧
      |derivWithin (fun t => G.flow.scalar t p.2) (Ici p.1.val) p.1.val| <
        C * G.flow.scalar p.1.val p.2 ^ 2 := by
  let c := (a+b)/2
  have hac : a < c := by dsimp only [c]; linarith [G.lt]
  have hcb : c < b := by dsimp only [c]; linarith [G.lt]
  refine ⟨c,hac,hcb,?_⟩
  have hmap : Continuous (fun p : Icc a c × P.Carrier => (p.1.val,p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hmaps : MapsTo (fun p : Icc a c × P.Carrier => (p.1.val,p.2)) univ (Icc a b ×ˢ univ) :=
    fun p _ => ⟨⟨p.1.property.1,p.1.property.2.trans hcb.le⟩,mem_univ _⟩
  have hscont : ContinuousOn (fun p : ℝ × P.Carrier => G.flow.scalar p.1 p.2)
      (Icc a b ×ˢ (univ : Set P.Carrier)) := G.equation.scalarCont
  have hsc : Continuous (fun p : Icc a c × P.Carrier => G.flow.scalar p.1.val p.2) :=
    hscont.comp_continuous (f := fun p : Icc a c × P.Carrier => (p.1.val,p.2)) hmap
      (fun p => hmaps (mem_univ p))
  have hgr : Continuous (fun p : Icc a c × P.Carrier =>
      (G.flow.base.metric p.1.val).inner p.2
        (gradientFun (G.flow.base.metric p.1.val) (G.flow.scalar p.1.val) p.2)
        (gradientFun (G.flow.base.metric p.1.val) (G.flow.scalar p.1.val) p.2)) :=
    G.scalar_gradient_norm_sq_continuousOn.comp_continuous
      (f := fun p : Icc a c × P.Carrier => (p.1.val,p.2)) hmap (fun p => hmaps (mem_univ p))
  have hder : Continuous (fun p : Icc a c × P.Carrier =>
      derivWithin (fun t => G.flow.scalar t p.2) (Ici p.1.val) p.1.val) :=
    (G.scalar_derivWithin_Ici_continuousOn hcb).comp_continuous
      (f := fun p : Icc a c × P.Carrier => (p.1.val,p.2)) hmap
      (fun p => ⟨p.1.property,mem_univ _⟩)
  have hd₀ : |derivWithin (fun t => G.flow.scalar t x) (Ici a) a| < C * G.flow.scalar a x ^ 2 := by
    rw [G.scalar_derivWithin_Ici_eq ⟨le_rfl,G.lt⟩ x]
    exact hJ
  filter_upwards [hsc.continuousAt.eventually (Ioi_mem_nhds hQ),
    hgr.continuousAt.eventually_lt (continuousAt_const.mul (hsc.continuousAt.pow 3)) hgrad,
    hder.continuousAt.abs.eventually_lt (continuousAt_const.mul (hsc.continuousAt.pow 2)) hd₀]
    with p hp hg hd
  exact ⟨hp,hg,hd⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab
