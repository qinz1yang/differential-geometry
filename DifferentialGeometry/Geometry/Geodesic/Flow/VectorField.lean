import DifferentialGeometry.Bundle.TangentChart
import DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Chart.Transition
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]

omit [NeZero (Module.finrank ℝ E)] in
theorem geodesicVectorFieldChart_fst
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    (geodesicVectorFieldChart (I := I) g α p : E × E).1 = (p.snd : E) := by
  classical
  have hp_dom : p ∈ geodesicChartDomain (I := I) α := hp
  have htriv := trivializationAt_apply_geodesicVectorFieldChart
    (I := I) g α (p := p) hp_dom
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M) with he_def
  have hp_base : p ∈ e.baseSet := by
    rw [he_def, ← geodesicChartDomain_eq_trivBaseSet (I := I) α]
    exact hp_dom
  have hcoe :=
    e.coe_linearMapAt_of_mem (R := ℝ) hp_base
  have hlin_at_gvf :
      (e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p) =
        geodesicVectorFieldChartFiber (I := I) g α p := by
    have h2 := congrArg Prod.snd htriv
    change (e.linearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p) = _
    have hh := congrFun hcoe (geodesicVectorFieldChart (I := I) g α p)
    rw [hh]; exact h2
  have hfst_eq :
      ((e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p)).1 =
        (geodesicVectorFieldChartFiber (I := I) g α p).1 :=
    congrArg Prod.fst hlin_at_gvf
  have hLHS :
      ((e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p)).1 =
        tangentCoordChange I p.proj α p.proj
          ((geodesicVectorFieldChart (I := I) g α p : E × E).1) :=
    fst_continuousLinearMapAt_secondaryTriv (I := I) (α := α) (p := p) hp
      (geodesicVectorFieldChart (I := I) g α p)
  have hRHS :
      (geodesicVectorFieldChartFiber (I := I) g α p).1 =
        tangentCoordChange I p.proj α p.proj (p.snd : E) := by
    change chartFiberCoord (I := I) α p = _
    exact chartFiberCoord_eq_tangentCoordChange (I := I) (α := α) (p := p) hp
  have hcc_eq :
      tangentCoordChange I p.proj α p.proj
          ((geodesicVectorFieldChart (I := I) g α p : E × E).1) =
        tangentCoordChange I p.proj α p.proj (p.snd : E) := by
    rw [← hLHS, hfst_eq, hRHS]
  have hp_E_source : p.proj ∈ (extChartAt I p.proj).source :=
    mem_extChartAt_source (I := I) p.proj
  have hp_E_source_α : p.proj ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hp
  have hself :
      tangentCoordChange I p.proj p.proj p.proj
          ((geodesicVectorFieldChart (I := I) g α p : E × E).1) =
        (geodesicVectorFieldChart (I := I) g α p : E × E).1 :=
    tangentCoordChange_self (I := I) (x := p.proj) (z := p.proj)
      (v := (geodesicVectorFieldChart (I := I) g α p : E × E).1) hp_E_source
  have hself_snd :
      tangentCoordChange I p.proj p.proj p.proj (p.snd : E) = p.snd :=
    tangentCoordChange_self (I := I) (x := p.proj) (z := p.proj)
      (v := p.snd) hp_E_source
  have h_comp1 :
      tangentCoordChange I α p.proj p.proj
          (tangentCoordChange I p.proj α p.proj
            ((geodesicVectorFieldChart (I := I) g α p : E × E).1)) =
        tangentCoordChange I p.proj p.proj p.proj
          ((geodesicVectorFieldChart (I := I) g α p : E × E).1) :=
    tangentCoordChange_comp (I := I) (w := p.proj) (x := α) (y := p.proj)
      (z := p.proj)
      (v := (geodesicVectorFieldChart (I := I) g α p : E × E).1)
      ⟨⟨hp_E_source, hp_E_source_α⟩, hp_E_source⟩
  have h_comp2 :
      tangentCoordChange I α p.proj p.proj
          (tangentCoordChange I p.proj α p.proj (p.snd : E)) =
        tangentCoordChange I p.proj p.proj p.proj (p.snd : E) :=
    tangentCoordChange_comp (I := I) (w := p.proj) (x := α) (y := p.proj)
      (z := p.proj) (v := p.snd) ⟨⟨hp_E_source, hp_E_source_α⟩, hp_E_source⟩
  have : (geodesicVectorFieldChart (I := I) g α p : E × E).1 = p.snd := by
    rw [← hself]
    rw [← h_comp1]
    rw [hcc_eq]
    rw [h_comp2]
    exact hself_snd
  exact this

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private lemma tangentCoordChange_eq_chartTransitionAt [I.Boundaryless]
    (x y : M) (z : M) :
    tangentCoordChange I x y z =
      chartTransitionAt (I := I) x y (extChartAt I x z) := by
  rw [tangentCoordChange_def, chartTransitionAt_def, chartTransitionMap_def]
  have h : (Set.range I : Set E) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ (I := I)
  rw [h, fderivWithin_univ]

private def applyJacobian (α : M) (p : TangentBundle I M) (z : E × E) : E :=
  chartTransitionAt (I := I) p.proj α z.1 z.2

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private lemma secondaryTrivSndForm_eventuallyEq_applyJacobian [I.Boundaryless]
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    secondaryTrivFiberComponentMap (I := I) α p =ᶠ[𝓝 ((extChartAt I.tangent p) p)]
      applyJacobian (I := I) α p := by
  classical
  have hbp1 : ((extChartAt I.tangent p) p).1 = extChartAt I p.proj p.proj :=
    extChartAt_tangent_apply_fst (I := I) (q := p) (p := p)
  set U : Set (E × E) :=
    {z : E × E | z.1 ∈ (extChartAt I p.proj).target ∧
      (extChartAt I p.proj).symm z.1 ∈ (chartAt H α).source} with hU_def
  have hUopen : IsOpen U := by
    have h1 : IsOpen ((extChartAt I p.proj).target) :=
      isOpen_extChartAt_target (I := I) p.proj
    have hcont : ContinuousOn (extChartAt I p.proj).symm (extChartAt I p.proj).target :=
      continuousOn_extChartAt_symm (I := I) p.proj
    have hset : U = (Prod.fst ⁻¹' (extChartAt I p.proj).target) ∩
        (Prod.fst ⁻¹' ((extChartAt I p.proj).target ∩
          (extChartAt I p.proj).symm ⁻¹' (chartAt H α).source)) := by
      ext z
      simp only [hU_def, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h1, h2⟩
      · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
    rw [hset]
    refine (h1.preimage continuous_fst).inter ((IsOpen.preimage continuous_fst) ?_)
    exact hcont.isOpen_inter_preimage h1 (chartAt H α).open_source
  have hbp_memU : ((extChartAt I.tangent p) p) ∈ U := by
    rw [hU_def, Set.mem_ofPred_eq, hbp1]
    refine ⟨(extChartAt I p.proj).map_source (mem_extChartAt_source (I := I) p.proj), ?_⟩
    rw [(extChartAt I p.proj).left_inv (mem_extChartAt_source (I := I) p.proj)]
    exact hp
  refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hbp_memU) ?_
  intro z hz
  obtain ⟨hz_target, hz_source⟩ := hz
  unfold secondaryTrivFiberComponentMap applyJacobian
  rw [tangentCoordChange_eq_chartTransitionAt (I := I) p.proj α ((extChartAt I p.proj).symm z.1)]
  congr 2
  exact (extChartAt I p.proj).right_inv hz_target

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private lemma differentiableAt_chartTransitionAt [I.Boundaryless]
    (α β : M) {x : E} (hx : x ∈ chartTransitionSource (I := I) α β) :
    DifferentiableAt ℝ (fun z => chartTransitionAt (I := I) α β z) x := by
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have hsmooth : ContDiffOn ℝ ∞ (fun z => (chartTransitionAt (I := I) α β z : E →L[ℝ] E))
      (chartTransitionSource (I := I) α β) :=
    chartTransitionAt_smooth (I := I) α β
  exact (hsmooth.contDiffAt (h_open.mem_nhds hx)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
omit [Module.Finite ℝ E] in
private lemma fderiv_applyJacobian_apply [I.Boundaryless]
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (w : E × E) :
    fderiv ℝ (applyJacobian (I := I) α p) ((extChartAt I.tangent p) p) w =
      chartTransitionAt (I := I) p.proj α ((extChartAt I.tangent p) p).1 w.2 +
        (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z)
          ((extChartAt I.tangent p) p).1 w.1) (((extChartAt I.tangent p) p).2) := by
  classical
  set bp := (extChartAt I.tangent p) p with hbp
  have hbp1 : bp.1 = extChartAt I p.proj p.proj := by
    rw [hbp]
    exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := p)
  have hx_source : bp.1 ∈ chartTransitionSource (I := I) p.proj α := by
    rw [hbp1]
    exact extChartAt_mem_chartTransitionSource (I := I) p.proj α
      (mem_chart_source H p.proj) hp
  set c : E × E → (E →L[ℝ] E) := fun z => chartTransitionAt (I := I) p.proj α z.1 with hc
  set u : E × E → E := fun z => z.2 with hu
  have hcA : DifferentiableAt ℝ (fun z => chartTransitionAt (I := I) p.proj α z) bp.1 :=
    differentiableAt_chartTransitionAt (I := I) p.proj α hx_source
  have hc_diff : DifferentiableAt ℝ c bp :=
    hcA.comp bp (differentiableAt_fst)
  have hu_diff : DifferentiableAt ℝ u bp := differentiableAt_snd
  have hfd : fderiv ℝ (fun z => (c z) (u z)) bp =
      (c bp).comp (fderiv ℝ u bp) + (fderiv ℝ c bp).flip (u bp) :=
    fderiv_clm_apply hc_diff hu_diff
  have happly_eq : applyJacobian (I := I) α p = fun z => (c z) (u z) := by
    funext z; rfl
  rw [happly_eq, hfd]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  have hu_fderiv : fderiv ℝ u bp = ContinuousLinearMap.snd ℝ E E := fderiv_snd
  rw [hu_fderiv]
  have hc_fderiv : fderiv ℝ c bp w =
      (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z) bp.1) (w.1) := by
    have hceq : c = (fun x => chartTransitionAt (I := I) p.proj α x) ∘ Prod.fst := by
      funext z; rfl
    rw [hceq]
    rw [fderiv_comp bp hcA differentiableAt_fst]
    simp only [ContinuousLinearMap.comp_apply, fderiv_fst, ContinuousLinearMap.coe_fst']
  rw [hc_fderiv]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem geodesicVectorFieldChart_eq_geodesicVectorField
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChart (I := I) g α p = geodesicVectorField (I := I) g p := by
  classical
  set x₀ := extChartAt I p.proj p.proj with hx₀
  set bp := (extChartAt I.tangent p) p with hbp
  set pModel : E := tangentSpaceModelContinuousLinearEquiv (I := I) p.proj p.snd with hpModel
  have hbp1 : bp.1 = x₀ := by
    rw [hbp, hx₀]
    exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := p)
  have hbp2 : bp.2 = pModel := by
    rw [hbp]
    rw [extChartAt_tangent_apply_snd_tangentCoordChange (I := I) (q := p) (p := p)
      (mem_chart_source H p.proj)]
    rw [hpModel, tangentSpaceModelContinuousLinearEquiv_apply]
    exact tangentCoordChange_self (I := I) (x := p.proj) (z := p.proj) (v := p.snd)
      (mem_extChartAt_source (I := I) p.proj)
  have hx_source : x₀ ∈ chartTransitionSource (I := I) p.proj α :=
    extChartAt_mem_chartTransitionSource (I := I) p.proj α
      (mem_chart_source H p.proj) hp
  have hfst : (geodesicVectorFieldChart (I := I) g α p : E × E).1 =
      (geodesicVectorField (I := I) g p : E × E).1 := by
    rw [geodesicVectorFieldChart_fst (I := I) g α hp]
    rfl
  have hsnd : (geodesicVectorFieldChart (I := I) g α p : E × E).2 =
      (geodesicVectorField (I := I) g p : E × E).2 := by
    set X := (geodesicVectorFieldChart (I := I) g α p : E × E).2 with hX
    have hgvf1 : (geodesicVectorFieldChart (I := I) g α p : E × E).1 = pModel := by
      rw [hpModel, tangentSpaceModelContinuousLinearEquiv_apply]
      exact geodesicVectorFieldChart_fst (I := I) g α hp
    have hp_dom : p ∈ geodesicChartDomain (I := I) α := hp
    have htriv := trivializationAt_apply_geodesicVectorFieldChart
      (I := I) g α (p := p) hp_dom
    set e := trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M) with he_def
    have hp_base : p ∈ e.baseSet := by
      rw [he_def, ← geodesicChartDomain_eq_trivBaseSet (I := I) α]; exact hp_dom
    have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) hp_base
    have hlin_at_gvf :
        (e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p) =
          geodesicVectorFieldChartFiber (I := I) g α p := by
      have h2 := congrArg Prod.snd htriv
      change (e.linearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p) = _
      have hh := congrFun hcoe (geodesicVectorFieldChart (I := I) g α p)
      rw [hh]; exact h2
    have hsnd_clm :
        ((e.continuousLinearMapAt ℝ p) (geodesicVectorFieldChart (I := I) g α p)).2 =
          (fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent) bp)
            (geodesicVectorFieldChart (I := I) g α p) :=
      snd_continuousLinearMapAt_secondaryTriv (I := I) (α := α) (p := p) hp
        (geodesicVectorFieldChart (I := I) g α p)
    have hkey0 : (geodesicVectorFieldChartFiber (I := I) g α p).2 =
        (fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent) bp)
          (geodesicVectorFieldChart (I := I) g α p) := by
      rw [← hsnd_clm, hlin_at_gvf]
    have hrangeT : (range (I.tangent) : Set (E × E)) = Set.univ :=
      ModelWithCorners.Boundaryless.range_eq_univ (I := I.tangent)
    have hfderiv_eq :
        fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent) bp =
          fderiv ℝ (applyJacobian (I := I) α p) bp := by
      rw [hrangeT, fderivWithin_univ]
      exact Filter.EventuallyEq.fderiv_eq
        (secondaryTrivSndForm_eventuallyEq_applyJacobian (I := I) α hp)
    rw [hfderiv_eq] at hkey0
    have hfderiv_apply :
        fderiv ℝ (applyJacobian (I := I) α p) bp (geodesicVectorFieldChart (I := I) g α p) =
          chartTransitionAt (I := I) p.proj α x₀ X +
            (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z) x₀ pModel)
              pModel := by
      have := fderiv_applyJacobian_apply (I := I) α hp (geodesicVectorFieldChart (I := I) g α p)
      rw [this, hbp1, hbp2, hgvf1]
    rw [hfderiv_apply] at hkey0
    set Dterm : E := (fderiv ℝ (fun z => chartTransitionAt (I := I) p.proj α z) x₀
      pModel) pModel with hDterm
    set v := chartFiberCoord (I := I) α p with hv
    have hfiber2 : (geodesicVectorFieldChartFiber (I := I) g α p).2 =
        - chartChristoffelContraction (I := I) g α v v (extChartAt I α p.proj) := rfl
    rw [hfiber2] at hkey0
    have htransform :
        chartChristoffelContraction (I := I) g p.proj pModel pModel x₀ =
          chartTransitionAt (I := I) α p.proj
              (chartTransitionMap (I := I) p.proj α x₀)
              (chartChristoffelContraction (I := I) g α
                (chartTransitionAt (I := I) p.proj α x₀ pModel)
                (chartTransitionAt (I := I) p.proj α x₀ pModel)
                (chartTransitionMap (I := I) p.proj α x₀))
            + chartTransitionSecondDerivCorrection (I := I) p.proj α pModel pModel x₀ := by
      have := chartChristoffelContraction_transform (I := I) g p.proj α
        (p := p.proj) (mem_chart_source H p.proj) hp pModel pModel
      rw [hx₀]; exact this
    have hTx₀ : chartTransitionMap (I := I) p.proj α x₀ = extChartAt I α p.proj := by
      rw [hx₀]
      exact chartTransitionMap_apply_extChartAt (I := I) p.proj α (mem_chart_source H p.proj)
    have hJsnd : chartTransitionAt (I := I) p.proj α x₀ pModel = v := by
      rw [hv, hx₀, ← tangentCoordChange_eq_chartTransitionAt (I := I) p.proj α p.proj]
      rw [hpModel, tangentSpaceModelContinuousLinearEquiv_apply]
      exact (chartFiberCoord_eq_tangentCoordChange (I := I) (α := α) (p := p) hp).symm
    rw [hTx₀, hJsnd] at htransform
    have hcorr :
        chartTransitionAt (I := I) α p.proj (extChartAt I α p.proj) Dterm =
          chartTransitionSecondDerivCorrection (I := I) p.proj α pModel pModel x₀ := by
      refine (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).ext_elem (fun k => ?_)
      change chartCoord (E := E) k
          (chartTransitionAt (I := I) α p.proj (extChartAt I α p.proj) Dterm) =
        chartCoord (E := E) k
          (chartTransitionSecondDerivCorrection (I := I) p.proj α pModel pModel x₀)
      rw [chartCoord_chartTransitionAt (I := I) α p.proj (extChartAt I α p.proj) Dterm k]
      rw [chartTransitionSecondDerivCorrection_def]
      rw [show chartCoord (E := E) k
          (∑ k' : Fin (Module.finrank ℝ E),
            (∑ c : Fin (Module.finrank ℝ E),
              chartTransitionJacobianEntry (I := I) α p.proj
                (chartTransitionMap (I := I) p.proj α x₀) k' c *
                (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
                  DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
                    (fun z => chartTransitionJacobianEntry (I := I) p.proj α z c j) x₀ *
                    chartCoord (E := E) i pModel * chartCoord (E := E) j pModel)) •
              DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k') =
          ∑ c : Fin (Module.finrank ℝ E),
              chartTransitionJacobianEntry (I := I) α p.proj
                (chartTransitionMap (I := I) p.proj α x₀) k c *
                (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
                  DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
                    (fun z => chartTransitionJacobianEntry (I := I) p.proj α z c j) x₀ *
                    chartCoord (E := E) i pModel * chartCoord (E := E) j pModel) from ?_]
      · rw [hTx₀]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [hDterm, chartCoord_fderiv_chartTransitionAt
          (I := I) p.proj α hx_source c pModel pModel]
      · rw [chartCoord_def, map_sum, Finsupp.finsetSum_apply]
        rw [Finset.sum_eq_single k]
        · rw [map_smul, Finsupp.smul_apply, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr_self k,
            Finsupp.single_eq_same, smul_eq_mul, mul_one]
        · intro k' _ hk'
          rw [map_smul, Finsupp.smul_apply, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr_self k']
          rw [Finsupp.single_eq_of_ne (Ne.symm hk'), smul_zero]
        · intro hk; exact absurd (Finset.mem_univ k) hk
    have hinv : chartTransitionAt (I := I) α p.proj
        (chartTransitionMap (I := I) p.proj α x₀)
        (chartTransitionAt (I := I) p.proj α x₀ X) = X := by
      have hcomp := chartTransitionAt_comp_chartTransitionAt (I := I) p.proj α hx_source
      have := congrArg (fun L : E →L[ℝ] E => L X) hcomp
      simpa using this
    set RJ : E →L[ℝ] E := chartTransitionAt (I := I) α p.proj
      (chartTransitionMap (I := I) p.proj α x₀) with hRJ
    have happ := congrArg (fun y => RJ y) hkey0
    rw [map_add] at happ
    have hRJ_X : RJ (chartTransitionAt (I := I) p.proj α x₀ X) = X := by
      rw [hRJ]; exact hinv
    rw [hRJ_X] at happ
    have hRJ_D : RJ Dterm =
        chartTransitionSecondDerivCorrection (I := I) p.proj α pModel pModel x₀ := by
      rw [hRJ, hTx₀]; exact hcorr
    rw [hRJ_D] at happ
    rw [map_neg] at happ
    have hRJ_Gamma :
        RJ (chartChristoffelContraction (I := I) g α v v (extChartAt I α p.proj)) =
          chartChristoffelContraction (I := I) g p.proj pModel pModel x₀ -
            chartTransitionSecondDerivCorrection (I := I) p.proj α pModel pModel x₀ := by
      rw [hRJ, hTx₀]
      rw [eq_sub_iff_add_eq]
      exact htransform.symm
    rw [hRJ_Gamma] at happ
    have hXval : X = - chartChristoffelContraction (I := I) g p.proj pModel pModel x₀ := by
      rw [neg_sub, sub_eq_neg_add] at happ
      exact (add_right_cancel happ).symm
    rw [hXval, geodesicVectorField_snd]
    rw [hpModel, tangentSpaceModelContinuousLinearEquiv_apply, hx₀]
  apply Prod.ext hfst hsnd

omit [NeZero (Module.finrank ℝ E)] in
theorem contMDiff_geodesicVectorField
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) :
    ContMDiff I.tangent I.tangent.tangent ∞
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorField (I := I) g p⟩ :
          TangentBundle I.tangent (TangentBundle I M))) := by
  intro p
  let α : M := p.proj
  have hp : p.proj ∈ (chartAt H α).source := by
    simp [α]
  have hsmooth := geodesicVectorFieldChart_contMDiffAt (I := I) g α hp
  refine hsmooth.congr_of_eventuallyEq ?_
  have hnhds : geodesicChartDomain (I := I) α ∈ nhds p :=
    (geodesicChartDomain_isOpen (I := I) (M := M) α).mem_nhds hp
  filter_upwards [hnhds] with q hq
  refine TotalSpace.ext rfl ?_
  exact heq_of_eq ((geodesicVectorFieldChart_eq_geodesicVectorField
    (I := I) g α hq).symm)

omit [NeZero (Module.finrank ℝ E)] in
theorem geodesicVectorFieldChart_eq_of_proj_mem
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α α' : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hα' : p.proj ∈ (chartAt H α').source) :
    geodesicVectorFieldChart (I := I) g α p =
      geodesicVectorFieldChart (I := I) g α' p := by
  rw [geodesicVectorFieldChart_eq_geodesicVectorField (I := I) g α hα,
    geodesicVectorFieldChart_eq_geodesicVectorField (I := I) g α' hα']

end DifferentialGeometry.Geometry.Riemannian.Geodesic

end
