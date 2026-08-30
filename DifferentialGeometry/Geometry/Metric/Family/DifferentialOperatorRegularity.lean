import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import DifferentialGeometry.Geometry.Connection.ChartBridge.Laplacian
import DifferentialGeometry.Geometry.Operator.MetricFamily
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Operator.HessianTraceChartGramRegularity

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
private theorem partialDeriv_contDiffOn
    {f : E → Real} {V : Set E} (hV : IsOpen V)
    (hf : ContDiffOn Real ∞ f V) (i : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞ (partialDeriv (E := E) i f) V := by
  have hfd : ContDiffOn Real ∞ (fderiv Real f) V :=
    hf.fderiv_of_isOpen hV (by rw [ENat.coe_top_add_one])
  exact hfd.clm_apply contDiffOn_const

omit [CompleteSpace E] in
private theorem scalarPartialOnE_continuousOn
    (α : M) {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ)
    (J : Set Real) (i : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × E =>
        partialDeriv (E := E) i (scalarOnE (I := I) α ρ) p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  have hρE : ContDiffOn Real ∞ (scalarOnE (I := I) α ρ)
      (interior (extChartAt I α).target) :=
    (scalarOnE_contDiffOn (I := I) α hρ).mono interior_subset
  have hpartial := partialDeriv_contDiffOn isOpen_interior hρE i
  exact hpartial.continuousOn.comp continuousOn_snd fun p hp => hp.2

omit [CompleteSpace E] in
private theorem scalarSecondPartialOnE_continuousOn
    (α : M) {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ)
    (J : Set Real) (i j : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × E =>
        partialDeriv (E := E) i
          (partialDeriv (E := E) j (scalarOnE (I := I) α ρ)) p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  have hρE : ContDiffOn Real ∞ (scalarOnE (I := I) α ρ)
      (interior (extChartAt I α).target) :=
    (scalarOnE_contDiffOn (I := I) α hρ).mono interior_subset
  have hfirst := partialDeriv_contDiffOn isOpen_interior hρE j
  have hsecond := partialDeriv_contDiffOn isOpen_interior hfirst i
  exact hsecond.continuousOn.comp continuousOn_snd fun p hp => hp.2

omit [CompleteSpace E] in
private theorem gradientCoeffOnE_continuousOn
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    (α : M) {ρ : M → Real}
    (hρ : ContMDiff I (modelWithCornersSelf Real Real) ∞ ρ)
    (i : Fin (Module.finrank Real E)) :
    ContinuousOn
      (fun p : Real × E =>
        ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) (g_fam p.1) α i j p.2 *
            partialDeriv (E := E) j (scalarOnE (I := I) α ρ) p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  refine continuousOn_finsetSum _ fun j _ => ?_
  exact (chartInvGramOnE_continuousOn (I := I) hG hJreg α i j).mul
    (scalarPartialOnE_continuousOn (I := I) α hρ J j)

omit [CompleteSpace E] in
theorem gradient_continuousOn [I.Boundaryless]
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    {ρ : M → Real}
    (hρ : ContMDiff I (modelWithCornersSelf Real Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        (TotalSpace.mk' E p.2
          (gradFun (I := I) (g_fam p.1) ρ p.2) : TangentBundle I M))
      (J ×ˢ (Set.univ : Set M)) := by
  classical
  refine continuousOn_of_locally_continuousOn ?_
  intro p hp
  let α := p.2
  let e := trivializationAt E (TangentSpace I : M → Type _) α
  let U : Set (Real × M) := Set.univ ×ˢ e.baseSet
  have hpU : p ∈ U := ⟨Set.mem_univ _, by simp [e, α]⟩
  refine ⟨U, isOpen_univ.prod e.open_baseSet, hpU, ?_⟩
  let S : Set (Real × M) := J ×ˢ e.baseSet
  let ψ : Real × M → Real × E := fun q => (q.1, extChartAt I α q.2)
  have hψ : ContinuousOn ψ S :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) α).comp continuous_snd.continuousOn
        fun q hq => by
          rw [extChartAt_source_eq_chartAt_source (I := I)]
          simpa [e] using hq.2)
  have hmapsψ : MapsTo ψ S
      (J ×ˢ interior (extChartAt I α).target) := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    apply extChartAt_target_subset_interior_of_boundaryless (I := I) α
    apply (extChartAt I α).map_source
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    simpa [e] using hq.2
  let coeff : Fin (Module.finrank Real E) → Real × M → Real := fun i q =>
    ∑ j : Fin (Module.finrank Real E),
      chartInvGramOnE (I := I) (g_fam q.1) α i j (extChartAt I α q.2) *
        partialDeriv (E := E) j (scalarOnE (I := I) α ρ) (extChartAt I α q.2)
  have hcoeff : ∀ i, ContinuousOn (coeff i) S := by
    intro i
    have h := (gradientCoeffOnE_continuousOn (I := I) hG hJreg α hρ i).comp hψ hmapsψ
    refine h.congr ?_
    intro q hq
    rfl
  let coord : Real × M → E := fun q =>
    ∑ i : Fin (Module.finrank Real E), coeff i q • chartModelBasis E i
  have hcoord : ContinuousOn coord S := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact (hcoeff i).smul continuousOn_const
  let toPair : Real × M → M × E := fun q => (q.2, coord q)
  have hpair : ContinuousOn toPair S :=
    continuous_snd.continuousOn.prodMk hcoord
  have hmapsPair : MapsTo toPair S (e.baseSet ×ˢ (Set.univ : Set E)) := by
    intro q hq
    exact ⟨hq.2, Set.mem_univ _⟩
  have htotal := e.continuousOn_symm.comp hpair hmapsPair
  refine (htotal.congr ?_).mono ?_
  · intro q hq
    have hbase : q.2 ∈ e.baseSet := hq.2
    have hsource : q.2 ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      simpa [e] using hbase
    have hcoord_eq : coord q =
        ∑ i : Fin (Module.finrank Real E),
          gradChartCoeff (I := I) (g_fam q.1) α ρ i q.2 • chartModelBasis E i := by
      simp only [coord, coeff, gradChartCoeff_def, chartInvGramOnE_def]
      rw [(extChartAt I α).left_inv hsource]
    change (TotalSpace.mk' E q.2
      (gradFun (I := I) (g_fam q.1) ρ q.2) : TangentBundle I M) =
        TotalSpace.mk' E q.2 (e.symm q.2 (coord q))
    congr 1
    rw [← e.symmL_apply (R := Real) hbase (coord q)]
    rw [hcoord_eq, map_sum]
    simp only [map_smul]
    rw [← gradChartLocal_eq_gradFun (I := I) (g_fam q.1) α
      (hρ.mdifferentiable (by simp) q.2) hbase
      (extChartAt_target_subset_interior_of_boundaryless (I := I) α
        ((extChartAt I α).map_source hsource))]
    symm
    unfold gradChartLocal
    apply Finset.sum_congr rfl
    intro i _
    rw [chartBasisVecFiber, Trivialization.symmL_apply _ hbase]
  · intro q hq
    exact ⟨hq.1.1, hq.2.2⟩

omit [CompleteSpace E] in
private theorem gradientNormSqOnE_continuousOn
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    (α : M) {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × E =>
        ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) (g_fam p.1) α i j p.2 *
            partialDeriv (E := E) j (scalarOnE (I := I) α ρ) p.2 *
            partialDeriv (E := E) i (scalarOnE (I := I) α ρ) p.2)
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  refine continuousOn_finsetSum _ fun i _ =>
    continuousOn_finsetSum _ fun j _ => ?_
  exact ((chartInvGramOnE_continuousOn (I := I) hG hJreg α i j).mul
    (scalarPartialOnE_continuousOn (I := I) α hρ J j)).mul
    (scalarPartialOnE_continuousOn (I := I) α hρ J i)

omit [CompleteSpace E] in
private theorem leviCivitaLaplacianOnE_continuousOn
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    (α : M) {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × E =>
        ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) (g_fam p.1) α i j p.2 *
            (partialDeriv (E := E) i
                (partialDeriv (E := E) j (scalarOnE (I := I) α ρ)) p.2 -
              ∑ k : Fin (Module.finrank Real E),
                chartChristoffel (I := I) (g_fam p.1) α i j k p.2 *
                  partialDeriv (E := E) k (scalarOnE (I := I) α ρ) p.2))
      (J ×ˢ interior (extChartAt I α).target) := by
  classical
  refine continuousOn_finsetSum _ fun i _ =>
    continuousOn_finsetSum _ fun j _ => ?_
  refine (chartInvGramOnE_continuousOn (I := I) hG hJreg α i j).mul ?_
  refine (scalarSecondPartialOnE_continuousOn (I := I) α hρ J i j).sub ?_
  refine continuousOn_finsetSum _ fun k _ => ?_
  exact (chartChristoffelOnE_continuousOn (I := I) hG hJreg hJ α i j k).mul
    (scalarPartialOnE_continuousOn (I := I) α hρ J k)

omit [CompleteSpace E] in
theorem gradient_norm_sq_continuousOn [I.Boundaryless]
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJreg : J ⊆ D.regular)
    {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        (g_fam p.1).inner p.2
          (gradientFun (I := I) (g_fam p.1) ρ p.2)
          (gradientFun (I := I) (g_fam p.1) ρ p.2))
      (J ×ˢ (Set.univ : Set M)) := by
  classical
  refine continuousOn_of_locally_continuousOn ?_
  intro p hp
  let α := p.2
  let U : Set (Real × M) := Set.univ ×ˢ chartLeviCivitaGoodSet (I := I) α
  have hpU : p ∈ U := ⟨Set.mem_univ _, self_mem_chartLeviCivitaGoodSet (I := I) (α := α)⟩
  refine ⟨U, isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) α), hpU, ?_⟩
  let S : Set (Real × M) := J ×ˢ chartLeviCivitaGoodSet (I := I) α
  have hψ : ContinuousOn (fun q : Real × M => (q.1, extChartAt I α q.2)) S :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) α).comp continuous_snd.continuousOn
        fun q hq => chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq.2)
  have hmaps : MapsTo (fun q : Real × M => (q.1, extChartAt I α q.2)) S
      (J ×ˢ interior (extChartAt I α).target) :=
    fun q hq => ⟨hq.1,
      chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hq.2⟩
  have hlocal := (gradientNormSqOnE_continuousOn (I := I) hG hJreg α hρ).comp hψ hmaps
  refine (hlocal.congr ?_).mono ?_
  · intro q hq
    simp only [Function.comp_apply]
    change (g_fam q.1).inner q.2
        (gradFun (I := I) (g_fam q.1) ρ q.2)
        (gradFun (I := I) (g_fam q.1) ρ q.2) = _
    rw [grad_norm_sq_chart (I := I) (g_fam q.1) α (hρ.mdifferentiable (by simp) q.2)
      (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hq.2)]
    simp only [chartInvGramOnE_def]
    rw [(extChartAt I α).left_inv
      (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq.2)]
  · intro q hq
    exact ⟨hq.1.1, hq.2.2⟩

omit [CompleteSpace E] in
theorem leviCivitaLaplacian_continuousOn [I.Boundaryless] [T2Space M]
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJ : UniqueDiffOn Real J)
    {ρ : M → Real} (hρ : ContMDiff I 𝓘(Real, Real) ∞ ρ) :
    ContinuousOn
      (fun p : Real × M =>
        laplacian (I := I) (LeviCivita (I := I) (g_fam p.1))
          (g_fam p.1) ρ p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  classical
  refine continuousOn_of_locally_continuousOn ?_
  intro p hp
  let α := p.2
  let U : Set (Real × M) := Set.univ ×ˢ chartLeviCivitaGoodSet (I := I) α
  have hpU : p ∈ U := ⟨Set.mem_univ _, self_mem_chartLeviCivitaGoodSet (I := I) (α := α)⟩
  refine ⟨U, isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) α), hpU, ?_⟩
  let S : Set (Real × M) := J ×ˢ chartLeviCivitaGoodSet (I := I) α
  have hψ : ContinuousOn (fun q : Real × M => (q.1, extChartAt I α q.2)) S :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) α).comp continuous_snd.continuousOn
        fun q hq => chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq.2)
  have hmaps : MapsTo (fun q : Real × M => (q.1, extChartAt I α q.2)) S
      (J ×ˢ interior (extChartAt I α).target) :=
    fun q hq => ⟨hq.1,
      chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hq.2⟩
  have hlocal :=
    (leviCivitaLaplacianOnE_continuousOn (I := I) hG hJreg hJ α hρ).comp hψ hmaps
  refine (hlocal.congr ?_).mono ?_
  · intro q hq
    simp only [Function.comp_apply]
    rw [laplacian_eq_chart_hessian_trace (I := I) (g_fam q.1) α hρ
      (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hq.2)]
    simp only [chartHessianTensor_def, chartIteratedPartialDeriv_def,
      chartInvGramOnE_def]
    rw [(extChartAt I α).left_inv
      (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq.2)]
  · intro q hq
    exact ⟨hq.1.1, hq.2.2⟩

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
    (I := I) (g_fam := G.metric) hG hJreg hρ
  have hfun : (fun p : Real × M =>
      (TotalSpace.mk' E p.2 (gradientAt (I := I) G p.1 ρ p.2) : TangentBundle I M)) =
      fun p : Real × M =>
        (TotalSpace.mk' E p.2 (gradFun (I := I) (G.metric p.1) ρ p.2) : TangentBundle I M) := by
    funext p
    congr 1
  rw [hfun]
  exact h

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
      (I := I) (g_fam := G.metric) hG hJreg hρ

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
    (I := I) (g_fam := G.metric) hG hJreg hJ hρ
  refine hlevi.congr ?_
  intro p hp
  change laplacianAt (I := I) G p.1 ρ p.2 =
    laplacian (I := I) (LeviCivita (I := I) (G.metric p.1))
      (G.metric p.1) ρ p.2
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

end MetricConnectionFamily

end DifferentialGeometry.Geometry.Curvature
