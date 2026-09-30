import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.LocalizedFrame.Coordinates
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Local.ChartInvariance

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator


noncomputable section


open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sum_chartChristoffel_diag_eq_half_trace
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i k k y) =
      (1 / 2 : ℝ) * ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y := by
  classical
  have hexpand : (∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i k k y) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α k l y *
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y +
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y -
           DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartChristoffel_def, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← chartInvGramOnE_def]
  rw [hexpand]
  rw [Finset.mul_sum]
  rw [show (∑ k : Fin (Module.finrank ℝ E), (1 / 2 : ℝ) *
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α k l y *
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y) =
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          (1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α k l y *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y) from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]]
  rw [← sub_eq_zero]
  rw [← Finset.sum_sub_distrib]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
          ((∑ l : Fin (Module.finrank ℝ E),
              (1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α k l y *
                (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y +
                 DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y -
                 DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y))) -
            ∑ l : Fin (Module.finrank ℝ E),
              (1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α k l y *
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y))) =
        (1 / 2 : ℝ) * (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          (chartInvGramOnE (I := I) g α k l y *
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y -
            chartInvGramOnE (I := I) g α k l y *
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y)) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring]
  rw [mul_eq_zero]
  right
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          (chartInvGramOnE (I := I) g α k l y *
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y -
            chartInvGramOnE (I := I) g α k l y *
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y)) =
        (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k l y *
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y) -
          ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k l y *
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y from by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.sum_sub_distrib]]
  rw [sub_eq_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hGUsym : chartInvGramOnE (I := I) g α l k y =
      chartInvGramOnE (I := I) g α k l y := chartInvGramOnE_symm (I := I) g α l k y
  have hdGsym : DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α k i) y =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y := by
    congr 1
    funext z
    exact chartGramOnE_symm (I := I) g α k i z
  rw [hGUsym, hdGsym]

omit [CompactSpace M] [I.Boundaryless] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_chartDensityOnE_eq_sum_chartChristoffel_diag
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y =
      (∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i k k y) * chartDensityOnE (I := I) g α y := by
  classical
  have htrace : Matrix.trace
        ((DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α ((extChartAt I α).symm y))⁻¹ *
          Matrix.of (fun a b => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
            (chartGramOnE (I := I) g α a b) y)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [chartInvGramOnE_def, Matrix.of_apply]
    rfl
  rw [partialDeriv_chartDensityOnE (I := I) g α y i hy]
  rw [sum_chartChristoffel_diag_eq_half_trace (I := I) g α i y]
  rw [htrace]

private noncomputable def coordProjE (k : Fin (Module.finrank ℝ E)) :
    E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.proj k).comp ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun.toLinearMap)) :
      E →ₗ[ℝ] ℝ)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma coordProjE_apply (k : Fin (Module.finrank ℝ E)) (v : E) :
    coordProjE (E := E) k v = ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr v) k := by
  classical
  unfold coordProjE
  change ((LinearMap.proj k).comp ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun.toLinearMap)) v = _
  rw [LinearMap.comp_apply]
  simp [Module.Basis.equivFun]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    in
private lemma trivToE_chartBasisVecFiber
    (α : M) (m : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    trivToE (I := I) α b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b) = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m := by
  classical
  have hcoe : DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b = trivFromE (I := I) α b
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m) := by
    unfold DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber trivFromE
    rfl
  rw [hcoe, trivToE_trivFromE (I := I) α hb]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartCoord_leviCivita_chartBasis
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (m k : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
        (trivToE (I := I) α b
          ((LeviCivita (I := I) g).toFun Z.toFun b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))) k =
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartCoeffOnE (I := I) α Z k) (extChartAt I α b) +
        ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α m j k (extChartAt I α b) *
            chartCoeffOnE (I := I) α Z j (extChartAt I α b) := by
  classical
  set y₀ : E := extChartAt I α b with hy₀_def
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hZ_mdiff :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) y (Z.toFun y)) b :=
    (Z.contMDiff b).mdifferentiableAt (by simp)
  rw [LeviCivita_chart_apply (I := I) g α hb hZ_mdiff
    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b)]
  rw [chartLeviCivita_apply (I := I) g α Z.toFun hb
    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b)]
  rw [trivToE_trivFromE (I := I) α hb_base]
  rw [trivToE_chartBasisVecFiber (I := I) α m hb_base]
  rw [map_add]
  rw [Finsupp.add_apply]
  congr 1
  · set F : E → E :=
      chartESectionRepr (I := I) α Z.toFun ∘ (extChartAt I α).symm with hF_def
    have hb_source : b ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
    have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
      chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
    have hF_diff : DifferentiableAt ℝ F y₀ := by
      rw [hF_def, hy₀_def]
      exact (mdifferentiableAt_section_iff_chartE_fderiv I α Z.toFun
        hb_source hb_base hb_int).mp hZ_mdiff
    rw [show ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (fderiv ℝ F y₀ ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m))) k =
          coordProjE (E := E) k (fderiv ℝ F y₀ ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m)) from by
        rw [coordProjE_apply]]
    rw [← ContinuousLinearMap.comp_apply]
    rw [show (coordProjE (E := E) k).comp (fderiv ℝ F y₀) =
          fderiv ℝ ((coordProjE (E := E) k : E → ℝ) ∘ F) y₀ from by
        rw [fderiv_comp y₀ (coordProjE (E := E) k).differentiableAt hF_diff,
            ContinuousLinearMap.fderiv]]
    change (fderiv ℝ ((coordProjE (E := E) k : E → ℝ) ∘ F) y₀) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) m) =
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartCoeffOnE (I := I) α Z k) y₀
    have htgt_nhd : (extChartAt I α).target ∈ 𝓝 y₀ :=
      mem_of_superset (isOpen_interior.mem_nhds hb_int) interior_subset
    have hev : ((coordProjE (E := E) k : E → ℝ) ∘ F) =ᶠ[𝓝 y₀]
        chartCoeffOnE (I := I) α Z k := by
      filter_upwards [htgt_nhd] with z hz
      rw [hF_def]
      simp only [Function.comp_apply, coordProjE_apply]
      rw [chartCoeffOnE, chartCoeff_def]
      have hz_base : (extChartAt I α).symm z ∈
          (trivializationAt E (TangentSpace I) α).baseSet := by
        have hsource : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
          (extChartAt I α).map_target hz
        rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
        rw [trivializationAt_baseSet_eq_chartAt_source]
        exact hsource
      rw [chartE_section_repr_eq_trivialization_snd (I := I) α Z.toFun hz_base]
      rfl
    rw [hev.fderiv_eq]
    rfl
  · rw [christoffelCorrection_apply (I := I) g α b
      (chartESectionRepr (I := I) α Z.toFun b)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b)]
    rw [show ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
            (∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
                    (trivToE (I := I) α b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))) a *
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
                    (chartESectionRepr (I := I) α Z.toFun b)) c *
                  chartChristoffel (I := I) g α a c d (extChartAt I α b)) •
                  (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) d)) k =
          coordProjE (E := E) k
            (∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
                    (trivToE (I := I) α b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))) a *
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
                    (chartESectionRepr (I := I) α Z.toFun b)) c *
                  chartChristoffel (I := I) g α a c d (extChartAt I α b)) •
                  (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) d) from by rw [coordProjE_apply]]
    rw [map_sum]
    rw [trivToE_chartBasisVecFiber (I := I) α m hb_base]
    simp only [map_sum, map_smul, smul_eq_mul, coordProjE_apply,
      Module.Basis.repr_self_apply]
    have hZcoeff : ∀ c : Fin (Module.finrank ℝ E),
        chartCoeffOnE (I := I) α Z c y₀ =
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
            (chartESectionRepr (I := I) α Z.toFun b)) c := by
      intro c
      rw [chartE_section_repr_eq_trivialization_snd (I := I) α Z.toFun hb_base]
      rw [chartCoeffOnE, chartCoeff_def, hy₀_def]
      rw [(extChartAt I α).left_inv (by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb)]
      rfl
    rw [Finset.sum_eq_single m]
    · refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_eq_single k]
      · rw [ite_eq_left rfl, ite_eq_left rfl, hZcoeff c]
        ring
      · intro d _ hdk
        rw [ite_eq_right hdk]
        ring
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    · intro a _ ham
      rw [ite_eq_right (Ne.symm ham)]
      simp
    · intro hm
      exact absurd (Finset.mem_univ m) hm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    in
private lemma tangent_eq_coordSum
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (w : TangentSpace I b) :
    w = ∑ k : Fin (Module.finrank ℝ E),
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α b w)) k •
        DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b := by
  classical
  have hsum : trivToE (I := I) α b w =
      ∑ k : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α b w)) k • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k :=
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).sum_repr (trivToE (I := I) α b w)).symm
  calc w = trivFromE (I := I) α b (trivToE (I := I) α b w) :=
            (trivFromE_trivToE (I := I) α hb w).symm
    _ = trivFromE (I := I) α b
          (∑ k : Fin (Module.finrank ℝ E),
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α b w)) k •
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k) := by rw [← hsum]
    _ = ∑ k : Fin (Module.finrank ℝ E),
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α b w)) k •
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b := by
          rw [map_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [map_smul]
          rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma inner_leviCivita_chartBasis_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (m n : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    g.inner b
        ((LeviCivita (I := I) g).toFun Z.toFun b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α n b) =
      ∑ k : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartCoeffOnE (I := I) α Z k) (extChartAt I α b) +
          ∑ j : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α m j k (extChartAt I α b) *
              chartCoeffOnE (I := I) α Z j (extChartAt I α b)) *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k n := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  rw [tangent_eq_coordSum (I := I) α hb_base
    ((LeviCivita (I := I) g).toFun Z.toFun b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))]
  rw [map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_apply, smul_eq_mul]
  rw [chartCoord_leviCivita_chartBasis (I := I) g α Z m k hb]
  rw [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]

omit [I.Boundaryless] in
lemma frameTrace_eq_metricTrace
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {b : M}
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (∑ i : Fin (Module.finrank ℝ E),
        g.inner b
          ((LeviCivita (I := I) g).toFun Z.toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)) =
      ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b m n *
          g.inner b
            ((LeviCivita (I := I) g).toFun Z.toFun b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α n b) := by
  classical
  set C : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b with hC_def
  set L := (LeviCivita (I := I) g).toFun Z.toFun b with hL_def
  have hsummand : ∀ i : Fin (Module.finrank ℝ E),
      g.inner b (L ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) =
        ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
          C i m * C i n *
            g.inner b (L (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α n b) := by
    intro i
    have hFeq : (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
        ∑ m : Fin (Module.finrank ℝ E), C i m • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b := by
      rw [hC_def]
      exact chartFrameNormGlobalSmooth_eq_coordMatrix_sum (I := I) (M := M) g α i hb
    rw [hFeq]
    have hLslot : L (∑ m : Fin (Module.finrank ℝ E),
            C i m • DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b) =
        ∑ m : Fin (Module.finrank ℝ E),
          C i m • L (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [map_smul]
    rw [hLslot]
    have hslot1 : (g.inner b) (∑ m : Fin (Module.finrank ℝ E),
            C i m • L (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b)) =
        ∑ m : Fin (Module.finrank ℝ E),
          C i m • (g.inner b) (L (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [map_smul]
    rw [hslot1, sum_apply]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [smul_apply, smul_eq_mul]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [map_smul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← Finset.sum_mul]
  rw [show (∑ i : Fin (Module.finrank ℝ E), C i m * C i n) =
        chartInvGramMatrix (I := I) g α b m n from by
      rw [hC_def]
      exact chartFrameNormGlobalSmoothCoordMatrix_orthonormality
        (I := I) (M := M) g α hb_pou hb m n]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma metricTrace_eq_coord_covariant_divergence
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b m n *
          g.inner b
            ((LeviCivita (I := I) g).toFun Z.toFun b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α n b)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartCoeffOnE (I := I) α Z m) (extChartAt I α b) +
          ∑ j : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α m j m (extChartAt I α b) *
              chartCoeffOnE (I := I) α Z j (extChartAt I α b)) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  set A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun m k =>
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartCoeffOnE (I := I) α Z k) (extChartAt I α b) +
        ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α m j k (extChartAt I α b) *
            chartCoeffOnE (I := I) α Z j (extChartAt I α b) with hA_def
  have hstep1 : (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b m n *
          g.inner b
            ((LeviCivita (I := I) g).toFun Z.toFun b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α m b))
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α n b)) =
      ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b m n *
          ∑ k : Fin (Module.finrank ℝ E),
            A m k * DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k n := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [inner_leviCivita_chartBasis_eq (I := I) g α Z m n hb]
  rw [hstep1]
  rw [show (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b m n *
            ∑ k : Fin (Module.finrank ℝ E),
              A m k * DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k n) =
        ∑ m : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          A m k * (∑ n : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b m n *
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k n) from by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [show (∑ n : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α b m n *
                ∑ k : Fin (Module.finrank ℝ E),
                  A m k * DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k n) =
            ∑ n : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              A m k * (chartInvGramMatrix (I := I) g α b m n *
                DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k n) from by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]]
  have hδ : ∀ m k : Fin (Module.finrank ℝ E),
      (∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b m n *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k n) =
        if m = k then (1 : ℝ) else 0 := by
    intro m k
    have hGsym : ∀ n : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k n = DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b n k := by
      intro n
      rw [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, g.symm]
    rw [show (∑ n : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b m n *
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k n) =
          (chartInvGramMatrix (I := I) g α b *
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b) m k from by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [hGsym n]]
    rw [chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hb_base]
    rw [Matrix.one_apply]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [show (∑ k : Fin (Module.finrank ℝ E),
          A m k * (∑ n : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b m n *
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k n)) =
        ∑ k : Fin (Module.finrank ℝ E), A m k * (if m = k then (1 : ℝ) else 0) from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hδ m k]]
  rw [Finset.sum_eq_single m]
  · rw [ite_eq_left rfl, mul_one, hA_def]
  · intro k _ hkm
    rw [ite_eq_right (Ne.symm hkm), mul_zero]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

omit [CompactSpace M] [I.Boundaryless] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma localDivergence_eq_coord_covariant_divergence
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    localDivergence (I := I) g α Z b =
      (∑ i : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) α Z i) (extChartAt I α b)) +
        ∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) α Z i (extChartAt I α b) *
            (∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α i k k (extChartAt I α b)) := by
  classical
  set y₀ : E := extChartAt I α b with hy₀_def
  have hy₀_int : y₀ ∈ interior (extChartAt I α).target :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hy₀_target : y₀ ∈ (extChartAt I α).target := interior_subset hy₀_int
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy₀_nhd : interior (extChartAt I α).target ∈ 𝓝 y₀ := hop_int.mem_nhds hy₀_int
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hD_ne : chartDensity (I := I) g α b ≠ 0 :=
    ne_of_gt (chartDensity_pos (I := I) g α hb_base)
  have hcoeff_diff : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartCoeffOnE (I := I) α Z i) y₀ := by
    intro i
    have hcd : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) α Z i)
        (extChartAt I α).target := chartCoeffOnE_contDiffOn (I := I) α Z i
    have hcd_int : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) α Z i)
        (interior (extChartAt I α).target) := hcd.mono interior_subset
    exact (hcd_int.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hdens_diff : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ :=
    chartDensityOnE_differentiableAt_interior (I := I) g α hy₀_int
  have hD_eq : chartDensity (I := I) g α b = chartDensityOnE (I := I) g α y₀ := by
    rw [chartDensityOnE]
    rw [hy₀_def]
    rw [(extChartAt I α).left_inv (by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb)]
  rw [localDivergence_def]
  rw [hD_eq]
  have hnum : (∑ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y => chartCoeffOnE (I := I) α Z i y * chartDensityOnE (I := I) g α y) y₀) =
      ∑ i : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) α Z i) y₀ *
            chartDensityOnE (I := I) g α y₀ +
          chartCoeffOnE (I := I) α Z i y₀ *
            DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
    rw [fderiv_fun_mul (hcoeff_diff i) hdens_diff]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hnum]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) α Z i) y₀ *
              chartDensityOnE (I := I) g α y₀ +
            chartCoeffOnE (I := I) α Z i y₀ *
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ((DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartCoeffOnE (I := I) α Z i) y₀ +
              chartCoeffOnE (I := I) α Z i y₀ *
                (∑ k : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g α i k k y₀)) *
            chartDensityOnE (I := I) g α y₀) from ?_]
  · have hDOnE_ne : chartDensityOnE (I := I) g α y₀ ≠ 0 := by
      rw [← hD_eq]; exact hD_ne
    rw [← Finset.sum_mul]
    rw [mul_div_assoc, div_self hDOnE_ne, mul_one]
    rw [Finset.sum_add_distrib]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [partialDeriv_chartDensityOnE_eq_sum_chartChristoffel_diag (I := I) g α i hy₀_int]
    ring

omit [CompactSpace M] [I.Boundaryless] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma linearMapTrace_eq_chart_sum
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I : M → Type _) α).baseSet)
    (F : TangentSpace I b →L[ℝ] TangentSpace I b) :
    LinearMap.trace ℝ (TangentSpace I b) F.toLinearMap =
      ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I : M → Type _) α).continuousLinearMapAt ℝ b
            (F (chartBasisVecFiber (I := I) α i b)))) i := by
  classical
  set e := trivializationAt E (TangentSpace I : M → Type _) α with he
  set basisB := chartBasisFamily (I := I) α hb with hbasisB_def
  rw [LinearMap.trace_eq_matrix_trace ℝ basisB F.toLinearMap]
  unfold Matrix.trace
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply]
  rw [show basisB i = chartBasisVecFiber (I := I) α i b from
    chartBasisFamily_apply (I := I) α hb i]
  change (basisB.repr (F (chartBasisVecFiber (I := I) α i b))) i =
      ((chartModelBasis E).repr
        (e.continuousLinearMapAt ℝ b (F (chartBasisVecFiber (I := I) α i b)))) i
  rw [hbasisB_def]
  unfold chartBasisFamily
  rw [Module.Basis.map_repr]
  simp only [LinearEquiv.trans_apply]
  congr 2
  change (e.continuousLinearEquivAt ℝ b hb : TangentSpace I b → E)
      (F (chartBasisVecFiber (I := I) α i b)) =
      (e.continuousLinearMapAt ℝ b : TangentSpace I b → E)
        (F (chartBasisVecFiber (I := I) α i b))
  rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) e hb]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem divergence_g_eq_leviCivita_divergence_of_isInteriorPoint
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx : x ∈ I.interior M) :
    divergenceG (I := I) g Z x =
      divergence (I := I) (leviCivitaConnectionOfMetric (I := I) g) Z x := by
  classical
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) x := by
    refine mem_chartLeviCivitaGoodSet_iff.mpr ⟨mem_extChartAt_source x,
      mem_baseSet_trivializationAt E (TangentSpace I) x, ?_⟩
    exact I.isInteriorPoint_iff.mp hx
  have hxbase : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hxgood
  rw [divergence_g_def]
  rw [localDivergence_eq_coord_covariant_divergence (I := I) g x Z hxgood]
  rw [divergence]
  rw [← LeviCivita_eq_leviCivitaConnectionOfMetric]
  rw [linearMapTrace_eq_chart_sum (I := I) x hxbase]
  have hdiag : ∀ i : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt ℝ x
          ((LeviCivita (I := I) g) (fun y => Z y) x
            (chartBasisVecFiber (I := I) x i x)))) i =
        partialDeriv (E := E) i (chartCoeffOnE (I := I) x Z i) (extChartAt I x x) +
          ∑ j : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x i j i (extChartAt I x x) *
              chartCoeffOnE (I := I) x Z j (extChartAt I x x) := by
    intro i
    exact chartCoord_leviCivita_chartBasis (I := I) g x Z i i hxgood
  rw [show (∑ i : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt ℝ x
          ((LeviCivita (I := I) g) (fun y => Z y) x
            (chartBasisVecFiber (I := I) x i x)))) i) =
      ∑ i : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) i (chartCoeffOnE (I := I) x Z i) (extChartAt I x x) +
          ∑ j : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x i j i (extChartAt I x x) *
              chartCoeffOnE (I := I) x Z j (extChartAt I x x)) from
    Finset.sum_congr rfl (fun i _ => hdiag i)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) x Z i (extChartAt I x x) *
            ∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g x i k k (extChartAt I x x)) =
        ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g x i k k (extChartAt I x x) *
            chartCoeffOnE (I := I) x Z i (extChartAt I x x) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartChristoffel_symm (I := I) g x k i i]

theorem voss_weyl_divergence_eq_leviCivita_frameTrace
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {b : M}
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    divergenceG (I := I) g Z b =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner b
          ((LeviCivita (I := I) g).toFun Z.toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) := by
  classical
  have hb_source : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  rw [voss_weyl_divergence_formula (I := I) g α Z hb_source]
  rw [localDivergence_eq_coord_covariant_divergence (I := I) g α Z hb]
  rw [frameTrace_eq_metricTrace (I := I) g α Z hb_pou hb]
  rw [metricTrace_eq_coord_covariant_divergence (I := I) g α Z hb]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) α Z i (extChartAt I α b) *
            ∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α i k k (extChartAt I α b)) =
        ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i k k (extChartAt I α b) *
            chartCoeffOnE (I := I) α Z i (extChartAt I α b) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartChristoffel_symm (I := I) g α k i i]

end Connection
end Geometry
end DifferentialGeometry

end
