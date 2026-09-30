import DifferentialGeometry.Geometry.Metric.UniformExponential








noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]



theorem exists_smooth_exp_neighborhood (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) (p : M) :
    ∃ W : Set (TangentBundle I M), IsOpen W ∧ TotalSpace.mk' E p 0 ∈ W ∧
      ContMDiffOn I.tangent I ∞ (fun u : TangentBundle I M =>
        expMapIntrinsic (I := I) g hg u.proj u.2) W := by
  obtain ⟨Φ, ρ, T, t, hρ, hT, ht, htpos, hG, hinit, hode, htarget, _⟩ :=
    exists_chartExp_jointContDiffOn_infty (I := I) g p
  let c := extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)
  let R : E × E → E × E := fun z => (z.1, t⁻¹ • z.2)
  let G : E × E → E := fun z => (Φ (z, t)).1
  have hR : ContDiff ℝ ∞ R := contDiff_fst.prodMk (contDiff_const.smul contDiff_snd)
  let W := c.source ∩ (fun u => R (c u)) ⁻¹' Metric.ball (extChartAt I p p, 0) ρ
  have hc : ContMDiffOn I.tangent 𝓘(ℝ, E × E) ∞ c c.source := by
    simpa only [c, extChartAt_source] using
      (contMDiffOn_extChartAt (I := I.tangent)
        (x := (⟨p, (0 : E)⟩ : TangentBundle I M)) (n := ∞))
  have hRC := hR.contMDiff.comp_contMDiffOn hc
  have hW : IsOpen W := hRC.continuousOn.isOpen_inter_preimage
    (by simpa only [c, extChartAt_source] using
      (chartAt (ModelProd H E) (⟨p, (0 : E)⟩ : TangentBundle I M)).open_source)
    Metric.isOpen_ball
  have hpW : TotalSpace.mk' E p (0 : TangentSpace I p) ∈ W := by
    refine ⟨mem_extChartAt_source _, ?_⟩
    change R (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)
      (⟨p, (0 : E)⟩ : TangentBundle I M)) ∈ Metric.ball (extChartAt I p p, 0) ρ
    rw [TangentBundle.extChartAt_tangent_zero_apply_chartFiber (I := I) p (mem_chart_source H p),
      TangentBundle.chartFiberCoord_self_zero]
    simpa only [R, smul_zero] using Metric.mem_ball_self hρ
  have hRG : ContMDiffOn I.tangent 𝓘(ℝ, E) ∞ (fun u => G (R (c u))) W :=
    hG.contMDiffOn.comp (hRC.mono inter_subset_left) (fun _ hu => hu.2)
  have hfinal : ContMDiffOn I.tangent I ∞
      (fun u => (extChartAt I p).symm (G (R (c u)))) W := by
    apply (contMDiffOn_extChartAt_symm p).comp hRG
    intro u hu
    change G (R (c u)) ∈ (extChartAt I p).target
    exact interior_subset (htarget (R (c u)) hu.2 t (Ioo_subset_Icc_self ht)).1
  refine ⟨W, hW, hpW, hfinal.congr ?_⟩
  intro u hu
  have hubase : u.proj ∈ (chartAt H p).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) p u).mp
      (by simpa only [c, extChartAt_source] using! hu.1)
  have hphase : (extChartAt I p u.proj,
      TangentBundle.chartFiberCoord (I := I) p (TotalSpace.mk' E u.proj (t⁻¹ • u.2))) = R (c u) := by
    rw [chartFiberCoord_fiberScale (I := I) p t⁻¹ hubase]
    dsimp only [R, c]
    rw [TangentBundle.extChartAt_tangent_zero_apply_chartFiber (I := I) p hubase]
  have hb := expMapIntrinsic_eq_chartFlow_proj_residual (I := I) g hg p 1 Φ ρ T t
    ⟨hρ, hT, ht, htpos, hG.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)),
      hinit, hode, htarget⟩ u.proj hubase u.2 (hphase.symm ▸ hu.2)
  simpa only [hphase, G] using hb



theorem exists_smooth_exp_zeroSection_neighborhood (g : SmoothRiemannianMetric I M)
    (hg : IsMetricNorm (I := I) (M := M) g) :
    ∃ W : Set (TangentBundle I M), IsOpen W ∧ (∀ p, TotalSpace.mk' E p 0 ∈ W) ∧
      ContMDiffOn I.tangent I ∞ (fun u : TangentBundle I M =>
        expMapIntrinsic (I := I) g hg u.proj u.2) W := by
  choose W hW hp hs using exists_smooth_exp_neighborhood g hg
  refine ⟨⋃ p, W p, isOpen_iUnion hW, fun p => mem_iUnion.mpr ⟨p, hp p⟩, ?_⟩
  intro u hu
  obtain ⟨p, hup⟩ := mem_iUnion.mp hu
  exact ((hs p u hup).contMDiffAt ((hW p).mem_nhds hup)).contMDiffWithinAt

end DifferentialGeometry.Geometry
