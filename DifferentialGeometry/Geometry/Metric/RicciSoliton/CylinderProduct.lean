import DifferentialGeometry.Geometry.Metric.RicciSoliton.PotentialSplitting
import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceIsometry

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator

variable {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [SimplyConnectedSpace M]

theorem exists_roundThreeCylinder_solitonModelCovering_of_prod_real_line_of_finrank_eq_two_of_nonflat
    {g : SmoothRiemannianMetric I M}
    {u : C^∞⟮I.prod 𝓘(Real, Real), M × Real; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I.prod 𝓘(Real, Real))
      (g.prod (euclideanMetric (E := Real))) u)
    (hdim : Module.finrank Real E = 2)
    (hnonflat : ∃ x : M, metricRm04At (I := I) g x ≠ 0) :
    ∃ Phi : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
        ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), I.prod 𝓘(Real, Real)⟯ (M × Real),
      solitonModelCovering roundThreeCylinderShrinkerMetric
        roundThreeCylinderShrinkerPotential
        (g.prod (euclideanMetric (E := Real))) u Phi := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  obtain ⟨s0, psi, hsplit, hpsi⟩ :=
    normalizedGradientRicciSoliton_prod_real_line_potential_splitting h
  obtain ⟨e, b, hemetric, hepotential⟩ :=
    gradientRicciSoliton_exists_round_sphere_isometry_of_finrank_eq_two_of_simply_connected_of_nonflat
      hpsi.1 hpsi.2.1 zero_lt_one hdim hnonflat
  have hpsiConst : (psi : M → Real) = fun _ => b := funext hepotential
  have hpsiOne (x : M) : psi x = 1 := by
    have htrace := gradientRicciSoliton_trace hpsi.2.1 x
    have hpsiMap : psi = ContMDiffMap.const b := by
      ext x
      exact hepotential x
    have hLap : ΔG (I := I) g psi x = 0 := by
      rw [hpsiMap, Operator.Δ_g_const]
    rw [hLap] at htrace
    have hscalar : metricScalarAt (I := I) g x = 1 := by
      norm_num [hdim] at htrace
      exact htrace
    have hnormal := hpsi.2.2 x
    rw [hpsiConst, normGradSqFun_def, gradFun_const] at hnormal
    simp only [map_zero, hscalar, add_zero] at hnormal
    exact (hepotential x).trans hnormal.symm
  have hemetric' : Diffeomorph.pullbackMetricCross roundTwoSphereShrinkerMetric e = g := by
    convert hemetric using 1
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    let _ : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩
    simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric,
      roundSphereShrinkerRadius_sq (by decide : 2 ≤ 2)]
    norm_num
  have hinverse : Diffeomorph.pullbackMetricCross g e.symm = roundTwoSphereShrinkerMetric :=
    Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hemetric'
  let T : Real ≃ₘ⟮𝓘(Real, Real), 𝓘(Real, Real)⟯ Real :=
    { toEquiv := Equiv.addRight s0
      contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
      contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  have hT (s : Real) : T s = s + s0 := rfl
  have hdT (s : Real) : mfderiv 𝓘(Real, Real) 𝓘(Real, Real) T s =
      ContinuousLinearMap.id Real Real := by
    change mfderiv 𝓘(Real, Real) 𝓘(Real, Real) (fun s : Real => s + s0) s = _
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id s).add_const s0).fderiv
  let Phi := e.symm.prodCongr T
  refine ⟨Phi, normalizedGradientRicciSoliton_roundThreeCylinder, h,
    Phi.isLocalDiffeomorph, Phi.surjective, ?_, ?_, ?_⟩
  · exact (solitonModelCovering_isCoveringMap
      (solitonModelCovering_refl normalizedGradientRicciSoliton_roundThreeCylinder)).homeomorph_comp
        Phi.toHomeomorph
  · intro x v w
    have hdi : mfderiv ((𝓡 2).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, Real)) Phi x =
        (mfderiv (𝓡 2) I e.symm x.1).prodMap (ContinuousLinearMap.id Real Real) := by
      rw [show (Phi : _ → _) = Prod.map (e.symm : _ → M) (T : Real → Real) from rfl]
      rw [mfderiv_prodMap (e.symm.contMDiff.mdifferentiableAt (by simp))
        (T.contMDiff.mdifferentiableAt (by simp)), hdT]
      rfl
    have hsurf := congrArg
      (fun k : SmoothRiemannianMetric (𝓡 2)
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) => k.inner x.1 v.1 w.1) hinverse
    erw [Diffeomorph.pullbackMetricCross_inner] at hsurf
    rw [roundThreeCylinderShrinkerMetric, SmoothRiemannianMetric.prod_inner,
      SmoothRiemannianMetric.prod_inner, hdi]
    simp only [ContinuousLinearMap.prodMap]
    change roundTwoSphereShrinkerMetric.inner x.1 v.1 w.1 +
        (euclideanMetric (E := Real)).inner x.2 v.2 w.2 =
      g.inner (e.symm x.1) (mfderiv (𝓡 2) I e.symm x.1 v.1)
        (mfderiv (𝓡 2) I e.symm x.1 w.1) +
          (euclideanMetric (E := Real)).inner (T x.2) v.2 w.2
    rw [hsurf]
    erw [euclideanMetric_inner]
  · intro x
    rw [hsplit, hpsiOne, roundThreeCylinderShrinkerPotential_apply]
    change 1 + x.2 ^ 2 / 4 = 1 + (1 / 4 : Real) * (T x.2 - s0) ^ 2
    rw [hT, add_sub_cancel_right]
    ring

theorem exists_roundThreeCylinder_solitonModelCovering_of_prod_real_line_of_finrank_eq_two_of_scalar_pos
    {g : SmoothRiemannianMetric I M}
    {u : C^∞⟮I.prod 𝓘(Real, Real), M × Real; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I.prod 𝓘(Real, Real))
      (g.prod (euclideanMetric (E := Real))) u)
    (hdim : Module.finrank Real E = 2)
    (hpositive : ∃ x : M, 0 < metricScalarAt (I := I) g x) :
    ∃ Phi : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
        ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), I.prod 𝓘(Real, Real)⟯ (M × Real),
      solitonModelCovering roundThreeCylinderShrinkerMetric
        roundThreeCylinderShrinkerPotential
        (g.prod (euclideanMetric (E := Real))) u Phi := by
  obtain ⟨x, hx⟩ := hpositive
  apply exists_roundThreeCylinder_solitonModelCovering_of_prod_real_line_of_finrank_eq_two_of_nonflat
    h hdim
  refine ⟨x, ?_⟩
  intro hzero
  exact (ne_of_gt hx) (metricScalarAt_eq_zero_of_metricRm04At_eq_zero g x hzero)

end DifferentialGeometry.Geometry
