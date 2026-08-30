import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

private theorem clock_eq_at
    (phi : Real → Real) {a b s0 : Real}
    (hs0 : s0 ∈ Ioo a b)
    (hphi : ∀ s ∈ Ioo a b, HasDerivAt phi 1 s)
    (hval : phi s0 = s0) :
    ∀ s ∈ Ioo a b, phi s = s := by
  let psi : Real → Real := phi - id
  have hconst (s : Real) (hs : s ∈ Ioo a b) :
      HasDerivAt psi 0 s := by
    simpa only [psi, sub_self] using (hphi s hs).sub (hasDerivAt_id s)
  intro s hs
  have hkey : psi s = psi s0 := by
    apply Convex.is_const_of_fderivWithin_eq_zero (𝕜 := Real)
      (convex_Ioo a b) (f := psi) (s := Ioo a b)
    · intro q hq
      exact (hconst q hq).differentiableAt.differentiableWithinAt
    · intro q hq
      have huniq : UniqueDiffWithinAt Real (Ioo a b) q :=
        isOpen_Ioo.uniqueDiffWithinAt hq
      have hfd : HasFDerivWithinAt psi
          (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real) (0 : Real))
          (Ioo a b) q :=
        ((hconst q hq).hasDerivWithinAt).hasFDerivWithinAt
      rw [hfd.fderivWithin huniq]
      ext
      simp
    · exact hs
    · exact hs0
  simp only [psi, Pi.sub_apply, id_eq] at hkey
  rw [hval] at hkey
  linarith

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

theorem exists_lPhaseSol_at
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : Real) (x0 : M) (s0 : Real) (z0 : E × E)
    (hT : T - s0 ^ 2 ∈ D.regular)
    (hz : z0.1 ∈ interior (extChartAt I x0).target) :
    ∃ (epsilon : Real) (_ : 0 < epsilon) (z : Real → E × E),
      z s0 = z0 ∧
        ∀ s ∈ Ioo (s0 - epsilon) (s0 + epsilon),
          HasDerivAt z (lPhaseField S T x0 s (z s)) s := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let vf0 : Real × (E × E) → Real × (E × E) := fun p ↦
    ((1 : Real), lPhaseField S T x0 p.1 p.2)
  let vf : (p : Real × (E × E)) →
      TangentSpace (modelWithCornersSelf Real (Real × (E × E))) p := fun p ↦
    (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real (Real × (E × E))) p).symm (vf0 p)
  have hphase : ContDiffAt Real 1
      (Function.uncurry (lPhaseField S T x0)) (s0, z0) :=
    (lPhaseField_smoothAt S hS T x0 hT hz).of_le (by norm_num)
  have hvf : ContDiffAt Real 1 vf0 (s0, z0) :=
    contDiffAt_const.prodMk hphase
  have hsection :
      ContMDiffAt (modelWithCornersSelf Real (Real × (E × E)))
        ((modelWithCornersSelf Real (Real × (E × E))).prod
          (modelWithCornersSelf Real (Real × (E × E)))) 1
        (fun p : Real × (E × E) ↦
          (⟨p, vf p⟩ : TangentBundle
            (modelWithCornersSelf Real (Real × (E × E)))
            (Real × (E × E)))) (s0, z0) := by
    rw [Bundle.contMDiffAt_section]
    simpa only [vf, tangentSpaceModelContinuousLinearEquiv_symm_apply,
      trivializationAt_model_space_apply] using hvf.contMDiffAt
  obtain ⟨c, hc0, hcurve⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (v := vf) (x₀ := (s0, z0)) (t₀ := s0) hsection
  rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem] at hcurve
  obtain ⟨U, hU, hcurveU⟩ := hcurve
  rw [Metric.mem_nhds_iff] at hU
  obtain ⟨epsilon, hepsilon, hball⟩ := hU
  refine ⟨epsilon, hepsilon, fun s ↦ (c s).2, ?_, ?_⟩
  · change (c s0).2 = z0
    rw [hc0]
  · intro s hs
    have hsU : s ∈ U := by
      apply hball
      simpa only [Real.ball_eq_Ioo] using hs
    let X : Real → ∀ z : E × E,
        TangentSpace (modelWithCornersSelf Real (E × E)) z := fun r z ↦
      (tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real (E × E)) z).symm
        (lPhaseField S T x0 r z)
    have hcurveX : ∀ r ∈ U,
        HasMFDerivAt (modelWithCornersSelf Real Real)
          ((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real (E × E))) c r
          ((1 : Real →L[Real] Real).smulRight
            (DifferentialGeometry.Analysis.ODE.autonomizedFlowVF X (c r))) := by
      intro r hr
      refine (hcurveU r hr).congr_mfderiv ?_
      congr 1
    have hcderiv :
        HasMFDerivAt (modelWithCornersSelf Real Real)
          ((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real (E × E))) c s
          ((1 : Real →L[Real] Real).smulRight
            (DifferentialGeometry.Analysis.ODE.autonomizedFlowVF X (c s))) := by
      exact hcurveX s hsU
    have hs0 : s0 ∈ Ioo (s0 - epsilon) (s0 + epsilon) := by
      constructor <;> linarith
    have htime : ∀ r ∈ Ioo (s0 - epsilon) (s0 + epsilon),
        (c r).1 = r := by
      apply clock_eq_at (fun r ↦ (c r).1) hs0
      · intro r hr
        have hrU : r ∈ U := by
          apply hball
          simpa only [Real.ball_eq_Ioo] using hr
        apply DifferentialGeometry.Analysis.ODE.autonomizedFlow_fst_hasDerivAt
          (I := modelWithCornersSelf Real (E × E)) X c r
        exact hcurveX r hrU
      · rw [hc0]
    have hsnd :=
      DifferentialGeometry.Analysis.ODE.autonomizedFlow_snd_hasMFDerivAt
        (I := modelWithCornersSelf Real (E × E)) X c s hcderiv
    rw [htime s hs] at hsnd
    have hsnd' := hasMFDerivAt_iff_hasFDerivAt.mp hsnd
    change HasFDerivAt (fun s => (c s).2)
      (ContinuousLinearMap.toSpanSingleton Real
        (lPhaseField S T x0 s (c s).2)) s
    refine hsnd'.congr_fderiv ?_
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
    congr 1

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
