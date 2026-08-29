import DifferentialGeometry.Analysis.Calculus.CompactCutoff
import DifferentialGeometry.Analysis.ODE.CompactSupportFlow
import DifferentialGeometry.Geometry.Comparison.Variation.FixedChartIdentities
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import DifferentialGeometry.Bundle.FiberBundleHausdorff

noncomputable section

open Bundle Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hM : IsManifold I ∞ M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_var_fix_ends
    (g : SmoothRiemannianMetric I M)
    (gamma : Real → M) (V : Real → E) (a b : Real)
    (hV : ContMDiff 𝓘(Real, Real) I.tangent (8 : Nat)
      (fun t => (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (gamma t) (V t) :
          TangentBundle I M)))
    (hVa : V a = 0) (hVb : V b = 0) :
    ∃ f : Real → Real → M,
      IsSmoothVariation (I := I) f ∧
      (∀ t, f 0 t = gamma t) ∧
      (∀ t ∈ uIcc a b,
        (mfderiv 𝓘(Real, Real) I (fun u => f u t) 0 1 : E) = V t) ∧
      (∀ u, f u a = gamma a) ∧
      (∀ u, f u b = gamma b) := by
  classical
  let init : Real → TangentBundle I M := fun t =>
    (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
      (gamma t) (V t) : TangentBundle I M)
  let K : Set (TangentBundle I M) := init '' uIcc a b
  have hK : IsCompact K := isCompact_uIcc.image hV.continuous
  obtain ⟨psi, hpsi, hpsic, hpsione⟩ :=
    exists_bump_nhds (I := I.tangent) hK
  let X : (q : TangentBundle I M) → TangentSpace I.tangent q :=
    fun q => psi q • geodesicVectorField (I := I) g q
  have hX : ContMDiff I.tangent I.tangent.tangent ∞
      (fun q : TangentBundle I M =>
        (⟨q, X q⟩ : TangentBundle I.tangent (TangentBundle I M))) := by
    exact hpsi.smul_section (geodesicVF_smooth (I := I) g)
  have hXc : IsCompact (tsupport X) := by
    change HasCompactSupport (psi • geodesicVectorField (I := I) g)
    exact hpsic.smul_right
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let hcomplete : ∀ q : TangentBundle I M,
      ∃ c : Real → TangentBundle I M,
        c 0 = q ∧ IsMIntegralCurve c X :=
    exists_globalIntegralCurve_of_compactSupport
      (I := I.tangent) (M := TangentBundle I M) X hX hXc
  have hflow : ContMDiff (𝓘(Real, Real).prod I.tangent) I.tangent ∞
      (fun p : Real × TangentBundle I M =>
        curveAt X hcomplete p.2 p.1) :=
    contMDiff_globalFlow_joint_of_compactSupport
      (I := I.tangent) (M := TangentBundle I M) X hX hXc
  let f : Real → Real → M := fun u t =>
    (curveAt X hcomplete (init t) u).proj
  have hf : IsSmoothVariation (I := I) f := by
    have hin : ContMDiff
        (𝓘(Real, Real).prod 𝓘(Real, Real))
        (𝓘(Real, Real).prod I.tangent) (8 : Nat)
        (fun p : Real × Real => (p.1, init p.2)) :=
      contMDiff_fst.prodMk (hV.comp contMDiff_snd)
    have hlift : ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I.tangent (8 : Nat)
        (fun p : Real × Real => curveAt X hcomplete (init p.2) p.1) :=
      (hflow.of_le
        (WithTop.coe_le_coe.mpr (le_top : (8 : ℕ∞) ≤ ⊤))).comp hin
    have hproj : ContMDiff I.tangent I (8 : Nat)
        (fun q : TangentBundle I M => q.proj) :=
      contMDiff_proj (TangentSpace I)
    change ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (8 : Nat)
      (fun p : Real × Real =>
        (curveAt X hcomplete (init p.2) p.1).proj)
    exact hproj.comp hlift
  have hfzero : ∀ t, f 0 t = gamma t := by
    intro t
    simp only [f, curveAt_zero]
    rfl
  have hfield : ∀ t ∈ uIcc a b,
      (mfderiv 𝓘(Real, Real) I (fun u => f u t) 0 1 : E) = V t := by
    intro t ht
    let c : Real → TangentBundle I M := fun u =>
      curveAt X hcomplete (init t) u
    have hc : IsMIntegralCurve c X :=
      curveAt_integralCurve X hcomplete (init t)
    have hinitK : init t ∈ K := ⟨t, ht, rfl⟩
    have hpsinit : psi =ᶠ[𝓝 (init t)] 1 :=
      eventually_nhdsSet_iff_forall.mp hpsione (init t) hinitK
    have hpsic : ∀ᶠ u in 𝓝 0, psi (c u) = 1 := by
      have hc0 : Tendsto c (𝓝 0) (𝓝 (init t)) := by
        have hc0eq : c 0 = init t := by
          simp only [c, curveAt_zero]
        rw [← hc0eq]
        exact (hc.continuous.continuousAt : ContinuousAt c 0)
      exact hpsinit.comp_tendsto hc0
    have hsrc0 : (c 0).proj ∈ (chartAt H (gamma t)).source := by
      simp only [c, curveAt_zero]
      exact mem_chart_source H (gamma t)
    have hcproj : Continuous (fun u => (c u).proj) :=
      ((contMDiff_proj (TangentSpace I) :
        ContMDiff I.tangent I ∞
          (fun q : TangentBundle I M => q.proj))).continuous.comp hc.continuous
    have hsrcc : ∀ᶠ u in 𝓝 0,
        (c u).proj ∈ (chartAt H (gamma t)).source :=
      hcproj.continuousAt.eventually
        ((chartAt H (gamma t)).open_source.mem_nhds hsrc0)
    have hchart : IsMIntegralCurveAt c
        (geodesicVectorFieldChart (I := I) g (gamma t)) 0 := by
      rw [IsMIntegralCurveAt]
      filter_upwards [hc.isMIntegralCurveAt 0, hpsic, hsrcc] with u hu hpsiu hsrcu
      have hXu : X (c u) =
          geodesicVectorFieldChart (I := I) g (gamma t) (c u) := by
        change psi (c u) • geodesicVectorField (I := I) g (c u) = _
        rw [hpsiu, one_smul]
        exact (geodesicVectorFieldChart_eq_geodesicVectorField
          (I := I) g (gamma t) hsrcu).symm
      rw [hXu] at hu
      exact hu
    have hvel := hchart.mfderiv_proj_one hsrc0
    have hc0 : c 0 = init t := by
      simp only [c, curveAt_zero]
    rw [hc0] at hvel
    rw [hfzero t]
    convert hvel using 1 ; rfl
  have hstationary : ∀ t, V t = 0 → ∀ u,
      curveAt X hcomplete (init t) u = init t := by
    intro t hVt u
    have hXt : X (init t) = 0 := by
      have hinit : init t =
          (⟨gamma t, (0 : E)⟩ : TangentBundle I M) := by
        simp only [init, hVt]
      rw [hinit]
      simp only [X, geodesicVectorField_zero_section]
      exact smul_zero _
    have hconst : IsMIntegralCurve (fun _ : Real => init t) X := by
      intro s
      rw [hXt, ContinuousLinearMap.smulRight_zero]
      exact hasMFDerivAt_const (c := init t) (x := s)
        (I := 𝓘(Real, Real)) (I' := I.tangent)
    have hXone : ContMDiff I.tangent I.tangent.tangent 1
        (fun q : TangentBundle I M =>
          (⟨q, X q⟩ : TangentBundle I.tangent (TangentBundle I M))) :=
      hX.of_le (by norm_num)
    have heq := integralCurve_eq_of_agree_zero X hXone
      (curveAt_integralCurve X hcomplete (init t)) hconst (by
        rw [curveAt_zero])
    exact congrFun heq u
  refine ⟨f, hf, hfzero, hfield, ?_, ?_⟩
  · intro u
    simp only [f]
    rw [hstationary a hVa u]
  · intro u
    simp only [f]
    rw [hstationary b hVb u]

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
