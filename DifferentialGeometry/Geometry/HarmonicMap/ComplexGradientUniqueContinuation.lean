import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientAnalyticGauge
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ExistenceReduction
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem exists_analytic_factor_with_differential_zero_set
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    ∃ R : ℝ, 0 < R ∧ ball a R ⊆ ball (0 : ℂ) 1 ∧
      ∃ F : ℂ → (Fin (Module.finrank ℝ E) → ℂ),
        AnalyticOnNhd ℂ F (ball a R) ∧
        ∀ z ∈ ball a R,
          F z = 0 ↔ mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z = 0 := by
  obtain ⟨R, hR, hbuffer, _, A_R, _, _, P, _, _, _, _, _, _, hfactor⟩ :=
    hu.exists_analytic_complex_gradient_gauge ha
  dsimp only at hfactor
  obtain ⟨_, _, _, _, _, _, hF, _, _, hzero⟩ := hfactor
  refine ⟨R, hR, ?_, _, hF, hzero⟩
  exact (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith : R ≤ 2 * R))).trans hbuffer

omit [FiniteDimensional ℝ E] in
private theorem eventually_eq_of_zero_differential_on_open
    {U : ℂ → M} (hU : Continuous U) {D : Set ℂ} (hD : IsOpen D)
    (hmd : ∀ z ∈ D, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (hzero : ∀ z ∈ D, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z = 0)
    {a : ℂ} (ha : a ∈ D) : ∀ᶠ z in 𝓝 a, U z = U a := by
  let e := extChartAt 𝓘(ℝ, E) (U a)
  let V : Set ℂ := D ∩ U ⁻¹' e.source
  let F : ℂ → E := e ∘ U
  have hV : IsOpen V :=
    hD.inter ((isOpen_extChartAt_source (I := 𝓘(ℝ, E)) (U a)).preimage hU)
  have haV : a ∈ V := ⟨ha, mem_extChartAt_source (U a)⟩
  have he (z : ℂ) (hz : z ∈ V) :
      MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e (U z) := by
    apply mdifferentiableAt_extChartAt
    simpa only [e, extChartAt_source, Set.mem_preimage] using hz.2
  have hF : DifferentiableOn ℝ F V := by
    intro z hz
    exact ((he z hz).comp z (hmd z hz.1)).differentiableAt.differentiableWithinAt
  have hFzero : EqOn (fderiv ℝ F) 0 V := by
    intro z hz
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E))
      (I'' := 𝓘(ℝ, E)) z (he z hz) (hmd z hz.1)
    rw [hzero z hz.1, ContinuousLinearMap.comp_zero, mfderiv_eq_fderiv] at hchain
    exact hchain
  have hopen : IsOpen (V ∩ F ⁻¹' ({F a} : Set E)) :=
    hV.isOpen_inter_preimage_of_fderiv_eq_zero hF hFzero {F a}
  have hamem : a ∈ V ∩ F ⁻¹' ({F a} : Set E) := ⟨haV, rfl⟩
  filter_upwards [hopen.mem_nhds hamem] with z hz
  exact e.injOn hz.1.2 haV.2 hz.2

/-- An original Morrey disk spanning a smooth embedded loop has no open germ on which
its differential vanishes. The conclusion concerns the original disk parametrization. -/
theorem IsMorreyDisk.not_eventually_mfderiv_eq_zero [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1) :
    ¬ (∀ᶠ z in 𝓝 a,
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z = 0) := by
  intro hvanish
  let U : ℂ → M := diskExtension u
  let D : Set ℂ := ball (0 : ℂ) 1
  let Z : Set ℂ := {x | ∀ᶠ z in 𝓝 x,
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z = 0}
  have hZ : IsOpen Z := isOpen_setOfPred_eventually_nhds
  have hclosure : closure Z ∩ D ⊆ Z := by
    rintro x ⟨hxZ, hxD⟩
    obtain ⟨R, hR, _, F, hF, hzero⟩ :=
      exists_analytic_factor_with_differential_zero_set hu hxD
    obtain ⟨b, hbZ, hxb⟩ := Metric.mem_closure_iff.mp hxZ R hR
    have hb : b ∈ ball x R := by simpa only [mem_ball, dist_comm] using hxb
    have hFgerm : F =ᶠ[𝓝 b] 0 := by
      filter_upwards [hbZ, isOpen_ball.mem_nhds hb] with z hz hzb
      exact (hzero z hzb).mpr hz
    have hFall : EqOn F 0 (ball x R) :=
      hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_ball hb hFgerm
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with z hz
    exact (hzero z hz).mp (hFall hz)
  have hDZ : D ⊆ Z :=
    isPreconnected_ball.subset_of_closure_inter_subset hZ ⟨a, ha, hvanish⟩ hclosure
  have hzero : ∀ z ∈ D, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z = 0 := by
    intro z hz
    have hgerm : ∀ᶠ w in 𝓝 z,
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U w = 0 := hDZ hz
    exact hgerm.self_of_nhds
  have hU : Continuous U := u.continuous.comp diskRetraction_lipschitz.continuous
  have hmd : ∀ z ∈ D, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z := by
    intro z hz
    exact (hu.smoothInterior.contMDiffAt (isOpen_ball.mem_nhds hz)).mdifferentiableAt
      (by decide)
  have hlocal (z : ℂ) (hz : z ∈ D) : ∀ᶠ w in 𝓝 z, U w = U z :=
    eventually_eq_of_zero_differential_on_open hU isOpen_ball hmd hzero hz
  let C : Set ℂ := {z | z ∈ D ∧ U z = U 0}
  have hC : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    filter_upwards [isOpen_ball.mem_nhds hz.1, hlocal z hz.1] with w hw hweq
    exact ⟨hw, hweq.trans hz.2⟩
  have hCclosure : closure C ∩ D ⊆ C := by
    rintro z ⟨hzC, hzD⟩
    have hsub : closure C ⊆ {z | U z = U 0} :=
      closure_minimal (fun _ hz => hz.2) (isClosed_eq hU continuous_const)
    exact ⟨hzD, hsub hzC⟩
  have h0 : (0 : ℂ) ∈ D := by simp [D]
  have hDC : D ⊆ C :=
    isPreconnected_ball.subset_of_closure_inter_subset hC ⟨0, h0, h0, rfl⟩ hCclosure
  have heq : EqOn U (fun _ => U 0) D := fun _ hz => (hDC hz).2
  have hclosed := heq.closure hU continuous_const
  change EqOn U (fun _ => U 0) (closure (ball (0 : ℂ) 1)) at hclosed
  rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)] at hclosed
  have huconst : u = ContinuousMap.const closedDisk (U 0) := by
    ext z
    exact (diskExtension_coe u z).symm.trans (hclosed z.property)
  exact not_isMorreyDisk_const_of_isSmoothEmbeddedLoop hγ (U 0) (huconst ▸ hu)

end DifferentialGeometry.Geometry
