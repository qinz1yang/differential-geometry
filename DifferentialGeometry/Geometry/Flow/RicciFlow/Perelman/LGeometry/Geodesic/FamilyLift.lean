import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.PhaseFamily
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.FamilyLift
import DifferentialGeometry.Geometry.Curve.VelocityFamily

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open Set Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology
variable {A E F H G X Y : Type*}
 [NormedAddCommGroup A] [NormedSpace ℝ A]
 [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [NormedAddCommGroup F] [NormedSpace ℝ F]
 [TopologicalSpace H] [TopologicalSpace G]
 {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [I.Boundaryless]
 [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
 [TopologicalSpace Y] [ChartedSpace G Y] [IsManifold J ∞ Y]
 {D : RealTimeInterval}

omit [IsManifold J ∞ Y] in
theorem exists_lRegularizedGeodesicFamily_lift_to_time
    (S : SolutionOn (I := I) (M := X) D) (hS : IsSolutionOn S) (T : ℝ)
    (f : X → Y) (hf : IsLocalDiffeomorph I J ∞ f)
    {α : A × ℝ → Y} {V : Set A} {K : Set ℝ} {a0 : A} {s0 b : ℝ}
    (hV : IsOpen V) (hK : IsOpen K) (ha0 : a0 ∈ V) (hs0K : s0 ∈ K)
    (hα : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) J ∞ α (V ×ˢ K))
    {η : ℝ → X} {L : Set ℝ} (hL : IsOpen L) (hLconn : IsPreconnected L)
    (hs0L : s0 ∈ L) (hbL : b ∈ L) (hη : IsLRegularizedGeodesicOn S T η L)
    (hcenter : (fun r => α (a0, r)) =ᶠ[𝓝 s0] f ∘ η) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ C : Set ℝ, IsOpen C ∧ IsPreconnected C ∧ s0 ∈ C ∧ b ∈ C ∧
        ∃ β : A × ℝ → X,
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ β (U ×ˢ C) ∧
          (∀ a ∈ U, f (β (a, s0)) = α (a, s0) ∧
            mfderiv I J f (β (a, s0)) (lVelocity (I := I) (fun r => β (a, r)) s0) =
              lVelocity (I := J) (fun r => α (a, r)) s0 ∧
            IsLRegularizedGeodesicOn S T (fun r => β (a, r)) C) ∧
          EqOn (fun r => β (a0, r)) η (C ∩ L) := by
  have hpoint : α (a0, s0) = f (η s0) := hcenter.self_of_nhds
  obtain ⟨U₀, hU₀, haU₀, hU₀V, ε, hε, hεK, theta, htheta, hproj, htheta0⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_contMDiff_family_lift_near f (hf (η s0)) hV hK ha0 hs0K hα hpoint
  let I₀ := Ioo (s0 - ε) (s0 + ε)
  have hsI : s0 ∈ I₀ := ⟨by linarith, by linarith⟩
  have hthetaD (a : A) (ha : a ∈ U₀) : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun r => theta (a, r)) s0 :=
    (((htheta (a, s0) ⟨ha, hsI⟩).contMDiffAt ((hU₀.prod isOpen_Ioo).mem_nhds ⟨ha, hsI⟩)).comp s0
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hphase (a : A) (ha : a ∈ U₀) :
      mfderiv I J f (theta (a, s0)) (lVelocity (I := I) (fun r => theta (a, r)) s0) =
        lVelocity (I := J) (fun r => α (a, r)) s0 := by
    have hgerm : f ∘ (fun r => theta (a, r)) =ᶠ[𝓝 s0] (fun r => α (a, r)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hsI] with r hr
      exact hproj ⟨ha, hr⟩
    unfold lVelocity
    rw [← hgerm.mfderiv_eq, mfderiv_comp s0 ((hf _).contMDiffAt.mdifferentiableAt (by simp)) (hthetaD a ha)]
    rfl
  let ζ : A → TangentBundle I X := fun a => ⟨theta (a, s0), lVelocity (I := I) (fun r => theta (a, r)) s0⟩
  have hζ : ContMDiffOn 𝓘(ℝ, A) I.tangent ∞ ζ U₀ :=
    (DifferentialGeometry.Geometry.contMDiffOn_curve_velocity_family hU₀ isOpen_Ioo htheta).comp
      (contMDiffOn_id.prodMk contMDiffOn_const) (fun a ha => ⟨ha, hsI⟩)
  have hvel : lVelocity (I := I) η s0 = (ζ a0).2 := by
    have hm := hphase a0 haU₀
    have heq : lVelocity (I := J) (fun r => α (a0, r)) s0 =
        mfderiv I J f (η s0) (lVelocity (I := I) η s0) := by
      unfold lVelocity
      rw [hcenter.mfderiv_eq, mfderiv_comp s0 ((hf _).contMDiffAt.mdifferentiableAt (by simp)) (hη s0 hs0L).2.1]
      rfl
    rw [heq, htheta0] at hm
    exact (((hf (η s0)).mfderivToContinuousLinearEquiv (by simp)).injective hm).symm
  obtain ⟨U, hU, haU, hUU₀, C, hC, hCconn, hsC, hbC, β, hβ, hcurves, hcenterβ⟩ :=
    exists_lRegularizedGeodesicFamily_to_time_of_smooth_phase S hS T hU₀ haU₀ ζ hζ hL hLconn
      hs0L hbL htheta0.symm hvel hη
  refine ⟨U, hU, haU, hUU₀.trans hU₀V, C, hC, hCconn, hsC, hbC, β, hβ, ?_, hcenterβ⟩
  intro a ha
  obtain ⟨hpointβ, hvelocityβ, hgeodesicβ⟩ := hcurves a ha
  refine ⟨?_, ?_, hgeodesicβ⟩
  · exact (congrArg f hpointβ).trans (hproj ⟨hUU₀ ha, hsI⟩)
  · rw [hpointβ, hvelocityβ]
    exact hphase a (hUU₀ ha)

end DifferentialGeometry.PDE.RicciFlow.Perelman
