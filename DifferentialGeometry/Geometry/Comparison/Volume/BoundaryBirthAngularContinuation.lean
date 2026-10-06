import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthIntervalFlow
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseJacobiLinearFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryJointJacobiFrame

/-!
A compact time tube extends the actual common birth seeds and their angular derivatives.
The maximal flow agrees on a velocity neighborhood, so its literal angular differential agrees.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {N : Type*} [nativeTopology : TopologicalSpace N]
  [nativeCharts : ChartedSpace E N] [nativeSmooth : IsManifold 𝓘(ℝ, E) ∞ N]
  [nativeT2 : T2Space N]

theorem boundaryBirth_angular_continuation (g : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    (V : Opens (E × ℝ)) (ρ : E × ℝ → N)
    (hρ : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V)
    (hgeo : ∀ q ∈ V, HasGeodesicEquationAt g (fun r => ρ (q.1, r)) q.2)
    (σ : E → TangentBundle 𝓘(ℝ, E) N) (W : Opens E) {v : E} (hv : v ∈ W)
    {a δ : ℝ} (ha : a ∈ Ioo 0 δ)
    (hbirth : ∀ r ∈ Ioo 0 δ, (v, r) ∈ V)
    (hseed : ∀ u ∈ W, σ u = DifferentialGeometry.velocityLift
      (I := 𝓘(ℝ, E)) (fun r => ρ (u, r)) a) :
    ∀ t ∈ Ioo 0 δ, (σ v, t - a) ∈ g.geodesicFlowDomain ∧
      boundaryPhasePoint g σ v (t - a) = ρ (v, t) ∧
      ∀ w : E, (boundaryPhaseJacobiLinear g σ v (t - a) w : E) =
        boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ v t w := by
  intro t ht
  let b := min a t / 2
  let c := (max a t + δ) / 2
  have hm : 0 < min a t := lt_min ha.1 ht.1
  have hM : max a t < δ := max_lt ha.2 ht.2
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : b < a := by dsimp [b]; linarith [min_le_left a t]
  have hbt : b < t := by dsimp [b]; linarith [min_le_right a t]
  have hac : a < c := by dsimp [c]; linarith [le_max_left a t]
  have htc : t < c := by dsimp [c]; linarith [le_max_right a t]
  have hc : c < δ := by dsimp [c]; linarith
  have htube : ({v} : Set E) ×ˢ Icc b c ⊆ V := by
    rintro ⟨u, r⟩ ⟨hu, hr⟩
    have hu' : u = v := mem_singleton_iff.mp hu
    subst u
    exact hbirth r ⟨lt_of_lt_of_le hb hr.1, lt_of_le_of_lt hr.2 hc⟩
  obtain ⟨A, B, hA, _hB, hvA, hK, hAB⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc V.isOpen htube
  let L : Opens E := ⟨A ∩ W, hA.inter W.isOpen⟩
  have hvL : v ∈ L := ⟨hvA (mem_singleton v), hv⟩
  have hinterval (u : E) (hu : u ∈ L) (r : ℝ) (hr : r ∈ Ioo b c) : (u, r) ∈ V :=
    hAB ⟨hu.1, hK ⟨hr.1.le, hr.2.le⟩⟩
  have hmatch (u : E) (hu : u ∈ L) : (σ u, t - a) ∈ g.geodesicFlowDomain ∧
      boundaryPhasePoint g σ u (t - a) = ρ (u, t) := by
    have hcurve : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun r => ρ (u, r)) (Ioo b c) := by
      intro r hr
      exact ((hρ.contMDiffAt (V.isOpen.mem_nhds (hinterval u hu r hr))).comp r
        (contMDiffAt_const.prodMk contMDiffAt_id)).contMDiffWithinAt
    have hflow := boundaryBirth_interval_flow g ⟨hba, hac⟩
      (fun r hr => hgeo (u, r) (hinterval u hu r hr)) hcurve.continuousOn t ⟨hbt, htc⟩
    rw [← hseed u hu.2] at hflow
    refine ⟨hflow.1, ?_⟩
    exact congrArg (fun x : TangentBundle 𝓘(ℝ, E) N => x.proj) hflow.2
  refine ⟨(hmatch v hvL).1, (hmatch v hvL).2, ?_⟩
  have heq : (fun u => boundaryPhasePoint g σ u (t - a)) =ᶠ[𝓝 v]
      (fun u => ρ (u, t)) :=
    eventually_of_mem (L.isOpen.mem_nhds hvL) (fun u hu => (hmatch u hu).2)
  intro w
  exact congrArg (fun A : E →L[ℝ] E => A w)
    (heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
