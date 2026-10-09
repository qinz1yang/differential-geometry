import DifferentialGeometry.Geometry.Geodesic.Ray
import DifferentialGeometry.Geometry.Comparison.HopfRinow.GeodesicSpeedBound

set_option autoImplicit false

/-!
# CH12-S92 / G1: complete unit-speed geodesics with the distance bound `d(p, Γ s) ≤ s`

For a complete smooth Riemannian metric `g`, every unit vector at `p` is the initial velocity of a
global `C^∞` geodesic `Γ` with unit speed, and `riemannianEDistOf g p (Γ s) ≤ s` for `s ≥ 0`.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff ENNReal NNReal Manifold Topology
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace GC.LongTime.Ch12

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]

omit [T2Space (TangentBundle I M)] [ConnectedSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_complete_unit_geodesic_S92
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) (v : TangentSpace I p) (hv : g.inner p v v = 1) :
    ∃ Γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ Γ ∧ IsGeodesic (I := I) g Γ ∧ Γ 0 = p ∧
      (mfderiv 𝓘(ℝ, ℝ) I Γ 0 (1 : ℝ) : E) = (v : E) ∧
      ∀ s : ℝ, 0 ≤ s → riemannianEDistOf (I := I) g p (Γ s) ≤ ENNReal.ofReal s := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := (∞ : ℕ∞ω))
    (by decide : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun x v ↦ tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  obtain ⟨Γ, hgeo, hΓ0, hΓv, hΓcont⟩ :=
    exists_complete_geodesic_at_velocity (I := I) g hEnorm p v
  have hat : ∀ t, IsGeodesicAt (I := I) g Γ t := fun t =>
    isGeodesicAt_of_isGeodesicOn g (U := univ) univ_mem (fun s _ => hgeo s) hΓcont.continuousOn
  have hsm : ContMDiff 𝓘(ℝ, ℝ) I ∞ Γ := fun t => contMDiffAt_of_isGeodesicAt (hat t)
  have hsm1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 Γ univ :=
    (hsm.of_le (by exact_mod_cast le_top)).contMDiffOn
  subst hΓ0
  have hv0 : mfderiv 𝓘(ℝ, ℝ) I Γ 0 1 = v := hΓv
  have hspeed : ∀ t, g.inner (Γ t) (mfderiv 𝓘(ℝ, ℝ) I Γ t 1) (mfderiv 𝓘(ℝ, ℝ) I Γ t 1) = 1 := by
    intro t
    have h := isGeodesicOn_speedSq_const (I := I) g (γ := Γ) (s := univ) (t₀ := 0) (t₁ := t)
      isOpen_univ (fun s _ => hgeo s) hsm1 (subset_univ _)
    refine h.symm.trans ?_
    have h0 : g.inner (Γ 0) (mfderiv 𝓘(ℝ, ℝ) I Γ 0 1) (mfderiv 𝓘(ℝ, ℝ) I Γ 0 1) = 1 := by
      rw [hv0]; exact hv
    exact h0
  refine ⟨Γ, hsm, hgeo, rfl, hΓv, fun s hs => ?_⟩
  rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
  have h := curve_edist_le_speed_mul_time (I := I) (γ := Γ) (s := 0) (t := s) (c := 1)
    zero_le_one hs (hsm1.mono (subset_univ _)) (fun τ _ => by
      rw [hEnorm]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : g.inner (Γ τ) (mfderiv 𝓘(ℝ, ℝ) I Γ τ (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I Γ τ (1 : ℝ)) = 1 :=
        hspeed τ
      rw [h1]; simp)
  simpa using h

end GC.LongTime.Ch12
