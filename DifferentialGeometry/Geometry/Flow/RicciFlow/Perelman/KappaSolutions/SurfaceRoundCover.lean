import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.Basic
import DifferentialGeometry.Geometry.Comparison.SurfaceCurvatureDecay
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Sphere.FreeOrthogonalAction
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.Representation
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.PositiveSpaceForm
import DifferentialGeometry.Topology.Covering.DeckDiffeomorph

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance upstreamSurfaceCoverSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

local instance upstreamSurfaceCoverC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

theorem complete_surface_constant_scalar_round_cover
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hscalar : ∀ x : M, metricScalarAt (I := I) g x = sigma) :
    ∃ pi : SphereTwo → M,
      IsLocalDiffeomorph (𝓡 2) I ∞ pi ∧ IsCoveringMap pi ∧ Function.Surjective pi ∧
      (∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
        g.inner (pi x) (mfderiv (𝓡 2) I pi x v) (mfderiv (𝓡 2) I pi x w) =
          (2 / sigma) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w) ∧
      (Function.Injective pi ∨
        ∀ x y : SphereTwo, pi x = pi y ↔ y = x ∨ y = -x) := by
  have hsec : ∀ x : M, ∀ v w : TangentSpace I x,
      metricRm04StandardAt (I := I) (M := M) g x v w w v =
        (sigma / 2) * (g.inner x v v * g.inner x w w -
          g.inner x v w * g.inner x v w) := by
    intro x v w
    rw [metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two (I := I) g hdim x v w w v,
      hscalar x, g.symm x w v]
  have hcompact : CompactSpace M :=
    Riemannian.compactSpace_of_metricScalarAt_lower_bound_of_finrank_eq_two
      (I := I) g hcomplete hdim hsigma fun x => (hscalar x).ge
  obtain ⟨cover, hlocal, hquotient, hmetric⟩ :=
    exists_round_two_sphere_quotient_cover_of_constant_positive_sectional_curvature
      (I := I) (M := M) hcompact inferInstance inferInstance hdim g
      (sigma / 2) (by positivity) hsec
  have hmetricG : ∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
      g.inner (cover x) (mfderiv (𝓡 2) I cover x v)
          (mfderiv (𝓡 2) I cover x w) =
        (2 / sigma) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
          x v w := by
    intro x v w
    have h := hmetric x v w
    rw [scaleMetric_inner] at h
    have htwo : (2 / sigma) * (sigma / 2) = 1 := by field_simp
    calc g.inner (cover x) (mfderiv (𝓡 2) I cover x v)
          (mfderiv (𝓡 2) I cover x w)
        = (2 / sigma) * ((sigma / 2) * g.inner (cover x)
            (mfderiv (𝓡 2) I cover x v) (mfderiv (𝓡 2) I cover x w)) := by
          rw [← mul_assoc, htwo, one_mul]
      _ = (2 / sigma) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w := by rw [h]
  have hmetricR : ∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w =
        (sigma / 2) * g.inner (cover x) (mfderiv (𝓡 2) I cover x v)
          (mfderiv (𝓡 2) I cover x w) := by
    intro x v w
    have h := hmetricG x v w
    have htwo : (sigma / 2) * (2 / sigma) = 1 := by field_simp
    calc (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w
        = (sigma / 2) * ((2 / sigma) *
            (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w) := by
          rw [← mul_assoc, htwo, one_mul]
      _ = (sigma / 2) * g.inner (cover x) (mfderiv (𝓡 2) I cover x v)
            (mfderiv (𝓡 2) I cover x w) := by rw [← h]
  let phi : coveringDeckGroup cover → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo :=
    fun gamma => coveringDeckGroupDiffeomorph hlocal gamma
  have hphiOne : ∀ x : SphereTwo, phi 1 x = x := by
    intro x
    rfl
  have hphiMul : ∀ (gamma delta : coveringDeckGroup cover) (x : SphereTwo),
      phi (gamma * delta) x = phi gamma (phi delta x) := by
    intro gamma delta x
    rfl
  have hphiMap (gamma : coveringDeckGroup cover) (x : SphereTwo) :
      cover (phi gamma x) = cover x :=
    coveringDeckGroup_map gamma x
  have hphiDeriv (gamma : coveringDeckGroup cover) (x : SphereTwo) :
      mfderiv (𝓡 2) I cover (phi gamma x) ∘L
          mfderiv (𝓡 2) (𝓡 2) (phi gamma : SphereTwo → SphereTwo) x =
        mfderiv (𝓡 2) I cover x := by
    have hcomp : cover ∘ (phi gamma : SphereTwo → SphereTwo) = cover := by
      funext z
      exact hphiMap gamma z
    have h' := mfderiv_comp x (hlocal.contMDiff.mdifferentiableAt (by simp))
      ((phi gamma).contMDiff.mdifferentiableAt (by simp))
    rw [hcomp] at h'
    exact h'.symm
  have hphiMetric (gamma : coveringDeckGroup cover) :
      Diffeomorph.pullbackMetricCross
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) (phi gamma) =
        roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner,
      hmetricR (phi gamma x) (mfderiv (𝓡 2) (𝓡 2) (phi gamma) x v)
        (mfderiv (𝓡 2) (𝓡 2) (phi gamma) x w),
      hmetricR x v w]
    congr 1
    have hv := congrArg
      (fun L : TangentSpace (𝓡 2) x →L[ℝ] TangentSpace I (cover (phi gamma x)) => L v)
      (hphiDeriv gamma x)
    have hw := congrArg
      (fun L : TangentSpace (𝓡 2) x →L[ℝ] TangentSpace I (cover (phi gamma x)) => L w)
      (hphiDeriv gamma x)
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    rw [hv, hw, hphiMap gamma x]
  have hphiIso (gamma : coveringDeckGroup cover) (x : SphereTwo)
      (v w : TangentSpace (𝓡 2) x) :
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w =
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner (phi gamma x)
          (mfderiv (𝓡 2) (𝓡 2) (phi gamma) x v)
          (mfderiv (𝓡 2) (𝓡 2) (phi gamma) x w) := by
    have h := Diffeomorph.pullbackMetricCross_inner
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) (phi gamma) x v w
    rw [hphiMetric gamma] at h
    exact h
  obtain ⟨rho, hrho⟩ := orth_rep_of_iso (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
    phi (by norm_num) hphiOne hphiMul hphiIso
  have hfree : ∀ (gamma : coveringDeckGroup cover) (x : SphereTwo),
      phi gamma x = x → gamma = 1 := by
    let _ : PreconnectedSpace SphereTwo :=
      Subtype.preconnectedSpace
        (isPreconnected_sphere
          (Module.one_lt_rank_of_one_lt_finrank (by norm_num))
          (0 : EuclideanSpace ℝ (Fin 3)) 1)
    intro gamma x hx
    exact coveringDeckGroup_eq_one_of_apply_eq hquotient.isCoveringMap gamma x hx
  have hfreeRho : ∀ (gamma : coveringDeckGroup cover) (x : SphereTwo),
      sphereDiffeo (n := 2) (rho gamma) x = x → gamma = 1 := by
    intro gamma x hx
    exact hfree gamma x (by rw [← hrho gamma]; exact hx)
  have hdich : ∀ gamma : coveringDeckGroup cover,
      (∀ x : SphereTwo, phi gamma x = x) ∨
        ∀ x : SphereTwo, phi gamma x = -x := by
    intro gamma
    rcases orth_rep_apply_eq_one_or_neg_of_free_sphere_action rho hfreeRho gamma with
      h1 | hneg
    · left
      intro x
      rw [← hrho gamma, h1]
      exact Subtype.ext (by simp [sphereDiffeo_coe])
    · right
      intro x
      rw [← hrho gamma, hneg]
      exact Subtype.ext (by simp [sphereDiffeo_coe])
  have hfib : Function.Injective cover ∨
      ∀ x y : SphereTwo, cover x = cover y ↔ y = x ∨ y = -x := by
    by_cases hanti : ∃ gamma : coveringDeckGroup cover,
        ∀ x : SphereTwo, phi gamma x = -x
    · right
      intro x y
      constructor
      · intro hxy
        obtain ⟨gamma, hgamma⟩ := hquotient.apply_eq_iff_mem_orbit.mp hxy
        rcases hdich gamma with hfix | hneg
        · left
          have hxy' : x = y := by
            rw [← hgamma]
            exact hfix y
          exact hxy'.symm
        · right
          have hxy' : x = -y := by
            rw [← hgamma]
            exact hneg y
          rw [hxy']
          simp
      · rintro (hyx | hyneg)
        · rw [hyx]
        · obtain ⟨gamma, hgamma⟩ := hanti
          have hx : x = -y := by rw [hyneg]; simp
          rw [hx, ← hgamma]
          simpa using hphiMap gamma y
    · left
      intro x y hxy
      obtain ⟨gamma, hgamma⟩ := hquotient.apply_eq_iff_mem_orbit.mp hxy
      rcases hdich gamma with hfix | hneg
      · rw [← hgamma]
        exact hfix y
      · exact (hanti ⟨gamma, hneg⟩).elim
  exact ⟨cover, hlocal, hquotient.isCoveringMap, hquotient.surjective, hmetricG, hfib⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
