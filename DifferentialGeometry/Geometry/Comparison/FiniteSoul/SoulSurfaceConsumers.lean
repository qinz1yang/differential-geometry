import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulSurface
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulNormalLineBundle

/-!
# Consumers of S-SOUL2 / S6: verbatim interfaces, the unoriented type, LFR21's output in model form

* the frozen interface texts of S-SOUL2 and S6 (with the interface block's instance arguments
  `[NeZero (finrank ℝ E)] [SigmaCompactSpace M]`), as `example`s;
* `nonempty_homeomorph_plane_or_normalLineBundle_finite`: WITHOUT orientation, the surface is
  homeomorphic to `ℝ²` or to a normal line bundle `NormalLineBundle σ` over the circle
  (`σ = 1`: the cylinder; `σ = -1`: the open Möbius band) — CMS-T's C5 applied to S-SOUL2;
* `exists_soul_normal_homeomorph_finite` (LFR21, model form): the soul `S` (a point `x`, or a
  simple closed unit geodesic of least period `ℓ` with its unit normal `ν`, `ν (t + ℓ) = σ ν t`) and
  a HOMEOMORPHISM from the normal bundle model (`T_x M`, resp. `NormalLineBundle σ`) onto `M`
  fixing `S` (`0 ↦ x`, resp. `[t, 0] ↦ γ (ℓ t)`) and calibrated by `d_S`. No differentiability of
  the homeomorphism is claimed (LFR21's own wording; disposition D7).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- S-SOUL2, verbatim frozen interface text (with the interface block's instance arguments). -/
example [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [NoncompactSpace M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvexFinite g S ∧
      ((∃ x, S = {x}) ∨
        ∃ (p : TangentBundle I M) (ℓ : ℝ), 0 < ℓ ∧ g.inner p.proj p.snd p.snd = 1 ∧
          g.geodesicFlow p ℓ = p ∧ InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ) ∧
          S = range (fun t => (g.geodesicFlow p t).proj)) ∧
      ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
        ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0 :=
  exists_finite_soul_strict_outward_dim_two g hr hnorm hsec hdim

/-- S6, verbatim frozen interface text (with the interface block's instance arguments). -/
example [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [NoncompactSpace M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) (o : DifferentialGeometry.ManifoldOrientation I M 2) :
    Nonempty (M ≃ₜ EuclideanSpace ℝ (Fin 2)) ∨ Nonempty (M ≃ₜ AddCircle (1 : ℝ) × ℝ) :=
  nonempty_homeomorph_plane_or_cylinder_finite g hr hnorm hsec hdim o

/-- **S6 without orientation.** A complete connected noncompact surface with a metric of class
`C^{r+1}`, `r ≥ 3`, and `sec ≥ 0` is homeomorphic to `ℝ²` or to a normal line bundle over the circle
(the cylinder for `σ = 1`, the open Möbius band for `σ = -1`). -/
theorem nonempty_homeomorph_plane_or_normalLineBundle_finite [NoncompactSpace M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) :
    Nonempty (M ≃ₜ EuclideanSpace ℝ (Fin 2)) ∨ ∃ σ : ℤˣ, Nonempty (M ≃ₜ NormalLineBundle σ) := by
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  obtain ⟨S, -, -, -, hshape, hout⟩ := exists_finite_soul_strict_outward_dim_two g hr hnorm hsec hdim
  exact nonempty_homeomorph_plane_or_normalLineBundle_of_soul g (le_trans (by norm_num) hr) hnorm
    hdim hshape hout

/-- **LFR21 (model form).** A complete connected noncompact surface with a metric of class
`C^{r+1}`, `r ≥ 3` (the blueprint's `m = r + 1 ≥ 4`), and `sec ≥ 0` has a compact, totally convex
soul `S` — a point `x`, or a simple closed unit geodesic of least period `ℓ` (connected, without
boundary, totally geodesic: `ClosedGeodesicSubmanifold.lean`) — and a HOMEOMORPHISM from the normal
bundle model onto `M` fixing `S`: `T_x M ≃ₜ M` with `0 ↦ x`, resp.
`NormalLineBundle σ ≃ₜ M` with `[t, 0] ↦ γ (ℓ t)`, where the unit normal satisfies
`ν (t + ℓ) = σ ν t`. Both maps are calibrated by `d_S`. -/
theorem exists_soul_normal_homeomorph_finite [NoncompactSpace M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvexFinite g S ∧
      ((∃ x, S = {x} ∧ ∃ F : E ≃ₜ M, F 0 = x ∧
          ∀ v, infDist (F v) S = Real.sqrt (g.inner x v v)) ∨
        ∃ (p : TangentBundle I M) (ℓ : ℝ), 0 < ℓ ∧ g.inner p.proj p.snd p.snd = 1 ∧
          g.geodesicFlow p ℓ = p ∧ InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ) ∧
          S = range (fun t => (g.geodesicFlow p t).proj) ∧
          ∃ ν : ℝ → E,
            Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)) ∧
            (∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1) ∧
            (∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0) ∧
            ∃ σ : ℤˣ, (∀ t, ν (t + ℓ) = ((σ : ℤ) : ℝ) • ν t) ∧
              ∃ F : NormalLineBundle σ ≃ₜ M,
                (∀ t, F (NormalLineBundle.mk σ t 0) = (g.geodesicFlow p (ℓ * t)).proj) ∧
                ∀ q, infDist (F q) S = NormalLineBundle.fiberAbs σ q) := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  obtain ⟨S, hSne, hSc, hSconv, hshape, hout⟩ :=
    exists_finite_soul_strict_outward_dim_two g hr hnorm hsec hdim
  refine ⟨S, hSne, hSc, hSconv, ?_⟩
  rcases hshape with ⟨x, rfl⟩ | ⟨p, ℓ, hℓ, hunit, hper, hinj, rfl⟩
  · obtain ⟨F, hF, -⟩ := exists_homeomorph_tangentSpace_exp_of_point_soul g hr2 hnorm x hout
    refine Or.inl ⟨x, rfl, F, ?_, hF⟩
    have h0 := hF 0
    have hz : g.inner x (0 : E) (0 : E) = 0 := by
      have := inner_smul_smul_self_finite g x 0 (0 : E)
      rw [zero_smul, zero_pow two_ne_zero, zero_mul] at this
      exact this
    rw [hz, Real.sqrt_zero, infDist_singleton] at h0
    exact dist_eq_zero.1 h0
  · obtain ⟨ν, hν, hνunit, hνperp, σ, hσ, F, hFd, hF0, -⟩ :=
      exists_homeomorph_normalLineBundle_of_closedGeodesic_soul g hr2 hnorm hdim p hℓ hunit hper hinj
        hout
    exact Or.inr ⟨p, ℓ, hℓ, hunit, hper, hinj, rfl, ν, hν, hνunit, hνperp, σ, hσ, F, hF0, hFd⟩

end DifferentialGeometry.Geometry.FiniteSoul
