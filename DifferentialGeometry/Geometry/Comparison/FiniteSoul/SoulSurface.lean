import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulStrictOutward
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveMaximalSet
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulPlaneCylinder

/-!
# S-SOUL2 and S6: the finite surface soul and the plane / cylinder theorem

Frozen interfaces of the finite soul package (`build-logs/scratch/D-CMS/FiniteSoulInterfaces.lean`):
* **S-SOUL2** `exists_finite_soul_strict_outward_dim_two`: a complete connected noncompact surface
  with a metric of class `C^{r+1}`, `r ≥ 3`, and `sec ≥ 0` has a soul `S` — a point or a simple closed
  unit geodesic, compact and totally convex — with strict outward unit vectors at every point
  outside `S` against every minimizing direction to `S` (LFR45.1 in dimension two).
* **S6** `nonempty_homeomorph_plane_or_cylinder_finite`: if moreover the surface is oriented, it is
  HOMEOMORPHIC to `ℝ²` or to `S¹ × ℝ` (disposition D7: a homeomorphism statement only; no
  differentiability of the identification is claimed).

Construction (design §3, review §3): `f = rayExhaustion o`, `C₀ = {f ≤ 0}` (compact, totally
convex). If `int C₀ = ∅`, the soul is found in `C₀` (S-SHAPE2: point, closed geodesic, or the
midpoint of an arc). Otherwise `∂C₀ ≠ ∅` (`M` is connected and noncompact) and CMS-B's shaving
gives `C₁ = argmax_{C₀} d(·, ∂C₀)` (compact, totally convex, empty interior), where the soul is
found. Strict outward vectors: `SoulStrictOutward.lean`. S6 is CMS-T's gluing
(`nonempty_homeomorph_plane_or_cylinder_of_soul`) applied to this soul.

Deviations (strengthenings): the instance arguments `[NeZero (finrank ℝ E)]` and
`[SigmaCompactSpace M]` of the interface block are not assumed (they follow from `hdim` and from
properness); the verbatim forms are kept as `example`s in `SoulSurfaceConsumers.lean`.
LFR21 stays PARTIAL (disposition D1): the non-orientable case and the normal-bundle form
`∃ S, ∃ e : ν_g S ≃ₜ M, ∀ s, e (s, 0) = s` are not delivered here.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology (rayExhaustion rayExhaustion_self)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **S-SOUL2 (frozen interface).** The finite surface soul with strict outward directions. -/
theorem exists_finite_soul_strict_outward_dim_two [NoncompactSpace M] [ConnectedSpace M]
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
        ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0 := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  obtain ⟨o⟩ : Nonempty M := inferInstance
  obtain ⟨hC₀c, hC₀conv⟩ := isCompact_isTotallyConvexFinite_rayExhaustion_sublevel g hr2 hnorm hsec o 0
  have hne : ({x : M | rayExhaustion o x ≤ 0} : Set M).Nonempty :=
    ⟨o, by change rayExhaustion o o ≤ 0; rw [rayExhaustion_self]⟩
  by_cases hint : interior {x : M | rayExhaustion o x ≤ 0} = ∅
  · exact exists_soul_of_layer_dim_two g hr2 hnorm hsec hdim o hC₀c hne hC₀conv hint subset_rfl
      fun _ _ _ _ q hq hq' => absurd hq hq'
  · have hB : (frontier {x : M | rayExhaustion o x ≤ 0}).Nonempty :=
      nonempty_frontier_iff.2 ⟨hne, fun h => noncompact_univ M (h ▸ hC₀c)⟩
    obtain ⟨hAc, hAne, hAconv, hAC, hAint⟩ :=
      isCompact_isTotallyConvexFinite_argmax_infDist_frontier g hr hnorm hsec hdim hC₀c hne
        hC₀conv hB
    exact exists_soul_of_layer_dim_two g hr2 hnorm hsec hdim o hAc hAne hAconv hAint hAC
      fun S hS hScl hSne q hq hq' => exists_unit_strict_outward_middle_layer g hr hnorm hsec hdim
        hC₀c.isClosed hC₀conv hS hScl hSne hq hq'

/-- **S6 (frozen interface; LFR21's orientable output, a HOMEOMORPHISM).** A complete connected
noncompact oriented surface with a metric of class `C^{r+1}`, `r ≥ 3`, and `sec ≥ 0` is homeomorphic
to `ℝ²` or to `S¹ × ℝ`. -/
theorem nonempty_homeomorph_plane_or_cylinder_finite [NoncompactSpace M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) (o : DifferentialGeometry.ManifoldOrientation I M 2) :
    Nonempty (M ≃ₜ EuclideanSpace ℝ (Fin 2)) ∨ Nonempty (M ≃ₜ AddCircle (1 : ℝ) × ℝ) := by
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  obtain ⟨S, -, -, -, hshape, hout⟩ := exists_finite_soul_strict_outward_dim_two g hr hnorm hsec hdim
  exact nonempty_homeomorph_plane_or_cylinder_of_soul g (le_trans (by norm_num) hr) hnorm hdim o
    hshape hout

end DifferentialGeometry.Geometry.FiniteSoul
