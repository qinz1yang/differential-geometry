import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedDefs
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Existence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ProfileConfinement

/-!
# S-MIRRORS G3 (`_HC2`): real `IsMorreyDisk.profile_confinement`, no placeholder

Replaces the placeholder mirror `IsMorreyDisk.profile_confinement_P2A` of
`P2AdapterImportedLemmas.lean` by the IMS03 theorem
`DifferentialGeometry.Geometry.IsMorreyDisk.profile_confinement`
(`Geometry/MinimalSurface/Plateau/ProfileConfinement.lean`, copied verbatim from branch
`gc/juihuichung/ims03-astra-20261005`, tip `f49e541fb`, with its 23 IMS03-only import
dependencies).  The statement is literally that of the mirror, with the metric
`profileMetric_P2A` and barrier `barrier_P2A` of `P2AdapterImportedDefs`; the real theorem closes it
because these are verbatim copies of the real `profileMetric` and `barrier` (definitional
unfolding).
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

section ProfileConfinement
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- Statement of the mirror `IsMorreyDisk.profile_confinement_P2A`, proved by the real IMS03
theorem `IsMorreyDisk.profile_confinement`. -/
theorem IsMorreyDisk.profile_confinement_P2A_HC2
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hρa : ∀ x, ρ x < a)
    (hbase : ∀ x : M, 0 < ρ x → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      0 ≤ hessFun g ρ x v v)
    (hcontact : ∀ x : M, ρ x = 0 → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      v ≠ 0 → 0 < hessFun g ρ x v v)
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk (profileMetric_P2A g a ha ρ hρ hρa) γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hboundary : ∀ θ : loopCircle, ρ (γ θ) ≤ 0) :
    (∀ z : closedDisk, ρ (u z) ≤ 0) ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ (u z) < 0) ∧
      ∀ z : closedDisk, ∀ᶠ y in 𝓝 (u z),
        (profileMetric_P2A g a ha ρ hρ hρa).inner y = g.inner y ∧
          barrier_P2A a (ρ y) = ρ y :=
  DifferentialGeometry.Geometry.IsMorreyDisk.profile_confinement
    g a ha ρ hρ hρa hbase hcontact hu hγ hboundary

/-- Consumer of G3: a Morrey disk of the profile metric lies in the sublevel `{ρ ≤ 0}`. -/
theorem IsMorreyDisk.range_le_of_profile_P2A_HC2
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hρa : ∀ x, ρ x < a)
    (hbase : ∀ x : M, 0 < ρ x → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      0 ≤ hessFun g ρ x v v)
    (hcontact : ∀ x : M, ρ x = 0 → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      v ≠ 0 → 0 < hessFun g ρ x v v)
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk (profileMetric_P2A g a ha ρ hρ hρa) γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hboundary : ∀ θ : loopCircle, ρ (γ θ) ≤ 0) :
    range u ⊆ {x | ρ x ≤ 0} := by
  rintro _ ⟨z, rfl⟩
  exact (IsMorreyDisk.profile_confinement_P2A_HC2 g a ha ρ hρ hρa hbase hcontact hu hγ
    hboundary).1 z

end ProfileConfinement

end GC.LongTime.CuspP1
