import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedDefs
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Existence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity
import DifferentialGeometry.Geometry.Metric.Completeness.PseudoEMetric

/-!
# P2A-24 (imported, EXPLICIT SORRY): mirrors of IMS03 declarations already proved on the other branch

User exception (BRIEF-CP1.md, 2026-10-06): every `sorry` in this file is a verbatim signature mirror
of a declaration of branch `gc/juihuichung/ims03-astra-20261005` (scanned tip `981d9a8cd`,
descendant of `dcf465959`).  Status of all three: **proved on the IMS03 branch** (no `sorry` token in
the source file; transitive closure not audited by us).  Replacement plan for all: after the IMS03
branch is merged, delete the mirror and refer to the original declaration directly.
Register: `docs/geometrization/chapter15/p2-adapter-sorries.md`.  Nothing outside
`CuspP1/P2AdapterImported*.lean` may import this file.
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

universe u

/-- MIRROR (sorry).  Source: `DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/CuspExteriorConvexity.lean:399`
(`GC.LongTime.PersistentCuspExterior.exists_eventual_convex_profiles`), IMS03 @ 981d9a8cd
(ancestor `dcf465959`).  Their status: PROVED.  Replacement: after merge, use the original.
Signature is verbatim except the name suffix `_P2A`. -/
theorem _root_.GC.LongTime.PersistentCuspExterior.exists_eventual_convex_profiles_P2A
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ}
    (C : PersistentHyperbolicCores F K) (E : PersistentCuspExterior C) (tmin : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∃ T : ℝ, ∃ hstart : E.start ≤ T,
      tmin ≤ T ∧ 1 ≤ T ∧ ∀ (t : ℝ) (ht : T ≤ t),
        ∃ ρ : (postStage F.observation t).Carrier → ℝ,
          ContMDiff (𝓡 3) 𝓘(ℝ) ∞ ρ ∧
          E.region t = {x | ρ x ≤ 0} ∧
          IsCompact (closure {x | ρ x < a}) ∧
          (∀ (i : Fin C.count) (j : Fin (E.truncation i).count) (s : Torus),
            ρ (C.map i t (E.after_cores.trans (hstart.trans ht))
              ((E.truncation i).cuspMap j (s, halfZero))) = 0) ∧
          ∀ x, 0 ≤ ρ x → ρ x < a →
            mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
            ∀ V : TangentSpace (𝓡 3) x, V ≠ 0 →
              0 < hessFun (postMetric F.observation t) ρ x V V := by
  sorry

section PositiveDomain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SecondCountableTopology M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- MIRROR (sorry).  Source: `DifferentialGeometry/Geometry/Metric/Conformal/PositiveDomain.lean:77`
(`DifferentialGeometry.Geometry.Metric.canonicalPositiveDomainMetric_complete_homogeneous`),
IMS03 @ 981d9a8cd.  Their status: PROVED.  The metric is our verbatim copy
`canonicalPositiveDomainMetric_P2A` (Defs file).  Replacement: after merge, use the original. -/
theorem canonicalPositiveDomainMetric_complete_homogeneous_P2A
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {δ : M → ℝ}
    (hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ)
    (U : TopologicalSpace.Opens M) (hU : ∀ x : M, x ∈ U ↔ 0 < δ x)
    (hK : IsCompact (closure (U : Set M))) (hdim : Module.finrank ℝ E = 3) :
    let : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace 𝓘(ℝ, E) M
    DifferentialGeometry.Geometry.RiemannianMetricComplete
        (canonicalPositiveDomainMetric_P2A g hδ U hU) ∧
      HomogeneouslyRegularMetric (canonicalPositiveDomainMetric_P2A g hδ U hU) := by
  sorry

end PositiveDomain

section ProfileConfinement
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- MIRROR (sorry).  Source: `DifferentialGeometry/Geometry/MinimalSurface/Plateau/ProfileConfinement.lean:24`
(`DifferentialGeometry.Geometry.IsMorreyDisk.profile_confinement`), IMS03 @ 981d9a8cd.
Their status: PROVED.  Uses our verbatim copies `profileMetric_P2A`, `barrier_P2A`.
Replacement: after merge, use the original. -/
theorem IsMorreyDisk.profile_confinement_P2A
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
          barrier_P2A a (ρ y) = ρ y := by
  sorry

end ProfileConfinement

end GC.LongTime.CuspP1
