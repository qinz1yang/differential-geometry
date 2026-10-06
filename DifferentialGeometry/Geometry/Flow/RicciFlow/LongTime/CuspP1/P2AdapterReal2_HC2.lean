import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExteriorConvexity

/-!
# S-MIRRORS G2 (`_HC2`): real `PersistentCuspExterior.exists_eventual_convex_profiles`

Replaces the placeholder mirror `PersistentCuspExterior.exists_eventual_convex_profiles_P2A` of
`P2AdapterImportedLemmas.lean` by the IMS03 theorem
`GC.LongTime.PersistentCuspExterior.exists_eventual_convex_profiles`
(`LongTime/CuspExteriorConvexity.lean`, branch `gc/juihuichung/ims03-astra-20261005`, tip
`f49e541fb`).  The statement is literally that of the mirror.

The IMS03 files `CuspExteriorCollars` and `CuspExteriorConvexity` do not compile in this tree as
they are; the modules of these names are shims over the repaired ports
`CuspExteriorCollarsIms03Port_HC2` and `CuspExteriorConvexityIms03Port_HC2` (see their headers for
the exact list of local repairs).  All other modules of the IMS03 dependency closure are verbatim
copies (or shims over this tree's equivalent monoliths).
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

/-- Statement of the mirror `exists_eventual_convex_profiles_P2A`, proved by the real IMS03 theorem
`PersistentCuspExterior.exists_eventual_convex_profiles`. -/
theorem _root_.GC.LongTime.PersistentCuspExterior.exists_eventual_convex_profiles_P2A_HC2
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
              0 < hessFun (postMetric F.observation t) ρ x V V :=
  PersistentCuspExterior.exists_eventual_convex_profiles C E tmin

/-- Consumer of G2: eventually the persistent exterior is a smooth sublevel set `{ρ ≤ 0}`. -/
theorem _root_.GC.LongTime.PersistentCuspExterior.exists_eventual_sublevel_P2A_HC2
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ}
    (C : PersistentHyperbolicCores F K) (E : PersistentCuspExterior C) (tmin : ℝ) :
    ∃ T : ℝ, E.start ≤ T ∧ ∀ (t : ℝ), T ≤ t →
      ∃ ρ : (postStage F.observation t).Carrier → ℝ,
        ContMDiff (𝓡 3) 𝓘(ℝ) ∞ ρ ∧ E.region t = {x | ρ x ≤ 0} := by
  obtain ⟨_, _, T, hstart, _, _, h⟩ :=
    PersistentCuspExterior.exists_eventual_convex_profiles_P2A_HC2 C E tmin
  refine ⟨T, hstart, fun t ht => ?_⟩
  obtain ⟨ρ, hρ, hreg, _⟩ := h t ht
  exact ⟨ρ, hρ, hreg⟩

end GC.LongTime.CuspP1
