import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HModel_S112

/-!
# CH12-S112 G2: `hchart_S112` (S80's `hchart`, unconditional)

`hchart_of_model_O43` (G2a of O43) with its inline binder `hmodel` discharged by `hmodel_S112`.
The statement is `[FROZEN v2] CH12-S80` `hchart` verbatim, so `ckErr_of_chartJets_S80 H (hchart_S112 H)`,
`isotopy_assembly_O40 H (hchart_S112 H)` and `step_isotopy_O50 H (hchart_S112 H)` close (d').
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open Set
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- **G2.** S80's `hchart` ([FROZEN v2] CH12-S80, verbatim), with no remaining input. -/
theorem hchart_S112 (H : FiniteVolumeHyperbolicModel.{u}) :
    ∀ (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D : Set H.Carrier) (k : ℕ) (ε : ℝ),
      IsCompact D → D ⊆ A.cover → 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ (F : H.Carrier → H.Carrier) (O : Set H.Carrier), IsOpen O → D ⊆ O →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ F O → CkCloseInAtlas_CX3 A D (k + 1) δ F →
          ∀ j : ℕ, j ≤ k → ∀ q ∈ D, ckErr_S45 H H.metric 1 F j q ≤ ε :=
  hchart_of_model_O43 H (hmodel_S112 H)

end GC.LongTime.Ch12
