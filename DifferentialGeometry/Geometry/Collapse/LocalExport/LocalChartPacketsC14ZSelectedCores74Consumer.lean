import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZSelectedCores74
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsDihedralInhabitant

/-!
# Draft 74, G32: consumer of the LFR54 bridge on the dihedral inhabitant

Lane C14-REG-CHAIN (by S-REG-CHAIN3), G32 (consumer). The final family `LocalChartPacketsC14Z` on
the actual closed manifold `ℝP³ # ℝP³` (`dihedralTinyPacketsC14Z_CHI`, one zero ball whose
sublevels are the whole source, the compact-model branch of LFR54) gives, through
`LocalChartPacketsC14Z.nonempty_selectedCore74`, a selected core of its actual sublevel
`{η ≤ 2/5}` (a closed core, with the dihedral metric of `sec ≥ 0`), and the canonical metric of
the type `ℝP³ # ℝP³` exists by `exists_nonneg_metric_of_isCompactNonnegativeType74`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian

attribute [local instance] dihedralTinyMetricSpace_CHI

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **The bridge on the dihedral inhabitant**: the actual sublevel `{η ≤ 2/5}` of the one zero
ball is a selected smooth core. -/
theorem dihedralTiny_selectedCore74_CHI (hβ : ∀ j, 1 ≤ j → j ≤ 3 → β j ≤ 1 / 4) (hb : b ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hεr : 0 ≤ εr) (he : 0 < e) (hT : 1000 ≤ T) (hδT : 1 ≤ δ * T)
    (hTV : T ≤ V) :
    Nonempty (GC.GraphManifold.Assembly.SelectedSmoothCore74.{0, 0}
      {x : dihedralZeroSource | ((dihedralTinyPacketsC14Z_CHI (Λ := Λ) (Δ := Δ) (σs := σs)
        (K := K) (σc := σc) (μ := μ) (s := s) (b' := b') (s' := s') (ε := ε) (γc := γc)
        (βc := βc) (Lmax := Lmax) (τ := τ) (γ := γ) (vs := vs) (ζ := ζ) (Λz := Λz)
        hβ hb hδ hδ1 hεr he hT hδT hTV).zero.zero dihedralTinyBase_CHI rfl).radial x ≤ 2 / 5}) :=
  (dihedralTinyPacketsC14Z_CHI (Λ := Λ) (Δ := Δ) (σs := σs) (K := K) (σc := σc) (μ := μ)
    (s := s) (b' := b') (s' := s') (ε := ε) (γc := γc) (βc := βc) (Lmax := Lmax) (τ := τ)
    (γ := γ) (vs := vs) (ζ := ζ) (Λz := Λz)
    hβ hb hδ hδ1 hεr he hT hδT hTV).nonempty_selectedCore74 rfl ⟨by norm_num, by norm_num⟩

/-- **The canonical metric of the type `ℝP³ # ℝP³`**: `RP³ # RP³` is of type
`IsCompactNonnegativeType` (identity diffeomorphism) and carries a smooth metric of `sec ≥ 0`. -/
theorem dihedralTiny_nonneg_metric_CHI :
    ∃ g : SmoothRiemannianMetric (𝓡 3) dihedralTinyManifold_CHI.Carrier,
      SectionalBoundedBelow g 0 :=
  exists_nonneg_metric_of_isCompactNonnegativeType74 dihedralTinyManifold_CHI
    (Or.inr (Or.inr (Or.inl ⟨Diffeomorph.refl (𝓡 3) dihedralZeroSource ∞⟩)))

end DifferentialGeometry.Geometry.Collapse
