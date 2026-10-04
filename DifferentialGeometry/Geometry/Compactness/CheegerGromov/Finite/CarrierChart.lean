import DifferentialGeometry.Topology.Manifold.SmoothCarrier.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Order-`K` chart parametrizations of a smooth carrier (LFR14, lane L-BIND)

Let `𝒜` be a smooth compatible atlas on a metric space `X` whose chart `j` is `ψ⁻¹ ≫ κ` for an
open partial homeomorphism `ψ : E → X` and a homeomorphism `κ` of `E` that is `C^K` with `C^K`
inverse (the shape produced by `SmoothCarrier.exists_of_contDiff_atlas`). Then `ψ`, read into the
smooth carrier `SmoothCarrier 𝒜`, is an order-`K` partial diffeomorphism
(`carrierChartParam`): its underlying partial equivalence is `ψ`'s, so its source, target, value
and inverse are those of `ψ` by definition.

`carrierChartParam_inner`: if a field of bilinear forms on `X` is `B` in the coordinates `ψ⁻¹`
and its pull-back to the carrier along `toBase` is `GN`, then `GN` read in the parametrization is
`B` again.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Topology.Manifold

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace X]

theorem smoothCarrier_chart_mem_maximalAtlas (𝒜 : SmoothCompatibleAtlas E X ι) (j : ι) :
    SmoothCarrier.chart 𝒜 j ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ (SmoothCarrier 𝒜) :=
  IsManifold.subset_maximalAtlas (⟨j, rfl⟩ : SmoothCarrier.chart 𝒜 j ∈ atlas E (SmoothCarrier 𝒜))

theorem natCast_le_infty (K : ℕ) : (K : ℕ∞ω) ≤ ∞ := by
  exact_mod_cast le_top

theorem contMDiffOn_carrierChartParam_toFun (𝒜 : SmoothCompatibleAtlas E X ι) {K : ℕ}
    (ψ : OpenPartialHomeomorph E X) (j : ι) (κ : E ≃ₜ E)
    (hchart : 𝒜.chart j = ψ.symm.trans κ.toOpenPartialHomeomorph) (hκ : ContDiff ℝ K κ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (fun u => SmoothCarrier.ofBase 𝒜 (ψ u)) ψ.source := by
  have hsymm : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (SmoothCarrier.chart 𝒜 j).symm
      (SmoothCarrier.chart 𝒜 j).target :=
    (contMDiffOn_symm_of_mem_maximalAtlas (smoothCarrier_chart_mem_maximalAtlas 𝒜 j)).of_le
      (natCast_le_infty K)
  have hmaps : MapsTo κ ψ.source (SmoothCarrier.chart 𝒜 j).target := by
    intro u hu
    change κ u ∈ (𝒜.chart j).target
    rw [hchart]
    simpa using hu
  refine (hsymm.comp hκ.contMDiff.contMDiffOn hmaps).congr ?_
  intro u _
  change SmoothCarrier.ofBase 𝒜 (ψ u) = (𝒜.chart j).symm (κ u)
  rw [hchart, OpenPartialHomeomorph.coe_trans_symm]
  simp [SmoothCarrier.ofBase]
  rfl

theorem contMDiffOn_carrierChartParam_invFun (𝒜 : SmoothCompatibleAtlas E X ι) {K : ℕ}
    (ψ : OpenPartialHomeomorph E X) (j : ι) (κ : E ≃ₜ E)
    (hchart : 𝒜.chart j = ψ.symm.trans κ.toOpenPartialHomeomorph) (hκs : ContDiff ℝ K κ.symm) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (fun x => ψ.symm (SmoothCarrier.toBase 𝒜 x))
      (SmoothCarrier.toBase 𝒜 ⁻¹' ψ.target) := by
  have hch : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (SmoothCarrier.chart 𝒜 j)
      (SmoothCarrier.chart 𝒜 j).source :=
    (contMDiffOn_of_mem_maximalAtlas (smoothCarrier_chart_mem_maximalAtlas 𝒜 j)).of_le
      (natCast_le_infty K)
  have hsub : SmoothCarrier.toBase 𝒜 ⁻¹' ψ.target ⊆ (SmoothCarrier.chart 𝒜 j).source := by
    intro x hx
    change SmoothCarrier.toBase 𝒜 x ∈ (𝒜.chart j).source
    rw [hchart]
    simpa using hx
  refine (((hκs.contMDiff.contMDiffOn (s := univ)).comp hch (fun _ _ => mem_univ _)).mono hsub).congr ?_
  intro x _
  change ψ.symm (SmoothCarrier.toBase 𝒜 x) = κ.symm (𝒜.chart j (SmoothCarrier.toBase 𝒜 x))
  rw [hchart]
  simp

/-- The order-`K` parametrization of the smooth carrier `SmoothCarrier 𝒜` given by `ψ`, when the
atlas chart `j` is `ψ⁻¹ ≫ κ` with `κ` a `C^K` homeomorphism of `E` with `C^K` inverse. Its
underlying partial equivalence is that of `ψ`. -/
def carrierChartParam (𝒜 : SmoothCompatibleAtlas E X ι) {K : ℕ}
    (ψ : OpenPartialHomeomorph E X) (j : ι) (κ : E ≃ₜ E)
    (hchart : 𝒜.chart j = ψ.symm.trans κ.toOpenPartialHomeomorph) (hκ : ContDiff ℝ K κ)
    (hκs : ContDiff ℝ K κ.symm) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (SmoothCarrier 𝒜) K where
  toPartialEquiv := ψ.toPartialEquiv
  open_source := ψ.open_source
  open_target := ψ.open_target
  contMDiffOn_toFun := contMDiffOn_carrierChartParam_toFun 𝒜 ψ j κ hchart hκ
  contMDiffOn_invFun := contMDiffOn_carrierChartParam_invFun 𝒜 ψ j κ hchart hκs

section Inner

variable [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) 1 X]

/-- The chain rule through the carrier: `dψ⁻¹ ∘ d toBase ∘ dσ = id` on the source of `ψ`. -/
theorem mfderiv_symm_toBase_carrierChartParam (𝒜 : SmoothCompatibleAtlas E X ι) {K : ℕ}
    (hK : 1 ≤ K) (ψ : OpenPartialHomeomorph E X) (j : ι) (κ : E ≃ₜ E)
    (hchart : 𝒜.chart j = ψ.symm.trans κ.toOpenPartialHomeomorph) (hκ : ContDiff ℝ K κ)
    (hκs : ContDiff ℝ K κ.symm) (hψ : ψ.symm ∈ atlas E X)
    (hT : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase 𝒜))
    {u : E} (hu : u ∈ ψ.source) (z : E) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ.symm
        (SmoothCarrier.toBase 𝒜 (carrierChartParam 𝒜 ψ j κ hchart hκ hκs u))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase 𝒜)
          (carrierChartParam 𝒜 ψ j κ hchart hκ hκs u)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (carrierChartParam 𝒜 ψ j κ hchart hκ hκs) u z)) : E) = z := by
  set σ := carrierChartParam 𝒜 ψ j κ hchart hκ hκs with hσ
  have hσu : SmoothCarrier.toBase 𝒜 (σ u) = ψ u := rfl
  have hK0 : (K : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hσd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) σ u :=
    ((σ.contMDiffOn_toFun u hu).contMDiffAt (σ.open_source.mem_nhds hu)).mdifferentiableAt hK0
  have hTd := hT (σ u)
  have hψd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) ψ.symm (SmoothCarrier.toBase 𝒜 (σ u)) :=
    mdifferentiableAt_atlas hψ (by rw [hσu]; exact ψ.map_source hu)
  have hid : (ψ.symm ∘ (SmoothCarrier.toBase 𝒜 ∘ σ)) =ᶠ[𝓝 u] id := by
    filter_upwards [ψ.open_source.mem_nhds hu] with x hx
    exact ψ.left_inv hx
  have h1 := mfderiv_comp_apply u hTd hσd z
  have h2 := mfderiv_comp_apply u hψd (hTd.comp u hσd) z
  have h4 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ.symm ∘ (SmoothCarrier.toBase 𝒜 ∘ σ)) u z = z := by
    rw [mfderiv_eq_fderiv, hid.fderiv_eq, fderiv_id]
    rfl
  exact (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ.symm (SmoothCarrier.toBase 𝒜 (σ u))) h1.symm).trans
    (h2.symm.trans h4)

/-- A field of bilinear forms `GX` on `X` that is `B` in the coordinates `ψ⁻¹`, pulled back to the
carrier along `toBase` (`GN`), is `B` in the parametrization `carrierChartParam`. -/
theorem carrierChartParam_inner (𝒜 : SmoothCompatibleAtlas E X ι) {K : ℕ} (hK : 1 ≤ K)
    (ψ : OpenPartialHomeomorph E X) (j : ι) (κ : E ≃ₜ E)
    (hchart : 𝒜.chart j = ψ.symm.trans κ.toOpenPartialHomeomorph) (hκ : ContDiff ℝ K κ)
    (hκs : ContDiff ℝ K κ.symm) (hψ : ψ.symm ∈ atlas E X)
    (hT : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase 𝒜))
    (GX : X → E →L[ℝ] E →L[ℝ] ℝ) (GN : SmoothCarrier 𝒜 → E →L[ℝ] E →L[ℝ] ℝ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hGX : ∀ x ∈ ψ.target, ∀ v w : E, GX x v w =
      B (ψ.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ.symm x v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ.symm x w))
    (hGN : ∀ (x : SmoothCarrier 𝒜) (v w : E), GN x v w = GX (SmoothCarrier.toBase 𝒜 x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase 𝒜) x v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (SmoothCarrier.toBase 𝒜) x w))
    {u : E} (hu : u ∈ ψ.source) (v w : E) :
    GN (carrierChartParam 𝒜 ψ j κ hchart hκ hκs u)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (carrierChartParam 𝒜 ψ j κ hchart hκ hκs) u v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (carrierChartParam 𝒜 ψ j κ hchart hκ hκs) u w) = B u v w := by
  have hmem : SmoothCarrier.toBase 𝒜 (carrierChartParam 𝒜 ψ j κ hchart hκ hκs u) ∈ ψ.target :=
    ψ.map_source hu
  have hv := mfderiv_symm_toBase_carrierChartParam 𝒜 hK ψ j κ hchart hκ hκs hψ hT hu v
  have hw := mfderiv_symm_toBase_carrierChartParam 𝒜 hK ψ j κ hchart hκ hκs hψ hT hu w
  refine (hGN _ _ _).trans ((hGX _ hmem _ _).trans ?_)
  simp only [hv, hw]
  exact congrArg (fun y => B y v w) (ψ.left_inv hu)

end Inner


section Identification

variable (𝒜 : SmoothCompatibleAtlas E X ι) {K : ℕ}

/-- **Two-sided regularity of `σ`** (review item 1). The parametrization `carrierChartParam` has
source `ψ.source`, target `toBase⁻¹ ψ.target`, value `ofBase ∘ ψ`, inverse `ψ⁻¹ ∘ toBase`, and is
`C^K` in both directions on these open sets. -/
theorem carrierChartParam_twoSided (ψ : OpenPartialHomeomorph E X) (j : ι) (κ : E ≃ₜ E)
    (hchart : 𝒜.chart j = ψ.symm.trans κ.toOpenPartialHomeomorph) (hκ : ContDiff ℝ K κ)
    (hκs : ContDiff ℝ K κ.symm) :
    (carrierChartParam 𝒜 ψ j κ hchart hκ hκs).source = ψ.source ∧
      (carrierChartParam 𝒜 ψ j κ hchart hκ hκs).target = SmoothCarrier.toBase 𝒜 ⁻¹' ψ.target ∧
      (∀ u, carrierChartParam 𝒜 ψ j κ hchart hκ hκs u = SmoothCarrier.ofBase 𝒜 (ψ u)) ∧
      (∀ x, (carrierChartParam 𝒜 ψ j κ hchart hκ hκs).symm x =
        ψ.symm (SmoothCarrier.toBase 𝒜 x)) ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (carrierChartParam 𝒜 ψ j κ hchart hκ hκs)
        (carrierChartParam 𝒜 ψ j κ hchart hκ hκs).source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (carrierChartParam 𝒜 ψ j κ hchart hκ hκs).symm
        (carrierChartParam 𝒜 ψ j κ hchart hκ hκs).target :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl,
    contMDiffOn_carrierChartParam_toFun 𝒜 ψ j κ hchart hκ,
    contMDiffOn_carrierChartParam_invFun 𝒜 ψ j κ hchart hκs⟩

/-- **`σ`/`ψ` transitions on the open overlaps** (review item 2). The transition
`σ_a ≫ σ_c⁻¹` of two parametrizations has exactly the overlap domain of `ψ_a ≫ ψ_c⁻¹` (an open
set) and agrees with it there. -/
theorem carrierChartParam_trans_symm (ψa ψc : OpenPartialHomeomorph E X) (ja jc : ι)
    (κa κc : E ≃ₜ E) (hcha : 𝒜.chart ja = ψa.symm.trans κa.toOpenPartialHomeomorph)
    (hchc : 𝒜.chart jc = ψc.symm.trans κc.toOpenPartialHomeomorph) (hκa : ContDiff ℝ K κa)
    (hκas : ContDiff ℝ K κa.symm) (hκc : ContDiff ℝ K κc) (hκcs : ContDiff ℝ K κc.symm) :
    ((carrierChartParam 𝒜 ψa ja κa hcha hκa hκas).trans
        (carrierChartParam 𝒜 ψc jc κc hchc hκc hκcs).symm).source =
        (ψa.trans ψc.symm).source ∧
      IsOpen (ψa.trans ψc.symm).source ∧
      EqOn ((carrierChartParam 𝒜 ψa ja κa hcha hκa hκas).trans
          (carrierChartParam 𝒜 ψc jc κc hchc hκc hκcs).symm)
        (ψa.trans ψc.symm) (ψa.trans ψc.symm).source :=
  ⟨rfl, (ψa.trans ψc.symm).open_source, fun _ _ => rfl⟩

end Identification

end DifferentialGeometry.CheegerGromovCompactness
