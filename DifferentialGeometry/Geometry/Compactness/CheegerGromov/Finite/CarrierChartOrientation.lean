import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CarrierChart
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.Orientation

/-!
# Orientation of the carrier chart parametrizations (LFR14, lane L-BIND, for I-LIM-OR)

Let `𝒜` be a smooth compatible atlas whose transitions have positive Jacobian determinant and let
`O` be an orientation of `SmoothCarrier 𝒜` that reads as `oE` in every chart (`O.inChart = oE`,
as produced by `SmoothCarrier.exists_of_contDiff_atlas_oriented`). If the chart `j` of `𝒜` is
`ψ⁻¹ ≫ κ` with `κ` a `C^K` homeomorphism of positive Jacobian determinant, then the
parametrization `carrierChartParam 𝒜 ψ j κ …` maps `oE` to `O` at EVERY point of its source
(`orientation_map_mfderiv_carrierChartParam`): in the chart of `O` at the image point its
derivative is the derivative of `(transition of 𝒜) ∘ κ`, a product of two positive determinants.
No connectedness of the source is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Topology.Manifold

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace X]

omit [FiniteDimensional ℝ E] in
/-- In the chart `j'` of the carrier, the parametrization `carrierChartParam 𝒜 ψ j κ …` is the
transition `(𝒜.chart j)⁻¹ ≫ 𝒜.chart j'` after `κ`, on all of `ψ.source`. -/
theorem chart_comp_carrierChartParam_eqOn (𝒜 : SmoothCompatibleAtlas E X ι) {K : ℕ}
    (ψ : OpenPartialHomeomorph E X) (j j' : ι) (κ : E ≃ₜ E)
    (hchart : 𝒜.chart j = ψ.symm.trans κ.toOpenPartialHomeomorph) (hκ : ContDiff ℝ K κ)
    (hκs : ContDiff ℝ K κ.symm) :
    EqOn (fun w => SmoothCarrier.chart 𝒜 j' (carrierChartParam 𝒜 ψ j κ hchart hκ hκs w))
      (fun w => ((𝒜.chart j).symm.trans (𝒜.chart j')) (κ w)) ψ.source := by
  intro w _
  change 𝒜.chart j' (ψ w) = 𝒜.chart j' ((𝒜.chart j).symm (κ w))
  congr 1
  rw [hchart, OpenPartialHomeomorph.coe_trans_symm]
  simp

/-- **Orientation of `σ`.** The parametrization `carrierChartParam 𝒜 ψ j κ …` maps `oE` to the
carrier orientation `O` at every point of its source. -/
theorem orientation_map_mfderiv_carrierChartParam (𝒜 : SmoothCompatibleAtlas E X ι) {K : ℕ}
    (hK : 1 ≤ K) (ψ : OpenPartialHomeomorph E X) (j : ι) (κ : E ≃ₜ E)
    (hchart : 𝒜.chart j = ψ.symm.trans κ.toOpenPartialHomeomorph) (hκ : ContDiff ℝ K κ)
    (hκs : ContDiff ℝ K κ.symm) (hdetκ : ∀ u, 0 < (fderiv ℝ κ u).det)
    (hpos : ∀ i i', ∀ u ∈ ((𝒜.chart i).symm.trans (𝒜.chart i')).source,
      0 < (fderiv ℝ ((𝒜.chart i).symm.trans (𝒜.chart i')) u).det)
    {n : ℕ} (O : ManifoldOrientation 𝓘(ℝ, E) (SmoothCarrier 𝒜) n)
    (oE : Orientation ℝ E (Fin n))
    (hO : ∀ (y₀ x : SmoothCarrier 𝒜)
      (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) y₀).baseSet), O.inChart y₀ x hx = oE)
    {u : E} (hu : u ∈ (carrierChartParam 𝒜 ψ j κ hchart hκ hκs).source) :
    Orientation.map (Fin n)
      (((carrierChartParam 𝒜 ψ j κ hchart hκ hκs).isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E)
          (K : ℕ∞ω) hu).mfderivToContinuousLinearEquiv
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK)).toLinearEquiv oE =
      O.orientation (carrierChartParam 𝒜 ψ j κ hchart hκ hκs u) := by
  set σ := carrierChartParam 𝒜 ψ j κ hchart hκ hκs with hσdef
  have hK0 : (K : ℕ∞ω) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ E :=
    (Fintype.card_fin n).trans O.dimension_eq.symm
  have hxx : σ u ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (σ u)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) (σ u)
  have hxc : σ u ∈ (chartAt E (σ u)).source := mem_chart_source E (σ u)
  obtain ⟨j', hj'⟩ := chart_mem_atlas E (σ u)
  let L : E ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, E) (σ u) :=
    ((σ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) (K : ℕ∞ω) hu).mfderivToContinuousLinearEquiv
      hK0).toLinearEquiv
  let T : TangentSpace 𝓘(ℝ, E) (σ u) ≃ₗ[ℝ] E :=
    tangentChartEquiv 𝓘(ℝ, E) (SmoothCarrier 𝒜) (σ u) (σ u) hxx
  have hT : Orientation.map (Fin n) T (O.orientation (σ u)) = oE := hO (σ u) (σ u) hxx
  change Orientation.map (Fin n) L oE = O.orientation (σ u)
  apply (Orientation.map (Fin n) T).injective
  rw [hT, DifferentialGeometry.VectorBundle.map_orientation_trans_between L T oE,
    Orientation.map_eq_iff_det_pos _ _ hcard]
  -- the composite derivative is the Euclidean derivative of `chart ∘ σ`
  have hσd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) σ u :=
    ((σ.contMDiffOn_toFun u hu).contMDiffAt (σ.open_source.mem_nhds hu)).mdifferentiableAt hK0
  have hcd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) (σ u)) (σ u) :=
    mdifferentiableAt_extChartAt hxc
  have hlin : ((L.trans T : E ≃ₗ[ℝ] E) : E →ₗ[ℝ] E) =
      (fderiv ℝ (extChartAt 𝓘(ℝ, E) (σ u) ∘ σ) u : E →L[ℝ] E) := by
    ext v
    have hTv : T (L v) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) (σ u)) (σ u) (L v) := by
      change tangentChartEquiv 𝓘(ℝ, E) (SmoothCarrier 𝒜) (σ u) (σ u) hxc (L v) = _
      rw [tangentChartEquiv_eq_preferredChartTangentEquiv 𝓘(ℝ, E) (σ u) (σ u) hxc]
      rfl
    change T (L v) = _
    rw [hTv]
    refine (mfderiv_comp_apply u hcd hσd v).symm.trans ?_
    rw [mfderiv_eq_fderiv]
    rfl
  rw [hlin]
  change 0 < (fderiv ℝ (extChartAt 𝓘(ℝ, E) (σ u) ∘ σ) u).det
  -- local form `transition ∘ κ`
  have hu' : u ∈ ψ.source := hu
  have hev : (extChartAt 𝓘(ℝ, E) (σ u) ∘ σ) =ᶠ[𝓝 u]
      (fun w => ((𝒜.chart j).symm.trans (𝒜.chart j')) (κ w)) := by
    filter_upwards [ψ.open_source.mem_nhds hu'] with w hw
    have h := chart_comp_carrierChartParam_eqOn 𝒜 ψ j j' κ hchart hκ hκs hw
    rw [Function.comp_apply, extChartAt_coe, Function.comp_apply, modelWithCornersSelf_coe, id_eq,
      ← hj']
    exact h
  have hmem : κ u ∈ ((𝒜.chart j).symm.trans (𝒜.chart j')).source := by
    refine ⟨?_, ?_⟩
    · change κ u ∈ (𝒜.chart j).target
      rw [hchart]
      simpa using hu'
    · change (𝒜.chart j).symm (κ u) ∈ (𝒜.chart j').source
      have hψu : (𝒜.chart j).symm (κ u) = ψ u := by
        rw [hchart, OpenPartialHomeomorph.coe_trans_symm]
        simp
      rw [hψu]
      change σ u ∈ (SmoothCarrier.chart 𝒜 j').source
      rw [hj']
      exact hxc
  have hTrd : DifferentiableAt ℝ ((𝒜.chart j).symm.trans (𝒜.chart j')) (κ u) :=
    ((𝒜.contDiffOn_transition j j').contDiffAt
      (((𝒜.chart j).symm.trans (𝒜.chart j')).open_source.mem_nhds hmem)).differentiableAt
      (by simp)
  have hκd : DifferentiableAt ℝ κ u :=
    (hκ.differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK)).differentiableAt
  rw [hev.fderiv_eq, show (fun w => ((𝒜.chart j).symm.trans (𝒜.chart j')) (κ w)) =
      ((𝒜.chart j).symm.trans (𝒜.chart j')) ∘ κ from rfl, fderiv_comp u hTrd hκd]
  have hdet : ((fderiv ℝ ((𝒜.chart j).symm.trans (𝒜.chart j')) (κ u)).comp
      (fderiv ℝ κ u)).det =
      (fderiv ℝ ((𝒜.chart j).symm.trans (𝒜.chart j')) (κ u)).det * (fderiv ℝ κ u).det :=
    LinearMap.det_comp _ _
  rw [hdet]
  exact mul_pos (hpos j j' (κ u) hmem) (hdetκ u)

end DifferentialGeometry.CheegerGromovCompactness
