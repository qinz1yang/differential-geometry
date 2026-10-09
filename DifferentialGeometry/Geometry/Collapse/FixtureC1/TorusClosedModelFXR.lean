import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusRegisterClosedExamples
import DifferentialGeometry.Geometry.Collapse.LocalExport.ClosedMemberModel
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4RealizationC14Z
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct

/-!
# D78-5 (3), the missing `ClosedModel` of the flat register torus

Lane S-FIX-REG2 (suffix `_FXR`), G5. `closedStagesAt_OCL` / `cutAt_OCL` take a source
`S : ClosedChainEZRowsSource_RGC`, whose normalized model `M : ClosedModel W g` of a
`CompactCarrier` did not exist for the flat torus `Tor_FXC1 Λ` of O-FIXTURE-C1. This file builds it
for every period lattice `Λ`:

* `torManifold_FXR Λ`: the flat torus as a `ConnectedClosedOrientedManifold` (carrier `Tor_FXC1 Λ`,
  orientation `torOrientation_OFC`);
* `torCarrier_FXR Λ := NoCuts.carrier (torManifold_FXR Λ)` (a `CompactCarrier`, empty boundary,
  `torCarrier_facts_FXR`);
* **`torClosedModel_FXR Λ : ClosedModel (torCarrier_FXR Λ) (torMetric_FXC1 Λ)`**: `X = Tor_FXC1 Λ`
  with the induced length metric space `torMS_FXC1`, `ψ = refl`, `gX = torMetric_FXC1`,
  `metric_eq` by `pullbackMetricCross_refl`, `hmetric = torMS_hmetric_FXC1`;
* `torClosedModel_orientation_FXR`: the pulled-back orientation `orientation_RGC` IS
  `torOrientation_OFC`;
* `torRegClosedFamily_FXR`, `torRegClosedFamily_selected_FXR`: the `family` and `selected` fields
  of `ClosedFamilyInstanceC14ZV4` over this model at the register torus (scale `ρ ≡ 1`,
  orientation `M.orientation_RGC`), unconditionally (the zero family is empty). The two fields
  that remain empty are `ρ_bounds` (LPA01 window) and `witness` (LPA02 joint witness);
* `torRegClosedFamilyInstance_FXR`: the complete `ClosedFamilyInstanceC14ZV4` over the register
  torus, taking exactly those two fields as arguments.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold GC.Endpoint GC.GraphManifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

/-- **The flat torus as a connected closed oriented three-manifold.** -/
abbrev torManifold_FXR (Λ : TorusPeriods_FXC1) : ConnectedClosedOrientedManifold.{0} 3 where
  Carrier := Tor_FXC1 Λ
  orientation := torOrientation_OFC Λ
  connected := inferInstance

/-- The compact carrier of the flat torus (closed kind, orientation `torOrientation_OFC`). -/
abbrev torCarrier_FXR (Λ : TorusPeriods_FXC1) : CompactCarrier.{0} :=
  NoCuts.carrier (torManifold_FXR Λ)

/-- **The normalized model of the flat torus** as a closed member of the standing sequence. -/
def torClosedModel_FXR (Λ : TorusPeriods_FXC1) :
    ClosedModel (torCarrier_FXR Λ) (torMetric_FXC1 Λ) where
  X := Tor_FXC1 Λ
  mX := torMS_FXC1 Λ
  ψ := Diffeomorph.refl 𝓘(ℝ, E3) (Tor_FXC1 Λ) ∞
  gX := torMetric_FXC1 Λ
  metric_eq := (Diffeomorph.pullbackMetricCross_refl _).symm
  hmetric := torMS_hmetric_FXC1 Λ

/-- The standing facts of a closed member hold for the flat torus: empty model boundary and
connectedness. -/
theorem torCarrier_facts_FXR (Λ : TorusPeriods_FXC1) : ClosedMemberFacts (torCarrier_FXR Λ) :=
  ⟨closedCarrier_boundary_eq_empty (torManifold_FXR Λ), inferInstance⟩

theorem torClosedModel_X_FXR (Λ : TorusPeriods_FXC1) :
    (torClosedModel_FXR Λ).X = Tor_FXC1 Λ :=
  rfl

theorem torClosedModel_gX_FXR (Λ : TorusPeriods_FXC1) :
    (torClosedModel_FXR Λ).gX = torMetric_FXC1 Λ :=
  rfl

theorem torClosedModel_psi_FXR (Λ : TorusPeriods_FXC1) (x : Tor_FXC1 Λ) :
    (torClosedModel_FXR Λ).ψ x = x :=
  rfl

/-- **The pulled-back orientation of the model is the orientation of the flat torus**
(`ψ = refl`, `W.orientation = torOrientation_OFC`). -/
theorem torClosedModel_orientation_FXR (Λ : TorusPeriods_FXC1) :
    (torClosedModel_FXR Λ).orientation_RGC = torOrientation_OFC Λ := by
  refine ManifoldOrientation.ext fun x => ?_
  have h := (torClosedModel_FXR Λ).orientation_RGC_spec x
  have hrefl : (DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective (𝓡 3)
      (torCarrier_FXR Λ).model (torClosedModel_FXR Λ).ψ
      (fun x => ((torClosedModel_FXR Λ).ψ.mfderivToContinuousLinearEquiv (by simp) x).bijective)
      x).toLinearEquiv = LinearEquiv.refl ℝ E3 := by
    refine LinearEquiv.ext fun v => ?_
    change mfderiv (𝓡 3) (𝓡 3) (id : (torClosedModel_FXR Λ).X → (torClosedModel_FXR Λ).X) x v = v
    rw [mfderiv_id]
    rfl
  rw [hrefl, Orientation.map_refl] at h
  exact h

section Register

variable {D : ClosedEarlyData} {T : ClosedThresholdsV4 D} (R : ClosedRegisterV4 D T)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C D))
  (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0})

/-- The normalized model of the register torus. -/
abbrev torRegModel_FXR : ClosedModel
    (torCarrier_FXR (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos))
    (torMetric_FXC1 (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos)) :=
  torClosedModel_FXR (torRegPeriods_OFC R.later.excl.β₂ R.later.β₂_pos)

/-- **The `family` field of `ClosedFamilyInstanceC14ZV4` over the model of the register torus**
(scale `ρ ≡ 1`, orientation `M.orientation_RGC`): the register packet of O-FIXTURE-C1 re-stated on
the fields of the `ClosedModel`. -/
def torRegClosedFamily_FXR (Kf : ℕ) (δ εr Λz : ℝ) :
    LocalChartPacketsC14Z (torRegModel_FXR R).X (torRegModel_FXR R).gX
      (torRegModel_FXR R).hmetric (fun _ => (1 : ℝ)) (fun _ => one_pos) R.later.scale.Λ R.β
      R.later.excl.Δ R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b
      R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc
      R.later.circle.βc R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀
      R.later.split.T₀ R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz
      (torRegModel_FXR R).orientation_RGC :=
  torRegPacketsZ_OFC R hT hlc Kf δ εr Λz (torRegModel_FXR R).orientation_RGC

/-- The `selected` field of `ClosedFamilyInstanceC14ZV4` over the register torus holds
(vacuously: the zero family of the register torus is empty). -/
theorem torRegClosedFamily_selected_FXR (Kf : ℕ) (δ εr Λz : ℝ) :
    ∀ c (hc : c ∈ (torRegClosedFamily_FXR R hT hlc Kf δ εr Λz).zero.centres),
      ∃ s ∈ Icc R.later.split.T₀ R.later.split.V, ∃ hs : 0 < s,
        ((torRegClosedFamily_FXR R hT hlc Kf δ εr Λz).zero.zero c hc).radius = s * (1 : ℝ) ∧
          Lpa02WitnessAtV2 (torRegModel_FXR R).gX Kf εr R.later.err.co.e₀ δ c (1 : ℝ) s one_pos
            hs :=
  fun c hc => absurd hc (notMem_empty c)

/-- **Assembly of `ClosedFamilyInstanceC14ZV4` over the register torus** from the two fields that
remain empty on the torus: LPA01's window `ρ_bounds` (for `ρ ≡ 1`) and LPA02's joint witness.
All other fields (scale, positivity, the family, the selection) are supplied above. -/
def torRegClosedFamilyInstance_FXR (Kf : ℕ) (δ εr Λz : ℝ)
    (hwin : ∀ p : (torRegModel_FXR R).X,
      firstVolumeScale (torRegModel_FXR R).gX p R.later.scale.w / 2 < (1 : ℝ) ∧
        (1 : ℝ) < 2 * firstVolumeScale (torRegModel_FXR R).gX p (closedWPrime R.later.scale))
    (hwit : Lpa02WitnessV2 (torRegModel_FXR R).gX Kf R.later.scale.Λ R.later.scale.w εr
      R.later.err.co.e₀ R.later.split.T₀ R.later.split.V δ) :
    ClosedFamilyInstanceC14ZV4 Kf R (torRegModel_FXR R) δ εr Λz :=
  ⟨fun _ => 1, fun _ => one_pos, hwin, torRegClosedFamily_FXR R hT hlc Kf δ εr Λz, hwit,
    torRegClosedFamily_selected_FXR R hT hlc Kf δ εr Λz⟩

end Register

end DifferentialGeometry.Geometry.Collapse
