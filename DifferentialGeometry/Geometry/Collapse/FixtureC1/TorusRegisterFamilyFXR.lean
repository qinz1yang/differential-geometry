import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusClosedModelFXR
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusWindowRHB

/-!
# D78-5 (3) / F-REG-1: the `ClosedFamilyInstanceC14ZV4` over the CORRECTED register torus

Lane S-FIX-REG2 (suffix `_FXR`), G5b (a correction of G5's register section after
F-REG-1 (by S-RHOBOUNDS): at registers whose volume parameter `w` is below `(3/10) β₂` the window
`ρ_bounds` is FALSE on the existing fixture torus `torRegPeriods_OFC`, but TRUE on the corrected
torus `torRegPeriodsR_RHB R` = periods `(N, N, min β₂ (w/4))`, with the same circle packet).

On the corrected torus `torRegTorusF_RHB R`:

* `torRegModelF_FXR R := torClosedModel_FXR (torRegPeriodsR_RHB R)` (the `ClosedModel` of G5 for
  those periods; `ψ = refl`, `gX = torMetric_FXC1`, so `ballVolume` / `firstVolumeScale` of `gX`
  ARE those of `g` at `ψ p = p`: no transport is needed, and the general transport is
  `ClosedModel.firstVolumeScale_eq`);
* **`torRegModelF_rhoBounds_FXR`**: LPA01's window `ρ_bounds` at `ρ ≡ 1` on the model, from
  `ClosedLaterV4.torWindowF_RHB`, at EVERY register;
* `torRegPacketsZF_FXR`: the final family `LocalChartPacketsC14Z` (empty zero family, vacuous weak
  edge density), built from `torRegPacketsF_RHB` as `torRegPacketsZ_OFC` is from
  `torRegPackets_OFC`;
* `torRegClosedFamilyF_FXR`, `torRegClosedFamilyF_selected_FXR`: the `family` and `selected` fields;
* **`torRegClosedFamilyInstanceF_FXR`**: the complete `ClosedFamilyInstanceC14ZV4 Kf R
  (torRegModelF_FXR R) δ εr Λz` from ONE remaining input, the LPA02 joint witness `witness`
  (layer iii); `ρ_bounds`, the family and the selection are supplied.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold GC.Endpoint
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

section Register

variable {D : ClosedEarlyData} {T : ClosedThresholdsV4 D} (R : ClosedRegisterV4 D T)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C D))
  (hlc : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0})

/-- The normalized model of the CORRECTED register torus. -/
abbrev torRegModelF_FXR : ClosedModel (torCarrier_FXR (torRegPeriodsR_RHB R))
    (torMetric_FXC1 (torRegPeriodsR_RHB R)) :=
  torClosedModel_FXR (torRegPeriodsR_RHB R)

/-- **LPA01's window `ρ_bounds` for `ρ ≡ 1` on the model of the corrected register torus**, at
every register. -/
theorem torRegModelF_rhoBounds_FXR :
    ∀ p : (torRegModelF_FXR R).X,
      firstVolumeScale (torRegModelF_FXR R).gX p R.later.scale.w / 2 < (1 : ℝ) ∧
        (1 : ℝ) < 2 * firstVolumeScale (torRegModelF_FXR R).gX p (closedWPrime R.later.scale) :=
  fun p => R.later.torWindowF_RHB p

/-- **The final family on the corrected register torus** (`o_M` a parameter; the zero family is
empty): `torRegPacketsF_RHB` with the empty zero family and vacuous weak edge density. -/
def torRegPacketsZF_FXR (Kf : ℕ) (δ εr Λz : ℝ)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (torRegTorusF_RHB R) 3) :
    LocalChartPacketsC14Z (torRegTorusF_RHB R) (torMetric_FXC1 (torRegPeriodsR_RHB R))
      (torMS_hmetric_FXC1 (torRegPeriodsR_RHB R)) (fun _ => (1 : ℝ)) (fun _ => one_pos)
      R.later.scale.Λ R.β R.later.excl.Δ R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ
      R.later.split.b R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε
      R.later.circle.γc R.later.circle.βc R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr
      R.later.err.co.e₀ R.later.split.T₀ R.later.split.V R.later.err.co.ve R.later.err.co.ζ
      Λz oM where
  toLocalChartPacketsC14 := torRegPacketsF_RHB R hT hlc Kf δ εr Λz
  weak_edge_density := fun p hp => absurd hp
    (torNotMemStratum_FXC1 (torRegPeriodsR_RHB R) one_pos
      (R.torus_numbers_OFC hT hlc).1 (R.torus_numbers_OFC hT hlc).2.1
      (by rw [R.β_two_VAL6]; exact torRegPeriodsF_L2_RHB R.later.β₂_pos R.later.w_pos)
      (by rw [R.β_two_VAL6]; exact torRegPeriodsF_plane_RHB R.later.β₂_pos R.later.w_pos)
      (R.torus_numbers_OFC hT hlc).2.2.1 (by decide) p)
  zero_sublevel_types := fun c hc => absurd hc (notMem_empty c)

/-- **The `family` field of `ClosedFamilyInstanceC14ZV4` over the model of the corrected register
torus** (scale `ρ ≡ 1`, orientation `M.orientation_RGC`). -/
def torRegClosedFamilyF_FXR (Kf : ℕ) (δ εr Λz : ℝ) :
    LocalChartPacketsC14Z (torRegModelF_FXR R).X (torRegModelF_FXR R).gX
      (torRegModelF_FXR R).hmetric (fun _ => (1 : ℝ)) (fun _ => one_pos) R.later.scale.Λ R.β
      R.later.excl.Δ R.later.err.co.qs Kf R.later.err.co.qe R.later.err.bd.μ R.later.split.b
      R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc
      R.later.circle.βc R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀
      R.later.split.T₀ R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz
      (torRegModelF_FXR R).orientation_RGC :=
  torRegPacketsZF_FXR R hT hlc Kf δ εr Λz (torRegModelF_FXR R).orientation_RGC

/-- The `selected` field holds (vacuously: the zero family is empty). -/
theorem torRegClosedFamilyF_selected_FXR (Kf : ℕ) (δ εr Λz : ℝ) :
    ∀ c (hc : c ∈ (torRegClosedFamilyF_FXR R hT hlc Kf δ εr Λz).zero.centres),
      ∃ s ∈ Icc R.later.split.T₀ R.later.split.V, ∃ hs : 0 < s,
        ((torRegClosedFamilyF_FXR R hT hlc Kf δ εr Λz).zero.zero c hc).radius = s * (1 : ℝ) ∧
          Lpa02WitnessAtV2 (torRegModelF_FXR R).gX Kf εr R.later.err.co.e₀ δ c (1 : ℝ) s one_pos
            hs :=
  fun c hc => absurd hc (notMem_empty c)

/-- **`ClosedFamilyInstanceC14ZV4` over the corrected register torus** from the ONE remaining
field, LPA02's joint witness (layer iii). LPA01's window, the final family and the selection are
supplied. -/
def torRegClosedFamilyInstanceF_FXR (Kf : ℕ) (δ εr Λz : ℝ)
    (hwit : Lpa02WitnessV2 (torRegModelF_FXR R).gX Kf R.later.scale.Λ R.later.scale.w εr
      R.later.err.co.e₀ R.later.split.T₀ R.later.split.V δ) :
    ClosedFamilyInstanceC14ZV4 Kf R (torRegModelF_FXR R) δ εr Λz :=
  ⟨fun _ => 1, fun _ => one_pos, torRegModelF_rhoBounds_FXR R,
    torRegClosedFamilyF_FXR R hT hlc Kf δ εr Λz, hwit,
    torRegClosedFamilyF_selected_FXR R hT hlc Kf δ εr Λz⟩

end Register

end DifferentialGeometry.Geometry.Collapse
