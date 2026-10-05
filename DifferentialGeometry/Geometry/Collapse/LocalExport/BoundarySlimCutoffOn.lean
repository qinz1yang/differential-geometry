import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalPacketsOn

/-!
# The actual slim cutoffs of a regional slim family on a complete carrier (lane B-COUNT, M1)

The closed slim cutoff `SlimCentre.cutoff` / `SlimFamily.cutoff` (`LocalChartFamilyApplications`)
is defined on a compact carrier. Its twin on a regional slim centre `SlimCentreOn` (complete,
σ-compact carrier, e.g. the completed interior `(W°, d_ĝ)` of a boundary family) is the packet's
LC85 cutoff with the normalized-scale instances built from the carrier's OWN completeness (the same
pattern as `SlimCentreOn.coord_BCG2`):

* `SlimCentreOn.cutoff_BCNT`, `SlimFamilyOn.cutoff_BCNT` (zero off the centres);
* `SlimCentreOn.tsupport_cutoff_subset_BCNT`, `SlimFamilyOn.tsupport_cutoff_subset_BCNT`: the closed
  support lies in the physical ball `B̄(j, 0.91·10⁶Δρ(j))`;
* `SlimCentreOn.contMDiff_cutoff_BCNT`, `SlimCentreOn.cutoff_mem_Icc_BCNT` (smooth, values in
  `[0, 1]`), `SlimFamilyOn.contMDiff_cutoff_BCNT` (consumer: every family cutoff is smooth).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

namespace SlimCentreOn

variable {β₁ Δ σs : ℝ} {K : ℕ} {j : X}

/-- The LC85 cutoff of a regional slim centre, as a function on the carrier (the packet's cutoff;
twin of `SlimCentre.cutoff` with the carrier's own completeness). -/
def cutoff_BCNT (S : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) : X → ℝ :=
  let P := S.packet
  letI := S.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  letI : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  P.cutoff

/-- The closed support of a regional slim cutoff lies in the physical ball
`B̄(j, 0.91·10⁶Δρ(j))`. -/
theorem tsupport_cutoff_subset_BCNT (S : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) :
    tsupport S.cutoff_BCNT ⊆ closedBall j (91 / 100 * (10 ^ 6 * Δ) * ρ j) := by
  intro x hx
  have hr := hρ j
  let P := S.packet
  let iZ := S.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have h := (P.tsupport_cutoff hx).1
  have h' : (ρ j)⁻¹ * @dist X mX.toDist x j ≤ 91 / 100 * (10 ^ 6 * Δ) := h
  rw [inv_mul_le_iff₀ hr] at h'
  change @dist X mX.toDist x j ≤ 91 / 100 * (10 ^ 6 * Δ) * ρ j
  linarith

/-- A regional slim cutoff is smooth. -/
theorem contMDiff_cutoff_BCNT (S : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ S.cutoff_BCNT := by
  let P := S.packet
  let iZ := S.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact P.contMDiff_cutoff

/-- A regional slim cutoff takes values in `[0, 1]`. -/
theorem cutoff_mem_Icc_BCNT (S : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) (x : X) :
    S.cutoff_BCNT x ∈ Icc (0 : ℝ) 1 := by
  let P := S.packet
  let iZ := S.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact P.cutoff_mem_Icc x

end SlimCentreOn

namespace SlimFamilyOn

variable {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {U₁ U₂ : Set X}

open Classical in
/-- The actual slim cutoff at `j` of a regional slim family (zero off the centres). -/
def cutoff_BCNT (S : SlimFamilyOn X g hmetric ρ hρ β Δ σs K U₁ U₂) (j : X) : X → ℝ :=
  if hj : j ∈ S.centres then (S.centre j hj).cutoff_BCNT else 0

theorem cutoff_BCNT_of_mem (S : SlimFamilyOn X g hmetric ρ hρ β Δ σs K U₁ U₂) {j : X}
    (hj : j ∈ S.centres) : S.cutoff_BCNT j = (S.centre j hj).cutoff_BCNT := by
  unfold cutoff_BCNT
  rw [dite_eq_left hj]

/-- The closed support of every actual slim cutoff lies in `B̄(j, 0.91·10⁶Δρ(j))`. -/
theorem tsupport_cutoff_subset_BCNT (S : SlimFamilyOn X g hmetric ρ hρ β Δ σs K U₁ U₂) (j : X) :
    tsupport (S.cutoff_BCNT j) ⊆ closedBall j (91 / 100 * (10 ^ 6 * Δ) * ρ j) := by
  by_cases hj : j ∈ S.centres
  · rw [S.cutoff_BCNT_of_mem hj]
    exact (S.centre j hj).tsupport_cutoff_subset_BCNT
  · have h0 : S.cutoff_BCNT j = 0 := by
      unfold cutoff_BCNT
      rw [dite_eq_right hj]
    rw [h0, tsupport_zero]
    exact empty_subset _

/-- **Consumer**: every actual slim cutoff of a regional slim family is smooth. -/
theorem contMDiff_cutoff_BCNT (S : SlimFamilyOn X g hmetric ρ hρ β Δ σs K U₁ U₂) (j : X) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (S.cutoff_BCNT j) := by
  by_cases hj : j ∈ S.centres
  · rw [S.cutoff_BCNT_of_mem hj]
    exact (S.centre j hj).contMDiff_cutoff_BCNT
  · have h0 : S.cutoff_BCNT j = fun _ => 0 := by
      unfold cutoff_BCNT
      rw [dite_eq_right hj]
      rfl
    rw [h0]
    exact contMDiff_const

end SlimFamilyOn

end DifferentialGeometry.Geometry.Collapse
