import DifferentialGeometry.Geometry.Fibration.ActualBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight

/-!
# Boundary port (lane B-PORT-A): circle / slim / edge coordinate Lipschitz and cutoff germs (CGP02 (b) inputs)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualBlockBudgets.lean` by `build-logs/scratch/B-PORT-A/gen_shared.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Profiles

end Profiles

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

end Generic

section Families

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}
  {τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The circle chart coordinate `η_j : X → ℝ²` of the family (normalized at `j`); the coordinate
of the circle block of `𝓔⁰`. -/
def cgpCircleCoord_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (j : X) (hj : j ∈ L.circle.centres) : X → ℝ² :=
  let c := L.circle.chart j hj
  letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  c.coord

/-- The circle coordinate `η_j` is `2/ρ(j)`-Lipschitz on the physical ball `B(j, 200ρ(j))`. -/
theorem cgpCircleCoord_lipschitz_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) {j : X}
    (hj : j ∈ L.circle.centres) :
    ∀ y ∈ ball j (200 * ρ j), ∀ z ∈ ball j (200 * ρ j),
      ‖cgpCircleCoord_BAUGP L j hj y - cgpCircleCoord_BAUGP L j hj z‖ ≤ 2 / ρ j * dist y z := by
  intro y hy z hz
  have hc := L.circle.chart_center j hj
  have hrj := hρ j
  have hy1 : (ρ j)⁻¹ * dist y j < 200 := inv_mul_dist_lt_of_mem_ball_LC87 hrj hy
  have hz1 : (ρ j)⁻¹ * dist z j < 200 := inv_mul_dist_lt_of_mem_ball_LC87 hrj hz
  have he : ((2 : NNReal) : ℝ) * ((ρ j)⁻¹ * dist y z) = 2 / ρ j * dist y z := by
    push_cast
    ring
  let c := L.circle.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hc' : c.center = j := hc
  have hy' : y ∈ @ball X mR.toPseudoMetricSpace c.center 200 := by
    change (ρ j)⁻¹ * @dist X mX.toDist y c.center < 200
    rw [hc']
    exact hy1
  have hz' : z ∈ @ball X mR.toPseudoMetricSpace c.center 200 := by
    change (ρ j)⁻¹ * @dist X mX.toDist z c.center < 200
    rw [hc']
    exact hz1
  have h := c.lipschitz.dist_le_mul y hy' z hz'
  change @dist ℝ² _ (c.coord y) (c.coord z) ≤
    ((2 : NNReal) : ℝ) * ((ρ j)⁻¹ * @dist X mX.toDist y z) at h
  change ‖c.coord y - c.coord z‖ ≤ 2 / ρ j * @dist X mX.toDist y z
  rw [← dist_eq_norm]
  linarith

/-- The circle coordinate is smooth on the physical ball `B(j, 200ρ(j))`. -/
theorem cgpCircleCoord_contMDiffOn_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) {j : X}
    (hj : j ∈ L.circle.centres) :
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (cgpCircleCoord_BAUGP L j hj) (ball j (200 * ρ j)) := by
  have hc := L.circle.chart_center j hj
  have hrj := hρ j
  let c := L.circle.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hc' : c.center = j := hc
  refine c.contMDiffOn_coord.mono fun x hx => ?_
  have hd := @inv_mul_dist_lt_of_mem_ball_LC87 X mX ρ j x 200 hrj hx
  change (ρ j)⁻¹ * @dist X mX.toDist x c.center < 200
  rw [hc']
  exact hd

/-- Near a point of the physical ball `B(j, 200ρ(j))` the circle cutoff is `ψ ∘ η_j`
(LC87 packet (ii)). -/
theorem circle_cutoff_eventuallyEq_KA2_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) {j : X}
    (hj : j ∈ L.circle.centres) {x : X} (hx : x ∈ ball j (200 * ρ j)) :
    L.circle.cutoff j =ᶠ[𝓝 x]
      fun y => circleCutoffBump_LC87 (cgpCircleCoord_BAUGP L j hj y) := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  have h : L.circle.cutoff j y = if dist y j < 200 * ρ j then
      circleCutoffBump_LC87 (cgpCircleCoord_BAUGP L j hj y) else 0 :=
    L.circle_cutoff_apply_BAUGP hj y
  simp only [h, mem_ball.mp hy, ↓reduceIte]

/-- The slim coordinate is `(1 + σ)/ρ(j)`-Lipschitz for the physical distance. -/
theorem slimCentre_coord_lipschitz_KA2_BAUGP {β₁ : ℝ} {j : X}
    (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) (hσs : 0 ≤ 1 + σs) (y z : X) :
    |c.coord_BCG2 y - c.coord_BCG2 z| ≤ (1 + σs) / ρ j * dist y z := by
  have hrj := hρ j
  have he : ((Real.toNNReal (1 + σs) : NNReal) : ℝ) * ((ρ j)⁻¹ * dist y z) =
      (1 + σs) / ρ j * dist y z := by
    rw [Real.coe_toNNReal _ hσs]
    field_simp
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have h := P.lipschitz.dist_le_mul y z
  change |P.coord y - P.coord z| ≤
    ((Real.toNNReal (1 + σs) : NNReal) : ℝ) * ((ρ j)⁻¹ * @dist X mX.toDist y z) at h
  change |P.coord y - P.coord z| ≤ (1 + σs) / ρ j * @dist X mX.toDist y z
  linarith

/-- Where the slim cutoff is nonzero, `|η_j| < 89·10⁴Δ`. -/
theorem slimCentre_abs_coord_lt_of_cutoff_ne_zero_KA2_BAUGP {β₁ : ℝ} {j : X}
    (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) {y : X} (hy : c.cutoff_BCNT y ≠ 0) :
    |c.coord_BCG2 y| < 89 * 10 ^ 4 * Δ := by
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact (P.cutoff_ne_zero y hy).2

theorem slimFamily_cutoff_eq_KA2_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) {j : X}
    (hj : j ∈ L.slim.centres) : L.slim.cutoff_BCNT j = (L.slim.centre j hj).cutoff_BCNT := by
  unfold SlimFamilyOn.cutoff_BCNT
  rw [dite_eq_left hj]

/-- Near a point of the physical ball `B(j, 10⁶Δρ(j))` the slim cutoff is `φ(η_j/(10⁵Δ))`
(LC87 packet (ii)). -/
theorem slim_cutoff_eventuallyEq_KA2_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) {j : X}
    (hj : j ∈ L.slim.centres) {x : X} (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j)) :
    L.slim.cutoff_BCNT j =ᶠ[𝓝 x]
      fun y => slimCutoffProfile_LC87 ((L.slim.centre j hj).coord_BCG2 y / (10 ^ 5 * Δ)) := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  rw [slimFamily_cutoff_eq_KA2_BAUGP L hj, L.slim_cutoff_apply_BAUGP hj y]
  simp only [mem_ball.mp hy, ↓reduceIte]

/-- The edge coordinate `η_j` is `(1 + σ)/ρ(j)`-Lipschitz for the physical distance. -/
theorem EdgeFamilyOn.coord_lipschitz_KA2_BAUGP {β : ℕ → ℝ}
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (hσc : 0 ≤ 1 + σc) {j : X}
    (hj : j ∈ F.centres) (y z : X) :
    |F.coord_BAUGA j y - F.coord_BAUGA j z| ≤ (1 + σc) / ρ j * dist y z := by
  have hrj := hρ j
  have he : ((Real.toNNReal (1 + σc) : NNReal) : ℝ) * ((ρ j)⁻¹ * dist y z) =
      (1 + σc) / ρ j * dist y z := by
    rw [Real.coe_toNNReal _ hσc]
    field_simp
  rw [F.coord_BAUGA_of_mem hj]
  unfold EdgeFamilyOn.coord_BCG1
  let C := F.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have h := C.lipschitz.dist_le_mul y z
  change |C.coord y - C.coord z| ≤
    ((Real.toNNReal (1 + σc) : NNReal) : ℝ) * ((ρ j)⁻¹ * @dist X mX.toDist y z) at h
  change |C.coord y - C.coord z| ≤ (1 + σc) / ρ j * @dist X mX.toDist y z
  linarith

/-- **The edge height near a collar point** (LFR38's collar, LC84 item 3): at a collar point `x` of
the chart at `j`, `ρ(x)/ρ(j) ≥ 99/100` and `t = F/ρ` is `(1 + γ)/ρ(x)`-Lipschitz on the physical
ball `B(x, 100ρ(x))`. -/
theorem EdgeFamilyOn.height_lipschitz_of_collar_KA2_BAUGP {β : ℕ → ℝ}
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) {j : X} (hj : j ∈ F.centres)
    {x : X} (hx : x ∈ ball j (100 * Δ * ρ j)) (hcoord : |F.coord_BAUGA j x| ≤ 10 * Δ)
    (h1 : Δ / 10 ≤ F.smoothing x / ρ x) (h2 : F.smoothing x / ρ x ≤ 10 * Δ) :
    99 / 100 ≤ ρ x / ρ j ∧ ∀ y ∈ ball x (100 * ρ x), ∀ z ∈ ball x (100 * ρ x),
      |F.smoothing y / ρ y - F.smoothing z / ρ z| ≤ (1 + γc) / ρ x * dist y z := by
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hrx := hρ x
  let Fs := F.smoothing
  have hq : ∀ y, Fs y / ρ j / (ρ y / ρ j) = Fs y / ρ y := fun y => by
    have := hρ y
    field_simp
  have hball : ∀ y ∈ ball x (100 * ρ x), (ρ j)⁻¹ * dist y x < 100 * (ρ x / ρ j) := by
    intro y hy
    have := mem_ball.mp hy
    rw [inv_mul_lt_iff₀ hrj]
    field_simp
    linarith
  have hlipeq : ∀ y z : X, (1 + γc) * ((ρ j)⁻¹ * dist y z / (ρ x / ρ j)) =
      (1 + γc) / ρ x * dist y z := fun y z => by
    field_simp
  rw [F.coord_BAUGA_of_mem hj] at hcoord
  unfold EdgeFamilyOn.coord_BCG1 at hcoord
  let C := F.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  have hmem : x ∈ ball C.center (100 * Δ) := by
    rw [hc']
    exact hd
  have hcoord' : |C.coord x| ≤ 10 * Δ := hcoord
  have h1' : Δ / 10 ≤ Fs x / ρ j / (ρ x / ρ j) := by rw [hq]; exact h1
  have h2' : Fs x / ρ j / (ρ x / ρ j) ≤ 10 * Δ := by rw [hq]; exact h2
  obtain ⟨hqq, -, -, -, hJlip, -⟩ := C.collar x hmem hcoord' h1' h2'
  refine ⟨hqq.1, fun y hy z hz => ?_⟩
  have hy' : y ∈ ball x (100 * (ρ x / ρ j)) := hball y hy
  have hz' : z ∈ ball x (100 * (ρ x / ρ j)) := hball z hz
  have h := (abs_euclid_one_sub_le_KA2 _ _).trans (hJlip y hy' z hz')
  change |Fs y / ρ j / (ρ y / ρ j) - Fs z / ρ j / (ρ z / ρ j)| ≤
    (1 + γc) * ((ρ j)⁻¹ * @dist X mX.toDist y z / (ρ x / ρ j)) at h
  rw [hq y, hq z, hlipeq y z] at h
  exact h

end Families


end DifferentialGeometry.Geometry.Collapse
