import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementWitnessBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeBCutoff
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBF
import DifferentialGeometry.Geometry.Fibration.ActualEdgeLevelDiskEFE

/-!
# O-WF G6a: EDP03's original buffer and the original zero disk on the revised edge charts

Boundary twins (on a complete, proper carrier; no compactness) of the closed
`edp03_buffer` (`Fibration/ActualEdgeBuffer.lean`) and
`LocalChartPacketsC14.edge_smoothDisk_EFE` (`Fibration/ActualEdgeLevelDiskEFE.lean`), for the
revised edge family `edgeB` of `LocalPacketsOnB` / `LocalPacketsOnBF`:

* `LocalPacketsOnB.isOpen_edgeBSource_OWF`: the original source
  `Y_j = {p ∈ B(j, 100Δρ(j)) : |η_j| < 5Δ, t < 5Δ}` is open.
* `LocalPacketsOnB.edgeB_buffer_OWF` (EDP03): `Y_j ⊆ B(j, 8Δρ(j))`; `η_j` and `H₀` smooth on
  `Y_j`; at every point of `Y_j` a vector of `g`-length `ρ(j)` with `dη_j > .99`; a compact
  `Q_j ⊆ Y_j` with `{|η_j| < 4.2Δ, t < 4.2Δ}` (EBuf, slightly enlarged) in its interior. The
  compactness of the closed buffer comes from `[ProperSpace X]` (the boundary carrier `W°` is
  proper by Hopf–Rinow).
* `LocalPacketsOnBF.edgeB_smoothDisk_OWF`: the original zero fibre `{η_j = 0, H₀ ≤ 4Δ}` of
  `B(j, 100Δρ(j))` is the range of a smooth embedding of `ClosedCell 2`, boundary circle onto the
  rim `{H₀ = 4Δ}` (LC84's disk packet `edgeDiskB`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The revised edge coordinate `η_j` is continuous on the carrier. -/
theorem LocalPacketsOnB.continuous_edgeBCoord_OWF
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) {j : X} (hj : j ∈ F.edgeB.centres) :
    Continuous (F.edgeB.coord_BAUGA j) := by
  rw [F.edgeB.coord_BAUGA_of_mem hj]
  unfold EdgeFamilyOn.coord_BCG1
  let C := F.edgeB.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact C.lipschitz.continuous

/-- The normalized height `t = F/ρ` of the revised edge family is continuous. -/
theorem LocalPacketsOnB.continuous_edgeBHeight_OWF
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) :
    Continuous (fun y => F.edgeB.smoothing y / ρ y) :=
  F.edgeB.lipschitz_smoothing.continuous.div F.lipschitz_scale.continuous (fun y => (hρ y).ne')

/-- **The original source `Y_j` is open.** -/
theorem LocalPacketsOnB.isOpen_edgeBSource_OWF
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) {j : X} (hj : j ∈ F.edgeB.centres) :
    IsOpen {p | p ∈ ball j (100 * Δ * ρ j) ∧ |F.edgeB.coord_BAUGA j p| < 5 * Δ ∧
      F.edgeB.smoothing p / ρ p < 5 * Δ} :=
  isOpen_ball.inter ((isOpen_lt (continuous_abs.comp (F.continuous_edgeBCoord_OWF hj))
    continuous_const).inter (isOpen_lt F.continuous_edgeBHeight_OWF continuous_const))

/-- **EDP03 on a revised edge chart** (see the module docstring). -/
theorem LocalPacketsOnB.edgeB_buffer_OWF [ProperSpace X]
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂)
    (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) {j : X} (hj : j ∈ F.edgeB.centres) :
    let Y : Set X := {p | p ∈ ball j (100 * Δ * ρ j) ∧ |F.edgeB.coord_BAUGA j p| < 5 * Δ ∧
      F.edgeB.smoothing p / ρ p < 5 * Δ}
    Y ⊆ ball j (8 * Δ * ρ j) ∧
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (F.edgeB.coord_BAUGA j) Y ∧
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ F.edgeB.smoothing ρ) Y ∧
    (∀ p ∈ Y, ∃ w : TangentSpace 𝓘(ℝ, E3) p, g.inner p w w = ρ j ^ 2 ∧
      99 / 100 < mvfderiv 𝓘(ℝ, E3) (F.edgeB.coord_BAUGA j) p w) ∧
    ∃ Q : Set X, IsCompact Q ∧ Q ⊆ Y ∧
      {p | p ∈ ball j (100 * Δ * ρ j) ∧ |F.edgeB.coord_BAUGA j p| < 21 / 5 * Δ ∧
        F.edgeB.smoothing p / ρ p < 21 / 5 * Δ} ⊆ interior Q := by
  intro Y
  have hΔ0 : 0 < Δ := by linarith
  have hrj := hρ j
  have hcoordc := F.continuous_edgeBCoord_OWF hj
  have htc := F.continuous_edgeBHeight_OWF
  have hencl := fun {x : X} {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 5)
      (hx : x ∈ ball j (100 * Δ * ρ j)) (hfx : |F.edgeB.coord_BAUGA j x| ≤ a * Δ)
      (htx : F.edgeB.smoothing x / ρ x ≤ a * Δ) =>
    F.edgeB_enclosure_BCF2K hΔ0 hμ hτ hlam hj ha0 ha hx hfx htx
  have hY8 : Y ⊆ ball j (8 * Δ * ρ j) := fun p hp =>
    (hencl (by norm_num) le_rfl hp.1 hp.2.1.le hp.2.2.le).1
  refine ⟨hY8, (F.edgeB.contMDiffOn_coord_BAUGA hj).mono fun p hp => hp.1, ?_, ?_, ?_⟩
  · -- `H₀ = Δψ(t/Δ)` is smooth on `Y`
    intro p hp
    refine ContMDiffAt.contMDiffWithinAt ?_
    rcases lt_or_ge (F.edgeB.smoothing p / ρ p) Δ with hlow | hhigh
    · have hev : ∀ᶠ y in 𝓝 p, F.edgeB.smoothing y / ρ y < Δ :=
        htc.continuousAt.eventually (gt_mem_nhds hlow)
      have he : edgeRowHeight Δ F.edgeB.smoothing ρ =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
        filter_upwards [hev] with y hy
        unfold edgeRowHeight
        rw [edgeSublevelProfile_eq_zero (by rw [div_le_iff₀ hΔ0]; linarith), mul_zero]
      exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq he
    · have ht := F.edgeB.contMDiffAt_height_of_collar_BAUGA hj hp.1 (by linarith [hp.2.1])
        (by linarith) (by linarith [hp.2.2])
      have hH : edgeRowHeight Δ F.edgeB.smoothing ρ =
          fun y => Δ * edgeSublevelProfile (F.edgeB.smoothing y / ρ y / Δ) := rfl
      rw [hH]
      exact contMDiffAt_const.mul
        (contDiff_edgeSublevelProfile.comp_contMDiffAt (ht.div_const Δ))
  · -- `dη_j > .99` on a unit vector of `ρ(j)⁻²g`
    intro p hp
    have hd : (ρ j)⁻¹ * dist p j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hrj hp.1
    have hcen := F.edgeB.chart_center j hj
    rw [F.edgeB.coord_BAUGA_of_mem hj]
    unfold EdgeFamilyOn.coord_BCG1
    let C := F.edgeB.chart j hj
    let hMc : CompleteSpace X := ‹CompleteSpace X›
    let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let kR : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g
    have hcen' : C.center = j := hcen
    let _ := C.instY
    have hb0 : 0 < b := C.split.error_pos
    have hbΔ : b ≤ 1 / 1000 := by
      have : b * 1000 ≤ b * (1000 * Δ) := by nlinarith
      linarith
    have hinv : 300 * Δ + 2 * b < b⁻¹ := by
      have h1 : 1000 * Δ ≤ b⁻¹ := by
        rw [le_inv_comm₀ (by positivity) hb0]
        rw [div_eq_inv_mul] at hbΔ
        have : b ≤ 1 / (1000 * Δ) := by
          rw [le_div_iff₀ (by positivity)]
          linarith
        rwa [one_div] at this
      linarith
    have hpC : p ∈ ball C.center (100 * Δ) := by rw [hcen']; exact hd
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
    have htest := C.test
    obtain ⟨w, hw, hlt⟩ := exists_unit_lt_mvfderiv_of_rankOne gR hnR C.split htest
      (r := 100 * Δ) le_rfl (by linarith) (by linarith) (by linarith) hpC
    refine ⟨w, ?_, ?_⟩
    · have hw' : (ρ j)⁻¹ ^ 2 * g.inner p w w = 1 := hw
      have hr2 : 0 < ρ j ^ 2 := by positivity
      field_simp at hw'
      linarith
    · refine lt_of_le_of_lt ?_ hlt
      rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
      nlinarith
  · -- the compact buffer `Q_j`
    let Qb : Set X := {p | dist p j ≤ 7 * Δ * ρ j ∧ |F.edgeB.coord_BAUGA j p| ≤ 21 / 5 * Δ ∧
      F.edgeB.smoothing p / ρ p ≤ 21 / 5 * Δ}
    have hQc : IsClosed Qb :=
      (isClosed_le (continuous_id.dist continuous_const) continuous_const).inter
        ((isClosed_le (continuous_abs.comp hcoordc) continuous_const).inter
          (isClosed_le htc continuous_const))
    have hQk : IsCompact Qb :=
      (isCompact_closedBall j (7 * Δ * ρ j)).of_isClosed_subset hQc
        (fun p hp => mem_closedBall.mpr hp.1)
    refine ⟨Qb, hQk, fun p hp => ⟨mem_ball.mpr (by nlinarith [hp.1]), by
      linarith [hp.2.1], by linarith [hp.2.2]⟩, fun p hp => ?_⟩
    let O : Set X := {p | dist p j < 7 * Δ * ρ j ∧ |F.edgeB.coord_BAUGA j p| < 21 / 5 * Δ ∧
      F.edgeB.smoothing p / ρ p < 21 / 5 * Δ}
    have hO : IsOpen O :=
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
        ((isOpen_lt (continuous_abs.comp hcoordc) continuous_const).inter
          (isOpen_lt htc continuous_const))
    have h6 := (hencl (a := 21 / 5) (by norm_num) (by norm_num) hp.1 hp.2.1.le hp.2.2.le).2
      le_rfl
    have hΔρ : 0 < Δ * ρ j := mul_pos hΔ0 hrj
    have hpO : p ∈ O := ⟨by nlinarith, by linarith [hp.2.1], by linarith [hp.2.2]⟩
    exact interior_maximal (fun y (hy : y ∈ O) => (⟨hy.1.le, hy.2.1.le, hy.2.2.le⟩ : y ∈ Qb)) hO
      hpO

/-- **The original LFR28 zero disk of a revised edge chart as a smooth embedding** onto the WHOLE
original zero fibre `{η_j = 0, H₀ ≤ 4Δ}` of `B(j, 100Δρ(j))`, boundary circle onto the rim. -/
theorem LocalPacketsOnBF.edgeB_smoothDisk_OWF
    (F : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) (hΔ : 0 < Δ) {j : X} (hj : j ∈ F.edgeB.centres) :
    ∃ φ : ClosedCell 2 → X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {p | p ∈ ball j (100 * Δ * ρ j) ∧ F.edgeB.coord_BAUGA j p = 0 ∧
        edgeRowHeight Δ F.edgeB.smoothing ρ p ≤ 4 * Δ} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {p | p ∈ ball j (100 * Δ * ρ j) ∧
        F.edgeB.coord_BAUGA j p = 0 ∧ edgeRowHeight Δ F.edgeB.smoothing ρ p = 4 * Δ} := by
  have hrj := hρ j
  have hq : ∀ y, F.edgeB.smoothing y / ρ j / (ρ y / ρ j) = F.edgeB.smoothing y / ρ y :=
    fun y => by
      have := hρ y
      field_simp
  have hH : edgeRowHeight Δ (fun x => F.edgeB.smoothing x / ρ j) (fun x => ρ x / ρ j) =
      edgeRowHeight Δ F.edgeB.smoothing ρ := by
    funext y
    unfold edgeRowHeight
    rw [hq]
  set Bp : Set X := ball j (100 * Δ * ρ j) with hBp
  have hball : ∀ y, (ρ j)⁻¹ * dist y j < 100 * Δ ↔ y ∈ Bp := fun y => by
    rw [hBp, mem_ball, inv_mul_lt_iff₀ hrj]
    constructor <;> intro h <;> linarith
  have hD := F.edgeDiskB j hj
  have hcc := F.edgeB.chart_center j hj
  set η := F.edgeB.coord_BAUGA j with hηdef
  have hc0 : η = F.edgeB.coord_BCG1 j hj := F.edgeB.coord_BAUGA_of_mem hj
  let c := F.edgeB.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc : η = c.coord := hc0
  obtain ⟨P, hP⟩ := hD
  have hPc : P.coord = η := by
    rw [hc]
    exact congrArg EdgeChart.coord hP
  have hPb : ∀ y, y ∈ ball P.center (100 * Δ) ↔ y ∈ Bp := fun y => by
    have hcen : P.center = j := (congrArg EdgeChart.center hP).trans hcc
    rw [hcen, ← hball y]
    rfl
  obtain ⟨φ, hφ, hr, hb⟩ := P.exists_smoothDisk_EFE hΔ
  refine ⟨φ, hφ, ?_, ?_⟩
  · rw [hr, hH, hPc]
    ext y
    simp only [mem_ofPred_eq, hPb]
  · rw [hb, hH, hPc]
    ext y
    simp only [mem_ofPred_eq, hPb]

end DifferentialGeometry.Geometry.Collapse
