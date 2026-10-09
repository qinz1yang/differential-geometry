import DifferentialGeometry.Geometry.Collapse.LocalExport.CircleFamily

/-!
# Consumers of the LC87 circle family

* `CircleFamily.exists_cutoff_eq_one`: stratum exhaustion — every point of the two-stratum lies in
  the plateau of the cutoff of some selected circle chart.
* `CircleFamily.nonempty_circle_diffeomorph`: in dimension three every fibre of every selected
  chart is diffeomorphic to the circle (fibre type, LC83).
* `eventually_two_stratum_exhausted_by_circle_family`: on one late tail of the closed standing
  sequence, the family of `eventually_nonempty_circleFamily` exhausts the two-stratum by plateaus.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u

namespace CircleFamily

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : Type u} [mX : MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ}

/-- Stratum exhaustion: every two-stratum point lies in the plateau of a selected cutoff. -/
theorem exists_cutoff_eq_one (F : CircleFamily I X ρ hρ β) {p : X}
    (hp : p ∈ scaledSplittingStratum.{u, 0} ρ hρ β 2) :
    ∃ j ∈ F.centres, F.cutoff j p = 1 := by
  obtain ⟨j, hj, hsub⟩ := F.covers p hp
  exact ⟨j, hj, F.plateau j hj p (hsub (mem_ball_self (hρ p)))⟩

/-- Fibre type: in dimension three every fibre of a selected circle chart is a circle. -/
theorem nonempty_circle_diffeomorph (F : CircleFamily I X ρ hρ β)
    (hdim : Module.finrank ℝ E = 3) {j : X} (hj : j ∈ F.centres) :
    let c := F.chart j hj
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    ∀ z : planeBallOpens 100,
      let f := diskPreimageMap (ball c.center 200) isOpen_ball c.coord
        c.contMDiffOn_coord.continuousOn 100
      letI := regularFiberChartedSpace f z
        (contMDiff_diskPreimageMap isOpen_ball c.contMDiffOn_coord 100)
        (fun x _ ↦ surjective_mfderiv_diskPreimageMap isOpen_ball c.contMDiffOn_coord c.rank 100 x)
      Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯
        {x // f x = z}) := by
  intro c z
  let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  exact c.nonempty_circle_diffeomorph hdim z

end CircleFamily

section Late

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- On one late tail of the closed standing sequence, the circle family of
`eventually_nonempty_circleFamily` exhausts the two-stratum of its scale by cutoff plateaus. -/
theorem eventually_two_stratum_exhausted_by_circle_family (hdim : Module.finrank ℝ E = 3) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ β : ℕ → ℝ, 0 < β 2 → β 2 ≤ β₀ → ∀ σ : ℝ, 0 < σ → σ < 1 → σ ≤ a₂ →
      ∀ Λ : ℝ, 0 < Λ → Λ * 2000000 ≤ 1 / 100 → ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        ∃ F : CircleFamily I (X i) ρ hρpos β,
          ∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 2, ∃ j ∈ F.centres, F.cutoff j p = 1 := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_circleFamily.{uE, uH, u} (E := E) (H := H)
    (I := I) hdim
  refine ⟨a₂, ha₂, fun γ hγ hγone => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγone
  refine ⟨β₀, hβ₀, hβ₀a, fun β hβ hββ₀ σ hσ hσ1 hσa Λ hΛ hΛsmall => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h β hβ hββ₀ σ hσ hσ1 hσa Λ hΛ hΛsmall
  refine ⟨w₀, hw₀, fun w hw hww₀ hwc X _ _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [h w hw hww₀ hwc X g hmetric α hα hstand] with i hi
  obtain ⟨ρ, hρpos, -, -, -, ⟨F⟩⟩ := hi
  exact ⟨ρ, hρpos, F, fun p hp => F.exists_cutoff_eq_one hp⟩

end Late

end DifferentialGeometry.Geometry.Collapse
