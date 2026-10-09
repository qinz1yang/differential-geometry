import DifferentialGeometry.Geometry.Collapse.CirclePacketFamilyLate

/-!
# Consumer of CF3: closed circle cutoff supports on the late tail

`eventually_circle_packet_family` applied once: on one late tail, every point with a
`(2, β)`-splitting at scale `ρ` has a selected center `j` whose packet cutoff `ζ` is smooth,
`[0,1]`-valued, equal to one at that point, with CLOSED support inside the physical ball
`B(j, 200 ρ_j)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

universe uE uH u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **Late-tail closed circle cutoff cover (consumer of CF3).** -/
theorem eventually_circle_cutoff_closed_cover (hdim : Module.finrank ℝ E = 3) {Λ : ℝ} (hΛ : 0 < Λ)
    (hΛsmall : Λ * 2000000 ≤ 1 / 100) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ β : ℝ, 0 < β → β ≤ β₀ → ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
      ∀ (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧ LipschitzWith (Real.toNNReal Λ) ρ ∧
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        ∃ J : Set (X i), J.Finite ∧
          ∀ p, @HasEuclideanSplitting.{u, 0} (X i)
            ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p 2 β →
          ∃ j ∈ J, ∃ ζ : X i → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ (∀ x, ζ x ∈ Icc 0 1) ∧ ζ p = 1 ∧
            ∀ x ∈ tsupport ζ, dist x j < 200 * ρ j := by
  obtain ⟨a₂, ha₂, hCF3⟩ := eventually_circle_packet_family (E := E) (H := H) (I := I) hdim hΛ
    hΛsmall
  refine ⟨a₂, ha₂, fun γ hγ hγone => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hβ⟩ := hCF3 γ hγ hγone
  refine ⟨β₀, hβ₀, hβ₀a, fun β hβpos hββ₀ => ?_⟩
  obtain ⟨w₀, hw₀, hw⟩ := hβ β hβpos hββ₀
  refine ⟨w₀, hw₀, fun w hw0 hww₀ hwc X mX _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [hw w hw0 hww₀ hwc X g hmetric α hα hstand] with i hi
  obtain ⟨ρ, hρpos, hρsm, hρlip, hρb, J, hfin, -, -, hcov, -, hpack⟩ := hi
  refine ⟨ρ, hρpos, hρsm, hρlip, hρb, J, hfin, fun p hp => ?_⟩
  obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp (hcov hp)
  obtain ⟨Y, mY, a, F, η, hη, hrank, -, -, -, -, -, h8, -, -, ζ, hζ, -, hζ01, hζ1, -, htsupp⟩ :=
    hpack j hj
  have hρj := hρpos j
  have hpj' : (ρ j)⁻¹ * dist p j < 2 := by
    rw [inv_mul_lt_iff₀ hρj]
    rw [mem_ball] at hpj
    linarith
  refine ⟨j, hj, ζ, hζ, hζ01, hζ1 p ?_ (h8 p hpj'), fun x hx => ?_⟩
  · change (ρ j)⁻¹ * dist p j < 200
    linarith
  · have hx' : (ρ j)⁻¹ * dist x j < 200 := (htsupp hx).1
    rw [inv_mul_lt_iff₀ hρj] at hx'
    linarith

end DifferentialGeometry.Geometry.Collapse
