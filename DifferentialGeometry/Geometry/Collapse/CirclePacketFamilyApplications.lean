import DifferentialGeometry.Geometry.Collapse.CirclePacketFamily

/-!
# Consumer of the circle packet family: the circle cutoffs cover the stratum

`exists_circle_packet_family` applied once: every point of `S` has a selected center `i` whose
packet cutoff `ζ` is smooth, `[0,1]`-valued, compactly supported inside the physical ball
`B(i, 200 ρ_i)` and equal to one at that point; the selection is finite with the numerical
multiplicity bound on the support balls.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The circle cutoffs cover the stratum (consumer of CF2).** -/
theorem exists_circle_cutoff_cover :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ (γ : ℝ), 0 < γ → γ < 1 / 10 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)], Module.finrank ℝ E = 3 →
      ∀ (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        [ConnectedSpace M] [CompactSpace M]
        (g : SmoothRiemannianMetric I M), IsMetricNorm (I := I) g →
      ∀ (ρ : M → ℝ) {Λ : NNReal}, LipschitzWith Λ ρ → ∀ (hρpos : ∀ p, 0 < ρ p),
        (Λ : ℝ) * 2000000 ≤ 1 / 100 →
      ∀ (S : Set M) (Y : S → Type w) [∀ p, MetricSpace (Y p)] (a : ∀ p, Y p)
        (C : S → Type v) [∀ p, MetricSpace (C p)] [∀ p, CompleteSpace (C p)] (c : ∀ p, C p)
        (σ β : S → ℝ),
      (∀ p : S, @KleinerLottApprox M (C p)
          (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p (c p) (σ p)) →
      (∀ p : S, @KleinerLottApprox M _ (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
          (WithLp.toLp 2 ((0 : ℝ²), a p)) (β p)) →
      (∀ p : S,
        (∀ x y : C p, ∀ e : ℝ, 0 < e →
          ∃ ξ : unitInterval → C p, Continuous ξ ∧ ξ 0 = x ∧ ξ 1 = y ∧
            eVariationOn ξ univ < ENNReal.ofReal (dist x y + e)) ∧
        dimH (univ : Set (C p)) ≤ 2 ∧ fourPointComparison 0 (univ : Set (C p)) ∧
        σ p ≤ a₂ ∧ β p ≤ β₀ ∧
        (∀ y ∈ ball (p : M) ((β p)⁻¹ * ρ p),
          SectionalBoundedBelowAt g y (-(β p ^ 2 * (ρ p)⁻¹ ^ 2))) ∧
        ∀ y ∈ ball (p : M) ((3 * 2000000 + 2 / 3) * ρ p),
          SectionalBoundedBelowAt g y (-((2000000 * ρ p) ^ 2)⁻¹)) →
      ∃ J : Set M, J ⊆ S ∧ J.Finite ∧
        (∀ x : M, ((J ∩ {i | x ∈ ball i (2000000 * ρ i)}).ncard : ℝ) ≤
          modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
            modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) ∧
        ∀ p ∈ S, ∃ i ∈ J, ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
          (∀ x, ζ x ∈ Icc 0 1) ∧ ζ p = 1 ∧ ∀ x, ζ x ≠ 0 → dist x i < 200 * ρ i := by
  obtain ⟨a₂, ha₂, hCF2⟩ := exists_circle_packet_family.{uE, uH, u, v, w}
  refine ⟨a₂, ha₂, fun γ hγ hγone => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hfam⟩ := hCF2 γ hγ hγone
  refine ⟨β₀, hβ₀, hβ₀a, ?_⟩
  intro E _ _ _ _ hdim H _ I _ M m _ _ _ _ _ _ _ _ _ g hEnorm ρ Λ hρ hρpos hΛ S Y _ a C _ _ c
    σ β f F hdata
  obtain ⟨J, hJS, hfin, -, hcov, hmult, hpack⟩ :=
    hfam E hdim H I M g hEnorm ρ hρ hρpos hΛ S Y a C c σ β f F hdata
  refine ⟨J, hJS, hfin, hmult, fun p hp => ?_⟩
  obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp (hcov hp)
  obtain ⟨η, hη, hrank, -, -, -, -, -, h8, -, -, ζ, hζ, hsupp, hζ01, hζ1, hζnz⟩ := hpack i hi
  have hρi := hρpos i
  have hpi' : (ρ i)⁻¹ * dist p i < 2 := by
    rw [inv_mul_lt_iff₀ hρi]
    rw [mem_ball] at hpi
    linarith
  refine ⟨i, hi, ζ, hζ, hsupp, hζ01, hζ1 p ?_ (h8 p hpi'), fun x hx => ?_⟩
  · change (ρ i)⁻¹ * dist p i < 200
    linarith
  · have hx' : (ρ i)⁻¹ * dist x i < 200 := (hζnz x hx).1
    rw [inv_mul_lt_iff₀ hρi] at hx'
    linarith

end DifferentialGeometry.Geometry.Collapse
