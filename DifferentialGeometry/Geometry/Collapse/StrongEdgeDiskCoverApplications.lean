import DifferentialGeometry.Geometry.Collapse.StrongEdgeDiskCover

/-!
# Consumer of the LFR44 disk clause: the height bound on the physical balls

`strong_edge_disk_cover_height_le`: for the ONE smoothing `F` of
`exists_shared_smoothing_strong_edge_disk_cover`, every point within `3Δρ(p)` (physical distance)
of a centre `p` has `η = F/ρ ≤ 4Δ` and is `μΔρ(p)`-close in `F` to the distance to the weak set.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

universe u w

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- The disk-domain height clause `η ≤ 4Δ` on the physical balls `B(p, 3Δρ(p))`. -/
theorem strong_edge_disk_cover_height_le (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {J : Finset M} (hJ : J.Nonempty)
    {ρ : M → ℝ} (hρpos : ∀ x, 0 < ρ x) {Λ : ℝ≥0} (hρ : LipschitzWith Λ ρ)
    (hρs : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ)
    {Δ τ κ ε μ b s b' s' : ℝ} (hΔ : 1 ≤ Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (hend : (Λ : ℝ) < s' / (100000000 * Δ ^ 2))
    (hb'domain : b' < 1 / (1000000 * Δ)) (hs'domain : s' < 1 / (1000000 * Δ))
    (hb'error : b' < τ * Δ / 1000000000) (hs'error : s' < τ * Δ / 1000000000)
    (hsb' : s < b' / 100000) (hss' : s < s' / 100000) (hbs : b < s / 100000)
    (hb : b < 1 / 100) (hsource : 100 * Δ < b⁻¹)
    (hJE : ∀ p ∈ J, @isEdgePoint.{u, w} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p Δ b s)
    (hκ : 0 ≤ κ) (hκΔ : ∀ p ∈ J, κ * (Δ * ρ p) ≤ 1 / 100)
    (hsec : ∀ p ∈ J, ∀ z ∈ ball p (1000 * (Δ * ρ p)), SectionalBoundedBelowAt g z (-κ ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1 / 100) (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 1000000)
    (hθ : 30 * Real.sqrt τ < ε ^ 2 / 20) (hlam : 100 * Δ * Λ ≤ 1 / 100) :
    ∃ F : M → ℝ, (∀ x, 0 ≤ F x) ∧ ∀ p ∈ J, ∀ x, dist x p < 3 * (Δ * ρ p) →
      F x / ρ x ≤ 4 * Δ ∧
        |F x - infDist x (closure {y | @isEdgePoint.{u, w} M
          (m.rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'})| < μ * (Δ * ρ p) := by
  obtain ⟨F, _O, _hO, _hFO, hF0, _hFL, _hdiff, hcent⟩ :=
    exists_shared_smoothing_strong_edge_disk_cover g hEnorm hJ hρpos hρ hρs hΔ hτ
      hτsmall hscale hend hb'domain hs'domain hb'error hs'error hsb' hss' hbs hb hsource hJE hκ
      hκΔ hsec hε hε1 hμ hμ1 hθ hlam
  refine ⟨F, hF0, fun p hp x hx => ?_⟩
  obtain ⟨hval, -, Y, mY, q, Fp, hdom, -⟩ := hcent p hp
  have hxb : x ∈ @ball M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).toPseudoMetricSpace p
      (3 * Δ) := by
    change (ρ p)⁻¹ * dist x p < 3 * Δ
    rw [← div_eq_inv_mul, div_lt_iff₀ (hρpos p)]
    linarith
  obtain ⟨-, -, hη⟩ := hdom hxb
  refine ⟨?_, hval x⟩
  have heq : F x / ρ p / (ρ x / ρ p) = F x / ρ x := by
    field_simp [(hρpos p).ne', (hρpos x).ne']
  rw [← heq]
  exact hη

end DifferentialGeometry.Geometry.Collapse
