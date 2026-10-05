import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroFamilyIdx

/-!
# P3b's scale-function consumer on the index-shifted sequence (lane BDRY-IDX3)

The accepted `lpa02_witnesses_at_scale_boundary_BDRY3` takes a boundary sequence at `δ_n` for ALL
`n`, which is uninhabited at `n = 0` (`δ_0 = 0`, lane FC39-BQ). This module restates it on
sequences at `δ_{n+1}` (BBR03's form), proof re-run on lane BDRY-IDX's
`lpa02_uniform_joint_zero_witnesses_boundary_BDRY2_IDX` (index changes only):

* `lpa02_witnesses_at_scale_boundary_BDRY3_IDX`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function Manifold
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry GC.Endpoint
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **The witnesses at an original scale function (index-shifted).** Sequence at `δ_{n+1}`
(BBR03's form). On the tail of P3b, for EVERY scale `ρ` on `W_n` below `2 r_p(w')` (the LC02 upper
bound of T2's scale), every centre `p ∈ U₀ = {D > 5}` has a scale `s ∈ [T, V]` with the original
buffer on `B_ĝ(p, 400 s ρ(p))` and a Kleiner–Lott `δ`-map of `((W n)°, (s ρ(p))⁻¹ d_ĝ, p)` to a
radial cone. -/
theorem lpa02_witnesses_at_scale_boundary_BDRY3_IDX :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {δ' T : ℝ}, 0 < δ' →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
        (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤)),
        (∀ n, RiemannianMetricComplete (I := 𝓡 3) (ĝ n)) →
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        letI := inducedMetricSpace (ĝ n)
        ∀ (ρ : (W n).Carrier → ℝ) (hρ : ∀ p, 0 < ρ p),
        (∀ p, ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
        ∀ (p : (W n).pieceInterior ⊤), ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) p →
        ∃ s ∈ Icc T V, ∃ hs : 0 < s,
          (∀ y ∈ Metric.ball p (400 * (s * ρ p)),
            SectionalBoundedBelowAt (ĝ n) y (-((1 / 60) ^ 2 * (s * ρ p)⁻¹ ^ 2))) ∧
          ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
            Nonempty (@KleinerLottApprox ((W n).pieceInterior ⊤) C
              ((inducedMetricSpace (ĝ n)).rescale (s * ρ p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ p))))
              mC p o δ) := by
  obtain ⟨δS, hδS, hmain⟩ := lpa02_uniform_joint_zero_witnesses_boundary_BDRY2_IDX
  refine ⟨δS, hδS, ?_⟩
  intro K hK A hA Λ w hΛ hw hwc δ' T hδ' δ₀ hδ₀ hδ₀S W _ g B hcoll hder ĝ hcomp heq
  obtain ⟨V, hTV, δ, hδ0, hδδ', hev⟩ := hmain K hK A hA hΛ hw hwc (ε := 1 / 2) (e := 1 / 80)
    (T := T) (by norm_num) (by norm_num) hδ' (by norm_num) (by norm_num) hδ₀ hδ₀S W g B hcoll
    hder ĝ hcomp heq
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [hev] with n hn ρ hρ hρw p hp
  obtain ⟨s, hsI, hs, N, mN, cN, hMN, G, q, -, -, -, -, -, -, C, mC, o, hC, -, -, Ns, tNs, cNs,
    hNs, hhom, hbuf, hφ, -⟩ := hn p hp (ρ p) (hρ p) (hρw p).le
  exact ⟨s, hsI, hs, hbuf, C, mC, o, hC, hφ⟩

end DifferentialGeometry.Geometry.Collapse
