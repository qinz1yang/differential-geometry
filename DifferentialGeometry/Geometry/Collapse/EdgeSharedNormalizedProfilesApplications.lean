import DifferentialGeometry.Geometry.Collapse.EdgeSharedNormalizedProfiles
import DifferentialGeometry.Geometry.Collapse.EdgeQuotientModelDerivatives

/-!
# Consumer: the normalized LFR27.2 estimate at every centre of the shared smoothing

`exists_shared_edge_smoothing_normalized` composed with F7-LFR28B's
`abs_mvfderiv_quotient_add_inner_le` in the normalization of each centre: for the SAME `η = F/ρ`,
`|dη(w) + ⟨v, w⟩_{g_p}| ≤ (ε + 100ΔΛ) |w|_{g_p}` for every point of LFR27's collar `C` (normalized
scale `Δ`) and EVERY normalized inward nearest direction `v` — the (LFR27.2) input that the LFR28.4
binding `eventually_abs_mvfderiv_edgeQuotient_comp_sub_model_le` consumes at each centre.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [hM : CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **Concrete consumer.** One shared smoothing, and at every centre, in its normalization, the
quotient `η = F/ρ` satisfies the covector form of (LFR27.2) with error `ε + 100ΔΛ` on LFR27's collar
for every normalized inward nearest direction. -/
theorem exists_shared_edge_smoothing_normalized_quotient_pinning (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g)
    {A : Set M} (hA : IsClosed A) {P : Finset M} (hP : P.Nonempty)
    {Q : M → M → WithLp 2 (ℝ × ℝ)} {ρ : M → ℝ} (hρpos : ∀ x, 0 < ρ x) {Δ τ κ ε μ : ℝ}
    (hΔ : 0 < Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000)
    (hQp : ∀ p ∈ P, Q p p = 0)
    (hdist : ∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), ∀ y ∈ ball p (200 * (Δ * ρ p)),
      |dist (Q p x) (Q p y) - dist x y| ≤ τ * (Δ * ρ p))
    (hheight : ∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), 0 ≤ (Q p x).snd)
    (hcover : ∀ p ∈ P, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * ρ p) →
      z.snd ∈ Icc 0 (100 * (Δ * ρ p)) →
        ∃ x ∈ ball p (200 * (Δ * ρ p)), dist (Q p x) z ≤ τ * (Δ * ρ p))
    (hpA : ∀ p ∈ P, p ∈ A)
    (hborder : ∀ p ∈ P, ∀ a ∈ A ∩ ball p (190 * (Δ * ρ p)), (Q p a).snd ≤ τ * (Δ * ρ p))
    (hbordercover : ∀ p ∈ P, ∀ t : ℝ, |t| ≤ 100 * (Δ * ρ p) →
      ∃ a ∈ A ∩ ball p (190 * (Δ * ρ p)),
        dist (Q p a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p))
    (hκ : 0 ≤ κ) (hκΔ : ∀ p ∈ P, κ * (Δ * ρ p) ≤ 1 / 100)
    (hsec : ∀ p ∈ P, ∀ z ∈ ball p (1000 * (Δ * ρ p)), SectionalBoundedBelowAt g z (-κ ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1 / 100) (hμ : 0 < μ) (hμ1 : μ < 1 / 100)
    (hθ : 30 * Real.sqrt τ < ε ^ 2 / 20)
    {Λ : ℝ≥0} (hρ : LipschitzWith Λ ρ)
    (hρs : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) (hlam : 100 * Δ * Λ ≤ 1 / 100) :
    ∃ F : M → ℝ, (∀ x, 0 ≤ F x) ∧ ∀ p ∈ P,
        (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
        letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
          radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsRiemannianManifold I M :=
          radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : CompleteSpace M :=
          (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hM
        let gR : SmoothRiemannianMetric I M :=
          scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
        have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
        ∀ x ∈ closedBall p (20 * Δ) ∩ {x | 3 / 4 * Δ ≤ infDist x A ∧ infDist x A ≤ 21 / 2 * Δ},
          ∀ v ∈ minimizingDirectionsTo gR hnR A x, ∀ w : TangentSpace I x,
            |mvfderiv I (fun y => F y / ρ y) x w + gR.inner x v w| ≤
              (ε + 100 * Δ * Λ) * Real.sqrt (gR.inner x w w)) := by
  obtain ⟨F, O, -, -, hF0, -, hcent⟩ := exists_shared_edge_smoothing_normalized g hEnorm hA hP hρpos hΔ hτ hτsmall hQp hdist hheight hcover hpA hborder hbordercover hκ hκΔ hsec hε hε1 hμ hμ1 hθ hρ hρs hlam
  refine ⟨F, hF0, fun p hp => ?_⟩
  have hr : 0 < ρ p := hρpos p
  have hηf : (fun y => F y / ρ p / (ρ y / ρ p)) = fun y => F y / ρ y :=
    funext fun y => div_div_div_cancel_right₀ hr.ne' (F y) (ρ y)
  intro hmetric
  let _ := m.rescale (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ : CompleteSpace M := (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr hr)).mpr hM
  let _ := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ := radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ := radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr hr)
  intro gR hnR x hx v hv w
  obtain ⟨-, -, -, -, -, -, hgrad, hquot, -⟩ := hcent p hp
  have h := abs_mvfderiv_quotient_add_inner_le gR (hgrad x hx v hv) (hquot x hx) w
  rwa [hηf] at h

end DifferentialGeometry.Geometry.Collapse
