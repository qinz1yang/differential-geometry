import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeChart
import DifferentialGeometry.Geometry.Collapse.RankOneValueCoordinates

/-!
# Producer and consumer of the LC84 edge chart

* `exists_edgeCharts_of_strong_edge_family` (LC84 items 1–3, threshold form, family level because
  the smoothing `F` of `d_A` is SHARED): LFR44's parameter chain (`exists_strong_edge_full_collar_cover`)
  with one more numerical threshold `b₁(Δ, μ, σ)` (LFR19 at `L = 100Δ`, `T = 1000Δ`, `e = μΔ`) on the
  strong quality `b`; for every complete manifold, Lipschitz smooth scale `ρ` and finite family `J`
  of strong edge points with LFR44's curvature hypotheses there is ONE `F ≥ 0`, `(1 + ε)`-Lipschitz,
  within `μΔρ(p)` of `d_A`, and at every `p ∈ J`, in the normalization `(ρ(p)⁻¹ d, ρ(p)⁻² g)`, an
  `EdgeChart` with centre `p` for `ρ/ρ(p)` and `F/ρ(p)`. All thresholds are numerical (no
  dependence on noncollapsing or derivative data), so the producer can be applied at every edge
  centre of LPA04's tail.
* consumer `EdgeChart.mem_edgeDiskDomain_center`: the centre lies in its edge disk domain with
  cutoff one, and `η_p` is within `μΔ` of the splitting coordinate on `B(p, 100Δ)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

universe uE uH uM

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **LC84 items 1–3, threshold form (family level).** -/
theorem exists_edgeCharts_of_strong_edge_family {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ → 1 ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ s b' s' : ℝ) (Λ : ℝ≥0), 0 < σ → σ ≤ σ₀ → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 ≤ κ → κ ≤ κ₀ → 100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γ / 1000 →
        (Λ : ℝ) < 1 / (1000000 * Δ) → (Λ : ℝ) < s' / (100000000 * Δ ^ 2) →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 →
        s < b' / 100000 → s < s' / 100000 →
      ∃ b₁ : ℝ, 0 < b₁ ∧ ∀ b : ℝ, 0 < b → b < b₀ → b < b₁ → b < 1 / 100 → 100 * Δ < b⁻¹ →
        b < s / 100000 →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [hM : CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (ρ : M → ℝ) (hρpos : ∀ x, 0 < ρ x) (J : Finset M),
      J.Nonempty →
      (∀ p ∈ J, @isEdgePoint.{uM, 0} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p Δ b s) →
      (∀ p ∈ J, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
        SectionalBoundedBelowAt g z (-(κ / ρ p) ^ 2)) →
      (∀ p ∈ J, ∀ z ∈ ball p (b⁻¹ * ρ p), SectionalBoundedBelowAt g z (-(b / ρ p) ^ 2)) →
      LipschitzWith Λ ρ → ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ →
      let A : Set M := closure
        {x | @isEdgePoint.{uM, 0} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b' s'}
      ∃ F : M → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
        ∀ p ∈ J, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
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
          ∃ c : EdgeChart gR hnR Δ σ μ b γ β A (fun x => ρ x / ρ p) (fun x => F x / ρ p),
            c.center = p) := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h44⟩ := exists_strong_edge_full_collar_cover
    hβ hβγ hγ hγ1
  refine ⟨min σ₀ (1 / 2), lt_min hσ₀ (by norm_num), Δ₀, hΔ₀, fun Δ hΔ hΔ1 => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, h44Δ⟩ := h44 Δ hΔ hΔ1
  refine ⟨min τ₀ (1 / 20000), lt_min hτ₀ (by norm_num), κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ s b' s' Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hlam hbudget hscale hend
    hb'domain hs'domain hb'error hs'error hsb' hss'
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨b₁, hb₁, h19⟩ := exists_rankOne_coordinate_value_tolerance
    (L := 100 * Δ) (T := 1000 * Δ) (e := μ * Δ) (σ := σ) (by positivity) (by linarith)
    (by positivity) hσ ((hσσ₀.trans (min_le_right _ _)).trans_lt (by norm_num))
  refine ⟨b₁, hb₁, ?_⟩
  intro b hb hbb₀ hbb₁ hb100 hsource hbs E _ _ _ _ H _ I _ M m _ _ _ hM _ _ _ g hEnorm ρ hρpos J
    hJ hJE hsec hsecb hρ hρs A
  have hτsmall : τ < 1 / 10000 := (hττ₀.trans (min_le_right _ _)).trans_lt (by norm_num)
  obtain ⟨F, hF0, hFL, hcent⟩ := h44Δ σ ε μ τ κ b s b' s' Λ hσ.le
    (hσσ₀.trans (min_le_left _ _)) hε hε1 hμ hμ1 hτ (hττ₀.trans (min_le_left _ _)) hθ hκ hκκ₀ hb
    hbb₀ hb100 hsource hlam hbudget hscale hend hb'domain hs'domain hb'error hs'error hsb' hss' hbs
    E H I M g hEnorm ρ hρpos J hJ hJE hsec hsecb hρ hρs
  refine ⟨F, hF0, hFL, fun p hp => ⟨(hcent p hp).1, ?_⟩⟩
  have hr : 0 < ρ p := hρpos p
  have hpA : p ∈ A := (exists_physical_coarse_border_chart hρ hρpos hΔ1 hτ hτsmall hscale hend
    hb'domain hs'domain hb'error hs'error hsb' hss' hbs p (hJE p hp)).choose_spec.2.2.2.2.1
  obtain ⟨Y, mY, q, Fp, Qn, hQn, hcl⟩ := (hcent p hp).2
  have hsecbR := radialScaled_sectional_bound g (r := b⁻¹) hr (hsecb p hp)
  have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
  let _ := m.rescale (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ : CompleteSpace M := (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr hr)).mpr hM
  let gR : SmoothRiemannianMetric I M :=
    scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
  have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
  obtain ⟨η, O, hO, hLO, hη, hηp, hηl, hval, -, -, htest⟩ :=
    h19 b hb hbb₁ E H I M gR hnR Y p q Fp hsecbR
  have hcl' := hcl η (hη.mono (ball_subset_closedBall.trans hLO)) hηl
    (fun x hx => (hval x hx).le) htest
  exact ⟨{ center := p
           rho_center := div_self hr.ne'
           center_mem := hpA
           Y := Y
           instY := mY
           q := q
           split := Fp
           Qn := Qn
           Qn_fst := hQn
           coord := η
           domain := O
           isOpen_domain := hO
           closedBall_subset_domain := hLO
           contMDiffOn_coord := hη
           coord_center := hηp
           lipschitz := hηl
           value := hval
           test := htest
           disk_subset := hcl'.1.1
           cutoff_eq_one := hcl'.1.2
           collar := hcl'.2 }, rfl⟩

section Consumer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **Consumer.** Every point of `B(p, 3Δ)` (in particular the centre) lies in the edge disk domain
`{|η_p| < 4Δ, F/ρ ≤ 4Δ}`, the edge cutoff is one there, and `η_p` vanishes at the centre. -/
theorem EdgeChart.mem_edgeDiskDomain_center {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm g} {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ}
    (c : EdgeChart g hEnorm Δ σ μ b γ β A ρ F) (hΔ : 0 < Δ) :
    c.center ∈ edgeDiskDomain c.center Δ (fun x => c.coord x.val) F ρ ∧
      (Subtype.val : ball c.center (100 * Δ) → M).extend
        (fun x => edgeCoordinateProfile (c.coord x.val / Δ) *
          edgeHeightProfile (F x.val / (Δ * ρ x.val))) 0 c.center = 1 ∧
      c.coord c.center = 0 := by
  have hmem : c.center ∈ ball c.center (3 * Δ) := mem_ball_self (by positivity)
  exact ⟨c.disk_subset hmem, c.cutoff_eq_one hmem, c.coord_center⟩

end Consumer

end DifferentialGeometry.Geometry.Collapse
