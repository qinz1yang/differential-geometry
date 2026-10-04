import DifferentialGeometry.Geometry.Collapse.EdgeSharedProfiles
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeBorderAdapters
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeDiskCoverage

/-!
# LFR44, disk clause without the adapted collars: one smoothing for a finite strong-edge family

Blueprint LFR44 (master207A.tex:28614–28752), last paragraph ("Finite selection and the ACTUAL disk
domains"), except the full adapted collars (LFR38). For a FINITE family `J` of strong edge points
(each in its own normalization `d / ρ(p)`), with LFR33's curvature hypothesis supplied at the
centres and the parameter order of LFR29.1:

* `exists_physical_coarse_border_chart`: LFR32 in physical units — the strip map of a strong edge
  `p`, scaled by `ρ(p)`, and the closure `A` of the weak edge set satisfy every clause of the
  coarse-border chart data at scale `ρ(p)` (the hypotheses of LFR33's shared smoothing);
* `infDist_rescale`: the distance to a set scales with the metric;
* `exists_shared_smoothing_strong_edge_disk_cover`: ONE nonnegative `(1+ε)`-Lipschitz function
  `F` (X91, `exists_shared_edge_smoothing_with_profiles`), smooth on an open set containing every
  collar region, `μΔρ(p)`-close to `d_A` for every centre, and at every centre, in its
  normalization, the ball `B(p, 3Δ)` lies in the ACTUAL edge disk domain `{|f_p| < 4Δ,
  η ≤ 4Δ}` (`η = F/ρ`, `f_p` the tangential coordinate of the strong edge map) and the edge cutoff
  equals one there (`ball_subset_edgeDiskDomain_and_cutoff_one`).

The family is arbitrary; for the selected family of LFR44 it is the output of
`exists_finite_strong_edge_cover_riemannian` (whose cover radius `2Δρ` is below `3Δρ`).
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

/-- The distance to a set in the rescaled metric `c • d` is `c` times the distance. -/
theorem infDist_rescale {X : Type*} (m : MetricSpace X) (c : ℝ) (hc : 0 < c) (x : X)
    (s : Set X) :
    @infDist X (m.rescale c hc).toPseudoMetricSpace x s =
      c * @infDist X m.toPseudoMetricSpace x s := by
  rw [@infDist_eq_iInf X (m.rescale c hc).toPseudoMetricSpace,
    @infDist_eq_iInf X m.toPseudoMetricSpace, Real.mul_iInf_of_nonneg hc.le]
  rfl

/-- **LFR32 in physical units, as LFR33's chart data.** For a strong edge point `p` (in its own
normalization), the strip map scaled by `ρ(p)` and the closure of the weak edge set satisfy the
coarse-border chart clauses at the physical scale `Δ ρ(p)`. -/
theorem exists_physical_coarse_border_chart {X : Type u} [mX : MetricSpace X]
    {Δ τ b s b' s' : ℝ} {Λ : NNReal} {ρ : X → ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x)
    (hΔ : 1 ≤ Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000)
    (hscale : (Λ : ℝ) < 1 / (1000000 * Δ))
    (hend : (Λ : ℝ) < s' / (100000000 * Δ ^ 2))
    (hb'domain : b' < 1 / (1000000 * Δ)) (hs'domain : s' < 1 / (1000000 * Δ))
    (hb'error : b' < τ * Δ / 1000000000) (hs'error : s' < τ * Δ / 1000000000)
    (hsb' : s < b' / 100000) (hss' : s < s' / 100000) (hbs : b < s / 100000) (p : X)
    (hp : @isEdgePoint.{u, w} X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p Δ b s) :
    ∃ Q : X → WithLp 2 (ℝ × ℝ), Q p = 0 ∧
      (∀ x ∈ ball p (200 * (Δ * ρ p)), ∀ y ∈ ball p (200 * (Δ * ρ p)),
        |dist (Q x) (Q y) - dist x y| ≤ τ * (Δ * ρ p)) ∧
      (∀ x ∈ ball p (200 * (Δ * ρ p)), 0 ≤ (Q x).snd) ∧
      (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * ρ p) →
        z.snd ∈ Icc 0 (100 * (Δ * ρ p)) →
          ∃ x ∈ ball p (200 * (Δ * ρ p)), dist (Q x) z ≤ τ * (Δ * ρ p)) ∧
      p ∈ closure {x | @isEdgePoint.{u, w} X (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x)))
        x Δ b' s'} ∧
      (∀ a ∈ closure {x | @isEdgePoint.{u, w} X (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x)))
          x Δ b' s'} ∩ ball p (190 * (Δ * ρ p)), (Q a).snd ≤ τ * (Δ * ρ p)) ∧
      (∀ t : ℝ, |t| ≤ 100 * (Δ * ρ p) →
        ∃ a ∈ closure {x | @isEdgePoint.{u, w} X (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x)))
          x Δ b' s'} ∩ ball p (190 * (Δ * ρ p)),
          dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p)) := by
  obtain ⟨Y, mY, q, C, hC, hCΔ, ⟨F⟩, ⟨G⟩⟩ := hp
  obtain ⟨-, hpA, hS0, hSnn, hSd, hSc, hSb, hSbc⟩ :=
    coarse_border_of_physical_lipschitz_scale (X := X) (Y := Y) (hC := hC) hρ hρpos F G hΔ hτ hτsmall
      hscale hend hb'domain hs'domain hb'error hs'error hsb' hss' hbs hCΔ.le
  have hc : 0 < ρ p := hρpos p
  have hball : ∀ r : ℝ, ∀ x : X,
      x ∈ @ball X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).toPseudoMetricSpace p r ↔
        x ∈ ball p (r * (ρ p)) := by
    intro r x
    change (ρ p)⁻¹ * dist x p < r ↔ dist x p < r * (ρ p)
    rw [← div_eq_inv_mul, div_lt_iff₀ hc]
  let S : X → WithLp 2 (ℝ × ℝ) :=
    letI := mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
    F.stripMap G
  have hcnorm : ‖(ρ p)‖ = (ρ p) := Real.norm_of_nonneg hc.le
  refine ⟨fun x => (ρ p) • S x, ?_, ?_, ?_, ?_, hpA, ?_, ?_⟩
  · change (ρ p) • S p = 0
    rw [show S p = 0 from hS0, smul_zero]
  · intro x hx y hy
    have hx' : x ∈ @ball X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).toPseudoMetricSpace p
        (200 * Δ) := (hball _ x).mpr (by rwa [mul_assoc])
    have hy' : y ∈ @ball X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).toPseudoMetricSpace p
        (200 * Δ) := (hball _ y).mpr (by rwa [mul_assoc])
    have h : |dist (S x) (S y) - (ρ p)⁻¹ * dist x y| ≤ τ * Δ := hSd x hx' y hy'
    rw [dist_smul₀, hcnorm]
    have hxy : dist x y = (ρ p) * ((ρ p)⁻¹ * dist x y) := by field_simp
    rw [hxy, ← mul_sub, abs_mul, abs_of_pos hc]
    calc (ρ p) * |dist (S x) (S y) - (ρ p)⁻¹ * dist x y| ≤ (ρ p) * (τ * Δ) :=
          mul_le_mul_of_nonneg_left h hc.le
      _ = τ * (Δ * (ρ p)) := by ring
  · intro x _
    change 0 ≤ ((ρ p) • S x).snd
    rw [WithLp.smul_snd, smul_eq_mul]
    exact mul_nonneg hc.le (hSnn x)
  · intro z hz1 hz2
    have hz1' : |((ρ p)⁻¹ • z).fst| ≤ 100 * Δ := by
      rw [WithLp.smul_fst, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hc), ← div_eq_inv_mul,
        div_le_iff₀ hc]
      linarith
    have hz2' : ((ρ p)⁻¹ • z).snd ∈ Icc 0 (100 * Δ) := by
      rw [WithLp.smul_snd, smul_eq_mul]
      refine ⟨mul_nonneg (inv_nonneg.mpr hc.le) hz2.1, ?_⟩
      rw [← div_eq_inv_mul, div_le_iff₀ hc]
      linarith [hz2.2]
    obtain ⟨x, hx, hxz⟩ := hSc ((ρ p)⁻¹ • z) hz1' hz2'
    refine ⟨x, by rw [← mul_assoc]; exact (hball _ x).mp hx, ?_⟩
    have hzz : z = (ρ p) • ((ρ p)⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    change dist ((ρ p) • S x) z ≤ τ * (Δ * (ρ p))
    rw [hzz, dist_smul₀, hcnorm]
    have h2 : (ρ p) * dist (S x) ((ρ p)⁻¹ • z) ≤ (ρ p) * (τ * Δ) := mul_le_mul_of_nonneg_left hxz.le hc.le
    linarith
  · rintro a ⟨haA, ha⟩
    have ha' : a ∈ @ball X (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).toPseudoMetricSpace p
        (190 * Δ) := (hball _ a).mpr (by rwa [mul_assoc])
    have h : (S a).snd ≤ τ * Δ := hSb a ⟨haA, ha'⟩
    change ((ρ p) • S a).snd ≤ τ * (Δ * (ρ p))
    rw [WithLp.smul_snd, smul_eq_mul]
    have h2 := mul_le_mul_of_nonneg_left h hc.le
    linarith
  · intro t ht
    have ht' : |t / (ρ p)| ≤ 100 * Δ := by
      rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]
      linarith
    obtain ⟨y0, ⟨hy0E, hy0⟩, hy0t⟩ := hSbc (t / (ρ p)) ht'
    refine ⟨y0, ⟨subset_closure hy0E, by rw [← mul_assoc]; exact (hball _ y0).mp hy0⟩, ?_⟩
    have htt : (WithLp.toLp 2 (t, (0 : ℝ)) : WithLp 2 (ℝ × ℝ)) =
        (ρ p) • WithLp.toLp 2 (t / (ρ p), (0 : ℝ)) := by
      rw [← WithLp.toLp_smul, Prod.smul_mk, smul_eq_mul, smul_zero, mul_div_cancel₀ t hc.ne']
    have hy0t' : dist (S y0) (WithLp.toLp 2 (t / (ρ p), (0 : ℝ))) ≤ τ * Δ := le_of_lt hy0t
    change dist ((ρ p) • S y0) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * (ρ p))
    rw [htt, dist_smul₀, hcnorm]
    have h2 := mul_le_mul_of_nonneg_left hy0t' hc.le
    linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **LFR44, disk clause (without LFR38's collars).** A finite family of strong edge points,
LFR33's curvature hypothesis at the centres, and LFR29.1's parameter order give ONE smoothing `F`
of the distance to the closed weak edge set whose edge disk domains, at every centre and in its
normalization, contain `B(p, 3Δ)` with the edge cutoff equal to one there. -/
theorem exists_shared_smoothing_strong_edge_disk_cover (g : SmoothRiemannianMetric I M)
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
    let A : Set M := closure
      {x | @isEdgePoint.{u, w} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b' s'}
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧ (∀ x, 0 ≤ F x) ∧
      LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∀ x y, |(F x - infDist x A) - (F y - infDist y A)| ≤ ε * dist x y) ∧
      ∀ p ∈ J, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
        (closedBall p (20 * (Δ * ρ p)) ∩ {x | 3 / 4 * (Δ * ρ p) ≤ infDist x A ∧
          infDist x A ≤ 21 / 2 * (Δ * ρ p)}) ⊆ O ∧
        ∃ (Y : Type w) (mY : MetricSpace Y), letI := mY
          ∃ (q : Y) (Fp : @KleinerLottApprox M (WithLp 2 (ℝ × Y))
              (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p (WithLp.toLp 2 ((0 : ℝ), q)) b),
            letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            ball p (3 * Δ) ⊆ edgeDiskDomain p Δ (fun x => (Fp.toFun x.val).fst)
                (fun x => F x / ρ p) (fun x => ρ x / ρ p) ∧
              EqOn ((Subtype.val : ball p (100 * Δ) → M).extend
                (fun x => edgeCoordinateProfile ((Fp.toFun x.val).fst / Δ) *
                  edgeHeightProfile (F x.val / ρ p / (Δ * (ρ x.val / ρ p)))) 0) 1
                (ball p (3 * Δ)) := by
  intro A
  have hΔpos : 0 < Δ := by linarith
  have hQex : ∀ p ∈ J, ∃ Q : M → WithLp 2 (ℝ × ℝ), Q p = 0 ∧
      (∀ x ∈ ball p (200 * (Δ * ρ p)), ∀ y ∈ ball p (200 * (Δ * ρ p)),
        |dist (Q x) (Q y) - dist x y| ≤ τ * (Δ * ρ p)) ∧
      (∀ x ∈ ball p (200 * (Δ * ρ p)), 0 ≤ (Q x).snd) ∧
      (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * ρ p) →
        z.snd ∈ Icc 0 (100 * (Δ * ρ p)) →
          ∃ x ∈ ball p (200 * (Δ * ρ p)), dist (Q x) z ≤ τ * (Δ * ρ p)) ∧
      p ∈ A ∧ (∀ a ∈ A ∩ ball p (190 * (Δ * ρ p)), (Q a).snd ≤ τ * (Δ * ρ p)) ∧
      (∀ t : ℝ, |t| ≤ 100 * (Δ * ρ p) → ∃ a ∈ A ∩ ball p (190 * (Δ * ρ p)),
          dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p)) := fun p hp =>
    exists_physical_coarse_border_chart (X := M) hρ hρpos hΔ hτ hτsmall hscale hend hb'domain
      hs'domain hb'error hs'error hsb' hss' hbs p (hJE p hp)
  choose! Q hQ using hQex
  obtain ⟨F, O, hO, hFO, hF0, hFL, hdiff, hcent⟩ :=
    exists_shared_edge_smoothing_with_profiles g hEnorm (A := A) isClosed_closure hJ hρpos hΔpos
      hτ hτsmall (fun p hp => (hQ p hp).1) (fun p hp => (hQ p hp).2.1)
      (fun p hp => (hQ p hp).2.2.1) (fun p hp => (hQ p hp).2.2.2.1)
      (fun p hp => (hQ p hp).2.2.2.2.1) (fun p hp => (hQ p hp).2.2.2.2.2.1)
      (fun p hp => (hQ p hp).2.2.2.2.2.2) hκ hκΔ hsec hε hε1 hμ (by linarith) hθ hρ hρs hlam
  refine ⟨F, O, hO, hFO, hF0, hFL, hdiff, fun p hp => ?_⟩
  obtain ⟨hval, hCO, -⟩ := hcent p hp
  refine ⟨hval, hCO, ?_⟩
  obtain ⟨Y, mY, q, C, hC, hCΔ, ⟨Fp⟩, -⟩ := hJE p hp
  refine ⟨Y, mY, q, Fp, ?_⟩
  have hscale' : Δ * (Λ : ℝ) ≤ 1 / 1000000 := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 1000000 * Δ)).mp hscale
    nlinarith
  have hP : ∀ x ∈ @ball M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).toPseudoMetricSpace p
      (100 * Δ), |F x / ρ p - @infDist M (m.rescale (ρ p)⁻¹
        (inv_pos.mpr (hρpos p))).toPseudoMetricSpace x A| ≤ μ * Δ := by
    intro x _
    rw [infDist_rescale, div_eq_inv_mul, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr (hρpos p))]
    have h := hval x
    rw [← div_eq_inv_mul, div_le_iff₀ (hρpos p)]
    linarith
  have hpA : p ∈ A := (hQ p hp).2.2.2.2.1
  have hρ' := lipschitzWith_normalized_scale hρ (hρpos p)
  let := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
  exact ball_subset_edgeDiskDomain_and_cutoff_one Fp hΔ hb hμ1 hsource
    (fun x => ρ x / ρ p) (fun x => F x / ρ p) hρ' (fun x => div_pos (hρpos x) (hρpos p))
    (div_self (hρpos p).ne') hscale' A hpA hP (fun x => (Fp.toFun x.val).fst)
    (fun x => by rw [sub_self, abs_zero]; positivity)

end DifferentialGeometry.Geometry.Collapse
