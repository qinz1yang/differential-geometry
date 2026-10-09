import DifferentialGeometry.Geometry.Collapse.EdgeFullCollarFamily

/-!
# LFR44: the selected strong-edge family has ONE smoothing, disk domains AND full collars

Blueprint 207A, LFR44 (`thm:collapse-strong-edge-density-cover`, A:28614–28752), last sentence of
the statement and last paragraph of the proof: "If the common analytic/curvature hypotheses and
parameter bounds of LFR33 and LFR38 are supplied at these centers, the SAME family has ONE distance
smoothing, actual proper smooth disk bundles and full adapted collars, and those actual disk
domains cover these sets. Their cutoffs equal one there. No choice of a new strong tolerance is
made after the family is selected."

For a finite family `J` of strong edge points (each in its own normalization), LFR29.1's edge
parameter relations, and the normalized curvature bounds at the centres:

* `exists_physical_coarse_border_chart_with_splitting`: F7-MISC's physical LFR32 chart, now also
  recording that its first coordinate is `ρ(p)` times that of the strong edge's ACTUAL splitting
  (the chart is `ρ(p)` times the strip map of that splitting);
* `exists_strong_edge_full_collar_cover`: ONE smoothing `F` of the distance to the closed weak
  edge set (`exists_edge_full_collar_family`), and at every centre, in its normalization, for EVERY
  LFR19-type coordinate `f` of the strong edge's splitting: `B(p, 3Δ)` lies in the actual edge disk
  domain `{|f| < 4Δ, F/ρ ≤ 4Δ}` with the edge cutoff equal to one there
  (`ball_subset_edgeDiskDomain_and_cutoff_one`), AND the pair `(f, F/ρ)` has the full adapted
  collar on the whole band (LFR38).

The proper disk BUNDLES of LFR28 remain blocked (LFR28: LFR14 data and LFR23/LFR24/LFR26).
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

universe u w uE uH uM

namespace DifferentialGeometry.Geometry.Collapse

/-- F7-MISC's `exists_physical_coarse_border_chart` with the strong edge's splitting recorded. -/
theorem exists_physical_coarse_border_chart_with_splitting {X : Type u} [mX : MetricSpace X]
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
          dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p)) ∧
      ∃ (Y : Type w) (mY : MetricSpace Y), letI := mY
        ∃ (q : Y) (Fp : @KleinerLottApprox X (WithLp 2 (ℝ × Y))
            (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p (WithLp.toLp 2 ((0 : ℝ), q)) b),
          letI := mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          ∀ z, (Q z).fst = ρ p * (Fp.toFun z).fst := by
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
  refine ⟨fun x => (ρ p) • S x, ?_, ?_, ?_, ?_, hpA, ?_, ?_, Y, mY, q, F, fun z => rfl⟩
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **LFR44, collars and disk domains on the SAME smoothing.** See the module docstring. -/
theorem exists_strong_edge_full_collar_cover {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ → 1 ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b s b' s' : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ → b < 1 / 100 → 100 * Δ < b⁻¹ →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γ / 1000 →
        (Λ : ℝ) < 1 / (1000000 * Δ) → (Λ : ℝ) < s' / (100000000 * Δ ^ 2) →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 →
        s < b' / 100000 → s < s' / 100000 → b < s / 100000 →
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
      (∀ p ∈ J, @isEdgePoint.{uM, w} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p Δ b s) →
      (∀ p ∈ J, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
        SectionalBoundedBelowAt g z (-(κ / ρ p) ^ 2)) →
      (∀ p ∈ J, ∀ z ∈ ball p (b⁻¹ * ρ p), SectionalBoundedBelowAt g z (-(b / ρ p) ^ 2)) →
      LipschitzWith Λ ρ → ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ →
      let A : Set M := closure
        {x | @isEdgePoint.{uM, w} M (m.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x Δ b' s'}
      ∃ F : M → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
        ∀ p ∈ J, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
        ∃ (Y : Type w) (mY : MetricSpace Y), letI := mY
          ∃ (q : Y) (Fp : @KleinerLottApprox M (WithLp 2 (ℝ × Y))
              (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p (WithLp.toLp 2 ((0 : ℝ), q)) b)
            (Qn : M → WithLp 2 (ℝ × ℝ)),
          (letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            ∀ z, (Qn z).fst = (Fp.toFun z).fst) ∧
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
          ∀ f : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
          LipschitzWith (Real.toNNReal (1 + σ)) f →
          (∀ x ∈ ball p (100 * Δ), |f x - (Fp.toFun x).fst| ≤ μ * Δ) →
          (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
            ∀ w : TangentSpace I x, gR.inner x w w = 1 →
            intrinsicGeodesic gR hnR x w (dist x x') = x' →
            |mvfderiv (I := I) f x w - ((Fp.toFun x').fst - (Fp.toFun x).fst) / dist x x'| < σ) →
          (ball p (3 * Δ) ⊆ edgeDiskDomain p Δ (fun x => f x.val)
              (fun x => F x / ρ p) (fun x => ρ x / ρ p) ∧
            EqOn ((Subtype.val : ball p (100 * Δ) → M).extend
              (fun x => edgeCoordinateProfile (f x.val / Δ) *
                edgeHeightProfile (F x.val / ρ p / (Δ * (ρ x.val / ρ p)))) 0) 1
              (ball p (3 * Δ))) ∧
          ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ →
            Δ / 10 ≤ F x / ρ p / (ρ x / ρ p) → F x / ρ p / (ρ x / ρ p) ≤ 10 * Δ →
          ∃ hq : 99 / 100 ≤ ρ x / ρ p ∧ ρ x / ρ p ≤ 101 / 100,
            (letI := (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).rescale (ρ x / ρ p)⁻¹
              (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq.1));
              ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β,
                ∀ y, Φ.toFun y = @planeComparisonMap M
                  (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) Qn p x Δ (ρ x / ρ p) y) ∧
            let J := edgeReferenceCoordinates ![f, fun z => F z / ρ p / (ρ z / ρ p)]
            ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ J (ball x (300 * (ρ x / ρ p))) ∧
            (∀ y ∈ ball x (100 * (ρ x / ρ p)), Function.Surjective (mvfderiv (I := I) J y)) ∧
            (∀ y ∈ ball x (100 * (ρ x / ρ p)), ∀ z ∈ ball x (100 * (ρ x / ρ p)),
              ‖J y - J z‖ ≤ (1 + γ) * (dist y z / (ρ x / ρ p))) ∧
            (∀ y ∈ ball x (100 * (ρ x / ρ p)), infDist (J y) (ball (J x) 100) < 100 * γ) ∧
            (∀ v ∈ ball (J x) 100, ∃ y ∈ ball x (100 * (ρ x / ρ p)), ‖J y - v‖ < 100 * γ) ∧
            ∀ y ∈ ball x (100 * (ρ x / ρ p)), ∀ z ∈ ball x (100 * (ρ x / ρ p) / γ),
              ρ x / ρ p < dist y z →
              ∀ W : TangentSpace I y, gR.inner y W W = 1 →
              intrinsicGeodesic gR hnR y W (dist y z) = z →
              ‖(ρ x / ρ p) • mvfderiv (I := I) J y W - (dist y z / (ρ x / ρ p))⁻¹ •
                (planeReferenceIsometry (planeComparisonMap Qn p x Δ (ρ x / ρ p) z) -
                  planeReferenceIsometry (planeComparisonMap Qn p x Δ (ρ x / ρ p) y))‖ < γ) := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hfam⟩ := exists_edge_full_collar_family.{uE, uH, uM, w}
    hβ hβγ hγ hγ1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ hΔ1 => ?_⟩
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hΔfam⟩ := hfam Δ hΔ
  refine ⟨min τ₀ (1 / 20000), lt_min hτ₀ (by norm_num), κ₀, hκ₀, b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b s b' s' Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hb hbb₀ hb100 hsource
    hlam hbudget hscale hend hb'domain hs'domain hb'error hs'error hsb' hss' hbs
    E _ _ _ _ H _ I _ M m _ _ _ hM _ _ _ g hEnorm ρ hρpos J hJ hJE hsec hsecb hρ hρs A
  have hτsmall : τ < 1 / 10000 :=
    (hττ₀.trans (min_le_right _ _)).trans_lt (by norm_num)
  have hQex : ∀ p ∈ J, ∃ Q : M → WithLp 2 (ℝ × ℝ), Q p = 0 ∧
      (∀ x ∈ ball p (200 * (Δ * ρ p)), ∀ y ∈ ball p (200 * (Δ * ρ p)),
        |dist (Q x) (Q y) - dist x y| ≤ τ * (Δ * ρ p)) ∧
      (∀ x ∈ ball p (200 * (Δ * ρ p)), 0 ≤ (Q x).snd) ∧
      (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * ρ p) →
        z.snd ∈ Icc 0 (100 * (Δ * ρ p)) →
          ∃ x ∈ ball p (200 * (Δ * ρ p)), dist (Q x) z ≤ τ * (Δ * ρ p)) ∧
      p ∈ A ∧ (∀ a ∈ A ∩ ball p (190 * (Δ * ρ p)), (Q a).snd ≤ τ * (Δ * ρ p)) ∧
      (∀ t : ℝ, |t| ≤ 100 * (Δ * ρ p) → ∃ a ∈ A ∩ ball p (190 * (Δ * ρ p)),
          dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p)) ∧
      ∃ (Y : Type w) (mY : MetricSpace Y), letI := mY
        ∃ (q : Y) (Fp : @KleinerLottApprox M (WithLp 2 (ℝ × Y))
            (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p (WithLp.toLp 2 ((0 : ℝ), q)) b),
          letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
          ∀ z, (Q z).fst = ρ p * (Fp.toFun z).fst := fun p hp =>
    exists_physical_coarse_border_chart_with_splitting (X := M) hρ hρpos hΔ1 hτ hτsmall hscale
      hend hb'domain hs'domain hb'error hs'error hsb' hss' hbs p (hJE p hp)
  choose! Q hQ using hQex
  obtain ⟨F, hF0, hFL, hcent⟩ := hΔfam σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ
    (hττ₀.trans (min_le_left _ _)) hθ hκ hκκ₀ hb hbb₀ hlam hbudget E H I M g hEnorm A J Q ρ
    hρpos hJ isClosed_closure (fun p hp => (hQ p hp).1) (fun p hp => (hQ p hp).2.1)
    (fun p hp => (hQ p hp).2.2.1) (fun p hp => (hQ p hp).2.2.2.1)
    (fun p hp => (hQ p hp).2.2.2.2.1) (fun p hp => (hQ p hp).2.2.2.2.2.1)
    (fun p hp => (hQ p hp).2.2.2.2.2.2.1) hsec hρ hρs
  refine ⟨F, hF0, hFL, fun p hp => ⟨(hcent p hp).1, ?_⟩⟩
  have hr : 0 < ρ p := hρpos p
  obtain ⟨Y, mY, q, Fp, hrel⟩ := (hQ p hp).2.2.2.2.2.2.2
  refine ⟨Y, mY, q, Fp, fun z => (ρ p)⁻¹ • Q p z, fun z => ?_, ?_⟩
  · change (ρ p)⁻¹ * (Q p z).fst = _
    rw [hrel z, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hsecbR := radialScaled_sectional_bound g (r := b⁻¹) hr (hsecb p hp)
  have hvalR := radialScaled_value_clause (A := A) hr (hcent p hp).1
  have hscale' : Δ * (Λ : ℝ) ≤ 1 / 1000000 := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 1000000 * Δ)).mp hscale
    nlinarith
  have hρ' := lipschitzWith_normalized_scale hρ hr
  have hpA : p ∈ A := (hQ p hp).2.2.2.2.1
  intro hmetric gR hnR f hfs hfL hfval htest
  refine ⟨?_, fun x hx hfx hη hη' => ?_⟩
  · let _ := m.rescale (ρ p)⁻¹ (inv_pos.mpr hr)
    exact ball_subset_edgeDiskDomain_and_cutoff_one Fp hΔ1 hb100 hμ1 hsource
      (fun x => ρ x / ρ p) (fun x => F x / ρ p) hρ' (fun x => div_pos (hρpos x) hr)
      (div_self hr.ne') hscale' A hpA (fun x _ => hvalR x) (fun x => f x.val)
      (fun x => hfval x.val x.property)
  · have hQα : letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr hr)
        ∀ z ∈ ball p (200 * Δ), (Q p z).fst = ρ p * (Fp.toFun z).fst := fun z _ => hrel z
    exact (hcent p hp).2 Y q Fp hsecbR hQα f hfs hfL hfval htest x hx hfx hη hη'

end DifferentialGeometry.Geometry.Collapse
