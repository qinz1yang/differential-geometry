import DifferentialGeometry.Geometry.Collapse.AnnularAdaptedCoordinates
import DifferentialGeometry.Geometry.Collapse.ZeroStratumRiemannian
import DifferentialGeometry.Geometry.Collapse.RiemannianConeScale
import DifferentialGeometry.Geometry.Metric.Approximation.OriginalRadialExport

/-!
# LCP04: the selected zero packets with their original comparison buffer

Blueprint `master207A.tex`, LCP04 (`prop:collapse-zero-comparison-consumer-binding`, A:30123).
The comparison premises of LC66, LC70, LC73, LC76, LC77 and LC80 are discharged from the
ORIGINAL curvature buffer `sec_g ≥ -(1/60)² r⁻²` on `B_g(i, 400 r)` (via the eight-ball
comparison theorem), and all consumers act on ONE selection with the SAME radius, cone, actual
Kleiner–Lott map, model and radial function.

* `selected_center_adapted_coordinate_of_original_buffer`: LC73 (Codex X83's
  `exists_prescribed_annular_adapted_parameters`) at an arbitrary scale `r`: the metric space
  `(M, r⁻¹ d)` with tensor `r⁻² g`, the original buffer at scale `r`, a supplied radial function
  with LC73's smoothness and error hypotheses at scale `r`.
* `exists_selected_zero_packets_of_original_buffer` (LCP04): on a closed connected Riemannian
  three-manifold, one LC64 selection `J` from LC66; under the original data at the selected
  centers it exports LC66's shell splitting and tenth-radius cover, X82's ORIGINAL radial
  coordinate (LC70) at every point of every closed shell, LC73's adapted coordinate built from
  the SAME supplied radial function at every such point and every admissible scale, and LC77's
  end count for the SAME model.

Models, cones, maps, errors and radial functions are families fixed before the selection
(LC80's order); their properties are required at the selected centers only. LC61's core
identification (LC80 item 2) is not part of this row.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Topology ContDiff Manifold ENNReal
open GC.MetricGeometry
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v w uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LC73 at an actual center and scale `r`.** The prescribed annular adapted coordinate of
LC73 for the metric space `(M, r⁻¹ d)` with tensor `r⁻² g`, under the original buffer
`sec_g ≥ -(1/60)² r⁻²` on `B(i, 400 r)`, an actual Kleiner–Lott map from `(M, r⁻¹ d, i)` and a
supplied radial function with LC73's hypotheses at scale `r`. The constants precede every
manifold, center, scale and function. -/
theorem selected_center_adapted_coordinate_of_original_buffer {β ζ : ℝ}
    (hβ : 0 < β) (hβζ : β < ζ) (hζone : ζ < 1) :
    ∃ ε δstar Λstar : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δstar ∧ 0 < Λstar ∧
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [hM : CompleteSpace M] [ConnectedSpace M]
        (g : SmoothRiemannianMetric I M),
      ∀ (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)),
      ∀ (i : M) (r : ℝ) (hr : 0 < r),
      (∀ y ∈ ball i (400 * r), SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * r⁻¹ ^ 2))) →
      ∀ (C : Type v) [MetricSpace C] (o : C), RadialConeData o →
      ∀ {δ : ℝ}, @KleinerLottApprox M C (m.rescale r⁻¹ (inv_pos.mpr hr)) _ i o δ →
      δ < δstar → ∀ η : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η {x | 3 / 40 ≤ r⁻¹ * dist x i ∧ r⁻¹ * dist x i ≤ 11} →
      (∀ x y, |(η x - r⁻¹ * dist i x) - (η y - r⁻¹ * dist i y)| ≤ ε * (r⁻¹ * dist x y)) →
      ∀ q : M, r / 10 ≤ dist i q → dist i q ≤ 10 * r →
      ∀ (lam : ℝ) (hlam : 0 < lam), Λstar ≤ lam →
      let mr := m.rescale r⁻¹ (inv_pos.mpr hr)
      let gr := scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
      let hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := m) g hmetric hr
      let := mr.rescale lam hlam
      letI := (mr.rescale_completeSpace_iff lam hlam).mpr
        ((m.rescale_completeSpace_iff r⁻¹ (inv_pos.mpr hr)).mpr hM)
      letI := radialScaledBundle gr lam hlam
      letI := radialScaledContinuous gr lam hlam
      letI := radialScaledManifold (m := mr) gr hmr lam hlam
      let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) gr
      let ψ := fun x => lam * (η x - η q)
      ∃ hEnorm : IsMetricNorm h,
        ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
          ∃ (z : Z) (α : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) β),
          (∀ x, (α.toFun x).fst = lam *
            (@dist M mr.toDist i x - @dist M mr.toDist i q)) ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
          (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
          (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
          (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
          ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
            ∀ w : TangentSpace I x, h.inner x w w = 1 →
            intrinsicGeodesic h hEnorm x w (dist x y) = y →
            |mvfderiv (I := I) ψ x w -
              ((α.toFun y).fst - (α.toFun x).fst) / dist x y| < ζ := by
  obtain ⟨ε, δstar, Λstar, hε, hεq, hδstar, hΛstar, hLC73⟩ :=
    exists_prescribed_annular_adapted_parameters (E := E) (H := H) (I := I) hβ hβζ hζone
  refine ⟨ε, δstar, Λstar, hε, hεq, hδstar, hΛstar, ?_⟩
  intro M m _ _ _ hM _ g hmetric i r hr hsec C _ o hcone δ F hδ η hη herr q hq1 hq2 lam hlam
    hΛ
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hMr : @CompleteSpace M (m.rescale r⁻¹ hrinv).toUniformSpace :=
    (m.rescale_completeSpace_iff r⁻¹ hrinv).mpr hM
  have hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := m) g hmetric hr
  have hsecr : ∀ y ∈ @ball M (m.rescale r⁻¹ hrinv).toPseudoMetricSpace i 400,
      SectionalBoundedBelowAt (scaleMetric (r⁻¹ ^ 2) (pow_pos hrinv 2) g) y
        (-((1 / 60) ^ 2)) := by
    intro y hy
    have hy' : r⁻¹ * dist y i < 400 := hy
    have hyr : y ∈ ball i (400 * r) := by
      rw [mem_ball]
      have := (inv_mul_lt_iff₀ hr).mp hy'
      linarith
    rw [sectionalBoundedBelowAt_scaleMetric_iff]
    simpa only [neg_mul] using hsec y hyr
  have hq1' : 1 / 10 ≤ @dist M (m.rescale r⁻¹ hrinv).toDist i q := by
    change 1 / 10 ≤ r⁻¹ * dist i q
    rw [le_inv_mul_iff₀ hr]
    linarith
  have hq2' : @dist M (m.rescale r⁻¹ hrinv).toDist i q ≤ 10 := by
    change r⁻¹ * dist i q ≤ 10
    rw [inv_mul_le_iff₀ hr]
    linarith
  exact @hLC73 M (m.rescale r⁻¹ hrinv) _ _ _ hMr _ _ hmr i hsecr C _ o hcone δ F hδ η hη herr q
    hq1' hq2' lam hlam hΛ

/-- **LCP04: the selected zero packets keep their data, with the original buffer.** On a closed
connected Riemannian three-manifold, ONE LC64 selection `J` (from LC66) of the LC16 zero stratum
`Z` at radii `r ∈ [Tρ, Uρ]`. Suppose at every selected center: the ORIGINAL buffer
`sec_g ≥ -(1/60)² r_i⁻²` on `B_g(i, 400 r_i)`; the model `N i` is a geodesic nonnegatively curved
proper space whose cone at infinity is `C i`; an actual Kleiner–Lott `δ_i`-map from
`(M, r_i⁻¹ d, i)` to `(C i, o i)` with `δ_i < δ'`; and the radial function `η i` has LC73's
smoothness and error hypotheses at scale `r_i`. Then: LC66's splitting at every point of every
closed shell and the tenth-radius cover of `Z`; X82's ORIGINAL radial coordinate
`(ρ q)⁻¹ (d(i,·) - d(i,q))` splits at every shell point (LC70); LC73's adapted coordinate
`λ (η i - η i q)` from the SAME `η i` at every shell point and every `λ ≥ Λ'`; and LC77: the SAME
model `N i` has at most one end. No comparison hypothesis is assumed; the constants precede every
manifold, family and selection. -/
theorem exists_selected_zero_packets_of_original_buffer (hE : Module.finrank ℝ E = 3)
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]
        (g : SmoothRiemannianMetric I M),
      letI m := inducedMetricSpace g
      ∀ (N C : M → Type v) [mN : ∀ i, MetricSpace (N i)] [∀ i, ProperSpace (N i)]
        [mC : ∀ i, MetricSpace (C i)] [∀ i, ProperSpace (C i)]
        (n₀ : ∀ i, N i) (o : ∀ i, C i), (∀ i, RadialConeData (o i)) →
      ∀ (δ : M → ℝ) (η : M → M → ℝ) (r ρ : M → ℝ), Continuous ρ →
      ∀ (hρpos : ∀ p, 0 < ρ p) {T U : ℝ} (hT : 0 < T), 20 * Λ' ≤ T → T ≤ U →
      ∀ (hlower : ∀ p, T * ρ p ≤ r p), (∀ p, r p ≤ U * ρ p) →
      ∃ J : Set M, J.Finite ∧ J.PairwiseDisjoint (fun i => ball i (r i)) ∧
        (∀ i ∈ J, (ball i (r i) ∩
          {q | @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}
          ).Nonempty) ∧
        (∀ i ∈ J, ∀ q, dist i q ≤ 10 * r i → r q ≤ 20 * r i ∧ T / 20 ≤ r i / ρ q) ∧
        ((∀ i ∈ J,
            (∀ y ∈ riemannianBallOf g i (400 * r i),
              SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * (r i)⁻¹ ^ 2))) ∧
            fourPointComparison 0 (univ : Set (N i)) ∧
            (∀ x y : N i, ∃ f : Icc (0 : ℝ) 1 → N i,
              Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
              ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
            (∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
              R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox (N i) (C i)
                ((mN i).rescale R⁻¹ (inv_pos.mpr hR)) (mC i) (n₀ i) (o i) δ₁)) ∧
            δ i < δ' ∧
            Nonempty (@KleinerLottApprox M (C i)
              (m.rescale (r i)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos i)).trans_le (hlower i))))
              (mC i) i (o i) (δ i)) ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i)
              {x | 3 / 40 ≤ (r i)⁻¹ * dist x i ∧ (r i)⁻¹ * dist x i ≤ 11} ∧
            ∀ x y, |(η i x - (r i)⁻¹ * dist i x) - (η i y - (r i)⁻¹ * dist i y)| ≤
              ε * ((r i)⁻¹ * dist x y)) →
          (∀ i ∈ J, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            @HasEuclideanSplitting.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q 1
              (β 1) ∧
            @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 ≠ 0) ∧
          {q | @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} ⊆
            ⋃ i ∈ J, ball i (r i / 10) ∧
          (∀ i ∈ J, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
              ∃ (z : Z) (F : @KleinerLottApprox M
                (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
                (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) inferInstance
                q (WithLp.toLp 2 (0, z)) (β 1)),
                ∀ x : M, (@KleinerLottApprox.toFun M
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
                  (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) inferInstance
                  q (WithLp.toLp 2 (0, z)) (β 1) F x).fst = WithLp.toLp 2
                  (Function.const (Fin 1) ((ρ q)⁻¹ * (dist i x - dist i q)))) ∧
          (∀ i ∈ J, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
            let hri := (mul_pos hT (hρpos i)).trans_le (hlower i)
            let mr := m.rescale (r i)⁻¹ (inv_pos.mpr hri)
            let gr := scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hri) 2) g
            let hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := m) g
              (inducedMetricSpace_hmetric g) hri
            let := mr.rescale lam hlam
            letI := (mr.rescale_completeSpace_iff lam hlam).mpr
              ((m.rescale_completeSpace_iff (r i)⁻¹ (inv_pos.mpr hri)).mpr
                (inducedMetricSpace_completeSpace g))
            letI := radialScaledBundle gr lam hlam
            letI := radialScaledContinuous gr lam hlam
            letI := radialScaledManifold (m := mr) gr hmr lam hlam
            let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) gr
            let ψ := fun x => lam * (η i x - η i q)
            ∃ hEnorm : IsMetricNorm h,
              ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
                ∃ (z : Z) (α : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)),
                (∀ x, (α.toFun x).fst = lam *
                  (@dist M mr.toDist i x - @dist M mr.toDist i q)) ∧
                ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
                (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
                (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
                (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
                ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
                  ∀ w : TangentSpace I x, h.inner x w w = 1 →
                  intrinsicGeodesic h hEnorm x w (dist x y) = y →
                  |mvfderiv (I := I) ψ x w -
                    ((α.toFun y).fst - (α.toFun x).fst) / dist x y| < ζ) ∧
          ∀ i ∈ J, ∀ K : Set (N i), IsCompact K → ∀ a b : N i,
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
            connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) := by
  obtain ⟨δ₁, Λ₁, hδ₁, hΛ₁, h66⟩ :=
    exists_zero_stratum_small_core_cover_riemannian.{u, v} (E := E) (H := H) (I := I) hE hβ
      hβone
  obtain ⟨δ₂, Λ₂, hδ₂, hΛ₂, h77⟩ :=
    exists_selected_model_one_end_parameter_riemannian.{u, v, v} (E := E) (H := H) (I := I) hE
      hβ hβone
  obtain ⟨δ₃, Λ₃, hδ₃, hΛ₃, h82⟩ :=
    original_radial_selected_shell_export.{u, v} (n := 3) (by norm_num) hβ hβone
  obtain ⟨ε, δ₄, Λ₄, hε, hεq, hδ₄, hΛ₄, h73⟩ :=
    selected_center_adapted_coordinate_of_original_buffer.{u, v} (E := E) (H := H) (I := I)
      hβ hβζ hζone
  refine ⟨ε, min (min δ₁ δ₂) (min δ₃ δ₄), max (max Λ₁ Λ₂) (max Λ₃ Λ₄), hε, hεq,
    lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδ₄), lt_max_of_lt_left (lt_max_of_lt_left hΛ₁), ?_⟩
  intro M _ _ _ _ _ _ _ g N C mN _ mC _ n₀ o H δ η r ρ hρ hρpos T U hT hTΛ hTU hlower hupper
  let := inducedMetricSpace g
  have hcomplete : CompleteSpace M := inducedMetricSpace_completeSpace g
  have hΛ₁' : Λ₁ ≤ max (max Λ₁ Λ₂) (max Λ₃ Λ₄) := (le_max_left _ _).trans (le_max_left _ _)
  have hΛ₂' : Λ₂ ≤ max (max Λ₁ Λ₂) (max Λ₃ Λ₄) := (le_max_right _ _).trans (le_max_left _ _)
  have hΛ₃' : Λ₃ ≤ max (max Λ₁ Λ₂) (max Λ₃ Λ₄) := (le_max_left _ _).trans (le_max_right _ _)
  have hΛ₄' : Λ₄ ≤ max (max Λ₁ Λ₂) (max Λ₃ Λ₄) := (le_max_right _ _).trans (le_max_right _ _)
  have hδ₁' : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₂' : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hδ₃' : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₄' : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₄ := (min_le_right _ _).trans (min_le_right _ _)
  have hr : ∀ p, 0 < r p := fun p => (mul_pos hT (hρpos p)).trans_le (hlower p)
  obtain ⟨J, hfin, hmax, hdisj, hloc, -, hcond⟩ :=
    h66 M g r ρ hρ hρpos hT ((mul_le_mul_of_nonneg_left hΛ₁' (by norm_num)).trans hTΛ) hTU
      hlower hupper
  refine ⟨J, hfin, hdisj, fun i hi => (hmax i hi).1, hloc, fun hdata => ?_⟩
  have hscale : ∀ i ∈ J, ∀ q, dist i q ≤ 10 * r i →
      max (max Λ₁ Λ₂) (max Λ₃ Λ₄) ≤ r i / ρ q := fun i hi q hq => by
    have := (hloc i hi q hq).2
    linarith
  have hsec8 : ∀ i ∈ J, ∀ y ∈ riemannianBallOf g i (8 * (21 * r i)),
      SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * (r i)⁻¹ ^ 2)) := by
    intro i hi y hy
    apply (hdata i hi).1 y
    have hsub : riemannianBallOf g i (8 * (21 * r i)) ⊆ riemannianBallOf g i (400 * r i) := by
      rw [← inducedMetricSpace_ball g, ← inducedMetricSpace_ball g]
      exact ball_subset_ball (by nlinarith [hr i])
    exact hsub hy
  obtain ⟨hshell, hcover⟩ := hcond fun i hi => by
    obtain ⟨hsec, -, -, -, hδ, hφ, -, -⟩ := hdata i hi
    exact ⟨hsec, C i, mC i, o i, ⟨H i⟩, δ i, hδ.trans_le hδ₁', hφ⟩
  refine ⟨hshell, hcover, ?_, ?_, ?_⟩
  · intro i hi q hq1 hq2
    have hdim : dimH (univ : Set M) ≤ 3 := by
      have h := DifferentialGeometry.Geometry.Metric.dimH_univ_le_finrank_inducedMetricSpace g
      rw [hE] at h
      exact_mod_cast h
    exact h82 M (inducedMetricSpace_segments g) hdim C o r ρ hr hρpos J
      (fun j _ => ⟨H j⟩)
      (fun j hj => inducedMetricSpace_fourPointComparison_levels g j (by positivity)
        (hsec8 j hj) _ le_rfl)
      (fun j hj => ⟨δ j, ((hdata j hj).2.2.2.2.1).trans_le hδ₃', (hdata j hj).2.2.2.2.2.1⟩)
      (fun j hj q' hq' => hΛ₃'.trans (hscale j hj q' hq')) i hi q hq1 hq2
  · intro i hi q hq1 hq2 lam hlam hΛ
    obtain ⟨hsec, -, -, -, hδ, ⟨F⟩, hη, herr⟩ := hdata i hi
    have hsec' : ∀ y ∈ ball i (400 * r i),
        SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * (r i)⁻¹ ^ 2)) := by
      intro y hy
      rw [inducedMetricSpace_ball g] at hy
      exact hsec y hy
    exact h73 M g (inducedMetricSpace_hmetric g) i (r i) (hr i) hsec' (C i) (o i) (H i) F
      (hδ.trans_le hδ₄') (η i) hη herr q hq1 hq2 lam hlam (hΛ₄'.trans hΛ)
  · intro i hi
    obtain ⟨hsec, hNcomp, hNseg, hcone, hδ, ⟨F⟩, -, -⟩ := hdata i hi
    exact h77 M g ρ hρpos i (hr i) hsec
      (fun q hq => hΛ₂'.trans (hscale i hi q (by linarith [hr i]))) (hmax i hi).1
      (N i) (n₀ i) (C i) (o i) hNcomp hNseg hcone (hδ.trans_le hδ₂') ⟨F⟩

end DifferentialGeometry.Geometry.Collapse
