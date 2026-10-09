import DifferentialGeometry.Geometry.Collapse.ZeroPacketCutoffFamily
import DifferentialGeometry.Geometry.Collapse.SharedInteriorAssignment

/-!
# Consumer: the selected zero family with its cutoffs on LPA04's tail

LPA05 (A:30548) uses "LPA04's single assignment and tail". On the tail of
`eventually_shared_interior_assignment` (S2), with its ONE LC02 scale `ρ`, every radius function
`r` with `T ρ ≤ r ≤ V ρ` (`V` fixed before the tail) receives the original buffer from LPA01's
zero-scale clause, so `exists_selected_zero_packets_with_cutoffs` applies with NO curvature
hypothesis: the zero stratum is covered by the tenth balls of one finite disjoint family, whose
LC31 cutoffs have pairwise disjoint closed supports inside the selected balls.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter
open scoped Topology ContDiff Manifold ENNReal
open GC.MetricGeometry
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The zero family on LPA04's tail.** S2's constants, then LCP04's (from `β 1 < ζ < 1`), then
`T ≥ 20 Λ'` and `V ≥ T`; on ONE tail with ONE LC02 scale `ρ`, for every `r ∈ [Tρ, Vρ]` and all
witness families, one finite disjoint selection covers the zero stratum by tenth balls and its
LC31 cutoffs have disjoint closed supports inside the selected balls. -/
theorem eventually_zero_cutoff_family_of_assignment (hdim : Module.finrank ℝ E = 3) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ β : ℕ → ℝ, 0 < β 2 → β 2 ≤ β₀ → β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      0 < β 1 → β 1 < 1 → ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ ε δ' Λ' : ℝ, 0 < ε ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ Λ : ℝ, 0 < Λ → Λ * 2000000 ≤ 1 / 100 → ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ T V : ℝ, ∀ hT : 0 < T, 20 * Λ' ≤ T → T ≤ V →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧ LipschitzWith (Real.toNNReal Λ) ρ ∧
        ∀ r : X i → ℝ, ∀ hlower : ∀ p, T * ρ p ≤ r p, (∀ p, r p ≤ V * ρ p) →
        ∀ (N C : X i → Type v) [mN : ∀ j, MetricSpace (N j)] [∀ j, ProperSpace (N j)]
          [mC : ∀ j, MetricSpace (C j)] [∀ j, ProperSpace (C j)]
          (n₀ : ∀ j, N j) (o : ∀ j, C j), (∀ j, RadialConeData (o j)) →
        ∀ (δ : X i → ℝ) (η : X i → X i → ℝ) (O : X i → Set (X i)) {e : ℝ}, e < 1 / 40 →
        ∃ J : Set (X i), J.Finite ∧ J.PairwiseDisjoint (fun j => ball j (r j)) ∧
          ((∀ j ∈ J,
            fourPointComparison 0 (univ : Set (N j)) ∧
            (∀ x y : N j, ∃ f : Icc (0 : ℝ) 1 → N j,
              Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
              ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
            (∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
              R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox (N j) (C j)
                ((mN j).rescale R⁻¹ (inv_pos.mpr hR)) (mC j) (n₀ j) (o j) δ₁)) ∧
            δ j < δ' ∧
            Nonempty (@KleinerLottApprox (X i) (C j)
              ((mX i).rescale (r j)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos j)).trans_le (hlower j))))
              (mC j) j (o j) (δ j)) ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η j)
              {x | 3 / 40 ≤ (r j)⁻¹ * dist x j ∧ (r j)⁻¹ * dist x j ≤ 11} ∧
            (∀ x y, |(η j x - (r j)⁻¹ * dist j x) - (η j y - (r j)⁻¹ * dist j y)| ≤
              ε * ((r j)⁻¹ * dist x y)) ∧
            Continuous (η j) ∧ IsOpen (O j) ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η j) (O j) ∧
            η j ⁻¹' Icc (1 / 5 : ℝ) (9 / 10) ⊆ O j ∧
            (∀ x, |η j x - (r j)⁻¹ * dist x j| < e) ∧
            ∀ q ∈ η j ⁻¹' Icc (1 / 5 : ℝ) (9 / 10),
              Real.sqrt ((scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)).inner q
                (gradFun (scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                  ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)) (η j) q)
                (gradFun (scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                  ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)) (η j) q)) ≤ 1 + ε) →
          scaledSplittingStratum.{u, 0} ρ hρpos β 0 ⊆ ⋃ j ∈ J, ball j (r j / 10) ∧
          (∀ j ∈ J, tsupport (fun x => annularCutoff cutoffProfile (η j x)) ⊆ ball j (r j)) ∧
          J.PairwiseDisjoint fun j => tsupport fun x => annularCutoff cutoffProfile (η j x)) := by
  obtain ⟨a₂, ha₂, hS2⟩ :=
    eventually_shared_interior_assignment.{uE, uH, u} (E := E) (H := H) (I := I) hdim
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hS2⟩ := hS2 γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun β hβ2 hββ₀ hβ3 hβ1 hβone ζ hβζ hζone => ?_⟩
  obtain ⟨ε, δ', Λ', hε, -, hδ', hΛ', hZ⟩ :=
    exists_selected_zero_packets_with_cutoffs.{u, v} (E := E) (H := H) (I := I) hdim hβ1 hβone
      hβζ hζone
  refine ⟨ε, δ', Λ', hε, hδ', hΛ', fun σ hσ hσa hση Λ hΛ hΛs => ?_⟩
  obtain ⟨w₀, hw₀, hS2⟩ := hS2 β hβ2 hββ₀ hβ3 σ hσ hσa hση Λ hΛ hΛs
  refine ⟨w₀, hw₀, fun w hw hww hwc T V hT hTΛ hTV X mX _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [hS2 w hw hww hwc X g hmetric α hα hstand,
    hα.eventually_gt_atTop (800 * V)] with i hi hαi
  obtain ⟨ρ, hρpos, hρsm, hρlip, -, -, hzero, -⟩ := hi
  refine ⟨ρ, hρpos, hρsm, hρlip, fun r hlower hupper N C mN _ mC _ n₀ o H δ η O e he => ?_⟩
  rcases isEmpty_or_nonempty (X i) with hX | ⟨⟨p₀⟩⟩
  · refine ⟨∅, Set.finite_empty, Set.pairwiseDisjoint_empty, fun _ => ⟨fun x _ =>
      (IsEmpty.false x).elim, fun j hj => absurd hj (Set.notMem_empty j),
      Set.pairwiseDisjoint_empty⟩⟩
  · have : ConnectedSpace (X i) := connectedSpace_of_aligned_metric (g i) (hmetric i) p₀
    have hsec : ∀ p, ∀ y ∈ ball p (400 * r p),
        SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (r p)⁻¹ ^ 2)) := by
      intro p y hy
      have hρp := hρpos p
      have hs : 0 < r p / ρ p := div_pos ((mul_pos hT hρp).trans_le (hlower p)) hρp
      have hrp : r p / ρ p * ρ p = r p := div_mul_cancel₀ _ hρp.ne'
      have hsV : r p / ρ p ≤ V := (div_le_iff₀ hρp).mpr (hupper p)
      have h := hzero (r p / ρ p) hs (by linarith) p y (by rw [hrp]; exact hy)
      rwa [hrp] at h
    obtain ⟨J, hfin, hdisj, -, -, himp⟩ := hZ (X i) (g i) (hmetric i) r ρ hρsm.continuous
      hρpos hT hTΛ hTV hlower hupper hsec N C n₀ o H δ η O he
    refine ⟨J, hfin, hdisj, fun hdata => ?_⟩
    obtain ⟨-, hcov, -, -, L, -, hcut, hdisjsupp⟩ := himp hdata
    exact ⟨hcov, fun j hj => (hcut j hj).2.2.2.2.1, hdisjsupp⟩

end DifferentialGeometry.Geometry.Collapse
