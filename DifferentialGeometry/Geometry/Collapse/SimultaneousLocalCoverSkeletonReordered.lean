import DifferentialGeometry.Geometry.Collapse.SimultaneousLocalCoverSkeleton
import DifferentialGeometry.Geometry.Collapse.SharedInteriorAssignmentReordered

/-!
# LPA06's skeleton on LPA04's tail in the blueprint parameter order

`eventually_simultaneous_local_cover_reordered` is `eventually_simultaneous_local_cover`
(`SimultaneousLocalCoverSkeleton.lean`) with the parameters in the order of LPA04 (A:30461–30515):
`a₂, γ, β₀`; `β₂, Δ, s`; LFR44's `a₀`; the collapsed-model error `σ ≤ min a₂ η₁₈ a₀`; `Λ`; LC09's
`w₀` and ONE `w` (fixing `v_*` and `𝒜`); THEN the strong quality `b`, LFR44's `b₀`, the tolerances
`β` with `β 1 < b₀`, `ζ` and the zero constants `εz, δ', Λ'`; `T, V` last. The conclusion is
unchanged.

The proof re-chains the same lemmas (`eventually_shared_interior_assignment_reordered`,
`exists_finite_strong_edge_cover_riemannian`, `exists_selected_zero_packets_with_cutoffs`); the
old theorem's tail (slim support cover, strong-edge family, cover of the manifold, zero family)
is inline, so it is copied unchanged; `ncard_disjoint_family_balls_le` is cited.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LPA06 skeleton on LPA04's tail, blueprint parameter order** (see the module docstring). -/
theorem eventually_simultaneous_local_cover_reordered (hdim : Module.finrank ℝ E = 3) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ →
      ∀ s : ℝ, 0 < s → s < 1 / 100 → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ b : ℝ, 0 < b → b < 1 / 100 → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εz δ' Λ' : ℝ, 0 < εz ∧ 0 < δ' ∧ 0 < Λ' ∧
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
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        (∀ L : ℝ, 0 < L → 2 * L < α i → ∀ (p : X i), ∀ y ∈ ball p (L * ρ p),
          SectionalBoundedBelowAt (g i) y (-((L * ρ p) ^ 2)⁻¹)) ∧
        (∀ s : ℝ, 0 < s → 800 * s < α i → ∀ (p : X i), ∀ y ∈ ball p (400 * (s * ρ p)),
          SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (s * ρ p)⁻¹ ^ 2))) ∧
        (∀ p : X i, ∃ (C : Type) (mC : MetricSpace C), letI := mC
          ∃ c : C, CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
            fourPointComparison 0 (univ : Set C) ∧
            (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
              f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
              ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
            Nonempty (@KleinerLottApprox (X i) C
              ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ)) ∧
        (∀ p : X i, scaledSplittingRank.{u, 0} ρ hρpos β p ≤ 2) ∧
        (∀ p : X i, p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 0 ∨
          p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1 ∨
          p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 2) ∧
        (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 2,
          ∃ (C : Type) (mC : MetricSpace C) (c : C), letI := mC
          CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
          fourPointComparison 0 (univ : Set C) ∧
          Nonempty (@KleinerLottApprox (X i) C
            ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ) ∧
          ∃ (Y : Type) (mY : MetricSpace Y) (a : Y), letI := mY
            ∃ F : @KleinerLottApprox (X i) _ ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _
              p (WithLp.toLp 2 ((0 : ℝ²), a)) (β 2),
            let hmet := hmetric i
            let hMc : CompleteSpace (X i) := complete_of_compact
            letI := (mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI := ((mX i).rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hMc
            letI := radialScaledBundle (g i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI := radialScaledContinuous (g i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI := radialScaledManifold (m := mX i) (g i) hmet (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            ∃ η : X i → ℝ², ∃ hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball p 200),
            ∃ hrank : ∀ x ∈ ball p 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x),
              η p = 0 ∧ LipschitzOnWith 2 η (ball p 200) ∧
              (∀ x ∈ ball p 200, ‖η x - (F.toFun x).fst‖ < γ) ∧
              (∀ x ∈ ball p 200, ‖η x‖ < 100 → x ∈ ball p 102) ∧
              (∀ x ∈ ball p 200, η x = 0 → x ∈ ball p 2) ∧
              (∀ x ∈ ball p 2, ‖η x‖ ≤ 8) ∧
              (let f := diskPreimageMap (ball p 200) isOpen_ball η hη.continuousOn 100
              ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧
                (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧ Surjective f ∧
                (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
                ∀ R (hR : 0 < R) (hRr : R < 100),
                  let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
                  letI := regularFiberChartedSpace f y₀
                    (contMDiff_diskPreimageMap isOpen_ball hη 100)
                    (fun x _ => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
                  let U : TopologicalSpace.Opens
                      (diskPreimageOpens (ball p 200) isOpen_ball η hη.continuousOn 100) :=
                    ⟨f ⁻¹' planeBallInner 100 R,
                      (planeBallInner 100 R).isOpen.preimage
                        (continuous_diskPreimageMap isOpen_ball hη.continuousOn 100)⟩
                  ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
                      (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
                      ({x // f x = y₀} × planeBallInner 100 R) U ∞),
                    (∀ z, f (Θ z).1 = z.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)) ∧
              (Module.finrank ℝ E = 3 → ∀ z : planeBallOpens 100,
                let f := diskPreimageMap (ball p 200) isOpen_ball η hη.continuousOn 100
                letI := regularFiberChartedSpace f z (contMDiff_diskPreimageMap isOpen_ball hη 100)
                  (fun x _ => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
                Nonempty (Circle ≃ₘ⟮𝓡 1,
                  𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯ {x // f x = z})) ∧
              ∃ ζ : X i → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
                (∀ x, ζ x ∈ Icc 0 1) ∧ (∀ x ∈ ball p 200, ‖η x‖ ≤ 8 → ζ x = 1) ∧
                (∀ x, ζ x ≠ 0 → x ∈ ball p 200 ∧ ‖η x‖ < 9) ∧
                tsupport ζ ⊆ {x | x ∈ ball p 200 ∧ ‖η x‖ ≤ 9} ∧
                tsupport ζ ⊆
                  (diskPreimageOpens (ball p 200) isOpen_ball η hη.continuousOn 100 : Set (X i)) ∧
                @ball (X i) (mX i).toPseudoMetricSpace p (2 * ρ p) ⊆
                  (diskPreimageOpens (ball p 200) isOpen_ball η hη.continuousOn 100 : Set (X i)) ∩
                    {x | ζ x = 1} ∧
                tsupport ζ ⊆ @ball (X i) (mX i).toPseudoMetricSpace p (200 * ρ p)) ∧
        ∃ J : Set (X i), J.Finite ∧ J ⊆ scaledSplittingStratum.{u, 0} ρ hρpos β 2 ∧
          J.PairwiseDisjoint (fun p => ball p (ρ p / 3)) ∧
          (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 2, ∃ j ∈ J,
            ball p (ρ p) ⊆ ball j (2 * ρ j)) ∧
          (∀ x : X i, ((J ∩ {j | x ∈ ball j (2000000 * ρ j)}).ncard : ℝ) ≤
            modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
              modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) ∧
          ∃ Js Je : Set (X i),
            Js.Finite ∧
            Js ⊆ {p | p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1 ∧
              (∃ (A : Type) (mA : MetricSpace A) (a : A), letI := mA
                Bornology.IsBounded (univ : Set A) ∧ diam (univ : Set A) < 1000 * Δ ∧
                Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × A))
                  ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
                  (WithLp.toLp 2 ((0 : ℝ), a)) (β 1)))} ∧
            Js.PairwiseDisjoint (fun j => ball j (Δ * ρ j / 3)) ∧
            (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1,
              (∃ (A : Type) (mA : MetricSpace A) (a : A), letI := mA
                Bornology.IsBounded (univ : Set A) ∧ diam (univ : Set A) < 1000 * Δ ∧
                Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × A))
                  ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
                  (WithLp.toLp 2 ((0 : ℝ), a)) (β 1))) →
              ∃ j ∈ Js, ball p (Δ * ρ p) ⊆ ball j (2 * (Δ * ρ j))) ∧
            (∀ x : X i, ((Js ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard : ℝ) ≤
              modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
                modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) ∧
            Je.Finite ∧
            (∀ j ∈ Je, @isEdgePoint.{u, 0} (X i)
              ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) j Δ b s) ∧
            Je.PairwiseDisjoint (fun j => ball j (Δ * ρ j / 3)) ∧
            (∀ a : X i, @isEdgePoint.{u, 0} (X i)
              ((mX i).rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ b s →
              ∃ j ∈ Je, dist a j < Δ * ρ j) ∧
            (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1,
              ¬ (∃ (A : Type) (mA : MetricSpace A) (a : A), letI := mA
                  Bornology.IsBounded (univ : Set A) ∧ diam (univ : Set A) < 1000 * Δ ∧
                  Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × A))
                    ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
                    (WithLp.toLp 2 ((0 : ℝ), a)) (β 1))) →
              ∃ j ∈ Je, dist p j < 2 * Δ * ρ j) ∧
            (∀ x : X i, ((Je ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard : ℝ) ≤
              modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3
                  (4 * (1 + 2 * 2000000 + 1 / 3)) /
                modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3 (1 / 3)) ∧
            (∀ x : X i, x ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 0 ∨
              (∃ j ∈ J, x ∈ ball j (2 * ρ j)) ∨ (∃ j ∈ Js, x ∈ ball j (2 * (Δ * ρ j))) ∨
              ∃ j ∈ Je, dist x j < 2 * Δ * ρ j) ∧
            ∀ r : X i → ℝ, ∀ hlower : ∀ p, T * ρ p ≤ r p, (∀ p, r p ≤ V * ρ p) →
            ∀ (N C : X i → Type v) [mN : ∀ j, MetricSpace (N j)] [∀ j, ProperSpace (N j)]
              [mC : ∀ j, MetricSpace (C j)] [∀ j, ProperSpace (C j)]
              (n₀ : ∀ j, N j) (o : ∀ j, C j), (∀ j, RadialConeData (o j)) →
            ∀ (δ : X i → ℝ) (η : X i → X i → ℝ) (O : X i → Set (X i)) {e : ℝ}, e < 1 / 40 →
            ∃ J₀ : Set (X i), J₀.Finite ∧ J₀.PairwiseDisjoint (fun j => ball j (r j)) ∧
              ((∀ j ∈ J₀,
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
                εz * ((r j)⁻¹ * dist x y)) ∧
              Continuous (η j) ∧ IsOpen (O j) ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η j) (O j) ∧
              η j ⁻¹' Icc (1 / 5 : ℝ) (9 / 10) ⊆ O j ∧
              (∀ x, |η j x - (r j)⁻¹ * dist x j| < e) ∧
              ∀ q ∈ η j ⁻¹' Icc (1 / 5 : ℝ) (9 / 10),
                Real.sqrt ((scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                  ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)).inner q
                  (gradFun (scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                    ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)) (η j) q)
                  (gradFun (scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                    ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)) (η j) q)) ≤ 1 + εz) →
                scaledSplittingStratum.{u, 0} ρ hρpos β 0 ⊆ ⋃ j ∈ J₀, ball j (r j / 10) ∧
                ∃ L : ℝ, 0 ≤ L ∧
              (∀ j ∈ J₀,
                let ζi : X i → ℝ := fun x => annularCutoff cutoffProfile (η j x)
                let gr := scaleMetric ((r j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                  ((mul_pos hT (hρpos j)).trans_le (hlower j))) 2) (g i)
                ContMDiff I 𝓘(ℝ, ℝ) ∞ ζi ∧ (∀ x, ζi x ∈ Icc (0 : ℝ) 1) ∧
                (∀ x, η j x ∈ Icc (3 / 10 : ℝ) (4 / 5) → ζi x = 1) ∧
                tsupport ζi ⊆
                  {x | (1 / 5 - e) * r j < dist x j ∧ dist x j < (9 / 10 + e) * r j} ∧
                tsupport ζi ⊆ ball j (r j) ∧ HasCompactSupport ζi ∧
                (∀ q, Real.sqrt (gr.inner q (gradFun gr ζi q) (gradFun gr ζi q)) ≤ L * (1 + εz)) ∧
                ball j (r j / 10) ⊆ {x | η j x < 1 / 5}) ∧
            J₀.PairwiseDisjoint fun j =>
              tsupport fun x => annularCutoff cutoffProfile (η j x)) := by
  obtain ⟨a₂, ha₂, hS2⟩ :=
    eventually_shared_interior_assignment_reordered.{uE, uH, u} (E := E) (H := H) (I := I) hdim
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hS2⟩ := hS2 γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ s hs hssmall => ?_⟩
  obtain ⟨a₀, ha₀, hE44⟩ := exists_finite_strong_edge_cover_riemannian.{u, 0, 0, 0} (E := E)
    (H := H) (I := I) hβ₂ hβ₂small hΔ hs hssmall
  refine ⟨a₀, ha₀, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  have hΔpos : 0 < Δ := by linarith
  have hΛs : Λ * 2000000 ≤ 1 / 100 := by nlinarith
  obtain ⟨w₀, hw₀, hS2⟩ := hS2 σ hσ hσa hση Λ hΛ hΛs
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb hbsmall => ?_⟩
  obtain ⟨b₀, hb₀, hE44⟩ := hE44 b hb hbsmall
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  obtain ⟨εz, δ', Λ', hεz, -, hδ', hΛ', hZ⟩ :=
    exists_selected_zero_packets_with_cutoffs.{u, v} (E := E) (H := H) (I := I) hdim hβ1 hβone
      hβζ hζone
  refine ⟨εz, δ', Λ', hεz, hδ', hΛ', fun T V hT hTΛ hTV X mX _ _ _ g hmetric α hα hstand => ?_⟩
  filter_upwards [hS2 w hw hww hwc β (by rw [hβ2]; exact hβ₂) (by rw [hβ2]; exact hβ₂β₀) hβ3 X g
    hmetric α hα hstand, hα.eventually_gt_atTop (800 * V),
    hα.eventually_gt_atTop (2 * ((3 * 2000000 + 2 / 3) * Δ)),
    hα.eventually_gt_atTop (2 * (4 * (1 + 2 * 2000000 + 1 / 3) * Δ))] with i hi hαV hαs hαe
  obtain ⟨ρ, hρpos, hρsm, hρlip, hρb, hsecL, hzero, hmod, hrank, htri, hcirc, J, hJfin, hJS,
    hJdisj, hJcov, hJmult⟩ := hi
  refine ⟨ρ, hρpos, hρsm, hρlip, hρb, hsecL, hzero, hmod, hrank, htri, hcirc, J, hJfin, hJS,
    hJdisj, hJcov, hJmult, ?_⟩
  rcases isEmpty_or_nonempty (X i) with hX | ⟨⟨p₀⟩⟩
  · refine ⟨∅, ∅, finite_empty, empty_subset _, pairwiseDisjoint_empty,
      fun p _ _ => (hX.false p).elim, fun x => (hX.false x).elim, finite_empty,
      fun j hj => absurd hj (notMem_empty j), pairwiseDisjoint_empty,
      fun a _ => (hX.false a).elim, fun p _ _ => (hX.false p).elim,
      fun x => (hX.false x).elim, fun x => (hX.false x).elim, ?_⟩
    intro r _ _ N C _ _ _ _ n₀ o _ δ η O e _
    exact ⟨∅, finite_empty, pairwiseDisjoint_empty, fun _ => ⟨fun x _ => (hX.false x).elim, 0,
      le_rfl, fun j hj => absurd hj (notMem_empty j), pairwiseDisjoint_empty⟩⟩
  have : ConnectedSpace (X i) := connectedSpace_of_aligned_metric (g i) (hmetric i) p₀
  let : RiemannianBundle (fun x : X i => TangentSpace I x) := ⟨(g i).toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (fun x : X i => TangentSpace I x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric (g i)
  have : IsRiemannianManifold I (X i) := by
    constructor
    intro a b
    change edist a b = riemannianEDistOf (g i) a b
    rw [edist_dist, hmetric]
  have hEnorm : IsMetricNorm (I := I) (g i) := isMetricNorm_of_riemannianBundle (g i)
  have : IsManifold I 1 (X i) := IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : T2Space (TangentBundle I (X i)) := inferInstance
  -- the slim family: X77's support cover with `r = Δ ρ`
  have hrlip : LipschitzWith (Real.toNNReal (Δ * Λ)) (fun p => Δ * ρ p) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := hρlip.dist_le_mul x y
    rw [Real.coe_toNNReal _ hΛ.le] at h
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hΔpos, Real.coe_toNNReal _ (by positivity),
      mul_assoc]
    rw [Real.dist_eq] at h
    exact mul_le_mul_of_nonneg_left h hΔpos.le
  have hsmall : ((Real.toNNReal (Δ * Λ) : NNReal) : ℝ) * 2000000 ≤ 1 / 100 := by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact hΛΔ
  have hsecs : ∀ p ∈ {p | p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1 ∧
        (∃ (A : Type) (mA : MetricSpace A) (a : A), letI := mA
          Bornology.IsBounded (univ : Set A) ∧ diam (univ : Set A) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × A))
            ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
            (WithLp.toLp 2 ((0 : ℝ), a)) (β 1)))}, ∀ y ∈ ball p ((3 * 2000000 + 2 / 3) * (Δ * ρ p)),
      SectionalBoundedBelowAt (g i) y (-((2000000 * (Δ * ρ p)) ^ 2)⁻¹) := by
    intro p _ y hy
    have hy' : y ∈ ball p ((3 * 2000000 + 2 / 3) * Δ * ρ p) := by rwa [mul_assoc]
    refine (hsecL ((3 * 2000000 + 2 / 3) * Δ) (by positivity) hαs p y hy').mono ?_
    have hρp := hρpos p
    rw [neg_le_neg_iff]
    apply inv_anti₀ (by positivity)
    have hΔρ := mul_pos hΔpos hρp
    have h1 : 2000000 * (Δ * ρ p) ≤ (3 * 2000000 + 2 / 3) * Δ * ρ p := by
      rw [mul_assoc]
      linarith
    exact pow_le_pow_left₀ (by positivity) h1 2
  obtain ⟨Js, hJsS, hJsfin, hJsdisj, hJscov, hJsmult⟩ :=
    exists_simultaneous_support_cover (g i) hEnorm hdim
      {p | p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1 ∧
        (∃ (A : Type) (mA : MetricSpace A) (a : A), letI := mA
          Bornology.IsBounded (univ : Set A) ∧ diam (univ : Set A) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × A))
            ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
            (WithLp.toLp 2 ((0 : ℝ), a)) (β 1)))} hrlip
      (fun p => mul_pos hΔpos (hρpos p)) hsmall hsecs
  -- the strong-edge family: LFR44 on the same tail and scale
  obtain ⟨Je, hJefin, hJeE, hJedisj, hJecovE, hJecov⟩ :=
    hE44 (X i) (g i) (hmetric i) (Real.toNNReal Λ) ρ hρpos hρlip
      (by rw [Real.coe_toNNReal _ hΛ.le]; exact hΛ44) β hβ2 hβ1b 0 0 (by norm_num) (by norm_num)
  have hns : ∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1,
      ¬ (∃ (A : Type) (mA : MetricSpace A) (a : A), letI := mA
          Bornology.IsBounded (univ : Set A) ∧ diam (univ : Set A) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × A))
            ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
            (WithLp.toLp 2 ((0 : ℝ), a)) (β 1))) →
      ∃ j ∈ Je, dist p j < 2 * Δ * ρ j := by
    intro p hp hnot
    obtain ⟨C, mC, c, hc1, -, hc3, hc4, hc5, hc6⟩ := hmod p
    refine (hJecov p hp ?_ ⟨C, mC, c, σ, hc1, hc5, hc3, hc4, hσa₀, hc6⟩).1
    intro A mA a hbdd hdiam hne
    exact hnot ⟨A, mA, a, hbdd, hdiam, hne⟩
  refine ⟨Js, Je, hJsfin, hJsS, hJsdisj, fun p hp hsl => hJscov p ⟨hp, hsl⟩, hJsmult, hJefin,
    hJeE, hJedisj, hJecovE, hns, ?_, ?_, ?_⟩
  · intro x
    have hbudget : ((Real.toNNReal Λ : NNReal) : ℝ) * (2000000 * Δ) ≤ 1 / 4 := by
      rw [Real.coe_toNNReal _ hΛ.le]
      nlinarith
    exact ncard_disjoint_family_balls_le (g i) hEnorm hdim hρlip hρpos hΔpos hbudget hJefin
      hJedisj (fun j _ => hsecL _ (by positivity) hαe j) x
  · intro x
    rcases htri x with h0 | h1 | h2
    · exact Or.inl h0
    · by_cases hsl : (∃ (A : Type) (mA : MetricSpace A) (a : A), letI := mA
          Bornology.IsBounded (univ : Set A) ∧ diam (univ : Set A) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × A))
            ((mX i).rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) _ x
            (WithLp.toLp 2 ((0 : ℝ), a)) (β 1)))
      · obtain ⟨j, hj, hsub⟩ := hJscov x ⟨h1, hsl⟩
        exact Or.inr (Or.inr (Or.inl ⟨j, hj, hsub (mem_ball_self (mul_pos hΔpos (hρpos x)))⟩))
      · exact Or.inr (Or.inr (Or.inr (hns x h1 hsl)))
    · obtain ⟨j, hj, hsub⟩ := hJcov x h2
      exact Or.inr (Or.inl ⟨j, hj, hsub (mem_ball_self (hρpos x))⟩)
  · intro r hlower hupper N C mN _ mC _ n₀ o H δ η O e he
    have hsec : ∀ p, ∀ y ∈ ball p (400 * r p),
        SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (r p)⁻¹ ^ 2)) := by
      intro p y hy
      have hρp := hρpos p
      have hsp : 0 < r p / ρ p := div_pos ((mul_pos hT hρp).trans_le (hlower p)) hρp
      have hrp : r p / ρ p * ρ p = r p := div_mul_cancel₀ _ hρp.ne'
      have hsV : r p / ρ p ≤ V := (div_le_iff₀ hρp).mpr (hupper p)
      have h := hzero (r p / ρ p) hsp (by linarith) p y (by rw [hrp]; exact hy)
      rwa [hrp] at h
    obtain ⟨J₀, hfin, hdisj, -, -, himp⟩ := hZ (X i) (g i) (hmetric i) r ρ hρsm.continuous
      hρpos hT hTΛ hTV hlower hupper hsec N C n₀ o H δ η O he
    refine ⟨J₀, hfin, hdisj, fun hdata => ?_⟩
    obtain ⟨-, hcov, -, -, L, hL0, hcut, hdisjsupp⟩ := himp hdata
    exact ⟨hcov, L, hL0, hcut, hdisjsupp⟩

end DifferentialGeometry.Geometry.Collapse
