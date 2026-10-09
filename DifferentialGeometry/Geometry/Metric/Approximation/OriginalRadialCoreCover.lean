import DifferentialGeometry.Geometry.Metric.Approximation.OriginalRadialExport

/-!
# Original radial splittings on the chosen zero-stratum core cover

LC64 chooses one finite disjoint family from the original radius functions. The LC80 item 3
consumer supplies exact original radial splittings on its closed shells and excludes rank zero.
-/

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v

theorem exists_original_radial_zero_stratum_core_cover {β : ℕ → ℝ}
    (hβ : 0 < β 1) (hβone : β 1 < 1) :
    ∃ δ' Λ' : ℝ, 0 < δ' ∧ 0 < Λ' ∧
      ∀ (X : Type u) [m : MetricSpace X] [CompactSpace X],
      (∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
        Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      dimH (univ : Set X) ≤ 3 →
      ∀ (r ρ : X → ℝ), Continuous ρ → ∀ (hρpos : ∀ p, 0 < ρ p) {T U : ℝ} (hT : 0 < T),
      20 * Λ' ≤ T → T ≤ U → ∀ (hlower : ∀ p, T * ρ p ≤ r p), (∀ p, r p ≤ U * ρ p) →
      ∃ I : Set X, I.Finite ∧
        (∀ i ∈ I, (ball i (r i) ∩
            {q | @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}
          ).Nonempty ∧
          ∀ q, (ball q (r q) ∩ {q | @splittingRank.{u, 0} X
              (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}).Nonempty →
            ball i (r i) ⊆ ball q (r q) → r q ≤ 2 * r i) ∧
        I.PairwiseDisjoint (fun i => ball i (r i)) ∧
        (∀ i ∈ I, ∀ q, dist i q ≤ 10 * r i → r q ≤ 20 * r i ∧ T / 20 ≤ r i / ρ q) ∧
        {q | @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} ⊆
          ⋃ i ∈ I, ball i (5 * r i) ∧
        ((∀ i ∈ I, fourPointComparison ((1 / 60) ^ 2 * (r i)⁻¹ ^ 2) (ball i (21 * r i)) ∧
            ∃ (C : Type v) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧ ∃ δ : ℝ,
              δ < δ' ∧ Nonempty (@KleinerLottApprox X C
                (m.rescale (r i)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos i)).trans_le (hlower i))))
                mC i o δ)) →
          (∀ i ∈ I, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            (∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
              ∃ (z : Z) (F : @KleinerLottApprox X
                (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
                (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) inferInstance
                q (WithLp.toLp 2 (0, z)) (β 1)),
                ∀ x : X, (@KleinerLottApprox.toFun X
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
                  (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) inferInstance
                  q (WithLp.toLp 2 (0, z)) (β 1) F x).fst = WithLp.toLp 2
                    (Function.const (Fin 1) ((ρ q)⁻¹ * (dist i x - dist i q)))) ∧
            @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 ≠ 0) ∧
          {q | @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} ⊆
            ⋃ i ∈ I, ball i (r i / 10)) := by
  obtain ⟨δstar, Λstar, hδstar, hΛstar, hproduce⟩ :=
    exists_original_radial_splitting_parameter.{u, v} (n := 3) (by norm_num) hβ hβone
  refine ⟨δstar, Λstar, hδstar, hΛstar, ?_⟩
  intro X m hcompact hsegments hdim r ρ hρ hρpos T U hT hTΛ hTU hlower hupper
  let Z0 : Set X := {q | @splittingRank.{u, 0} X
    (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}
  have hr (p : X) : 0 < r p := (mul_pos hT (hρpos p)).trans_le (hlower p)
  obtain ⟨I, hfin, hmax, hdisj, hlocal, hcover, hsmall⟩ :=
    Metric.exists_zero_set_small_core_cover Z0 r ρ hρ hρpos hT hTU hlower hupper
  refine ⟨I, hfin, hmax, hdisj, hlocal, hcover, ?_⟩
  intro hdata
  have hshell : ∀ i ∈ I, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
      ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
        ∃ (z : Z) (F : @KleinerLottApprox X
          (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
          (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) inferInstance
          q (WithLp.toLp 2 (0, z)) (β 1)),
          ∀ x : X, (@KleinerLottApprox.toFun X
            (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
            (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) inferInstance
            q (WithLp.toLp 2 (0, z)) (β 1) F x).fst = WithLp.toLp 2
              (Function.const (Fin 1) ((ρ q)⁻¹ * (dist i x - dist i q))) := by
    intro i hi q hqlo hqhi
    obtain ⟨hcomparison, C, mC, o, ⟨H⟩, δ, hδ, ⟨F⟩⟩ := hdata i hi
    have hri : 0 < (r i)⁻¹ := inv_pos.mpr (hr i)
    have hlam : 0 < r i / ρ q := div_pos (hr i) (hρpos q)
    have hcomplete' : @CompleteSpace X (m.rescale (r i)⁻¹ hri).toUniformSpace :=
      (MetricSpace.rescale_completeSpace_iff m (r i)⁻¹ hri).mpr inferInstance
    have hdim' : @dimH X (m.rescale (r i)⁻¹ hri).toEMetricSpace univ ≤ 3 := by
      rw [MetricSpace.rescale_dimH]; exact hdim
    have hcomp : @fourPointComparison X (m.rescale (r i)⁻¹ hri) ((1 / 60) ^ 2)
        (@ball X (m.rescale (r i)⁻¹ hri).toPseudoMetricSpace i 21) := by
      have hb := MetricSpace.rescale_ball m (r i)⁻¹ hri i (21 * r i)
      have hc : (r i)⁻¹ * (21 * r i) = 21 := by field_simp [(hr i).ne']
      rw [hc] at hb
      rw [hb, fourPointComparison_rescale_iff (m := m) hri (by positivity)]
      exact hcomparison
    have hlo : 1 / 10 ≤ @dist X (m.rescale (r i)⁻¹ hri).toDist i q := by
      rw [MetricSpace.rescale_dist, le_inv_mul_iff₀ (hr i)]
      linarith only [hqlo]
    have hhi : @dist X (m.rescale (r i)⁻¹ hri).toDist i q ≤ 10 := by
      rw [MetricSpace.rescale_dist, inv_mul_le_iff₀ (hr i)]
      simpa only [mul_comm (r i)] using hqhi
    have hΛ : Λstar ≤ r i / ρ q := by
      linarith only [(hlocal i hi q hqhi).2, hTΛ]
    have hpack := @hproduce X (m.rescale (r i)⁻¹ hri) hcomplete'
      (rescale_segments m hri hsegments) hdim' C mC i o H δ F hδ hcomp q hlo hhi
      (r i / ρ q) hlam hΛ
    have heq : (m.rescale (r i)⁻¹ hri).rescale (r i / ρ q) hlam =
        m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q)) := by
      rw [MetricSpace.rescale_mul]
      congr 1
      field_simp [(hr i).ne', (hρpos q).ne']
    have hcoord (x : X) : (r i / ρ q) *
        (@dist X (m.rescale (r i)⁻¹ hri).toDist i x -
          @dist X (m.rescale (r i)⁻¹ hri).toDist i q) =
        (ρ q)⁻¹ * (dist i x - dist i q) := by
      simp only [MetricSpace.rescale_dist]
      field_simp [(hr i).ne', (hρpos q).ne']
    simp only [hcoord] at hpack
    rw [heq] at hpack
    exact hpack
  have hrank : ∀ i ∈ I, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
      @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 ≠ 0 := by
    intro i hi q hlo hhi
    obtain ⟨Z, mZ, z, F, hF⟩ := hshell i hi q hlo hhi
    have hsplit : @HasEuclideanSplitting.{u, 0} X
        (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q 1 (β 1) := ⟨Z, mZ, z, ⟨F⟩⟩
    have h := @le_splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q)))
      q β 3 1 (by norm_num) hsplit
    omega
  refine ⟨fun i hi q hlo hhi => ⟨hshell i hi q hlo hhi, hrank i hi q hlo hhi⟩, ?_⟩
  apply hsmall
  intro i hi z hz hshellz
  exact hrank i hi z hshellz.1 hshellz.2 hz

end GC.MetricGeometry
