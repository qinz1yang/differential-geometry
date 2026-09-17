import DifferentialGeometry.Topology.Morse.CriticalLevelResolution
import DifferentialGeometry.Topology.Morse.NormalForm.Saddle

open Set Metric Filter Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ (MorseModel 2) H}
  [I.Boundaryless] [IsManifold I ∞ M]

open DifferentialGeometry.Morse CellAttachment in
theorem exists_ambient_isotopy_saddle_band
    {e : M → EuclideanSpace ℝ (Fin 2) × ℝ}
    (he : IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ e)
    {p : M} (hnd : IsNondegenerateCriticalPointAt I (fun x => (e x).2) p)
    (hindex : sigNeg (chartHessianAt (fun y => (e ((extChartAt I p).symm y)).2)
      (extChartAt I p p)) = 1)
    (hunique : ∀ x, (e x).2 = (e p).2 →
      IsCriticalPointAt I (fun y => (e y).2) x → x = p)
    {η : ℝ} (hη : 0 < η) :
    ∃ s : ℝ, ∃ hs : 0 < s, s < η ∧ ∃ r t h : ℝ, 0 < r ∧ 0 < t ∧ 0 < h ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I
          (EuclideanSpace ℝ (Fin 2)) M ∞,
        ∃ A : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ),
          closedBall 0 r ⊆ χ.source ∧ χ 0 = p ∧ (∀ z, (A z).2 = z.2) ∧
          MapsTo (saddleBandChart hs) (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) (ball 0 r) ∧
          ∃ Φ : ℝ → ((EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ)),
            ContDiff ℝ ∞ (fun z : ℝ × (EuclideanSpace ℝ (Fin 2) × ℝ) => Φ z.1 z.2) ∧
            ContDiff ℝ ∞ (fun z : ℝ × (EuclideanSpace ℝ (Fin 2) × ℝ) => (Φ z.1).symm z.2) ∧
            Φ 0 = Diffeomorph.refl 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
              (EuclideanSpace ℝ (Fin 2) × ℝ) ∞ ∧
            (∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h,
              Φ 1 (e (χ (saddleBandChart hs z))) =
                A (saddleBandChart hs z,
                  (e p).2 + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) ∧
            (∃ U : Set (ℝ × ℝ), IsOpen U ∧ (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) ⊆ U ∧
              MapsTo (saddleBandChart hs) U χ.source ∧
              ∀ z ∈ U, Φ 1 (e (χ (saddleBandChart hs z))) =
                A (saddleBandChart hs z,
                  (e p).2 + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2)) ∧
            (∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h,
              A (saddleBandChart hs z, (e p).2) ∈ range (Φ 1 ∘ e) ↔ z.1 = -1 ∨ z.1 = 1) ∧
            (∀ x, (Φ 1 (e x)).2 = (e p).2 →
              ¬ IsCriticalPointAt I (fun y => (Φ 1 (e y)).2) x) ∧
            (∀ x, IsCriticalPointAt I (fun y => (Φ 1 (e y)).2) x ↔
              IsCriticalPointAt I (fun y => (e y).2) x) ∧
            (∀ x, IsCriticalPointAt I (fun y => (e y).2) x →
              chartHessianAt (fun y => (Φ 1 (e ((extChartAt I x).symm y))).2)
                (extChartAt I x x) =
              chartHessianAt (fun y => (e ((extChartAt I x).symm y)).2)
                (extChartAt I x x)) ∧
            (fun y => (Φ 1 (e y)).2) =ᶠ[𝓝 p] (fun y => (e y).2 + s) ∧
            (∀ x, IsCriticalPointAt I (fun y => (e y).2) x → x ≠ p →
              (fun y => (Φ 1 (e y)).2) =ᶠ[𝓝 x] (fun y => (e y).2)) ∧
            ∃ K : Set (EuclideanSpace ℝ (Fin 2) × ℝ), IsCompact K ∧
              K ⊆ A '' (ball 0 r ×ˢ ball (e p).2 t) ∧ ∀ u : ℝ,
                EqOn (Φ u) id Kᶜ ∧ EqOn (Φ u).symm id Kᶜ := by
  let q := fun y => morseNormalForm (n := 2) (k := 1) (by omega) (e p).2
    (EuclideanSpace.equiv (Fin 2) ℝ y)
  obtain ⟨r, t, hr, ht, χ, A, hχ, hχ0, hAh, hgraph, hset, ρ, _, _, _, hρone,
    ε, hε, hfamily⟩ := exists_ambient_isotopy_critical_value_shift he 1 (by omega) hnd hindex hunique
  obtain ⟨δ, hδ, hδone⟩ := Metric.mem_nhds_iff.mp hρone
  let R := min r δ
  have hR : 0 < R := lt_min hr hδ
  have hRr : R ≤ r := min_le_left _ _
  have hRδ : R ≤ δ := min_le_right _ _
  let s := min η (min ε (R ^ 2 / 4)) / 2
  have hmin : 0 < min η (min ε (R ^ 2 / 4)) := lt_min hη (lt_min hε (by positivity))
  have hs : 0 < s := half_pos hmin
  have hsmin : s < min η (min ε (R ^ 2 / 4)) := half_lt_self hmin
  have hsη : s < η := hsmin.trans_le (min_le_left _ _)
  have hsε : |s| < ε := by
    rw [abs_of_pos hs]
    exact hsmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsR : 2 * s < R ^ 2 := by
    have hs4 := hsmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    nlinarith [sq_pos_of_pos hR]
  obtain ⟨_, Φ, hΦ, hΦi, hΦ0, hΦgraph, hregular, hcritical, hhessian, hpgerm, hgerm,
    K, hK, hKO, hfix⟩ := hfamily s hsε
  let g := fun y => q y + s * ρ y
  have hg : EqOn g (fun y => q y + s) (ball 0 R) := by
    intro y hy
    have hρy : ρ y = 1 := hδone ((ball_subset_ball hRδ) hy)
    simp only [g, hρy, mul_one]
  obtain ⟨h, hh, hband, _, _⟩ := exists_saddle_band_of_eqOn hs hR hsR hg
  have hbandr : MapsTo (saddleBandChart hs) (Icc (-1 : ℝ) 1 ×ˢ Icc (-h) h) (ball 0 r) :=
    hband.mono_right (ball_subset_ball hRr)
  have hlevel_actual (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ ball 0 r) :
      A (y, (e p).2) ∈ range (Φ 1 ∘ e) ↔ g y = (e p).2 := by
    constructor
    · rintro ⟨x, hx⟩
      have hxO : e x ∈ A '' (ball 0 r ×ˢ ball (e p).2 t) := by
        by_cases hxK : e x ∈ K
        · exact hKO hxK
        · have hxeq : e x = A (y, (e p).2) := by
            rw [Function.comp_apply, (hfix 1).1 hxK] at hx
            exact hx
          rw [hxeq]
          exact ⟨(y, (e p).2), ⟨hy, mem_ball_self ht⟩, rfl⟩
      obtain ⟨z, hz, hzx⟩ := hxO
      have hzrange : z ∈ range (A.symm ∘ e) := by
        refine ⟨x, ?_⟩
        change A.symm (e x) = z
        rw [← hzx, A.symm_apply_apply]
      obtain ⟨v, _, hvz⟩ := hset.subset
        ⟨⟨ball_subset_closedBall hz.1, ball_subset_closedBall hz.2⟩, hzrange⟩
      have hvx : e x = A (v, q v) := by rw [← hzx, ← hvz]
      have heq : A (v, g v) = A (y, (e p).2) := by
        change Φ 1 (e x) = A (y, (e p).2) at hx
        rw [hvx, hΦgraph] at hx
        exact hx
      have hpair := A.injective heq
      have hvy : v = y := congrArg Prod.fst hpair
      exact hvy ▸ congrArg Prod.snd hpair
    · intro hyc
      refine ⟨χ y, ?_⟩
      change Φ 1 (e (χ y)) = A (y, (e p).2)
      rw [hgraph y (ball_subset_closedBall hy), hΦgraph]
      exact congrArg A (Prod.ext rfl hyc)
  have hgraph_open (z : ℝ × ℝ) (hz : saddleBandChart hs z ∈ ball 0 R) :
      Φ 1 (e (χ (saddleBandChart hs z))) = A (saddleBandChart hs z,
        (e p).2 + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2) := by
    rw [hgraph _ (ball_subset_closedBall ((ball_subset_ball hRr) hz)), hΦgraph]
    change A (saddleBandChart hs z, g (saddleBandChart hs z)) = _
    rw [hg hz]
    apply congrArg A
    apply congrArg (Prod.mk (saddleBandChart hs z))
    have heq := morseNormalForm_saddleBandChart hs (e p).2 z
    dsimp only [q]
    linarith
  refine ⟨s, hs, hsη, r, t, h, hr, ht, hh, χ, A, hχ, hχ0, hAh, hbandr,
    Φ, hΦ, hΦi, hΦ0, fun z hz => hgraph_open z (hband hz), ?_, ?_,
    hregular hs.ne', hcritical, hhessian, hpgerm, hgerm, K, hK, hKO, hfix⟩
  · exact ⟨(saddleBandChart hs) ⁻¹' ball 0 R,
      isOpen_ball.preimage (saddleBandChart hs).contMDiff.continuous, hband,
      fun z hz => hχ (ball_subset_closedBall ((ball_subset_ball hRr) hz)), hgraph_open⟩
  · intro z hz
    rw [hlevel_actual _ (hbandr hz), hg (hband hz)]
    exact morseNormalForm_saddleBandChart_eq_iff hs (e p).2 z

end DifferentialGeometry.Topology.Morse
