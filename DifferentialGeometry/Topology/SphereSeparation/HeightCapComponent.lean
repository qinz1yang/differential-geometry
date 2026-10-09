import DifferentialGeometry.Topology.SphereSeparation.HeightNormalForm
import DifferentialGeometry.Topology.Morse.ExtremumIndex
import DifferentialGeometry.Topology.Morse.QuadraticComponent

open Set Metric
open Manifold
open scoped Manifold ContDiff
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_global_height_preserving_local_maximum_cap {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    {p : SphereTwo}
    (hnd : IsNondegenerateCriticalPointAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun x => e x 2) p)
    (hmax : IsLocalMax (fun x => e x 2) p) :
    ∃ R : ℝ, 0 < R ∧ ∃ t : ℝ, 0 < t ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞,
        ∃ Φ : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
          closedBall 0 R ⊆ χ.source ∧ χ 0 = p ∧ (∀ z, Φ z 2 = z 2) ∧
          (∀ y ∈ χ.source,
            e (χ y) 2 = e p 2 + (-1) / 2 * ‖y‖ ^ 2 ∧
            Φ ((EuclideanSpace.equivProdLast 2).symm
              (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) = e (χ y)) ∧
          ((closedBall 0 R ×ˢ closedBall (e p 2) t) ∩
              range (fun x => EuclideanSpace.equivProdLast 2 (Φ.symm (e x))) =
            (fun y => (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 R) ∧
          ∀ r : ℝ, 0 ≤ r → r ≤ R →
            χ '' closedBall 0 r =
              connectedComponentIn {x | e p 2 + (-1) / 2 * r ^ 2 ≤ e x 2} p ∧
            χ '' sphere 0 r =
              connectedComponentIn {x | e p 2 + (-1) / 2 * r ^ 2 ≤ e x 2} p ∩
                {x | e x 2 = e p 2 + (-1) / 2 * r ^ 2} := by
  have hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p).symm y) 2)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p p)) = 2 := by
    simpa using maximum_morse_index_eq_finrank hf hnd hmax
  obtain ⟨R, hR, t, ht, χ, Φ, hsource, hχ0, hheight, hnormal, _, hgraph⟩ :=
    exists_global_height_preserving_normal_neighborhood he 2 le_rfl hnd hindex
  have hquad (y : EuclideanSpace ℝ (Fin 2)) : morseNormalForm (le_refl 2) (e p 2)
      (EuclideanSpace.equiv (Fin 2) ℝ y) = e p 2 + (-1) / 2 * ‖y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [morseNormalForm, posIdx, negIdx, Fin.sum_univ_two]
    ring
  simp_rw [hquad] at hnormal hgraph
  let χ' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict χ (ball 0 R) isOpen_ball
  have hsource' : χ'.source = ball 0 R :=
    inter_eq_right.mpr (ball_subset_closedBall.trans hsource)
  have hRs : closedBall 0 (R / 2) ⊆ χ'.source := by
    rw [hsource']
    exact closedBall_subset_ball (half_lt_self hR)
  have hnormal' (y) (hy : y ∈ χ'.source) :
      e (χ' y) 2 = e p 2 + (-1) / 2 * ‖y‖ ^ 2 ∧
      Φ ((EuclideanSpace.equivProdLast 2).symm
        (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) = e (χ' y) := by
    have hn := hnormal y (ball_subset_closedBall (hsource' ▸ hy))
    refine ⟨?_, hn⟩
    change e (χ y) 2 = _
    rw [← hn, hheight]
    exact EuclideanSpace.equivProdLast_symm_last (n := 2) _
  have hsmall : closedBall (0 : EuclideanSpace ℝ (Fin 2)) (R / 2) ⊆ closedBall 0 R :=
    closedBall_subset_closedBall (half_le_self hR.le)
  have hgraph' : (closedBall 0 (R / 2) ×ˢ closedBall (e p 2) t) ∩
      range (fun x => EuclideanSpace.equivProdLast 2 (Φ.symm (e x))) =
        (fun y => (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 (R / 2) := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨y, hy, hyz⟩ := hgraph.subset ⟨⟨hsmall hz.1.1, hz.1.2⟩, hz.2⟩
      refine ⟨y, ?_, hyz⟩
      simpa only [← hyz] using hz.1.1
    · rintro z ⟨y, hy, rfl⟩
      have hz := hgraph.symm.subset (mem_image_of_mem _ (hsmall hy))
      exact ⟨⟨hy, hz.1.2⟩, hz.2⟩
  refine ⟨R / 2, half_pos hR, t, ht, χ', Φ, hRs, hχ0, hheight, hnormal', hgraph', ?_⟩
  intro r hr hrR
  have hrs : closedBall 0 r ⊆ χ'.source :=
    (closedBall_subset_closedBall hrR).trans hRs
  have hχ0' : χ'.toOpenPartialHomeomorph 0 = p := hχ0
  have hcomponent := χ'.toOpenPartialHomeomorph.closedBall_image_eq_connectedComponentIn_superlevel
    hr (isCompact_closedBall 0 r) hrs (by norm_num : (-1 : ℝ) < 0)
    (f := fun x => e x 2) (fun y hy => by
      change e (χ' y) 2 = e (χ' 0) 2 + (-1) / 2 * ‖y‖ ^ 2
      simpa only [show χ' 0 = p from hχ0] using (hnormal' y hy).1)
  change χ' '' closedBall 0 r = _ at hcomponent
  simp only [hχ0'] at hcomponent
  change χ' '' closedBall 0 r =
    connectedComponentIn {x | e p 2 + (-1) / 2 * r ^ 2 ≤ e x 2} p at hcomponent
  refine ⟨hcomponent, ?_⟩
  rw [← hcomponent]
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨mem_image_of_mem χ' (sphere_subset_closedBall hy), ?_⟩
    change e (χ' y) 2 = _
    rw [(hnormal' y (hrs (sphere_subset_closedBall hy))).1,
      mem_sphere_zero_iff_norm.mp hy]
  · rintro x ⟨⟨y, hy, rfl⟩, hlevel⟩
    refine ⟨y, ?_, rfl⟩
    rw [mem_sphere_zero_iff_norm]
    apply (sq_eq_sq₀ (norm_nonneg y) hr).mp
    have hn := (hnormal' y (hrs hy)).1
    change e (χ' y) 2 = _ at hlevel
    nlinarith

end DifferentialGeometry.Topology.SphereSeparation
