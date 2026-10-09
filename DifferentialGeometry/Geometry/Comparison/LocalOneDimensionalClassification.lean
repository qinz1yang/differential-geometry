import DifferentialGeometry.Geometry.Comparison.UnitComparisonSegments
import DifferentialGeometry.Geometry.Comparison.CompleteFourPointComparison
import DifferentialGeometry.Geometry.Comparison.GlobalOneDimensionalModels
import DifferentialGeometry.Topology.MetricSpace.ModelTypeUniqueness
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

theorem pointed_one_dimensional_classification_of_local_unit_comparison
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hlocal : ∀ z : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω)
    (hdim : dimH (univ : Set X) ≤ 1) (p : X) :
    ((∃ e : X ≃ᵢ EuclideanSpace ℝ (Fin 0), e p = 0) ∨
    (∃ e : X ≃ᵢ ℝ, e p = 0) ∨
    (∃ a : ℝ, 0 ≤ a ∧ ∃ e : X ≃ᵢ Ici (0 : ℝ), (e p : ℝ) = a) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ a ∈ Icc (0 : ℝ) L, ∃ e : X ≃ᵢ Icc (0 : ℝ) L,
      (e p : ℝ) = a) ∨
    (∃ L : ℝ, 0 < L ∧ ∃ e : X ≃ᵢ AddCircle L, e p = 0)) ∧
    List.Pairwise (fun A B : Prop => ¬ (A ∧ B))
      [Nonempty (X ≃ᵢ EuclideanSpace ℝ (Fin 0)),
       Nonempty (X ≃ᵢ ℝ),
       Nonempty (X ≃ᵢ Ici (0 : ℝ)),
       ∃ L : ℝ, 0 < L ∧ Nonempty (X ≃ᵢ Icc (0 : ℝ) L),
       ∃ L : ℝ, 0 < L ∧ Nonempty (X ≃ᵢ AddCircle L)] := by
  classical
  let : ProperSpace X := properSpace_of_local_comparison_and_dimH hcurves
    (by norm_num : (0 : ℝ) ≤ 1) (n := 1) (by simpa using hdim) hlocal
  have hsegments := exists_metric_segment_of_locallyCompact_of_arbitrarily_short_curves hcurves
  have hisosegments : ∀ x y : X, ∃ σ : Icc (0 : ℝ) (dist x y) → X,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
    intro x y
    obtain ⟨f, _, hf0, hf1, hfd⟩ := hsegments x y
    exact exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
  have hcomp : fourPointComparison 1 (univ : Set X) :=
    fourPointComparison_of_complete_local_comparison (by norm_num) hisosegments hlocal
  have hopen := isOpen_segment_image_of_unit_comparison_and_dimH_le_one hcurves hcomp
    (fun z => ⟨1, zero_lt_one, isClosed_closedBall.isComplete⟩) hdim
  refine ⟨?_, one_dimensional_model_types_pairwise⟩
  rcases subsingleton_or_nontrivial X with hsub | hnontrivial
  · let e : X ≃ᵢ EuclideanSpace ℝ (Fin 0) :=
      { toFun := fun _ => 0
        invFun := fun _ => p
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _
        isometry_toFun := isometry_subsingleton }
    exact Or.inl ⟨e, rfl⟩
  · by_cases hc : IsCompact (univ : Set X)
    · let : CompactSpace X := ⟨hc⟩
      obtain ⟨D, hD, σ, hσ, hdiam⟩ := exists_diameter_isometric_segment hsegments
      by_cases hsurj : Function.Surjective σ
      · let f : Icc (0 : ℝ) D ≃ᵢ X := ⟨Equiv.ofBijective σ ⟨hσ.injective, hsurj⟩, hσ⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨D, hD, (f.symm p : ℝ), (f.symm p).property, f.symm, rfl⟩)))
      · have hout : ∃ x : X, x ∉ range σ := by
          by_contra hn
          apply hsurj
          intro x
          by_contra hx
          exact hn ⟨x, hx⟩
        obtain ⟨x, hx⟩ := hout
        obtain ⟨e, _⟩ := exists_circle_isometry_of_outside_diameter_segment
          (by norm_num : (0 : ℝ) ≤ 1) hcomp hsegments hD hσ (hopen 0 D σ hσ) hdiam hx
        let f := e.trans (IsometryEquiv.subRight (e p))
        exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨2 * D, by linarith, f, show e p - e p = 0 from sub_self _⟩)))
    · obtain ⟨r, hr, hr0⟩ := exists_isometric_ray_of_not_isCompact hsegments hc p
      rcases exists_line_or_ray_isometry_of_isometric_ray_of_open_segments
          (by norm_num : (0 : ℝ) ≤ 1) hcomp hsegments hopen hr with
        ⟨e, he0, _⟩ | ⟨a, ha, e, he0, _⟩
      · exact Or.inr (Or.inl ⟨e, hr0 ▸ he0⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨a, ha, e, hr0 ▸ he0⟩))

end DifferentialGeometry.Geometry.Comparison.Toponogov
