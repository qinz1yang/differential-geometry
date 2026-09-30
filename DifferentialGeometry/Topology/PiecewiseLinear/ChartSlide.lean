import DifferentialGeometry.Topology.PiecewiseLinear.ModelSlide
import DifferentialGeometry.Topology.PiecewiseLinear.ChartConjugate

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def slideSupport : Set (ℝ × ℝ × ℝ) := {p | |p.2.1| + |p.2.2| ≤ 1 ∧ |p.1| ≤ 3}

theorem isClosed_slideSupport : IsClosed slideSupport := by
  have h1 : Continuous fun p : ℝ × ℝ × ℝ => |p.2.1| + |p.2.2| :=
    (continuous_abs.comp (continuous_fst.comp continuous_snd)).add
      (continuous_abs.comp (continuous_snd.comp continuous_snd))
  have h2 : Continuous fun p : ℝ × ℝ × ℝ => |p.1| := continuous_abs.comp continuous_fst
  exact (isClosed_le h1 continuous_const).inter (isClosed_le h2 continuous_const)

theorem slideSupport_subset_closedBall : slideSupport ⊆ Metric.closedBall 0 3 := by
  rintro p ⟨h1, h2⟩
  have hy : |p.2.1| ≤ 3 := by
    have := abs_nonneg p.2.2
    linarith
  have hz : |p.2.2| ≤ 3 := by
    have := abs_nonneg p.2.1
    linarith
  simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_le_iff]
  exact ⟨h2, hy, hz⟩

theorem isCompact_slideSupport : IsCompact slideSupport :=
  Metric.isCompact_of_isClosed_isBounded isClosed_slideSupport
    ((Metric.isBounded_closedBall).subset slideSupport_subset_closedBall)

theorem eqOn_slideMap_id_compl : EqOn slideMap id slideSupportᶜ := by
  intro p hp
  simp only [slideSupport, mem_compl_iff, mem_ofPred_eq, not_and_or, not_le] at hp
  rcases hp with h | h
  · exact slideMap_eq_self_of_width h.le
  · exact slideMap_eq_self_of_taper h.le

theorem slideAmount_le_max_taper (p : ℝ × ℝ × ℝ) : slideAmount p ≤ max 0 (slideTaper p) :=
  max_le_max (le_refl 0) (min_le_right _ _)

theorem mapsTo_slideMap_slideSupport : MapsTo slideMap slideSupport slideSupport := by
  rintro p ⟨h1, h2⟩
  have hnn := slideAmount_nonneg p
  have hmax := slideAmount_le_max_taper p
  rw [abs_le] at h2
  refine ⟨h1, ?_⟩
  have hfst : (slideMap p).1 = p.1 - slideAmount p := rfl
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rw [hfst]
    rcases le_total 0 p.1 with hx | hx
    · have hT : slideTaper p ≤ 3 / 2 := by
        simp only [slideTaper, abs_of_nonneg hx]
        linarith
      have hle : slideAmount p ≤ 3 / 2 := le_trans hmax (max_le (by norm_num) hT)
      linarith
    · have hT : slideTaper p = (3 + p.1) / 2 := by
        simp only [slideTaper, abs_of_nonpos hx]
        ring
      rw [hT] at hmax
      rcases le_total ((3 + p.1) / 2) 0 with hneg | hposs
      · rw [max_eq_left hneg] at hmax
        linarith
      · rw [max_eq_right hposs] at hmax
        linarith
  · rw [hfst]
    linarith

theorem mapsTo_slideMap_of_subset {T : Set (ℝ × ℝ × ℝ)} (hT : slideSupport ⊆ T) :
    MapsTo slideMap T T := by
  intro p hp
  by_cases hC : p ∈ slideSupport
  · exact hT (mapsTo_slideMap_slideSupport hC)
  · rw [eqOn_slideMap_id_compl hC]
    exact hp

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

theorem isPiecewiseAffineOn_chartSlide (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hsub : slideSupport ⊆ e.target) :
    IsPiecewiseAffineOn (e.conjugateMap slideMap) univ :=
  isPiecewiseAffineOn_conjugateMap e he hei
    (isPiecewiseAffineOn_slideMap.mono e.open_target (subset_univ _))
    (mapsTo_slideMap_of_subset hsub) isCompact_slideSupport hsub eqOn_slideMap_id_compl

omit [NormedSpace ℝ M] [FiniteDimensional ℝ M] in
theorem injective_chartSlide (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ))
    (hsub : slideSupport ⊆ e.target) : Function.Injective (e.conjugateMap slideMap) := by
  have hmaps := mapsTo_slideMap_of_subset hsub
  intro x y hxy
  by_cases hx : x ∈ e.source
  · by_cases hy : y ∈ e.source
    · rw [e.conjugateMap_of_mem _ hx, e.conjugateMap_of_mem _ hy] at hxy
      have h1 : slideMap (e x) ∈ e.target := hmaps (e.map_source hx)
      have h2 : slideMap (e y) ∈ e.target := hmaps (e.map_source hy)
      have hslide : slideMap (e x) = slideMap (e y) := by
        have := congrArg e hxy
        rwa [e.right_inv h1, e.right_inv h2] at this
      have hex : e x = e y := injective_slideMap hslide
      have := congrArg e.symm hex
      rwa [e.left_inv hx, e.left_inv hy] at this
    · rw [e.conjugateMap_of_mem _ hx, e.conjugateMap_of_notMem _ hy] at hxy
      exact absurd (hxy ▸ e.map_target (hmaps (e.map_source hx))) hy
  · by_cases hy : y ∈ e.source
    · rw [e.conjugateMap_of_notMem _ hx, e.conjugateMap_of_mem _ hy] at hxy
      exact absurd (hxy.symm ▸ e.map_target (hmaps (e.map_source hy))) hx
    · rwa [e.conjugateMap_of_notMem _ hx, e.conjugateMap_of_notMem _ hy] at hxy

omit [NormedSpace ℝ M] [FiniteDimensional ℝ M] in
theorem disjoint_chartSlide_image (e : OpenPartialHomeomorph M (ℝ × ℝ × ℝ))
    (hsub : slideSupport ⊆ e.target) (hA : modelBandA ⊆ e.target)
    (hQ : modelBandQ ⊆ e.target) :
    Disjoint (e.conjugateMap slideMap '' (e.symm '' modelBandA)) (e.symm '' modelBandQ) := by
  have hmaps := mapsTo_slideMap_of_subset hsub
  rw [Set.disjoint_left]
  rintro w ⟨u, ⟨p, hp, rfl⟩, rfl⟩ ⟨q, hq, hqe⟩
  have hps : e.symm p ∈ e.source := e.map_target (hA hp)
  have hval : e.conjugateMap slideMap (e.symm p) = e.symm (slideMap p) := by
    rw [e.conjugateMap_of_mem _ hps, e.right_inv (hA hp)]
  rw [hval] at hqe
  have h1 : slideMap p ∈ e.target := hmaps (hA hp)
  have hpq : slideMap p = q := by
    have hcong := congrArg e hqe
    rw [e.right_inv h1, e.right_inv (hQ hq)] at hcong
    exact hcong.symm
  exact Set.disjoint_left.mp disjoint_slideMap_image_modelBandA ⟨p, hp, rfl⟩ (hpq ▸ hq)

end DifferentialGeometry.Topology.PiecewiseLinear
