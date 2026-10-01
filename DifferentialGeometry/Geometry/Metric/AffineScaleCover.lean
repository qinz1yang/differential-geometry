import DifferentialGeometry.Topology.MetricSpace.CoarseScaleComparison
import DifferentialGeometry.Analysis.InnerProductSpace.AffineProjectionDistance
import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionPacking
import DifferentialGeometry.Topology.MetricSpace.VariableRadiusCover
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Set Metric

namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem neighborhood_support_packing_of_coarse_control
    (I : Set H) (hI : I.Finite) (r : H → ℝ)
    (P : Submodule ℝ H) [FiniteDimensional ℝ P] (C : ℝ) (hC : 0 ≤ C) :
    let ℓ : ℝ := 1 / (100 * (C + 1))
    let A : ℝ := 2 * (C + 1)
    let D : ℝ := 20 * A + 6
    ∀ (δ : ℝ), 0 < δ → δ ≤ ℓ / (2 * A) →
    ∀ (x₀ v : H) (r₀ : ℝ), 0 < r₀ →
    (∀ i ∈ I, 0 < r i) →
    (∀ i ∈ I, r i - r₀ ≤ C * (dist i x₀ + r₀)) →
    (∀ i ∈ I, r₀ - r i ≤ C * (dist i x₀ + r i)) →
    I.Pairwise (fun i j => Disjoint (ball i (ℓ * r i)) (ball j (ℓ * r j))) →
    (∀ i ∈ I, dist i x₀ < r₀ / δ →
      infDist i (AffineSubspace.mk' x₀ P : Set H) ≤ δ * r₀) →
    v ∈ ball x₀ (5 * ℓ * r₀) →
    let J : Set H := I ∩ {i | (closedBall i (20 * ℓ * r i) ∩ ball v (ℓ * r₀)).Nonempty}
    (J.ncard : ℝ) ≤ (1 + 2 * A * D) ^ Module.finrank ℝ P := by
  dsimp only
  let ℓ : ℝ := 1 / (100 * (C + 1))
  let A : ℝ := 2 * (C + 1)
  let D : ℝ := 20 * A + 6
  intro δ hδ hδsmall x₀ v r₀ hr₀ hr hforward hreverse hdisjoint hflat hv
  let J : Set H := I ∩ {i | (closedBall i (20 * ℓ * r i) ∩ ball v (ℓ * r₀)).Nonempty}
  change (J.ncard : ℝ) ≤ (1 + 2 * A * D) ^ Module.finrank ℝ P
  have hden : 0 < 100 * (C + 1) := by positivity
  have hℓ : 0 < ℓ := one_div_pos.mpr hden
  have hA : 0 < A := by dsimp [A]; positivity
  have hA2 : 2 ≤ A := by dsimp [A]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hbudget : C * ℓ ≤ 1 / 100 := by
    dsimp [ℓ]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hℓsmall : ℓ ≤ 1 / 100 := by
    dsimp [ℓ]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hδone : δ < 1 := by
    have hdiv : ℓ / (2 * A) ≤ ℓ := div_le_self hℓ.le (by linarith)
    have hsmall : δ ≤ ℓ / (2 * A) := hδsmall
    linarith
  have hDℓ : D * ℓ < 1 := by
    dsimp [D, A, ℓ]
    rw [← mul_div_assoc, mul_one]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hlocal (i : H) (hi : i ∈ J) :
      r₀ / A ≤ r i ∧ r i ≤ A * r₀ ∧ dist i x₀ ≤ D * ℓ * r₀ := by
    exact coarse_scale_comparison_of_support_meeting hr₀ (hr i hi.1) hC hℓ.le
      hbudget (hforward i hi.1) (hreverse i hi.1) hv hi.2
  have hJ : J.Finite := hI.subset (fun _ hi => hi.1)
  let : Fintype J := hJ.fintype
  let q : ℝ := ℓ * r₀ / A
  have hq : 0 < q := div_pos (mul_pos hℓ hr₀) hA
  have hδr : δ * r₀ ≤ q / 2 := by
    have h := mul_le_mul_of_nonneg_right hδsmall hr₀.le
    have heq : (ℓ / (2 * A)) * r₀ = q / 2 := by
      dsimp [q]
      field_simp [hA.ne']
    exact h.trans_eq heq
  have hnormal (i : J) :
      ‖((i : H) - x₀) - P.starProjection ((i : H) - x₀)‖ ≤ q / 2 := by
    rw [P.norm_sub_starProjection_eq_infDist_affine]
    apply (hflat i i.property.1 ?_).trans hδr
    have hlocation := (hlocal i i.property).2.2
    have hinside : dist (i : H) x₀ < r₀ := by
      have h := mul_lt_mul_of_pos_right hDℓ hr₀
      nlinarith
    have hlarge : r₀ < r₀ / δ := by
      apply (lt_div_iff₀ hδ).mpr
      nlinarith
    exact hinside.trans hlarge
  have hsep (i j : J) (hij : i ≠ j) : 2 * q ≤ dist (i : H) (j : H) := by
    have hne : (i : H) ≠ (j : H) := fun h => hij (Subtype.ext h)
    have hd := (disjoint_ball_ball_iff
      (mul_pos hℓ (hr i i.property.1)) (mul_pos hℓ (hr j j.property.1))).mp
        (hdisjoint i.property.1 j.property.1 hne)
    have hi := mul_le_mul_of_nonneg_left (hlocal i i.property).1 hℓ.le
    have hj := mul_le_mul_of_nonneg_left (hlocal j j.property).1 hℓ.le
    have heq : ℓ * (r₀ / A) = q := by dsimp [q]; ring
    rw [heq] at hi hj
    linarith
  have hpack := P.card_le_of_near_subspace_separated_family
    (fun i : J => (i : H)) x₀ (R := D * ℓ * r₀) (ε := 2 * q) (δ := q / 2)
    (by positivity) (by linarith)
    (fun i => by simpa only [dist_eq_norm] using (hlocal i i.property).2.2)
    hnormal hsep
  have hconstant : 1 + 2 * (D * ℓ * r₀) / (2 * q - 2 * (q / 2)) =
      1 + 2 * A * D := by
    have hgap : 2 * q - 2 * (q / 2) = q := by ring
    rw [hgap]
    dsimp [q]
    field_simp [hA.ne', hℓ.ne', hr₀.ne']
  rw [hconstant, Set.fintypeCard_eq_ncard] at hpack
  exact hpack

theorem exists_finite_disjoint_scale_cover_near_affine_subspaces
    (S : Set H) (hS : TotallyBounded S) (r : H → ℝ)
    (P : S → Submodule ℝ H) [∀ x : S, FiniteDimensional ℝ (P x)]
    {rmin R C δ : ℝ} (hrmin : 0 < rmin)
    (hlower : ∀ x ∈ S, rmin ≤ r x) (hupper : ∀ x ∈ S, r x ≤ R)
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hδsmall : δ ≤ (1 / (100 * (C + 1))) / (2 * (2 * (C + 1))))
    (hscale : ∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x))
    (hflat : ∀ x : S, ∀ y ∈ S, dist y x < r x / δ →
      Metric.infDist y (AffineSubspace.mk' (x : H) (P x) : Set H) ≤ δ * r x) :
    let ℓ : ℝ := 1 / (100 * (C + 1))
    let A : ℝ := 2 * (C + 1)
    let D : ℝ := 20 * A + 6
    ∃ I : Set H, I ⊆ S ∧ I.Finite ∧
      I.PairwiseDisjoint (fun x => ball x (ℓ * r x)) ∧
      ((⋃ x ∈ S, ball x (ℓ * r x)) ⊆ ⋃ i ∈ I, ball i (5 * ℓ * r i)) ∧
      ∀ x : S, ∀ v ∈ ball (x : H) (5 * ℓ * r x),
        ((I ∩ {i : H | (closedBall i (20 * ℓ * r i) ∩
          ball v (ℓ * r x)).Nonempty}).ncard : ℝ) ≤
            (1 + 2 * A * D) ^ Module.finrank ℝ (P x) := by
  let ℓ : ℝ := 1 / (100 * (C + 1))
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hr (x : H) (hx : x ∈ S) : 0 < r x := hrmin.trans_le (hlower x hx)
  obtain ⟨I, hIS, hIfin, hdisj, hcover⟩ := Metric.exists_finite_disjoint_ball_selection
    hS (fun x => ℓ * r x) (mul_pos hℓ hrmin)
    (fun x hx => mul_le_mul_of_nonneg_left (hlower x hx) hℓ.le)
    (fun x hx => mul_le_mul_of_nonneg_left (hupper x hx) hℓ.le)
  refine ⟨I, hIS, hIfin, hdisj, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp hz
    obtain ⟨i, hi, _, _, _, hball⟩ := hcover x hx
    exact mem_iUnion₂.mpr ⟨i, hi, by simpa only [mul_assoc] using hball hzx⟩
  · intro x v hv
    exact neighborhood_support_packing_of_coarse_control
      I hIfin r (P x) C hC δ hδ hδsmall (x : H) v (r x) (hr x x.property)
      (fun i hi => hr i (hIS hi))
      (fun i hi => by
        have h := (abs_le.mp (hscale x x.property i (hIS hi))).2
        simpa only [dist_comm (x : H) i] using h)
      (fun i hi => (abs_le.mp (hscale i (hIS hi) x x.property)).2)
      hdisj (fun i hi hdist => hflat x i (hIS hi) hdist) hv

theorem exists_finite_disjoint_scale_cover_of_hausdorffEDist_le
    (S T : Set H) (hST : S ⊆ T) (hS : TotallyBounded S) (r : H → ℝ)
    (P : S → Submodule ℝ H) [∀ x : S, FiniteDimensional ℝ (P x)]
    {rmin R C δ : ℝ} (hrmin : 0 < rmin)
    (hlower : ∀ x ∈ S, rmin ≤ r x) (hupper : ∀ x ∈ S, r x ≤ R)
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hδsmall : δ ≤ (1 / (100 * (C + 1))) / (2 * (2 * (C + 1))))
    (hscale : ∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x))
    (hcloud : ∀ x : S,
      hausdorffEDist (T ∩ ball (x : H) (r x / δ))
        ((AffineSubspace.mk' (x : H) (P x) : Set H) ∩ ball (x : H) (r x / δ)) ≤
          ENNReal.ofReal (δ * r x)) :
    let ℓ : ℝ := 1 / (100 * (C + 1))
    let A : ℝ := 2 * (C + 1)
    let D : ℝ := 20 * A + 6
    ∃ I : Set H, I ⊆ S ∧ I.Finite ∧
      I.PairwiseDisjoint (fun x => ball x (ℓ * r x)) ∧
      ((⋃ x ∈ S, ball x (ℓ * r x)) ⊆ ⋃ i ∈ I, ball i (5 * ℓ * r i)) ∧
      ∀ x : S, ∀ v ∈ ball (x : H) (5 * ℓ * r x),
        ((I ∩ {i : H | (closedBall i (20 * ℓ * r i) ∩
          ball v (ℓ * r x)).Nonempty}).ncard : ℝ) ≤
            (1 + 2 * A * D) ^ Module.finrank ℝ (P x) := by
  apply exists_finite_disjoint_scale_cover_near_affine_subspaces
    S hS r P hrmin hlower hupper hC hδ hδsmall hscale
  intro x y hy hdist
  have he : infEDist y (AffineSubspace.mk' (x : H) (P x) : Set H) ≤
      ENNReal.ofReal (δ * r x) :=
    (infEDist_anti inter_subset_left).trans
      ((infEDist_le_hausdorffEDist_of_mem
        (show y ∈ T ∩ ball (x : H) (r x / δ) from ⟨hST hy, hdist⟩)).trans (hcloud x))
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [Metric.infDist, ENNReal.toReal_ofReal
    (mul_nonneg hδ.le (hrmin.trans_le (hlower x x.property)).le)] using hreal

end GC.MetricGeometry
