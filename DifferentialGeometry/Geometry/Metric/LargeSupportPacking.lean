import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionPacking
import DifferentialGeometry.Analysis.InnerProductSpace.AffineProjectionDistance
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Data.Set.Card
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Set Metric
namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem large_support_packing_of_local_scale_control
    (I : Set H) (hI : I.Finite) (r : H → ℝ)
    (P : Submodule ℝ H) [FiniteDimensional ℝ P]
    (x₀ : H) (r₀ b B δ : ℝ) (hr₀ : 0 < r₀) (hb : 1 ≤ b) (hB : 1 ≤ B)
    (hr : ∀ i ∈ I, 0 < r i)
    (hdisjoint : I.PairwiseDisjoint (fun i => ball i (r i)))
    (hscale : ∀ i ∈ I, dist i x₀ ≤ 128 * b * max (r i) r₀ →
      r₀ / B ≤ r i ∧ r i ≤ B * r₀)
    (hflat : ∀ i ∈ I, dist i x₀ < r₀ / δ →
      infDist i (AffineSubspace.mk' x₀ P : Set H) ≤ δ * r₀)
    (hδ : 0 < δ) (hinterior : δ * (80 * B + 31) * b < 1) :
    let D : ℝ := 80 * B + 31
    let J : Set H := I ∩ {i | (closedBall i (80 * b * r i) ∩ ball x₀ (30 * b * r₀)).Nonempty}
    (∀ i ∈ J, r₀ / B ≤ r i ∧ r i ≤ B * r₀ ∧ dist i x₀ < D * b * r₀) ∧
      (J.ncard : ℝ) ≤ (1 + 2 * B * D * b) ^ Module.finrank ℝ P := by
  dsimp only
  let D : ℝ := 80 * B + 31
  let J : Set H := I ∩ {i | (closedBall i (80 * b * r i) ∩ ball x₀ (30 * b * r₀)).Nonempty}
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hδsmall : δ ≤ 1 / (2 * B) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * B)).mpr
    have hDb : 2 * B ≤ (80 * B + 31) * b := by
      nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 80 * B + 31)]
    have hh := mul_le_mul_of_nonneg_left hDb hδ.le
    nlinarith
  have hlocal (i : H) (hi : i ∈ J) :
      r₀ / B ≤ r i ∧ r i ≤ B * r₀ ∧ dist i x₀ < D * b * r₀ := by
    obtain ⟨z,hzi,hzx⟩ := hi.2
    have hzleft : dist i z ≤ 80 * b * r i := by
      simpa only [mem_closedBall,dist_comm z i] using hzi
    have hzright : dist z x₀ < 30 * b * r₀ := hzx
    have hraw : dist i x₀ < 80 * b * r i + 30 * b * r₀ :=
      (dist_triangle i z x₀).trans_lt (add_lt_add_of_le_of_lt hzleft hzright)
    have hmax : 0 ≤ max (r i) r₀ := hr₀.le.trans (le_max_right _ _)
    have hlocality : dist i x₀ ≤ 128 * b * max (r i) r₀ := by
      apply hraw.le.trans
      calc
        _ ≤ 80 * b * max (r i) r₀ + 30 * b * max (r i) r₀ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
            (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
        _ ≤ 128 * b * max (r i) r₀ := by nlinarith [mul_nonneg hbpos.le hmax]
    obtain ⟨hlo,hup⟩ := hscale i hi.1 hlocality
    refine ⟨hlo,hup,?_⟩
    have hh := mul_le_mul_of_nonneg_left hup (by positivity : 0 ≤ 80 * b)
    dsimp [D]
    nlinarith [mul_pos hbpos hr₀]
  refine ⟨hlocal,?_⟩
  have hJ : J.Finite := hI.subset (fun _ hi => hi.1)
  let : Fintype J := hJ.fintype
  let q : ℝ := r₀ / B
  have hq : 0 < q := div_pos hr₀ hBpos
  have hδr : δ * r₀ ≤ q / 2 := by
    have hh := mul_le_mul_of_nonneg_right hδsmall hr₀.le
    have heq : (1 / (2 * B)) * r₀ = q / 2 := by dsimp [q]; field_simp [hBpos.ne']
    exact hh.trans_eq heq
  have hinside : D * b * r₀ < r₀ / δ := by
    apply (lt_div_iff₀ hδ).mpr
    have hh := mul_lt_mul_of_pos_right hinterior hr₀
    dsimp [D]
    nlinarith
  have hnormal (i : J) :
      ‖((i : H) - x₀) - P.starProjection ((i : H) - x₀)‖ ≤ q / 2 := by
    rw [P.norm_sub_starProjection_eq_infDist_affine]
    exact (hflat i i.property.1 ((hlocal i i.property).2.2.trans hinside)).trans hδr
  have hsep (i j : J) (hij : i ≠ j) : 2 * q ≤ dist (i : H) (j : H) := by
    have hne : (i : H) ≠ (j : H) := fun h => hij (Subtype.ext h)
    have hd := (disjoint_ball_ball_iff (hr i i.property.1) (hr j j.property.1)).mp
      (hdisjoint i.property.1 j.property.1 hne)
    have hi := (hlocal i i.property).1
    have hj := (hlocal j j.property).1
    change q ≤ r i at hi
    change q ≤ r j at hj
    linarith
  have hpack := P.card_le_of_near_subspace_separated_family
    (fun i : J => (i : H)) x₀ (R := D * b * r₀) (ε := 2 * q) (δ := q / 2)
    (by positivity) (by linarith)
    (fun i => by simpa only [dist_eq_norm] using (hlocal i i.property).2.2.le)
    hnormal hsep
  have hconstant : 1 + 2 * (D * b * r₀) / (2 * q - 2 * (q / 2)) = 1 + 2 * B * D * b := by
    have hg : 2 * q - 2 * (q / 2)=q := by ring
    rw [hg]
    dsimp [q]
    field_simp [hBpos.ne',hr₀.ne']
  rw [hconstant,Set.fintypeCard_eq_ncard] at hpack
  exact hpack

end GC.MetricGeometry
