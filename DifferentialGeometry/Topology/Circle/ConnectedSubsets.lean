import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.OpenPartialHomeomorph.Basic

section

noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem isPreconnected_sphere_inter_coordinate_gt {R : ℝ} (hR : 0 ≤ R) (a : ℝ) :
    IsPreconnected (sphere (0 : V) R ∩ {x | a < x 0}) := by
  let I := Icc (-R) R ∩ Ioi a
  let f : ℝ → V := fun t => !₂[t, Real.sqrt (R ^ 2 - t ^ 2)]
  let g : ℝ → V := fun t => !₂[t, -Real.sqrt (R ^ 2 - t ^ 2)]
  have hIc : IsPreconnected I := ((convex_Icc (-R) R).inter (convex_Ioi a)).isPreconnected
  have hf : Continuous f := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_id
    · exact (continuous_const.sub (continuous_id.pow 2)).sqrt
  have hg : Continuous g := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_id
    · exact (continuous_const.sub (continuous_id.pow 2)).sqrt.neg
  have hEq : sphere (0 : V) R ∩ {x | a < x 0} = f '' I ∪ g '' I := by
    ext z
    constructor
    · rintro ⟨hzR, hza⟩
      have hz : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hzR
      have hsq : z 0 ^ 2 + z 1 ^ 2 = R ^ 2 := by
        have h := EuclideanSpace.real_norm_sq_eq z
        simpa only [Fin.sum_univ_two, hz] using h.symm
      have hbound : |z 0| ≤ R := by
        have h := PiLp.norm_apply_le z 0
        simpa only [Real.norm_eq_abs, hz] using h
      have hzI : z 0 ∈ I := ⟨abs_le.mp hbound, hza⟩
      have hsqrt : Real.sqrt (R ^ 2 - z 0 ^ 2) = |z 1| := by
        rw [show R ^ 2 - z 0 ^ 2 = z 1 ^ 2 by linarith, Real.sqrt_sq_eq_abs]
      by_cases hz1 : 0 ≤ z 1
      · left
        refine ⟨z 0, hzI, ?_⟩
        ext i
        fin_cases i <;> simp [f, hsqrt, abs_of_nonneg hz1]
      · right
        refine ⟨z 0, hzI, ?_⟩
        ext i
        fin_cases i <;> simp [g, hsqrt, abs_of_neg (lt_of_not_ge hz1)]
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      all_goals
        have hnon : 0 ≤ R ^ 2 - t ^ 2 := by nlinarith [ht.1.1, ht.1.2]
        constructor
        · rw [mem_sphere_zero_iff_norm]
          apply (sq_eq_sq₀ (norm_nonneg _) hR).mp
          simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, f, g,
            Real.sq_sqrt hnon]
        · exact ht.2
  rw [hEq]
  by_cases ha : a < R
  · have hRI : R ∈ I := ⟨⟨by linarith, le_rfl⟩, ha⟩
    have heq : f R = g R := by simp [f, g]
    exact IsPreconnected.union' ⟨f R, ⟨R, hRI, rfl⟩, ⟨R, hRI, heq.symm⟩⟩
      (hIc.image f hf.continuousOn) (hIc.image g hg.continuousOn)
  · have hI : I = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact ha (ht.2.trans_le ht.1.2)
    simp only [hI, image_empty, union_empty]
    exact isPreconnected_empty


theorem isPreconnected_sphere_inter_coordinate_lt {R : ℝ} (hR : 0 ≤ R) (a : ℝ) :
    IsPreconnected (sphere (0 : V) R ∩ {x | x 0 < a}) := by
  have h := (isPreconnected_sphere_inter_coordinate_gt hR (-a)).image
    (fun x : V => -x) continuous_neg.continuousOn
  have heq : (fun x : V => -x) '' (sphere (0 : V) R ∩ {x | -a < x 0}) =
      sphere (0 : V) R ∩ {x | x 0 < a} := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyR, hya⟩, rfl⟩
      constructor
      · simpa only [mem_sphere_zero_iff_norm, norm_neg] using hyR
      · change -y 0 < a
        change -a < y 0 at hya
        linarith
    · rintro ⟨hxR, hxa⟩
      refine ⟨-x, ⟨?_, ?_⟩, neg_neg x⟩
      · simpa only [mem_sphere_zero_iff_norm, norm_neg] using hxR
      · change -a < -x 0
        exact neg_lt_neg hxa
  exact heq ▸ h

end DifferentialGeometry.Topology

end

end

section

open Set

namespace AddCircle

theorem nonempty_interior_of_isPreconnected_of_nontrivial
    {p : ℝ} [Fact (0 < p)] {S : Set (AddCircle p)}
    (hconn : IsPreconnected S) (hpair : S.Nontrivial) : (interior S).Nonempty := by
  by_cases hfull : S = univ
  · rw [hfull, interior_univ]
    exact ⟨0, mem_univ _⟩
  obtain ⟨q, hq⟩ : ∃ q : AddCircle p, q ∉ S := by
    by_contra! hall
    exact hfull (eq_univ_of_forall hall)
  obtain ⟨a, _, haq⟩ := eq_coe_Ico q
  let e := openPartialHomeomorphCoe p a
  have htarget : S ⊆ e.target := by
    intro z hz
    change z ∉ {(a : AddCircle p)}
    intro hza
    have hzq : z = q := (mem_singleton_iff.mp hza).trans haq
    exact hq (hzq ▸ hz)
  let T := e.symm '' S
  have hTconn : IsPreconnected T := hconn.image e.symm (e.continuousOn_symm.mono htarget)
  have hTpair : T.Nontrivial := hpair.image_of_injOn (e.symm.injOn.mono htarget)
  have hTsource : T ⊆ e.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_target (htarget hz)
  obtain ⟨x, hx⟩ := hTconn.convex.nontrivial_iff_nonempty_interior.mp hTpair
  have hopen : IsOpen (e '' interior T) :=
    e.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hTsource)
  have hsub : e '' interior T ⊆ S := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨z, hz, hzt⟩ := interior_subset ht
    rw [← hzt, e.right_inv (htarget hz)]
    exact hz
  refine ⟨e x, interior_mono hsub ?_⟩
  rw [hopen.interior_eq]
  exact mem_image_of_mem e hx

end AddCircle

namespace Circle

theorem nonempty_interior_of_isPreconnected_of_nontrivial
    {S : Set Circle} (hconn : IsPreconnected S) (hpair : S.Nontrivial) :
    (interior S).Nonempty := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let h := AddCircle.homeomorphCircle'
  let T := h.symm '' S
  have hTconn : IsPreconnected T := hconn.image h.symm h.symm.continuous.continuousOn
  have hTpair : T.Nontrivial := hpair.image_of_injOn h.symm.injective.injOn
  obtain ⟨x, hx⟩ := AddCircle.nonempty_interior_of_isPreconnected_of_nontrivial hTconn hTpair
  have hopen : IsOpen (h '' interior T) := h.isOpenMap _ isOpen_interior
  have hsub : h '' interior T ⊆ S := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨z, hz, hzt⟩ := interior_subset ht
    rw [← hzt, h.apply_symm_apply]
    exact hz
  refine ⟨h x, interior_mono hsub ?_⟩
  rw [hopen.interior_eq]
  exact mem_image_of_mem h hx

end Circle

namespace Complex

theorem exists_relative_ball_subset_of_isPreconnected_sphere
    {S : Set ℂ} (hS : S ⊆ Metric.sphere (0 : ℂ) 1)
    (hconn : IsPreconnected S) (hpair : S.Nontrivial) :
    ∃ p ∈ Metric.sphere (0 : ℂ) 1, ∃ ε > 0, Metric.sphere 0 1 ∩ Metric.ball p ε ⊆ S := by
  let T : Set Circle := (Subtype.val : Circle → ℂ) ⁻¹' S
  have hTimage : (Subtype.val : Circle → ℂ) '' T = S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, hS hz⟩, hz, rfl⟩
  have hTconn : IsPreconnected T := by
    have hval : Topology.IsInducing (Subtype.val : Circle → ℂ) := ⟨rfl⟩
    apply hval.isPreconnected_image.mp
    exact hTimage.symm ▸ hconn
  have hTpair : T.Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hpair
    refine ⟨⟨x, hS hx⟩, hx, ⟨y, hS hy⟩, hy, ?_⟩
    exact fun h => hxy (congrArg Subtype.val h)
  obtain ⟨p, hp⟩ := Circle.nonempty_interior_of_isPreconnected_of_nontrivial hTconn hTpair
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  refine ⟨p, p.2, ε, hε, ?_⟩
  intro z hz
  exact hball (show (⟨z, hz.1⟩ : Circle) ∈ Metric.ball p ε from hz.2)

end Complex

end
