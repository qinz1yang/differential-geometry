import DifferentialGeometry.Geometry.Comparison.ScaledPairedChart
import DifferentialGeometry.Geometry.Comparison.BairePairedPacket
import DifferentialGeometry.Geometry.Comparison.CommonTangentDimension

set_option autoImplicit false

open Set Metric Real
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_local_rank_dense_paired_qualities_of_intrinsic_eight_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hdim : dimH (ball p (8 * R)) ≤ n)
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω) :
    ∃ m : ℕ, m ≤ n ∧ dimH (closedBall p R) = m ∧
      (∀ V : Set X, IsOpen V → V.Nonempty → V ⊆ ball p (R / 2) → dimH V = m) ∧
      (∀ (q : X) (hq : q ∈ ball p (R / 2)),
        letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
          (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
          (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
        dimH (univ : Set (TangentCone q)) = m) ∧
      ∃ S : Set (ball p (R / 2)), IsGδ S ∧ Dense S ∧
        ∀ q ∈ S, ∀ ε : ℝ, 0 < ε →
          ∃ a b : Fin m → ball p (R / 2), PairedComparisonPacket ε {q} a b := by
  classical
  obtain ⟨m, hmn, hclosed, hopen, htangent⟩ :=
    exists_common_tangent_dimH_of_intrinsic_eight_comparison_and_dimH hcurves p hR hdim hlocal
  refine ⟨m, hmn, hclosed, hopen, htangent, ?_⟩
  rcases subsingleton_or_nontrivial X with hsub | hnontrivial
  · have hz : dimH (closedBall p R) = 0 :=
      Set.Subsingleton.dimH_zero (fun _ _ _ _ => Subsingleton.elim _ _)
    have hmzero : m = 0 := by exact_mod_cast hclosed.symm.trans hz
    subst m
    refine ⟨univ, IsGδ.univ, dense_univ, ?_⟩
    intro q _ ε _
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      ⟨fun _ _ i => Fin.elim0 i, fun _ _ i => Fin.elim0 i⟩⟩
  · let W : Set X := ball p (R / 2)
    have hW : IsOpen W := isOpen_ball
    let : BaireSpace W := hW.baireSpace
    apply exists_dense_isGδ_all_paired_qualities
    intro ε hε O hO hOne
    let O' : Set X := Subtype.val '' O
    have hO' : IsOpen O' := hW.isOpenMap_subtype_val O hO
    have hOW : O' ⊆ W := by
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    obtain ⟨x, hx⟩ := hOne
    have hx8 : x.val ∈ ball p (8 * R) := by
      change dist x.val p < 8 * R
      have hh : dist x.val p < R / 2 := x.property
      linarith
    obtain ⟨Ω₀, hΩ₀, hcomp₀, hxΩ₀⟩ :=
      (exists_local_fourPointComparison_intrinsicBall_iff hcurves p
        (by positivity : 0 < 8 * R) ⟨x.val, hx8⟩).mp (hlocal ⟨x.val, hx8⟩)
    let Ω := Ω₀ ∩ W
    have hcomp : fourPointComparison 1 Ω := hcomp₀.mono inter_subset_left
    let V := Ω ∩ O'
    have hV : IsOpen V := (hΩ₀.inter hW).inter hO'
    have hxV : x.val ∈ V := ⟨⟨hxΩ₀, x.property⟩, x, hx, rfl⟩
    have hΩ8 : Ω ⊆ ball p (8 * R) := by
      intro y hy
      change dist y p < 8 * R
      have hh : dist y p < R / 2 := hy.2
      linarith
    have hdimΩ : dimH Ω ≤ (n + 1 : ℕ) :=
      ((dimH_mono hΩ8).trans hdim).trans (by exact_mod_cast Nat.le_succ n)
    let c : ℝ := min 1 ε
    have hc : 0 < c := lt_min zero_lt_one hε
    have hc1 : c ≤ 1 := min_le_left _ _
    obtain ⟨k, hk1, hkn, q, hq, a, b, hpacket, hab, r, hr, hBr, U, hU, e, he, hlo, hhi⟩ :=
      exists_distance_chart_of_scaled_quality_in_open_set hcurves hcomp inter_subset_left hV
        ⟨x.val, hxV⟩ (fun z _ => ⟨1, zero_lt_one, isClosed_closedBall.isComplete⟩)
        (by omega : 1 ≤ n + 1) hdimΩ hc hc1
    let F : ball q r → PiLp 2 (fun _ : Fin k => ℝ) := fun z => (e z).val
    let L : ℝ := ((c * pairedChartQuality (n + 1) (k + 1)) / (100 * Real.pi)) ^ 2
    have hL : 0 < L := by
      dsimp [L]
      exact sq_pos_of_pos (div_pos (mul_pos hc (pairedChartQuality_pos _ _)) (by positivity))
    let D : ℝ≥0 := ⟨L⁻¹, (inv_pos.mpr hL).le⟩
    have hLip : LipschitzWith (NNReal.sqrt k) F := by
      simpa only [F, Function.comp_def, one_mul] using isometry_subtype_coe.lipschitzWith.comp hhi
    have hAnti : AntilipschitzWith D F := by
      apply AntilipschitzWith.of_le_mul_dist
      intro x y
      change dist x y ≤ L⁻¹ * dist (e x) (e y)
      have hh := mul_le_mul_of_nonneg_left (hlo x y) (inv_pos.mpr hL).le
      simpa only [L, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul] using hh
    have himage : F '' (univ : Set (ball q r)) = U := by
      rw [image_univ]
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact (e x).property
      · intro hz
        obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
        exact ⟨x, congrArg Subtype.val hx⟩
    have hsource : dimH (univ : Set (ball q r)) = dimH (ball q r) := by
      simpa only [image_univ, Subtype.range_coe] using
        (isometry_subtype_coe.dimH_image (univ : Set (ball q r))).symm
    have heq : dimH (ball q r) = dimH U := by
      apply le_antisymm
      · simpa only [himage, hsource] using hAnti.le_dimH_image (univ : Set (ball q r))
      · simpa only [himage, hsource] using hLip.dimH_image_le (univ : Set (ball q r))
    have hchart : dimH (ball q r) = k := by
      apply heq.trans
      have hdU := Real.dimH_of_mem_nhds (hU.mem_nhds (e ⟨q, mem_ball_self hr⟩).property)
      simpa using hdU
    have hkm : k = m := by
      exact_mod_cast hchart.symm.trans (hopen _ isOpen_ball ⟨q, mem_ball_self hr⟩ (hBr.trans (inter_subset_right.trans hOW)))
    subst k
    have hquality : pairedChartQuality (n + 1) m ≤ 1 := by
      have hh := pairedChartQuality_le (n + 1) (show m ≤ (n + 1) + 1 by omega)
      apply hh.trans
      apply (div_le_one (by positivity)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) (n + 1)]
    have hsmall : c * pairedChartQuality (n + 1) m ≤ ε :=
      (mul_le_of_le_one_right hc.le hquality).trans (min_le_right 1 ε)
    have hqW : q ∈ W := hq.1.2
    let a' : Fin m → W := fun i => ⟨a i, (hab (Or.inl ⟨i, rfl⟩)).2⟩
    let b' : Fin m → W := fun i => ⟨b i, (hab (Or.inr ⟨i, rfl⟩)).2⟩
    have hqO : (⟨q, hqW⟩ : W) ∈ O := by
      obtain ⟨z, hz, heq⟩ := hq.2
      have heq' : z = ⟨q, hqW⟩ := Subtype.ext heq
      exact heq' ▸ hz
    refine ⟨⟨q, hqW⟩, hqO, a', b', ?_⟩
    have hp := hpacket.weaken hsmall
    constructor
    · intro z hz i
      obtain rfl := mem_singleton_iff.mp hz
      exact hp.opposite q (mem_singleton q) i
    · intro z hz i j hij u hu v hv
      obtain rfl := mem_singleton_iff.mp hz
      have hu' : u.val ∈ ({a i, b i} : Set X) := by
        rcases hu with hu | hu
        · exact Or.inl (congrArg Subtype.val hu)
        · exact Or.inr (congrArg Subtype.val hu)
      have hv' : v.val ∈ ({a j, b j} : Set X) := by
        rcases hv with hv | hv
        · exact Or.inl (congrArg Subtype.val hv)
        · exact Or.inr (congrArg Subtype.val hv)
      exact hp.cross q (mem_singleton q) i j hij u.val hu' v.val hv'

end DifferentialGeometry.Geometry.Comparison.Toponogov
