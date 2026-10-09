import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonGerm
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonFlow
import DifferentialGeometry.Topology.PlanarJordan.ParabolicLens
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The local empty-bigon push

A bigon in `ℝ × ℝ` is bounded by an arc `γ '' [t₁, t₂]` and the segment joining its ends on a
horizontal line. Its closed region `bigonRegion` is the closure of the bounded complementary
component of this Jordan curve. For a normalised bigon (corners `(∓1, 0)`, arc above the axis,
transverse crossings) and any open neighbourhood `N` of the region, there is a compactly
supported isotopy of the plane with support in `N` whose time-one map pushes the whole curve
piece `γ '' [-1 - ε, 1 + ε]` strictly below the axis.

The proof matches the model lens to the bigon by the germ of `TorusBigonGerm`, checks the
inner-side compatibility (`IsImage`) on collars that are connected because they are radial
annuli of the convex lens, extends the germ by the corner Schoenflies theorem for parabolic
lenses, and conjugates the model flow of `TorusBigonFlow`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace GC.Seifert

def bigonPlaneEquiv : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
  Complex.equivRealProdCLM.symm.trans Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv

def bigonCurveSet (γ : ℝ → ℝ × ℝ) (t₁ t₂ : ℝ) : Set (ℝ × ℝ) :=
  γ '' Icc t₁ t₂ ∪ segment ℝ (γ t₁) (γ t₂)

def bigonRegion (γ : ℝ → ℝ × ℝ) (t₁ t₂ : ℝ) : Set (ℝ × ℝ) :=
  bigonPlaneEquiv ⁻¹' closure (Schoenflies.inside (bigonPlaneEquiv '' bigonCurveSet γ t₁ t₂))

theorem segment_axis : segment ℝ ((-1 : ℝ), (0 : ℝ)) (1, 0) = Icc (-1 : ℝ) 1 ×ˢ {0} := by
  ext ⟨x, y⟩
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨s, hs, he⟩
    simp only [AffineMap.lineMap_apply_module, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul,
      Prod.mk.injEq, mul_zero, add_zero] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨⟨by nlinarith [hs.1, hs.2], by nlinarith [hs.1, hs.2]⟩, rfl⟩
  · rintro ⟨hx, hy⟩
    refine ⟨(x + 1) / 2, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
    simp only [AffineMap.lineMap_apply_module, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul,
      Prod.mk.injEq, mul_zero, add_zero]
    exact ⟨by ring, hy.symm⟩

theorem isJordanCurve_bigon {γ : ℝ → ℝ × ℝ} (hγc : ContinuousOn γ (Icc (-1) 1))
    (hγm : γ (-1) = (-1, 0)) (hγp : γ 1 = (1, 0)) (hin : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < (γ t).2)
    (hinj : InjOn γ (Icc (-1) 1)) :
    Schoenflies.IsJordanCurve (bigonPlaneEquiv '' bigonCurveSet γ (-1) 1) := by
  set L := bigonPlaneEquiv
  have hlin : (fun s : ℝ => 2 * s - 1) '' unitInterval = Icc (-1) 1 := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · intro ht
      exact ⟨(t + 1) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by ring⟩
  have hA : Schoenflies.IsArcBetween (L '' (γ '' Icc (-1) 1)) (L (-1, 0)) (L (1, 0)) := by
    refine ⟨fun s => L (γ (2 * s - 1)), ?_, ?_, ?_, ?_, ?_⟩
    · exact L.continuous.comp_continuousOn (hγc.comp (by fun_prop)
        (fun s hs => hlin ▸ mem_image_of_mem _ hs))
    · intro s hs s' hs' he
      have h1 := hinj (hlin ▸ mem_image_of_mem _ hs) (hlin ▸ mem_image_of_mem _ hs')
        (L.injective he)
      linarith
    · rw [← hlin, image_image, image_image]
    · simp only
      norm_num [hγm]
    · simp only
      norm_num [hγp]
  have hP : Schoenflies.IsArcBetween (L '' segment ℝ (γ (-1)) (γ 1)) (L (-1, 0)) (L (1, 0)) := by
    rw [hγm, hγp, segment_eq_image_lineMap]
    refine ⟨fun s => L (AffineMap.lineMap ((-1 : ℝ), (0 : ℝ)) (1, 0) s), ?_, ?_, ?_, ?_, ?_⟩
    · exact (L.continuous.comp (AffineMap.lineMap_continuous)).continuousOn
    · intro s _ s' _ he
      have := congrArg Prod.fst (L.injective he)
      simp only [AffineMap.lineMap_apply_module, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this
      linarith
    · rw [image_image]
    · simp
    · simp
  unfold bigonCurveSet
  rw [image_union]
  refine Schoenflies.isJordanCurve_union hA hP ?_
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ ⟨q, hq, hqe⟩
  rw [hγm, hγp, segment_axis] at hq
  have hq2 : (γ t).2 = 0 := by rw [← L.injective hqe]; exact hq.2
  rcases eq_or_lt_of_le ht.1 with h | h
  · left; rw [← h, hγm]
  · rcases eq_or_lt_of_le ht.2 with h' | h'
    · right; rw [h', hγp]
    · exact absurd hq2 (hin t ⟨h, h'⟩).ne'

theorem mem_outside_of_snd_neg {C : Set Schoenflies.Plane}
    (hC : ∀ p ∈ C, 0 ≤ (bigonPlaneEquiv.symm p).2) {x : ℝ × ℝ} (hx : x.2 < 0) :
    bigonPlaneEquiv x ∈ Schoenflies.outside C := by
  set L := bigonPlaneEquiv
  let H : Set Schoenflies.Plane := L '' {p | p.2 < 0}
  have hHC : H ⊆ Cᶜ := by
    rintro _ ⟨p, hp, rfl⟩ hpC
    have := hC _ hpC
    rw [L.symm_apply_apply] at this
    exact absurd hp (not_lt.mpr this)
  have hHconn : IsPreconnected H :=
    ((convex_halfSpace_lt (f := Prod.snd) (by
      exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩) 0).isPreconnected).image _
      L.continuous.continuousOn
  have hxH : L x ∈ H := mem_image_of_mem _ hx
  refine ⟨hHC hxH, fun hb => ?_⟩
  have hsub := hHconn.subset_connectedComponentIn hxH hHC
  have hHb : Bornology.IsBounded H := hb.subset hsub
  have hpre : Bornology.IsBounded {p : ℝ × ℝ | p.2 < 0} := by
    have := (ContinuousLinearMap.lipschitzWith
      (L.symm : Schoenflies.Plane →L[ℝ] ℝ × ℝ)).isBounded_image hHb
    have he : ((L.symm : Schoenflies.Plane →L[ℝ] ℝ × ℝ) : Schoenflies.Plane → ℝ × ℝ) '' H =
        {p : ℝ × ℝ | p.2 < 0} := by
      change L.symm '' H = _
      simp only [H, image_image, L.symm_apply_apply, image_id']
    rwa [he] at this
  obtain ⟨R, hR⟩ := hpre.subset_closedBall 0
  have hm := hR (show ((0 : ℝ), -(|R| + 1)) ∈ {p : ℝ × ℝ | p.2 < 0} by
    change -(|R| + 1) < 0
    have := abs_nonneg R
    linarith)
  rw [mem_closedBall, dist_zero_right, Prod.norm_def] at hm
  have h1 : ‖(-(|R| + 1))‖ ≤ R := (le_max_right _ _).trans hm
  rw [Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)] at h1
  have := le_abs_self R
  linarith

theorem bigonCurveSet_snd_nonneg {γ : ℝ → ℝ × ℝ} (hγm : γ (-1) = (-1, 0)) (hγp : γ 1 = (1, 0))
    (hin : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < (γ t).2) :
    ∀ p ∈ bigonCurveSet γ (-1) 1, 0 ≤ p.2 := by
  rintro p (⟨t, ht, rfl⟩ | hp)
  · rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hγm]
    · rcases eq_or_lt_of_le ht.2 with h' | h'
      · rw [h', hγp]
      · exact (hin t ⟨h, h'⟩).le
  · rw [hγm, hγp, segment_axis] at hp
    rw [hp.2]

theorem bigonRegion_snd_nonneg {γ : ℝ → ℝ × ℝ} (hγm : γ (-1) = (-1, 0)) (hγp : γ 1 = (1, 0))
    (hin : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < (γ t).2) :
    ∀ p ∈ bigonRegion γ (-1) 1, 0 ≤ p.2 := by
  set L := bigonPlaneEquiv
  set C := L '' bigonCurveSet γ (-1) 1
  have hC : ∀ q ∈ C, 0 ≤ (L.symm q).2 := by
    rintro _ ⟨p, hp, rfl⟩
    rw [L.symm_apply_apply]
    exact bigonCurveSet_snd_nonneg hγm hγp hin p hp
  have hcl : IsClosed (L.symm ⁻¹' {p : ℝ × ℝ | 0 ≤ p.2}) :=
    (isClosed_le continuous_const continuous_snd).preimage L.symm.continuous
  have hins : Schoenflies.inside C ⊆ L.symm ⁻¹' {p : ℝ × ℝ | 0 ≤ p.2} := by
    intro q hq
    by_contra hneg
    have hneg' : (L.symm q).2 < 0 := not_le.mp hneg
    have hout := mem_outside_of_snd_neg hC hneg'
    rw [L.apply_symm_apply] at hout
    exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hq hout
  intro p hp
  have := closure_minimal hins hcl hp
  change 0 ≤ (L.symm (L p)).2 at this
  rwa [L.symm_apply_apply] at this

theorem isConnected_annulus {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsConnected {p : ℝ × ℝ | a < ‖p‖ ∧ ‖p‖ < b} := by
  have hrank : 1 < Module.rank ℝ (ℝ × ℝ) := by
    rw [rank_prod', Module.rank_self]
    norm_num
  have hS := isConnected_sphere hrank (0 : ℝ × ℝ) zero_le_one
  have hI : IsConnected (Ioo a b) := isConnected_Ioo hab
  have himg : {p : ℝ × ℝ | a < ‖p‖ ∧ ‖p‖ < b} =
      (fun q : (ℝ × ℝ) × ℝ => q.2 • q.1) '' (sphere 0 1 ×ˢ Ioo a b) := by
    ext p
    constructor
    · rintro ⟨h1, h2⟩
      have hp : ‖p‖ ≠ 0 := by linarith
      refine ⟨(‖p‖⁻¹ • p, ‖p‖), ⟨?_, h1, h2⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp]
      · simp only
        rw [smul_smul, mul_inv_cancel₀ hp, one_smul]
    · rintro ⟨⟨u, s⟩, ⟨hu, hs⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hu
      simp only [mem_ofPred_eq, norm_smul, hu, mul_one, Real.norm_eq_abs,
        abs_of_pos (ha.trans hs.1)]
      exact hs
  rw [himg]
  exact (hS.prod hI).image _ (by fun_prop)

theorem exists_collar_of_convex {X W : Set (ℝ × ℝ)} (hc : Convex ℝ X)
    (hne : (interior X).Nonempty) (hb : Bornology.IsBounded X) (hX : IsClosed X)
    (hW : IsOpen W) (hXW : frontier X ⊆ W) :
    ∃ S : Set (ℝ × ℝ), IsOpen S ∧ frontier X ⊆ S ∧ S ⊆ W ∧
      IsPreconnected (S ∩ interior X) ∧ IsPreconnected (S \ X) := by
  obtain ⟨R, hRi, hRc, hRf⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hb
  rw [hX.closure_eq] at hRc
  have hsph : sphere (0 : ℝ × ℝ) 1 ⊆ R '' W := by
    rw [← hRf]
    exact image_mono hXW
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_sphere (0 : ℝ × ℝ) 1).exists_thickening_subset_open
    (R.isOpenMap W hW) hsph
  set r := min δ (1 / 2) with hrdef
  have hr : 0 < r := lt_min hδ (by norm_num)
  have hrδ : r ≤ δ := min_le_left _ _
  have hr1 : r ≤ 1 / 2 := min_le_right _ _
  have hmemi (x : ℝ × ℝ) : x ∈ interior X ↔ ‖R x‖ < 1 := by
    rw [← mem_ball_zero_iff, ← hRi, R.injective.mem_set_image]
  have hmemc (x : ℝ × ℝ) : x ∈ X ↔ ‖R x‖ ≤ 1 := by
    rw [← mem_closedBall_zero_iff, ← hRc, R.injective.mem_set_image]
  have hmemf (x : ℝ × ℝ) : x ∈ frontier X ↔ ‖R x‖ = 1 := by
    rw [← mem_sphere_zero_iff_norm, ← hRf, R.injective.mem_set_image]
  refine ⟨R ⁻¹' {p | 1 - r < ‖p‖ ∧ ‖p‖ < 1 + r}, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).preimage R.continuous
  · intro x hx
    have := (hmemf x).mp hx
    exact ⟨by rw [this]; linarith, by rw [this]; linarith⟩
  · intro x ⟨h1, h2⟩
    have hp : ‖R x‖ ≠ 0 := by linarith
    have hmem : R x ∈ thickening δ (sphere (0 : ℝ × ℝ) 1) := by
      rw [mem_thickening_iff]
      refine ⟨‖R x‖⁻¹ • R x, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp]
      · rw [dist_eq_norm]
        have : R x - ‖R x‖⁻¹ • R x = (1 - ‖R x‖⁻¹) • R x := by
          rw [sub_smul, one_smul]
        rw [this, norm_smul, Real.norm_eq_abs]
        have he : |1 - ‖R x‖⁻¹| * ‖R x‖ = |‖R x‖ - 1| := by
          rw [← abs_of_pos (show 0 < ‖R x‖ by linarith), ← abs_mul, abs_of_pos
            (show 0 < ‖R x‖ by linarith), sub_mul, one_mul, inv_mul_cancel₀ hp]
        rw [he, abs_lt]
        constructor <;> linarith
    obtain ⟨y, hy, hyx⟩ := hthick hmem
    rw [← R.injective hyx]
    exact hy
  · have heq : R ⁻¹' {p | 1 - r < ‖p‖ ∧ ‖p‖ < 1 + r} ∩ interior X =
        R ⁻¹' {p | 1 - r < ‖p‖ ∧ ‖p‖ < 1} := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, hmemi]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, by linarith⟩, h3⟩
    rw [heq, ← R.image_symm]
    exact ((isConnected_annulus (by linarith) (by linarith)).image _
      R.symm.continuous.continuousOn).isPreconnected
  · have heq : R ⁻¹' {p | 1 - r < ‖p‖ ∧ ‖p‖ < 1 + r} \ X =
        R ⁻¹' {p | 1 < ‖p‖ ∧ ‖p‖ < 1 + r} := by
      ext x
      simp only [Set.mem_sdiff, mem_preimage, mem_ofPred_eq]
      rw [hmemc, not_le]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨by linarith, h3⟩, h1⟩
    rw [heq, ← R.image_symm]
    exact ((isConnected_annulus one_pos (by linarith)).image _
      R.symm.continuous.continuousOn).isPreconnected

theorem mem_closure_inside_iff_of_collar {X S : Set (ℝ × ℝ)} {C : Set Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C) {f : ℝ × ℝ → Schoenflies.Plane}
    (hfS : InjOn f S) (hfopen : IsOpen (f '' S)) (hfc : ContinuousOn f S) (hX : IsClosed X)
    (hfr : frontier X ⊆ S) (himg : f '' frontier X = C)
    (hin : IsPreconnected (S ∩ interior X)) (hout : IsPreconnected (S \ X))
    {x₀ : ℝ × ℝ} (hx₀ : x₀ ∈ S \ X) (hfx₀ : f x₀ ∈ Schoenflies.outside C) :
    ∀ x ∈ S, f x ∈ closure (Schoenflies.inside C) ↔ x ∈ X := by
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hfrX : frontier X ⊆ X := hX.frontier_subset
  have hnotC : ∀ x ∈ S, x ∉ frontier X → f x ∉ C := by
    intro x hx hxf hxC
    rw [← himg] at hxC
    obtain ⟨y, hy, hyx⟩ := hxC
    exact hxf (hfS (hfr hy) hx hyx ▸ hy)
  have hWout : f '' (S \ X) ⊆ Schoenflies.outside C := by
    have hsub : f '' (S \ X) ⊆ Cᶜ := by
      rintro _ ⟨x, hx, rfl⟩
      exact hnotC x hx.1 (fun h => hx.2 (hfrX h))
    have hpc : IsPreconnected (f '' (S \ X)) := hout.image f (hfc.mono sdiff_subset)
    have hcomp := hpc.subset_connectedComponentIn (mem_image_of_mem f hx₀) hsub
    exact hcomp.trans (Schoenflies.connectedComponentIn_subset_outside hfx₀)
  have hCne : C.Nonempty := by
    obtain ⟨g, _, hg⟩ := hC
    rw [← hg]
    exact ⟨g 0, mem_image_of_mem g unitInterval.zero_mem⟩
  obtain ⟨p, hp⟩ := hCne
  have hpcl : p ∈ closure (Schoenflies.inside C) := by
    have := hsep.frontier_inside
    rw [← this] at hp
    exact frontier_subset_closure hp
  have hpS : p ∈ f '' S := by
    rw [← himg] at hp
    exact image_mono hfr hp
  obtain ⟨y, hyS, hyi⟩ := mem_closure_iff_nhds.mp hpcl _ (hfopen.mem_nhds hpS)
  obtain ⟨x₁, hx₁S, rfl⟩ := hyS
  have hx₁i : x₁ ∈ interior X := by
    by_contra hni
    by_cases hx₁X : x₁ ∈ X
    · have hfr₁ : x₁ ∈ frontier X := ⟨subset_closure hx₁X, hni⟩
      exact hyi.1 (himg ▸ mem_image_of_mem f hfr₁)
    · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hyi
        (hWout (mem_image_of_mem f ⟨hx₁S, hx₁X⟩))
  have hWin : f '' (S ∩ interior X) ⊆ Schoenflies.inside C := by
    have hsub : f '' (S ∩ interior X) ⊆ Cᶜ := by
      rintro _ ⟨x, hx, rfl⟩
      exact hnotC x hx.1 (fun h => (Set.disjoint_left.mp disjoint_interior_frontier hx.2) h)
    have hpc : IsPreconnected (f '' (S ∩ interior X)) := hin.image f (hfc.mono inter_subset_left)
    have hcomp := hpc.subset_connectedComponentIn (mem_image_of_mem f ⟨hx₁S, hx₁i⟩) hsub
    exact hcomp.trans (Schoenflies.connectedComponentIn_subset_inside hyi)
  intro x hx
  constructor
  · intro hcl
    by_contra hxX
    have ho := hWout (mem_image_of_mem f ⟨hx, hxX⟩)
    have hdisj : Disjoint (Schoenflies.outside C) (closure (Schoenflies.inside C)) :=
      (Schoenflies.disjoint_inside_outside.symm).closure_right (Schoenflies.isOpen_outside
        hsep.isClosed)
    exact Set.disjoint_left.mp hdisj ho hcl
  · intro hxX
    by_cases hxi : x ∈ interior X
    · exact subset_closure (hWin (mem_image_of_mem f ⟨hx, hxi⟩))
    · have hxf : x ∈ frontier X := ⟨subset_closure hxX, hxi⟩
      have hfC : f x ∈ C := himg ▸ mem_image_of_mem f hxf
      rw [← hsep.frontier_inside] at hfC
      exact frontier_subset_closure hfC

def lensSet : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ z.1 ≤ 1 - 1 * z.2 ^ 2}

theorem lensSet_eq : lensSet = {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 ≤ 1 - z.2 ^ 2} := by
  ext z
  simp [lensSet]

theorem frontier_lensSet :
    frontier lensSet = lensCurve '' Icc (-1) 1 ∪ {0} ×ˢ Icc (-1) 1 := by
  have h := DifferentialGeometry.Topology.PlanarJordan.frontier_parabolic_lens
    (a := 0) (A := 1) (B := 1) one_pos one_pos
  have hr : Real.sqrt ((1 - 0) / 1) = 1 := by norm_num
  rw [hr] at h
  unfold lensSet
  rw [h]
  congr 2
  funext u
  simp [lensCurve]

theorem isClosed_lensSet : IsClosed lensSet :=
  (isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_fst (continuous_const.sub (continuous_const.mul
      (continuous_snd.pow 2))))

theorem convex_lensSet : Convex ℝ lensSet := by
  intro x hx y hy s t hs ht hst
  change 0 ≤ s * x.1 + t * y.1 ∧ s * x.1 + t * y.1 ≤ 1 - 1 * (s * x.2 + t * y.2) ^ 2
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have hsq : (s * x.2 + t * y.2) ^ 2 ≤ s * x.2 ^ 2 + t * y.2 ^ 2 := by
    have hv : s * x.2 ^ 2 + t * y.2 ^ 2 - (s * x.2 + t * y.2) ^ 2 = s * t * (x.2 - y.2) ^ 2 := by
      have : t = 1 - s := by linarith
      subst this
      ring
    nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x.2 - y.2))]
  constructor
  · positivity
  · have : t = 1 - s := by linarith
    subst this
    nlinarith [mul_nonneg hs (sub_nonneg.mpr hx1), mul_nonneg ht (sub_nonneg.mpr hy1)]

theorem isBounded_lensSet : Bornology.IsBounded lensSet := by
  refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := 1)).subset ?_
  rintro z ⟨h0, h1⟩
  rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_le, abs_le]
  refine ⟨⟨by linarith, by nlinarith [sq_nonneg z.2]⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg z.2]

theorem interior_lensSet_nonempty : (interior lensSet).Nonempty := by
  refine ⟨(1 / 2, 0), ?_⟩
  unfold lensSet
  rw [DifferentialGeometry.Topology.PlanarJordan.interior_parabolic_lens one_pos one_pos]
  constructor <;> norm_num

theorem lensCurve_mem_frontier {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) :
    lensCurve τ ∈ frontier lensSet := by
  rw [frontier_lensSet]
  exact Or.inl (mem_image_of_mem _ hτ)

theorem axis_mem_frontier {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) :
    ((0 : ℝ), v) ∈ frontier lensSet := by
  rw [frontier_lensSet]
  exact Or.inr ⟨rfl, hv⟩

theorem frontier_lensSet_subset_lensCore {ε : ℝ} (hε : 0 ≤ ε) :
    frontier lensSet ⊆ lensCore ε := by
  rw [frontier_lensSet]
  have hI : Icc (-1 : ℝ) 1 ⊆ Icc (-1 - ε) (1 + ε) := Icc_subset_Icc (by linarith) (by linarith)
  exact union_subset_union (image_mono hI) (prod_mono le_rfl hI) |>.trans
    (by rw [lensCore, union_comm])

theorem exists_bigon_push_normal {γ : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ) {ε : ℝ} (hε : 0 < ε)
    (hγm : γ (-1) = (-1, 0)) (hγp : γ 1 = (1, 0))
    (hout : ∀ t ∈ Icc (-1 - ε) (1 + ε), t < -1 ∨ 1 < t → (γ t).2 < 0)
    (hin : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < (γ t).2)
    (htm : 0 < (deriv γ (-1)).2) (htp : (deriv γ 1).2 < 0)
    (himm : ∀ t ∈ Icc (-1 - ε) (1 + ε), deriv γ t ≠ 0)
    (hinj : InjOn γ (Icc (-1 - ε) (1 + ε)))
    {N : Set (ℝ × ℝ)} (hN : IsOpen N) (hDN : bigonRegion γ (-1) 1 ⊆ N) :
    ∃ H : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => H q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (H q.1).symm q.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞ ∧
      (∃ K : Set (ℝ × ℝ), IsCompact K ∧ K ⊆ N ∧ ∀ s z, z ∉ K → H s z = z) ∧
      ∀ t ∈ Icc (-1 - ε) (1 + ε), (H 1 (γ t)).2 < 0 := by
  set L := bigonPlaneEquiv
  set C := L '' bigonCurveSet γ (-1) 1
  have hI1 : Icc (-1 : ℝ) 1 ⊆ Icc (-1 - ε) (1 + ε) := Icc_subset_Icc (by linarith) (by linarith)
  obtain ⟨c₀, U, hU, hKU, hinjU, hlocU, hax, hcurve, hswap⟩ :=
    exists_bigon_germ hγ hγm hγp hout hin htm htp himm hinj
  have hc₀cont : ContinuousOn c₀ U := fun x hx =>
    (hlocU x hx).contMDiffAt.continuousAt.continuousWithinAt
  have hfrU : frontier lensSet ⊆ U := (frontier_lensSet_subset_lensCore hε.le).trans hKU
  have hc₀fr : c₀ '' frontier lensSet = bigonCurveSet γ (-1) 1 := by
    rw [frontier_lensSet, image_union, bigonCurveSet, hγm, hγp, segment_axis, image_image]
    congr 1
    · exact image_congr fun τ _ => hcurve τ
    · ext ⟨x, y⟩
      constructor
      · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, he⟩
        have hu' : u = 0 := hu
        subst hu'
        rw [hax] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨hv, rfl⟩
      · rintro ⟨hx, hy⟩
        have hy' : y = 0 := hy
        subst hy'
        exact ⟨(0, x), ⟨rfl, hx⟩, hax x⟩
  have hCsnd : ∀ q ∈ C, 0 ≤ (L.symm q).2 := by
    rintro _ ⟨p, hp, rfl⟩
    rw [L.symm_apply_apply]
    exact bigonCurveSet_snd_nonneg hγm hγp hin p hp
  have hJ : Schoenflies.IsJordanCurve C :=
    isJordanCurve_bigon hγ.continuous.continuousOn hγm hγp hin (hinj.mono hI1)
  set Ωl : Set (ℝ × ℝ) := {p | p.2 ≠ 0 ∨ |p.1| < 1 + ε}
  have hΩl : IsOpen Ωl := (isOpen_ne_fun continuous_snd continuous_const).union
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const)
  set W₀ := U ∩ c₀ ⁻¹' Ωl
  have hW₀ : IsOpen W₀ := hc₀cont.isOpen_inter_preimage hU hΩl
  have hfrW₀ : frontier lensSet ⊆ W₀ := by
    intro x hx
    refine ⟨hfrU hx, ?_⟩
    have hc : c₀ x ∈ bigonCurveSet γ (-1) 1 := hc₀fr ▸ mem_image_of_mem c₀ hx
    change (c₀ x).2 ≠ 0 ∨ |(c₀ x).1| < 1 + ε
    by_cases h0 : (c₀ x).2 = 0
    · right
      rcases hc with ⟨t, ht, he⟩ | hc
      · rcases eq_or_lt_of_le ht.1 with h | h
        · rw [← he, ← h, hγm]; norm_num; linarith
        · rcases eq_or_lt_of_le ht.2 with h' | h'
          · rw [← he, h', hγp]; norm_num; linarith
          · exact absurd (he ▸ h0) (hin t ⟨h, h'⟩).ne'
      · rw [hγm, hγp, segment_axis] at hc
        rw [abs_lt]
        constructor <;> linarith [hc.1.1, hc.1.2]
    · exact Or.inl h0
  have hP2 : ∀ z ∈ W₀, (c₀ z).2 = 0 → z.1 = 0 := by
    intro z hz h0
    have hl : |(c₀ z).1| < 1 + ε := (hz.2 : (c₀ z).2 ≠ 0 ∨ _).resolve_left (not_not.mpr h0)
    set v := (c₀ z).1
    have hvK : ((0 : ℝ), v) ∈ lensCore ε := by
      left
      rw [abs_lt] at hl
      exact ⟨rfl, by linarith, by linarith⟩
    have he : c₀ (0, v) = c₀ z := by rw [hax]; exact Prod.ext rfl h0.symm
    rw [← hinjU (hKU hvK) hz.1 he]
  obtain ⟨S, hSo, hfrS, hSW, hSin, hSout⟩ := exists_collar_of_convex convex_lensSet
    interior_lensSet_nonempty isBounded_lensSet isClosed_lensSet hW₀ hfrW₀
  have hSU : S ⊆ U := fun x hx => (hSW hx).1
  set f : ℝ × ℝ → Schoenflies.Plane := fun x => L (c₀ x) with hfdef
  have hfloc : IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ f S := by
    intro x
    exact (hlocU x (hSU x.2)).comp (P := Schoenflies.Plane) (K := 𝓘(ℝ, Schoenflies.Plane))
      (L.toDiffeomorph.isLocalDiffeomorph (c₀ x))
  have hfinj : InjOn f S := fun x hx y hy he => hinjU (hSU hx) (hSU hy) (L.injective he)
  obtain ⟨c, hcs, hct, hcf⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn hSo hfloc hfinj
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ S := hfrS (axis_mem_frontier ⟨by norm_num, by norm_num⟩)
  obtain ⟨η₀, hη₀, hballS⟩ := Metric.isOpen_iff.mp hSo _ h00
  set η := min (η₀ / 2) (1 / 64) with hηdef
  have hη : 0 < η := lt_min (half_pos hη₀) (by norm_num)
  have hηle : η ≤ 1 / 64 := min_le_right _ _
  have hx₀ : ((-η, 0) : ℝ × ℝ) ∈ S \ lensSet := by
    refine ⟨hballS ?_, fun h => ?_⟩
    · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [abs_neg, sub_zero, abs_zero]
      rw [abs_of_pos hη, max_lt_iff]
      exact ⟨by linarith [min_le_left (η₀ / 2) (1 / 64)], hη₀⟩
    · have := h.1
      simp only at this
      linarith
  have hfx₀ : f (-η, 0) ∈ Schoenflies.outside C := by
    have hc : c₀ (-η, 0) = (0, -η) := by
      rw [hswap _ (by simp) (by rw [abs_neg, abs_of_pos hη]; linarith)]
      rfl
    change L (c₀ (-η, 0)) ∈ _
    rw [hc]
    exact mem_outside_of_snd_neg hCsnd (by simp only; linarith)
  have himgC : f '' frontier lensSet = C := by
    rw [show f = L ∘ c₀ from rfl, image_comp, hc₀fr]
  have hiff := mem_closure_inside_iff_of_collar hJ hfinj (by rw [← hct]; exact c.open_target)
    (fun x hx => (hfloc ⟨x, hx⟩).contMDiffAt.continuousAt.continuousWithinAt)
    isClosed_lensSet hfrS himgC hSin hSout hx₀ hfx₀
  have hcIm : c.toOpenPartialHomeomorph.IsImage lensSet (closure (Schoenflies.inside C)) := by
    intro x hx
    rw [show c.toOpenPartialHomeomorph x = f x from congrFun hcf x]
    exact hiff x (hcs ▸ hx)
  obtain ⟨F, hFfr, hFX, V, hV, hfrV, hVc, hFc⟩ := by
    open DifferentialGeometry.Topology.PlanarJordan in
    exact exists_diffeomorph_eqOn_neighborhood_of_parabolic_lens
      (a := 0) (A := 1) (B := 1) one_pos one_pos c hJ (hcs ▸ hfrS) hcIm
  have hFX' : F '' lensSet = closure (Schoenflies.inside C) := hFX
  have hfrV' : frontier lensSet ⊆ V := hfrV
  set G : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) := F.trans L.symm.toDiffeomorph with hGdef
  have hGapp (z : ℝ × ℝ) : G z = L.symm (F z) := rfl
  have hVS : V ⊆ S := hcs ▸ hVc
  have hGV : ∀ z ∈ V, G z = c₀ z := by
    intro z hz
    rw [hGapp, hFc hz, show c z = f z from congrFun hcf z]
    exact L.symm_apply_apply _
  have hGX : G '' lensSet = bigonRegion γ (-1) 1 := by
    rw [show (G : ℝ × ℝ → ℝ × ℝ) = L.symm ∘ F from rfl, image_comp, hFX']
    unfold bigonRegion
    exact L.toEquiv.symm.image_eq_preimage_symm _ |>.trans rfl
  have hGint : G '' interior lensSet = L.symm '' interior (closure (Schoenflies.inside C)) := by
    rw [show (G : ℝ × ℝ → ℝ × ℝ) = L.symm ∘ F from rfl, image_comp, ← hFX']
    congr 1
    exact F.toHomeomorph.image_interior lensSet
  have hγint : ∀ t ∈ Icc (-1 - ε) (1 + ε), γ t ∉ G '' interior lensSet := by
    intro t ht hmem
    rw [hGint] at hmem
    obtain ⟨q, hq, hqe⟩ := hmem
    have hLq : q = L (γ t) := by rw [← hqe, L.apply_symm_apply]
    by_cases ht1 : t ∈ Icc (-1 : ℝ) 1
    · have hqC : q ∈ C := hLq ▸ mem_image_of_mem L (Or.inl (mem_image_of_mem γ ht1))
      rw [← DifferentialGeometry.Topology.PlanarJordan.frontier_closure_inside hJ] at hqC
      exact (Set.disjoint_left.mp disjoint_interior_frontier hq) hqC
    · have hlt : t < -1 ∨ 1 < t := by
        by_contra hcon
        push Not at hcon
        exact ht1 ⟨hcon.1, hcon.2⟩
      have h1 := hout t ht hlt
      have h2 := bigonRegion_snd_nonneg hγm hγp hin (γ t) (by
        change L (γ t) ∈ closure _
        rw [← hLq]
        exact interior_subset hq)
      linarith
  have hfrc : IsCompact (frontier lensSet) := Metric.isCompact_of_isClosed_isBounded
    isClosed_frontier (isBounded_lensSet.subset isClosed_lensSet.frontier_subset)
  obtain ⟨δ, hδ, hthick⟩ := hfrc.exists_thickening_subset_open hV hfrV'
  set r := min (δ / 2) (1 / 32) with hrdef
  have hr : 0 < r := lt_min (half_pos hδ) (by norm_num)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hr32 : r ≤ 1 / 32 := min_le_right _ _
  set B : Set (ℝ × ℝ) := Ioo (-r) 0 ×ˢ Ioo (-1 - r) (1 + r)
  have hBV : B ⊆ V := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    apply hthick
    rw [mem_thickening_iff]
    refine ⟨(0, max (-1) (min 1 v)), axis_mem_frontier ⟨le_max_left _ _,
      max_le (by norm_num) (min_le_left _ _)⟩, ?_⟩
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    constructor
    · rw [sub_zero, abs_lt]
      constructor <;> linarith [hu.1, hu.2]
    · rw [abs_lt]
      constructor
      · have := min_le_right 1 v
        have := le_max_right (-1) (min 1 v)
        rcases le_total v 1 with h | h
        · rw [min_eq_right h] at *
          rcases le_total (-1) v with h' | h'
          · rw [max_eq_right h']; linarith
          · rw [max_eq_left h']; linarith [hv.1]
        · rw [min_eq_left h, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]; linarith
      · rcases le_total v 1 with h | h
        · rw [min_eq_right h]
          rcases le_total (-1) v with h' | h'
          · rw [max_eq_right h']; linarith
          · rw [max_eq_left h']; linarith
        · rw [min_eq_left h, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]; linarith [hv.2]
  have hBsign : ∀ z ∈ B, (c₀ z).2 < 0 := by
    have hBpc : IsPreconnected B := ((convex_Ioo _ _).prod (convex_Ioo _ _)).isPreconnected
    have hcont : ContinuousOn (fun z => (c₀ z).2) B :=
      continuous_snd.comp_continuousOn (hc₀cont.mono (hBV.trans (hVS.trans hSU)))
    have hne : ∀ z ∈ B, (c₀ z).2 ≠ 0 := by
      intro z hz h0
      have := hP2 z (hSW (hVS (hBV hz))) h0
      linarith [hz.1.2]
    have href : ((-(r / 2), 0) : ℝ × ℝ) ∈ B :=
      ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    have hrefv : (c₀ (-(r / 2), 0)).2 = -(r / 2) := by
      rw [hswap _ (by simp) (by rw [abs_neg, abs_of_pos (half_pos hr)]; linarith)]
      rfl
    intro z hz
    by_contra hge
    have hpos : 0 < (c₀ z).2 := lt_of_le_of_ne (not_lt.mp hge) (hne z hz).symm
    have hIcc := (hBpc.image _ hcont).Icc_subset (mem_image_of_mem _ href) (mem_image_of_mem _ hz)
    obtain ⟨w, hw, hw0⟩ := hIcc ⟨by rw [hrefv]; linarith, hpos.le⟩
    exact hne w hw hw0
  set Wf : Set (ℝ × ℝ) := (interior lensSet ∪ V) ∩ G ⁻¹' N
  have hWf : IsOpen Wf := (isOpen_interior.union hV).inter (hN.preimage G.continuous)
  have hXWf : {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 ≤ 1 - z.2 ^ 2} ⊆ Wf := by
    rw [← lensSet_eq]
    intro z hz
    refine ⟨?_, hDN (hGX ▸ mem_image_of_mem G hz)⟩
    by_cases hzi : z ∈ interior lensSet
    · exact Or.inl hzi
    · exact Or.inr (hfrV' ⟨subset_closure hz, hzi⟩)
  obtain ⟨Hm, hHm, hHm', hHm0, Sm, hSmc, hSmW, hSmbox, hSmfix, -, hpush⟩ :=
    exists_lens_push hWf hXWf hr
  have hGs : ContDiff ℝ ∞ (G : ℝ × ℝ → ℝ × ℝ) := contMDiff_iff_contDiff.mp G.contMDiff
  have hGs' : ContDiff ℝ ∞ (G.symm : ℝ × ℝ → ℝ × ℝ) := contMDiff_iff_contDiff.mp G.symm.contMDiff
  refine ⟨fun s => G.symm.trans ((Hm s).trans G), ?_, ?_, ?_, ⟨G '' Sm, hSmc.image G.continuous,
    ?_, ?_⟩, ?_⟩
  · exact hGs.comp (hHm.comp (contDiff_fst.prodMk (hGs'.comp contDiff_snd)))
  · exact hGs.comp (hHm'.comp (contDiff_fst.prodMk (hGs'.comp contDiff_snd)))
  · refine Diffeomorph.ext fun z => ?_
    change G (Hm 0 (G.symm z)) = z
    rw [hHm0]
    simp
  · rintro _ ⟨z, hz, rfl⟩
    exact (hSmW hz).2
  · intro s z hz
    have hz' : G.symm z ∉ Sm := fun h => hz ⟨G.symm z, h, G.apply_symm_apply z⟩
    change G (Hm s (G.symm z)) = z
    rw [hSmfix s _ hz', G.apply_symm_apply]
  · intro t ht
    change (G (Hm 1 (G.symm (γ t)))).2 < 0
    set w := G.symm (γ t) with hwdef
    have hGw : G w = γ t := G.apply_symm_apply _
    have hcurveV : ∀ τ ∈ Icc (-1 : ℝ) 1, lensCurve τ ∈ Sm := by
      intro τ hτ
      by_contra hn
      have h1 := hpush τ
      rw [show ((1 - τ ^ 2, τ) : ℝ × ℝ) = lensCurve τ from rfl, hSmfix 1 _ hn] at h1
      have : 0 ≤ (lensCurve τ).1 := by
        change 0 ≤ 1 - τ ^ 2
        nlinarith [hτ.1, hτ.2]
      linarith
    by_cases hwS : w ∈ Sm
    · have hwV : w ∈ V := by
        rcases (hSmW hwS).1 with hi | hv
        · exact absurd (hGw ▸ mem_image_of_mem G hi) (hγint t ht)
        · exact hv
      have hwc : c₀ w = γ t := (hGV w hwV).symm.trans hGw
      have hwl : w = lensCurve t := hinjU (hSU (hVS hwV)) (hKU (Or.inr (mem_image_of_mem _ ht)))
        (hwc.trans (hcurve t).symm)
      set z' := Hm 1 w
      have hz'S : z' ∈ Sm := by
        by_contra hn
        have := hSmfix 1 z' hn
        exact hn ((Hm 1).injective this ▸ hwS)
      have hz'1 : z'.1 < 0 := by
        have := hpush t
        rw [show ((1 - t ^ 2, t) : ℝ × ℝ) = lensCurve t from rfl, ← hwl] at this
        exact this
      have hz'B : z' ∈ B := hSmbox ⟨hz'S, hz'1⟩
      rw [hGV z' (hBV hz'B)]
      exact hBsign z' hz'B
    · rw [hSmfix 1 w hwS, hGw]
      have hnot : t ∉ Icc (-1 : ℝ) 1 := by
        intro ht1
        have hw' : w = lensCurve t := by
          rw [hwdef, ← hcurve t, ← hGV _ (hfrV' (lensCurve_mem_frontier ht1)),
            G.symm_apply_apply]
        exact hwS (hw' ▸ hcurveV t ht1)
      have hlt : t < -1 ∨ 1 < t := by
        by_contra hcon
        push Not at hcon
        exact hnot ⟨hcon.1, hcon.2⟩
      exact hout t ht hlt

theorem deriv_pos_of_zero_of_pos_right {f : ℝ → ℝ} {a b d : ℝ} (hab : a < b)
    (hf : HasDerivAt f d a) (h0 : f a = 0) (hpos : ∀ t ∈ Ioo a b, 0 < f t) (hd : d ≠ 0) :
    0 < d := by
  by_contra hneg
  have hlt : d < 0 := lt_of_le_of_ne (not_lt.mp hneg) hd
  have hsl : Tendsto (slope f a) (𝓝[>] a) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.mp hf).mono_left (nhdsWithin_mono _ (fun t ht => ne_of_gt ht))
  have h1 : ∀ᶠ t in 𝓝[>] a, slope f a t < 0 := hsl (Iio_mem_nhds hlt)
  have h2 : ∀ᶠ t in 𝓝[>] a, t ∈ Ioo a b := Ioo_mem_nhdsGT hab
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  rw [slope_def_field, h0, sub_zero] at ht1
  have := div_pos (hpos t ht2) (sub_pos.mpr ht2.1)
  linarith

theorem deriv_neg_of_zero_of_pos_left {f : ℝ → ℝ} {a b d : ℝ} (hab : a < b)
    (hf : HasDerivAt f d b) (h0 : f b = 0) (hpos : ∀ t ∈ Ioo a b, 0 < f t) (hd : d ≠ 0) :
    d < 0 := by
  by_contra hneg
  have hlt : 0 < d := lt_of_le_of_ne (not_lt.mp hneg) hd.symm
  have hsl : Tendsto (slope f b) (𝓝[<] b) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.mp hf).mono_left (nhdsWithin_mono _ (fun t ht => ne_of_lt ht))
  have h1 : ∀ᶠ t in 𝓝[<] b, 0 < slope f b t := hsl (Ioi_mem_nhds hlt)
  have h2 : ∀ᶠ t in 𝓝[<] b, t ∈ Ioo a b := Ioo_mem_nhdsLT hab
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  rw [slope_def_field, h0, sub_zero] at ht1
  have := div_neg_of_pos_of_neg (hpos t ht2) (sub_neg.mpr ht2.2)
  linarith

def bigonAffine (μ m σ c : ℝ) (hm : m ≠ 0) (hσ : σ ≠ 0) : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) where
  toFun p := ((p.1 - μ) / m, σ * (p.2 - c))
  invFun q := (m * q.1 + μ, q.2 / σ + c)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · change m * ((p.1 - μ) / m) + μ = p.1
      field_simp
      ring
    · change σ * (p.2 - c) / σ + c = p.2
      field_simp
      ring
  right_inv q := by
    refine Prod.ext ?_ ?_
    · change (m * q.1 + μ - μ) / m = q.1
      field_simp
      ring
    · change σ * (q.2 / σ + c - c) = q.2
      field_simp
      ring
  contMDiff_toFun := by
    refine ContDiff.contMDiff ?_
    exact ((contDiff_fst.sub contDiff_const).div_const m).prodMk
      (contDiff_const.mul (contDiff_snd.sub contDiff_const))
  contMDiff_invFun := by
    refine ContDiff.contMDiff ?_
    exact ((contDiff_const.mul contDiff_fst).add contDiff_const).prodMk
      ((contDiff_snd.div_const σ).add contDiff_const)

theorem bigonAffine_apply {μ m σ c : ℝ} (hm : m ≠ 0) (hσ : σ ≠ 0) (p : ℝ × ℝ) :
    bigonAffine μ m σ c hm hσ p = ((p.1 - μ) / m, σ * (p.2 - c)) := rfl

theorem bigonAffine_symm_apply {μ m σ c : ℝ} (hm : m ≠ 0) (hσ : σ ≠ 0) (q : ℝ × ℝ) :
    (bigonAffine μ m σ c hm hσ).symm q = (m * q.1 + μ, q.2 / σ + c) := rfl

theorem bigonAffine_image_segment {μ m σ c : ℝ} (hm : m ≠ 0) (hσ : σ ≠ 0) (a b : ℝ × ℝ) :
    bigonAffine μ m σ c hm hσ '' segment ℝ a b =
      segment ℝ (bigonAffine μ m σ c hm hσ a) (bigonAffine μ m σ c hm hσ b) := by
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap, image_image]
  refine image_congr fun s _ => ?_
  simp only [bigonAffine_apply, AffineMap.lineMap_apply_module, Prod.smul_mk, Prod.mk_add_mk,
    smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  refine Prod.ext ?_ ?_
  · simp only
    field_simp
    ring
  · simp only
    ring

theorem bigonRegion_image (A : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) {γ γ' : ℝ → ℝ × ℝ} {t₁ t₂ t₁' t₂' : ℝ}
    (h : A '' bigonCurveSet γ t₁ t₂ = bigonCurveSet γ' t₁' t₂') :
    A '' bigonRegion γ t₁ t₂ = bigonRegion γ' t₁' t₂' := by
  set L := bigonPlaneEquiv
  let Φ : Schoenflies.Plane ≃ₜ Schoenflies.Plane :=
    L.symm.toHomeomorph.trans (A.trans L.toHomeomorph)
  have hΦ : ∀ Z : Set (ℝ × ℝ), Φ '' (L '' Z) = L '' (A '' Z) := by
    intro Z
    simp only [Φ, image_image]
    refine image_congr fun z _ => ?_
    simp
  have key := Schoenflies.image_closure_inside_homeomorph Φ (L '' bigonCurveSet γ t₁ t₂)
  rw [hΦ, h] at key
  unfold bigonRegion
  rw [← key]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨L y, hy, ?_⟩
    simp only [Φ, Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph,
      ContinuousLinearEquiv.symm_apply_apply]
    rfl
  · rintro ⟨q, hq, hqz⟩
    refine ⟨A.symm z, ?_, A.apply_symm_apply z⟩
    change bigonPlaneEquiv (A.symm z) ∈
      closure (Schoenflies.inside (bigonPlaneEquiv '' bigonCurveSet γ t₁ t₂))
    have : L (A.symm z) = q := by
      apply Φ.injective
      rw [hqz]
      simp only [Φ, Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph,
        ContinuousLinearEquiv.symm_apply_apply, Homeomorph.apply_symm_apply]
      rfl
    rw [this]
    exact hq

theorem exists_bigon_push_of_sign {σ : ℝ} (hσ : σ ^ 2 = 1) {γ : ℝ → ℝ × ℝ}
    (hγ : ContDiff ℝ ∞ γ) {c t₁ t₂ ε : ℝ} (ht : t₁ < t₂) (hε : 0 < ε)
    (h₁ : (γ t₁).2 = c) (h₂ : (γ t₂).2 = c)
    (hin : ∀ t ∈ Ioo t₁ t₂, 0 < σ * ((γ t).2 - c))
    (hout : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), t < t₁ ∨ t₂ < t → σ * ((γ t).2 - c) < 0)
    (htr₁ : (deriv γ t₁).2 ≠ 0) (htr₂ : (deriv γ t₂).2 ≠ 0)
    (himm : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), deriv γ t ≠ 0)
    (hinj : InjOn γ (Icc (t₁ - ε) (t₂ + ε)))
    {N : Set (ℝ × ℝ)} (hN : IsOpen N) (hDN : bigonRegion γ t₁ t₂ ⊆ N) :
    ∃ H : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => H q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (H q.1).symm q.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞ ∧
      (∃ K : Set (ℝ × ℝ), IsCompact K ∧ K ⊆ N ∧ ∀ s z, z ∉ K → H s z = z) ∧
      ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), σ * ((H 1 (γ t)).2 - c) < 0 := by
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσ
  have ht₁I : t₁ ∈ Icc (t₁ - ε) (t₂ + ε) := ⟨by linarith, by linarith⟩
  have ht₂I : t₂ ∈ Icc (t₁ - ε) (t₂ + ε) := ⟨by linarith, by linarith⟩
  set x₁ := (γ t₁).1
  set x₂ := (γ t₂).1
  have hx : x₁ ≠ x₂ := by
    intro he
    have : γ t₁ = γ t₂ := Prod.ext he (h₁.trans h₂.symm)
    exact ht.ne (hinj ht₁I ht₂I this)
  set μ := (x₁ + x₂) / 2
  set m := (x₂ - x₁) / 2
  have hm : m ≠ 0 := by
    intro h0
    apply hx
    change (x₂ - x₁) / 2 = 0 at h0
    linarith
  set lam := (t₂ - t₁) / 2
  have hlam : 0 < lam := by
    change 0 < (t₂ - t₁) / 2
    linarith
  set ν := (t₁ + t₂) / 2
  set θ : ℝ → ℝ := fun τ => ν + lam * τ
  set A := bigonAffine μ m σ c hm hσ0
  set γ' : ℝ → ℝ × ℝ := fun τ => A (γ (θ τ))
  set ε' := ε / lam
  have hε' : 0 < ε' := div_pos hε hlam
  have hθm : θ (-1) = t₁ := by
    change ν + lam * (-1) = t₁
    simp only [ν, lam]
    ring
  have hθp : θ 1 = t₂ := by
    change ν + lam * 1 = t₂
    simp only [ν, lam]
    ring
  have hθmem : ∀ τ, τ ∈ Icc (-1 - ε') (1 + ε') ↔ θ τ ∈ Icc (t₁ - ε) (t₂ + ε) := by
    intro τ
    have hlε : lam * ε' = ε := mul_div_cancel₀ ε hlam.ne'
    simp only [mem_Icc, θ, ν]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hlam.le,
        mul_le_mul_of_nonneg_left h2 hlam.le]
    · rintro ⟨h1, h2⟩
      constructor
      · by_contra hc
        push Not at hc
        have := mul_lt_mul_of_pos_left hc hlam
        nlinarith
      · by_contra hc
        push Not at hc
        have := mul_lt_mul_of_pos_left hc hlam
        nlinarith
  have hθlt : ∀ τ, τ < -1 ↔ θ τ < t₁ := by
    intro τ
    rw [← hθm]
    simp only [θ]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hθgt : ∀ τ, 1 < τ ↔ t₂ < θ τ := by
    intro τ
    rw [← hθp]
    simp only [θ]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hθIoo : ∀ τ, τ ∈ Ioo (-1 : ℝ) 1 → θ τ ∈ Ioo t₁ t₂ := by
    intro τ hτ
    exact ⟨by rw [← hθm]; simp only [θ]; nlinarith [hτ.1],
      by rw [← hθp]; simp only [θ]; nlinarith [hτ.2]⟩
  have hγ'2 : ∀ τ, (γ' τ).2 = σ * ((γ (θ τ)).2 - c) := fun τ => rfl
  have hγ'm : γ' (-1) = (-1, 0) := by
    refine Prod.ext ?_ ?_
    · change ((γ (θ (-1))).1 - μ) / m = -1
      rw [hθm]
      field_simp
      simp only [μ, m, x₁]
      ring
    · change σ * ((γ (θ (-1))).2 - c) = 0
      rw [hθm, h₁, sub_self, mul_zero]
  have hγ'p : γ' 1 = (1, 0) := by
    refine Prod.ext ?_ ?_
    · change ((γ (θ 1)).1 - μ) / m = 1
      rw [hθp]
      field_simp
      simp only [μ, m, x₂]
      ring
    · change σ * ((γ (θ 1)).2 - c) = 0
      rw [hθp, h₂, sub_self, mul_zero]
  have hγ's : ContDiff ℝ ∞ γ' :=
    (contMDiff_iff_contDiff.mp A.contMDiff).comp (hγ.comp (contDiff_const.add
      (contDiff_const.mul contDiff_id)))
  have hderiv : ∀ τ, HasDerivAt γ' (lam * (deriv γ (θ τ)).1 / m,
      σ * (lam * (deriv γ (θ τ)).2)) τ := by
    intro τ
    have hθd : HasDerivAt θ lam τ := by
      have := ((hasDerivAt_id τ).const_mul lam).const_add ν
      rw [mul_one] at this
      exact this
    have hγd : HasDerivAt γ (deriv γ (θ τ)) (θ τ) :=
      (hγ.differentiable (by simp) _).hasDerivAt
    have hc := hγd.scomp τ hθd
    have h1 : HasDerivAt (fun τ => ((γ (θ τ)).1 - μ) / m) (lam * (deriv γ (θ τ)).1 / m) τ := by
      have := (((hasFDerivAt_fst (𝕜 := ℝ) (p := γ (θ τ))).comp_hasDerivAt τ hc).sub_const
        μ).div_const m
      exact this.congr_deriv (by simp)
    have h2 : HasDerivAt (fun τ => σ * ((γ (θ τ)).2 - c)) (σ * (lam * (deriv γ (θ τ)).2)) τ := by
      have := (((hasFDerivAt_snd (𝕜 := ℝ) (p := γ (θ τ))).comp_hasDerivAt τ hc).sub_const
        c).const_mul σ
      exact this.congr_deriv (by simp)
    exact h1.prodMk h2
  have hderiv_eq : ∀ τ, deriv γ' τ = (lam * (deriv γ (θ τ)).1 / m,
      σ * (lam * (deriv γ (θ τ)).2)) := fun τ => (hderiv τ).deriv
  have himm' : ∀ τ ∈ Icc (-1 - ε') (1 + ε'), deriv γ' τ ≠ 0 := by
    intro τ hτ h0
    rw [hderiv_eq, Prod.mk_eq_zero] at h0
    apply himm (θ τ) ((hθmem τ).mp hτ)
    refine Prod.ext ?_ ?_
    · have : lam * (deriv γ (θ τ)).1 = 0 := by
        have := h0.1
        rwa [div_eq_zero_iff, or_iff_left hm] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hlam.ne'
      · exact h
    · have := h0.2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hσ0
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hlam.ne'
        · exact h
  have hinj' : InjOn γ' (Icc (-1 - ε') (1 + ε')) := by
    intro τ hτ τ' hτ' he
    have := hinj ((hθmem τ).mp hτ) ((hθmem τ').mp hτ') (A.injective he)
    simp only [θ] at this
    have := mul_left_cancel₀ hlam.ne' (add_left_cancel this)
    exact this
  have hout' : ∀ τ ∈ Icc (-1 - ε') (1 + ε'), τ < -1 ∨ 1 < τ → (γ' τ).2 < 0 := by
    intro τ hτ hlt
    rw [hγ'2]
    exact hout (θ τ) ((hθmem τ).mp hτ) (hlt.imp (hθlt τ).mp (hθgt τ).mp)
  have hin' : ∀ τ ∈ Ioo (-1 : ℝ) 1, 0 < (γ' τ).2 := by
    intro τ hτ
    rw [hγ'2]
    exact hin (θ τ) (hθIoo τ hτ)
  have hd2 : ∀ τ, HasDerivAt (fun τ => (γ' τ).2) (σ * (lam * (deriv γ (θ τ)).2)) τ :=
    fun τ => (hasFDerivAt_snd (𝕜 := ℝ) (p := γ' τ)).comp_hasDerivAt τ (hderiv τ)
  have htm' : 0 < (deriv γ' (-1)).2 := by
    rw [hderiv_eq]
    refine deriv_pos_of_zero_of_pos_right (b := 1) (by norm_num) (hd2 (-1)) ?_ hin' ?_
    · rw [hγ'm]
    · rw [hθm]
      exact mul_ne_zero hσ0 (mul_ne_zero hlam.ne' htr₁)
  have htp' : (deriv γ' 1).2 < 0 := by
    rw [hderiv_eq]
    refine deriv_neg_of_zero_of_pos_left (a := -1) (by norm_num) (hd2 1) ?_ hin' ?_
    · rw [hγ'p]
    · rw [hθp]
      exact mul_ne_zero hσ0 (mul_ne_zero hlam.ne' htr₂)
  have hcurve : A.toHomeomorph '' bigonCurveSet γ t₁ t₂ = bigonCurveSet γ' (-1) 1 := by
    unfold bigonCurveSet
    rw [image_union]
    congr 1
    · have hθI : θ '' Icc (-1) 1 = Icc t₁ t₂ := by
        have hθe : θ = fun x => lam * x + ν := funext fun x => add_comm _ _
        rw [← hθm, ← hθp, hθe, image_affine_Icc' hlam]
      rw [← hθI, image_image, image_image]
      rfl
    · change A '' segment ℝ (γ t₁) (γ t₂) = segment ℝ (γ' (-1)) (γ' 1)
      rw [bigonAffine_image_segment]
      change segment ℝ (A (γ t₁)) (A (γ t₂)) = segment ℝ (A (γ (θ (-1)))) (A (γ (θ 1)))
      rw [hθm, hθp]
  have hregion := bigonRegion_image A.toHomeomorph hcurve
  have hDN' : bigonRegion γ' (-1) 1 ⊆ A '' N := by
    rw [← hregion]
    exact image_mono hDN
  obtain ⟨H', hH', hH'', hH'0, ⟨K', hK'c, hK'N, hK'fix⟩, hpush⟩ :=
    exists_bigon_push_normal hγ's hε' hγ'm hγ'p hout' hin' htm' htp' himm' hinj'
      (A.toHomeomorph.isOpenMap N hN) hDN'
  have hAs : ContDiff ℝ ∞ (A : ℝ × ℝ → ℝ × ℝ) := contMDiff_iff_contDiff.mp A.contMDiff
  have hAs' : ContDiff ℝ ∞ (A.symm : ℝ × ℝ → ℝ × ℝ) := contMDiff_iff_contDiff.mp A.symm.contMDiff
  refine ⟨fun s => A.trans ((H' s).trans A.symm), ?_, ?_, ?_,
    ⟨A.symm '' K', hK'c.image A.symm.continuous, ?_, ?_⟩, ?_⟩
  · exact hAs'.comp (hH'.comp (contDiff_fst.prodMk (hAs.comp contDiff_snd)))
  · exact hAs'.comp (hH''.comp (contDiff_fst.prodMk (hAs.comp contDiff_snd)))
  · refine Diffeomorph.ext fun z => ?_
    change A.symm (H' 0 (A z)) = z
    rw [hH'0]
    simp
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hyz⟩ := hK'N hz
    rw [← hyz]
    change A.symm (A y) ∈ N
    rw [A.symm_apply_apply]
    exact hy
  · intro s z hz
    have hz' : A z ∉ K' := fun h => hz ⟨A z, h, A.symm_apply_apply z⟩
    change A.symm (H' s (A z)) = z
    rw [hK'fix s _ hz', A.symm_apply_apply]
  · intro t ht
    set τ := (t - ν) / lam
    have hτ : θ τ = t := by
      simp only [θ, τ]
      field_simp
      ring
    have hτI : τ ∈ Icc (-1 - ε') (1 + ε') := (hθmem τ).mpr (hτ ▸ ht)
    have h := hpush τ hτI
    change σ * ((A.symm (H' 1 (A (γ t)))).2 - c) < 0
    rw [← hτ]
    change (H' 1 (γ' τ)).2 < 0 at h
    rw [bigonAffine_symm_apply]
    simp only
    have : σ * ((H' 1 (γ' τ)).2 / σ + c - c) = (H' 1 (γ' τ)).2 := by
      field_simp
      ring
    rw [this]
    exact h

theorem exists_bigon_push {γ : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ) {c t₁ t₂ ε : ℝ} (ht : t₁ < t₂)
    (hε : 0 < ε) (h₁ : (γ t₁).2 = c) (h₂ : (γ t₂).2 = c)
    (hin : ∀ t ∈ Ioo t₁ t₂, c < (γ t).2)
    (hout : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), t < t₁ ∨ t₂ < t → (γ t).2 < c)
    (htr₁ : (deriv γ t₁).2 ≠ 0) (htr₂ : (deriv γ t₂).2 ≠ 0)
    (himm : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), deriv γ t ≠ 0)
    (hinj : InjOn γ (Icc (t₁ - ε) (t₂ + ε)))
    {N : Set (ℝ × ℝ)} (hN : IsOpen N) (hDN : bigonRegion γ t₁ t₂ ⊆ N) :
    ∃ H : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => H q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (H q.1).symm q.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞ ∧
      (∃ K : Set (ℝ × ℝ), IsCompact K ∧ K ⊆ N ∧ ∀ s z, z ∉ K → H s z = z) ∧
      ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), (H 1 (γ t)).2 < c := by
  obtain ⟨H, h1, h2, h3, h4, h5⟩ := exists_bigon_push_of_sign (σ := 1) (by norm_num) hγ ht hε
    h₁ h₂ (fun t ht => by linarith [hin t ht]) (fun t ht h => by linarith [hout t ht h])
    htr₁ htr₂ himm hinj hN hDN
  exact ⟨H, h1, h2, h3, h4, fun t ht => by linarith [h5 t ht]⟩

theorem exists_bigon_push_below {γ : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ) {c t₁ t₂ ε : ℝ}
    (ht : t₁ < t₂) (hε : 0 < ε) (h₁ : (γ t₁).2 = c) (h₂ : (γ t₂).2 = c)
    (hin : ∀ t ∈ Ioo t₁ t₂, (γ t).2 < c)
    (hout : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), t < t₁ ∨ t₂ < t → c < (γ t).2)
    (htr₁ : (deriv γ t₁).2 ≠ 0) (htr₂ : (deriv γ t₂).2 ≠ 0)
    (himm : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), deriv γ t ≠ 0)
    (hinj : InjOn γ (Icc (t₁ - ε) (t₂ + ε)))
    {N : Set (ℝ × ℝ)} (hN : IsOpen N) (hDN : bigonRegion γ t₁ t₂ ⊆ N) :
    ∃ H : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => H q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (H q.1).symm q.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞ ∧
      (∃ K : Set (ℝ × ℝ), IsCompact K ∧ K ⊆ N ∧ ∀ s z, z ∉ K → H s z = z) ∧
      ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), c < (H 1 (γ t)).2 := by
  obtain ⟨H, h1, h2, h3, h4, h5⟩ := exists_bigon_push_of_sign (σ := -1) (by norm_num) hγ ht hε
    h₁ h₂ (fun t ht => by linarith [hin t ht]) (fun t ht h => by linarith [hout t ht h])
    htr₁ htr₂ himm hinj hN hDN
  exact ⟨H, h1, h2, h3, h4, fun t ht => by linarith [h5 t ht]⟩

end GC.Seifert
