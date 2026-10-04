import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelSolidInj
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelCoverPlanar

/-!
# The capped solid tori cover the cap and the split region

Lane N2f, side model, step 6 (cover). Every point of the split region `V ∪ H` whose image lies in
the core of the split tube is the lift of a model point of one side at a level of the sign of that
side (`exists_lift_of_splitRegion`): for `V` the meridian disc point itself, for `H` the nested
circle of side `t` through its host chart point (`exists_point_eq`), and for the host circle of `H`
the seam gluing with the boundary torus of `V` (`cutMap_solidPt_three`). The level is at least one
in absolute value, as the removed band is not in the core. The ball chart `Φ` of a side covers the
tube levels `(1, 5/2)` of that side (`exists_ball_eq_tube`, by connectedness of `S² × (1, 5/2)`),
so `solMap` covers the cap (`exists_solMap_eq_cap`) and every core point of the split region on
its side (`exists_solMap_eq_coreMap`), and its values are cap points or core points of the split
region (`solMap_image`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace GC.Seifert.ElementaryPresentation

open SplitTube

theorem exists_sgnR_mul_eq_abs (x : ℝ) : ∃ t : Bool, sgnR t * x = |x| := by
  rcases le_or_gt 0 x with hx | hx
  · exact ⟨true, by rw [sgnR_true, one_mul, abs_of_nonneg hx]⟩
  · exact ⟨false, by rw [sgnR_false, abs_of_neg hx]; ring⟩

section Lift

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b) (hlin : E.IsLinearSeam j)

theorem liftPt_mem_splitRegion (t : Bool) (q : ℂ × Circle) :
    E.InSplitRegion (j := j) (b := b) (E.liftPt h hlin t q) := by
  unfold liftPt
  split_ifs
  · exact Or.inl (E.solidPt_mem h _ _)
  · exact Or.inr (E.hostPt_mem h _ _)

theorem tubeMap_not_mem_core {p : S2} {lv : ℝ} (h1 : |lv| < 1) :
    (E.splitCharts h hlin).tubeMap (p, lv) ∉ (E.splitSeamTube j b h hlin).core := by
  intro hc
  apply hc
  have hm := abs_lt.mp h1
  exact mem_iUnion.mpr ⟨(), (p, ⟨lv, by constructor <;> linarith⟩), ⟨hm.1, hm.2⟩, rfl⟩

theorem one_le_abs_of_mem_core {t : Bool} {q : ℂ × Circle} (hq : E.sideDom h t q)
    (hc : (E.splitCharts h hlin).liftMap t q ∈ (E.splitSeamTube j b h hlin).core) :
    1 ≤ |E.sideLevel h t q| := by
  by_contra hlt
  push Not at hlt
  obtain ⟨p, hp⟩ := E.exists_tubeMap_eq_liftMap h hlin t hq (by linarith)
  rw [← hp] at hc
  exact E.tubeMap_not_mem_core h hlin hlt hc

theorem exists_lift_of_solidPt {z : ℂ} (hz : ‖z‖ ≤ 3) (w : Circle) :
    ∃ t q, E.sideDom h t q ∧ sgnR t * E.sideLevel h t q = |E.sideLevel h t q| ∧
      (E.splitCharts h hlin).liftMap t q = E.toTorus.cutMap (E.solidPt h z w) := by
  have he₀ := (E.splitCharts h hlin).he₀
  set q : ℂ × Circle := ((1 / 2 : ℝ) • z, w ^ (E.splitCharts h hlin).e₀) with hqdef
  have hn : ‖q.1‖ ≤ 3 / 2 := by
    change ‖(1 / 2 : ℝ) • z‖ ≤ 3 / 2
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith
  obtain ⟨t, ht⟩ := exists_sgnR_mul_eq_abs (E.sideLevel h false q)
  have hlv : E.sideLevel h t q = E.sideLevel h false q :=
    E.sideLevel_eq_of_le h t false (by linarith)
  refine ⟨t, q, (E.sideDom_iff h).mpr ⟨by linarith, ?_⟩, by rw [hlv, ht], ?_⟩
  · rw [hlv, ht]
    linarith [abs_nonneg (E.sideLevel h false q)]
  · rw [E.liftMap_eq_cutMap]
    unfold liftPt
    rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
    have e1 : (2 : ℝ) • q.1 = z := by
      change (2 : ℝ) • (1 / 2 : ℝ) • z = z
      rw [smul_smul]
      norm_num
    have e2 : q.2 ^ (E.splitCharts h hlin).e₀ = w := zpow_zpow_unit he₀ w
    rw [e1, e2]

theorem cutMap_solidPt_three (τ : Torus) :
    E.toTorus.cutMap (E.solidPt h ((3 : ℝ) • (τ.1 : ℂ)) τ.2) =
      E.toTorus.cutMap (E.hostPt h (planarCollarFormula 3 (E.hostSide h)
        (((E.crossMap j b τ).1 : ℂ), 0)) (E.crossMap j b τ).2) := by
  rw [E.solidPt_three_smul h, E.hostPt_collar h, E.standardPort_hostSide h]
  have e0 := E.cutMap_sideCollar_eq_seam j b τ 0 le_rfl zero_lt_one
  have e1 := E.cutMap_sideCollar_eq_seam j (!b) (E.crossMap j b τ) 0 le_rfl zero_lt_one
  rw [E.leftOfSide_not_crossMap, sideHeight_not] at e1
  change E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j b) (τ, halfPoint 0 le_rfl)) =
    E.toTorus.cutMap (E.toTorus.sideCollar (E.seamSide j !b)
      (E.crossMap j b τ, halfPoint 0 le_rfl))
  rw [e0, e1]
  cases b <;> simp [sideHeight]

theorem exists_lift_of_hostPt {z : ℂ} (hz : z ∈ planarModel 3) (ν : Circle) :
    ∃ t q, E.sideDom h t q ∧ sgnR t * E.sideLevel h t q = |E.sideLevel h t q| ∧
      (E.splitCharts h hlin).liftMap t q = E.toTorus.cutMap (E.hostPt h z ν) := by
  have he₁ := (E.splitCharts h hlin).he₁
  set l := E.hostSide h with hl
  obtain ⟨t, ht⟩ := exists_sgnR_mul_eq_abs (stripLevel l (hostInv l z))
  obtain ⟨⟨u, ρ⟩, hρ, hpt⟩ := exists_point_eq l t hz
  simp only at hρ hpt
  rcases eq_or_lt_of_le hρ.1 with h32 | h32
  · subst h32
    have key : hostChart l ((sideData l t).point (u, 3 / 2)) =
        planarCollarFormula 3 l ((u : ℂ), (4 * (3 / 2) - 6) / 3) :=
      (E.splitCharts h hlin).hostChart_point_of_le t (by norm_num) (by norm_num)
    rw [hpt, hostChart_hostInv, show (4 * (3 / 2 : ℝ) - 6) / 3 = 0 by norm_num] at key
    set τ := (E.crossMap j b).symm (u, ν) with hτ
    have hc : E.crossMap j b τ = (u, ν) := (E.crossMap j b).apply_symm_apply _
    have hglue := E.cutMap_solidPt_three h τ
    rw [hc] at hglue
    obtain ⟨t', q', hq', hs', he'⟩ := E.exists_lift_of_solidPt h hlin (z := (3 : ℝ) • (τ.1 : ℂ))
      (by rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by norm_num)]) τ.2
    refine ⟨t', q', hq', hs', ?_⟩
    rw [he', hglue, key]
  · set θ : Circle := (ν * (u ^ ((E.splitCharts h hlin).e₀ * (E.splitCharts h hlin).d))⁻¹) ^
      (E.splitCharts h hlin).e₁ with hθ
    set q : ℂ × Circle := (ρ • (θ : ℂ), u) with hqdef
    have hn : ‖q.1‖ = ρ := by
      change ‖ρ • (θ : ℂ)‖ = ρ
      rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by linarith)]
    have hu : unitOf q.1 = θ := unitOf_smul (by linarith) θ
    have hlev : E.sideLevel h t q = stripLevel l (hostInv l z) := by
      unfold sideLevel
      rw [hn]
      change stripLevel l ((sideData l t).point (u, ρ)) = _
      rw [hpt]
    refine ⟨t, q, (E.sideDom_iff h).mpr ⟨by rw [hn]; exact hρ.2, ?_⟩, by rw [hlev, ht], ?_⟩
    · rw [hlev, ht]
      linarith [abs_nonneg (stripLevel l (hostInv l z))]
    · rw [E.liftMap_eq_cutMap]
      unfold liftPt
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hn]; linarith))]
      have e1 : hostChart (E.hostSide h) ((sideData (E.hostSide h) t).point (q.2, ‖q.1‖)) = z := by
        rw [hn]
        change hostChart l ((sideData l t).point (u, ρ)) = z
        rw [hpt, hostChart_hostInv]
      have e2 : E.liftFib h hlin q = ν := by
        unfold liftFib
        rw [hu, hθ, zpow_zpow_unit he₁, mul_comm ν, mul_inv_cancel_left]
      rw [e1, e2]

theorem exists_solidPt_eq {y : E.toTorus.cutCarrier.Carrier}
    (hy : y ∈ E.toTorus.components.piece (E.seamPiece j b)) :
    ∃ z : ℂ, ‖z‖ ≤ 3 ∧ ∃ w : Circle, E.solidPt h z w = y := by
  obtain ⟨⟨x, w⟩, hx⟩ := (E.splitData h).ΘV.surjective ⟨y, hy⟩
  have hx3 : ‖(show discSet.{u} from x).val.down‖ ≤ 3 := (mem_discSet_iff _).mp x.2
  refine ⟨(show discSet.{u} from x).val.down, hx3, w, ?_⟩
  have hcl : clampDisc.{u} (show discSet.{u} from x).val.down = x := by
    apply Subtype.ext
    exact clampDisc_val hx3
  unfold solidPt
  rw [hcl]
  exact congrArg Subtype.val hx

theorem exists_hostPt_eq {y : E.toTorus.cutCarrier.Carrier}
    (hy : y ∈ E.toTorus.components.piece (E.hostPiece j b)) :
    ∃ z : ℂ, z ∈ planarModel 3 ∧ ∃ ν : Circle, E.hostPt h z ν = y := by
  obtain ⟨⟨x, ν⟩, hx⟩ := (E.splitData h).ΘH.surjective ⟨y, hy⟩
  have hx3 : (show planarSet.{u} 3 from x).val.down ∈ planarModel 3 :=
    (mem_planarSet_iff (Or.inr rfl) _).mp x.2
  refine ⟨(show planarSet.{u} 3 from x).val.down, hx3, ν, ?_⟩
  have hcl : clampPants.{u} (show planarSet.{u} 3 from x).val.down = x := by
    apply Subtype.ext
    exact clampPants_val hx3
  unfold hostPt
  rw [hcl]
  exact congrArg Subtype.val hx

theorem exists_lift_of_splitRegion {y : E.toTorus.cutCarrier.Carrier}
    (hy : E.InSplitRegion (j := j) (b := b) y) :
    ∃ t q, E.sideDom h t q ∧ sgnR t * E.sideLevel h t q = |E.sideLevel h t q| ∧
      (E.splitCharts h hlin).liftMap t q = E.toTorus.cutMap y := by
  rcases hy with hy | hy
  · obtain ⟨z, hz, w, rfl⟩ := E.exists_solidPt_eq h hy
    exact E.exists_lift_of_solidPt h hlin hz w
  · obtain ⟨z, hz, ν, rfl⟩ := E.exists_hostPt_eq h hy
    exact E.exists_lift_of_hostPt h hlin hz ν

end Lift

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {E : ElementaryPresentation (NoCuts.carrier Q)}
  {j : Fin E.toTorus.pairing.count} {b : Bool} {h : E.IsSplitSeam j b} {hlin : E.IsLinearSeam j}
  {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N (E.splitSeamTube j b h hlin)}

theorem coreMap_boundarySphere_eq_cap (c : (E.splitSeamTube j b h hlin).Boundary) (p : S2) :
    coreMap K ((E.splitSeamTube j b h hlin).boundarySphere c p) =
      K.cap c (sphereToClosedCell ((K.attaching c).symm p)) := by
  rw [K.boundary_eq c, Diffeomorph.apply_symm_apply,
    coreMap_of_mem K ((E.splitSeamTube j b h hlin).boundarySphere_mem_core c p)]
  rfl

theorem rank_lt_E3 : 1 < Module.rank ℝ E3 := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (by norm_num : (1 : ℕ) < 3)

namespace SideCap

variable {t : Bool} (S : E.SideCap h hlin K t)

theorem exists_ball_eq_tube (z : S2) {r : ℝ} (h1 : 1 < r) (h2 : r < 5 / 2) :
    ∃ x : E3, ‖x‖ = r ∧
      S.Φ x = coreMap K ((E.splitCharts h hlin).tubeMap (z, sgnR t * r)) := by
  set C := E.splitCharts h hlin
  let Λ : S2 × ℝ → N.Carrier := fun p => coreMap K (C.tubeMap (p.1, sgnR t * p.2))
  set B : Set (S2 × ℝ) := {p | 1 < p.2 ∧ p.2 < 5 / 2 ∧ ∃ x : E3, ‖x‖ = p.2 ∧ S.Φ x = Λ p}
    with hB
  have habs : ∀ s : ℝ, 0 < s → |sgnR t * s| = s := fun s hs => abs_sgnR_mul_of_pos t hs
  have hΛ : ∀ p : S2 × ℝ, 1 < p.2 → p.2 < 3 → ContinuousAt Λ p := by
    intro p hp1 hp3
    have hc := (IsLocalDiffeomorphAt.contMDiffAt
      (C.isLocalDiffeomorphAt_coreMap_tubeMap K (q := (p.1, sgnR t * p.2))
      (by change 1 < |sgnR t * p.2|; rw [habs _ (by linarith)]; exact hp1)
      (by change |sgnR t * p.2| < 3; rw [habs _ (by linarith)]; exact hp3))).continuousAt
    exact ContinuousAt.comp (f := fun p : S2 × ℝ => (p.1, sgnR t * p.2)) hc (by fun_prop)
  have hnorm : ∀ (x : E3) (p : S2 × ℝ), 1 ≤ ‖x‖ → ‖x‖ < 5 / 2 → 1 ≤ p.2 → p.2 < 3 →
      S.Φ x = Λ p → ‖x‖ = p.2 := by
    intro x p hx1 hx2 hp1 hp3 he
    obtain ⟨z', hz'⟩ := S.shell x hx1 hx2
    rw [hz'] at he
    have hq := C.coreMap_tubeMap_inj K (q := (z', sgnR t * ‖x‖)) (q' := (p.1, sgnR t * p.2))
      (by change 1 ≤ |sgnR t * ‖x‖|; rw [habs _ (by linarith)]; exact hx1)
      (by change |sgnR t * ‖x‖| < 3; rw [habs _ (by linarith)]; linarith)
      (by change 1 ≤ |sgnR t * p.2|; rw [habs _ (by linarith)]; exact hp1)
      (by change |sgnR t * p.2| < 3; rw [habs _ (by linarith)]; exact hp3) he
    exact mul_left_cancel₀ (SplitCharts.sgnR_ne_zero t) (congrArg Prod.snd hq)
  have hWo : IsOpen {x : E3 | 1 < ‖x‖ ∧ ‖x‖ < 5 / 2} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hW : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ S.Φ {x : E3 | 1 < ‖x‖ ∧ ‖x‖ < 5 / 2} :=
    fun x => S.loc x x.2.2
  have hstrip : IsOpen {p : S2 × ℝ | 1 < p.2 ∧ p.2 < 5 / 2} :=
    (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)
  have hopen : IsOpen B := by
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨hp1, hp2, x, hx, hxe⟩
    have hxW : x ∈ {x : E3 | 1 < ‖x‖ ∧ ‖x‖ < 5 / 2} :=
      ⟨by rw [hx]; exact hp1, by rw [hx]; exact hp2⟩
    have himg : S.Φ '' {x : E3 | 1 < ‖x‖ ∧ ‖x‖ < 5 / 2} ∈ 𝓝 (S.Φ x) := by
      rw [← hW.isLocalHomeomorphOn.map_nhds_eq hxW]
      exact image_mem_map (hWo.mem_nhds hxW)
    rw [hxe] at himg
    have hpre := (hΛ p hp1 (by linarith)).preimage_mem_nhds himg
    filter_upwards [hpre, hstrip.mem_nhds ⟨hp1, hp2⟩] with p' hp' hs'
    obtain ⟨x', hx', hx'e⟩ := hp'
    exact ⟨hs'.1, hs'.2, x', hnorm x' p' hx'.1.le hx'.2 hs'.1.le (by linarith [hs'.2]) hx'e,
      hx'e⟩
  have hclosed : closure B ∩ (univ ×ˢ Ioo 1 (5 / 2)) ⊆ B := by
    rintro p ⟨hpc, -, hp1, hp2⟩
    set ρ₁ := (1 + p.2) / 2 with hρ₁
    set ρ₂ := (p.2 + 5 / 2) / 2 with hρ₂
    set A : Set E3 := {x | ρ₁ ≤ ‖x‖ ∧ ‖x‖ ≤ ρ₂} with hA
    have hAc : IsCompact A := (isCompact_closedBall (0 : E3) ρ₂).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      (fun x hx => mem_closedBall_zero_iff.mpr hx.2)
    have hΦA : ContinuousOn S.Φ A := fun x hx =>
      (IsLocalDiffeomorphAt.contMDiffAt
        (S.loc x (by linarith [hx.2]))).continuousAt.continuousWithinAt
    have hIc : IsClosed (S.Φ '' A) := (hAc.image_of_continuousOn hΦA).isClosed
    set O : Set (S2 × ℝ) := {p' | ρ₁ < p'.2 ∧ p'.2 < ρ₂} with hO
    have hOo : IsOpen O :=
      (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)
    have hpO : p ∈ O := ⟨by linarith, by linarith⟩
    have hsub : Λ '' (B ∩ O) ⊆ S.Φ '' A := by
      rintro _ ⟨p', ⟨⟨-, -, x, hx, hxe⟩, ho1, ho2⟩, rfl⟩
      exact ⟨x, ⟨by rw [hx]; exact ho1.le, by rw [hx]; exact ho2.le⟩, hxe⟩
    have hpc' : p ∈ closure (B ∩ O) := by
      have := hOo.inter_closure ⟨hpO, hpc⟩
      rwa [inter_comm] at this
    have hmem : Λ p ∈ closure (Λ '' (B ∩ O)) := mem_closure_image (hΛ p hp1 (by linarith)) hpc'
    obtain ⟨x, hxA, hxe⟩ := hIc.closure_subset_iff.mpr hsub hmem
    have hx1 : 1 < ‖x‖ := by linarith [hxA.1]
    exact ⟨hp1, hp2, x, hnorm x p hx1.le (by linarith [hxA.2]) hp1.le (by linarith) hxe, hxe⟩
  have hconn : IsPreconnected (univ ×ˢ Ioo (1 : ℝ) (5 / 2) : Set (S2 × ℝ)) := by
    have hsp : IsConnected (sphere (0 : E3) 1) := isConnected_sphere rank_lt_E3 0 zero_le_one
    have _ : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp hsp
    exact isPreconnected_univ.prod isPreconnected_Ioo
  have hne : ((univ ×ˢ Ioo (1 : ℝ) (5 / 2)) ∩ B).Nonempty := by
    set x₀ : E3 := (2 : ℝ) • ((poleS2 : S2) : E3) with hx₀def
    have hx₀ : ‖x₀‖ = 2 := by
      rw [hx₀def, norm_smul, norm_eq_of_mem_sphere poleS2, Real.norm_of_nonneg (by norm_num)]
      norm_num
    refine ⟨(Manifold.sphereDirection poleS2 x₀, ‖x₀‖), ⟨trivial, by rw [hx₀]; norm_num,
      by rw [hx₀]; norm_num⟩, by rw [hx₀]; norm_num, by rw [hx₀]; norm_num, x₀, rfl, ?_⟩
    exact S.shell' x₀ (by rw [hx₀]; linarith [S.r_le]) (by rw [hx₀]; norm_num)
  have hall := hconn.subset_of_closure_inter_subset hopen hne hclosed
  obtain ⟨-, -, x, hx, hxe⟩ := hall (show (z, r) ∈ univ ×ˢ Ioo (1 : ℝ) (5 / 2) from
    ⟨trivial, h1, h2⟩)
  exact ⟨x, hx, hxe⟩

theorem exists_solMap_eq_ball {x : E3} (hx : ‖x‖ ≤ 2) :
    ∃ q : ℂ × Circle, ‖q.1‖ ≤ 3 ∧ S.solMap q = S.Φ x := by
  obtain ⟨q, h3, h2, hG⟩ := S.G_onto ((1 / 2 : ℝ) • x) (by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith)
  refine ⟨q, h3.le, ?_⟩
  rw [S.solMap_of_fake h3 h2, ← hG, S.G.symm_apply_apply, smul_smul]
  norm_num

theorem exists_solMap_eq_cap (w : ClosedCell 3) :
    ∃ q : ℂ × Circle, ‖q.1‖ ≤ 3 ∧ S.solMap q = K.cap ((), t) w := by
  obtain ⟨x, hx, he⟩ := S.cap_surj w
  obtain ⟨q, hq, hq'⟩ := S.exists_solMap_eq_ball (x := x) (by linarith)
  exact ⟨q, hq, hq'.trans he⟩

theorem exists_solMap_eq_coreMap {q : ℂ × Circle} (hq : E.sideDom h t q)
    (hpos : sgnR t * E.sideLevel h t q = |E.sideLevel h t q|)
    (hc : (E.splitCharts h hlin).liftMap t q ∈ (E.splitSeamTube j b h hlin).core) :
    ∃ q' : ℂ × Circle, ‖q'.1‖ ≤ 3 ∧
      S.solMap q' = coreMap K ((E.splitCharts h hlin).liftMap t q) := by
  have h1 := E.one_le_abs_of_mem_core h hlin hq hc
  by_cases h2 : 2 < |E.sideLevel h t q|
  · exact ⟨q, hq.1, S.solMap_of_real (by rw [hpos]; exact h2)⟩
  · push Not at h2
    obtain ⟨p, hp⟩ := E.exists_tubeMap_eq_liftMap h hlin t hq (by linarith)
    have hL : E.sideLevel h t q = sgnR t * |E.sideLevel h t q| := by
      rw [← hpos, ← mul_assoc, sgnR_mul_self, one_mul]
    rw [← hp, hL]
    rcases eq_or_lt_of_le h1 with he | hlt
    · rw [← he, mul_one, ← (E.splitCharts h hlin).boundarySphere_eq ((), t) p]
      obtain ⟨q', hq', he'⟩ :=
        S.exists_solMap_eq_cap (sphereToClosedCell ((K.attaching ((), t)).symm p))
      exact ⟨q', hq', he'.trans (coreMap_boundarySphere_eq_cap ((), t) p).symm⟩
    · obtain ⟨x, hx, hxe⟩ := S.exists_ball_eq_tube p hlt (by linarith)
      obtain ⟨q', hq', he'⟩ := S.exists_solMap_eq_ball (x := x) (by rw [hx]; exact h2)
      exact ⟨q', hq', he'.trans hxe⟩

theorem solMap_image {q : ℂ × Circle} (hq : ‖q.1‖ ≤ 3) :
    (∃ w, S.solMap q = K.cap ((), t) w) ∨ ∃ y : E.toTorus.cutCarrier.Carrier,
      E.InSplitRegion (j := j) (b := b) y ∧
        E.toTorus.cutMap y ∈ (E.splitSeamTube j b h hlin).core ∧
          S.solMap q = coreMap K (E.toTorus.cutMap y) := by
  rcases S.solMap_cases hq with ⟨h3, h2, e⟩ | ⟨hd, h2, e⟩
  · rw [e]
    rcases S.fakeMap_cases h3 h2 with hcap | ⟨z, r, h1, hr2, hz⟩
    · exact Or.inl hcap
    · right
      have habs : |sgnR t * r| = r := abs_sgnR_mul_of_pos t (by linarith)
      obtain ⟨q', -, -, -, he'⟩ := E.exists_liftMap_eq_tubeMap h hlin t z
        (lv := sgnR t * r) (by rw [habs]; linarith)
      refine ⟨E.liftPt h hlin t q', E.liftPt_mem_splitRegion h hlin t q', ?_, ?_⟩
      · rw [← E.liftMap_eq_cutMap, he']
        exact (E.splitCharts h hlin).tubeMap_mem_core (q := (z, sgnR t * r))
          (by change 1 ≤ |sgnR t * r|; rw [habs]; linarith)
          (by change |sgnR t * r| < 3; rw [habs]; linarith)
      · rw [hz, ← E.liftMap_eq_cutMap, he']
  · right
    refine ⟨E.liftPt h hlin t q, E.liftPt_mem_splitRegion h hlin t q, ?_, ?_⟩
    · rw [← E.liftMap_eq_cutMap]
      exact liftMap_mem_core hd (one_lt_abs_sideLevel h2)
    · rw [e, E.liftMap_eq_cutMap]

end SideCap

theorem exists_solMap_eq_of_splitRegion (S : ∀ t, E.SideCap h hlin K t)
    {y : E.toTorus.cutCarrier.Carrier} (hy : E.InSplitRegion (j := j) (b := b) y)
    (hc : E.toTorus.cutMap y ∈ (E.splitSeamTube j b h hlin).core) :
    ∃ t, ∃ q : ℂ × Circle, ‖q.1‖ ≤ 3 ∧ (S t).solMap q = coreMap K (E.toTorus.cutMap y) := by
  obtain ⟨t, q, hq, hpos, he⟩ := E.exists_lift_of_splitRegion h hlin hy
  rw [← he] at hc ⊢
  obtain ⟨q', hq', he'⟩ := (S t).exists_solMap_eq_coreMap hq hpos hc
  exact ⟨t, q', hq', he'⟩

end GC.Seifert.ElementaryPresentation
