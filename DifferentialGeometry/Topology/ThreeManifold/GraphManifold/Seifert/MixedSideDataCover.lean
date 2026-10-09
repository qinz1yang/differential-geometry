import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSideDataSolid
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelCover

/-!
# The capped solid tori of a mixed split cover the cap and the split region

Lane N2f, tier 2. The text of `MoveSplitCappedSideModelCover` for a mixed split site:
every point of the split region `V ∪ H` whose image lies in the core of the split tube is a lifted
model point of one side at a level of the sign of that side (`exists_lift_of_splitRegion`), the
ball chart covers the tube levels `(1, 5/2)` (`exists_ball_eq_tube`), so `solMap` covers the cap
and the core points of the split region and its values are cap points or such core points
(`exists_solMap_eq_of_splitRegion`, `SideCap.solMap_image`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace GC.Seifert.RelativeNormalization.MixedStage

open GC.Seifert.ElementaryPresentation (clampDisc clampPants clampDisc_val clampPants_val
  discCollar_eq pantsCollar_eq isLocalDiffeomorphAt_clampDisc isLocalDiffeomorphAt_clampPants
  sideHeight sideHeight_not sideHeight_neg seamRadius_one OnSolidBoundary neg_three_lt_sgnR_mul
  sgnR_mul_lt_three sqrt_three_half_sq sqrt_three_half_lt_one seamHeight_pos_of_lt
  seamHeight_sqrt_three_half seamHeight_neg_sqrt_three_half exists_bandHeight_eq
  abs_sgnR_mul_of_pos sgnR_false sgnR_true exists_sgnR_mul_eq_abs rank_lt_E3)

section

open SplitTube

section Lift

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} (h : σ.IsSplitSeam j b) (SD : σ.SplitData h)
  (hlin : σ.IsLinearSeam j)

theorem liftPt_mem_splitRegion (t : Bool) (q : ℂ × Circle) :
    σ.InSplitRegion (j := j) (b := b) (σ.liftPt h SD hlin t q) := by
  unfold liftPt
  split_ifs
  · exact Or.inl (σ.solidPt_mem h SD _ _)
  · exact Or.inr (σ.hostPt_mem h SD _ _)

theorem tubeMap_not_mem_core {p : S2} {lv : ℝ} (h1 : |lv| < 1) :
    (σ.splitCharts SD hlin).tubeMap (p, lv) ∉ (σ.splitSeamTube SD hlin).core := by
  intro hc
  apply hc
  have hm := abs_lt.mp h1
  exact mem_iUnion.mpr ⟨(), (p, ⟨lv, by constructor <;> linarith⟩), ⟨hm.1, hm.2⟩, rfl⟩

theorem one_le_abs_of_mem_core {t : Bool} {q : ℂ × Circle} (hq : σ.sideDom h t q)
    (hc : (σ.splitCharts SD hlin).liftMap t q ∈ (σ.splitSeamTube SD hlin).core) :
    1 ≤ |σ.sideLevel h t q| := by
  by_contra hlt
  push Not at hlt
  obtain ⟨p, hp⟩ := σ.exists_tubeMap_eq_liftMap h SD hlin t hq (by linarith)
  rw [← hp] at hc
  exact σ.tubeMap_not_mem_core h SD hlin hlt hc

theorem exists_lift_of_solidPt {z : ℂ} (hz : ‖z‖ ≤ 3) (w : Circle) :
    ∃ t q, σ.sideDom h t q ∧ sgnR t * σ.sideLevel h t q = |σ.sideLevel h t q| ∧
      (σ.splitCharts SD hlin).liftMap t q = σ.toTorus.cutMap (σ.solidPt h SD z w) := by
  have he₀ := (σ.splitCharts SD hlin).he₀
  set q : ℂ × Circle := ((1 / 2 : ℝ) • z, w ^ (σ.splitCharts SD hlin).e₀) with hqdef
  have hn : ‖q.1‖ ≤ 3 / 2 := by
    change ‖(1 / 2 : ℝ) • z‖ ≤ 3 / 2
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith
  obtain ⟨t, ht⟩ := exists_sgnR_mul_eq_abs (σ.sideLevel h false q)
  have hlv : σ.sideLevel h t q = σ.sideLevel h false q :=
    σ.sideLevel_eq_of_le h t false (by linarith)
  refine ⟨t, q, (σ.sideDom_iff h).mpr ⟨by linarith, ?_⟩, by rw [hlv, ht], ?_⟩
  · rw [hlv, ht]
    linarith [abs_nonneg (σ.sideLevel h false q)]
  · rw [σ.liftMap_eq_cutMap]
    unfold liftPt
    rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
    have e1 : (2 : ℝ) • q.1 = z := by
      change (2 : ℝ) • (1 / 2 : ℝ) • z = z
      rw [smul_smul]
      norm_num
    have e2 : q.2 ^ (σ.splitCharts SD hlin).e₀ = w := zpow_zpow_unit he₀ w
    rw [e1, e2]

theorem cutMap_solidPt_three (τ : Torus) :
    σ.toTorus.cutMap (σ.solidPt h SD ((3 : ℝ) • (τ.1 : ℂ)) τ.2) =
      σ.toTorus.cutMap (σ.hostPt h SD (planarCollarFormula 3 (σ.hostSide h)
        (((σ.crossMap j b τ).1 : ℂ), 0)) (σ.crossMap j b τ).2) := by
  rw [σ.solidPt_three_smul h SD, σ.hostPt_collar h SD, σ.standardPort_hostSide h]
  have e0 := σ.cutMap_sideCollar_eq_seam j b τ 0 le_rfl zero_lt_one
  have e1 := σ.cutMap_sideCollar_eq_seam j (!b) (σ.crossMap j b τ) 0 le_rfl zero_lt_one
  rw [σ.leftOfSide_not_crossMap, sideHeight_not] at e1
  change σ.toTorus.cutMap (σ.toTorus.sideCollar (σ.seamSide j b) (τ, halfPoint 0 le_rfl)) =
    σ.toTorus.cutMap (σ.toTorus.sideCollar (σ.seamSide j !b)
      (σ.crossMap j b τ, halfPoint 0 le_rfl))
  rw [e0, e1]
  cases b <;> simp [sideHeight]

theorem exists_lift_of_hostPt {z : ℂ} (hz : z ∈ planarModel 3) (ν : Circle) :
    ∃ t q, σ.sideDom h t q ∧ sgnR t * σ.sideLevel h t q = |σ.sideLevel h t q| ∧
      (σ.splitCharts SD hlin).liftMap t q = σ.toTorus.cutMap (σ.hostPt h SD z ν) := by
  have he₁ := (σ.splitCharts SD hlin).he₁
  set l := σ.hostSide h with hl
  obtain ⟨t, ht⟩ := exists_sgnR_mul_eq_abs (stripLevel l (hostInv l z))
  obtain ⟨⟨u, ρ⟩, hρ, hpt⟩ := exists_point_eq l t hz
  simp only at hρ hpt
  rcases eq_or_lt_of_le hρ.1 with h32 | h32
  · subst h32
    have key : hostChart l ((sideData l t).point (u, 3 / 2)) =
        planarCollarFormula 3 l ((u : ℂ), (4 * (3 / 2) - 6) / 3) :=
      (σ.splitCharts SD hlin).hostChart_point_of_le t (by norm_num) (by norm_num)
    rw [hpt, hostChart_hostInv, show (4 * (3 / 2 : ℝ) - 6) / 3 = 0 by norm_num] at key
    set τ := (σ.crossMap j b).symm (u, ν) with hτ
    have hc : σ.crossMap j b τ = (u, ν) := (σ.crossMap j b).apply_symm_apply _
    have hglue := σ.cutMap_solidPt_three h SD τ
    rw [hc] at hglue
    obtain ⟨t', q', hq', hs', he'⟩ := σ.exists_lift_of_solidPt h SD hlin (z := (3 : ℝ) • (τ.1 : ℂ))
      (by rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by norm_num)]) τ.2
    refine ⟨t', q', hq', hs', ?_⟩
    rw [he', hglue, key]
  · set θ : Circle := (ν * (u ^ ((σ.splitCharts SD hlin).e₀ * (σ.splitCharts SD hlin).d))⁻¹) ^
      (σ.splitCharts SD hlin).e₁ with hθ
    set q : ℂ × Circle := (ρ • (θ : ℂ), u) with hqdef
    have hn : ‖q.1‖ = ρ := by
      change ‖ρ • (θ : ℂ)‖ = ρ
      rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by linarith)]
    have hu : unitOf q.1 = θ := unitOf_smul (by linarith) θ
    have hlev : σ.sideLevel h t q = stripLevel l (hostInv l z) := by
      unfold sideLevel
      rw [hn]
      change stripLevel l ((sideData l t).point (u, ρ)) = _
      rw [hpt]
    refine ⟨t, q, (σ.sideDom_iff h).mpr ⟨by rw [hn]; exact hρ.2, ?_⟩, by rw [hlev, ht], ?_⟩
    · rw [hlev, ht]
      linarith [abs_nonneg (stripLevel l (hostInv l z))]
    · rw [σ.liftMap_eq_cutMap]
      unfold liftPt
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hn]; linarith))]
      have e1 : hostChart (σ.hostSide h) ((sideData (σ.hostSide h) t).point (q.2, ‖q.1‖)) = z := by
        rw [hn]
        change hostChart l ((sideData l t).point (u, ρ)) = z
        rw [hpt, hostChart_hostInv]
      have e2 : σ.liftFib h SD hlin q = ν := by
        unfold liftFib
        rw [hu, hθ, zpow_zpow_unit he₁, mul_comm ν, mul_inv_cancel_left]
      rw [e1, e2]

theorem exists_solidPt_eq {y : σ.toTorus.cutCarrier.Carrier}
    (hy : y ∈ σ.toTorus.components.piece (σ.seamPiece j b)) :
    ∃ z : ℂ, ‖z‖ ≤ 3 ∧ ∃ w : Circle, σ.solidPt h SD z w = y := by
  obtain ⟨⟨x, w⟩, hx⟩ := (SD).ΘV.surjective ⟨y, hy⟩
  have hx3 : ‖(show discSet.{u} from x).val.down‖ ≤ 3 := (mem_discSet_iff _).mp x.2
  refine ⟨(show discSet.{u} from x).val.down, hx3, w, ?_⟩
  have hcl : clampDisc.{u} (show discSet.{u} from x).val.down = x := by
    apply Subtype.ext
    exact clampDisc_val hx3
  unfold solidPt
  rw [hcl]
  exact congrArg Subtype.val hx

theorem exists_hostPt_eq {y : σ.toTorus.cutCarrier.Carrier}
    (hy : y ∈ σ.toTorus.components.piece (σ.hostPiece j b)) :
    ∃ z : ℂ, z ∈ planarModel 3 ∧ ∃ ν : Circle, σ.hostPt h SD z ν = y := by
  obtain ⟨⟨x, ν⟩, hx⟩ := (SD).ΘH.surjective ⟨y, hy⟩
  have hx3 : (show planarSet.{u} 3 from x).val.down ∈ planarModel 3 :=
    (mem_planarSet_iff (Or.inr rfl) _).mp x.2
  refine ⟨(show planarSet.{u} 3 from x).val.down, hx3, ν, ?_⟩
  have hcl : clampPants.{u} (show planarSet.{u} 3 from x).val.down = x := by
    apply Subtype.ext
    exact clampPants_val hx3
  unfold hostPt
  rw [hcl]
  exact congrArg Subtype.val hx

theorem exists_lift_of_splitRegion {y : σ.toTorus.cutCarrier.Carrier}
    (hy : σ.InSplitRegion (j := j) (b := b) y) :
    ∃ t q, σ.sideDom h t q ∧ sgnR t * σ.sideLevel h t q = |σ.sideLevel h t q| ∧
      (σ.splitCharts SD hlin).liftMap t q = σ.toTorus.cutMap y := by
  rcases hy with hy | hy
  · obtain ⟨z, hz, w, rfl⟩ := σ.exists_solidPt_eq h SD hy
    exact σ.exists_lift_of_solidPt h SD hlin hz w
  · obtain ⟨z, hz, ν, rfl⟩ := σ.exists_hostPt_eq h SD hy
    exact σ.exists_lift_of_hostPt h SD hlin hz ν

end Lift

variable {Q : ConnectedClosedOrientedManifold.{u} 3} {σ : MixedStage Q}
  {j : Fin σ.toTorus.pairing.count} {b : Bool} {h : σ.IsSplitSeam j b} {SD : σ.SplitData h}
  {hlin : σ.IsLinearSeam j}
  {N : ClosedOrientedManifold.{u} 3}
  {K : SphericalCapping Q.toClosedOrientedManifold N (σ.splitSeamTube SD hlin)}

theorem coreMap_boundarySphere_eq_cap (c : (σ.splitSeamTube SD hlin).Boundary) (p : S2) :
    coreMap K ((σ.splitSeamTube SD hlin).boundarySphere c p) =
      K.cap c (sphereToClosedCell ((K.attaching c).symm p)) := by
  rw [K.boundary_eq c, Diffeomorph.apply_symm_apply,
    coreMap_of_mem K ((σ.splitSeamTube SD hlin).boundarySphere_mem_core c p)]
  rfl

namespace SideCap

variable {t : Bool} (S : σ.SideCap h SD hlin K t)

theorem exists_ball_eq_tube (z : S2) {r : ℝ} (h1 : 1 < r) (h2 : r < 5 / 2) :
    ∃ x : E3, ‖x‖ = r ∧
      S.Φ x = coreMap K ((σ.splitCharts SD hlin).tubeMap (z, sgnR t * r)) := by
  set C := σ.splitCharts SD hlin
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

theorem exists_solMap_eq_coreMap {q : ℂ × Circle} (hq : σ.sideDom h t q)
    (hpos : sgnR t * σ.sideLevel h t q = |σ.sideLevel h t q|)
    (hc : (σ.splitCharts SD hlin).liftMap t q ∈ (σ.splitSeamTube SD hlin).core) :
    ∃ q' : ℂ × Circle, ‖q'.1‖ ≤ 3 ∧
      S.solMap q' = coreMap K ((σ.splitCharts SD hlin).liftMap t q) := by
  have h1 := σ.one_le_abs_of_mem_core h SD hlin hq hc
  by_cases h2 : 2 < |σ.sideLevel h t q|
  · exact ⟨q, hq.1, S.solMap_of_real (by rw [hpos]; exact h2)⟩
  · push Not at h2
    obtain ⟨p, hp⟩ := σ.exists_tubeMap_eq_liftMap h SD hlin t hq (by linarith)
    have hL : σ.sideLevel h t q = sgnR t * |σ.sideLevel h t q| := by
      rw [← hpos, ← mul_assoc, sgnR_mul_self, one_mul]
    rw [← hp, hL]
    rcases eq_or_lt_of_le h1 with he | hlt
    · rw [← he, mul_one, ← (σ.splitCharts SD hlin).boundarySphere_eq ((), t) p]
      obtain ⟨q', hq', he'⟩ :=
        S.exists_solMap_eq_cap (sphereToClosedCell ((K.attaching ((), t)).symm p))
      exact ⟨q', hq', he'.trans (coreMap_boundarySphere_eq_cap ((), t) p).symm⟩
    · obtain ⟨x, hx, hxe⟩ := S.exists_ball_eq_tube p hlt (by linarith)
      obtain ⟨q', hq', he'⟩ := S.exists_solMap_eq_ball (x := x) (by rw [hx]; exact h2)
      exact ⟨q', hq', he'.trans hxe⟩

theorem solMap_image {q : ℂ × Circle} (hq : ‖q.1‖ ≤ 3) :
    (∃ w, S.solMap q = K.cap ((), t) w) ∨ ∃ y : σ.toTorus.cutCarrier.Carrier,
      σ.InSplitRegion (j := j) (b := b) y ∧
        σ.toTorus.cutMap y ∈ (σ.splitSeamTube SD hlin).core ∧
          S.solMap q = coreMap K (σ.toTorus.cutMap y) := by
  rcases S.solMap_cases hq with ⟨h3, h2, e⟩ | ⟨hd, h2, e⟩
  · rw [e]
    rcases S.fakeMap_cases h3 h2 with hcap | ⟨z, r, h1, hr2, hz⟩
    · exact Or.inl hcap
    · right
      have habs : |sgnR t * r| = r := abs_sgnR_mul_of_pos t (by linarith)
      obtain ⟨q', -, -, -, he'⟩ := σ.exists_liftMap_eq_tubeMap h SD hlin t z
        (lv := sgnR t * r) (by rw [habs]; linarith)
      refine ⟨σ.liftPt h SD hlin t q', σ.liftPt_mem_splitRegion h SD hlin t q', ?_, ?_⟩
      · rw [← σ.liftMap_eq_cutMap, he']
        exact (σ.splitCharts SD hlin).tubeMap_mem_core (q := (z, sgnR t * r))
          (by change 1 ≤ |sgnR t * r|; rw [habs]; linarith)
          (by change |sgnR t * r| < 3; rw [habs]; linarith)
      · rw [hz, ← σ.liftMap_eq_cutMap, he']
  · right
    refine ⟨σ.liftPt h SD hlin t q, σ.liftPt_mem_splitRegion h SD hlin t q, ?_, ?_⟩
    · rw [← σ.liftMap_eq_cutMap]
      exact liftMap_mem_core hd (one_lt_abs_sideLevel h2)
    · rw [e, σ.liftMap_eq_cutMap]

end SideCap

theorem exists_solMap_eq_of_splitRegion (S : ∀ t, σ.SideCap h SD hlin K t)
    {y : σ.toTorus.cutCarrier.Carrier} (hy : σ.InSplitRegion (j := j) (b := b) y)
    (hc : σ.toTorus.cutMap y ∈ (σ.splitSeamTube SD hlin).core) :
    ∃ t, ∃ q : ℂ × Circle, ‖q.1‖ ≤ 3 ∧ (S t).solMap q = coreMap K (σ.toTorus.cutMap y) := by
  obtain ⟨t, q, hq, hpos, he⟩ := σ.exists_lift_of_splitRegion h SD hlin hy
  rw [← he] at hc ⊢
  obtain ⟨q', hq', he'⟩ := (S t).exists_solMap_eq_coreMap hq hpos hc
  exact ⟨t, q', hq', he'⟩

end

end GC.Seifert.RelativeNormalization.MixedStage
