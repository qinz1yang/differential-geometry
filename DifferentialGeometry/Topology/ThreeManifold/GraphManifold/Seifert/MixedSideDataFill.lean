import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MixedSideDataTube
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelSolid

/-!
# The cap filling and the capped solid torus of one side of a mixed split

Lane N2f, tier 2. The texts of `MoveSplitCappedSideModelFill` and
`MoveSplitCappedSideModelSolid` for a mixed split site `(σ, h, SD)`: the fake region `fakeSet` is
open and preconnected, the ball filling `exists_capFill`, the chart data `SideCap` of one side and
the model map `solMap` (cap formula on the fake region, lift into the core elsewhere), which agree
near the level two (`fake_eq_real`).
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
  seamHeight_sqrt_three_half seamHeight_neg_sqrt_three_half exists_bandHeight_eq)

section

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} (h : σ.IsSplitSeam j b) (SD : σ.SplitData h)

theorem continuousOn_sideLevel (t : Bool) :
    ContinuousOn (σ.sideLevel h t) {q : ℂ × Circle | ‖q.1‖ ≤ 3} := by
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  refine (contDiff_stripLevel _).continuous.comp_continuousOn ?_
  exact (sideData (σ.hostSide h) t).continuousOn_point.comp
    (continuous_snd.prodMk hcn).continuousOn fun q hq => ⟨mem_univ _, norm_nonneg _, hq⟩

theorem three_lt_sideLevel_of_ge (t : Bool) {q : ℂ × Circle} (h1 : 5 / 2 ≤ ‖q.1‖)
    (h3 : ‖q.1‖ ≤ 3) : 3 < sgnR t * σ.sideLevel h t q :=
  three_lt_level_of_ge _ t h1 h3

def fakeSet (t : Bool) : Set (ℂ × Circle) :=
  {q | ‖q.1‖ < 3 ∧ sgnR t * σ.sideLevel h t q < 2}

theorem isOpen_fakeSet (t : Bool) : IsOpen (σ.fakeSet h t) := by
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  have hc : ContinuousOn (fun q : ℂ × Circle => sgnR t * σ.sideLevel h t q)
      {q | ‖q.1‖ < 3} :=
    (continuousOn_const.mul (σ.continuousOn_sideLevel h t)).mono fun q hq =>
      show ‖q.1‖ ≤ 3 from le_of_lt hq
  exact hc.isOpen_inter_preimage (isOpen_lt hcn continuous_const)
    (isOpen_lt continuous_id continuous_const)

theorem isPreconnected_fakeSet (t : Bool) : IsPreconnected (σ.fakeSet h t) := by
  set l := σ.hostSide h
  have hS := isPreconnected_levelPoints l t
  have himg : (fun x : Circle × (Circle × ℝ) => ((x.2.2 : ℝ) • (x.1 : ℂ), x.2.1)) ''
      (univ ×ˢ {p : Circle × ℝ | p.2 ∈ Icc (0 : ℝ) 3 ∧
        sgnR t * stripLevel l ((sideData l t).point p) < 2}) = σ.fakeSet h t := by
    ext q
    constructor
    · rintro ⟨⟨φ, ⟨u, ρ⟩⟩, ⟨-, hρ, hlev⟩, rfl⟩
      have hn : ‖(ρ • (φ : ℂ))‖ = ρ := by
        rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hρ.1]
      have hρ3 : ρ < 3 := by
        by_contra hc
        push Not at hc
        have := three_lt_level_of_ge l t (u := u) (by linarith) hρ.2
        dsimp only at hlev
        linarith
      refine ⟨by dsimp only; rw [hn]; exact hρ3, ?_⟩
      change sgnR t * stripLevel l ((sideData l t).point (u, ‖ρ • (φ : ℂ)‖)) < 2
      rw [hn]
      exact hlev
    · rintro ⟨hq3, hlev⟩
      refine ⟨(unitOf q.1, (q.2, ‖q.1‖)), ⟨mem_univ _, ⟨norm_nonneg _, hq3.le⟩, hlev⟩, ?_⟩
      exact Prod.ext (norm_smul_unitOf q.1) rfl
  rw [← himg]
  refine (isPreconnected_univ.prod hS).image _ (Continuous.continuousOn ?_)
  exact ((continuous_snd.comp continuous_snd).smul
    (continuous_subtype_val.comp continuous_fst)).prodMk (continuous_fst.comp continuous_snd)

section Lift

variable (hlin : σ.IsLinearSeam j)

theorem exists_capFill (t : Bool) :
    ∃ G : E3 ≃ₘ[ℝ] E3,
      (∀ q : ℂ × Circle, ‖q.1‖ < 3 → sgnR t * σ.sideLevel h t q ≤ 2 →
        ‖G.symm (torusPD q)‖ ≤ 1) ∧
      (∀ x : E3, ‖x‖ ≤ 1 → ∃ q : ℂ × Circle, ‖q.1‖ < 3 ∧ sgnR t * σ.sideLevel h t q ≤ 2 ∧
        G x = torusPD q) ∧
      ∃ V : Set E3, IsOpen V ∧ sphere (0 : E3) 1 ⊆ V ∧ V ⊆ shellSet ∧
        ∀ x ∈ V, G x = σ.shellMap h SD hlin t x := by
  obtain ⟨F, hFs, hF⟩ := σ.exists_shellPD h SD hlin t
  set D := σ.fakeSet h t with hD
  set U := torusPD '' D with hU
  have hDsrc : D ⊆ torusPD.source := fun q hq => show ‖q.1‖ < 4 by linarith [hq.1]
  have hUo : IsOpen U := torusPD.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (σ.isOpen_fakeSet h t) hDsrc
  have hUb : Bornology.IsBounded U := (isBounded_closedBall (x := (0 : E3)) (r := 10)).subset
    (by rintro _ ⟨q, hq, rfl⟩; exact mem_closedBall_zero_iff.mpr (norm_torusPD_le hq.1.le))
  have hUc : IsPreconnected U := (σ.isPreconnected_fakeSet h t).image _
    (torusPD.toOpenPartialHomeomorph.continuousOn.mono hDsrc)
  set Dc : Set (ℂ × Circle) := {q | ‖q.1‖ ≤ 3 ∧ sgnR t * σ.sideLevel h t q ≤ 2} with hDc
  have hDc_lt : ∀ q ∈ Dc, ‖q.1‖ < 3 := by
    intro q hq
    by_contra hc
    push Not at hc
    linarith [σ.three_lt_sideLevel_of_ge h t (q := q) (by linarith) hq.1, hq.2]
  have hDc_closed : IsClosed Dc :=
    (continuousOn_const.mul (σ.continuousOn_sideLevel h t)).preimage_isClosed_of_isClosed
      (isClosed_le (continuous_norm.comp continuous_fst) continuous_const) isClosed_Iic
  have hDc_compact : IsCompact Dc :=
    ((isCompact_closedBall (0 : ℂ) 3).prod isCompact_univ).of_isClosed_subset hDc_closed
      fun q hq => ⟨mem_closedBall_zero_iff.mpr hq.1, mem_univ _⟩
  have hDcsrc : Dc ⊆ torusPD.source := fun q hq => show ‖q.1‖ < 4 by linarith [hq.1]
  have hcl : closure U ⊆ torusPD '' Dc := closure_minimal
    (image_mono fun q hq => ⟨hq.1.le, hq.2.le⟩)
    (hDc_compact.image_of_continuousOn
      (torusPD.toOpenPartialHomeomorph.continuousOn.mono hDcsrc)).isClosed
  have hinj : ∀ q ∈ Dc, ∀ q' : ℂ × Circle, ‖q'.1‖ < 3 → torusPD q = torusPD q' → q = q' :=
    fun q hq q' hq' he => torusPD_injOn (show ‖q.1‖ < 4 by linarith [hq.1])
      (show ‖q'.1‖ < 4 by linarith) he
  have hshell : ∀ x ∈ shellSet, ∃ q ∈ σ.liftDom h t, F x = torusPD q ∧
      sgnR t * σ.sideLevel h t q = 2 * ‖x‖ := by
    intro x hx
    obtain ⟨h1, -, h3⟩ := σ.shellMap_spec h SD hlin t hx
    exact ⟨_, h1, hF x, h3⟩
  have hin : ∀ x ∈ F.source, ‖x‖ < 1 → F x ∈ U := by
    intro x hx hx1
    rw [show F.source = shellSet from hFs] at hx
    obtain ⟨q, hq, hFq, hlev⟩ := hshell x hx
    exact ⟨q, ⟨hq.1, by rw [hlev]; linarith⟩, hFq.symm⟩
  have hout : ∀ x ∈ F.source, 1 < ‖x‖ → F x ∉ closure U := by
    intro x hx hx1 hmem
    rw [show F.source = shellSet from hFs] at hx
    obtain ⟨q, hq, hFq, hlev⟩ := hshell x hx
    obtain ⟨q', hq', he⟩ := hcl hmem
    rw [hFq] at he
    have := hinj q' hq' q hq.1 he
    rw [← this] at hlev
    linarith [hq'.2]
  have hlevel2 : ∀ q : ℂ × Circle, ‖q.1‖ < 3 → sgnR t * σ.sideLevel h t q = 2 →
      torusPD q ∈ F '' sphere (0 : E3) 1 := by
    intro q hq3 hq2
    have hL : σ.sideLevel h t q = 2 * sgnR t := by
      have := sgnR_mul_self t
      linear_combination sgnR t * hq2 - σ.sideLevel h t q * this
    have hlev3 : |σ.sideLevel h t q| < 3 := by
      rw [hL, mul_comm, SplitCharts.abs_sgnR_mul]
      norm_num
    have hqd : q ∈ σ.liftDom h t := ⟨hq3, by rw [hq2]; norm_num⟩
    obtain ⟨p, hp⟩ := σ.exists_tubeMap_eq_liftMap h SD hlin t (σ.sideDom_of_mem_liftDom h hqd) hlev3
    have hpn : ‖(p : E3)‖ = 1 := norm_eq_of_mem_sphere p
    have hdir : shellDir t (p : E3) = (p, σ.sideLevel h t q) := by
      refine Prod.ext ?_ ?_
      · change Manifold.sphereDirection poleS2 (p : E3) = p
        have := Manifold.sphereDirection_pos_smul poleS2 p one_pos
        rwa [one_smul] at this
      · change 2 * sgnR t * ‖(p : E3)‖ = _
        rw [hpn, hL]
        ring
    refine ⟨(p : E3), p.2, ?_⟩
    rw [hF, shellMap, hdir, hp, σ.liftInv_liftMap h SD hlin hqd]
  have hfront : frontier U = F '' sphere (0 : E3) 1 := by
    apply Subset.antisymm
    · intro y hy
      rw [hUo.frontier_eq] at hy
      obtain ⟨q, hq, rfl⟩ := hcl hy.1
      have h2 : sgnR t * σ.sideLevel h t q = 2 :=
        le_antisymm hq.2 (not_lt.mp fun hlt => hy.2 ⟨q, ⟨hDc_lt q hq, hlt⟩, rfl⟩)
      exact hlevel2 q (hDc_lt q hq) h2
    · rintro _ ⟨x, hx, rfl⟩
      have hxs : x ∈ shellSet := sphere_subset_shellSet hx
      have hxn : ‖x‖ = 1 := norm_eq_of_mem_sphere ⟨x, hx⟩
      rw [hUo.frontier_eq]
      refine ⟨?_, ?_⟩
      · have hc1 : ContinuousAt F x :=
          F.toOpenPartialHomeomorph.continuousAt (show x ∈ F.source by rw [hFs]; exact hxs)
        have hc : ContinuousAt (fun s : ℝ => F (s • x)) 1 :=
          hc1.comp_of_eq (continuous_id.smul continuous_const).continuousAt (one_smul ℝ x)
        have ht : Tendsto (fun s : ℝ => F (s • x)) (𝓝[<] (1 : ℝ)) (𝓝 (F x)) := by
          have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
          rwa [one_smul] at this
        refine mem_closure_of_tendsto ht ?_
        · have hI : Ioo (3 / 4 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
          filter_upwards [hI] with s hs
          have hsn : ‖s • x‖ = s := by
            rw [norm_smul, hxn, mul_one, Real.norm_of_nonneg (by linarith [hs.1])]
          exact hin _ (by rw [hFs]; exact ⟨by rw [hsn]; exact hs.1, by rw [hsn]; linarith [hs.2]⟩)
            (by rw [hsn]; exact hs.2)
      · rintro ⟨q', hq', he⟩
        obtain ⟨q, hq, hFq, hlev⟩ := hshell x hxs
        rw [hFq] at he
        have := hinj q ⟨hq.1.le, by rw [hlev, hxn]; norm_num⟩ q' hq'.1 he.symm
        rw [this, hxn] at hlev
        linarith [hq'.2]
  obtain ⟨G, -, hGcb, V, hV, hSV, hVs, hGV⟩ := exists_ballFill_of_shell F
    (by rw [hFs]; exact sphere_subset_shellSet) hUo hUb hUc hfront hin hout
  refine ⟨G, ?_, ?_, V, hV, hSV, by rwa [hFs] at hVs, fun x hx => (hGV hx).trans (hF x)⟩
  · intro q hq3 hq2
    have hmem : torusPD q ∈ closure U := by
      rcases lt_or_eq_of_le hq2 with hlt | heq
      · exact subset_closure ⟨q, ⟨hq3, hlt⟩, rfl⟩
      · have := hlevel2 q hq3 heq
        rw [← hfront] at this
        exact frontier_subset_closure this
    rw [← hGcb] at hmem
    obtain ⟨x, hx, hxe⟩ := hmem
    rw [← hxe, G.symm_apply_apply]
    exact mem_closedBall_zero_iff.mp hx
  · intro x hx
    have : G x ∈ closure U := hGcb ▸ ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
    obtain ⟨q, hq, hqe⟩ := hcl this
    exact ⟨q, hDc_lt q hq, hq.2, hqe.symm⟩

end Lift

end

section

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  {j : Fin σ.toTorus.pairing.count} {b : Bool} (h : σ.IsSplitSeam j b) (SD : σ.SplitData h)
  (hlin : σ.IsLinearSeam j)
  {N : ClosedOrientedManifold.{u} 3}
  (K : SphericalCapping Q.toClosedOrientedManifold N (σ.splitSeamTube SD hlin))

structure SideCap (t : Bool) where
  r : ℝ
  r_pos : 0 < r
  r_le : r ≤ 1 / 2
  Φ : E3 → N.Carrier
  loc : ∀ x : E3, ‖x‖ < 5 / 2 → IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ Φ x
  inj : InjOn Φ (ball 0 (5 / 2))
  cap_in : ∀ x : E3, ‖x‖ ≤ 1 → ∃ w : ClosedCell 3, Φ x = K.cap ((), t) w
  cap_surj : ∀ w : ClosedCell 3, ∃ x : E3, ‖x‖ ≤ 1 ∧ Φ x = K.cap ((), t) w
  shell : ∀ x : E3, 1 ≤ ‖x‖ → ‖x‖ < 5 / 2 →
    ∃ z : S2, Φ x = coreMap K ((σ.splitCharts SD hlin).tubeMap (z, sgnR t * ‖x‖))
  shell' : ∀ x : E3, 1 + r / 2 ≤ ‖x‖ → ‖x‖ < 5 / 2 →
    Φ x = coreMap K ((σ.splitCharts SD hlin).tubeMap
      (Manifold.sphereDirection poleS2 x, sgnR t * ‖x‖))
  G : E3 ≃ₘ[ℝ] E3
  G_ball : ∀ q : ℂ × Circle, ‖q.1‖ < 3 → sgnR t * σ.sideLevel h t q ≤ 2 →
    ‖G.symm (torusPD q)‖ ≤ 1
  G_onto : ∀ x : E3, ‖x‖ ≤ 1 → ∃ q : ℂ × Circle, ‖q.1‖ < 3 ∧
    sgnR t * σ.sideLevel h t q ≤ 2 ∧ G x = torusPD q
  V : Set E3
  V_open : IsOpen V
  V_sphere : sphere (0 : E3) 1 ⊆ V
  V_shell : V ⊆ shellSet
  G_shell : ∀ x ∈ V, G x = σ.shellMap h SD hlin t x

theorem nonempty_sideCap (t : Bool) : Nonempty (σ.SideCap h SD hlin K t) := by
  obtain ⟨r, hr, hr2, Φ, hloc, hinj, hin, hsurj, hsh, hsh'⟩ :=
    (σ.splitCharts SD hlin).exists_sideBall K t
  obtain ⟨G, hG1, hG2, V, hV, hSV, hVs, hGV⟩ := σ.exists_capFill h SD hlin t
  exact ⟨⟨r, hr, hr2, Φ, hloc, hinj, hin, hsurj, hsh, hsh', G, hG1, hG2, V, hV, hSV, hVs, hGV⟩⟩

variable {σ h SD hlin K}

theorem liftMap_ne_tubeMap {t : Bool} {q : ℂ × Circle} (hq : σ.sideDom h t q)
    {z : S2} {lv : ℝ} (hlv : |lv| < 3) (hne : σ.sideLevel h t q ≠ lv) :
    (σ.splitCharts SD hlin).liftMap t q ≠ (σ.splitCharts SD hlin).tubeMap (z, lv) := by
  intro he
  obtain ⟨q', hq', -, hlev, he'⟩ := σ.exists_liftMap_eq_tubeMap h SD hlin t z hlv
  rw [← he'] at he
  have := σ.liftMap_injOn h SD hlin t hq hq' he
  rw [this] at hne
  exact hne hlev

theorem liftMap_mem_core {t : Bool} {q : ℂ × Circle} (hq : σ.sideDom h t q)
    (hlev : 1 < |σ.sideLevel h t q|) :
    (σ.splitCharts SD hlin).liftMap t q ∈ (σ.splitSeamTube SD hlin).core := by
  intro hmem
  simp only [mem_iUnion, SphericalTubeSystem.removedBand, mem_image] at hmem
  obtain ⟨a, y, hy, he⟩ := hmem
  have he' : (σ.splitCharts SD hlin).tubeMap (y.1, y.2.val) =
      (σ.splitCharts SD hlin).liftMap t q := he
  have hy1 : |y.2.val| < 1 := abs_lt.mpr ⟨hy.1, hy.2⟩
  refine liftMap_ne_tubeMap hq (by linarith) ?_ he'.symm
  intro h0
  rw [h0] at hlev
  linarith

theorem liftMap_ne_boundarySphere {t : Bool} {q : ℂ × Circle} (hq : σ.sideDom h t q)
    (hlev : 1 < |σ.sideLevel h t q|) (c : (σ.splitSeamTube SD hlin).Boundary) (z : S2) :
    (σ.splitSeamTube SD hlin).boundarySphere c z ≠ (σ.splitCharts SD hlin).liftMap t q := by
  rw [show (σ.splitSeamTube SD hlin).boundarySphere c z =
    (σ.splitCharts SD hlin).tubeMap (z, sgnR c.2) from
      (σ.splitCharts SD hlin).boundarySphere_eq c z]
  have hs : |sgnR c.2| = 1 := by rcases sgnR_eq c.2 with e | e <;> rw [e] <;> norm_num
  refine (liftMap_ne_tubeMap hq (by rw [hs]; norm_num) ?_).symm
  intro h0
  rw [h0, hs] at hlev
  exact lt_irrefl _ hlev

theorem isLocalDiffeomorphAt_coreMap_liftMap {t : Bool} {q : ℂ × Circle}
    (hq : q ∈ σ.liftDom h t) (hlev : 1 < |σ.sideLevel h t q|) :
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞
      (coreMap K ∘ (σ.splitCharts SD hlin).liftMap t) q := by
  have hd := σ.sideDom_of_mem_liftDom h hq
  exact (σ.isLocalDiffeomorphAt_liftMap_of_mem h SD hlin hq).comp (𝓡 3) N.Carrier
    (isLocalDiffeomorphAt_coreMap K ⟨_, liftMap_mem_core hd hlev⟩
      (isInteriorPoint_of_forall_ne K _ fun c z => liftMap_ne_boundarySphere hd hlev c z))

namespace SideCap

variable {t : Bool} (S : σ.SideCap h SD hlin K t)

def solMap (q : ℂ × Circle) : N.Carrier :=
  if ‖q.1‖ < 3 ∧ sgnR t * σ.sideLevel h t q ≤ 2 then S.Φ ((2 : ℝ) • S.G.symm (torusPD q))
  else coreMap K ((σ.splitCharts SD hlin).liftMap t q)

theorem solMap_of_fake {q : ℂ × Circle} (h3 : ‖q.1‖ < 3) (h2 : sgnR t * σ.sideLevel h t q ≤ 2) :
    S.solMap q = S.Φ ((2 : ℝ) • S.G.symm (torusPD q)) :=
  ite_eq_left_of_eq_true _ _ (eq_true ⟨h3, h2⟩)

theorem solMap_of_real {q : ℂ × Circle} (h2 : 2 < sgnR t * σ.sideLevel h t q) :
    S.solMap q = coreMap K ((σ.splitCharts SD hlin).liftMap t q) :=
  ite_eq_right_of_eq_false _ _ (eq_false fun hc => absurd hc.2 (not_le.mpr h2))

theorem norm_two_smul_le {q : ℂ × Circle} (h3 : ‖q.1‖ < 3) (h2 : sgnR t * σ.sideLevel h t q ≤ 2) :
    ‖(2 : ℝ) • S.G.symm (torusPD q)‖ ≤ 2 := by
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have := S.G_ball q h3 h2
  linarith

theorem fake_eq_real {q : ℂ × Circle} (h3 : ‖q.1‖ < 3) (hV : S.G.symm (torusPD q) ∈ S.V) :
    S.Φ ((2 : ℝ) • S.G.symm (torusPD q)) = coreMap K ((σ.splitCharts SD hlin).liftMap t q) := by
  set x := S.G.symm (torusPD q) with hx
  have hxs := S.V_shell hV
  obtain ⟨h1, h2, -⟩ := σ.shellMap_spec h SD hlin t hxs
  have hGx : S.G x = torusPD q := S.G.apply_symm_apply _
  rw [S.G_shell x hV] at hGx
  have hq : σ.liftInv h SD hlin t ((σ.splitCharts SD hlin).tubeMap (shellDir t x)) = q :=
    torusPD_injOn (show ‖_‖ < 4 by linarith [h1.1]) (show ‖q.1‖ < 4 by linarith) hGx
  rw [hq] at h2
  rw [h2]
  have hx0 : x ≠ 0 := fun h0 => by have := hxs.1; rw [h0, norm_zero] at this; linarith
  have hn : ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have r2 := S.r_le
  rw [S.shell' _ (by rw [hn]; linarith [hxs.1]) (by rw [hn]; linarith [hxs.2])]
  congr 2
  refine Prod.ext ?_ ?_
  · change Manifold.sphereDirection poleS2 ((2 : ℝ) • x) = Manifold.sphereDirection poleS2 x
    conv_lhs => rw [← Manifold.norm_smul_sphereDirection poleS2 hx0, smul_smul]
    exact Manifold.sphereDirection_pos_smul poleS2 _ (by positivity)
  · change sgnR t * ‖(2 : ℝ) • x‖ = 2 * sgnR t * ‖x‖
    rw [hn]
    ring

end SideCap

end

end GC.Seifert.RelativeNormalization.MixedStage
