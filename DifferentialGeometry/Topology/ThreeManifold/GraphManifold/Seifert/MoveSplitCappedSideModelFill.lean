import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSideModelShell

/-!
# Filling the fake region by a ball

Lane N2d, side model, step 4 (fill). The fake region `D t` of the model solid torus (level
`sgnR(t) · level < 2`) is open and preconnected: in the plane of the nested circles it is the part
of a disc on one side of a graph over the imaginary axis (`isPreconnected_levelDisc`), and the
nested parametrisation is an embedding on the compact annulus. Its image in `ℝ³` under the torus of
revolution has the image of the unit sphere under the shell diffeomorphism as frontier, so the
ball filling `exists_ballFill_of_shell` gives a diffeomorphism `G` of `ℝ³` carrying the closed unit
ball onto the closure of the fake region and agreeing with the shell map near the unit sphere
(`exists_capFill`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace GC.Seifert.SplitTube

theorem le_norm_sub_of_level (l : Fin 3) (t : Bool) {w : ℂ} (hw : sgnR t * stripLevel l w < 3) :
    (sideData l t).famR 3 ≤ ‖w - (sideData l t).famC 3‖ := by
  by_contra hc
  push Not at hc
  by_cases hw0 : l.val ≠ 0 → w ≠ 0
  · linarith [three_lt_of_inside_port l t hw0 hc.le]
  · push Not at hw0
    obtain ⟨hl, rfl⟩ := hw0
    have hO : IsOpen {z : ℂ | ‖z - (sideData l t).famC 3‖ < (sideData l t).famR 3 ∧
        sgnR t * stripLevel l z < 3} :=
      (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).inter
        (isOpen_lt (continuous_const.mul (contDiff_stripLevel l).continuous) continuous_const)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hO 0 ⟨hc, hw⟩
    have hz : ((δ / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) δ := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    have hm := hball hz
    have hz0 : ((δ / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]
      linarith
    linarith [three_lt_of_inside_port l t (fun _ => hz0) hm.1.le, hm.2]

theorem three_lt_level_of_ge (l : Fin 3) (t : Bool) {u : Circle} {ρ : ℝ} (h : 5 / 2 ≤ ρ)
    (h3 : ρ ≤ 3) : 3 < sgnR t * stripLevel l ((sideData l t).point (u, ρ)) := by
  rw [sideData_point_collar l t h (by linarith)]
  refine (lt_sgnR_mul_stripLevel l t ?_).2
  exact planarCollarFormula_mem_outerCollarRegion _ _ (by unfold collarDepth; linarith)
    (by unfold collarDepth; linarith)

def levelDisc (l : Fin 3) (t : Bool) : Set ℂ :=
  {w | ‖w‖ ≤ vRadius l 0 ∧ sgnR t * stripLevel l w < 2}

def levelArc (l : Fin 3) (t : Bool) (Y : ℝ) : ℂ :=
  ((sgnR t * Real.sqrt (vRadius l 0 ^ 2 - Y ^ 2) : ℝ) : ℂ) + Y • Complex.I

theorem levelArc_re (l : Fin 3) (t : Bool) (Y : ℝ) :
    (levelArc l t Y).re = sgnR t * Real.sqrt (vRadius l 0 ^ 2 - Y ^ 2) := by
  simp [levelArc]

theorem levelArc_im (l : Fin 3) (t : Bool) (Y : ℝ) : (levelArc l t Y).im = Y := by
  simp [levelArc]

theorem stripLevel_affine (l : Fin 3) {w w' : ℂ} (him : w.im = w'.im) {a c : ℝ}
    (hac : a + c = 1) :
    stripLevel l (a • w + c • w') = a * stripLevel l w + c * stripLevel l w' := by
  have him' : (a • w + c • w').im = w.im := by
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rw [← him]
    linear_combination w.im * hac
  have hre : (a • w + c • w').re = a * w.re + c * w'.re := by
    simp [Complex.real_smul]
  rw [stripLevel_eq, stripLevel_eq, stripLevel_eq, him', hre, ← him, mul_div_assoc',
    mul_div_assoc', ← add_div]
  congr 1
  linear_combination (-(stripCenter l * stripBump w.im)) * hac

theorem levelArc_mem (l : Fin 3) (t : Bool) {Y : ℝ} (hY : |Y| ≤ vRadius l 0) :
    levelArc l t Y ∈ levelDisc l t := by
  have hR := two_le_vRadius l (le_refl 0) (by norm_num)
  have hY2 : Y ^ 2 ≤ vRadius l 0 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg Y) hY 2
  have hs := Real.sq_sqrt (show 0 ≤ vRadius l 0 ^ 2 - Y ^ 2 by linarith)
  refine ⟨?_, ?_⟩
  · have e : ‖levelArc l t Y‖ ^ 2 = vRadius l 0 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, levelArc_re, levelArc_im]
      have := sgnR_mul_self t
      nlinarith
    have := (pow_left_inj₀ (norm_nonneg _) (by linarith) two_ne_zero).mp e
    linarith
  · rw [stripLevel_eq, levelArc_re, levelArc_im]
    have hW := stripWidth_pos Y
    have hden : 0 < tubeSlope * stripWidth Y := mul_pos (by norm_num [tubeSlope]) hW
    have key :
        sgnR t * (stripCenter l * stripBump Y) - Real.sqrt (vRadius l 0 ^ 2 - Y ^ 2) ≤ 0 := by
      by_cases h1 : 1 ≤ |Y|
      · rw [stripBump_of_one_le h1]
        simp only [mul_zero, zero_sub, neg_nonpos]
        exact Real.sqrt_nonneg _
      · push Not at h1
        have hc := abs_stripCenter_le l
        have hB0 := stripBump_nonneg Y
        have hB1 := stripBump_le_one Y
        have hcb : sgnR t * (stripCenter l * stripBump Y) ≤ 1 / 4 := by
          have : |sgnR t * (stripCenter l * stripBump Y)| ≤ 1 / 4 := by
            rw [SplitCharts.abs_sgnR_mul, abs_mul, abs_of_nonneg hB0]
            nlinarith [abs_nonneg (stripCenter l)]
          exact (abs_le.mp this).2
        have hY1 : Y ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg Y]
        have hsq : 1 / 4 ≤ Real.sqrt (vRadius l 0 ^ 2 - Y ^ 2) := by
          rw [show (1 / 4 : ℝ) = Real.sqrt ((1 / 4) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by nlinarith)
        linarith
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    have := sgnR_mul_self t
    have e : sgnR t * (stripCenter l * stripBump Y - sgnR t * Real.sqrt (vRadius l 0 ^ 2 - Y ^ 2)) =
        sgnR t * (stripCenter l * stripBump Y) - Real.sqrt (vRadius l 0 ^ 2 - Y ^ 2) := by
      linear_combination (-Real.sqrt (vRadius l 0 ^ 2 - Y ^ 2)) * this
    rw [e]
    linarith

theorem isPreconnected_levelDisc (l : Fin 3) (t : Bool) : IsPreconnected (levelDisc l t) := by
  set R := vRadius l 0 with hRdef
  have hR := two_le_vRadius l (le_refl 0) (by norm_num)
  set Γ := levelArc l t '' Icc (-R) R with hΓ
  have hcont : Continuous (levelArc l t) := by
    unfold levelArc
    fun_prop
  have hΓc : IsPreconnected Γ := isPreconnected_Icc.image _ hcont.continuousOn
  have hΓs : Γ ⊆ levelDisc l t := by
    rintro _ ⟨Y, hY, rfl⟩
    exact levelArc_mem l t (abs_le.mpr ⟨hY.1, hY.2⟩)
  have h0 : levelArc l t 0 ∈ levelDisc l t := levelArc_mem l t (by rw [abs_zero]; linarith)
  refine isPreconnected_of_forall (levelArc l t 0) fun w hw => ?_
  have hY : |w.im| ≤ R := (Complex.abs_im_le_norm w).trans hw.1
  set w' := levelArc l t w.im with hw'
  have hw'm := levelArc_mem l t hY
  have hseg : segment ℝ w w' ⊆ levelDisc l t := by
    rintro z ⟨a, c, ha, hc, hac, rfl⟩
    refine ⟨?_, ?_⟩
    · calc ‖a • w + c • w'‖ ≤ a * ‖w‖ + c * ‖w'‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hc]
        _ ≤ a * R + c * R := by
            have := hw'm.1
            have := hw.1
            nlinarith
        _ = R := by rw [← add_mul, hac, one_mul]
    · rw [stripLevel_affine l (by rw [hw', levelArc_im]) hac]
      have hx : sgnR t * stripLevel l w < 2 := hw.2
      have hy : sgnR t * stripLevel l w' < 2 := hw'm.2
      have e : sgnR t * (a * stripLevel l w + c * stripLevel l w') =
          a * (sgnR t * stripLevel l w) + c * (sgnR t * stripLevel l w') := by ring
      rw [e]
      rcases eq_or_lt_of_le ha with h0 | hpos
      · rw [← h0] at hac ⊢
        rw [zero_add] at hac
        rw [hac]
        linarith
      · nlinarith [mul_lt_mul_of_pos_left hx hpos, mul_le_mul_of_nonneg_left hy.le hc]
  refine ⟨segment ℝ w w' ∪ Γ, union_subset hseg hΓs, Or.inr ⟨0, ⟨by linarith, by linarith⟩, rfl⟩,
    Or.inl (left_mem_segment ℝ w w'), ?_⟩
  exact (convex_segment w w').isPreconnected.union w' (right_mem_segment ℝ w w')
    ⟨w.im, ⟨(abs_le.mp hY).1, (abs_le.mp hY).2⟩, rfl⟩ hΓc

theorem isPreconnected_levelPoints (l : Fin 3) (t : Bool) :
    IsPreconnected {p : Circle × ℝ | p.2 ∈ Icc (0 : ℝ) 3 ∧
      sgnR t * stripLevel l ((sideData l t).point p) < 2} := by
  set K : Set (Circle × ℝ) := univ ×ˢ Icc (0 : ℝ) 3 with hK
  have hKc : IsCompact K := isCompact_univ.prod isCompact_Icc
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let P : K → ℂ := fun k => (sideData l t).point k.val
  have hPc : Continuous P := (sideData l t).continuousOn_point.domRestrict
  have hPi : Injective P := fun k k' he => Subtype.ext ((sideData l t).point_injOn k.2 k'.2 he)
  have hemb : Topology.IsClosedEmbedding P := hPc.isClosedEmbedding hPi
  set S' : Set K := {k | sgnR t * stripLevel l (P k) < 2} with hS'
  have h0 : (sideData l t).famC 0 = 0 := (sideData l t).famC_of_le (by norm_num)
  have hr0 : (sideData l t).famR 0 = vRadius l 0 := by
    rw [(sideData l t).famR_of_le (by norm_num), mul_zero]
  have himg : P '' S' = levelDisc l t := by
    ext w
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, hk⟩
      have := (nestedPoint_mem (μ := (sideData l t).famMu) (a := (sideData l t).famA)
        (sideData l t).nestedOn_fam (fun _ hρ => ((sideData l t).famR_pos hρ).le) k.2.2).1
      rw [h0, hr0, sub_zero] at this
      exact this
    · rintro ⟨hw1, hw2⟩
      have h3 := le_norm_sub_of_level l t (by linarith : sgnR t * stripLevel l w < 3)
      have hw0 : ‖w - (sideData l t).famC 0‖ ≤ (sideData l t).famR 0 := by
        rw [h0, hr0, sub_zero]
        exact hw1
      obtain ⟨p, hp, hpe⟩ := exists_nestedPoint_eq (μ := (sideData l t).famMu)
        (a := (sideData l t).famA) (sideData l t).continuousOn_famC
        (sideData l t).continuousOn_famR (fun _ hρ => (sideData l t).famR_pos hρ)
        (fun _ hρ => (sideData l t).famA_lt' hρ) hw0 h3
      refine ⟨⟨p, ⟨mem_univ _, hp⟩⟩, ?_, hpe⟩
      change sgnR t * stripLevel l ((sideData l t).point p) < 2
      change (sideData l t).point p = w at hpe
      rw [hpe]
      exact hw2
  have hS'c : IsPreconnected S' := by
    rw [← hemb.isInducing.isPreconnected_image, himg]
    exact isPreconnected_levelDisc l t
  have := hS'c.image Subtype.val continuous_subtype_val.continuousOn
  convert this using 1
  ext p
  constructor
  · rintro ⟨hp, hl⟩
    exact ⟨⟨p, ⟨mem_univ _, hp⟩⟩, hl, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2.2, hk⟩

end GC.Seifert.SplitTube

namespace GC.Seifert.ElementaryPresentation

open SplitTube

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (E : ElementaryPresentation (NoCuts.carrier Q))
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)

theorem continuousOn_sideLevel (t : Bool) :
    ContinuousOn (E.sideLevel h t) {q : ℂ × Circle | ‖q.1‖ ≤ 3} := by
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  refine (contDiff_stripLevel _).continuous.comp_continuousOn ?_
  exact (sideData (E.hostSide h) t).continuousOn_point.comp
    (continuous_snd.prodMk hcn).continuousOn fun q hq => ⟨mem_univ _, norm_nonneg _, hq⟩

theorem three_lt_sideLevel_of_ge (t : Bool) {q : ℂ × Circle} (h1 : 5 / 2 ≤ ‖q.1‖)
    (h3 : ‖q.1‖ ≤ 3) : 3 < sgnR t * E.sideLevel h t q :=
  three_lt_level_of_ge _ t h1 h3

def fakeSet (t : Bool) : Set (ℂ × Circle) :=
  {q | ‖q.1‖ < 3 ∧ sgnR t * E.sideLevel h t q < 2}

theorem isOpen_fakeSet (t : Bool) : IsOpen (E.fakeSet h t) := by
  have hcn : Continuous fun q : ℂ × Circle => ‖q.1‖ := continuous_norm.comp continuous_fst
  have hc : ContinuousOn (fun q : ℂ × Circle => sgnR t * E.sideLevel h t q)
      {q | ‖q.1‖ < 3} :=
    (continuousOn_const.mul (E.continuousOn_sideLevel h t)).mono fun q hq =>
      show ‖q.1‖ ≤ 3 from le_of_lt hq
  exact hc.isOpen_inter_preimage (isOpen_lt hcn continuous_const)
    (isOpen_lt continuous_id continuous_const)

theorem isPreconnected_fakeSet (t : Bool) : IsPreconnected (E.fakeSet h t) := by
  set l := E.hostSide h
  have hS := isPreconnected_levelPoints l t
  have himg : (fun x : Circle × (Circle × ℝ) => ((x.2.2 : ℝ) • (x.1 : ℂ), x.2.1)) ''
      (univ ×ˢ {p : Circle × ℝ | p.2 ∈ Icc (0 : ℝ) 3 ∧
        sgnR t * stripLevel l ((sideData l t).point p) < 2}) = E.fakeSet h t := by
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

variable (hlin : E.IsLinearSeam j)

theorem exists_capFill (t : Bool) :
    ∃ G : E3 ≃ₘ[ℝ] E3,
      (∀ q : ℂ × Circle, ‖q.1‖ < 3 → sgnR t * E.sideLevel h t q ≤ 2 →
        ‖G.symm (torusPD q)‖ ≤ 1) ∧
      (∀ x : E3, ‖x‖ ≤ 1 → ∃ q : ℂ × Circle, ‖q.1‖ < 3 ∧ sgnR t * E.sideLevel h t q ≤ 2 ∧
        G x = torusPD q) ∧
      ∃ V : Set E3, IsOpen V ∧ sphere (0 : E3) 1 ⊆ V ∧ V ⊆ shellSet ∧
        ∀ x ∈ V, G x = E.shellMap h hlin t x := by
  obtain ⟨F, hFs, hF⟩ := E.exists_shellPD h hlin t
  set D := E.fakeSet h t with hD
  set U := torusPD '' D with hU
  have hDsrc : D ⊆ torusPD.source := fun q hq => show ‖q.1‖ < 4 by linarith [hq.1]
  have hUo : IsOpen U := torusPD.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (E.isOpen_fakeSet h t) hDsrc
  have hUb : Bornology.IsBounded U := (isBounded_closedBall (x := (0 : E3)) (r := 10)).subset
    (by rintro _ ⟨q, hq, rfl⟩; exact mem_closedBall_zero_iff.mpr (norm_torusPD_le hq.1.le))
  have hUc : IsPreconnected U := (E.isPreconnected_fakeSet h t).image _
    (torusPD.toOpenPartialHomeomorph.continuousOn.mono hDsrc)
  set Dc : Set (ℂ × Circle) := {q | ‖q.1‖ ≤ 3 ∧ sgnR t * E.sideLevel h t q ≤ 2} with hDc
  have hDc_lt : ∀ q ∈ Dc, ‖q.1‖ < 3 := by
    intro q hq
    by_contra hc
    push Not at hc
    linarith [E.three_lt_sideLevel_of_ge h t (q := q) (by linarith) hq.1, hq.2]
  have hDc_closed : IsClosed Dc :=
    (continuousOn_const.mul (E.continuousOn_sideLevel h t)).preimage_isClosed_of_isClosed
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
  have hshell : ∀ x ∈ shellSet, ∃ q ∈ E.liftDom h t, F x = torusPD q ∧
      sgnR t * E.sideLevel h t q = 2 * ‖x‖ := by
    intro x hx
    obtain ⟨h1, -, h3⟩ := E.shellMap_spec h hlin t hx
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
  have hlevel2 : ∀ q : ℂ × Circle, ‖q.1‖ < 3 → sgnR t * E.sideLevel h t q = 2 →
      torusPD q ∈ F '' sphere (0 : E3) 1 := by
    intro q hq3 hq2
    have hL : E.sideLevel h t q = 2 * sgnR t := by
      have := sgnR_mul_self t
      linear_combination sgnR t * hq2 - E.sideLevel h t q * this
    have hlev3 : |E.sideLevel h t q| < 3 := by
      rw [hL, mul_comm, SplitCharts.abs_sgnR_mul]
      norm_num
    have hqd : q ∈ E.liftDom h t := ⟨hq3, by rw [hq2]; norm_num⟩
    obtain ⟨p, hp⟩ := E.exists_tubeMap_eq_liftMap h hlin t (E.sideDom_of_mem_liftDom h hqd) hlev3
    have hpn : ‖(p : E3)‖ = 1 := norm_eq_of_mem_sphere p
    have hdir : shellDir t (p : E3) = (p, E.sideLevel h t q) := by
      refine Prod.ext ?_ ?_
      · change Manifold.sphereDirection poleS2 (p : E3) = p
        have := Manifold.sphereDirection_pos_smul poleS2 p one_pos
        rwa [one_smul] at this
      · change 2 * sgnR t * ‖(p : E3)‖ = _
        rw [hpn, hL]
        ring
    refine ⟨(p : E3), p.2, ?_⟩
    rw [hF, shellMap, hdir, hp, E.liftInv_liftMap h hlin hqd]
  have hfront : frontier U = F '' sphere (0 : E3) 1 := by
    apply Subset.antisymm
    · intro y hy
      rw [hUo.frontier_eq] at hy
      obtain ⟨q, hq, rfl⟩ := hcl hy.1
      have h2 : sgnR t * E.sideLevel h t q = 2 :=
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

end GC.Seifert.ElementaryPresentation
