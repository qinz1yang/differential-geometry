/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ExtremalPoints
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.Incidence

noncomputable section

open Set Filter Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.StratumDeformation

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open HyperbolicConvexity AsymptoticRays BusemannCocycle
open OrbifoldStrata FixedLocusGeometry LorentzExtremal

variable {n : ℕ}

theorem continuous_of_val {X : Type*} [TopologicalSpace X]
    {f : X → HUpper n} (hf : Continuous (fun x => (f x).val)) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hd : Continuous (fun y => dist (f y) (f x)) := by
    change Continuous (fun y => Real.arcosh (-lorB (f y).val (f x).val))
    exact Real.continuousOn_arcosh.comp_continuous
      ((HyperbolicGeometry.continuous_neg_lorB_right (f x).val).comp hf)
      (fun y => HUpper.one_le_neg_lorB (f y) (f x))
  simpa only [dist_self] using hd.tendsto x

theorem continuous_rayTo_neg_start (ξ : BoundaryH n) (s : ℝ) :
    Continuous (fun x : HUpper n => rayTo x ξ (-s)) := by
  apply continuous_of_val
  have hc : Continuous (fun x : HUpper n => -lorB x.val ξ.val) :=
    (HyperbolicGeometry.continuous_neg_lorB_right ξ.val).comp continuous_val
  have hne (x : HUpper n) : -lorB x.val ξ.val ≠ 0 :=
    (Busemann.neg_lorB_upper_boundary_pos x ξ).ne'
  have he : Continuous (fun x : HUpper n =>
      Real.exp s • x.val - (Real.sinh s / (-lorB x.val ξ.val)) • ξ.val) := by
    exact (continuous_val.const_smul (Real.exp s)).sub
      (((continuous_const : Continuous (fun _ : HUpper n => Real.sinh s)).div hc hne).smul
        (continuous_const (y := ξ.val)))
  exact he.congr (fun x => (rayTo_neg_val x ξ s).symm)

theorem continuous_rayTo_neg_param (x : HUpper n) (ξ : BoundaryH n) :
    Continuous (fun s : ℝ => rayTo x ξ (-s)) := by
  apply continuous_of_val
  exact ((Real.continuous_exp.smul continuous_const).sub
    ((Real.continuous_sinh.div_const _).smul continuous_const)).congr
    (fun s => (rayTo_neg_val x ξ s).symm)

theorem boundary_val_mem_locusSpan_of_fixed (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (hD : (fixedLocus hn D).Nonempty) (ξ : BoundaryH n)
    (hξ : ∀ γ : D, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ) :
    ξ.val ∈ locusSpan (fixedLocus hn D) := by
  obtain ⟨p, hp⟩ := hD
  have hq : rayTo p ξ 1 ∈ fixedLocus hn D := by
    intro γ
    have he := BoundaryExtension.po_smul_rayTo hn (γ : PO n 1) p ξ 1
    change (poMulAction hn).smul (γ : PO n 1) (rayTo p ξ 1) =
      rayTo ((poMulAction hn).smul (γ : PO n 1) p)
        ((poBoundaryMulAction hn).smul (γ : PO n 1) ξ) 1 at he
    simpa only [hp γ, hξ γ] using he
  let V := locusSpan (fixedLocus hn D)
  have hpV : p.val ∈ V := val_mem_locusSpan hp
  have hqV : (rayTo p ξ 1).val ∈ V := val_mem_locusSpan hq
  have hsV : Real.sinh 1 • dirTo p ξ ∈ V := by
    have h := V.sub_mem hqV (V.smul_mem (Real.cosh 1) hpV)
    change Real.cosh 1 • p.val + Real.sinh 1 • dirTo p ξ -
      Real.cosh 1 • p.val ∈ V at h
    simpa only [add_sub_cancel_left] using h
  have hdir : dirTo p ξ ∈ V := by
    have h := V.smul_mem (Real.sinh 1)⁻¹ hsV
    rwa [smul_smul, inv_mul_cancel₀ (Real.sinh_pos_iff.mpr zero_lt_one).ne', one_smul] at h
  have h := V.smul_mem (-lorB p.val ξ.val) (V.add_mem hpV hdir)
  rwa [Busemann.add_dirTo_eq, smul_smul,
    mul_inv_cancel₀ (Busemann.neg_lorB_upper_boundary_pos p ξ).ne', one_smul] at h

theorem boundary_val_mem_span_at_closure (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ : Set (HUpper n)} (hσ : σ.Nonempty) {x : HUpper n}
    (hx : x ∈ closure (fixedStratum hn Γ ε σ)) (ξ : BoundaryH n)
    (hξ : ∀ γ : closedSmallSubgroup hn Γ ε x,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ) :
    ξ.val ∈ locusSpan σ := by
  obtain ⟨y, hy, hyF⟩ := mem_closure_iff_nhds.mp hx _
    (eventually_closedSmallSubgroup_le hn Γ hΓ ε x)
  have he : fixedLocus hn (closedSmallSubgroup hn Γ ε y) = σ := hyF
  have h := boundary_val_mem_locusSpan_of_fixed hn (closedSmallSubgroup hn Γ ε y)
    (he.symm ▸ hσ) ξ (fun γ => hξ ⟨γ, hy γ.property⟩)
  simpa only [he] using h

theorem displacement_le_rayTo_neg (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n)
    (hξ : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hscale : poConfFactor hn g ξ = 1) (y : HUpper n)
    {t : ℝ} (ht : 0 ≤ t) :
    dist ((poMulAction hn).smul g y) y ≤
      dist ((poMulAction hn).smul g (rayTo y ξ (-t))) (rayTo y ξ (-t)) := by
  have he := ParabolicRegions.cosh_displacement_rayTo_sub_one hn g ξ hξ hscale y (-t)
  have hfactor : 1 ≤ Real.exp (-(2 * -t)) := Real.one_le_exp_iff.mpr (by linarith)
  have hnonneg : 0 ≤ Real.cosh (dist ((poMulAction hn).smul g y) y) - 1 :=
    sub_nonneg.mpr (Real.one_le_cosh _)
  have hmul := mul_le_mul_of_nonneg_left hfactor hnonneg
  have hcosh : Real.cosh (dist ((poMulAction hn).smul g y) y) ≤
      Real.cosh (dist ((poMulAction hn).smul g (rayTo y ξ (-t))) (rayTo y ξ (-t))) := by
    linarith
  exact (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp hcosh

theorem closedSmallSubgroup_rayTo_neg_le (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (D : Subgroup (PO n 1)) (ξ : BoundaryH n)
    (hD : ∀ γ : D, (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
      poConfFactor hn (γ : PO n 1) ξ = 1)
    (y : HUpper n) {t : ℝ} (ht : 0 ≤ t)
    (hle : closedSmallSubgroup hn Γ ε (rayTo y ξ (-t)) ≤ D) :
    closedSmallSubgroup hn Γ ε (rayTo y ξ (-t)) ≤ closedSmallSubgroup hn Γ ε y := by
  apply Subgroup.closure_mono
  intro g hg
  have hgD : g ∈ D := hle (Subgroup.subset_closure hg)
  obtain ⟨hfix, hscale⟩ := hD ⟨g, hgD⟩
  exact ⟨hg.1, (displacement_le_rayTo_neg hn g ξ hfix hscale y ht).trans hg.2⟩

theorem not_isOpen_of_horospherical_exit (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ : Set (HUpper n)} {x : HUpper n}
    (hx : x ∈ closure (fixedStratum hn Γ ε σ)) (ξ : BoundaryH n)
    (hD : ∀ γ : closedSmallSubgroup hn Γ ε x,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
        poConfFactor hn (γ : PO n 1) ξ = 1)
    (hexit : ∀ s : ℝ, 0 < s → rayTo x ξ (-s) ∉ closure (fixedStratum hn Γ ε σ)) :
    ¬IsOpen (fixedStratum hn Γ ε σ) := by
  intro hopen
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_closedSmallSubgroup_le hn Γ hΓ ε x)
  let s : ℝ := r / 4
  have hs : 0 < s := by dsimp [s]; positivity
  have hout : {y : HUpper n | rayTo y ξ (-s) ∉ closure (fixedStratum hn Γ ε σ)} ∈ 𝓝 x :=
    (isClosed_closure.isOpen_compl.preimage (continuous_rayTo_neg_start ξ s)).mem_nhds
      (hexit s hs)
  obtain ⟨y, hy, hyF⟩ := mem_closure_iff_nhds.mp hx _
    (inter_mem (Metric.ball_mem_nhds x hs) hout)
  have hyclose : dist y x < s := hy.1
  let q : ℝ → HUpper n := fun t => rayTo y ξ (-t)
  have hqcont : Continuous q := continuous_rayTo_neg_param y ξ
  have hqzero : q 0 = y := by dsimp [q]; rw [neg_zero, rayTo_zero]
  have hqball : ∀ t ∈ Icc 0 s, q t ∈ Metric.ball x r := by
    intro t ht
    have hd : dist (q t) y = t := by
      rw [dist_comm, dist_rayTo_self, abs_neg, abs_of_nonneg ht.1]
    have h := dist_triangle (q t) y x
    rw [hd] at h
    change dist (q t) x < r
    dsimp [s] at ht hyclose
    linarith [ht.2]
  have hqclosed : ∀ t ∈ Icc 0 s, q t ∈ closure (fixedStratum hn Γ ε σ) →
      q t ∈ fixedStratum hn Γ ε σ := by
    intro t ht hcl
    have hle := closedSmallSubgroup_rayTo_neg_le hn Γ ε
      (closedSmallSubgroup hn Γ ε x) ξ hD y ht.1 (hball (hqball t ht))
    have hsub := fixedLocus_antitone hn hle
    have hsup := fixedLocus_subset_of_incident hn Γ hΓ ε (x := q t) rfl hcl
    change fixedLocus hn (closedSmallSubgroup hn Γ ε (q t)) = σ
    apply Subset.antisymm hsup
    simpa only [show fixedLocus hn (closedSmallSubgroup hn Γ ε y) = σ from hyF] using hsub
  have hconn : IsPreconnected (q '' Icc 0 s) :=
    isPreconnected_Icc.image q hqcont.continuousOn
  have hstart : ((q '' Icc 0 s) ∩ fixedStratum hn Γ ε σ).Nonempty :=
    ⟨y, ⟨0, ⟨le_rfl, hs.le⟩, hqzero⟩, hyF⟩
  have hwhole : q '' Icc 0 s ⊆ fixedStratum hn Γ ε σ :=
    hconn.subset_of_closure_inter_subset hopen hstart (by
      rintro z ⟨hz, t, ht, rfl⟩
      exact hqclosed t ht hz)
  exact hy.2 (subset_closure (hwhole ⟨s, ⟨hs.le, le_rfl⟩, rfl⟩))

theorem not_isOpen_of_horospherical_extremal (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ : Set (HUpper n)} (hσ : σ.Nonempty) {x : HUpper n}
    (hx : x ∈ closure (fixedStratum hn Γ ε σ))
    (hext : ∀ y ∈ closure (fixedStratum hn Γ ε σ), ∀ c : ℝ, 1 < c →
      ∀ w ∈ locusSpan σ, w ∈ futureCone → y.val ≠ c • x.val - w)
    (ξ : BoundaryH n)
    (hD : ∀ γ : closedSmallSubgroup hn Γ ε x,
      (poBoundaryMulAction hn).smul (γ : PO n 1) ξ = ξ ∧
        poConfFactor hn (γ : PO n 1) ξ = 1) :
    ¬IsOpen (fixedStratum hn Γ ε σ) := by
  have hξ := boundary_val_mem_span_at_closure hn Γ hΓ ε hσ hx ξ (fun γ => (hD γ).1)
  exact not_isOpen_of_horospherical_exit hn Γ hΓ ε hx ξ hD
    (fun _ hs => rayTo_neg_notMem_of_extremal (locusSpan σ) hext hξ hs)

theorem cosh_displacement_geodFromTo_sub_one (hn : 1 ≤ n) (g : PO n 1)
    (p y : HUpper n) (hpy : p ≠ y)
    (hfix : (poMulAction hn).smul g p = p) (t : ℝ) :
    Real.cosh (dist ((poMulAction hn).smul g (geodFromTo p y hpy t))
      (geodFromTo p y hpy t)) - 1 =
        (Real.sinh t / Real.sinh (dist p y)) ^ 2 *
          (Real.cosh (dist ((poMulAction hn).smul g y) y) - 1) := by
  let := poMulAction hn
  change g • p = p at hfix
  let q := geodFromTo p y hpy
  have hs : Real.sinh (dist p y) ≠ 0 := (Real.sinh_pos_iff.mpr (dist_pos.mpr hpy)).ne'
  have hnear : Real.cosh (dist (g • q t) p) = Real.cosh t := by
    have hd : dist (q t) p = |t| := by
      simpa only [geodFromTo_zero, sub_zero] using dist_geodFromTo hpy t 0
    calc
      Real.cosh (dist (g • q t) p) = Real.cosh (dist (g • q t) (g • p)) := by rw [hfix]
      _ = Real.cosh (dist (q t) p) := by rw [po_dist_smul hn]
      _ = Real.cosh t := by rw [hd, Real.cosh_abs]
  have hinvp : dist (g⁻¹ • y) p = dist p y := by
    calc
      dist (g⁻¹ • y) p = dist (g • (g⁻¹ • y)) (g • p) := (po_dist_smul hn g _ _).symm
      _ = dist p y := by rw [smul_inv_smul, hfix, dist_comm]
  have hinvy : dist (g⁻¹ • y) y = dist (g • y) y := by
    calc
      dist (g⁻¹ • y) y = dist (g • (g⁻¹ • y)) (g • y) := (po_dist_smul hn g _ _).symm
      _ = dist (g • y) y := by rw [smul_inv_smul, dist_comm]
  have hmove : dist (g • q t) y = dist (g⁻¹ • y) (q t) := by
    calc
      dist (g • q t) y = dist (g • q t) (g • (g⁻¹ • y)) := by rw [smul_inv_smul]
      _ = dist (g⁻¹ • y) (q t) := by rw [po_dist_smul hn, dist_comm]
  have hcross : Real.cosh (dist (g • q t) y) =
      Real.cosh t * Real.cosh (dist p y) +
        Real.sinh t * ((Real.cosh (dist (g • y) y) -
          Real.cosh (dist p y) ^ 2) / Real.sinh (dist p y)) := by
    rw [hmove, cosh_dist_geodFromTo hpy, hinvp, hinvy, pow_two]
  have he := cosh_dist_geodFromTo hpy (g • q t) t
  change Real.cosh (dist (g • q t) (q t)) =
    Real.cosh t * Real.cosh (dist (g • q t) p) +
      Real.sinh t * ((Real.cosh (dist (g • q t) y) -
        Real.cosh (dist p y) * Real.cosh (dist (g • q t) p)) /
          Real.sinh (dist p y)) at he
  rw [hnear, hcross] at he
  change Real.cosh (dist (g • q t) (q t)) - 1 = _
  rw [he]
  field_simp
  linear_combination (Real.sinh (dist p y)) ^ 2 * Real.cosh_sq_sub_sinh_sq t -
    (Real.sinh t) ^ 2 * Real.cosh_sq_sub_sinh_sq (dist p y)

theorem displacement_le_geodFromTo (hn : 1 ≤ n) (g : PO n 1)
    (p y : HUpper n) (hpy : p ≠ y)
    (hfix : (poMulAction hn).smul g p = p) {t : ℝ} (ht : dist p y ≤ t) :
    dist ((poMulAction hn).smul g y) y ≤
      dist ((poMulAction hn).smul g (geodFromTo p y hpy t)) (geodFromTo p y hpy t) := by
  have he := cosh_displacement_geodFromTo_sub_one hn g p y hpy hfix t
  have hs : 0 < Real.sinh (dist p y) := Real.sinh_pos_iff.mpr (dist_pos.mpr hpy)
  have hratio : 1 ≤ Real.sinh t / Real.sinh (dist p y) :=
    (one_le_div hs).mpr (Real.sinh_le_sinh.mpr ht)
  have hsq : 1 ≤ (Real.sinh t / Real.sinh (dist p y)) ^ 2 := by nlinarith
  have hnonneg : 0 ≤ Real.cosh (dist ((poMulAction hn).smul g y) y) - 1 :=
    sub_nonneg.mpr (Real.one_le_cosh _)
  have hmul := mul_le_mul_of_nonneg_right hsq hnonneg
  apply (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp
  linarith

def radialExpand (p : HUpper n) (s : ℝ) (y : HUpper n) : HUpper n := by
  classical
  exact if h : p = y then y else geodFromTo p y h (dist p y + s)

theorem radialExpand_of_ne {p y : HUpper n} (hpy : p ≠ y) (s : ℝ) :
    radialExpand p s y = geodFromTo p y hpy (dist p y + s) := dite_eq_right hpy

theorem continuousAt_radialExpand {p x : HUpper n} (hpx : p ≠ x) (s : ℝ) :
    ContinuousAt (radialExpand p s) x := by
  let S := {y : HUpper n // p ≠ y}
  have hd : Continuous (fun y : S => dist p y.val) :=
    continuous_const.dist continuous_subtype_val
  have hv : Continuous (fun y : S => y.val.val) := continuous_val.comp continuous_subtype_val
  have hinv : Continuous (fun y : S => (Real.sinh (dist p y.val))⁻¹) :=
    (Real.continuous_sinh.comp hd).inv₀
      (fun y => (Real.sinh_pos_iff.mpr (dist_pos.mpr y.property)).ne')
  have hval : Continuous (fun y : S => (radialExpand p s y.val).val) := by
    have hc : Continuous (fun y : S =>
        Real.cosh (dist p y.val + s) • p.val +
          Real.sinh (dist p y.val + s) •
            ((Real.sinh (dist p y.val))⁻¹ •
              (y.val.val - Real.cosh (dist p y.val) • p.val))) :=
      ((Real.continuous_cosh.comp (hd.add_const s)).smul continuous_const).add
        ((Real.continuous_sinh.comp (hd.add_const s)).smul
          (hinv.smul (hv.sub ((Real.continuous_cosh.comp hd).smul continuous_const))))
    exact hc.congr (fun y => by rw [radialExpand_of_ne y.property]; rfl)
  have hco : ContinuousOn (radialExpand p s) {y : HUpper n | p ≠ y} :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_of_val hval)
  have hopen : IsOpen {y : HUpper n | p ≠ y} := by
    simpa only [ne_comm] using (isOpen_ne (x := p))
  exact hco.continuousAt (hopen.mem_nhds hpx)

theorem closedSmallSubgroup_radial_le (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (D : Subgroup (PO n 1)) (p : HUpper n) (hp : p ∈ fixedLocus hn D)
    (y : HUpper n) (hpy : p ≠ y) {t : ℝ} (ht : dist p y ≤ t)
    (hle : closedSmallSubgroup hn Γ ε (geodFromTo p y hpy t) ≤ D) :
    closedSmallSubgroup hn Γ ε (geodFromTo p y hpy t) ≤ closedSmallSubgroup hn Γ ε y := by
  apply Subgroup.closure_mono
  intro g hg
  have hgD : g ∈ D := hle (Subgroup.subset_closure hg)
  exact ⟨hg.1, (displacement_le_geodFromTo hn g p y hpy (hp ⟨g, hgD⟩) ht).trans hg.2⟩

theorem not_isOpen_of_fixed_point_exit (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ : Set (HUpper n)} {x p : HUpper n}
    (hx : x ∈ closure (fixedStratum hn Γ ε σ)) (hpx : p ≠ x)
    (hp : p ∈ fixedLocus hn (closedSmallSubgroup hn Γ ε x))
    (hexit : ∀ s : ℝ, 0 < s → radialExpand p s x ∉ closure (fixedStratum hn Γ ε σ)) :
    ¬IsOpen (fixedStratum hn Γ ε σ) := by
  intro hopen
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_closedSmallSubgroup_le hn Γ hΓ ε x)
  let s : ℝ := min r (dist p x) / 4
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos (lt_min hr (dist_pos.mpr hpx)) (by norm_num)
  have hsr : s ≤ r / 4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hsp : s ≤ dist p x / 4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hout : {y : HUpper n | radialExpand p s y ∉ closure (fixedStratum hn Γ ε σ)} ∈ 𝓝 x :=
    (continuousAt_radialExpand hpx s).preimage_mem_nhds
      (isClosed_closure.isOpen_compl.mem_nhds (hexit s hs))
  obtain ⟨y, hy, hyF⟩ := mem_closure_iff_nhds.mp hx _
    (inter_mem (Metric.ball_mem_nhds x hs) hout)
  have hyclose : dist y x < s := hy.1
  have hpy : p ≠ y := by
    intro he
    rw [← he] at hyclose
    have := dist_nonneg (x := p) (y := x)
    linarith
  let q : ℝ → HUpper n := fun t => geodFromTo p y hpy (dist p y + t)
  have hqcont : Continuous q :=
    (continuous_geodFromTo (hd := hpy)).comp (continuous_const.add continuous_id)
  have hqzero : q 0 = y := by dsimp [q]; rw [add_zero, geodFromTo_dist]
  have hqball : ∀ t ∈ Icc 0 s, q t ∈ Metric.ball x r := by
    intro t ht
    have hd : dist (q t) y = t := by
      have h := dist_geodFromTo hpy (dist p y + t) (dist p y)
      simpa only [geodFromTo_dist, add_sub_cancel_left, abs_of_nonneg ht.1] using h
    have h := dist_triangle (q t) y x
    rw [hd] at h
    change dist (q t) x < r
    linarith [ht.2]
  have hqclosed : ∀ t ∈ Icc 0 s, q t ∈ closure (fixedStratum hn Γ ε σ) →
      q t ∈ fixedStratum hn Γ ε σ := by
    intro t ht hcl
    have hle := closedSmallSubgroup_radial_le hn Γ ε
      (closedSmallSubgroup hn Γ ε x) p hp y hpy (le_add_of_nonneg_right ht.1)
      (hball (hqball t ht))
    have hsub := fixedLocus_antitone hn hle
    have hsup := fixedLocus_subset_of_incident hn Γ hΓ ε (x := q t) rfl hcl
    change fixedLocus hn (closedSmallSubgroup hn Γ ε (q t)) = σ
    apply Subset.antisymm hsup
    simpa only [show fixedLocus hn (closedSmallSubgroup hn Γ ε y) = σ from hyF] using hsub
  have hconn : IsPreconnected (q '' Icc 0 s) :=
    isPreconnected_Icc.image q hqcont.continuousOn
  have hstart : ((q '' Icc 0 s) ∩ fixedStratum hn Γ ε σ).Nonempty :=
    ⟨y, ⟨0, ⟨le_rfl, hs.le⟩, hqzero⟩, hyF⟩
  have hwhole : q '' Icc 0 s ⊆ fixedStratum hn Γ ε σ :=
    hconn.subset_of_closure_inter_subset hopen hstart (by
      rintro z ⟨hz, t, ht, rfl⟩
      exact hqclosed t ht hz)
  apply hy.2
  rw [radialExpand_of_ne hpy]
  exact subset_closure (hwhole ⟨s, ⟨hs.le, le_rfl⟩, rfl⟩)

theorem not_isOpen_of_finite_extremal (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ : Set (HUpper n)} {x : HUpper n}
    (hx : x ∈ closure (fixedStratum hn Γ ε σ)) (hxσ : x ∉ σ)
    (hext : ∀ y ∈ closure (fixedStratum hn Γ ε σ), ∀ c : ℝ, 1 < c →
      ∀ w ∈ locusSpan σ, w ∈ futureCone → y.val ≠ c • x.val - w)
    [Finite (closedSmallSubgroup hn Γ ε x)] :
    ¬IsOpen (fixedStratum hn Γ ε σ) := by
  obtain ⟨p, hp⟩ := (fixedLocus_nonempty_iff_finite hn (closedSmallSubgroup hn Γ ε x)
    (hΓ.mono (closedSmallSubgroup_le hn Γ ε x))).mpr inferInstance
  have hpσ : p ∈ σ := fixedLocus_subset_of_incident hn Γ hΓ ε (x := x) rfl hx hp
  have hpx : p ≠ x := fun he => hxσ (he ▸ hpσ)
  apply not_isOpen_of_fixed_point_exit hn Γ hΓ ε hx hpx hp
  intro s hs
  rw [radialExpand_of_ne hpx]
  exact geodFromTo_notMem_of_extremal (locusSpan σ) hext (val_mem_locusSpan hpσ) hpx
    (lt_add_of_pos_right _ hs)

theorem exists_axial_extremal_of_isOpen (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hgeometry : ∀ x : HUpper n,
      BoundaryStabilizer.ElementaryGeometry hn (closedSmallSubgroup hn Γ ε x))
    {σ : Set (HUpper n)} (hσ : σ.Nonempty)
    (hF : (fixedStratum hn Γ ε σ).Nonempty) (hproper : σ ≠ univ)
    (hopen : IsOpen (fixedStratum hn Γ ε σ)) :
    ∃ x ∈ closure (fixedStratum hn Γ ε σ), x ∉ σ ∧
      (∀ y ∈ closure (fixedStratum hn Γ ε σ), ∀ c : ℝ, 1 < c →
        ∀ w ∈ locusSpan σ, w ∈ futureCone → y.val ≠ c • x.val - w) ∧
      Infinite (closedSmallSubgroup hn Γ ε x) ∧
      ∃ ξ η : BoundaryH n, ξ ≠ η ∧ ∀ γ : closedSmallSubgroup hn Γ ε x,
        (poBoundaryMulAction hn).smul (γ : PO n 1) ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
        (poBoundaryMulAction hn).smul (γ : PO n 1) η ∈ ({ξ, η} : Set (BoundaryH n)) := by
  have hnotSub : ¬fixedStratum hn Γ ε σ ⊆ σ :=
    fun hsub => StratumIncidence.not_isOpen_of_subset_fixedLocus hn Γ ε hF hproper hsub hopen
  obtain ⟨z, hz, hzσ⟩ := Set.not_subset.mp hnotSub
  obtain ⟨x, hx, hxσ, hext⟩ :=
    exists_extremal_closure_fixedStratum hn Γ hΓ hε hσ hz hzσ
  have hnotFinite : ¬Finite (closedSmallSubgroup hn Γ ε x) := by
    intro hfin
    let := hfin
    exact not_isOpen_of_finite_extremal hn Γ hΓ ε hx hxσ hext hopen
  have hInf := not_finite_iff_infinite.mp hnotFinite
  rcases hgeometry x with ⟨hfin, _⟩ | hpair | ⟨ξ, hhor⟩
  · exact (hnotFinite hfin).elim
  · exact ⟨x, hx, hxσ, hext, hInf, hpair⟩
  · exact (not_isOpen_of_horospherical_extremal hn Γ hΓ ε hσ hx hext ξ hhor hopen).elim

end DifferentialGeometry.StratumDeformation
