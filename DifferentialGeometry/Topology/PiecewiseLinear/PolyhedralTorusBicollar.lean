import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.TorusCylinder
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# A polyhedral torus with an explicit bicollar

The square donut. Polar coordinates for the max norm `max |re| |im|` on `ℂ` send
`(k, u) ∈ (0, ∞) × Circle` to `k • u / max |u.re| |u.im|`, with inverse `w ↦ (max norm, w / ‖w‖)`.
Using them once in the meridian half-plane around `(2, 0)` and once in the horizontal plane gives
an open partial homeomorphism from `Torus × (-1, 1)` onto the open square shell
`{x | 1/2 < max |max |x₀| |x₁| - 2| |x₂| < 3/2}` of `ℝ³`. Its zero level is the boundary of the
solid square donut, a union of sixteen coordinate boxes, hence a polyhedron
(`exists_polyhedral_bicollar_model`).
-/

set_option autoImplicit false

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable section

private def sqN (w : ℂ) : ℝ := max |w.re| |w.im|

private def sqPolar (k : ℝ) (u : Circle) : ℂ := ((k / sqN u : ℝ) : ℂ) * u

private theorem normalize_mem_unitSphere {w : ℂ} (hw : w ≠ 0) :
    ((‖w‖⁻¹ : ℝ) : ℂ) * w ∈ Submonoid.unitSphere ℂ :=
  mem_sphere_zero_iff_norm.2 (by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)])

private def toCircle (w : ℂ) : Circle :=
  if h : w = 0 then 1 else ⟨((‖w‖⁻¹ : ℝ) : ℂ) * w, normalize_mem_unitSphere h⟩

private theorem continuous_sqN : Continuous sqN := by
  unfold sqN
  fun_prop

private theorem sqN_pos {w : ℂ} (hw : w ≠ 0) : 0 < sqN w := by
  by_contra h
  replace h := not_lt.mp h
  apply hw
  apply Complex.ext
  · simpa using abs_nonpos_iff.mp ((le_max_left _ _).trans h)
  · simpa using abs_nonpos_iff.mp ((le_max_right _ _).trans h)

private theorem sqN_zero : sqN 0 = 0 := by simp [sqN]

private theorem sqN_ofReal_mul {c : ℝ} (hc : 0 ≤ c) (w : ℂ) : sqN (c * w) = c * sqN w := by
  simp only [sqN, Complex.re_ofReal_mul, Complex.im_ofReal_mul, abs_mul, abs_of_nonneg hc]
  rw [mul_max_of_nonneg _ _ hc]

private theorem abs_re_le_sqN (w : ℂ) : |w.re| ≤ sqN w := le_max_left _ _

private theorem sqN_sqPolar {k : ℝ} (hk : 0 ≤ k) (u : Circle) : sqN (sqPolar k u) = k := by
  have hu := sqN_pos (Circle.coe_ne_zero u)
  rw [sqPolar, sqN_ofReal_mul (div_nonneg hk hu.le)]
  field_simp

private theorem coe_toCircle {w : ℂ} (hw : w ≠ 0) :
    (toCircle w : ℂ) = ((‖w‖⁻¹ : ℝ) : ℂ) * w := by
  simp [toCircle, hw]

private theorem toCircle_ofReal_mul {c : ℝ} (hc : 0 < c) (u : Circle) :
    toCircle (c * u) = u := by
  have hne : ((c : ℂ) * u) ≠ 0 := mul_ne_zero (by exact_mod_cast hc.ne') (Circle.coe_ne_zero u)
  apply Circle.ext
  rw [coe_toCircle hne, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg hc.le, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne',
    Complex.ofReal_one, one_mul]

private theorem toCircle_sqPolar {k : ℝ} (hk : 0 < k) (u : Circle) :
    toCircle (sqPolar k u) = u :=
  toCircle_ofReal_mul (div_pos hk (sqN_pos (Circle.coe_ne_zero u))) u

private theorem sqPolar_toCircle {w : ℂ} (hw : w ≠ 0) : sqPolar (sqN w) (toCircle w) = w := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hs := sqN_pos hw
  rw [sqPolar, coe_toCircle hw, sqN_ofReal_mul (inv_nonneg.mpr hn.le), ← mul_assoc,
    ← Complex.ofReal_mul]
  have h : sqN w / (‖w‖⁻¹ * sqN w) * ‖w‖⁻¹ = 1 := by field_simp
  rw [h, Complex.ofReal_one, one_mul]

private theorem continuousOn_toCircle : ContinuousOn toCircle {0}ᶜ := by
  have hind : IsInducing ((↑) : Circle → ℂ) := IsInducing.subtypeVal
  refine hind.continuousOn_iff.mpr ?_
  refine ContinuousOn.congr (f := fun w : ℂ => ((‖w‖⁻¹ : ℝ) : ℂ) * w) ?_ ?_
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (continuous_norm.continuousOn.inv₀ fun w hw => norm_ne_zero_iff.mpr hw)).mul
      continuousOn_id
  · intro w hw
    exact coe_toCircle hw

private theorem Continuous.sqPolar {X : Type*} [TopologicalSpace X] {f : X → ℝ} {g : X → Circle}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => sqPolar (f x) (g x) := by
  have hg' : Continuous fun x => ((g x : Circle) : ℂ) := continuous_subtype_val.comp hg
  exact (Complex.continuous_ofReal.comp (hf.div (continuous_sqN.comp hg')
    fun x => (sqN_pos (Circle.coe_ne_zero _)).ne')).mul hg'

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

private def cpx (a b : ℝ) : ℂ := (a : ℂ) + (b : ℂ) * Complex.I

@[simp] private theorem cpx_re (a b : ℝ) : (cpx a b).re = a := by simp [cpx]

@[simp] private theorem cpx_im (a b : ℝ) : (cpx a b).im = b := by simp [cpx]

private theorem cpx_re_im (w : ℂ) : cpx w.re w.im = w := Complex.ext (by simp) (by simp)

private theorem sqN_cpx (a b : ℝ) : sqN (cpx a b) = max |a| |b| := by simp [sqN]

private theorem Continuous.cpx {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => cpx (f x) (g x) := by
  unfold PiecewiseLinear.cpx
  fun_prop

private def meridian (p : GC.Topology.Torus × ℝ) : ℂ := sqPolar (1 + p.2 / 2) p.1.2

private def chartFun (p : GC.Topology.Torus × ℝ) : ℝ³ :=
  !₂[(sqPolar (2 + (meridian p).re) p.1.1).re, (sqPolar (2 + (meridian p).re) p.1.1).im,
    (meridian p).im]

private def planeOf (x : ℝ³) : ℂ := cpx (x 0) (x 1)

private def merOf (x : ℝ³) : ℂ := cpx (sqN (planeOf x) - 2) (x 2)

private def chartInv (x : ℝ³) : GC.Topology.Torus × ℝ :=
  ((toCircle (planeOf x), toCircle (merOf x)), 2 * (sqN (merOf x) - 1))

private def shell : Set ℝ³ := {x | 1 / 2 < sqN (merOf x) ∧ sqN (merOf x) < 3 / 2}

private theorem sqN_merOf (x : ℝ³) : sqN (merOf x) = max |max |x 0| |x 1| - 2| |x 2| := by
  rw [merOf, sqN_cpx, planeOf, sqN_cpx]

private theorem continuous_planeOf : Continuous planeOf :=
  Continuous.cpx (PiLp.continuous_apply 2 _ 0) (PiLp.continuous_apply 2 _ 1)

private theorem continuous_merOf : Continuous merOf :=
  Continuous.cpx ((continuous_sqN.comp continuous_planeOf).sub continuous_const)
    (PiLp.continuous_apply 2 _ 2)

private theorem continuous_chartFun : Continuous chartFun := by
  have hm : Continuous meridian :=
    Continuous.sqPolar (continuous_const.add (continuous_snd.div_const 2))
      (continuous_snd.comp continuous_fst)
  have hw : Continuous fun p : GC.Topology.Torus × ℝ =>
      sqPolar (2 + (meridian p).re) p.1.1 :=
    Continuous.sqPolar (continuous_const.add (Complex.continuous_re.comp hm))
      (continuous_fst.comp continuous_fst)
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact Complex.continuous_re.comp hw
  · exact Complex.continuous_im.comp hw
  · exact Complex.continuous_im.comp hm

private theorem sqN_meridian {p : GC.Topology.Torus × ℝ} (hp : -2 ≤ p.2) :
    sqN (meridian p) = 1 + p.2 / 2 :=
  sqN_sqPolar (by linarith) _

private theorem planeOf_chartFun (p : GC.Topology.Torus × ℝ) :
    planeOf (chartFun p) = sqPolar (2 + (meridian p).re) p.1.1 := by
  rw [planeOf, ← cpx_re_im (sqPolar _ _)]
  rfl

private theorem two_add_re_pos {p : GC.Topology.Torus × ℝ} (hp : -1 < p.2 ∧ p.2 < 1) :
    0 < 2 + (meridian p).re := by
  have h1 := sqN_meridian (p := p) (by linarith)
  have h2 := neg_le_of_abs_le (abs_re_le_sqN (meridian p))
  linarith

private theorem merOf_chartFun {p : GC.Topology.Torus × ℝ} (hp : -1 < p.2 ∧ p.2 < 1) :
    merOf (chartFun p) = meridian p := by
  apply Complex.ext
  · rw [merOf, cpx_re, planeOf_chartFun, sqN_sqPolar (two_add_re_pos hp).le,
      add_sub_cancel_left]
  · rw [merOf, cpx_im]
    rfl

private theorem chartInv_chartFun {p : GC.Topology.Torus × ℝ} (hp : -1 < p.2 ∧ p.2 < 1) :
    chartInv (chartFun p) = p := by
  obtain ⟨⟨u, v⟩, s⟩ := p
  have h1 := sqN_meridian (p := ((u, v), s)) (by simp only at hp ⊢; linarith)
  have hv : toCircle (meridian ((u, v), s)) = v :=
    toCircle_sqPolar (by simp only at hp ⊢; linarith) v
  simp only [chartInv]
  rw [planeOf_chartFun, merOf_chartFun hp, toCircle_sqPolar (two_add_re_pos hp), hv, h1]
  simp only [Prod.mk.injEq, true_and]
  ring

private theorem chartFun_chartInv {x : ℝ³} (hx : x ∈ shell) : chartFun (chartInv x) = x := by
  obtain ⟨hlo, hhi⟩ := hx
  have hm0 : merOf x ≠ 0 := fun h => by rw [h, sqN_zero] at hlo; linarith
  have hmer : meridian (chartInv x) = merOf x := by
    simp only [meridian, chartInv]
    rw [show 1 + 2 * (sqN (merOf x) - 1) / 2 = sqN (merOf x) by ring]
    exact sqPolar_toCircle hm0
  have hre : (merOf x).re = sqN (planeOf x) - 2 := cpx_re _ _
  have hpl : planeOf x ≠ 0 := by
    intro h
    have h3 := abs_re_le_sqN (merOf x)
    rw [hre, h, sqN_zero, zero_sub, abs_neg] at h3
    norm_num at h3
    linarith
  have hw : sqPolar (2 + (meridian (chartInv x)).re) (chartInv x).1.1 = planeOf x := by
    rw [hmer, hre, add_sub_cancel]
    exact sqPolar_toCircle hpl
  unfold chartFun
  rw [hw, hmer]
  ext i
  fin_cases i <;> simp [planeOf, merOf]

private def chart : OpenPartialHomeomorph (GC.Topology.Torus × ℝ) ℝ³ where
  toFun := chartFun
  invFun := chartInv
  source := {p | -1 < p.2 ∧ p.2 < 1}
  target := shell
  map_source' p hp := by
    have h := sqN_meridian (p := p) (by linarith [hp.1])
    simp only [shell, mem_ofPred_eq]
    rw [merOf_chartFun hp, h]
    constructor <;> linarith [hp.1, hp.2]
  map_target' x hx := by
    obtain ⟨hlo, hhi⟩ := hx
    simp only [chartInv, mem_ofPred_eq]
    constructor <;> linarith
  left_inv' p hp := chartInv_chartFun hp
  right_inv' x hx := chartFun_chartInv hx
  open_source := (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd continuous_const)
  open_target := (isOpen_lt continuous_const (continuous_sqN.comp continuous_merOf)).inter
    (isOpen_lt (continuous_sqN.comp continuous_merOf) continuous_const)
  continuousOn_toFun := continuous_chartFun.continuousOn
  continuousOn_invFun := by
    have hpl : MapsTo planeOf shell {0}ᶜ := by
      intro x hx h
      have h3 := abs_re_le_sqN (merOf x)
      rw [show (merOf x).re = sqN (planeOf x) - 2 from cpx_re _ _, mem_singleton_iff.mp h,
        sqN_zero, zero_sub, abs_neg] at h3
      norm_num at h3
      linarith [hx.2]
    have hme : MapsTo merOf shell {0}ᶜ := by
      intro x hx h
      have h0 := hx.1
      rw [mem_singleton_iff.mp h, sqN_zero] at h0
      linarith
    refine ContinuousOn.prodMk (ContinuousOn.prodMk ?_ ?_) ?_
    · exact continuousOn_toCircle.comp continuous_planeOf.continuousOn hpl
    · exact continuousOn_toCircle.comp continuous_merOf.continuousOn hme
    · exact (continuous_const.mul
        ((continuous_sqN.comp continuous_merOf).sub continuous_const)).continuousOn

private theorem range_chart_level :
    (Set.range fun t => chart (t, 0)) = {x | sqN (merOf x) = 1} := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    have h0 : -1 < (t, (0 : ℝ)).2 ∧ (t, (0 : ℝ)).2 < 1 := by norm_num
    change sqN (merOf (chartFun (t, 0))) = 1
    rw [merOf_chartFun h0, sqN_meridian (by norm_num)]
    norm_num
  · intro hx
    have hx1 : sqN (merOf x) = 1 := hx
    have hx' : x ∈ shell := by
      simp only [shell, mem_ofPred_eq]
      rw [hx1]
      norm_num
    refine ⟨(chartInv x).1, ?_⟩
    have h2 : (chartInv x).2 = 0 := by
      simp only [chartInv]
      rw [hx1]
      ring
    change chartFun ((chartInv x).1, 0) = x
    rw [← h2]
    exact chartFun_chartInv hx'

private def box (a b : Fin 3 → ℝ) : Set ℝ³ := {x | ∀ i, a i ≤ x i ∧ x i ≤ b i}

private theorem isPolyhedron_box (a b : Fin 3 → ℝ) : IsPolyhedron (box a b) := by
  refine IsHPolytope.isPolyhedron ⟨?_, Fin 3 ⊕ Fin 3, inferInstance,
    Sum.elim (fun i => PiLp.projₗ 2 (fun _ : Fin 3 => ℝ) i)
      (fun i => -PiLp.projₗ 2 (fun _ : Fin 3 => ℝ) i), Sum.elim b fun i => -a i, ?_⟩
  · have h : box a b = PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ) ⁻¹' Icc a b := by
      ext x
      exact forall_and
    rw [h, Homeomorph.isCompact_preimage]
    exact isCompact_Icc
  · ext x
    simp only [box, mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr, LinearMap.neg_apply,
      PiLp.projₗ_apply, neg_le_neg_iff, forall_and]
    exact and_comm

private theorem mem_box {a b : Fin 3 → ℝ} {x : ℝ³} :
    x ∈ box a b ↔
      (a 0 ≤ x 0 ∧ x 0 ≤ b 0) ∧ (a 1 ≤ x 1 ∧ x 1 ≤ b 1) ∧ (a 2 ≤ x 2 ∧ x 2 ≤ b 2) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    exacts [h0, h1, h2]

private def slab (lo hi zlo zhi : ℝ) : Set ℝ³ :=
  {x | lo ≤ max |x 0| |x 1| ∧ max |x 0| |x 1| ≤ hi ∧ zlo ≤ x 2 ∧ x 2 ≤ zhi}

private theorem sq_annulus_iff {lo hi a b : ℝ} (hlo : 0 < lo) :
    (lo ≤ max |a| |b| ∧ max |a| |b| ≤ hi) ↔
      (lo ≤ a ∧ a ≤ hi ∧ -hi ≤ b ∧ b ≤ hi) ∨ (-hi ≤ a ∧ a ≤ -lo ∧ -hi ≤ b ∧ b ≤ hi) ∨
      (-hi ≤ a ∧ a ≤ hi ∧ lo ≤ b ∧ b ≤ hi) ∨ (-hi ≤ a ∧ a ≤ hi ∧ -hi ≤ b ∧ b ≤ -lo) := by
  rw [le_max_iff, max_le_iff, abs_le, abs_le, le_abs', le_abs']
  constructor
  · rintro ⟨(ha | ha) | (hb | hb), ⟨h1, h2⟩, h3, h4⟩
    · exact Or.inr (Or.inl ⟨h1, ha, h3, h4⟩)
    · exact Or.inl ⟨ha, h2, h3, h4⟩
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, hb⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, hb, h4⟩))
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨Or.inl (Or.inr h1), ⟨by linarith, h2⟩, h3, h4⟩
    · exact ⟨Or.inl (Or.inl h2), ⟨h1, by linarith⟩, h3, h4⟩
    · exact ⟨Or.inr (Or.inr h3), ⟨h1, h2⟩, by linarith, h4⟩
    · exact ⟨Or.inr (Or.inl h4), ⟨h1, h2⟩, h3, by linarith⟩

private theorem isPolyhedron_slab {lo : ℝ} (hlo : 0 < lo) (hi zlo zhi : ℝ) :
    IsPolyhedron (slab lo hi zlo zhi) := by
  have h : slab lo hi zlo zhi = box ![lo, -hi, zlo] ![hi, hi, zhi] ∪
      box ![-hi, -hi, zlo] ![-lo, hi, zhi] ∪ box ![-hi, lo, zlo] ![hi, hi, zhi] ∪
      box ![-hi, -hi, zlo] ![hi, -lo, zhi] := by
    ext x
    have hs : x ∈ slab lo hi zlo zhi ↔
        ((lo ≤ x 0 ∧ x 0 ≤ hi ∧ -hi ≤ x 1 ∧ x 1 ≤ hi) ∨
          (-hi ≤ x 0 ∧ x 0 ≤ -lo ∧ -hi ≤ x 1 ∧ x 1 ≤ hi) ∨
          (-hi ≤ x 0 ∧ x 0 ≤ hi ∧ lo ≤ x 1 ∧ x 1 ≤ hi) ∨
          (-hi ≤ x 0 ∧ x 0 ≤ hi ∧ -hi ≤ x 1 ∧ x 1 ≤ -lo)) ∧ (zlo ≤ x 2 ∧ x 2 ≤ zhi) :=
      and_assoc.symm.trans (and_congr_left' (sq_annulus_iff hlo))
    rw [hs, mem_union, mem_union, mem_union, mem_box, mem_box, mem_box, mem_box]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, or_and_right, and_assoc, or_assoc]
  rw [h]
  exact (((isPolyhedron_box _ _).union (isPolyhedron_box _ _)).union
    (isPolyhedron_box _ _)).union (isPolyhedron_box _ _)

private theorem sq_circle_iff {r z : ℝ} :
    max |r - 2| |z| = 1 ↔
      (1 ≤ r ∧ r ≤ 3 ∧ 1 ≤ z ∧ z ≤ 1) ∨ (1 ≤ r ∧ r ≤ 3 ∧ -1 ≤ z ∧ z ≤ -1) ∨
      (1 ≤ r ∧ r ≤ 1 ∧ -1 ≤ z ∧ z ≤ 1) ∨ (3 ≤ r ∧ r ≤ 3 ∧ -1 ≤ z ∧ z ≤ 1) := by
  rw [le_antisymm_iff, max_le_iff, le_max_iff, abs_le, abs_le, le_abs', le_abs']
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, (h | h) | (h | h)⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, h3, h4⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, h3, h4⟩))
    · exact Or.inr (Or.inl ⟨by linarith, by linarith, h3, h⟩)
    · exact Or.inl ⟨by linarith, by linarith, h, h4⟩
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨⟨⟨by linarith, by linarith⟩, by linarith, h4⟩, Or.inr (Or.inr h3)⟩
    · exact ⟨⟨⟨by linarith, by linarith⟩, h3, by linarith⟩, Or.inr (Or.inl h4)⟩
    · exact ⟨⟨⟨by linarith, by linarith⟩, h3, h4⟩, Or.inl (Or.inl (by linarith))⟩
    · exact ⟨⟨⟨by linarith, by linarith⟩, h3, h4⟩, Or.inl (Or.inr (by linarith))⟩

private theorem isPolyhedron_level : IsPolyhedron {x : ℝ³ | sqN (merOf x) = 1} := by
  have h : {x : ℝ³ | sqN (merOf x) = 1} = slab 1 3 1 1 ∪ slab 1 3 (-1) (-1) ∪
      slab 1 1 (-1) 1 ∪ slab 3 3 (-1) 1 := by
    ext x
    simp only [mem_ofPred_eq, slab, mem_union, sqN_merOf, sq_circle_iff, or_assoc]
  rw [h]
  exact (((isPolyhedron_slab one_pos _ _ _).union (isPolyhedron_slab one_pos _ _ _)).union
    (isPolyhedron_slab one_pos _ _ _)).union (isPolyhedron_slab (by norm_num) _ _ _)

end

theorem exists_polyhedral_bicollar_model :
    ∃ Φ : OpenPartialHomeomorph (GC.Topology.Torus × ℝ) (EuclideanSpace ℝ (Fin 3)),
      Φ.source = {p | -1 < p.2 ∧ p.2 < 1} ∧ IsPolyhedron (Set.range fun t => Φ (t, 0)) := by
  refine ⟨chart, rfl, ?_⟩
  rw [range_chart_level]
  exact isPolyhedron_level

end DifferentialGeometry.Topology.PiecewiseLinear
