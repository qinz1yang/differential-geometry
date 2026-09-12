import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Collar

noncomputable section

open scoped Manifold ContDiff Topology

open Topology

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N]

namespace ConnectedSumQuotient

abbrev SeamShell : Set (EuclideanSpace ℝ (Fin 3)) := {x | (1/2 : ℝ) < ‖x‖ ∧ ‖x‖ < 3/2}

abbrev Seam : Type := {x : EuclideanSpace ℝ (Fin 3) // x ∈ SeamShell}

abbrev OuterSeam : Type := {x : EuclideanSpace ℝ (Fin 3) // 1 ≤ ‖x‖ ∧ ‖x‖ < 3/2}

abbrev InnerSeam : Type := {x : EuclideanSpace ℝ (Fin 3) // (1/2 : ℝ) < ‖x‖ ∧ ‖x‖ < 1}

theorem isOpen_seamShell : IsOpen SeamShell :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

def unitVec (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨(‖x‖)⁻¹ • x, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

@[simp]
theorem unitVec_val (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    ((unitVec x hx : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) = (‖x‖)⁻¹ • x := rfl

theorem norm_unitVec (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    ‖((unitVec x hx : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))‖ = 1 := by
  rw [unitVec_val, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem smul_unitVec (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    ‖x‖ • ((unitVec x hx : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) = x := by
  rw [unitVec_val, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem norm_smul_unitVec (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    ‖r • ((unitVec x hx : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
    norm_unitVec x hx, mul_one]

theorem unitVec_eq_of_smul_eq {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) (hy : y ≠ 0)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : r • ((unitVec x hx : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) =
      s • ((unitVec y hy : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))) :
    (unitVec x hx : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      unitVec y hy := by
  have hr' : r = s := by
    have h1 : ‖r • ((unitVec x hx : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))‖ =
        ‖s • ((unitVec y hy : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3))‖ := by rw [h]
    rwa [norm_smul_unitVec x hx r hr.le, norm_smul_unitVec y hy s hs.le] at h1
  have h2 := h
  rw [hr'] at h2
  have h3 := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => s⁻¹ • w) h2
  simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul] at h3
  exact Subtype.ext h3

theorem continuous_radialFamily' {α : Type*} [TopologicalSpace α]
    (c : BallChart 3 I M)
    (z : α → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (r : α → ℝ)
    (hz : Continuous z) (hr : Continuous r) (h1 : ∀ p, 1 ≤ r p) (h2 : ∀ p, r p ≤ 2) :
    Continuous fun p => c.radialMap (z p) (r p) ⟨h1 p, h2 p⟩ := by
  have hsmul : Continuous fun p : α =>
      r p • ((z p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) :=
    hr.smul (continuous_subtype_val.comp hz)
  have hsrc : ∀ p : α,
      r p • ((z p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) ∈ c.chart.source := by
    intro p
    refine mem_chart_source_of_norm_le_two c ?_
    have hz1 : ‖((z p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using (z p).2
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (h1 p)), hz1, mul_one]
    exact h2 p
  have hchart : Continuous fun p : α =>
      (⟨c.chart (r p • ((z p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3))),
        (c.radialMap (z p) (r p) ⟨h1 p, h2 p⟩).2⟩ : c.Punctured) :=
    ((c.chart.contMDiffOn_toFun.continuousOn.comp_continuous hsmul hsrc)).subtype_mk _
  convert hchart using 1
  funext p
  exact Subtype.ext rfl

theorem seam_ne_zero (x : Seam) : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
  intro h
  have h1 := x.2.1
  rw [h, norm_zero] at h1
  norm_num at h1

def seamDir (x : Seam) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  unitVec (x : EuclideanSpace ℝ (Fin 3)) (seam_ne_zero x)

theorem continuous_seamDir : Continuous (seamDir : Seam → _) := by
  have hnorm : Continuous fun x : Seam => ‖(x : EuclideanSpace ℝ (Fin 3))‖ :=
    continuous_norm.comp continuous_subtype_val
  have hinv : Continuous fun x : Seam => (‖(x : EuclideanSpace ℝ (Fin 3))‖)⁻¹ :=
    hnorm.inv₀ fun x => norm_ne_zero_iff.mpr (seam_ne_zero x)
  have hval : Continuous fun x : Seam =>
      ((‖(x : EuclideanSpace ℝ (Fin 3))‖)⁻¹ • (x : EuclideanSpace ℝ (Fin 3))) :=
    hinv.smul continuous_subtype_val
  have hmem : ∀ x : Seam, ((‖(x : EuclideanSpace ℝ (Fin 3))‖)⁻¹ •
      (x : EuclideanSpace ℝ (Fin 3))) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro x
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr (seam_ne_zero x))]
  have := hval.subtype_mk hmem
  convert this using 1
  funext x
  exact Subtype.ext rfl

theorem continuous_seamDir_comp
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Continuous fun x : Seam => a (seamDir x) :=
  a.continuous.comp continuous_seamDir

variable (c : BallChart 3 I M) (d : BallChart 3 J N)
  (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

def seamLeft : Seam → ConnectedSumQuotient c d a := fun x =>
  inl c d a (c.radialMap (seamDir x) (max 1 ‖(x : EuclideanSpace ℝ (Fin 3))‖) (by
    refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
    linarith [x.2.2]))

def seamRight : Seam → ConnectedSumQuotient c d a := fun x =>
  inr c d a (d.radialMap (a (seamDir x)) (max 1 (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖)) (by
    refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
    linarith [x.2.1]))

theorem continuous_seamLeft : Continuous (seamLeft c d a) :=
  (continuous_inl c d a).comp
    (continuous_radialFamily' c (fun x : Seam => seamDir x)
      (fun x : Seam => max 1 ‖(x : EuclideanSpace ℝ (Fin 3))‖)
      continuous_seamDir (continuous_const.max (continuous_norm.comp continuous_subtype_val))
      (fun x => le_max_left _ _) (fun x => by
        refine max_le (by norm_num) ?_
        linarith [x.2.2]))

theorem continuous_seamRight : Continuous (seamRight c d a) :=
  (continuous_inr c d a).comp
    (continuous_radialFamily' d (fun x : Seam => a (seamDir x))
      (fun x : Seam => max 1 (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖))
      (continuous_seamDir_comp a)
      (continuous_const.max (continuous_const.sub (continuous_norm.comp continuous_subtype_val)))
      (fun x => le_max_left _ _) (fun x => by
        refine max_le (by norm_num) ?_
        linarith [x.2.1]))

def seamMap : Seam → ConnectedSumQuotient c d a := fun x =>
  if 1 ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖ then seamLeft c d a x else seamRight c d a x

theorem frontier_seam_cut :
    frontier {x : Seam | (1 : ℝ) ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖} ⊆
      {x : Seam | ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1} := by
  have h := frontier_half_le_subset_eq_zero
    (fun x : Seam => ‖(x : EuclideanSpace ℝ (Fin 3))‖ - 1)
    (continuous_norm.comp continuous_subtype_val |>.sub continuous_const)
  simpa [sub_nonneg, sub_eq_zero] using h

theorem seamLeft_eq_of_one_le (x : Seam) (h : 1 ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖) :
    seamLeft c d a x = inl c d a (c.radialMap (seamDir x) ‖(x : EuclideanSpace ℝ (Fin 3))‖
      ⟨h, by linarith [x.2.2]⟩) := by
  unfold seamLeft
  congr 1
  apply Subtype.ext
  change c.chart ((max 1 ‖(x : EuclideanSpace ℝ (Fin 3))‖) •
      ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))) =
    c.chart (‖(x : EuclideanSpace ℝ (Fin 3))‖ •
      ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)))
  rw [max_eq_right h]

theorem seamRight_eq_of_lt_one (x : Seam) (h : ‖(x : EuclideanSpace ℝ (Fin 3))‖ < 1) :
    seamRight c d a x = inr c d a (d.radialMap (a (seamDir x))
      (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖) ⟨by linarith, by linarith [x.2.1]⟩) := by
  unfold seamRight
  congr 1
  apply Subtype.ext
  change d.chart ((max 1 (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖)) •
      ((a (seamDir x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))) =
    d.chart ((2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖) •
      ((a (seamDir x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)))
  rw [max_eq_right (by linarith : (1 : ℝ) ≤ 2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖)]

theorem seamLeft_eq_boundary (x : Seam) (hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1) :
    seamLeft c d a x = inl c d a (c.boundaryMap (seamDir x)) := by
  rw [seamLeft_eq_of_one_le c d a x (le_of_eq hx.symm)]
  congr 1
  apply Subtype.ext
  change c.chart (‖(x : EuclideanSpace ℝ (Fin 3))‖ •
      ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))) =
    c.chart (((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)))
  rw [hx]
  simp

theorem seamRight_eq_boundary (x : Seam) (hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1) :
    seamRight c d a x = inr c d a (d.boundaryMap (a (seamDir x))) := by
  unfold seamRight
  congr 1
  apply Subtype.ext
  change d.chart ((max 1 (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖)) •
      ((a (seamDir x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))) =
    d.chart (((a (seamDir x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)))
  rw [hx]
  norm_num

theorem seamLeft_eq_seamRight_of_norm_eq_one (x : Seam)
    (hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1) :
    seamLeft c d a x = seamRight c d a x := by
  rw [seamLeft_eq_boundary c d a x hx, seamRight_eq_boundary c d a x hx]
  exact boundary_eq c d a (seamDir x)

theorem seamMap_of_one_le (x : Seam) (h : 1 ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖) :
    seamMap c d a x = seamLeft c d a x := by
  unfold seamMap
  rw [if_pos h]

theorem seamMap_of_lt_one (x : Seam) (h : ¬ 1 ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖) :
    seamMap c d a x = seamRight c d a x := by
  unfold seamMap
  rw [if_neg h]

theorem continuous_seamMap : Continuous (seamMap c d a) := by
  have h : seamMap c d a = fun x : Seam =>
      if 1 ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖ then seamLeft c d a x else seamRight c d a x := rfl
  rw [h]
  refine continuous_if ?_ ((continuous_seamLeft c d a).continuousOn.mono (Set.subset_univ _))
    ((continuous_seamRight c d a).continuousOn.mono (Set.subset_univ _))
  intro x hx
  exact seamLeft_eq_seamRight_of_norm_eq_one c d a x (frontier_seam_cut hx)

theorem norm_smul_seamDir (x : Seam) {r : ℝ} (hr : 0 ≤ r) :
    ‖r • ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))‖ = r :=
  norm_smul_unitVec _ (seam_ne_zero x) r hr

theorem norm_coe_sphere (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ‖((z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using z.2

theorem coe_sphere_mem_source (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ((z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) ∈ c.chart.source :=
  mem_chart_source_of_norm_le_two c (by rw [norm_coe_sphere]; norm_num)

theorem smul_coe_sphere_mem_source (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2) :
    r • ((z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) ∈ c.chart.source :=
  mem_chart_source_of_norm_le_two c (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one h1), norm_coe_sphere,
      mul_one]
    exact h2)

theorem seamDir_eq_of_smul_eq {r s : ℝ} {x y : Seam} (hr : 0 < r) (hs : 0 < s)
    (h : r • ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) =
      s • ((seamDir y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))) :
    r = s ∧ ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) =
      ((seamDir y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) := by
  have hrs : r = s := by
    have h1 : ‖r • ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))‖ =
        ‖s • ((seamDir y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3))‖ := by rw [h]
    rwa [norm_smul_seamDir x hr.le, norm_smul_seamDir y hs.le] at h1
  refine ⟨hrs, ?_⟩
  have h2 := h
  rw [hrs] at h2
  have h3 := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => s⁻¹ • w) h2
  simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul] using h3

theorem eq_of_norm_eq_of_seamDir_eq {x y : Seam}
    (hn : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = ‖(y : EuclideanSpace ℝ (Fin 3))‖)
    (h : ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) =
      ((seamDir y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))) :
    x = y := by
  refine Subtype.ext ?_
  calc (x : EuclideanSpace ℝ (Fin 3))
      = ‖(x : EuclideanSpace ℝ (Fin 3))‖ •
        ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)) := (smul_unitVec _ (seam_ne_zero x)).symm
    _ = ‖(y : EuclideanSpace ℝ (Fin 3))‖ •
        ((seamDir y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)) := by rw [hn, h]
    _ = (y : EuclideanSpace ℝ (Fin 3)) := smul_unitVec _ (seam_ne_zero y)

theorem eq_of_smul_sphereMap_eq {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    {u v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (h : t • ((a u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) =
      s • ((a v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))) :
    t = s ∧ u = v := by
  have hts : t = s := by
    have h1 : ‖t • ((a u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))‖ =
        ‖s • ((a v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3))‖ := by rw [h]
    rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.le, norm_coe_sphere, mul_one,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.le, norm_coe_sphere, mul_one] at h1
  refine ⟨hts, ?_⟩
  have h2 := h
  rw [← hts] at h2
  have h3 := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => t⁻¹ • w) h2
  have h4 : ((a u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) =
      ((a v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) := by
    simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul] using h3
  exact a.injective (Subtype.ext h4)

theorem seamDir_eq_of_radialMap_eq (x y : Seam) (hx : 1 ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖)
    (hy : 1 ≤ ‖(y : EuclideanSpace ℝ (Fin 3))‖)
    (h : c.radialMap (seamDir x) ‖(x : EuclideanSpace ℝ (Fin 3))‖
        ⟨hx, by linarith [x.2.2]⟩ =
      c.radialMap (seamDir y) ‖(y : EuclideanSpace ℝ (Fin 3))‖
        ⟨hy, by linarith [y.2.2]⟩) :
    x = y := by
  have hchart : c.chart (‖(x : EuclideanSpace ℝ (Fin 3))‖ •
      ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))) =
      c.chart (‖(y : EuclideanSpace ℝ (Fin 3))‖ •
        ((seamDir y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))) := by
    exact congrArg Subtype.val h
  have hv : ‖(x : EuclideanSpace ℝ (Fin 3))‖ •
      ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) =
      ‖(y : EuclideanSpace ℝ (Fin 3))‖ •
        ((seamDir y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) :=
    c.chart.toPartialEquiv.injOn
      (smul_coe_sphere_mem_source c (seamDir x) hx (by linarith [x.2.2]))
      (smul_coe_sphere_mem_source c (seamDir y) hy (by linarith [y.2.2]))
      hchart
  obtain ⟨hrs, hd⟩ := seamDir_eq_of_smul_eq (by linarith) (by linarith) hv
  exact eq_of_norm_eq_of_seamDir_eq hrs hd

theorem eq_of_radialMap_eq_of_lt_one (x y : Seam) (hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ < 1)
    (hy : ‖(y : EuclideanSpace ℝ (Fin 3))‖ < 1)
    (h : d.radialMap (a (seamDir x)) (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖)
        ⟨by linarith, by have h := norm_nonneg (x : EuclideanSpace ℝ (Fin 3)); linarith⟩ =
      d.radialMap (a (seamDir y)) (2 - ‖(y : EuclideanSpace ℝ (Fin 3))‖)
        ⟨by linarith, by have h := norm_nonneg (y : EuclideanSpace ℝ (Fin 3)); linarith⟩) :
    x = y := by
  have hchart : d.chart ((2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖) •
      ((a (seamDir x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))) =
      d.chart ((2 - ‖(y : EuclideanSpace ℝ (Fin 3))‖) •
        ((a (seamDir y) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3))) := by
    exact congrArg Subtype.val h
  have hv : (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖) •
      ((a (seamDir x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) =
      (2 - ‖(y : EuclideanSpace ℝ (Fin 3))‖) •
        ((a (seamDir y) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)) :=
    d.chart.toPartialEquiv.injOn
      (smul_coe_sphere_mem_source d (a (seamDir x)) (by linarith)
        (by have h := norm_nonneg (x : EuclideanSpace ℝ (Fin 3)); linarith))
      (smul_coe_sphere_mem_source d (a (seamDir y)) (by linarith)
        (by have h := norm_nonneg (y : EuclideanSpace ℝ (Fin 3)); linarith))
      hchart
  obtain ⟨hrs, huv⟩ := eq_of_smul_sphereMap_eq a (t := 2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖)
    (s := 2 - ‖(y : EuclideanSpace ℝ (Fin 3))‖) (by linarith [x.2.2]) (by linarith [y.2.2]) hv
  exact eq_of_norm_eq_of_seamDir_eq (by linarith) (congrArg Subtype.val huv)

theorem seamMap_injective : Function.Injective (seamMap c d a) := by
  intro x y hxy
  by_cases hx : 1 ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖
  · by_cases hy : 1 ≤ ‖(y : EuclideanSpace ℝ (Fin 3))‖
    · rw [seamMap_of_one_le c d a x hx, seamMap_of_one_le c d a y hy,
        seamLeft_eq_of_one_le c d a x hx, seamLeft_eq_of_one_le c d a y hy] at hxy
      exact seamDir_eq_of_radialMap_eq c x y hx hy (inl_injective c d a hxy)
    · have hy' : ‖(y : EuclideanSpace ℝ (Fin 3))‖ < 1 := not_le.mp hy
      rw [seamMap_of_one_le c d a x hx, seamMap_of_lt_one c d a y hy,
        seamLeft_eq_of_one_le c d a x hx, seamRight_eq_of_lt_one c d a y hy'] at hxy
      obtain ⟨z, hz, hz'⟩ := (inl_eq_inr_iff c d a _ _).mp hxy
      have hzx : ((z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)) =
          ‖(x : EuclideanSpace ℝ (Fin 3))‖ •
            ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
              EuclideanSpace ℝ (Fin 3)) :=
        c.chart.toPartialEquiv.injOn (coe_sphere_mem_source c z)
          (smul_coe_sphere_mem_source c (seamDir x) hx (by linarith [x.2.2]))
          (congrArg Subtype.val hz)
      have hzy : ((a z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)) =
          (2 - ‖(y : EuclideanSpace ℝ (Fin 3))‖) •
            ((a (seamDir y) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
              EuclideanSpace ℝ (Fin 3)) :=
        d.chart.toPartialEquiv.injOn (coe_sphere_mem_source d (a z))
          (smul_coe_sphere_mem_source d (a (seamDir y)) (by linarith [hy'])
            (by have h := norm_nonneg (y : EuclideanSpace ℝ (Fin 3)); linarith))
          (congrArg Subtype.val hz')
      have h1 : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
        have hnorm := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => ‖w‖) hzx
        rw [norm_coe_sphere] at hnorm
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_coe_sphere,
          mul_one] at hnorm
        exact hnorm.symm
      have h2 : ‖(y : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
        have hnorm := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => ‖w‖) hzy
        rw [norm_coe_sphere, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith),
          norm_coe_sphere, mul_one] at hnorm
        linarith
      linarith
  · have hx' : ‖(x : EuclideanSpace ℝ (Fin 3))‖ < 1 := not_le.mp hx
    by_cases hy : 1 ≤ ‖(y : EuclideanSpace ℝ (Fin 3))‖
    · rw [seamMap_of_lt_one c d a x hx, seamMap_of_one_le c d a y hy,
        seamRight_eq_of_lt_one c d a x hx', seamLeft_eq_of_one_le c d a y hy] at hxy
      obtain ⟨z, hz, hz'⟩ := (inl_eq_inr_iff c d a _ _).mp hxy.symm
      have hzy : ((z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)) =
          ‖(y : EuclideanSpace ℝ (Fin 3))‖ •
            ((seamDir y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
              EuclideanSpace ℝ (Fin 3)) :=
        c.chart.toPartialEquiv.injOn (coe_sphere_mem_source c z)
          (smul_coe_sphere_mem_source c (seamDir y) hy (by linarith [y.2.2]))
          (congrArg Subtype.val hz)
      have hzx : ((a z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)) =
          (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖) •
            ((a (seamDir x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
              EuclideanSpace ℝ (Fin 3)) :=
        d.chart.toPartialEquiv.injOn (coe_sphere_mem_source d (a z))
          (smul_coe_sphere_mem_source d (a (seamDir x)) (by linarith [hx'])
            (by have h := norm_nonneg (x : EuclideanSpace ℝ (Fin 3)); linarith))
          (congrArg Subtype.val hz')
      have h1 : ‖(y : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
        have hnorm := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => ‖w‖) hzy
        rw [norm_coe_sphere] at hnorm
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_coe_sphere,
          mul_one] at hnorm
        exact hnorm.symm
      have h2 : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
        have hnorm := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => ‖w‖) hzx
        rw [norm_coe_sphere, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith),
          norm_coe_sphere, mul_one] at hnorm
        linarith
      linarith
    · have hy' : ‖(y : EuclideanSpace ℝ (Fin 3))‖ < 1 := not_le.mp hy
      rw [seamMap_of_lt_one c d a x hx, seamMap_of_lt_one c d a y hy,
        seamRight_eq_of_lt_one c d a x hx', seamRight_eq_of_lt_one c d a y hy'] at hxy
      exact eq_of_radialMap_eq_of_lt_one d a x y hx' hy' (inr_injective c d a hxy)

noncomputable def unitVecFun (x : EuclideanSpace ℝ (Fin 3)) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  if hx : x = 0 then ⟨EuclideanSpace.single 0 (1 : ℝ), by
    rw [Metric.mem_sphere, dist_zero_right]
    simp⟩
  else unitVec x hx

theorem unitVecFun_of_ne {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    unitVecFun x = unitVec x hx := by
  simp only [unitVecFun, dif_neg hx]

theorem continuous_unitVecFun_subtype :
    Continuous fun x : {x : EuclideanSpace ℝ (Fin 3) // x ≠ 0} =>
      unitVecFun (x : EuclideanSpace ℝ (Fin 3)) := by
  have hcongr : (fun x : {x : EuclideanSpace ℝ (Fin 3) // x ≠ 0} =>
      unitVecFun (x : EuclideanSpace ℝ (Fin 3))) =
      fun x : {x : EuclideanSpace ℝ (Fin 3) // x ≠ 0} =>
        unitVec (x : EuclideanSpace ℝ (Fin 3)) x.2 := by
    funext x
    exact unitVecFun_of_ne x.2
  rw [hcongr]
  have hval : Continuous fun x : {x : EuclideanSpace ℝ (Fin 3) // x ≠ 0} =>
      ((‖(x : EuclideanSpace ℝ (Fin 3))‖)⁻¹ • (x : EuclideanSpace ℝ (Fin 3))) :=
    ((continuous_norm.comp continuous_subtype_val).inv₀
      (fun x => norm_ne_zero_iff.mpr x.2)).smul continuous_subtype_val
  have hmem : ∀ x : {x : EuclideanSpace ℝ (Fin 3) // x ≠ 0},
      ((‖(x : EuclideanSpace ℝ (Fin 3))‖)⁻¹ • (x : EuclideanSpace ℝ (Fin 3))) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro x
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr x.2)]
  have := hval.subtype_mk hmem
  convert this using 1
  funext x
  exact Subtype.ext rfl

theorem continuousOn_unitVecFun :
    ContinuousOn unitVecFun {x : EuclideanSpace ℝ (Fin 3) | x ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_unitVecFun_subtype

noncomputable def reflectMap
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (2 - ‖x‖) • ((a (unitVecFun x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3))

noncomputable def reflectMapInv
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (2 - ‖x‖) • ((a.symm (unitVecFun x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3))

theorem continuousOn_reflectMap
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ContinuousOn (reflectMap a) {x : EuclideanSpace ℝ (Fin 3) | x ≠ 0} := by
  have h1 : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => a (unitVecFun x))
      {x : EuclideanSpace ℝ (Fin 3) | x ≠ 0} :=
    a.continuous.comp_continuousOn continuousOn_unitVecFun
  have h2 : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) =>
      ((a (unitVecFun x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))) {x : EuclideanSpace ℝ (Fin 3) | x ≠ 0} :=
    continuous_subtype_val.comp_continuousOn h1
  have h3 : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => (2 : ℝ) - ‖x‖)
      {x : EuclideanSpace ℝ (Fin 3) | x ≠ 0} :=
    (continuous_const.sub continuous_norm).continuousOn
  exact h3.smul h2

theorem continuousOn_reflectMapInv
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ContinuousOn (reflectMapInv a) {x : EuclideanSpace ℝ (Fin 3) | x ≠ 0} := by
  have h1 : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => a.symm (unitVecFun x))
      {x : EuclideanSpace ℝ (Fin 3) | x ≠ 0} :=
    a.symm.continuous.comp_continuousOn continuousOn_unitVecFun
  have h2 : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) =>
      ((a.symm (unitVecFun x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))) {x : EuclideanSpace ℝ (Fin 3) | x ≠ 0} :=
    continuous_subtype_val.comp_continuousOn h1
  have h3 : ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => (2 : ℝ) - ‖x‖)
      {x : EuclideanSpace ℝ (Fin 3) | x ≠ 0} :=
    (continuous_const.sub continuous_norm).continuousOn
  exact h3.smul h2

theorem norm_reflectMap {a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ ≤ 2) : ‖reflectMap a x‖ = 2 - ‖x‖ := by
  rw [reflectMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_coe_sphere,
    mul_one]

theorem norm_reflectMapInv {a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ ≤ 2) : ‖reflectMapInv a x‖ = 2 - ‖x‖ := by
  rw [reflectMapInv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_coe_sphere,
    mul_one]

theorem unitVecFun_seamDir (x : Seam) : unitVecFun (x : EuclideanSpace ℝ (Fin 3)) = seamDir x := by
  rw [unitVecFun_of_ne (seam_ne_zero x)]
  rfl

theorem reflectMap_seamDir
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (x : Seam) :
    reflectMap a (x : EuclideanSpace ℝ (Fin 3)) =
      (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖) •
        ((a (seamDir x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)) := by
  rw [reflectMap, unitVecFun_seamDir x]

theorem reflectMapInv_reflectMap
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (x : Seam) :
    reflectMapInv a (reflectMap a (x : EuclideanSpace ℝ (Fin 3))) =
      (x : EuclideanSpace ℝ (Fin 3)) := by
  have hle : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ≤ 2 := by linarith [x.2.2]
  have hnorm : ‖reflectMap a (x : EuclideanSpace ℝ (Fin 3))‖ =
      2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖ := norm_reflectMap hle
  have hpos : 0 < 2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖ := by linarith [x.2.2]
  have hne : reflectMap a (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    linarith
  have hunit : unitVecFun (reflectMap a (x : EuclideanSpace ℝ (Fin 3))) =
      a (unitVecFun (x : EuclideanSpace ℝ (Fin 3))) := by
    refine Subtype.ext ?_
    rw [unitVecFun_of_ne hne, unitVec_val, hnorm, reflectMap, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hpos), one_smul]
  rw [reflectMapInv, hunit, hnorm]
  rw [show 2 - (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖) = ‖(x : EuclideanSpace ℝ (Fin 3))‖ from by
    ring]
  rw [a.symm_apply_apply]
  rw [unitVecFun_of_ne (seam_ne_zero x)]
  exact smul_unitVec _ (seam_ne_zero x)

theorem reflectMap_reflectMapInv
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (x : Seam) :
    reflectMap a (reflectMapInv a (x : EuclideanSpace ℝ (Fin 3))) =
      (x : EuclideanSpace ℝ (Fin 3)) := by
  have hle : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ≤ 2 := by linarith [x.2.2]
  have hnorm : ‖reflectMapInv a (x : EuclideanSpace ℝ (Fin 3))‖ =
      2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖ := norm_reflectMapInv hle
  have hpos : 0 < 2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖ := by linarith [x.2.2]
  have hne : reflectMapInv a (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    linarith
  have hunit : unitVecFun (reflectMapInv a (x : EuclideanSpace ℝ (Fin 3))) =
      a.symm (unitVecFun (x : EuclideanSpace ℝ (Fin 3))) := by
    refine Subtype.ext ?_
    rw [unitVecFun_of_ne hne, unitVec_val, hnorm, reflectMapInv, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hpos), one_smul]
  rw [reflectMap, hunit, hnorm,
    show 2 - (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖) = ‖(x : EuclideanSpace ℝ (Fin 3))‖ from by
      ring]
  rw [a.apply_symm_apply, unitVecFun_of_ne (seam_ne_zero x)]
  exact smul_unitVec _ (seam_ne_zero x)

theorem smul_seamDir (x : Seam) :
    ‖(x : EuclideanSpace ℝ (Fin 3))‖ •
      ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) = (x : EuclideanSpace ℝ (Fin 3)) :=
  smul_unitVec _ (seam_ne_zero x)

theorem chart_mem_punctured (c : BallChart 3 I M) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ c.chart.source) (hx1 : 1 ≤ ‖x‖) :
    c.chart x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rintro ⟨y, hy, h⟩
  have hyx : y = x := c.chart.toPartialEquiv.injOn (c.ball_subset_source hy) hx h
  rw [hyx] at hy
  have := Metric.mem_ball.mp hy
  rw [dist_zero_right] at this
  linarith

theorem coe_seamDir_eq (x : Seam) :
    ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3)) = (‖(x : EuclideanSpace ℝ (Fin 3))‖)⁻¹ •
        (x : EuclideanSpace ℝ (Fin 3)) := by
  simp only [seamDir, unitVec_val]

theorem unitVecFun_coe_sphere (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    unitVecFun (z : EuclideanSpace ℝ (Fin 3)) = z := by
  have hz : (z : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    have := norm_coe_sphere z
    rw [h, norm_zero] at this
    norm_num at this
  rw [unitVecFun_of_ne hz]
  apply Subtype.ext
  rw [unitVec_val, norm_coe_sphere, inv_one, one_smul]

theorem reflectMap_coe_sphere
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    reflectMap a (z : EuclideanSpace ℝ (Fin 3)) =
      ((a z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3)) := by
  rw [reflectMap, unitVecFun_coe_sphere, norm_coe_sphere]
  norm_num

theorem reflectMapInv_coe_sphere
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    reflectMapInv a (z : EuclideanSpace ℝ (Fin 3)) =
      ((a.symm z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) := by
  rw [reflectMapInv, unitVecFun_coe_sphere, norm_coe_sphere]
  norm_num

theorem reflectMap_mem_source (d : BallChart 3 J N)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (x : Seam) :
    reflectMap a (x : EuclideanSpace ℝ (Fin 3)) ∈ d.chart.source := by
  refine mem_chart_source_of_norm_le_two d ?_
  rw [norm_reflectMap (by linarith [x.2.2])]
  have h := norm_nonneg (x : EuclideanSpace ℝ (Fin 3))
  linarith [x.2.2]

theorem radialMap_seamDir_eq (c : BallChart 3 I M) (x : Seam)
    (h : 1 ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖) :
    c.radialMap (seamDir x) ‖(x : EuclideanSpace ℝ (Fin 3))‖
        ⟨h, by linarith [x.2.2]⟩ =
      ⟨c.chart (x : EuclideanSpace ℝ (Fin 3)), chart_mem_punctured c
        (mem_chart_source_of_norm_le_two c (by linarith [x.2.2])) h⟩ := by
  apply Subtype.ext
  change c.chart (‖(x : EuclideanSpace ℝ (Fin 3))‖ •
    ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))) = c.chart (x : EuclideanSpace ℝ (Fin 3))
  rw [smul_seamDir x]

theorem radialMap_a_seamDir_eq (d : BallChart 3 J N)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (x : Seam)
    (h : ‖(x : EuclideanSpace ℝ (Fin 3))‖ < 1) :
    d.radialMap (a (seamDir x)) (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖)
        ⟨by linarith, by linarith [x.2.1]⟩ =
      ⟨d.chart (reflectMap a (x : EuclideanSpace ℝ (Fin 3))),
        chart_mem_punctured d (reflectMap_mem_source d a x) (by
          rw [norm_reflectMap (by linarith [x.2.2])]; linarith)⟩ := by
  apply Subtype.ext
  change d.chart ((2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖) •
    ((a (seamDir x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))) = d.chart (reflectMap a (x : EuclideanSpace ℝ (Fin 3)))
  rw [reflectMap_seamDir a x]

theorem radialMap_seamDir_coe (c : BallChart 3 I M) (x : Seam)
    (h : 1 ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖) :
    (c.radialMap (seamDir x) ‖(x : EuclideanSpace ℝ (Fin 3))‖
      ⟨h, by linarith [x.2.2]⟩ : M) = c.chart (x : EuclideanSpace ℝ (Fin 3)) :=
  congrArg Subtype.val (radialMap_seamDir_eq c x h)

theorem radialMap_a_seamDir_coe (d : BallChart 3 J N)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (x : Seam)
    (h : ‖(x : EuclideanSpace ℝ (Fin 3))‖ < 1) :
    (d.radialMap (a (seamDir x)) (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖)
      ⟨by linarith, by linarith [x.2.1]⟩ : N) =
      d.chart (reflectMap a (x : EuclideanSpace ℝ (Fin 3))) :=
  congrArg Subtype.val (radialMap_a_seamDir_eq d a x h)

def outerSeamImage (c : BallChart 3 I M) (W : Set Seam) : Set c.Punctured :=
  {p | (p : M) ∈ c.chart.toOpenPartialHomeomorph '' (Subtype.val '' W)}

theorem isOpen_image_union_of_boundary_iff {n : ℕ} (c : BallChart n I M) (d : BallChart n J N)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {U : Set c.Punctured} {V : Set d.Punctured} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : ∀ z, c.boundaryMap z ∈ U ↔ d.boundaryMap (a z) ∈ V) :
    IsOpen (inl c d a '' U ∪ inr c d a '' V) := by
  have hcoe : (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) ⁻¹'
      (inl c d a '' U ∪ inr c d a '' V) = Sum.inl '' U ∪ Sum.inr '' V := by
    ext s
    constructor
    · rintro (⟨p, hpU, hp⟩ | ⟨q, hqV, hq⟩)
      · cases s with
        | inl x =>
            refine Or.inl ⟨x, ?_, rfl⟩
            rwa [← (inl_injective c d a hp)]
        | inr y =>
            obtain ⟨z, hz, hz'⟩ := (inl_eq_inr_iff c d a p y).mp hp
            refine Or.inr ⟨y, ?_, rfl⟩
            have hpU' : c.boundaryMap z ∈ U := by rwa [hz]
            have hV' : d.boundaryMap (a z) ∈ V := (hUV z).mp hpU'
            rwa [hz'] at hV'
      · cases s with
        | inl x =>
            obtain ⟨z, hz, hz'⟩ := (inl_eq_inr_iff c d a x q).mp hq.symm
            refine Or.inl ⟨x, ?_, rfl⟩
            have hV' : d.boundaryMap (a z) ∈ V := by rwa [hz']
            have hU' : c.boundaryMap z ∈ U := (hUV z).mpr hV'
            rwa [hz] at hU'
        | inr y =>
            refine Or.inr ⟨y, ?_, rfl⟩
            rwa [← (inr_injective c d a hq)]
    · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨y, hy, rfl⟩
  change IsOpen[TopologicalSpace.coinduced
    (adjunctionMk c.boundaryMap (d.boundaryMap ∘ a)) inferInstance]
    (inl c d a '' U ∪ inr c d a '' V)
  rw [isOpen_coinduced, hcoe]
  exact (isOpenMap_inl U hU).union (isOpenMap_inr V hV)

def innerSeamImage (d : BallChart 3 J N)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (W : Set Seam) :
    Set d.Punctured :=
  {q | (q : N) ∈ d.chart.toOpenPartialHomeomorph ''
    (reflectMap a '' (Subtype.val '' W))}

theorem one_le_norm_of_chart_eq (c : BallChart 3 I M)
    {x : EuclideanSpace ℝ (Fin 3)} {p : c.Punctured}
    (hp : c.chart x = (p : M)) : 1 ≤ ‖x‖ := by
  by_contra h
  exact p.2 ⟨x, by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_not_ge h, hp⟩

theorem continuousOn_reflectMapInv_shell
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ContinuousOn (reflectMapInv a) SeamShell :=
  (continuousOn_reflectMapInv a).mono fun x hx => by
    intro h0
    have hx1 : (1 / 2 : ℝ) < ‖x‖ := hx.1
    rw [h0, norm_zero] at hx1
    linarith

theorem isOpen_outerSeamImage (c : BallChart 3 I M) (W : Set Seam) (hW : IsOpen W) :
    IsOpen (outerSeamImage c W) := by
  have hWz : IsOpen (Subtype.val '' W) := isOpen_seamShell.isOpenMap_subtype_val W hW
  have hsub : Subtype.val '' W ⊆ c.chart.toOpenPartialHomeomorph.source := by
    rintro y ⟨x, -, rfl⟩
    exact mem_chart_source_of_norm_le_two c (by linarith [x.2.2])
  have himg : IsOpen (c.chart.toOpenPartialHomeomorph '' (Subtype.val '' W)) :=
    c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source hWz hsub
  exact himg.preimage continuous_subtype_val

theorem isOpen_reflectMap_image (W : Set Seam) (hW : IsOpen W) :
    IsOpen (reflectMap a '' (Subtype.val '' W)) := by
  have hWz : IsOpen (Subtype.val '' W) := isOpen_seamShell.isOpenMap_subtype_val W hW
  have hshell : Subtype.val '' W ⊆ SeamShell := by
    rintro y ⟨x, -, rfl⟩
    exact x.2
  have hpre : IsOpen ({x : EuclideanSpace ℝ (Fin 3) | x ≠ 0} ∩
      (reflectMapInv a) ⁻¹' (Subtype.val '' W)) :=
    (continuousOn_reflectMapInv a).isOpen_inter_preimage isOpen_ne hWz
  have hpre' : IsOpen (SeamShell ∩ (reflectMapInv a) ⁻¹' (Subtype.val '' W)) :=
    (continuousOn_reflectMapInv_shell a).isOpen_inter_preimage isOpen_seamShell hWz
  have hset : reflectMap a '' (Subtype.val '' W) =
      SeamShell ∩ (reflectMapInv a) ⁻¹' (Subtype.val '' W) := by
    ext y
    constructor
    · rintro ⟨x, hxW, rfl⟩
      have hx := hshell hxW
      refine ⟨?_, ?_⟩
      · change (1 / 2 : ℝ) < ‖reflectMap a x‖ ∧ ‖reflectMap a x‖ < 3 / 2
        rw [norm_reflectMap (by linarith [hx.2])]
        exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
      · have h := reflectMapInv_reflectMap a ⟨x, hx⟩
        change reflectMapInv a (reflectMap a x) ∈ Subtype.val '' W
        rw [show reflectMapInv a (reflectMap a x) = x from h]
        exact hxW
    · rintro ⟨hyshell, hyW⟩
      refine ⟨reflectMapInv a y, hyW, ?_⟩
      exact reflectMap_reflectMapInv a ⟨y, hyshell⟩
  rw [hset]
  exact hpre'

theorem isOpen_innerSeamImage (W : Set Seam) (hW : IsOpen W) :
    IsOpen (innerSeamImage d a W) := by
  have himg : IsOpen (reflectMap a '' (Subtype.val '' W)) := isOpen_reflectMap_image a W hW
  have hsub : reflectMap a '' (Subtype.val '' W) ⊆
      d.chart.toOpenPartialHomeomorph.source := by
    rintro y ⟨z, ⟨x, hxW, rfl⟩, rfl⟩
    have hx' : (x : EuclideanSpace ℝ (Fin 3)) ∈ SeamShell := x.2
    refine mem_chart_source_of_norm_le_two d ?_
    rw [norm_reflectMap (by linarith [hx'.2])]
    have h := norm_nonneg (x : EuclideanSpace ℝ (Fin 3))
    linarith [hx'.2]
  have hchart : IsOpen (d.chart.toOpenPartialHomeomorph ''
      (reflectMap a '' (Subtype.val '' W))) :=
    d.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source himg hsub
  exact hchart.preimage continuous_subtype_val

theorem seamMap_image_eq (W : Set Seam) :
    seamMap c d a '' W =
      inl c d a '' (outerSeamImage c W) ∪ inr c d a '' (innerSeamImage d a W) := by
  ext y
  constructor
  · rintro ⟨x, hxW, rfl⟩
    by_cases h : 1 ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖
    · refine Or.inl ⟨c.radialMap (seamDir x) ‖(x : EuclideanSpace ℝ (Fin 3))‖
        ⟨h, by linarith [x.2.2]⟩, ?_, ?_⟩
      · refine ⟨(x : EuclideanSpace ℝ (Fin 3)), ⟨x, hxW, rfl⟩, ?_⟩
        exact (radialMap_seamDir_coe c x h).symm
      · rw [seamMap_of_one_le c d a x h, seamLeft_eq_of_one_le c d a x h]
    · have hlt : ‖(x : EuclideanSpace ℝ (Fin 3))‖ < 1 := not_le.mp h
      refine Or.inr ⟨d.radialMap (a (seamDir x)) (2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖)
        ⟨by linarith, by linarith [x.2.1]⟩, ?_, ?_⟩
      · refine ⟨reflectMap a (x : EuclideanSpace ℝ (Fin 3)),
          ⟨(x : EuclideanSpace ℝ (Fin 3)), ⟨x, hxW, rfl⟩, rfl⟩, ?_⟩
        exact (radialMap_a_seamDir_coe d a x hlt).symm
      · rw [seamMap_of_lt_one c d a x h, seamRight_eq_of_lt_one c d a x hlt]
  · rintro (⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩)
    · obtain ⟨z, ⟨x, hxW, hxz⟩, hpz⟩ := hp
      subst hxz
      have h1 : 1 ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖ := one_le_norm_of_chart_eq c hpz
      refine ⟨x, hxW, ?_⟩
      rw [seamMap_of_one_le c d a x h1, seamLeft_eq_of_one_le c d a x h1]
      congr 1
      apply Subtype.ext
      change c.chart (‖(x : EuclideanSpace ℝ (Fin 3))‖ •
        ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3))) = (p : M)
      rw [smul_seamDir x]
      exact hpz
    · obtain ⟨z, hzmem, hqz⟩ := hq
      obtain ⟨u, humem, hzu⟩ := hzmem
      obtain ⟨x, hxW, hxu⟩ := humem
      subst hxu
      subst hzu
      have h1 : 1 ≤ ‖reflectMap a (x : EuclideanSpace ℝ (Fin 3))‖ :=
        one_le_norm_of_chart_eq d hqz
      have hnorm : ‖reflectMap a (x : EuclideanSpace ℝ (Fin 3))‖ =
          2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖ := norm_reflectMap (by linarith [x.2.2])
      have hxle : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := by linarith
      have hchart : d.chart (reflectMap a (x : EuclideanSpace ℝ (Fin 3))) = (q : N) := hqz
      rcases lt_or_eq_of_le hxle with hlt | heq
      · refine ⟨x, hxW, ?_⟩
        rw [seamMap_of_lt_one c d a x (not_le.mpr hlt),
          seamRight_eq_of_lt_one c d a x hlt]
        congr 1
        apply Subtype.ext
        change d.chart ((2 - ‖(x : EuclideanSpace ℝ (Fin 3))‖) •
          ((a (seamDir x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
            EuclideanSpace ℝ (Fin 3))) = (q : N)
        rw [← reflectMap_seamDir a x]
        exact hchart
      · refine ⟨x, hxW, ?_⟩
        rw [seamMap_of_one_le c d a x (le_of_eq heq.symm),
          seamLeft_eq_of_one_le c d a x (le_of_eq heq.symm)]
        have hbound : c.radialMap (seamDir x) ‖(x : EuclideanSpace ℝ (Fin 3))‖
            ⟨le_of_eq heq.symm, by linarith [x.2.2]⟩ = c.boundaryMap (seamDir x) := by
          apply Subtype.ext
          change c.chart (‖(x : EuclideanSpace ℝ (Fin 3))‖ •
            ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
              EuclideanSpace ℝ (Fin 3))) = c.chart
            (((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
              EuclideanSpace ℝ (Fin 3)))
          rw [heq, one_smul]
        rw [hbound, boundary_eq c d a (seamDir x)]
        congr 1
        apply Subtype.ext
        change d.chart (((a (seamDir x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3))) = (q : N)
        rw [← hchart, reflectMap_seamDir a x, heq]
        norm_num

theorem boundary_compat (W : Set Seam)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    c.boundaryMap z ∈ outerSeamImage c W ↔
      d.boundaryMap (a z) ∈ innerSeamImage d a W := by
  constructor
  · intro hz
    obtain ⟨y, hymem, hzy⟩ := hz
    obtain ⟨x, hxW, hxu⟩ := hymem
    subst hxu
    have hchart : c.chart.toPartialEquiv (x : EuclideanSpace ℝ (Fin 3)) =
        c.chart.toPartialEquiv (z : EuclideanSpace ℝ (Fin 3)) := hzy
    have hx : (x : EuclideanSpace ℝ (Fin 3)) = (z : EuclideanSpace ℝ (Fin 3)) :=
      c.chart.toPartialEquiv.injOn
        (mem_chart_source_of_norm_le_two c (by linarith [x.2.2]))
        (coe_sphere_mem_source c z) hchart
    refine ⟨reflectMap a (z : EuclideanSpace ℝ (Fin 3)),
      ⟨(z : EuclideanSpace ℝ (Fin 3)), ⟨x, hxW, hx⟩, rfl⟩, ?_⟩
    rw [reflectMap_coe_sphere a z]
    simp only [BallChart.boundaryMap_val]
    rfl
  · intro hz
    obtain ⟨z', hz'mem, hqz'⟩ := hz
    obtain ⟨u, humem, hzu⟩ := hz'mem
    obtain ⟨x, hxW, hxu⟩ := humem
    subst hxu
    subst hzu
    have hchart : d.chart.toPartialEquiv (reflectMap a (x : EuclideanSpace ℝ (Fin 3))) =
        d.chart.toPartialEquiv ((a z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)) := hqz'
    have hux : reflectMap a (x : EuclideanSpace ℝ (Fin 3)) =
        ((a z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)) :=
      d.chart.toPartialEquiv.injOn (reflectMap_mem_source d a x)
        (coe_sphere_mem_source d (a z)) hchart
    have heq : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      have hnorm := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => ‖w‖) hux
      rw [norm_reflectMap (by linarith [x.2.2]), norm_coe_sphere] at hnorm
      linarith
    have hdir : ((seamDir x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) = (z : EuclideanSpace ℝ (Fin 3)) := by
      have h1 : ((a (seamDir x) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)) =
          ((a z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
            EuclideanSpace ℝ (Fin 3)) := by
        rw [← hux, reflectMap_seamDir a x, heq]
        norm_num
      rw [a.injective (Subtype.ext h1)]
    refine ⟨(x : EuclideanSpace ℝ (Fin 3)), ⟨x, hxW, rfl⟩, ?_⟩
    simp only [BallChart.boundaryMap_val]
    rw [← hdir, coe_seamDir_eq x, heq, inv_one, one_smul]
    rfl

theorem seamMap_isOpenMap : IsOpenMap (seamMap c d a) := by
  intro W hW
  rw [seamMap_image_eq c d a W]
  exact isOpen_image_union_of_boundary_iff c d a
    (isOpen_outerSeamImage c W hW) (isOpen_innerSeamImage d a W hW) (boundary_compat c d a W)

theorem seamMap_eq_inl_chart (x : Seam) (h : 1 ≤ ‖(x : EuclideanSpace ℝ (Fin 3))‖) :
    seamMap c d a x = inl c d a
      ⟨c.chart (x : EuclideanSpace ℝ (Fin 3)), chart_mem_punctured c
        (mem_chart_source_of_norm_le_two c (by linarith [x.2.2])) h⟩ := by
  rw [seamMap_of_one_le c d a x h, seamLeft_eq_of_one_le c d a x h]
  congr 1
  exact radialMap_seamDir_eq c x h

theorem seamMap_eq_inr_chart (x : Seam) (h : ‖(x : EuclideanSpace ℝ (Fin 3))‖ < 1) :
    seamMap c d a x = inr c d a
      ⟨d.chart (reflectMap a (x : EuclideanSpace ℝ (Fin 3))),
        chart_mem_punctured d (reflectMap_mem_source d a x) (by
          rw [norm_reflectMap (by linarith [x.2.2])]; linarith)⟩ := by
  rw [seamMap_of_lt_one c d a x (not_le.mpr h), seamRight_eq_of_lt_one c d a x h]
  congr 1
  exact radialMap_a_seamDir_eq d a x h

theorem isOpenEmbedding_seamMap : IsOpenEmbedding (seamMap c d a) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_seamMap c d a)
    (seamMap_injective c d a) (seamMap_isOpenMap c d a)

end ConnectedSumQuotient

end DifferentialGeometry.Topology
