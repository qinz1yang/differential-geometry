import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient
import Mathlib.Geometry.Manifold.Instances.Sphere

open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace BallChart

variable {n : ℕ} (c : BallChart n I M)

theorem closedBall_one_subset_source : Metric.closedBall 0 1 ⊆ c.chart.source := by
  intro x hx
  apply c.closedBall_subset_source
  change dist x 0 ≤ 2
  exact le_trans (Metric.mem_closedBall.mp hx) (by norm_num)

theorem norm_radial (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {r : ℝ} (hr : 0 ≤ r) : ‖r • (z : EuclideanSpace ℝ (Fin n))‖ = r := by
  have hz : ‖(z : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using z.2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hz, mul_one]

def radialMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (r : ℝ) (hr : r ∈ Set.Icc 1 2) : c.Punctured :=
  ⟨c.chart (r • (z : EuclideanSpace ℝ (Fin n))), by
    rintro ⟨x, hx, h⟩
    have hr0 : 0 ≤ r := le_trans (by norm_num) hr.1
    have hs : r • (z : EuclideanSpace ℝ (Fin n)) ∈ c.chart.source := by
      apply c.closedBall_subset_source
      change dist (r • (z : EuclideanSpace ℝ (Fin n))) 0 ≤ 2
      rw [dist_zero_right, norm_radial z hr0]
      exact hr.2
    have heq : x = r • (z : EuclideanSpace ℝ (Fin n)) :=
      c.chart.toPartialEquiv.injOn (c.ball_subset_source hx) hs h
    have hxnorm : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    rw [heq, norm_radial z hr0] at hxnorm
    exact (not_lt_of_ge hr.1) hxnorm⟩

@[simp]
theorem radialMap_val (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (r : ℝ) (hr : r ∈ Set.Icc 1 2) :
    (c.radialMap z r hr : M) = c.chart (r • (z : EuclideanSpace ℝ (Fin n))) := rfl

@[simp]
theorem radialMap_one (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hr : (1 : ℝ) ∈ Set.Icc 1 2) : c.radialMap z 1 hr = c.boundaryMap z := by
  apply Subtype.ext
  simp only [radialMap_val, boundaryMap_val, one_smul]

theorem isCompact_closedBall_image : IsCompact (c.chart '' Metric.closedBall 0 1) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).image_of_continuousOn
    (c.chart.contMDiffOn_toFun.continuousOn.mono c.closedBall_one_subset_source)

def interior [T2Space M] : TopologicalSpace.Opens M :=
  ⟨(c.chart '' Metric.closedBall 0 1)ᶜ, c.isCompact_closedBall_image.isClosed.isOpen_compl⟩

@[simp]
theorem mem_interior [T2Space M] {x : M} :
    x ∈ c.interior ↔ x ∉ c.chart '' Metric.closedBall 0 1 := Iff.rfl

def interiorToPunctured [T2Space M] (x : c.interior) : c.Punctured :=
  ⟨x, by
    rintro ⟨y, hy, h⟩
    exact x.2 ⟨y, le_of_lt (Metric.mem_ball.mp hy), h⟩⟩

@[simp]
theorem interiorToPunctured_val [T2Space M] (x : c.interior) :
    (c.interiorToPunctured x : M) = x := rfl

theorem continuous_interiorToPunctured [T2Space M] : Continuous c.interiorToPunctured :=
  continuous_subtype_val.subtype_mk _

theorem interiorToPunctured_injective [T2Space M] :
    Function.Injective c.interiorToPunctured := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : c.Punctured => (z : M)) h)

theorem interior_boundary_cover [T2Space M] (x : c.Punctured) :
    (∃ y, c.interiorToPunctured y = x) ∨ (∃ z, c.boundaryMap z = x) := by
  classical
  by_cases hx : (x : M) ∈ c.chart '' Metric.closedBall 0 1
  · obtain ⟨y, hy, heq⟩ := hx
    have hynot : ¬dist y 0 < 1 := by
      intro hylt
      exact x.2 ⟨y, hylt, heq⟩
    have hyone : dist y 0 = 1 :=
      le_antisymm (Metric.mem_closedBall.mp hy) (le_of_not_gt hynot)
    exact Or.inr ⟨⟨y, hyone⟩, Subtype.ext heq⟩
  · exact Or.inl ⟨⟨x, hx⟩, rfl⟩

end BallChart

namespace ConnectedSumQuotient

def collarInterval : TopologicalSpace.Opens ℝ :=
  ⟨Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), isOpen_Ioo⟩

abbrev CollarDomain :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × collarInterval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {N : Type*} [TopologicalSpace N] [ChartedSpace K N]
  (c : BallChart 3 I M) (d : BallChart 3 J N)
  (a : Diffeomorph (𝓡 2) (𝓡 2)
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)

theorem collar_left_radius (t : collarInterval) (ht : 0 ≤ (t : ℝ)) :
    1 + (t : ℝ) ∈ Set.Ico 1 (3 / 2 : ℝ) := by
  have htupper := t.2.2
  constructor <;> linarith

theorem collar_right_radius (t : collarInterval) (ht : (t : ℝ) ≤ 0) :
    1 - (t : ℝ) ∈ Set.Ico 1 (3 / 2 : ℝ) := by
  have htlower := t.2.1
  constructor <;> linarith

def collarMap (p : CollarDomain) : ConnectedSumQuotient c d a.toHomeomorph :=
  if ht : 0 ≤ (p.2 : ℝ) then
    inl c d a.toHomeomorph (c.radialMap p.1 (1 + (p.2 : ℝ)) (by
      have hr := collar_left_radius p.2 ht
      exact ⟨hr.1, le_trans (le_of_lt hr.2) (by norm_num)⟩))
  else
    inr c d a.toHomeomorph (d.radialMap (a p.1) (1 - (p.2 : ℝ)) (by
      have hr := collar_right_radius p.2 (le_of_lt (lt_of_not_ge ht))
      exact ⟨hr.1, le_trans (le_of_lt hr.2) (by norm_num)⟩))

theorem collarMap_of_nonneg (p : CollarDomain) (ht : 0 ≤ (p.2 : ℝ)) :
    collarMap c d a p = inl c d a.toHomeomorph
      (c.radialMap p.1 (1 + (p.2 : ℝ)) (by
        have hr := collar_left_radius p.2 ht
        exact ⟨hr.1, le_trans (le_of_lt hr.2) (by norm_num)⟩)) := by
  simp only [collarMap, dif_pos ht]

theorem collarMap_of_neg (p : CollarDomain) (ht : (p.2 : ℝ) < 0) :
    collarMap c d a p = inr c d a.toHomeomorph
      (d.radialMap (a p.1) (1 - (p.2 : ℝ)) (by
        have hr := collar_right_radius p.2 ht.le
        exact ⟨hr.1, le_trans (le_of_lt hr.2) (by norm_num)⟩)) := by
  simp only [collarMap, dif_neg (not_le.mpr ht)]

theorem collarMap_zero_left (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    collarMap c d a (z, ⟨0, by constructor <;> norm_num [collarInterval]⟩) =
      inl c d a.toHomeomorph (c.boundaryMap z) := by
  simp [collarMap]

theorem collarMap_zero_right (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    collarMap c d a (z, ⟨0, by constructor <;> norm_num [collarInterval]⟩) =
      inr c d a.toHomeomorph (d.boundaryMap (a z)) := by
  rw [collarMap_zero_left]
  exact boundary_eq c d a.toHomeomorph z

def interiorLeft [T2Space M] : c.interior → ConnectedSumQuotient c d a.toHomeomorph :=
  inl c d a.toHomeomorph ∘ c.interiorToPunctured

def interiorRight [T2Space N] : d.interior → ConnectedSumQuotient c d a.toHomeomorph :=
  inr c d a.toHomeomorph ∘ d.interiorToPunctured

theorem continuous_interiorLeft [T2Space M] : Continuous (interiorLeft c d a) :=
  (continuous_inl c d a.toHomeomorph).comp c.continuous_interiorToPunctured

theorem continuous_interiorRight [T2Space N] : Continuous (interiorRight c d a) :=
  (continuous_inr c d a.toHomeomorph).comp d.continuous_interiorToPunctured

theorem interiorLeft_injective [T2Space M] : Function.Injective (interiorLeft c d a) :=
  (inl_injective c d a.toHomeomorph).comp c.interiorToPunctured_injective

theorem interiorRight_injective [T2Space N] : Function.Injective (interiorRight c d a) :=
  (inr_injective c d a.toHomeomorph).comp d.interiorToPunctured_injective

theorem interior_collar_cover [T2Space M] [T2Space N]
    (x : ConnectedSumQuotient c d a.toHomeomorph) :
    (∃ y, interiorLeft c d a y = x) ∨
      (∃ y, interiorRight c d a y = x) ∨ (∃ p, collarMap c d a p = x) := by
  obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := jointly_surjective c d a.toHomeomorph x
  · obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := c.interior_boundary_cover y
    · exact Or.inl ⟨z, rfl⟩
    · exact Or.inr (Or.inr ⟨(z, ⟨0, by constructor <;> norm_num [collarInterval]⟩),
        collarMap_zero_left c d a z⟩)
  · obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := d.interior_boundary_cover y
    · exact Or.inr (Or.inl ⟨z, rfl⟩)
    · refine Or.inr (Or.inr ⟨(a.symm z, ⟨0, by constructor <;> norm_num [collarInterval]⟩), ?_⟩)
      simpa only [a.apply_symm_apply] using collarMap_zero_right c d a (a.symm z)

theorem mem_chart_source_of_norm_le_two {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ ≤ 2) :
    x ∈ c.chart.source :=
  c.closedBall_subset_source (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)

theorem continuous_radialFamily
    (z : CollarDomain → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (r : CollarDomain → ℝ) (hz : Continuous z) (hr : Continuous r)
    (h1 : ∀ p, 1 ≤ r p) (h2 : ∀ p, r p ≤ 2) :
    Continuous fun p => c.radialMap (z p) (r p) ⟨h1 p, h2 p⟩ := by
  have hsmul : Continuous fun p : CollarDomain =>
      r p • ((z p : EuclideanSpace ℝ (Fin 3))) :=
    hr.smul (continuous_subtype_val.comp hz)
  have hsrc : ∀ p : CollarDomain,
      r p • ((z p : EuclideanSpace ℝ (Fin 3))) ∈ c.chart.source := by
    intro p
    refine mem_chart_source_of_norm_le_two c ?_
    have hz1 : ‖(z p : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using (z p).2
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (h1 p)), hz1, mul_one]
    exact h2 p
  have hchart : Continuous fun p : CollarDomain =>
      (⟨c.chart (r p • ((z p : EuclideanSpace ℝ (Fin 3)))),
        (c.radialMap (z p) (r p) ⟨h1 p, h2 p⟩).2⟩ : c.Punctured) :=
    ((c.chart.contMDiffOn_toFun.continuousOn.comp_continuous hsmul hsrc)).subtype_mk _
  convert hchart using 1
  funext p
  exact Subtype.ext rfl

def radialLeftClamp : CollarDomain → c.Punctured :=
  fun p => c.radialMap p.1 (max 1 (1 + (p.2 : ℝ))) (by
    refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
    have h := p.2.2.2
    linarith)

theorem continuous_radialLeftClamp : Continuous (radialLeftClamp c) := by
  have hr : Continuous fun p : CollarDomain => max 1 (1 + (p.2 : ℝ)) :=
    continuous_const.max (continuous_const.add (continuous_subtype_val.comp continuous_snd))
  refine continuous_radialFamily c (fun p => p.1) (fun p => max 1 (1 + (p.2 : ℝ)))
    continuous_fst hr ?_ ?_
  · intro p; exact le_max_left _ _
  · intro p
    refine max_le (by norm_num) ?_
    have h := p.2.2.2
    linarith

theorem radialLeftClamp_of_nonneg (p : CollarDomain) (ht : 0 ≤ (p.2 : ℝ)) :
    radialLeftClamp c p = c.radialMap p.1 (1 + (p.2 : ℝ))
      (by
        have h := collar_left_radius p.2 ht
        exact ⟨h.1, le_trans (le_of_lt h.2) (by norm_num)⟩) := by
  apply Subtype.ext
  change c.chart ((max 1 (1 + (p.2 : ℝ))) • ((p.1 : EuclideanSpace ℝ (Fin 3)))) =
    c.chart ((1 + (p.2 : ℝ)) • ((p.1 : EuclideanSpace ℝ (Fin 3))))
  rw [max_eq_right (by linarith : (1 : ℝ) ≤ 1 + (p.2 : ℝ))]

def radialRightClamp (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    CollarDomain → c.Punctured :=
  fun p => c.radialMap z (max 1 (1 - (p.2 : ℝ))) (by
    refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
    have h := p.2.2.1
    linarith)

theorem continuous_radialRightClamp
    (z : CollarDomain → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hz : Continuous z) :
    Continuous fun p => radialRightClamp c (z p) p := by
  have hr : Continuous fun p : CollarDomain => max 1 (1 - (p.2 : ℝ)) :=
    continuous_const.max (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
  refine continuous_radialFamily c z (fun p => max 1 (1 - (p.2 : ℝ))) hz hr ?_ ?_
  · intro p; exact le_max_left _ _
  · intro p
    refine max_le (by norm_num) ?_
    have h := p.2.2.1
    linarith

theorem radialRightClamp_of_neg (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (p : CollarDomain) (ht : (p.2 : ℝ) < 0) :
    radialRightClamp c z p = c.radialMap z (1 - (p.2 : ℝ))
      (by
        have h := collar_right_radius p.2 ht.le
        exact ⟨h.1, le_trans (le_of_lt h.2) (by norm_num)⟩) := by
  apply Subtype.ext
  change c.chart ((max 1 (1 - (p.2 : ℝ))) • ((z : EuclideanSpace ℝ (Fin 3)))) =
    c.chart ((1 - (p.2 : ℝ)) • ((z : EuclideanSpace ℝ (Fin 3))))
  rw [max_eq_right (by linarith : (1 : ℝ) ≤ 1 - (p.2 : ℝ))]

def collarLeft : CollarDomain → ConnectedSumQuotient c d a.toHomeomorph :=
  fun p => inl c d a.toHomeomorph (radialLeftClamp c p)

def collarRight : CollarDomain → ConnectedSumQuotient c d a.toHomeomorph :=
  fun p => inr c d a.toHomeomorph (radialRightClamp d (a p.1) p)

theorem continuous_collarLeft : Continuous (collarLeft c d a) :=
  (continuous_inl c d a.toHomeomorph).comp (continuous_radialLeftClamp c)

theorem continuous_collarRight : Continuous (collarRight c d a) := by
  have hz : Continuous fun p : CollarDomain => a p.1 :=
    Continuous.comp a.toHomeomorph.continuous_toFun continuous_fst
  exact (continuous_inr c d a.toHomeomorph).comp (continuous_radialRightClamp d _ hz)

theorem collarLeft_of_nonneg (p : CollarDomain) (ht : 0 ≤ (p.2 : ℝ)) :
    collarLeft c d a p = collarMap c d a p := by
  rw [collarMap_of_nonneg c d a p ht]
  exact congrArg (inl c d a.toHomeomorph) (radialLeftClamp_of_nonneg c p ht)

theorem collarRight_of_neg (p : CollarDomain) (ht : (p.2 : ℝ) < 0) :
    collarRight c d a p = collarMap c d a p := by
  rw [collarMap_of_neg c d a p ht]
  exact congrArg (inr c d a.toHomeomorph) (radialRightClamp_of_neg d (a p.1) p ht)

theorem collarLeft_eq_collarRight_of_eq_zero (p : CollarDomain) (ht : (p.2 : ℝ) = 0) :
    collarLeft c d a p = collarRight c d a p := by
  have hleft : radialLeftClamp c p = c.boundaryMap p.1 := by
    apply Subtype.ext
    change c.chart ((max 1 (1 + (p.2 : ℝ))) • ((p.1 : EuclideanSpace ℝ (Fin 3)))) =
      c.chart ((p.1 : EuclideanSpace ℝ (Fin 3)))
    rw [ht]
    norm_num
  have hright : radialRightClamp d (a p.1) p = d.boundaryMap (a p.1) := by
    apply Subtype.ext
    change d.chart ((max 1 (1 - (p.2 : ℝ))) •
        (((a p.1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)))) =
      d.chart (((a p.1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)))
    rw [ht]
    norm_num
  rw [collarLeft, collarRight, hleft, hright]
  exact boundary_eq c d a.toHomeomorph p.1

theorem collarMap_eq_if :
    collarMap c d a = fun p : CollarDomain =>
      if 0 ≤ (p.2 : ℝ) then collarLeft c d a p else collarRight c d a p := by
  funext p
  by_cases ht : 0 ≤ (p.2 : ℝ)
  · rw [if_pos ht, ← collarLeft_of_nonneg c d a p ht]
  · rw [if_neg ht, ← collarRight_of_neg c d a p (lt_of_not_ge ht)]

theorem continuous_collarMap : Continuous (collarMap c d a) := by
  rw [collarMap_eq_if]
  refine continuous_if ?_ (continuous_collarLeft c d a).continuousOn
    (continuous_collarRight c d a).continuousOn
  intro p hp
  exact collarLeft_eq_collarRight_of_eq_zero c d a p
    (frontier_half_le_subset_eq_zero (fun q : CollarDomain => (q.2 : ℝ))
      (continuous_subtype_val.comp continuous_snd) hp)

end ConnectedSumQuotient

end DifferentialGeometry.Topology
