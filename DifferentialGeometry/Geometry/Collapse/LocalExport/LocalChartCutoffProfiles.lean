import DifferentialGeometry.Geometry.Collapse.LocalExport.CircleChart
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimChart
import DifferentialGeometry.Analysis.Calculus.Cutoff.EdgeNetworkProfiles
import DifferentialGeometry.Analysis.Calculus.FlatTailDerivativeBounds

/-!
# The actual cutoff formulas of the circle and slim charts (review-42 packet (ii), kernels)

Review 42 §6.4: plateau, support and smoothness of a cutoff do not bound its derivatives; the LC87
consumers (FC24's fixed model profiles) need the ACTUAL formula. Here the circle and slim cutoffs are
fixed profiles composed with the chart's own coordinate, extended by zero:

* `circleCutoffBump_LC87`: the bump of `ℝ²` with plateau `B̄(0, 8)` and support `B(0, 9)` (the
  profile of `exists_cutoff_of_enclosure`); `CircleChart.formulaCutoff c =
  𝟙_{B(p, 200)} · ψ ∘ η`, with `CircleChart.formulaCutoff_spec`: smooth, values in `[0, 1]`, one
  where `‖η‖ ≤ 8`, nonzero only where `‖η‖ < 9`, closed support in `B̄(p, 102) ∩ {‖η‖ ≤ 9}` (the
  chart's enclosure), hence inside the bundle domain.
* `slimCutoffProfile_LC87`: the profile with plateau `[-8, 8]` and support in `(-89/10, 89/10)`
  (variable `η/(10⁵Δ)`); `SlimChart.withFormulaCutoff c`: the SAME slim chart (same coordinate and
  every other field) with the cutoff `𝟙_{B(p, 10⁶Δ)} · φ(η/(10⁵Δ))`.
* `circleCutoffBump_budget_LC87`, `slimCutoffProfile_budget_LC87`: numerical `C²` budgets of the two
  fixed profiles (chosen before every parameter).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The circle cutoff profile: the bump of `ℝ²` with plateau `B̄(0, 8)` and support `B(0, 9)`. -/
def circleCutoffBump_LC87 : ContDiffBump (0 : ℝ²) := ⟨8, 9, by norm_num, by norm_num⟩

/-- The slim cutoff profile (variable `η/(10⁵Δ)`): plateau `[-8, 8]`, support in
`(-89/10, 89/10)`. -/
def slimCutoffProfile_LC87 : ℝ → ℝ := intervalPlateauProfile (-89 / 10) (-8) 8 (89 / 10)

/-- Uniform `C²` budget of the circle profile. -/
theorem circleCutoffBump_budget_LC87 : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ v : ℝ²,
    ‖fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ) v‖ ≤ A ∧
      ‖fderiv ℝ (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ)) v‖ ≤ B := by
  have hf : ContDiff ℝ 2 (circleCutoffBump_LC87 : ℝ² → ℝ) := circleCutoffBump_LC87.contDiff
  have hD : ContDiff ℝ 1 (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ)) :=
    hf.fderiv_right (by norm_num)
  have hDD : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ))) :=
    hD.fderiv_right (by norm_num)
  have hs : HasCompactSupport (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ)) :=
    circleCutoffBump_LC87.hasCompactSupport.fderiv ℝ
  have hs2 : HasCompactSupport (fderiv ℝ (fderiv ℝ (circleCutoffBump_LC87 : ℝ² → ℝ))) :=
    hs.fderiv ℝ
  obtain ⟨A, hA⟩ := hD.continuous.norm.bddAbove_range_of_hasCompactSupport
    (hs.comp_left norm_zero)
  let iN : NormedAddCommGroup (ℝ² →L[ℝ] ℝ² →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨B, hB⟩ := hDD.continuous.norm.bddAbove_range_of_hasCompactSupport
    (hs2.comp_left norm_zero)
  refine ⟨max A 0, max B 0, le_max_right _ _, le_max_right _ _, fun v => ⟨?_, ?_⟩⟩
  · exact (hA ⟨v, rfl⟩).trans (le_max_left _ _)
  · exact (hB ⟨v, rfl⟩).trans (le_max_left _ _)

/-- Uniform `C²` budget of the slim profile. -/
theorem slimCutoffProfile_budget_LC87 : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ t : ℝ,
    ‖fderiv ℝ slimCutoffProfile_LC87 t‖ ≤ A ∧
      ‖fderiv ℝ (fderiv ℝ slimCutoffProfile_LC87) t‖ ≤ B := by
  obtain ⟨P, hP, hD, hDD⟩ := exists_derivative_bounds_of_constant_tails
    ((contDiff_intervalPlateauProfile (-89 / 10 : ℝ) (-8) 8 (89 / 10)).of_le (by simp) :
      ContDiff ℝ 2 slimCutoffProfile_LC87)
    (fun x hx => intervalPlateauProfile_zero_left (a := (-89 / 10 : ℝ)) (b := -8) (c := 8)
      (d := 89 / 10) (by norm_num) hx)
    (fun x hx => intervalPlateauProfile_zero_right (a := (-89 / 10 : ℝ)) (b := -8) (c := 8)
      (d := 89 / 10) (by norm_num) hx)
  exact ⟨P, P, by linarith, by linarith, fun t => ⟨hD t, hDD t⟩⟩

section Circle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The circle cutoff of a chart: `ψ ∘ η` on `B(p, 200)`, zero elsewhere. -/
def CircleChart.formulaCutoff (c : CircleChart I M) : M → ℝ :=
  (ball c.center 200).indicator (fun x => circleCutoffBump_LC87 (c.coord x))

/-- **The formula circle cutoff** has the LC87 cutoff clauses. -/
theorem CircleChart.formulaCutoff_spec (c : CircleChart I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ c.formulaCutoff ∧ (∀ x, c.formulaCutoff x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ball c.center 200, ‖c.coord x‖ ≤ 8 → c.formulaCutoff x = 1) ∧
      (∀ x, c.formulaCutoff x ≠ 0 → x ∈ ball c.center 200 ∧ ‖c.coord x‖ < 9) ∧
      tsupport c.formulaCutoff ⊆ closedBall c.center 102 ∩ {x | ‖c.coord x‖ ≤ 9} ∧
      tsupport c.formulaCutoff ⊆ (diskPreimageOpens (ball c.center 200) isOpen_ball c.coord
        c.contMDiffOn_coord.continuousOn 100 : Set M) := by
  classical
  set ψ := circleCutoffBump_LC87
  have hval : ∀ x, c.formulaCutoff x = if x ∈ ball c.center 200 then ψ (c.coord x) else 0 :=
    fun x => by simp only [CircleChart.formulaCutoff, indicator_apply]; rfl
  let T : Set M := closedBall c.center 102 ∩ c.coord ⁻¹' closedBall 0 9
  have hT : IsClosed T :=
    (c.contMDiffOn_coord.continuousOn.mono (closedBall_subset_ball (by norm_num))).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_closedBall
  have hsupp : ∀ x, c.formulaCutoff x ≠ 0 → x ∈ ball c.center 200 ∧ ‖c.coord x‖ < 9 := by
    intro x hx
    rw [hval] at hx
    by_cases hxW : x ∈ ball c.center 200
    · refine ⟨hxW, ?_⟩
      simp only [hxW, ↓reduceIte] at hx
      have hmem : c.coord x ∈ support ψ := hx
      rw [ψ.support_eq, mem_ball, dist_zero_right] at hmem
      exact hmem
    · simp only [hxW, ↓reduceIte] at hx
      exact absurd rfl hx
  have hsuppT : support c.formulaCutoff ⊆ T := by
    intro x hx
    obtain ⟨hxW, hx9⟩ := hsupp x hx
    exact ⟨ball_subset_closedBall (c.enclosure x hxW (by linarith)), by
      rw [mem_preimage, mem_closedBall, dist_zero_right]; exact hx9.le⟩
  have htsupp : tsupport c.formulaCutoff ⊆ T := closure_minimal hsuppT hT
  refine ⟨?_, ?_, ?_, hsupp, fun x hx => ⟨(htsupp hx).1, by
    have h9 := (htsupp hx).2
    rw [mem_preimage, mem_closedBall, dist_zero_right] at h9
    exact h9⟩, ?_⟩
  · intro x
    by_cases hxW : x ∈ ball c.center 200
    · have hcomp : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => ψ (c.coord y)) x :=
        (ψ.contDiff.contMDiff.contMDiffAt).comp x
          ((c.contMDiffOn_coord x hxW).contMDiffAt (isOpen_ball.mem_nhds hxW))
      refine hcomp.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds hxW] with y hy
      rw [hval]; simp only [hy, ↓reduceIte]
    · have hxT : x ∉ T := fun h => hxW (closedBall_subset_ball (by norm_num) h.1)
      refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hT.isOpen_compl.mem_nhds hxT] with y hy
      by_contra hne
      exact hy (hsuppT hne)
  · intro x
    rw [hval]
    by_cases hxW : x ∈ ball c.center 200
    · simp only [hxW, ↓reduceIte]
      exact ⟨ψ.nonneg, ψ.le_one⟩
    · simp only [hxW, ↓reduceIte]
      exact ⟨le_rfl, zero_le_one⟩
  · intro x hxW hx8
    rw [hval]; simp only [hxW, ↓reduceIte]
    exact ψ.one_of_mem_closedBall (by rwa [mem_closedBall, dist_zero_right])
  · intro x hx
    have hxT := htsupp hx
    have hxW : x ∈ ball c.center 200 := closedBall_subset_ball (by norm_num) hxT.1
    have hx9 : ‖c.coord x‖ ≤ 9 := by
      have := hxT.2
      rwa [mem_preimage, mem_closedBall, dist_zero_right] at this
    refine ⟨hxW, ?_⟩
    rw [mem_preimage, mem_ball, dist_zero_right]
    linarith

end Circle

section Slim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {Δ σ : ℝ}
  {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
  {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}

/-- The formula slim cutoff `𝟙_{B(p, 10⁶Δ)} · φ(η/(10⁵Δ))` of a slim chart. -/
def SlimChart.formulaCutoff (c : SlimChart g hEnorm Δ σ α) : M → ℝ :=
  (ball p (10 ^ 6 * Δ)).indicator (fun x => slimCutoffProfile_LC87 (c.coord x / (10 ^ 5 * Δ)))

open Classical in
/-- **The same slim chart with the formula cutoff** (every other field unchanged). -/
def SlimChart.withFormulaCutoff [CompactSpace M] (c : SlimChart g hEnorm Δ σ α) (hΔ : 0 < Δ) :
    SlimChart g hEnorm Δ σ α :=
  have hval : ∀ x, c.formulaCutoff x = if x ∈ ball p (10 ^ 6 * Δ) then
      slimCutoffProfile_LC87 (c.coord x / (10 ^ 5 * Δ)) else 0 := fun x => by
    classical
    simp only [SlimChart.formulaCutoff, indicator_apply]
  have hsupp : ∀ x, c.formulaCutoff x ≠ 0 →
      x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| < 89 * 10 ^ 4 * Δ := by
    intro x hx
    classical
    rw [hval] at hx
    by_cases hxW : x ∈ ball p (10 ^ 6 * Δ)
    · refine ⟨hxW, ?_⟩
      simp only [hxW, ↓reduceIte] at hx
      have hl : (-89 / 10 : ℝ) < c.coord x / (10 ^ 5 * Δ) := by
        by_contra h
        exact hx (intervalPlateauProfile_zero_left (by norm_num) (not_lt.mp h))
      have hr : c.coord x / (10 ^ 5 * Δ) < 89 / 10 := by
        by_contra h
        exact hx (intervalPlateauProfile_zero_right (by norm_num) (not_lt.mp h))
      have hpos : (0 : ℝ) < 10 ^ 5 * Δ := by positivity
      rw [lt_div_iff₀ hpos] at hl
      rw [div_lt_iff₀ hpos] at hr
      rw [abs_lt]
      constructor <;> linarith
    · simp only [hxW, ↓reduceIte] at hx
      exact absurd rfl hx
  let T : Set M := closedBall p (91 / 100 * (10 ^ 6 * Δ)) ∩ {x | |c.coord x| ≤ 89 * 10 ^ 4 * Δ}
  have hT : IsClosed T :=
    isClosed_closedBall.inter (isClosed_le (continuous_abs.comp c.lipschitz.continuous)
      continuous_const)
  have hsuppT : support c.formulaCutoff ⊆ T := by
    intro x hx
    obtain ⟨hxW, hx9⟩ := hsupp x hx
    exact ⟨(c.enclosure x hxW (by linarith)).le, hx9.le⟩
  have htsupp : tsupport c.formulaCutoff ⊆ T := closure_minimal hsuppT hT
  { c with
    cutoff := c.formulaCutoff
    contMDiff_cutoff := by
      classical
      intro x
      by_cases hxW : x ∈ ball p (10 ^ 6 * Δ)
      · have hdom : x ∈ c.domain := c.closedBall_subset_domain (ball_subset_closedBall hxW)
        have hη : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ c.coord x :=
          (c.contMDiffOn_coord x hdom).contMDiffAt (c.isOpen_domain.mem_nhds hdom)
        have hcomp : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
            (fun y => slimCutoffProfile_LC87 (c.coord y / (10 ^ 5 * Δ))) x :=
          ((contDiff_intervalPlateauProfile _ _ _ _).contMDiff.contMDiffAt).comp x
            (hη.div_const _)
        refine hcomp.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_ball.mem_nhds hxW] with y hy
        rw [hval]; simp only [hy, ↓reduceIte]
      · have hxT : x ∉ T := fun h => hxW (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp h.1)
          (by nlinarith)))
        refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
        filter_upwards [hT.isOpen_compl.mem_nhds hxT] with y hy
        by_contra hne
        exact hy (hsuppT hne)
    hasCompactSupport_cutoff := (hT.isCompact).of_isClosed_subset (isClosed_tsupport _) htsupp
    cutoff_mem_Icc := by
      classical
      intro x
      rw [hval]
      by_cases hxW : x ∈ ball p (10 ^ 6 * Δ)
      · simp only [hxW, ↓reduceIte]
        exact intervalPlateauProfile_mem_Icc _ _ _ _ _
      · simp only [hxW, ↓reduceIte]
        exact ⟨le_rfl, zero_le_one⟩
    cutoff_eq_one := by
      classical
      intro x hxW hx8
      rw [hval]; simp only [hxW, ↓reduceIte]
      have hpos : (0 : ℝ) < 10 ^ 5 * Δ := by positivity
      refine intervalPlateauProfile_one (by norm_num) (by norm_num) ⟨?_, ?_⟩
      · rw [le_div_iff₀ hpos]
        linarith [(abs_le.mp hx8).1]
      · rw [div_le_iff₀ hpos]
        linarith [(abs_le.mp hx8).2]
    cutoff_ne_zero := hsupp
    tsupport_cutoff := fun x hx => ⟨mem_closedBall.mp (htsupp hx).1, (htsupp hx).2⟩ }

theorem SlimChart.withFormulaCutoff_coord [CompactSpace M] (c : SlimChart g hEnorm Δ σ α) (hΔ : 0 < Δ) :
    (c.withFormulaCutoff hΔ).coord = c.coord := rfl

theorem SlimChart.withFormulaCutoff_cutoff [CompactSpace M] (c : SlimChart g hEnorm Δ σ α) (hΔ : 0 < Δ) :
    (c.withFormulaCutoff hΔ).cutoff = c.formulaCutoff := rfl

end Slim

end DifferentialGeometry.Geometry.Collapse
