import DifferentialGeometry.Analysis.ODE.GeodesicLimits.LipschitzTube
import DifferentialGeometry.Topology.FirstExit
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Native chart confinement from conditional coordinate equations

A compact inverse chart tube and the Lipschitz limit field prevent the original native curves
from leaving the chart. No confinement of the approximating curves is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.Analysis.ODE.GeodesicLimits

theorem eventually_mapsTo_chart_of_coordinate_ODE
    {X E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph X E) {a b : ℝ} (hab : a ≤ b)
    (gamma : ℕ → ℝ → X) (gammaInf : ℝ → X)
    (v : ℕ → E → E) (vInf : E → E)
    (hcontinuous : ∀ i, ContinuousOn (gamma i) (Icc a b))
    (hsourceInf : MapsTo gammaInf (Icc a b) e.source)
    (hderiv : ∀ i, ∀ t ∈ Icc a b, gamma i t ∈ e.source →
      HasDerivWithinAt (e ∘ gamma i) (v i (e (gamma i t))) (Icc a b) t)
    (hderivInf : ∀ t ∈ Icc a b,
      HasDerivWithinAt (e ∘ gammaInf) (vInf (e (gammaInf t))) (Icc a b) t)
    (hfield : ContDiffOn ℝ 1 vInf e.target)
    (hconv : ∀ C : Set E, IsCompact C → C ⊆ e.target →
      TendstoUniformlyOn v vInf atTop C)
    (hinit : Tendsto (fun i => gamma i a) atTop (𝓝 (gammaInf a))) :
    ∀ᶠ i in atTop, MapsTo (gamma i) (Icc a b) e.source := by
  let zInf := e ∘ gammaInf
  have hzInf : ContinuousOn zInf (Icc a b) :=
    fun t ht => (hderivInf t ht).continuousWithinAt
  have hcompact : IsCompact (zInf '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn hzInf
  have htarget : zInf '' Icc a b ⊆ e.target := by
    rintro y ⟨t, ht, rfl⟩
    exact e.map_source (hsourceInf ht)
  obtain ⟨r, hr, hrTarget⟩ :=
    hcompact.exists_cthickening_subset_open e.open_target htarget
  let S := cthickening r (zInf '' Icc a b)
  let O := e.symm '' thickening r (zInf '' Icc a b)
  let K := e.symm '' S
  have hS : IsCompact S := hcompact.cthickening
  have hK : IsCompact K := hS.image_of_continuousOn (e.symm.continuousOn.mono hrTarget)
  have hKsource : K ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_target (hrTarget hy)
  have hO : IsOpen O := e.isOpen_image_symm_of_subset_target isOpen_thickening
    ((thickening_subset_cthickening r _).trans hrTarget)
  have hOK : O ⊆ K := image_mono (thickening_subset_cthickening r _)
  have hOInt : O ⊆ interior K := hO.subset_interior_iff.mpr hOK
  have hstart : gammaInf a ∈ O := by
    refine ⟨zInf a, ?_, e.left_inv (hsourceInf (left_mem_Icc.mpr hab))⟩
    exact mem_thickening_iff.mpr ⟨zInf a, mem_image_of_mem zInf (left_mem_Icc.mpr hab),
      by simpa using hr⟩
  obtain ⟨L, hL⟩ := hfield.exists_lipschitzOnWith_of_isCompact e.open_target hS hrTarget
  obtain ⟨theta, htheta, hsmall, hbound⟩ :=
    exists_pos_gronwallBound_lt_of_pos (L : ℝ) (b - a) r hr
  have hcoordInit : Tendsto (fun i => e (gamma i a)) atTop (𝓝 (zInf a)) :=
    (e.continuousAt (hsourceInf (left_mem_Icc.mpr hab))).tendsto.comp hinit
  filter_upwards [hinit.eventually (hO.mem_nhds hstart),
    Metric.tendsto_nhds.mp hcoordInit theta htheta,
    Metric.tendstoUniformlyOn_iff.mp (hconv S hS hrTarget) theta htheta] with i hi hzero hv
  have hstay : MapsTo (gamma i) (Icc a b) K := by
    by_contra hexit
    obtain ⟨tau, htau, hprefix, hfront⟩ :=
      DifferentialGeometry.exists_first_exit_frontier_Icc_of_not_mapsTo hK.isClosed
        (hcontinuous i) (hOInt hi) hexit
    let z := e ∘ gamma i
    have hprefixSource : MapsTo (gamma i) (Icc a tau) e.source := fun t ht => hKsource (hprefix ht)
    have hzc : ContinuousOn z (Icc a tau) :=
      e.continuousOn.comp ((hcontinuous i).mono (Icc_subset_Icc le_rfl htau.2.le))
        hprefixSource
    have hsub : Icc a tau ⊆ Icc a b := Icc_subset_Icc le_rfl htau.2.le
    have hsubIco : Ico a tau ⊆ Ico a b := Ico_subset_Ico le_rfl htau.2.le
    have hzS : ∀ t ∈ Icc a tau, z t ∈ S := by
      intro t ht
      obtain ⟨y, hy, heq⟩ := hprefix ht
      dsimp [z]
      rw [← heq, e.right_inv (hrTarget hy)]
      exact hy
    have hInfS : ∀ t ∈ Icc a b, zInf t ∈ S := fun t ht =>
      mem_cthickening_of_dist_le _ _ r _ (mem_image_of_mem zInf ht) (by simpa using hr.le)
    have hcompare := dist_le_of_approx_trajectories_ODE_of_mem
      (v := fun _time => vInf) (s := fun _time => S) (K := L)
      (f := zInf) (g := z) (f' := fun t => vInf (zInf t)) (g' := fun t => v i (z t))
      (a := a) (b := tau) (εf := 0) (εg := theta) (δ := theta)
      (fun _time _htime => hL) (hzInf.mono hsub)
      (fun t ht => (hderivInf t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem (hsubIco ht)))
      (fun _time _htime => by simp) (fun t ht => hInfS t (hsub (Ico_subset_Icc_self ht)))
      hzc
      (fun t ht => (hderiv i t (hsub (Ico_subset_Icc_self ht))
        (hprefixSource (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem (hsubIco ht)))
      (fun t ht => by rw [dist_comm]; exact (hv _ (hzS t (Ico_subset_Icc_self ht))).le)
      (fun t ht => hzS t (Ico_subset_Icc_self ht))
      (by rw [dist_comm]; exact hzero.le) tau ⟨htau.1.le, le_rfl⟩
    have hmono : gronwallBound theta (L : ℝ) (0 + theta) (tau - a) ≤
        gronwallBound theta (L : ℝ) theta (b - a) := by
      rw [zero_add]
      exact gronwallBound_mono htheta.le htheta.le L.coe_nonneg
        (sub_le_sub_right htau.2.le a)
    have hdist : dist (zInf tau) (z tau) ≤
        gronwallBound theta (L : ℝ) (0 + theta) (tau - a) := hcompare
    have hclose : dist (z tau) (zInf tau) < r := by
      rw [dist_comm]
      exact hdist.trans_lt (hmono.trans_lt hbound)
    have hinside : gamma i tau ∈ O := by
      refine ⟨z tau, mem_thickening_iff.mpr
        ⟨zInf tau, mem_image_of_mem zInf ⟨htau.1.le, htau.2.le⟩, hclose⟩, ?_⟩
      exact e.left_inv (hprefixSource ⟨htau.1.le, le_rfl⟩)
    exact hfront.2 (hOInt hinside)
  exact fun t ht => hKsource (hstay ht)


theorem tendstoUniformlyOn_chart_of_coordinate_ODE
    {X E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph X E) {a b : ℝ} (hab : a ≤ b)
    (gamma : ℕ → ℝ → X) (gammaInf : ℝ → X)
    (v : ℕ → E → E) (vInf : E → E)
    (hcontinuous : ∀ i, ContinuousOn (gamma i) (Icc a b))
    (hsourceInf : MapsTo gammaInf (Icc a b) e.source)
    (hderiv : ∀ i, ∀ t ∈ Icc a b, gamma i t ∈ e.source →
      HasDerivWithinAt (e ∘ gamma i) (v i (e (gamma i t))) (Icc a b) t)
    (hderivInf : ∀ t ∈ Icc a b,
      HasDerivWithinAt (e ∘ gammaInf) (vInf (e (gammaInf t))) (Icc a b) t)
    (hfield : ContDiffOn ℝ 1 vInf e.target)
    (hconv : ∀ C : Set E, IsCompact C → C ⊆ e.target →
      TendstoUniformlyOn v vInf atTop C)
    (hinit : Tendsto (fun i => gamma i a) atTop (𝓝 (gammaInf a))) :
    TendstoUniformlyOn (fun i => e ∘ gamma i) (e ∘ gammaInf) atTop (Icc a b) := by
  classical
  have hstay := eventually_mapsTo_chart_of_coordinate_ODE e hab gamma gammaInf v vInf
    hcontinuous hsourceInf hderiv hderivInf hfield hconv hinit
  let good (i : ℕ) := MapsTo (gamma i) (Icc a b) e.source
  let z (i : ℕ) := if good i then e ∘ gamma i else e ∘ gammaInf
  let vSel (i : ℕ) := if good i then v i else vInf
  have hz : ∀ i, ∀ t ∈ Icc a b,
      HasDerivWithinAt (z i) (vSel i (z i t)) (Icc a b) t := by
    intro i t ht
    by_cases hi : good i
    · simpa only [z, vSel, ite_eq_left hi, Function.comp_apply] using hderiv i t ht (hi ht)
    · simpa only [z, vSel, ite_eq_right hi, Function.comp_apply] using hderivInf t ht
  have hcoordInit : Tendsto (fun i => e (gamma i a)) atTop (𝓝 (e (gammaInf a))) :=
    (e.continuousAt (hsourceInf (left_mem_Icc.mpr hab))).tendsto.comp hinit
  have hselInit : Tendsto (fun i => z i a) atTop (𝓝 ((e ∘ gammaInf) a)) := by
    apply hcoordInit.congr'
    filter_upwards [hstay] with i hi
    simp only [z, good, ite_eq_left hi, Function.comp_apply]
  have hzc : ContinuousOn (e ∘ gammaInf) (Icc a b) :=
    fun t ht => (hderivInf t ht).continuousWithinAt
  have hcompact : IsCompact ((e ∘ gammaInf) '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn hzc
  have htarget : (e ∘ gammaInf) '' Icc a b ⊆ e.target := by
    rintro y ⟨t, ht, rfl⟩
    exact e.map_source (hsourceInf ht)
  obtain ⟨r, hr, hrtarget⟩ :=
    hcompact.exists_cthickening_subset_open e.open_target htarget
  have hS : IsCompact (cthickening r ((e ∘ gammaInf) '' Icc a b)) := hcompact.cthickening
  obtain ⟨L, hL⟩ := hfield.exists_lipschitzOnWith_of_isCompact e.open_target hS hrtarget
  have hselConv : TendstoUniformlyOn vSel vInf atTop
      (cthickening r ((e ∘ gammaInf) '' Icc a b)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    filter_upwards [hstay,
      Metric.tendstoUniformlyOn_iff.mp (hconv _ hS hrtarget) epsilon hepsilon] with i hi hv
    simpa only [vSel, good, ite_eq_left hi] using hv
  have huniform := tendstoUniformlyOn_of_tendsto_of_lipschitzOnWith_limit hr hz
    hderivInf hL hselConv hselInit
  rw [Metric.tendstoUniformlyOn_iff] at huniform ⊢
  intro epsilon hepsilon
  filter_upwards [hstay, huniform epsilon hepsilon] with i hi hu
  simpa only [z, good, ite_eq_left hi] using hu

theorem real_constant_chart_trajectories_converge {a b : ℝ} (hab : a ≤ b) :
    TendstoUniformlyOn (fun i : ℕ => fun _time : ℝ => 1 / (i + 1 : ℝ))
      (fun _time : ℝ => 0) atTop (Icc a b) := by
  let e := OpenPartialHomeomorph.refl ℝ
  change TendstoUniformlyOn (fun i : ℕ => e ∘ (fun _time => 1 / (i + 1 : ℝ)))
    (e ∘ (fun _time => 0)) atTop (Icc a b)
  apply tendstoUniformlyOn_chart_of_coordinate_ODE e hab
    (fun i : ℕ => fun _time => 1 / (i + 1 : ℝ)) (fun _time => 0)
    (fun _i : ℕ => fun _x : ℝ => 0) (fun _x : ℝ => 0)
  · exact fun _i => continuousOn_const
  · exact fun _time _htime => mem_univ _
  · intro i t _ht _hsource
    exact (hasDerivAt_const t (1 / (i + 1 : ℝ))).hasDerivWithinAt
  · intro t _ht
    exact (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt
  · exact contDiffOn_const
  · intro C _hC _hTarget
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Eventually.of_forall (fun _i _x _hx => by simpa using hepsilon)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

end DifferentialGeometry.Geometry.Riemannian.Geodesic
