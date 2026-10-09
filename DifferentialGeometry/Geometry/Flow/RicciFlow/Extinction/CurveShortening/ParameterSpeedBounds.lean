import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ArcLengthBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ArcLengthTensorBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RicciDerivativeBounds
import DifferentialGeometry.Analysis.ODE.ScalarParameterDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParameterDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing
import DifferentialGeometry.Analysis.Calculus.Periodic.Affine

open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

omit [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] in
private theorem iterated_ds_add_eq (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (f h : ℝ → ℝ → ℝ) (t : ℝ) (ht : t ∈ J)
    (hf : ContDiff ℝ ∞ (fun x => f x t)) (hh : ContDiff ℝ ∞ (fun x => h x t))
    (m : ℕ) (x : ℝ) :
    (c.ds g)^[m] (fun y τ => f y τ + h y τ) x t =
      (c.ds g)^[m] f x t + (c.ds g)^[m] h x t := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    change (c.speed g x t)⁻¹ * deriv (fun y => (c.ds g)^[m] (fun z τ => f z τ + h z τ) y t) x = _
    rw [funext ih, deriv_fun_add
      ((c.iterated_ds_contDiff g hc hi f t ht hf m).differentiable (by simp) x)
      ((c.iterated_ds_contDiff g hc hi h t ht hh m).differentiable (by simp) x), mul_add]
    rfl

variable [CompactSpace M] {D : RealTimeInterval} {a b : ℝ}

theorem exists_iterated_ds_q_bounds_on_Ico_of_curvature_le
    (B : RicciBackground (I := I) (M := M) D a b) {T : ℝ}
    (haT : a < T) (hTb : T ≤ b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Ico a T)) {K : ℝ}
    (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K)
    (s : ℝ) (has : a < s) :
    ∀ m, ∃ C : ℝ, 0 < C ∧ ∀ x t, t ∈ Ico s T →
      |(c.ds B.family.metric)^[m] (c.q B.family) x t| ≤ C := by
  have hsub : Ico s T ⊆ Ico a T := fun t ht => ⟨has.le.trans ht.1, ht.2⟩
  have hsm : c.SmoothOn (I := I) (Ico s T) := hc.smooth.mono (prod_mono_right hsub)
  have him : c.ImmersedOn (I := I) (Ico s T) := fun x t ht => hc.immersed x t (hsub ht)
  have hT := c.exists_iteratedDs_unitTangent_bounds_on_Ico_of_curvature_le B haT hTb hc hcurv s has
  have hH := c.exists_iterated_ds_curvatureSq_bounds_on_Ico_of_curvature_le B haT hTb hc hcurv s has
  have hR (j : ℕ) : ∃ C : ℝ, ∀ x t, t ∈ Ico s T →
      Real.sqrt (normSq0S (B.family.metric t) (c.lift x t) (2 + j)
        (iterCov (B.family.metric t) 2 (B.family.ricci t) j (c.lift x t))) ≤ C := by
    obtain ⟨C, hC, hb⟩ := B.exists_iterCov_ricci_bound j
    exact ⟨C, fun x t ht => Real.sqrt_le_iff.mpr ⟨hC.le,
      hb t ⟨has.le.trans ht.1, ht.2.le.trans hTb⟩ (c.lift x t)⟩⟩
  intro m
  obtain ⟨CH, hCH⟩ := hH m
  obtain ⟨CR, hCR, hbR⟩ := c.exists_iterated_ds_ricciTangent_bound B.family hsm him hR hT m
  refine ⟨max 1 (CH + CR), zero_lt_one.trans_le (le_max_left _ _), fun x t ht => ?_⟩
  have hTs := c.unitTangent_contMDiff B.family.metric (Ico s T) hsm him t ht
  have hRs : ContDiff ℝ ∞ (fun y => c.ricciTangent B.family y t) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact contDiffWithinAt_univ.mp
      (c.contDiffWithinAt_ricciTangent_slice (B.family.metric t) (Ico s T)
        hsm (c.unitTangent B.family.metric) (c.unitTangent B.family.metric) y t ht hTs hTs)
  change |(c.ds B.family.metric)^[m]
    (fun y τ => c.curvatureSq B.family.metric y τ + c.ricciTangent B.family y τ) x t| ≤ _
  rw [iterated_ds_add_eq c B.family.metric hsm him _ _ t ht
    (c.curvatureSq_contDiff B.family.metric (Ico s T) hsm him t ht) hRs m x]
  exact ((abs_add_le _ _).trans (add_le_add (hCH x t ht) (hbR x t ht))).trans
    (le_max_right _ _)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
variable {D : RealTimeInterval} {a b T : ℝ}

namespace CurveMap

theorem deriv_speed_Ioo (B : RicciBackground (I := I) (M := M) D a b)
    (hTb : T ≤ b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Ico a T)) {t : ℝ} (ht : t ∈ Ioo a T) (x : ℝ) :
    deriv (c.speed B.family.metric x) t =
      -(c.q B.family x t * c.speed B.family.metric x t) := by
  obtain ⟨u, htu, huT⟩ := exists_between ht.2
  have hau : a < u := ht.1.trans htu
  have hsub : Icc a u ⊆ Ico a T := fun r hr => ⟨hr.1, hr.2.trans_lt huT⟩
  have hc' : c.IsSolutionOn B.family.metric (Icc a u) :=
    hc.mono hsub (fun r hr => ((uniqueDiffOn_Icc hau) r hr).uniqueMDiffWithinAt)
  have heq := (rfs_csf_speed B hau (Icc_subset_Icc le_rfl (huT.le.trans hTb))
    c hc' x t ⟨ht.1.le, htu.le⟩).1
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 htu)] at heq
  simpa only [neg_mul] using heq

omit [SigmaCompactSpace M] in
theorem contDiff_q_slice (G : SolutionFamily (I := I) (M := M)) (c : CurveMap M)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {t : ℝ} (ht : t ∈ J) : ContDiff ℝ ∞ (fun x => c.q G x t) := by
  have hT := c.unitTangent_contMDiff G.metric J hc hi t ht
  rw [contDiff_iff_contDiffAt]
  intro x
  exact ((c.curvatureSq_contDiff G.metric J hc hi t ht).contDiffAt).add
    (contDiffWithinAt_univ.mp (c.contDiffWithinAt_ricciTangent_slice (G.metric t) J hc
      (c.unitTangent G.metric) (c.unitTangent G.metric) x t ht hT hT))

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless] in
private theorem exists_iteratedDeriv_speed_bound (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {t : ℝ} (ht : t ∈ J) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖iteratedDeriv n (fun y => c.speed g y t) x‖ ≤ C := by
  have hsp := c.speed_contDiff g J hc hi t ht
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) :=
    contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)
  have hper : Function.Periodic (fun x => c.speed g x t) 1 :=
    fun x => c.speed_add_period g t x (hγ.mdifferentiableAt (by norm_num))
  have hpern : Function.Periodic (iteratedDeriv n (fun y => c.speed g y t)) 1 := by
    intro x
    have h := congrFun (iteratedDeriv_comp_add_const n (fun y => c.speed g y t) 1) x
    rw [show (fun z => c.speed g (z + 1) t) = (fun z => c.speed g z t) from funext hper] at h
    exact h.symm
  exact DifferentialGeometry.Analysis.exists_bound_of_continuous_unit_periodic
    (hsp.continuous_iteratedDeriv n (by exact_mod_cast le_top)) hpern

theorem exists_iteratedDeriv_speed_bounds_of_iterate_ds_q_bounds
    (B : RicciBackground (I := I) (M := M) D a b)
    (hTb : T ≤ b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Ico a T)) {s : ℝ} (has : a < s)
    (hqb : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, t ∈ Ico s T →
      ‖(c.ds B.family.metric)^[j] (c.q B.family) x t‖ ≤ C) :
    ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, t ∈ Ico s T →
      ‖iteratedDeriv j (fun y => c.speed B.family.metric y t) x‖ ≤ C := by
  by_cases hsT : s < T
  · have hs : s ∈ Ico a T := ⟨has.le, hsT⟩
    have hwindow : Ico s T ⊆ Ioo a T := fun t ht => ⟨has.trans_le ht.1, ht.2⟩
    have hco : Ioo a T ⊆ Ico a T := fun t ht => ⟨ht.1.le, ht.2⟩
    have hsp := Field.smoothOn_speed B.family.metric B.smooth
      (fun t (ht : t ∈ Ioo a T) => B.regular ⟨ht.1.le, ht.2.le.trans hTb⟩)
      c (hc.smooth.mono (Set.prod_mono Subset.rfl hco))
      (fun x t ht => hc.immersed x t (hco ht))
    have hb := DifferentialGeometry.Analysis.exists_iteratedDeriv_bounds_of_weightedDeriv_and_deriv_eq_neg_mul
      (v := c.speed B.family.metric) (q := c.q B.family)
      (U := univ) (V := Ioo a T) isOpen_univ isOpen_Ioo hsp hwindow
      (fun x _ t ht => (c.contDiff_q_slice B.family hc.smooth hc.immersed (hco (hwindow ht))).contDiffAt)
      (fun x _ t ht => (c.speed_pos B.family.metric hc.immersed x t (hco (hwindow ht))).ne')
      (fun t ht x _ => c.deriv_speed_Ioo B hTb hc (hwindow ht) x)
      (fun j => by
        obtain ⟨C, hC, hbound⟩ := c.exists_iteratedDeriv_speed_bound B.family.metric hc.smooth hc.immersed hs j
        exact ⟨C, hC.le, fun x _ => hbound x⟩)
      (fun j => by
        obtain ⟨C, hC, hbound⟩ := hqb j
        refine ⟨C, hC, fun x _ t ht => ?_⟩
        rw [← c.iterate_ds_eq_weightedDeriv B.family.metric (c.q B.family) j t]
        exact hbound x t ht)
    exact fun j => by
      obtain ⟨C, hC, hbound⟩ := hb j
      exact ⟨C, hC, fun x t ht => hbound x (mem_univ x) t ht⟩
  · exact fun j => ⟨0, le_rfl, fun x t ht => (hsT (ht.1.trans_lt ht.2)).elim⟩

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening


namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}

theorem exists_iteratedDeriv_speed_bounds_on_Ico_of_curvature_le
    (B : RicciBackground (I := I) (M := M) D a b) {T : ℝ}
    (haT : a < T) (hTb : T ≤ b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Ico a T)) {K : ℝ}
    (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K)
    (s : ℝ) (has : a < s) :
    ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, t ∈ Ico s T →
      ‖iteratedDeriv j (fun y => c.speed B.family.metric y t) x‖ ≤ C := by
  apply c.exists_iteratedDeriv_speed_bounds_of_iterate_ds_q_bounds B hTb hc has
  intro j
  obtain ⟨C, hC, hb⟩ := c.exists_iterated_ds_q_bounds_on_Ico_of_curvature_le
    B haT hTb hc hcurv s has j
  exact ⟨C, hC.le, fun x t ht => by simpa only [Real.norm_eq_abs] using hb x t ht⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
