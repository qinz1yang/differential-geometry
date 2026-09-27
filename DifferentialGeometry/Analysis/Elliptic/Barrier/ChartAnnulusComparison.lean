import DifferentialGeometry.Analysis.Elliptic.Barrier.CompactUpperSupportComparison
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section

open Bundle Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem euclidean_dist_norm (z w : E) :
    Euclidean.dist z w = ‖toEuclidean (z - w)‖ := by
  rw [Euclidean.dist, dist_eq_norm, map_sub]

private theorem norm_dist_le_euclidean (z w : E) :
    dist z w ≤ ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ *
      Euclidean.dist z w := by
  rw [dist_eq_norm, euclidean_dist_norm]
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
    (toEuclidean (E := E)).symm.toContinuousLinearMap.le_opNorm (toEuclidean (z - w))

omit [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
private theorem coordinate_ball_in_core (a : M) (b : SmoothBumpFunction I a)
    (z : E) (R : ℝ)
    (hfit : ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ * R +
      dist z (extChartAt I a a) < b.rIn)
    {y : E} (hy : y ∈ Euclidean.closedBall z R) :
    dist y (extChartAt I a a) < b.rIn := by
  have hnorm := norm_dist_le_euclidean y z
  have hbound := mul_le_mul_of_nonneg_left hy
    (norm_nonneg (toEuclidean (E := E)).symm.toContinuousLinearMap)
  exact (dist_triangle y z (extChartAt I a a)).trans_lt
    ((add_le_add (hnorm.trans hbound) (le_refl (dist z (extChartAt I a a)))).trans_lt hfit)

omit [IsManifold I ∞ M] [T2Space M] in
private theorem coordinate_ball_in_target (a : M) (b : SmoothBumpFunction I a)
    (z : E) (R : ℝ)
    (hfit : ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ * R +
      dist z (extChartAt I a a) < b.rIn) :
    Euclidean.closedBall z R ⊆ (extChartAt I a).target := by
  intro y hy
  apply b.closedBall_subset
  refine ⟨?_, ?_⟩
  · exact (coordinate_ball_in_core a b z R hfit hy).le.trans b.rIn_lt_rOut.le
  · rw [I.range_eq_univ]
    exact mem_univ y

private def radialSquare (a : M) (z : E) (x : M) : ℝ :=
  ‖toEuclidean (extChartAt I a x - z)‖ ^ 2

omit [I.Boundaryless] [T2Space M] in
private theorem radialSquare_smooth (a : M) (z : E) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (radialSquare (I := I) a z) (chartAt H a).source := by
  have hq : ContDiff ℝ ∞ (fun w : E => ‖toEuclidean (w - z)‖ ^ 2) :=
    ((toEuclidean (E := E)).contDiff.comp (contDiff_id.sub contDiff_const)).norm_sq ℝ
  intro x hx
  exact (hq.contMDiff.contMDiffAt.comp x
    ((contMDiffOn_extChartAt (I := I) (x := a) x hx).contMDiffAt
      ((chartAt H a).open_source.mem_nhds hx))).contMDiffWithinAt

private def cutoffRadialSquare {a : M} (b : SmoothBumpFunction I a) (z : E) (x : M) : ℝ :=
  b x * radialSquare (I := I) a z x

omit [I.Boundaryless] in
private theorem cutoffRadialSquare_smooth {a : M} (b : SmoothBumpFunction I a) (z : E) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (cutoffRadialSquare (I := I) b z) := by
  have h := b.contMDiff_smul (radialSquare_smooth (I := I) a z)
  change ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => b x * radialSquare (I := I) a z x) at h
  exact h

private theorem radial_fderiv (z w : E) :
    fderiv ℝ (fun y : E => ‖toEuclidean (y - z)‖ ^ 2) w (w - z) =
      2 * ‖toEuclidean (w - z)‖ ^ 2 := by
  have hlin : HasFDerivAt (fun y : E => toEuclidean (y - z))
      (toEuclidean (E := E)).toContinuousLinearMap w := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      (toEuclidean (E := E)).hasFDerivAt.comp w ((hasFDerivAt_id w).sub_const z)
  rw [hlin.norm_sq.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, coe_innerSL_apply, real_inner_self_eq_norm_sq,
    nsmul_eq_mul, Nat.cast_ofNat]

omit [I.Boundaryless] [T2Space M] in
private theorem cutoffRadialSquare_gradient_ne_zero
    (g : SmoothRiemannianMetric I M) {a : M} (b : SmoothBumpFunction I a)
    (z : E) {x : M} (hx : x ∈ (chartAt H a).source)
    (hcore : dist (extChartAt I a x) (extChartAt I a a) < b.rIn)
    (hpos : 0 < Euclidean.dist (extChartAt I a x) z) :
    gradientFun (I := I) g (cutoffRadialSquare (I := I) b z) x ≠ 0 := by
  let f := cutoffRadialSquare (I := I) b z
  let q : E → ℝ := fun y => ‖toEuclidean (y - z)‖ ^ 2
  have heq : f =ᶠ[𝓝 x] radialSquare (I := I) a z := by
    filter_upwards [b.eventuallyEq_one_of_dist_lt hx hcore] with y hy
    change b y = 1 at hy
    change b y * radialSquare (I := I) a z y = radialSquare (I := I) a z y
    rw [hy, one_mul]
  have hq : ContDiff ℝ ∞ q :=
    ((toEuclidean (E := E)).contDiff.comp (contDiff_id.sub contDiff_const)).norm_sq ℝ
  have hcomp : mfderiv I 𝓘(ℝ, ℝ) (radialSquare (I := I) a z) x =
      (fderiv ℝ q (extChartAt I a x)).comp
        (mfderiv I 𝓘(ℝ, E) (extChartAt I a) x) := by
    change mfderiv I 𝓘(ℝ, ℝ) (q ∘ extChartAt I a) x = _
    have h := mfderiv_comp x (hq.contMDiff.mdifferentiable (by simp) (extChartAt I a x))
      (mdifferentiableAt_extChartAt (I := I) hx)
    rw [mfderiv_eq_fderiv] at h
    exact h
  intro hzero
  have hdf : mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply (NormedSpace.fromTangentSpace (f x)).injective
    have hinner := inner_gradientFun g f x v
    rw [show gradientFun g f x = 0 from hzero] at hinner
    change mvfderiv (I := I) f x v = (0 : ℝ)
    simpa only [map_zero, zero_apply] using hinner.symm
  rw [heq.mfderiv_eq, hcomp] at hdf
  have hinv := isInvertible_mfderiv_extChartAt (I := I)
    (show x ∈ (extChartAt I a).source by simpa only [extChartAt_source] using hx)
  obtain ⟨v, hv⟩ := hinv.surjective (extChartAt I a x - z)
  have heval := congrArg (fun D : TangentSpace I x →L[ℝ] ℝ => D v) hdf
  change fderiv ℝ q (extChartAt I a x)
    (mfderiv I 𝓘(ℝ, E) (extChartAt I a) x v) = 0 at heval
  rw [hv] at heval
  have hrad := radial_fderiv z (extChartAt I a x)
  change fderiv ℝ q (extChartAt I a x) (extChartAt I a x - z) = _ at hrad
  rw [heval] at hrad
  rw [euclidean_dist_norm] at hpos
  have hsq : 0 < ‖toEuclidean (extChartAt I a x - z)‖ ^ 2 := sq_pos_of_pos hpos
  linarith

omit [I.Boundaryless] [T2Space M] in
private theorem laplacian_exp_neg_mul (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (α : ℝ) (x : M) :
    laplacian (LeviCivita g) g (fun y => Real.exp (-α * f y)) x =
      Real.exp (-α * f x) * (α ^ 2 *
        g.inner x (gradientFun g f x) (gradientFun g f x) -
          α * laplacian (LeviCivita g) g f x) := by
  let Φ : ℝ → ℝ := fun s => Real.exp (-α * s)
  have hΦ (s : ℝ) : HasDerivAt Φ ((-α) * Real.exp (-α * s)) s := by
    have h : HasDerivAt Φ (Real.exp (-α * s) * (-α)) s := by
      simpa only [Φ, id_eq, mul_one] using (((hasDerivAt_id s).const_mul (-α)).exp)
    exact h.congr_deriv (by ring)
  have hderiv : deriv Φ = fun s => (-α) * Real.exp (-α * s) :=
    funext fun s => (hΦ s).deriv
  have hsecond : deriv (deriv Φ) (f x) = α ^ 2 * Real.exp (-α * f x) := by
    rw [hderiv]
    calc
      _ = (-α) * ((-α) * Real.exp (-α * f x)) := ((hΦ (f x)).const_mul (-α)).deriv
      _ = _ := by ring
  have hΦ' : DifferentiableAt ℝ (deriv Φ) (f x) := by
    rw [hderiv]
    fun_prop
  have h := laplacian_comp (LeviCivita g) g (φ := Φ) (f := f) (x := x)
    (fun s => (hΦ s).differentiableAt) hΦ'
    (hf.mdifferentiable (by simp)) (gradientFun_mdiffAt g hf x)
  rw [(hΦ (f x)).deriv, hsecond] at h
  change laplacian (LeviCivita g) g (fun y => Real.exp (-α * f y)) x = _ at h
  rw [h]
  ring

omit [IsManifold I ∞ M] [T2Space M] in
private theorem chart_annulus_data (a : M) (b : SmoothBumpFunction I a) (z : E)
    (r R : ℝ)
    (hfit : ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ * R +
      dist z (extChartAt I a a) < b.rIn)
    {x : M} (hx : x ∈ (extChartAt I a).symm ''
      (Euclidean.closedBall z R \ Euclidean.ball z r)) :
    x ∈ (chartAt H a).source ∧
      dist (extChartAt I a x) (extChartAt I a a) < b.rIn ∧
      r ≤ Euclidean.dist (extChartAt I a x) z ∧
      Euclidean.dist (extChartAt I a x) z ≤ R := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hyt := coordinate_ball_in_target a b z R hfit hy.1
  have hright := (extChartAt I a).right_inv hyt
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [extChartAt_source] using (extChartAt I a).map_target hyt
  · rw [hright]
    exact coordinate_ball_in_core a b z R hfit hy.1
  · rw [hright]
    exact le_of_not_gt hy.2
  · rw [hright]
    exact hy.1

theorem exists_subharmonic_chart_annulus
    (g : SmoothRiemannianMetric I M) (a : M) (b : SmoothBumpFunction I a)
    (z : E) (r R : ℝ) (hr : 0 < r)
    (hfit : ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ * R +
      dist z (extChartAt I a a) < b.rIn) :
    let K := (extChartAt I a).symm '' (Euclidean.closedBall z R \ Euclidean.ball z r)
    IsCompact K ∧ ∃ ψ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ ∧
      ∀ x ∈ K, 0 < laplacian (LeviCivita g) g ψ x ∧
        0 ≤ ψ x ∧ ψ x < 1 ∧
        (Euclidean.dist (extChartAt I a x) z < R → 0 < ψ x) ∧
        (Euclidean.dist (extChartAt I a x) z = R → ψ x = 0) := by
  let K := (extChartAt I a).symm '' (Euclidean.closedBall z R \ Euclidean.ball z r)
  have hK : IsCompact K :=
    (Euclidean.isCompact_closedBall.diff Euclidean.isOpen_ball).image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) a).mono
        (fun y hy => coordinate_ball_in_target a b z R hfit hy.1))
  let f := cutoffRadialSquare (I := I) b z
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := cutoffRadialSquare_smooth b z
  let q : M → ℝ := fun x => g.inner x (gradientFun g f x) (gradientFun g f x)
  have hq : Continuous q := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (CovariantDerivative.metric_inner_contMDiffAt g
      (gradientFun_smooth g hf).contMDiffAt (gradientFun_smooth g hf).contMDiffAt
      le_rfl).continuousAt
  have hqpos : ∀ x ∈ K, 0 < q x := by
    intro x hx
    have hd := chart_annulus_data a b z r R hfit hx
    exact g.pos x _ (cutoffRadialSquare_gradient_ne_zero g b z hd.1 hd.2.1
      (hr.trans_le hd.2.2.1))
  obtain ⟨m, hm, hm_bound⟩ := hK.exists_forall_le' hq.continuousOn hqpos
  have hLapCont : Continuous (laplacian (LeviCivita g) g f) := by
    have heq : laplacian (LeviCivita g) g f = ΔG g ⟨f, hf⟩ :=
      funext fun x => laplacian_levi_eq g hf x
    rw [heq]
    exact (Δ_g_contMDiff g ⟨f, hf⟩).continuous
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hLapCont.continuousOn
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hB_bound (x : M) (hx : x ∈ K) : laplacian (LeviCivita g) g f x ≤ B := by
    have habs : |laplacian (LeviCivita g) g f x| ≤ B₀ := by
      simpa only [Real.norm_eq_abs] using hB₀ x hx
    exact (le_abs_self _).trans (habs.trans (le_max_left B₀ 0))
  let α : ℝ := (B + 1) / m
  have hα : 0 < α := div_pos (by linarith only [hB]) hm
  have hαm : α * m = B + 1 := div_mul_cancel₀ _ hm.ne'
  let ψ : M → ℝ := fun x => Real.exp (-α * f x) - Real.exp (-α * R ^ 2)
  have hExp : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => Real.exp (-α * f x)) :=
    Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul hf)
  have hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ := hExp.sub contMDiff_const
  refine ⟨hK, ψ, hψ, ?_⟩
  intro x hx
  have hd := chart_annulus_data a b z r R hfit hx
  let d := Euclidean.dist (extChartAt I a x) z
  have hdpos : 0 < d := hr.trans_le hd.2.2.1
  have hdR : d ≤ R := hd.2.2.2
  have hf_value : f x = d ^ 2 := by
    rw [show f x = b x * radialSquare (I := I) a z x from rfl,
      b.one_of_dist_le hd.1 hd.2.1.le, one_mul]
    simp only [radialSquare, d, euclidean_dist_norm]
  have hvalue : ψ x = Real.exp (-α * d ^ 2) - Real.exp (-α * R ^ 2) := by
    dsimp only [ψ]
    rw [hf_value]
  have hsq : d ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hdpos.le (hdpos.le.trans hdR)).mpr hdR
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change 0 < laplacian (LeviCivita g) g
      (fun y => Real.exp (-α * f y) - Real.exp (-α * R ^ 2)) x
    rw [laplacian_sub_const (LeviCivita g) g (Real.exp (-α * R ^ 2))
      (hExp.mdifferentiable (by simp)) x, laplacian_exp_neg_mul g f hf α x]
    have hmq := mul_le_mul_of_nonneg_left (hm_bound x hx) hα.le
    rw [hαm] at hmq
    have hgap : 0 < α * q x - laplacian (LeviCivita g) g f x := by
      linarith only [hmq, hB_bound x hx]
    have hfactor : α ^ 2 * q x - α * laplacian (LeviCivita g) g f x =
        α * (α * q x - laplacian (LeviCivita g) g f x) := by ring
    change 0 < Real.exp (-α * f x) *
      (α ^ 2 * q x - α * laplacian (LeviCivita g) g f x)
    rw [hfactor]
    exact mul_pos (Real.exp_pos _) (mul_pos hα hgap)
  · rw [hvalue]
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left hsq hα.le)
  · rw [hvalue]
    have he : Real.exp (-α * d ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le)
        (sq_nonneg d))
    linarith only [he, Real.exp_pos (-α * R ^ 2)]
  · intro hdlt
    rw [hvalue]
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    have hslt : d ^ 2 < R ^ 2 := (sq_lt_sq₀ hdpos.le (hdpos.le.trans hdR)).mpr hdlt
    simpa only [neg_mul] using neg_lt_neg (mul_lt_mul_of_pos_left hslt hα)
  · intro hdEq
    rw [hvalue, show d = R from hdEq, sub_self]

omit [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
private theorem chart_annulus_interior (a : M) (z : E) (r R : ℝ) {x : M}
    (hx : x ∈ (chartAt H a).source)
    (hr : r < Euclidean.dist (extChartAt I a x) z)
    (hR : Euclidean.dist (extChartAt I a x) z < R) :
    x ∈ interior ((extChartAt I a).symm ''
      (Euclidean.closedBall z R \ Euclidean.ball z r)) := by
  let U := (chartAt H a).source ∩ (extChartAt I a) ⁻¹'
    (Euclidean.ball z R \ Euclidean.closedBall z r)
  have hU : IsOpen U := isOpen_extChartAt_preimage a
    (Euclidean.isOpen_ball.sdiff Euclidean.isClosed_closedBall)
  have hxU : x ∈ U := ⟨hx, hR, not_le.mpr hr⟩
  have hsub : U ⊆ (extChartAt I a).symm ''
      (Euclidean.closedBall z R \ Euclidean.ball z r) := by
    intro y hy
    have hrlt : r < Euclidean.dist (extChartAt I a y) z := lt_of_not_ge hy.2.2
    have hRlt : Euclidean.dist (extChartAt I a y) z < R := hy.2.1
    refine ⟨extChartAt I a y, ⟨hRlt.le, not_lt.mpr hrlt.le⟩, ?_⟩
    exact (extChartAt I a).left_inv
      (show y ∈ (extChartAt I a).source by simpa only [extChartAt_source] using hy.1)
  apply interior_mono hsub
  simpa only [hU.interior_eq] using hxU

theorem positive_on_chart_annulus_of_laplacian_upper_supports
    (g : SmoothRiemannianMetric I M) (a : M) (b : SmoothBumpFunction I a)
    (z : E) (r R : ℝ) (hr : 0 < r)
    (hfit : ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ * R +
      dist z (extChartAt I a a) < b.rIn)
    (u : M → ℝ) (η : ℝ) (hη : 0 < η) :
    let K := (extChartAt I a).symm '' (Euclidean.closedBall z R \ Euclidean.ball z r)
    ContinuousOn u K → (∀ x ∈ K, 0 ≤ u x) →
      (∀ x ∈ K, Euclidean.dist (extChartAt I a x) z = r → η ≤ u x) →
      (∀ x ∈ interior K, ∀ ε : ℝ, 0 < ε →
        ∃ U : Set M, ∃ φ : M → ℝ,
          IsOpen U ∧ x ∈ U ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ U ∧
            φ x = u x ∧ (∀ y ∈ U, u y ≤ φ y) ∧
              laplacian (LeviCivita g) g φ x ≤ ε) →
      ∀ x ∈ K, Euclidean.dist (extChartAt I a x) z < R → 0 < u x := by
  let K := (extChartAt I a).symm '' (Euclidean.closedBall z R \ Euclidean.ball z r)
  dsimp only
  intro hu hnonneg hinner hsupport
  obtain ⟨hK, ψ, hψ, hψdata⟩ := exists_subharmonic_chart_annulus g a b z r R hr hfit
  have hscaled : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => η * ψ x) := contMDiff_const.mul hψ
  have hboundary : ∀ x ∈ K \ interior K, η * ψ x ≤ u x := by
    intro x hx
    have hd := chart_annulus_data a b z r R hfit hx.1
    have hp := hψdata x hx.1
    by_cases heq : Euclidean.dist (extChartAt I a x) z = r
    · exact (mul_le_mul_of_nonneg_left hp.2.2.1.le hη.le).trans
        (by simpa only [mul_one] using hinner x hx.1 heq)
    · have hrlt : r < Euclidean.dist (extChartAt I a x) z :=
        lt_of_le_of_ne hd.2.2.1 (Ne.symm heq)
      have houter : Euclidean.dist (extChartAt I a x) z = R := by
        by_contra hne
        have hlt : Euclidean.dist (extChartAt I a x) z < R :=
          lt_of_le_of_ne hd.2.2.2 hne
        exact hx.2 (chart_annulus_interior a z r R hd.1 hrlt hlt)
      rw [hp.2.2.2.2 houter, mul_zero]
      exact hnonneg x hx.1
  have hscaledLap : ∀ x ∈ interior K,
      0 < laplacian (LeviCivita g) g (fun y => η * ψ y) x := by
    intro x hx
    change 0 < laplacian (LeviCivita g) g (η • ψ) x
    rw [laplacian_const_smul (LeviCivita g) g η
      (hψ.mdifferentiable (by simp)) (gradientFun_mdiffAt g hψ x)]
    exact mul_pos hη (hψdata x (interior_subset hx)).1
  have hcomparison := le_on_compact_of_laplacian_upper_supports g K hK u (fun x => η * ψ x)
    hu hscaled.continuous.continuousOn hscaled.contMDiffOn hboundary hscaledLap hsupport
  intro x hx hlt
  exact (mul_pos hη ((hψdata x hx).2.2.2.1 hlt)).trans_le (hcomparison x hx)

end DifferentialGeometry.Analysis

end
