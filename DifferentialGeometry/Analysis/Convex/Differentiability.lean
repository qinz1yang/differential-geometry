import DifferentialGeometry.Analysis.Calculus.Taylor
import DifferentialGeometry.Analysis.Convex.Proximal
import DifferentialGeometry.Analysis.Calculus.Sard
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.Compact

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

theorem ConvexOn.le_sub_of_hasFDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {s : Set E} (hf : ConvexOn ℝ s f)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) {D : E →L[ℝ] ℝ}
    (hd : HasFDerivWithinAt f D s x) : D (y - x) ≤ f y - f x := by
  let γ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hmaps : MapsTo γ (Icc 0 1) s := fun t ht => hf.1.lineMap_mem hx hy ht
  have hg : ConvexOn ℝ (Icc 0 1) (f ∘ γ) :=
    (hf.comp_affineMap γ).subset hmaps (convex_Icc _ _)
  have hd' : HasDerivWithinAt (f ∘ γ) (D (y - x)) (Icc 0 1) 0 := by
    have hdx : HasFDerivWithinAt f D s (γ 0) := by simpa only [γ, AffineMap.lineMap_apply_zero] using hd
    exact hdx.comp_hasDerivWithinAt 0 AffineMap.hasDerivWithinAt_lineMap hmaps
  have h := hg.le_slope_of_hasDerivWithinAt (by simp) (by simp) zero_lt_one hd'
  simpa only [slope_def_field, Function.comp_apply, γ, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] using h

theorem ConvexOn.continuousWithinAt_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {s : Set E} (hf : ConvexOn ℝ s f)
    {x : E} (hs : s ∈ 𝓝 x) (hd : DifferentiableAt ℝ f x) :
    ContinuousWithinAt (fderiv ℝ f) {y | DifferentiableAt ℝ f y} x := by
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro δ hδ
  let D := fderiv ℝ f x
  let q : E → ℝ := fun z => f z - D z - (f x - D x)
  have hrem : ∀ᶠ z in 𝓝 x, ‖f z - f x - D (z - x)‖ ≤ (δ / 8) * ‖z - x‖ :=
    hd.hasFDerivAt.isLittleO.bound (by positivity)
  obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.mp (inter_mem hs hrem)
  have hq : ConvexOn ℝ (Metric.ball x r) q := by
    exact ((hf.sub (D.toLinearMap.concaveOn hf.1)).sub
      (concaveOn_const (f x - D x) hf.1)).subset (fun _ hz => (hrb hz).1) (convex_ball _ _)
  have hqbound : ∀ z, dist z x < r → |q z| ≤ (δ / 8) * r := by
    intro z hz
    have heq : q z = f z - f x - D (z - x) := by simp only [q, map_sub]; ring
    rw [heq, ← Real.norm_eq_abs]
    exact (hrb hz).2.trans (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hz.le) (by positivity))
  have hlip := hq.lipschitzOnWith_of_abs_le (by positivity : 0 < r / 2) hqbound
  have hradius : r - r / 2 = r / 2 := by ring
  rw [hradius] at hlip
  have hconst : 2 * (δ / 8 * r) / (r / 2) = δ / 2 := by field_simp; ring
  rw [hconst] at hlip
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (half_pos hr)), self_mem_nhdsWithin]
    with z hz hzd
  have hn := norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds hz) hlip
  have heq : fderiv ℝ q z = fderiv ℝ f z - D := by
    exact ((hzd.hasFDerivAt.sub D.hasFDerivAt).sub_const (f x - D x)).fderiv
  rw [heq] at hn
  have hn' : ‖fderiv ℝ f z - D‖ ≤ δ / 2 := by
    simpa only [Real.coe_toNNReal _ (by positivity : 0 ≤ δ / 2)] using hn
  exact lt_of_le_of_lt (by simpa only [dist_eq_norm] using hn') (half_lt_self hδ)

private theorem ae_differentiableWithinAt_fderiv_of_isCompact
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {f : E → ℝ} {s : Set E} (hf : ConvexOn ℝ s f) (hs : IsCompact s)
    (hc : ContinuousOn f s) :
    ∀ᵐ x ∂μ.restrict (interior s),
      DifferentiableWithinAt ℝ (fderiv ℝ f) {y | DifferentiableAt ℝ f y} x := by
  by_cases hne : s.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp
  have hex (x : E) : ∃ y ∈ s, IsMinOn (fun z => f z + ‖z - x‖ ^ 2 / (2 * (1 : ℝ))) s y := by
    apply hs.exists_isMinOn hne
    exact hc.add (by fun_prop : ContinuousOn (fun z : E => ‖z - x‖ ^ 2 / (2 * (1 : ℝ))) s)
  choose P hPs hPmin using hex
  have hPlip : LipschitzWith 1 P := hf.lipschitzWith_of_isMinOn_add_norm_sq (by norm_num) hPs hPmin
  let R : E ≃L[ℝ] (E →L[ℝ] ℝ) := (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv
  let Q : E → E := fun y => y + R.symm (fderiv ℝ f y)
  let D : Set E := {y | DifferentiableAt ℝ f y}
  have hinverse {y : E} (hy : y ∈ s) (hdy : DifferentiableAt ℝ f y) : P (Q y) = y := by
    have hymin : IsMinOn (fun z => f z + ‖z - Q y‖ ^ 2 / (2 * (1 : ℝ))) s y := by
      apply (hf.isMinOn_add_norm_sq_iff (by norm_num) (Q y) hy).mpr
      intro z hz
      have h := hf.le_sub_of_hasFDerivWithinAt hy hz hdy.hasFDerivAt.hasFDerivWithinAt
      simp only [Q, add_sub_cancel_left, one_mul]
      change inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)) (z - y) ≤ f z - f y
      rw [InnerProductSpace.toDual_symm_apply]
      exact h
    have h := hf.norm_sub_sq_le_inner_sub_of_isMinOn_add_norm_sq (by norm_num)
      (hPs (Q y)) hy (hPmin (Q y)) hymin
    rw [sub_self, inner_zero_left] at h
    have hz : ‖P (Q y) - y‖ = 0 := by nlinarith [norm_nonneg (P (Q y) - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hgood := hPlip.locallyLipschitz.locallyLipschitzOn.ae_forall_hasFDerivAt_equiv
    (ν := μ) (Ω := univ) isOpen_univ rfl
  have hdiff : ∀ᵐ x ∂μ.restrict (interior s), DifferentiableAt ℝ f x :=
    ((hf.subset interior_subset hf.1.interior).locallyLipschitzOn_iff_continuousOn
      isOpen_interior).mpr (hc.mono interior_subset) |>.ae_differentiableAt isOpen_interior
  filter_upwards [ae_restrict_of_ae hgood, hdiff, ae_restrict_mem isOpen_interior.measurableSet]
    with x hx hdx hxs
  obtain ⟨A, hA⟩ := hx (Q x) (mem_univ _) (hinverse (interior_subset hxs) hdx)
  have hQc : ContinuousWithinAt Q D x :=
    continuousWithinAt_id.add (R.symm.continuousAt.comp_continuousWithinAt
      (hf.continuousWithinAt_fderiv (mem_interior_iff_mem_nhds.mp hxs) hdx))
  have hQinv : ∀ᶠ y in 𝓝[D] x, P (Q y) = y := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hxs)]
      with y hyd hys
    exact hinverse hys hyd
  have hQ : HasFDerivWithinAt Q (A.symm : E →L[ℝ] E) D x :=
    HasFDerivWithinAt.of_local_left_inverse (t := univ)
      (by simpa only [nhdsWithin_univ, ContinuousWithinAt] using hQc)
      hA.hasFDerivWithinAt hdx hQinv
  have hgradient := R.hasFDerivAt.comp_hasFDerivWithinAt x (hQ.sub (hasFDerivWithinAt_id x D))
  have heq : (R ∘ (Q - id)) = fderiv ℝ f := by
    funext y
    change R (Q y - y) = fderiv ℝ f y
    simp only [Q, add_sub_cancel_left, R.apply_symm_apply]
  rw [heq] at hgradient
  exact hgradient.differentiableWithinAt

private theorem ae_differentiableWithinAt_fderiv_of_innerProductSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {f : E → ℝ} {s : Set E} (hf : ConvexOn ℝ s f) (hs : IsOpen s) :
    ∀ᵐ x ∂μ.restrict s,
      DifferentiableWithinAt ℝ (fderiv ℝ f) {y | DifferentiableAt ℝ f y} x := by
  have hc := hf.continuousOn hs
  have hlocal (x : s) : ∃ V : Set E, IsOpen V ∧ x.1 ∈ V ∧
      ∀ᵐ y ∂μ, y ∈ V → DifferentiableWithinAt ℝ (fderiv ℝ f) {z | DifferentiableAt ℝ f z} y := by
    obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds x.2)
    have hsub : Metric.closedBall x.1 (r / 2) ⊆ s :=
      (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrb
    have h := ae_differentiableWithinAt_fderiv_of_isCompact (μ := μ)
      (hf.subset hsub (convex_closedBall _ _)) (isCompact_closedBall _ _) (hc.mono hsub)
    have hh := (ae_restrict_iff' isOpen_interior.measurableSet).mp h
    refine ⟨Metric.ball x.1 (r / 2), Metric.isOpen_ball, Metric.mem_ball_self (half_pos hr), ?_⟩
    filter_upwards [hh] with y hy
    exact fun hyb => hy (Metric.ball_subset_interior_closedBall hyb)
  choose V hV hxV hdiff using hlocal
  obtain ⟨S, hS, hcover⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover
    V hV (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (hxV ⟨x, hx⟩))
  have hcommon : ∀ᵐ y ∂μ, ∀ x ∈ S, y ∈ V x →
      DifferentiableWithinAt ℝ (fderiv ℝ f) {z | DifferentiableAt ℝ f z} y :=
    (ae_ball_iff hS).mpr (fun x _ => hdiff x)
  apply (ae_restrict_iff' hs.measurableSet).mpr
  filter_upwards [hcommon] with y hy
  intro hys
  obtain ⟨x, hx, hyV⟩ := mem_iUnion₂.mp (hcover hys)
  exact hy x hx hyV

theorem ConvexOn.ae_differentiableWithinAt_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {f : E → ℝ} {s : Set E} (hf : ConvexOn ℝ s f) :
    ∀ᵐ x ∂μ.restrict (interior s),
      DifferentiableWithinAt ℝ (fderiv ℝ f) {y | DifferentiableAt ℝ f y} x := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let e : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq (by simp [F])
  let g : F → ℝ := f ∘ e.symm
  let t : Set F := e.symm ⁻¹' interior s
  let _ : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have ht : IsOpen t := isOpen_interior.preimage e.symm.continuous
  have hg : ConvexOn ℝ t g :=
    (hf.subset interior_subset hf.1.interior).comp_linearMap e.symm.toLinearMap
  have ha := ae_differentiableWithinAt_fderiv_of_innerProductSpace (μ := μ.map e) hg ht
  have hb := ae_of_ae_map e.continuous.measurable.aemeasurable
    ((ae_restrict_iff' ht.measurableSet).mp ha)
  apply (ae_restrict_iff' isOpen_interior.measurableSet).mpr
  filter_upwards [hb] with x hx
  intro hxs
  have hgx := hx (by simpa only [t, mem_preimage, e.symm_apply_apply] using hxs)
  have hmaps : MapsTo e {y | DifferentiableAt ℝ f y} {z | DifferentiableAt ℝ g z} := by
    intro y hyd
    change DifferentiableAt ℝ f y at hyd
    apply e.symm.comp_right_differentiableAt_iff.mpr
    simpa only [e.symm_apply_apply] using hyd
  have hcomp := hgx.comp x e.differentiableWithinAt hmaps
  have hout := hcomp.clm_comp (differentiableWithinAt_const (e : E →L[ℝ] F))
  have heq : (fun z => (fderiv ℝ g (e z)).comp (e : E →L[ℝ] F)) = fderiv ℝ f := by
    have hge : g ∘ e = f := by funext z; simp only [g, Function.comp_apply, e.symm_apply_apply]
    funext z
    have hh := e.comp_right_fderiv (f := g) (x := z)
    rw [hge] at hh
    exact hh.symm
  change DifferentiableWithinAt ℝ (fun z => (fderiv ℝ g (e z)).comp (e : E →L[ℝ] F))
    {y | DifferentiableAt ℝ f y} x at hout
  rw [heq] at hout
  exact hout

theorem ConvexOn.alexandrov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {f : E → ℝ} {s : Set E} (hf : ConvexOn ℝ s f) :
    ∀ᵐ x ∂μ.restrict (interior s), DifferentiableAt ℝ f x ∧
      ∃ B : E →L[ℝ] E →L[ℝ] ℝ, B.flip = B ∧
        (fun y => f y - f x - fderiv ℝ f x (y - x) - (1 / 2 : ℝ) * B (y - x) (y - x))
          =o[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
  have hlip := (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior
  filter_upwards [hf.ae_differentiableWithinAt_fderiv (μ := μ),
    hlip.ae_differentiableAt isOpen_interior, ae_restrict_mem isOpen_interior.measurableSet]
    with x hx hdx hxs
  obtain ⟨L, U, hU, hfU⟩ := hlip hxs
  rw [isOpen_interior.nhdsWithin_eq hxs] at hU
  let A := fderivWithin ℝ (fderiv ℝ f) {y | DifferentiableAt ℝ f y} x
  let B := (1 / 2 : ℝ) • (A + A.flip)
  have hsym : B.flip = B := by
    simp only [B, ContinuousLinearMap.flip_smul, ContinuousLinearMap.flip_add,
      ContinuousLinearMap.flip_flip, add_comm]
  have hdiag (v : E) : B v v = A v v := by
    simp only [B, smul_apply, add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  have h := DifferentialGeometry.Analysis.second_order_taylor_isLittleO_of_hasFDerivWithinAt_fderiv
    hU hfU hx.hasFDerivWithinAt
  refine ⟨hdx, B, hsym, ?_⟩
  simpa only [hdiag, smul_eq_mul] using h
