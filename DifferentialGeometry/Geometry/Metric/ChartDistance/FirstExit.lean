import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import DifferentialGeometry.Geometry.Metric.SmoothLipschitz
import DifferentialGeometry.Topology.FirstExit
import Mathlib.Analysis.Normed.Module.FiniteDimension
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

section

set_option autoImplicit false
noncomputable section

open Bundle Filter Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem edist_comp_le_riemannianCurveELength_of_bound_on_path
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {f : M → F} {C : ℝ≥0} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) 1 f U)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hbound : ∀ t ∈ Ioo a b, ∀ v : TangentSpace 𝓘(ℝ, E) (γ t),
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (γ t) v : F)‖ ≤
        C * Real.sqrt (g.inner (γ t) v v)) :
    edist (f (γ a)) (f (γ b)) ≤ (C : ℝ≥0∞) * riemannianCurveELength g γ a b := by
  have hη : ContDiffOn ℝ 1 (f ∘ γ) (Icc a b) :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp hγ hγU)
  have hh := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hη hab
  rw [← edist_eq_enorm_sub, edist_comm] at hh
  apply hh.trans
  unfold riemannianCurveELength riemannianCurveSpeed
  rw [← restrict_Ioo_eq_restrict_Icc, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have htIcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hγt := (hγ t htIcc).contMDiffAt (Icc_mem_nhds ht.1 ht.2)
  have hft := (hf (γ t) (hγU htIcc)).contMDiffAt (hU.mem_nhds (hγU htIcc))
  have hD := mfderiv_comp t (hft.mdifferentiableAt one_ne_zero)
    (hγt.mdifferentiableAt one_ne_zero)
  have hder : deriv (f ∘ γ) t =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)) := by
    rw [mfderiv_eq_fderiv] at hD
    have hv := congrArg (fun D => NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (γ t))
      (D ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm (1 : ℝ)))) hD
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, fderiv_apply_one_eq_deriv] using! hv
  rw [hder]
  have hb := ENNReal.ofReal_le_ofReal
    (hbound t ht (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)))
  simpa only [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ofReal_norm] using hb

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Filter Set MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mapsTo_chart_ball_of_riemannianCurveELength_lt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (ψ : OpenPartialHomeomorph F M)
    {R : ℝ} (hR : 0 < R) (hsource : closedBall (0 : F) R ⊆ ψ.source)
    (hψinv : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) 1 ψ.symm ψ.target)
    {C : ℝ≥0}
    (hbound : ∀ y ∈ ψ '' ball (0 : F) R, ∀ v : TangentSpace 𝓘(ℝ, E) y,
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) ψ.symm y v : F)‖ ≤
        C * Real.sqrt (g.inner y v v))
    {γ : ℝ → M} {b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc 0 b))
    (hstart : γ 0 = ψ 0)
    (hshort : (C : ℝ≥0∞) * riemannianCurveELength g γ 0 b < ENNReal.ofReal R) :
    MapsTo γ (Icc 0 b) (ψ '' ball (0 : F) R) := by
  let U := ψ '' ball (0 : F) R
  let K := ψ '' closedBall (0 : F) R
  have hsub : ball (0 : F) R ⊆ ψ.source := ball_subset_closedBall.trans hsource
  have hU : IsOpen U := ψ.isOpen_image_of_subset_source isOpen_ball hsub
  have hK : IsClosed K :=
    ((isCompact_closedBall (0 : F) R).image_of_continuousOn
      (ψ.continuousOn.mono hsource)).isClosed
  have hUK : U ⊆ K := image_mono ball_subset_closedBall
  have h0 : γ 0 ∈ U := hstart ▸ mem_image_of_mem ψ (mem_ball_self hR)
  intro q hq
  by_contra hqU
  have hqpos : 0 < q := lt_of_le_of_ne hq.1 (by
    intro heq
    exact hqU (heq ▸ h0))
  obtain ⟨t, ht, hbefore, hfront⟩ :=
    DifferentialGeometry.exists_first_exit_frontier_of_not_mem_interior hqpos
      (hγ.continuousOn.mono (Icc_subset_Icc le_rfl hq.2))
      (hU.interior_eq ▸ h0) (by simpa only [hU.interior_eq] using hqU)
  have hbeforeU : ∀ s ∈ Ico (0 : ℝ) t, γ s ∈ U := by
    simpa only [hU.interior_eq] using hbefore
  have htK : γ t ∈ K :=
    closure_minimal hUK hK (frontier_subset_closure hfront)
  have htNot : γ t ∉ U := by
    simpa only [hU.interior_eq] using hfront.2
  obtain ⟨x, hx, hxt⟩ := htK
  have hxsource : x ∈ ψ.source := hsource hx
  have hxtarget : γ t ∈ ψ.target := hxt ▸ ψ.map_source hxsource
  have hxnorm : ‖x‖ = R := by
    have hle : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hge : R ≤ ‖x‖ := le_of_not_gt (fun hlt =>
      htNot ⟨x, by simpa only [mem_ball, dist_zero_right] using hlt, hxt⟩)
    exact le_antisymm hle hge
  have hmaps : MapsTo γ (Icc 0 t) ψ.target := by
    intro s hs
    by_cases hst : s = t
    · simpa only [hst] using hxtarget
    · obtain ⟨y, hy, hyγ⟩ := hbeforeU s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
      exact hyγ ▸ ψ.map_source (hsub hy)
  have hdisp := edist_comp_le_riemannianCurveELength_of_bound_on_path g ψ.open_target
    hψinv ht.1.le (hγ.mono (Icc_subset_Icc le_rfl (ht.2.trans hq.2))) hmaps
    (fun s hs => hbound (γ s) (hbeforeU s ⟨hs.1.le, hs.2⟩))
  have heq : edist (ψ.symm (γ 0)) (ψ.symm (γ t)) = ENNReal.ofReal R := by
    rw [hstart, ψ.left_inv (hsource (mem_closedBall_self hR.le)), ← hxt,
      ψ.left_inv hxsource, edist_dist, dist_zero_left, hxnorm]
  rw [heq] at hdisp
  have hlen : riemannianCurveELength g γ 0 t ≤ riemannianCurveELength g γ 0 b :=
    lintegral_mono' (Measure.restrict_mono_set volume
      (Icc_subset_Icc le_rfl (ht.2.trans hq.2))) (fun _ => le_rfl)
  exact (not_lt_of_ge (hdisp.trans (mul_le_mul_right hlen _))) hshort

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Filter Set MeasureTheory Metric Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mem_chart_ball_of_riemannianEDistOf_lt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (ψ : OpenPartialHomeomorph F M)
    {R : ℝ} (hR : 0 < R) (hsource : closedBall (0 : F) R ⊆ ψ.source)
    (hψinv : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) 1 ψ.symm ψ.target)
    {C : ℝ≥0} (hC : 0 < C)
    (hbound : ∀ y ∈ ψ '' ball (0 : F) R, ∀ v : TangentSpace 𝓘(ℝ, E) y,
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) ψ.symm y v : F)‖ ≤
        C * Real.sqrt (g.inner y v v))
    {q : M} (hq : riemannianEDistOf g (ψ 0) q < ENNReal.ofReal R / C) :
    q ∈ ψ '' ball (0 : F) R := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hq
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  have hshort : (C : ℝ≥0∞) * riemannianCurveELength g γ 0 1 < ENNReal.ofReal R := by
    rw [riemannianCurveELength_eq_pathELength]
    have h := (ENNReal.lt_div_iff_mul_lt (Or.inl hC0) (Or.inl ENNReal.coe_ne_top)).mp hlen
    simpa only [mul_comm] using h
  have hmaps := mapsTo_chart_ball_of_riemannianCurveELength_lt
    g ψ hR hsource hψinv hbound hγ hγ0 hshort
  simpa only [hγ1] using hmaps (right_mem_Icc.mpr zero_le_one)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem edist_chart_symm_center_le_riemannianEDistOf
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (ψ : OpenPartialHomeomorph F M)
    {R : ℝ} (hR : 0 < R) (hsource : closedBall (0 : F) R ⊆ ψ.source)
    (hψinv : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) 1 ψ.symm ψ.target)
    {C : ℝ≥0} (hC : 0 < C)
    (hbound : ∀ y ∈ ψ '' ball (0 : F) R, ∀ v : TangentSpace 𝓘(ℝ, E) y,
      ‖(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) ψ.symm y v : F)‖ ≤
        C * Real.sqrt (g.inner y v v))
    {q : M} (hq : riemannianEDistOf g (ψ 0) q < ENNReal.ofReal R / C) :
    edist (ψ.symm q) (0 : F) ≤ (C : ℝ≥0∞) * riemannianEDistOf g (ψ 0) q := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  by_contra hn
  have hgap : riemannianEDistOf g (ψ 0) q < edist (ψ.symm q) (0 : F) / C := by
    apply (ENNReal.lt_div_iff_mul_lt (Or.inl hC0) (Or.inl ENNReal.coe_ne_top)).mpr
    simpa only [mul_comm] using lt_of_not_ge hn
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt (lt_min hq hgap)
  have hshort : (C : ℝ≥0∞) * riemannianCurveELength g γ 0 1 < ENNReal.ofReal R := by
    rw [riemannianCurveELength_eq_pathELength]
    have h := (ENNReal.lt_div_iff_mul_lt (Or.inl hC0) (Or.inl ENNReal.coe_ne_top)).mp
      (lt_of_lt_of_le hlen (min_le_left _ _))
    simpa only [mul_comm] using h
  have hmaps := mapsTo_chart_ball_of_riemannianCurveELength_lt
    g ψ hR hsource hψinv hbound hγ hγ0 hshort
  have htarget : MapsTo γ (Icc 0 1) ψ.target := by
    intro t ht
    obtain ⟨x, hx, hxeq⟩ := hmaps ht
    exact hxeq ▸ ψ.map_source (hsource (ball_subset_closedBall hx))
  have hdisp := edist_comp_le_riemannianCurveELength_of_bound_on_path g ψ.open_target
    hψinv zero_le_one hγ htarget
    (fun t ht => hbound (γ t) (hmaps ⟨ht.1.le, ht.2.le⟩))
  have hstart := ψ.left_inv (hsource (mem_closedBall_self hR.le))
  rw [hγ0, hγ1, hstart, edist_comm] at hdisp
  have hstrict : (C : ℝ≥0∞) * riemannianCurveELength g γ 0 1 < edist (ψ.symm q) (0 : F) := by
    rw [riemannianCurveELength_eq_pathELength]
    have h := (ENNReal.lt_div_iff_mul_lt (Or.inl hC0) (Or.inl ENNReal.coe_ne_top)).mp
      (lt_of_lt_of_le hlen (min_le_right _ _))
    simpa only [mul_comm] using h
  exact (not_lt_of_ge hdisp) hstrict

end DifferentialGeometry.Geometry

end

end
