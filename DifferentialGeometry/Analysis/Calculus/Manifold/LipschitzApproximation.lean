import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import DifferentialGeometry.Geometry.Metric.LocalChartDistance
import DifferentialGeometry.Analysis.Calculus.LipschitzConvolution
import DifferentialGeometry.Geometry.Metric.CompactDerivative
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Metrizable

noncomputable section

open Bundle Manifold Filter Set Metric DifferentialGeometry
open scoped Manifold ContDiff Topology NNReal ENNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem local_smooth_approx
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {L : ℝ≥0}
    (hf : ∀ x y, edist (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y)
    {κ : ℝ≥0} (hκ : (1 : ℝ) < κ) (p : M) : ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ ε : ℝ, 0 < ε →
      ∃ h : M → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ h U ∧
        (∀ x ∈ U, |h x - f x| < ε) ∧
        ∀ x ∈ U, ∀ v : TangentSpace I x,
          |(show ℝ from mfderiv I 𝓘(ℝ) h x v)| ≤ (κ : ℝ) ^ 2 * L * Real.sqrt (g.inner x v v) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let e := trivializationAt E (TangentSpace I) p
  let A : TangentSpace I p ≃L[ℝ] E :=
    e.continuousLinearEquivAt ℝ p (mem_baseSet_trivializationAt E (TangentSpace I) p)
  let φ : M → TangentSpace I p := fun x => A.symm (extChartAt I p x)
  let ψ : TangentSpace I p → M := fun v => (extChartAt I p).symm (A v)
  have hφsmooth : ContMDiffOn I 𝓘(ℝ, TangentSpace I p) ∞ φ (extChartAt I p).source :=
    A.symm.contDiff.contMDiff.comp_contMDiffOn (by
      simpa only [extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (x := p) (n := ∞)))
  have hψsmooth : ContMDiffOn 𝓘(ℝ, TangentSpace I p) I ∞ ψ
      (A ⁻¹' (extChartAt I p).target) :=
    (contMDiffOn_extChartAt_symm p).comp A.contDiff.contMDiff.contMDiffOn (fun _ h => h)
  have hψφ (x : M) (hx : x ∈ (extChartAt I p).source) : ψ (φ x) = x := by
    dsimp only [φ, ψ]
    rw [A.apply_symm_apply, (extChartAt I p).left_inv hx]
  have hV := Metric.eventually_tangent_transport_le g p hκ
  obtain ⟨V, hVV, hVo, hpV⟩ := mem_nhds_iff.mp hV
  have htarget : IsOpen (A ⁻¹' (extChartAt I p).target) :=
    (isOpen_extChartAt_target p).preimage A.continuous
  have hptarget : A (φ p) ∈ (extChartAt I p).target := by
    simpa only [φ, A.apply_symm_apply] using (extChartAt I p).map_source (mem_extChartAt_source p)
  have hψp : ContinuousAt ψ (φ p) :=
    (hψsmooth.continuousOn (φ p) hptarget).continuousAt (htarget.mem_nhds hptarget)
  have hpreV : ψ ⁻¹' V ∈ 𝓝 (φ p) := by
    apply hψp.preimage_mem_nhds
    rw [hψφ p (mem_extChartAt_source p)]
    exact hVo.mem_nhds hpV
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (htarget.mem_nhds hptarget) hpreV)
  let W : Set (TangentSpace I p) := Metric.ball (φ p) r
  let U : Set M := (extChartAt I p).source ∩ φ ⁻¹' W
  have hUo : IsOpen U := hφsmooth.continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_source p) isOpen_ball
  have hpU : p ∈ U := ⟨mem_extChartAt_source p, mem_ball_self hr⟩
  have hWV : ∀ v ∈ W, ψ v ∈ V := fun v hv => (hrsub hv).2
  have hWt : ∀ v ∈ W, A v ∈ (extChartAt I p).target := fun v hv => (hrsub hv).1
  have hUV : U ⊆ V := by
    intro x hx
    have h := hWV (φ x) hx.2
    rwa [hψφ x hx.1] at h
  have hφbound (x : M) (hx : x ∈ U) (v : TangentSpace I x) :
      ‖mfderiv I 𝓘(ℝ, TangentSpace I p) φ x v‖ ≤ κ * Real.sqrt (g.inner x v v) := by
    have hxs : x ∈ (chartAt H p).source := by simpa only [extChartAt_source] using hx.1
    have hder := mfderiv_comp x A.symm.hasMFDerivAt.mdifferentiableAt
      (mdifferentiableAt_extChartAt (I := I) hxs)
    change ‖mfderiv I 𝓘(ℝ, TangentSpace I p) (A.symm ∘ extChartAt I p) x v‖ ≤ _
    rw [hder, A.symm.hasMFDerivAt.mfderiv]
    change ‖A.symm (mfderiv I 𝓘(ℝ, E) (extChartAt I p) x v)‖ ≤ _
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt hxs]
    have hAs : (A.symm : E → TangentSpace I p) = e.symmL ℝ p :=
      e.symm_continuousLinearEquivAt_eq _
    rw [hAs, norm_eq_sqrt_real_inner]
    exact (hVV (hUV hx)).2.1 v
  have hψbound (v : TangentSpace I p) (hv : v ∈ W) (w : TangentSpace I p) :
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I ψ v w‖ ≤ κ * ‖w‖ := by
    have hvT := hWt v hv
    have hy := (extChartAt I p).map_target hvT
    have hs := ((contMDiffOn_extChartAt_symm (n := ∞) p) (A v) hvT).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hvT)
    have hder := mfderiv_comp v (hs.mdifferentiableAt (by simp)) A.hasMFDerivAt.mdifferentiableAt
    change ‖mfderiv 𝓘(ℝ, TangentSpace I p) I ((extChartAt I p).symm ∘ A) v w‖ ≤ _
    rw [hder, A.hasMFDerivAt.mfderiv]
    change ‖mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (A v) (A w)‖ ≤ _
    have htriv := TangentBundle.symmL_trivializationAt (I := I) (by
      simpa only [extChartAt_source] using hy)
    rw [ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ,
      (extChartAt I p).right_inv hvT] at htriv
    rw [← htriv]
    have hA : (A : TangentSpace I p → E) = e.continuousLinearMapAt ℝ p :=
      e.coe_continuousLinearEquivAt_eq _
    have hAw : A w = e.continuousLinearMapAt ℝ p w := congrFun hA w
    rw [hAw, norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    exact (hVV (hWV v hv)).2.2 w
  have hLip : LipschitzOnWith (κ * L) (f ∘ ψ) W := by
    intro v hv w hw
    have hdist : riemannianEDistOf g (ψ v) (ψ w) ≤ ENNReal.ofReal (κ * dist v w) := by
      apply riemannianEDist_le_of_mfderivWithin_le (s := W) (U := W)
        ((hψsmooth.mono (fun y hy => hWt y hy)).of_le (by simp)) Subset.rfl
      · intro y hy z
        rw [mfderivWithin_eq_mfderiv
          (isOpen_ball.uniqueMDiffWithinAt hy)
          (((hψsmooth y (hWt y hy)).contMDiffAt (htarget.mem_nhds (hWt y hy))).mdifferentiableAt (by simp)),
          ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hψbound y hy z)
      · exact (convex_ball (φ p) r).segment_subset hv hw
    calc edist (f (ψ v)) (f (ψ w)) ≤ (L : ℝ≥0∞) * riemannianEDistOf g (ψ v) (ψ w) := hf _ _
      _ ≤ (L : ℝ≥0∞) * ENNReal.ofReal (κ * dist v w) := mul_le_mul_right hdist _
      _ = (κ * L : ℝ≥0) * edist v w := by
        rw [ENNReal.ofReal_mul κ.coe_nonneg, edist_dist]
        simp only [ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul]
        ring
  obtain ⟨F, hF, hFeq⟩ := hLip.extend_real
  obtain ⟨G, hGs, hGL, hGlim⟩ := hF.exists_contDiff_lipschitz_tendstoUniformly
  refine ⟨U, hUo, hpU, fun ε hε => ?_⟩
  obtain ⟨n, hn⟩ := ((Metric.tendstoUniformly_iff.mp hGlim) ε hε).exists
  let h : M → ℝ := G n ∘ φ
  refine ⟨h, (hGs n).contMDiff.comp_contMDiffOn (hφsmooth.mono inter_subset_left), ?_, ?_⟩
  · intro x hx
    have heq : F (φ x) = f x := by
      rw [← hFeq hx.2]
      simp only [Function.comp_apply, hψφ x hx.1]
    simpa only [h, Function.comp_apply, heq, dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hn (φ x)
  · intro x hx v
    have hgd : MDifferentiableAt 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ) (G n) (φ x) :=
      ((hGs n).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    have hpd := ((hφsmooth x hx.1).contMDiffAt
      ((isOpen_extChartAt_source p).mem_nhds hx.1)).mdifferentiableAt (by simp)
    have hd := mfderiv_comp x hgd hpd
    change |(show ℝ from mfderiv I 𝓘(ℝ) (G n ∘ φ) x v)| ≤ _
    rw [hd]
    change |(show ℝ from mfderiv 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ) (G n) (φ x)
      (mfderiv I 𝓘(ℝ, TangentSpace I p) φ x v))| ≤ _
    rw [mfderiv_eq_fderiv, ← Real.norm_eq_abs]
    have hb := (fderiv ℝ (G n) (φ x)).le_opNorm (mfderiv I 𝓘(ℝ, TangentSpace I p) φ x v)
    calc _ ≤ ‖fderiv ℝ (G n) (φ x)‖ * ‖mfderiv I 𝓘(ℝ, TangentSpace I p) φ x v‖ := hb
      _ ≤ (κ * L : ℝ≥0) * (κ * Real.sqrt (g.inner x v v)) :=
        mul_le_mul (norm_fderiv_le_of_lipschitz ℝ (hGL n)) (hφbound x hx v)
          (norm_nonneg _) (by positivity)
      _ = _ := by simp only [NNReal.coe_mul]; ring

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
set_option backward.isDefEq.respectTransparency false in
private theorem partition_derivative_cancel {n : ℕ} {f : M → ℝ} (hf : Continuous f)
    (ρ : SmoothPartitionOfUnity (Fin n) I M (tsupport f)) (x : M)
    (v : TangentSpace I x) :
    f x * (∑ i, (show ℝ from mfderiv I 𝓘(ℝ) (ρ i) x v)) = 0 := by
  classical
  by_cases hx : f x = 0
  · rw [hx, zero_mul]
  · have heq : (fun y => ∑ i, ρ i y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [hf.continuousAt.eventually_ne hx] with y hy
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (subset_tsupport f hy)
    have hd := HasMFDerivAt.sum (t := Finset.univ)
      (fun i _ => ((ρ i).contMDiff.mdifferentiable (by simp) x).hasMFDerivAt)
    have he : (∑ i, (show TangentSpace I x →L[ℝ] ℝ from mfderiv I 𝓘(ℝ) (ρ i) x)) = 0 := by
      rw [← hd.mfderiv]
      rw [show (∑ i, (ρ i : M → ℝ)) = (fun y => ∑ i, ρ i y) by ext y; simp]
      rw [heq.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero]
    have hev := congrArg (fun A : TangentSpace I x →L[ℝ] ℝ => A v) he
    simp only [sum_apply, zero_apply] at hev
    exact mul_eq_zero_of_right (f x) hev
omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
set_option backward.isDefEq.respectTransparency false in
private theorem partition_mul_derivative {n : ℕ} {K : Set M}
    (ρ : SmoothPartitionOfUnity (Fin n) I M K) {F : Fin n → M → ℝ}
    (hF : ∀ i, ∀ x ∈ tsupport (ρ i), ContMDiffAt I 𝓘(ℝ) ∞ (F i) x)
    (x : M) :
    mfderiv I 𝓘(ℝ) (fun y => ∑ i, ρ i y * F i y) x =
      ∑ i, (ρ i x • (show TangentSpace I x →L[ℝ] ℝ from mfderiv I 𝓘(ℝ) (F i) x) +
        F i x • (show TangentSpace I x →L[ℝ] ℝ from mfderiv I 𝓘(ℝ) (ρ i) x)) := by
  classical
  have hd (i : Fin n) : HasMFDerivAt I 𝓘(ℝ) (fun y => ρ i y * F i y) x
      (ρ i x • (show TangentSpace I x →L[ℝ] ℝ from mfderiv I 𝓘(ℝ) (F i) x) +
        F i x • (show TangentSpace I x →L[ℝ] ℝ from mfderiv I 𝓘(ℝ) (ρ i) x)) := by
    by_cases hx : x ∈ tsupport (ρ i)
    · exact ((ρ i).contMDiff.mdifferentiable (by simp) x).hasMFDerivAt.mul
        ((hF i x hx).mdifferentiableAt (by simp)).hasMFDerivAt
    · have heq : (ρ i : M → ℝ) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        notMem_tsupport_iff_eventuallyEq.mp hx
      have hz : mfderiv I 𝓘(ℝ) (ρ i) x = 0 := by
        rw [heq.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero]
      have hz0 := image_eq_zero_of_notMem_tsupport hx
      rw [hz0, hz, zero_smul, smul_zero, add_zero]
      apply (hasMFDerivAt_const (I := I) (c := (0 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [heq] with y hy
      rw [hy, zero_mul]
  have hsum := (HasMFDerivAt.sum (t := Finset.univ) (fun i _ => hd i)).mfderiv
  rw [show (∑ i, fun y => ρ i y * F i y) = (fun y => ∑ i, ρ i y * F i y) by
    ext y; simp] at hsum
  exact hsum
omit [FiniteDimensional ℝ E] [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
private theorem partition_derivative_bound {n : ℕ} (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : Continuous f) (ρ : SmoothPartitionOfUnity (Fin n) I M (tsupport f))
    {F : Fin n → M → ℝ} (hF : ∀ i, ∀ x ∈ tsupport (ρ i), ContMDiffAt I 𝓘(ℝ) ∞ (F i) x)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (C : Fin n → ℝ≥0)
    (hC : ∀ i x (v : TangentSpace I x),
      |(show ℝ from mfderiv I 𝓘(ℝ) (ρ i) x v)| ≤ C i * Real.sqrt (g.inner x v v))
    (herr : ∀ i x, x ∈ tsupport (ρ i) → |F i x - f x| ≤ δ)
    (hbound : ∀ i x, x ∈ tsupport (ρ i) → ∀ v : TangentSpace I x,
      |(show ℝ from mfderiv I 𝓘(ℝ) (F i) x v)| ≤ A * Real.sqrt (g.inner x v v))
    (x : M) (v : TangentSpace I x) :
    |(show ℝ from mfderiv I 𝓘(ℝ) (fun y => ∑ i, ρ i y * F i y) x v)| ≤
      (A + δ * ∑ i, (C i : ℝ)) * Real.sqrt (g.inner x v v) := by
  classical
  let dF (i : Fin n) : ℝ := mfderiv I 𝓘(ℝ) (F i) x v
  let dρ (i : Fin n) : ℝ := mfderiv I 𝓘(ℝ) (ρ i) x v
  let r := Real.sqrt (g.inner x v v)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hd : (show ℝ from mfderiv I 𝓘(ℝ) (fun y => ∑ i, ρ i y * F i y) x v) =
      ∑ i, (ρ i x * dF i + F i x * dρ i) := by
    have he := congrArg (fun D : TangentSpace I x →L[ℝ] ℝ => D v)
      (partition_mul_derivative ρ hF x)
    simp only [sum_apply, add_apply, smul_apply, smul_eq_mul] at he
    convert he using 1
  have hcancel : f x * ∑ i, dρ i = 0 := partition_derivative_cancel hf ρ x v
  have hrewrite : (∑ i, (ρ i x * dF i + F i x * dρ i)) =
      ∑ i, (ρ i x * dF i + (F i x - f x) * dρ i) := by
    calc
      _ = (∑ i, (ρ i x * dF i + (F i x - f x) * dρ i)) + f x * ∑ i, dρ i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hcancel, add_zero]
  have hi (i : Fin n) : |ρ i x * dF i + (F i x - f x) * dρ i| ≤
      ρ i x * (A * r) + δ * (C i * r) := by
    by_cases hx : x ∈ tsupport (ρ i)
    · calc
        _ ≤ |ρ i x * dF i| + |(F i x - f x) * dρ i| := abs_add_le _ _
        _ = ρ i x * |dF i| + |F i x - f x| * |dρ i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (ρ.nonneg i x)]
        _ ≤ ρ i x * (A * r) + δ * (C i * r) :=
          add_le_add (mul_le_mul_of_nonneg_left (hbound i x hx v) (ρ.nonneg i x))
            (mul_le_mul (herr i x hx) (hC i x v) (abs_nonneg _) hδ)
    · have hz : ρ i x = 0 := image_eq_zero_of_notMem_tsupport hx
      have heq : (ρ i : M → ℝ) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        notMem_tsupport_iff_eventuallyEq.mp hx
      have hdρ : dρ i = 0 := by
        dsimp only [dρ]
        rw [heq.mfderiv_eq, mfderiv_const]
        rfl
      simp only [hz, hdρ, mul_zero, zero_mul, add_zero, abs_zero, zero_add]
      positivity
  have hsum : ∑ i, ρ i x ≤ 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_le_one x
  rw [hd, hrewrite]
  calc
    _ ≤ ∑ i, |ρ i x * dF i + (F i x - f x) * dρ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (ρ i x * (A * r) + δ * (C i * r)) := Finset.sum_le_sum (fun i _ => hi i)
    _ = (∑ i, ρ i x) * (A * r) + δ * (∑ i, (C i : ℝ)) * r := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    _ ≤ 1 * (A * r) + δ * (∑ i, (C i : ℝ)) * r := by gcongr
    _ = _ := by ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiff_approximation_of_lipschitz_hasCompactSupport
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {L : ℝ≥0}
    (hf : ∀ x y, edist (f x) (f y) ≤ (L : ℝ≥0∞) * riemannianEDistOf g x y)
    (hc : HasCompactSupport f) {U₀ : Set M} (hU₀ : IsOpen U₀)
    (hsub : tsupport f ⊆ U₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ h ∧ HasCompactSupport h ∧
      tsupport h ⊆ U₀ ∧ (∀ x, |h x - f x| < ε) ∧
      ∀ x (v : TangentSpace I x),
        |(show ℝ from mfderiv I 𝓘(ℝ) h x v)| ≤ (L + ε) * Real.sqrt (g.inner x v v) := by
  classical
  have : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  have : NormalSpace M := inferInstance
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  have hfcont : Continuous f := by
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    let : PseudoEMetricSpace M := .ofRiemannianMetric I M
    exact (show LipschitzWith L f from hf).continuous
  have hn : {k : ℝ | k ^ 2 * L < L + ε / 2} ∈ 𝓝 (1 : ℝ) := by
    exact (show ContinuousAt (fun k : ℝ => k ^ 2 * L) 1 by fun_prop).preimage_mem_nhds
      (Iio_mem_nhds (show 1 ^ 2 * (L : ℝ) < L + ε / 2 by nlinarith))
  obtain ⟨r, hr, hrmem⟩ := Metric.mem_nhds_iff.mp hn
  let κ : ℝ≥0 := ⟨1 + r / 2, by linarith⟩
  have hκ : (1 : ℝ) < κ := by change 1 < 1 + r / 2; linarith
  have hκbound : (κ : ℝ) ^ 2 * L < L + ε / 2 := by
    apply hrmem
    change dist (1 + r / 2) 1 < r
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  choose U hU hpU happ using fun p => local_smooth_approx g hf hκ p
  obtain ⟨Q, hQ, hKQ, hQU⟩ := exists_compact_between hc hU₀ hsub
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun p => U p ∩ interior Q)
    (fun p => (hU p).inter isOpen_interior)
    (fun x hx => mem_iUnion.mpr ⟨x, hpU x, hKQ hx⟩)
  let e : t ≃ Fin t.card := Finset.equivFinOfCardEq rfl
  let p (i : Fin t.card) : M := (e.symm i).val
  let V (i : Fin t.card) := U (p i) ∩ interior Q
  have hV (i : Fin t.card) : IsOpen (V i) := (hU _).inter isOpen_interior
  have hcover : tsupport f ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨q, hqt, hxq⟩ := mem_iUnion₂.mp (ht hx)
    refine mem_iUnion.mpr ⟨e ⟨q, hqt⟩, ?_⟩
    simpa only [V, p, e.symm_apply_apply] using hxq
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := I) hc.isClosed V hV hcover
  have hρc (i : Fin t.card) : HasCompactSupport (ρ i : M → ℝ) :=
    hQ.of_isClosed_subset (isClosed_tsupport _) (fun x hx => interior_subset (hρ i hx).2)
  choose C hC using fun i => exists_metric_mfderiv_bound_of_hasCompactSupport g
    ((ρ i).contMDiff.of_le (by simp)) (hρc i)
  let S : ℝ := ∑ i, (C i : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)
  let δ := (ε / 2) / (S + 1)
  have hδ : 0 < δ := div_pos (half_pos hε) (by linarith)
  have hδeq : δ * (S + 1) = ε / 2 := div_mul_cancel₀ _ (by linarith)
  have hδle : δ < ε := by nlinarith [mul_nonneg hδ.le hS]
  have hδS : δ * S ≤ ε / 2 := by nlinarith
  choose F hFs hFerr hFbound using fun i : Fin t.card => happ (p i) δ hδ
  have hFat (i : Fin t.card) (x : M) (hx : x ∈ tsupport (ρ i)) :
      ContMDiffAt I 𝓘(ℝ) ∞ (F i) x :=
    (hFs i x (hρ i hx).1).contMDiffAt ((hU (p i)).mem_nhds (hρ i hx).1)
  let h : M → ℝ := fun x => ∑ i, ρ i x * F i x
  have hs : ContMDiff I 𝓘(ℝ) ∞ h := by
    simpa only [finsum_eq_sum_of_fintype, smul_eq_mul] using ρ.contMDiff_finsum_smul hFat
  have hhsupp : tsupport h ⊆ Q := by
    apply closure_minimal _ hQ.isClosed
    intro x hx
    by_contra hxQ
    apply hx
    apply Finset.sum_eq_zero
    intro i _
    have hi : ρ i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hxρ => hxQ (interior_subset (hρ i hxρ).2))
    rw [hi, zero_mul]
  refine ⟨h, hs, hQ.of_isClosed_subset (isClosed_tsupport _) hhsupp, hhsupp.trans hQU, ?_, ?_⟩
  · intro x
    have hsum : ∑ i, ρ i x ≤ 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_le_one x
    have heq : h x - f x = ∑ i, ρ i x * (F i x - f x) := by
      rw [show (∑ i, ρ i x * (F i x - f x)) = h x - (∑ i, ρ i x) * f x by
        simp only [h, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]]
      by_cases hx : f x = 0
      · rw [hx, mul_zero]
      · have hsumone : ∑ i, ρ i x = 1 := by
          simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (subset_tsupport f hx)
        rw [hsumone, one_mul]
    have hi (i : Fin t.card) : |ρ i x * (F i x - f x)| ≤ ρ i x * δ := by
      by_cases hx : x ∈ tsupport (ρ i)
      · rw [abs_mul, abs_of_nonneg (ρ.nonneg i x)]
        exact mul_le_mul_of_nonneg_left (hFerr i x (hρ i hx).1).le (ρ.nonneg i x)
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul, abs_zero]
    calc
      |h x - f x| = |∑ i, ρ i x * (F i x - f x)| := congrArg abs heq
      _ ≤ ∑ i, |ρ i x * (F i x - f x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ρ i x * δ := Finset.sum_le_sum (fun i _ => hi i)
      _ = (∑ i, ρ i x) * δ := (Finset.sum_mul ..).symm
      _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hsum hδ.le
      _ < ε := by simpa only [one_mul] using hδle
  · intro x v
    apply (partition_derivative_bound g hfcont ρ hFat (by positivity) hδ.le C
      (fun i x v => by
        have hi := hC i x v
        change ‖(show ℝ from mfderiv I 𝓘(ℝ) (ρ i) x v)‖ ≤ _ at hi
        rwa [Real.norm_eq_abs] at hi)
      (fun i x hx => (hFerr i x (hρ i hx).1).le)
      (fun i x hx => hFbound i x (hρ i hx).1) x v).trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    change (κ : ℝ) ^ 2 * L + δ * S ≤ L + ε
    linarith

end DifferentialGeometry.Geometry
