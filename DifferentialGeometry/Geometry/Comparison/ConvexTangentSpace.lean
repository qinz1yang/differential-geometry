import DifferentialGeometry.Geometry.Comparison.ConvexTangentCone
import DifferentialGeometry.Geometry.Comparison.Soul.SliceTangent

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem riemannian_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem dist_intrinsicGeodesic_le (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (p : M) (v : TangentSpace I p) {s t : ℝ}
    (hst : s ≤ t) :
    dist (intrinsicGeodesic (I := I) g hEnorm p v s)
        (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ Real.sqrt (g.inner p v v) * (t - s) := by
  have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p v hst
  rw [← riemannian_toReal_eq_dist (I := I)]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (by linarith))]

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem branch_source_tube
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) :
    ∃ A ∈ 𝓝 p, ∃ r : ℝ, 0 < r ∧ ∀ y ∈ A, ∀ v : TangentSpace I y,
      Real.sqrt (g.inner y v v) < r → (⟨y, v⟩ : TangentBundle I M) ∈ B.hom.source := by
  let e := trivializationAt E (TangentSpace I) p
  let O : Set (M × E) := e '' (e.source ∩ B.hom.source)
  have hpbase : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  have hO : IsOpen O := e.toOpenPartialHomeomorph.isOpen_image_source_inter B.hom.open_source
  have hpO : (p, (0 : E)) ∈ O := by
    refine ⟨⟨p, 0⟩, ⟨?_, B.zero_mem⟩, e.zeroSection ℝ hpbase⟩
    rwa [e.mem_source]
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 (hO.mem_nhds hpO)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨C, hC, hbound⟩ := eventually_norm_trivializationAt_lt E (fun x : M => TangentSpace I x) p
  change ∀ᶠ y in 𝓝 p, ‖e.continuousLinearMapAt ℝ y‖ < C at hbound
  let A := (U ∩ {y | ‖e.continuousLinearMapAt ℝ y‖ < C}) ∩ e.baseSet
  have hA : A ∈ 𝓝 p := inter_mem (inter_mem hU hbound) (e.open_baseSet.mem_nhds hpbase)
  refine ⟨A, hA, r / C, div_pos hr hC, ?_⟩
  intro y hy v hv
  have hnorm : ‖v‖ = Real.sqrt (g.inner y v v) := by
    have h := hEnorm y v
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) (Real.sqrt_nonneg _)).1 h
  let w := e.continuousLinearMapAt ℝ y v
  have hw : ‖w‖ < r := by
    calc
      ‖w‖ ≤ ‖e.continuousLinearMapAt ℝ y‖ * ‖v‖ := (e.continuousLinearMapAt ℝ y).le_opNorm v
      _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right hy.1.2.le (norm_nonneg v)
      _ < C * (r / C) := mul_lt_mul_of_pos_left (by rwa [hnorm]) hC
      _ = r := mul_div_cancel₀ r hC.ne'
  have hwV : w ∈ V := hrV (by simpa only [Metric.mem_ball, dist_zero_right] using hw)
  obtain ⟨z, hz, hez⟩ := hUV (Set.mk_mem_prod hy.1.1 hwV)
  have hvsource : (⟨y, v⟩ : TangentBundle I M) ∈ e.source := by
    rw [e.mem_source]
    exact hy.2
  have hev : e (⟨y, v⟩ : TangentBundle I M) = (y, w) := by
    rw [e.apply_eq_prod_continuousLinearEquivAt ℝ y hy.2 v]
    exact congrArg (fun a : E => (y, a)) (congrFun (e.coe_continuousLinearEquivAt_eq hy.2) v)
  have hzv := e.toOpenPartialHomeomorph.injOn hz.1 hvsource (hez.trans hev.symm)
  exact hzv ▸ hz.2

private theorem branch_minimizing_pair
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) :
    ∀ᶠ yz : M × M in 𝓝 (p, p),
      yz.2 ∈ (B.fixed yz.1).hom.target ∧
      (B.fixed yz.1).hom.symm yz.2 = (minimizingVec (I := I) g hEnorm yz.1 yz.2 : E) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, t • (B.fixed yz.1).hom.symm yz.2 ∈ (B.fixed yz.1).hom.source) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        (B.fixed yz.1).hom (t • (B.fixed yz.1).hom.symm yz.2) =
          minJoin (I := I) g hEnorm yz.1 yz.2 t := by
  obtain ⟨A, hA, r, hr, hsource⟩ := branch_source_tube B
  have hdist : {yz : M × M | dist yz.1 yz.2 < r} ∈ 𝓝 (p, p) :=
    (isOpen_lt (continuous_fst.dist continuous_snd) continuous_const).mem_nhds (by simpa using hr)
  filter_upwards [continuous_fst.continuousAt hA, hdist] with yz hyA hyd
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (⟨yz.1, t • minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ : TangentBundle I M)
        ∈ B.hom.source := by
    apply hsource yz.1 hyA
    rw [sqrt_gInner_smul_self (I := I) g yz.1 ht.1, minimizingVec_len,
      riemannian_toReal_eq_dist (I := I)]
    exact (mul_le_of_le_one_left dist_nonneg ht.2).trans_lt hyd
  have hvsource : (⟨yz.1, minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ : TangentBundle I M)
      ∈ B.hom.source := by
    simpa only [one_smul] using hseg 1 ⟨zero_le_one, le_rfl⟩
  have hEq := B.inv_eq_of_exp hvsource (minimizingVec_exp (I := I) g hEnorm yz.1 yz.2)
  have hinv : (B.fixed yz.1).hom.symm yz.2 = (minimizingVec (I := I) g hEnorm yz.1 yz.2 : E) :=
    congrArg (fun z : TangentBundle I M => (z.snd : E)) hEq
  have htarget : yz.2 ∈ (B.fixed yz.1).hom.target := by
    have hh := B.hom.map_source hvsource
    have heq : B.hom (⟨yz.1, minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ : TangentBundle I M) =
        diagExp (I := I) g hEnorm ⟨yz.1, minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ :=
      B.hom_eq hvsource
    rw [heq] at hh
    have hpairmem : (yz.1, yz.2) ∈ B.hom.target := by
      simpa only [diagExp, minimizingVec_exp] using hh
    exact (DiagonalInverseBranch.fixed_target (p := yz.1) B yz.2).2 hpairmem
  refine ⟨htarget, hinv, ?_, ?_⟩
  · intro t ht
    rw [hinv]
    exact hseg t ht
  · intro t ht
    rw [hinv]
    change expMapIntrinsic (I := I) g hEnorm yz.1
      (t • minimizingVec (I := I) g hEnorm yz.1 yz.2) = minJoin (I := I) g hEnorm yz.1 yz.2 t
    exact intrinsicGeodesic_smul (I := I) g hEnorm yz.1
      (minimizingVec (I := I) g hEnorm yz.1 yz.2) t



omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem mem_sliceTangent_of_isInnerDirection
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {C : Set M} {x : M} {v : TangentSpace I x}
    (hv : IsInnerDirection (I := I) g hEnorm C x v) :
    v ∈ sliceTangent I (maxSliceLocus I C) x := by
  have hgeo : ContMDiff 𝓘(ℝ, ℝ) I ∞ (intrinsicGeodesic (I := I) g hEnorm x v) :=
    isGeodesic_contMDiff (I := I) g (intrinsicGeodesic_isGeodesic (I := I) g hEnorm x v)
      (intrinsicGeodesic_continuous (I := I) g hEnorm x v)
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm x v) 0 :=
    hgeo.contMDiffAt.mdifferentiableAt (by simp)
  have h0 : intrinsicGeodesic (I := I) g hEnorm x v 0 = x :=
    intrinsicGeodesic_zero (I := I) g hEnorm x v
  have hmem := mem_sliceTangent_of_curve (I := I) (S := maxSliceLocus I C) h0
    (isInnerDirection_iff.1 hv) hmd
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm x v) 0
      (show TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) from (1 : ℝ)) : TangentSpace I x) = v :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x v
  rwa [hvel] at hmem

theorem finrank_sliceTangent_maxSliceLocus
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) {x : M}
    (hx : x ∈ maxSliceLocus I C) :
    Module.finrank ℝ (sliceTangent I (maxSliceLocus I C) x) = maxSliceDim I C :=
  finrank_sliceTangent (isEmbeddedSlice_maxSliceLocus hEnorm hC) hx



theorem isInnerDirection_of_mem_sliceTangent
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) {x : M}
    (hx : x ∈ maxSliceLocus I C) {v : TangentSpace I x}
    (hv : v ∈ sliceTangent I (maxSliceLocus I C) x) :
    IsInnerDirection (I := I) g hEnorm C x v := by
  set B := standardDiagonalInverseBranch (I := I) g hEnorm x with hBdef
  set Ψ := tangentSpaceModelContinuousLinearEquiv (I := I) (M := M) x with hΨdef
  have happ : ∀ u ∈ (B.fixed x).hom.source,
      (B.fixed x).hom u = expMapIntrinsic (I := I) g hEnorm x (Ψ.symm u) :=
    fun u hu => ((B.fixed x).hom_eq hu).symm
  have h0src : (0 : E) ∈ (B.fixed x).hom.source := B.zero_mem
  have hzeroexp : (B.fixed x).hom (0 : E) = x := by
    rw [happ 0 h0src, ContinuousLinearEquiv.map_zero]
    exact expMapIntrinsic_zero (I := I) g hEnorm x
  have hxT : x ∈ (B.fixed x).hom.target := by
    have hmap := (B.fixed x).hom.map_source h0src
    rwa [hzeroexp] at hmap
  have hsymm0 : (B.fixed x).hom.symm x = (0 : E) := by
    have hleft := (B.fixed x).hom.toPartialEquiv.left_inv h0src
    rwa [hzeroexp] at hleft
  have hmap1 : Tendsto (fun y : M => (x, y)) (𝓝 x) (𝓝 (x, x)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hmap2 : Tendsto (fun y : M => (y, x)) (𝓝 x) (𝓝 (x, x)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hmin := hmap1.eventually (branch_minimizing_pair (I := I) B)
  have hjoin := hmap2.eventually (maxSliceLocus_minJoin (C := C) hEnorm hC B)
  have hgood : ∀ᶠ y in 𝓝 x,
      (∀ t ∈ Icc (0 : ℝ) 1, t • (B.fixed x).hom.symm y ∈ (B.fixed x).hom.source) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (B.fixed x).hom (t • (B.fixed x).hom.symm y) =
        minJoin (I := I) g hEnorm x y t) ∧
      (y ∈ maxSliceLocus I C →
        ∀ t ∈ Icc (0 : ℝ) 1, minJoin (I := I) g hEnorm x y t ∈ maxSliceLocus I C) ∧
      y ∈ (B.fixed x).hom.target := by
    filter_upwards [hmin, hjoin, (B.fixed x).hom.open_target.mem_nhds hxT] with y h1 h2 h3
    exact ⟨h1.2.2.1, h1.2.2.2, fun hy => h2 hy hx, h3⟩
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.1 hgood
  have hWT : W ⊆ (B.fixed x).hom.target := fun y hy => (hWsub hy).2.2.2
  set V : Set E := (B.fixed x).hom.symm '' (maxSliceLocus I C ∩ W) with hVdef
  have hVslice : IsEmbeddedSlice 𝓘(ℝ, E) (maxSliceDim I C) V :=
    ((isEmbeddedSlice_maxSliceLocus hEnorm hC).inter_open hWopen).image
      (B.fixed x).hom.symm (fun y hy => hWT hy.2)
  have h0V : (0 : E) ∈ V := ⟨x, ⟨hx, hxW⟩, hsymm0⟩
  have hVinner : ∀ u ∈ V, IsInnerDirection (I := I) g hEnorm C x (Ψ.symm u) := by
    rintro _ ⟨y, ⟨hyN, hyW⟩, rfl⟩
    obtain ⟨hsrc, hchord, hjoinN, -⟩ := hWsub hyW
    rw [isInnerDirection_iff]
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hgeo : intrinsicGeodesic (I := I) g hEnorm x (Ψ.symm ((B.fixed x).hom.symm y)) t =
        expMapIntrinsic (I := I) g hEnorm x (t • Ψ.symm ((B.fixed x).hom.symm y)) :=
      (intrinsicGeodesic_smul (I := I) g hEnorm x _ t).symm
    rw [hgeo, ← ContinuousLinearEquiv.map_smul, ← happ _ (hsrc t htIcc), hchord t htIcc]
    exact hjoinN hyN t htIcc
  set L : Submodule ℝ E :=
    Submodule.map (Ψ.toLinearEquiv : TangentSpace I x →ₗ[ℝ] E)
      (sliceTangent I (maxSliceLocus I C) x) with hLdef
  have hmemL : ∀ u : E, u ∈ L ↔ Ψ.symm u ∈ sliceTangent I (maxSliceLocus I C) x := by
    intro u
    rw [hLdef]
    simp [Submodule.mem_map_equiv]
  have hVL : V ⊆ (L : Set E) := fun u hu =>
    (hmemL u).2 (mem_sliceTangent_of_isInnerDirection (hVinner u hu))
  have hdimL : Module.finrank ℝ L = maxSliceDim I C := by
    rw [hLdef, LinearEquiv.finrank_map_eq]
    exact finrank_sliceTangent_maxSliceLocus hEnorm hC hx
  have hnhds := hVslice.preimage_val_mem_nhds hVL hdimL h0V
  have hvL : (Ψ v : E) ∈ L := (hmemL _).2 (by rw [ContinuousLinearEquiv.symm_apply_apply]; exact hv)
  have hz : ((0 : ℝ) • (⟨Ψ v, hvL⟩ : L)) = ⟨0, L.zero_mem⟩ := by
    ext
    simp
  have hc : ContinuousAt (fun s : ℝ => (s • ⟨Ψ v, hvL⟩ : L)) 0 :=
    (continuous_id.smul continuous_const).continuousAt
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), (s • (Ψ v : E)) ∈ V := by
    have h := hc.preimage_mem_nhds (by rw [hz]; exact hnhds)
    filter_upwards [h] with s hs
    exact hs
  rw [isInnerDirection_iff]
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with s hs
  obtain ⟨y, ⟨hyN, hyW⟩, hy⟩ := hs
  have hsrcy : (B.fixed x).hom.symm y ∈ (B.fixed x).hom.source :=
    (B.fixed x).hom.toPartialEquiv.map_target (hWT hyW)
  have hval : (B.fixed x).hom ((B.fixed x).hom.symm y) = y :=
    (B.fixed x).hom.toPartialEquiv.right_inv (hWT hyW)
  have hgeo : intrinsicGeodesic (I := I) g hEnorm x v s =
      expMapIntrinsic (I := I) g hEnorm x (s • v) :=
    (intrinsicGeodesic_smul (I := I) g hEnorm x v s).symm
  have hpsi : Ψ.symm (s • (Ψ v : E)) = s • v := by
    rw [← ContinuousLinearEquiv.map_smul, ContinuousLinearEquiv.symm_apply_apply]
  have hsrcs : (s • (Ψ v : E)) ∈ (B.fixed x).hom.source := by
    rw [← hy]
    exact hsrcy
  rw [hgeo, ← hpsi, ← happ _ hsrcs, ← hy, hval]
  exact hyN



theorem mem_maxSliceLocus_of_mem_sliceTangent
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {x : M} (hx : x ∈ maxSliceLocus I C) {v : TangentSpace I x}
    (hv : v ∈ sliceTangent I (maxSliceLocus I C) x)
    {O : Set M} (hOsub : O ∩ C ⊆ maxSliceLocus I C) {T : ℝ} (hT : 0 ≤ T)
    (hstay : ∀ t ∈ Icc (0 : ℝ) T, intrinsicGeodesic (I := I) g hEnorm x v t ∈ O) :
    ∀ t ∈ Icc (0 : ℝ) T,
      intrinsicGeodesic (I := I) g hEnorm x v t ∈ maxSliceLocus I C := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x v with hγdef
  have hγcont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm x v
  have hγ0 : γ 0 = x := intrinsicGeodesic_zero (I := I) g hEnorm x v
  set A : Set ℝ :=
    {t | t ∈ Icc (0 : ℝ) T ∧ ∀ s ∈ Icc (0 : ℝ) t, γ s ∈ maxSliceLocus I C} with hAdef
  have h0A : (0 : ℝ) ∈ A := by
    refine ⟨⟨le_rfl, hT⟩, fun s hs => ?_⟩
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    rw [hs0, hγ0]
    exact hx
  have hAne : A.Nonempty := ⟨0, h0A⟩
  have hAbdd : BddAbove A := ⟨T, fun t ht => ht.1.2⟩
  have hb0 : (0 : ℝ) ≤ sSup A := le_csSup hAbdd h0A
  have hbT : sSup A ≤ T := csSup_le hAne fun t ht => ht.1.2
  have hbelow : ∀ s, 0 ≤ s → s < sSup A → γ s ∈ maxSliceLocus I C := by
    intro s hs hsb
    obtain ⟨t, htA, hst⟩ := exists_lt_of_lt_csSup hAne hsb
    exact htA.2 s ⟨hs, hst.le⟩
  have hbN : γ (sSup A) ∈ maxSliceLocus I C := by
    rcases eq_or_lt_of_le hb0 with hb | hb
    · rw [← hb, hγ0]
      exact hx
    · have hlim : Tendsto γ (𝓝[<] sSup A) (𝓝 (γ (sSup A))) :=
        hγcont.continuousAt.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ s in 𝓝[<] sSup A, γ s ∈ maxSliceLocus I C := by
        filter_upwards [Ioo_mem_nhdsLT hb] with s hs
        exact hbelow s hs.1.le hs.2
      have hclos : γ (sSup A) ∈ closure (maxSliceLocus I C) :=
        mem_closure_of_tendsto hlim hev
      have hCmem : γ (sSup A) ∈ C := by
        have h1 : closure (maxSliceLocus I C) ⊆ closure C :=
          closure_mono maxSliceLocus_subset
        rw [hCclosed.closure_eq] at h1
        exact h1 hclos
      exact hOsub ⟨hstay _ ⟨hb0, hbT⟩, hCmem⟩
  have hbA : sSup A ∈ A := by
    refine ⟨⟨hb0, hbT⟩, fun s hs => ?_⟩
    rcases eq_or_lt_of_le hs.2 with hsb | hsb
    · rw [hsb]
      exact hbN
    · exact hbelow s hs.1 hsb
  have hbeqT : sSup A = T := by
    by_contra hne
    have hblt : sSup A < T := lt_of_le_of_ne hbT hne
    have hcontn := intrinsicGeodesic_continuation (I := I) g hEnorm x v (sSup A)
    rw [← hγdef] at hcontn
    have huT : mfderiv 𝓘(ℝ, ℝ) I γ (sSup A) (1 : ℝ) ∈
        sliceTangent I (maxSliceLocus I C) (γ (sSup A)) := by
      rcases eq_or_lt_of_le hb0 with hb | hb
      · have hvel : mfderiv 𝓘(ℝ, ℝ) I γ (sSup A) (1 : ℝ) =
            (show TangentSpace I (γ (sSup A)) from v) := by
          rw [← hb]
          exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x v
        rw [hvel, ← hb, hγ0]
        exact hv
      · have hback : IsInnerDirection (I := I) g hEnorm C (γ (sSup A))
            (-(mfderiv 𝓘(ℝ, ℝ) I γ (sSup A) (1 : ℝ))) := by
          rw [isInnerDirection_iff]
          filter_upwards [Ioo_mem_nhdsGT hb] with s hs
          rw [intrinsicGeodesic_neg, ← congrFun hcontn (-s)]
          exact hbA.2 (-s + sSup A) ⟨by linarith [hs.1, hs.2], by linarith [hs.1]⟩
        have hmem := mem_sliceTangent_of_isInnerDirection hback
        have := (sliceTangent I (maxSliceLocus I C) (γ (sSup A))).neg_mem hmem
        rwa [neg_neg] at this
    have hinner : IsInnerDirection (I := I) g hEnorm C (γ (sSup A))
        (mfderiv 𝓘(ℝ, ℝ) I γ (sSup A) (1 : ℝ)) :=
      isInnerDirection_of_mem_sliceTangent hEnorm hC hbN huT
    rw [isInnerDirection_iff] at hinner
    obtain ⟨Z, hZopen, hZ0, hZsub⟩ := mem_nhdsWithin.1 hinner
    obtain ⟨δ, hδpos, hδball⟩ := Metric.isOpen_iff.1 hZopen 0 hZ0
    set s₀ : ℝ := min (δ / 2) ((T - sSup A) / 2) with hs₀def
    have hs₀pos : 0 < s₀ := lt_min (by linarith) (by linarith)
    have hs₀δ : s₀ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hs₀T : sSup A + s₀ ≤ T := by
      have := min_le_right (δ / 2) ((T - sSup A) / 2)
      linarith
    have hnext : sSup A + s₀ ∈ A := by
      refine ⟨⟨by linarith, hs₀T⟩, fun r hr => ?_⟩
      rcases le_or_gt r (sSup A) with hrb | hrb
      · exact hbA.2 r ⟨hr.1, hrb⟩
      · have hmem : r - sSup A ∈ Z ∩ Ioi (0 : ℝ) := by
          refine ⟨hδball ?_, by simpa using sub_pos.2 hrb⟩
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (sub_pos.2 hrb)]
          have := hr.2
          linarith
        have hgood : intrinsicGeodesic (I := I) g hEnorm (γ (sSup A))
            (mfderiv 𝓘(ℝ, ℝ) I γ (sSup A) (1 : ℝ)) (r - sSup A) ∈ maxSliceLocus I C :=
          hZsub hmem
        rw [← congrFun hcontn (r - sSup A)] at hgood
        have harg : r - sSup A + sSup A = r := by ring
        rwa [harg] at hgood
    have := le_csSup hAbdd hnext
    linarith
  intro t ht
  rw [← hbeqT] at ht
  exact hbA.2 t ht

theorem expMapIntrinsic_mem_maxSliceLocus
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {x : M} (hx : x ∈ maxSliceLocus I C) {v : TangentSpace I x}
    (hv : v ∈ sliceTangent I (maxSliceLocus I C) x)
    (hlen : Real.sqrt (g.inner x v v) < Metric.infDist x (relBoundary I C)) :
    expMapIntrinsic (I := I) g hEnorm x v ∈ maxSliceLocus I C := by
  have hstay : ∀ t ∈ Icc (0 : ℝ) 1,
      intrinsicGeodesic (I := I) g hEnorm x v t ∈
        Metric.ball x (Metric.infDist x (relBoundary I C)) := by
    intro t ht
    rw [Metric.mem_ball, dist_comm]
    have h := dist_intrinsicGeodesic_le g hEnorm x v (s := 0) (t := t) ht.1
    rw [intrinsicGeodesic_zero, sub_zero] at h
    have h2 : Real.sqrt (g.inner x v v) * t ≤ Real.sqrt (g.inner x v v) := by
      nlinarith [Real.sqrt_nonneg (g.inner x v v), ht.1, ht.2]
    linarith
  have hall := mem_maxSliceLocus_of_mem_sliceTangent hEnorm hC hCclosed hx hv
    (ball_inter_subset_maxSliceLocus (I := I) (C := C) x le_rfl) zero_le_one hstay
  rw [expMapIntrinsic_def]
  exact hall 1 ⟨zero_le_one, le_rfl⟩

theorem isInnerDirection_iff_mem_sliceTangent
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) {x : M}
    (hx : x ∈ maxSliceLocus I C) {v : TangentSpace I x} :
    IsInnerDirection (I := I) g hEnorm C x v ↔
      v ∈ sliceTangent I (maxSliceLocus I C) x :=
  ⟨mem_sliceTangent_of_isInnerDirection,
    isInnerDirection_of_mem_sliceTangent hEnorm hC hx⟩



def HasTangentConeSpan (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (C : Set M) : Prop :=
  ∀ p ∈ relBoundary I C, ∃ L : Submodule ℝ (TangentSpace I p),
    Module.finrank ℝ L = maxSliceDim I C ∧
      ∀ v : TangentSpace I p, IsInnerDirection (I := I) g hEnorm C p v → v ∈ L

theorem hasOpenTangentCone_of_hasTangentConeSpan
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    (hspan : HasTangentConeSpan (I := I) g hEnorm C) :
    HasOpenTangentCone (I := I) g hEnorm C := by
  intro p hp v w hvin hwin
  obtain ⟨L, hLdim, hLcone⟩ := hspan p hp
  set B := standardDiagonalInverseBranch (I := I) g hEnorm p with hBdef
  set Ψ := tangentSpaceModelContinuousLinearEquiv (I := I) (M := M) p with hΨdef
  have happ : ∀ u ∈ (B.fixed p).hom.source,
      (B.fixed p).hom u = expMapIntrinsic (I := I) g hEnorm p (Ψ.symm u) :=
    fun u hu => ((B.fixed p).hom_eq hu).symm
  have h0src : (0 : E) ∈ (B.fixed p).hom.source := B.zero_mem
  have hzeroexp : (B.fixed p).hom (0 : E) = p := by
    rw [happ 0 h0src, ContinuousLinearEquiv.map_zero]
    exact expMapIntrinsic_zero (I := I) g hEnorm p
  have hpT : p ∈ (B.fixed p).hom.target := by
    have hmap := (B.fixed p).hom.map_source h0src
    rwa [hzeroexp] at hmap
  have hmap1 : Tendsto (fun y : M => (p, y)) (𝓝 p) (𝓝 (p, p)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hmap2 : Tendsto (fun y : M => (y, p)) (𝓝 p) (𝓝 (p, p)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hmin := hmap1.eventually (branch_minimizing_pair (I := I) B)
  have hpair := hmap2.eventually (maxSliceLocus_pair (C := C) hEnorm hC B)
  have hgood : ∀ᶠ y in 𝓝 p,
      (∀ t ∈ Icc (0 : ℝ) 1, t • (B.fixed p).hom.symm y ∈ (B.fixed p).hom.source) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (B.fixed p).hom (t • (B.fixed p).hom.symm y) =
        minJoin (I := I) g hEnorm p y t) ∧
      (y ∈ maxSliceLocus I C →
        ∀ t ∈ Ioc (0 : ℝ) 1, minJoin (I := I) g hEnorm p y t ∈ maxSliceLocus I C) ∧
      y ∈ (B.fixed p).hom.target := by
    filter_upwards [hmin, hpair, (B.fixed p).hom.open_target.mem_nhds hpT] with y h1 h2 h3
    exact ⟨h1.2.2.1, h1.2.2.2, fun hy => h2 hy hp.1, h3⟩
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.1 hgood
  have hWT : W ⊆ (B.fixed p).hom.target := fun y hy => (hWsub hy).2.2.2
  set V : Set E := (B.fixed p).hom.symm '' (maxSliceLocus I C ∩ W) with hVdef
  have hVslice : IsEmbeddedSlice 𝓘(ℝ, E) (maxSliceDim I C) V :=
    ((isEmbeddedSlice_maxSliceLocus hEnorm hC).inter_open hWopen).image
      (B.fixed p).hom.symm (fun y hy => hWT hy.2)
  have hVinner : ∀ u ∈ V, IsInnerDirection (I := I) g hEnorm C p (Ψ.symm u) := by
    rintro _ ⟨y, ⟨hyN, hyW⟩, rfl⟩
    obtain ⟨hsrc, hchord, hjoinN, -⟩ := hWsub hyW
    rw [isInnerDirection_iff]
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hgeo : intrinsicGeodesic (I := I) g hEnorm p (Ψ.symm ((B.fixed p).hom.symm y)) t =
        expMapIntrinsic (I := I) g hEnorm p (t • Ψ.symm ((B.fixed p).hom.symm y)) :=
      (intrinsicGeodesic_smul (I := I) g hEnorm p _ t).symm
    rw [hgeo, ← ContinuousLinearEquiv.map_smul, ← happ _ (hsrc t htIcc), hchord t htIcc]
    exact hjoinN hyN t ⟨ht.1, ht.2.le⟩
  have hVenter : ∀ z : TangentSpace I p, IsInnerDirection (I := I) g hEnorm C p z →
      ∃ s : ℝ, 0 < s ∧ s • (Ψ z : E) ∈ V := by
    intro z hz
    have hW' : ∀ᶠ s in 𝓝 (0 : ℝ), intrinsicGeodesic (I := I) g hEnorm p z s ∈ W := by
      have hcont : ContinuousAt (intrinsicGeodesic (I := I) g hEnorm p z) 0 :=
        (intrinsicGeodesic_continuous (I := I) g hEnorm p z).continuousAt
      exact hcont.preimage_mem_nhds
        (by rw [intrinsicGeodesic_zero]; exact hWopen.mem_nhds hpW)
    have hsrcW : ∀ᶠ s in 𝓝 (0 : ℝ), s • (Ψ z : E) ∈ (B.fixed p).hom.source := by
      have hcont : ContinuousAt (fun s : ℝ => s • (Ψ z : E)) 0 :=
        (continuous_id.smul continuous_const).continuousAt
      exact hcont.preimage_mem_nhds
        (by simpa using (B.fixed p).hom.open_source.mem_nhds h0src)
    have hkey : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        intrinsicGeodesic (I := I) g hEnorm p z s ∈ maxSliceLocus I C ∧
        intrinsicGeodesic (I := I) g hEnorm p z s ∈ W ∧
        s • (Ψ z : E) ∈ (B.fixed p).hom.source ∧ (0 : ℝ) < s := by
      filter_upwards [isInnerDirection_iff.1 hz, hW'.filter_mono nhdsWithin_le_nhds,
        hsrcW.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    obtain ⟨s, hsN, hsW, hssrc, hspos⟩ := hkey.exists
    refine ⟨s, hspos, intrinsicGeodesic (I := I) g hEnorm p z s, ⟨hsN, hsW⟩, ?_⟩
    have hphi : (B.fixed p).hom (s • (Ψ z : E)) =
        intrinsicGeodesic (I := I) g hEnorm p z s := by
      rw [happ _ hssrc, ← ContinuousLinearEquiv.map_smul,
        ContinuousLinearEquiv.symm_apply_apply]
      exact intrinsicGeodesic_smul (I := I) g hEnorm p z s
    rw [← hphi]
    exact (B.fixed p).hom.toPartialEquiv.left_inv hssrc
  set L' : Submodule ℝ E :=
    Submodule.map (Ψ.toLinearEquiv : TangentSpace I p →ₗ[ℝ] E) L with hL'def
  have hmemL' : ∀ u : E, u ∈ L' ↔ Ψ.symm u ∈ L := by
    intro u
    rw [hL'def]
    simp [Submodule.mem_map_equiv]
  have hVL : V ⊆ (L' : Set E) := fun u hu => (hmemL' u).2 (hLcone _ (hVinner u hu))
  have hdimL' : Module.finrank ℝ L' = maxSliceDim I C := by
    rw [hL'def, LinearEquiv.finrank_map_eq]
    exact hLdim
  obtain ⟨s, hspos, hsV⟩ := hVenter v hvin
  have hnhds := hVslice.preimage_val_mem_nhds hVL hdimL' hsV
  have hvL : v ∈ L := hLcone v hvin
  have hwL : w ∈ L := hLcone w hwin
  have hlin : ∀ ε : ℝ, (Ψ (v - ε • w) : E) = (Ψ v : E) - ε • (Ψ w : E) := by
    intro ε
    rw [ContinuousLinearEquiv.map_sub, ContinuousLinearEquiv.map_smul]
  have hmem : ∀ ε : ℝ, s • ((Ψ v : E) - ε • (Ψ w : E)) ∈ L' := by
    intro ε
    refine (hmemL' _).2 ?_
    rw [← hlin ε, ← ContinuousLinearEquiv.map_smul,
      ContinuousLinearEquiv.symm_apply_apply]
    exact L.smul_mem s (L.sub_mem hvL (L.smul_mem ε hwL))
  have hcont : Continuous fun ε : ℝ =>
      (⟨s • ((Ψ v : E) - ε • (Ψ w : E)), hmem ε⟩ : L') := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.smul (continuous_const.sub (continuous_id.smul continuous_const))
  have hzero : (⟨s • ((Ψ v : E) - (0 : ℝ) • (Ψ w : E)), hmem 0⟩ : L') =
      ⟨s • (Ψ v : E), hVL hsV⟩ := by
    ext
    simp
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), s • ((Ψ v : E) - ε • (Ψ w : E)) ∈ V := by
    have h := hcont.continuousAt.preimage_mem_nhds (by rw [hzero]; exact hnhds)
    filter_upwards [h] with ε hε
    exact hε
  have hfinal : ∀ᶠ ε in 𝓝 (0 : ℝ), IsInnerDirection (I := I) g hEnorm C p (v - ε • w) := by
    filter_upwards [hev] with ε hε
    have hin := hVinner _ hε
    have hsymm : Ψ.symm (s • ((Ψ v : E) - ε • (Ψ w : E))) = s • (v - ε • w) := by
      rw [← hlin ε, ← ContinuousLinearEquiv.map_smul,
        ContinuousLinearEquiv.symm_apply_apply]
    rw [hsymm] at hin
    have hscaled := isInnerDirection_smul (t := s⁻¹) (inv_pos.2 hspos) hin
    rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hspos), one_smul] at hscaled
  exact (hfinal.filter_mono nhdsWithin_le_nhds).frequently

theorem hasTangentConeSpan_of_isPreconnected
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hconn : IsPreconnected C) :
    HasTangentConeSpan (I := I) g hEnorm C := by
  intro p hp
  set B := standardDiagonalInverseBranch (I := I) g hEnorm p with hBdef
  have hswap : Tendsto (fun qy : M × M => (qy.2, qy.1)) (𝓝 (p, p)) (𝓝 (p, p)) :=
    (continuous_snd.prodMk continuous_fst).continuousAt
  have hjoin := hswap.eventually (maxSliceLocus_minJoin (C := C) hEnorm hC B)
  have hcomb : ∀ᶠ qy : M × M in 𝓝 (p, p),
      (qy.2 ∈ (B.fixed qy.1).hom.target ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          t • (B.fixed qy.1).hom.symm qy.2 ∈ (B.fixed qy.1).hom.source) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, (B.fixed qy.1).hom (t • (B.fixed qy.1).hom.symm qy.2) =
          minJoin (I := I) g hEnorm qy.1 qy.2 t) ∧
      (qy.2 ∈ maxSliceLocus I C → qy.1 ∈ maxSliceLocus I C →
        ∀ t ∈ Icc (0 : ℝ) 1,
          minJoin (I := I) g hEnorm qy.1 qy.2 t ∈ maxSliceLocus I C) := by
    filter_upwards [branch_minimizing_pair (I := I) B, hjoin] with qy h1 h2
    exact ⟨⟨h1.1, h1.2.2.1, h1.2.2.2⟩, h2⟩
  obtain ⟨P, Q, hPopen, hpP, hQopen, hpQ, hPQ⟩ := mem_nhds_prod_iff'.1 hcomb
  have hpclos : p ∈ closure (maxSliceLocus I C) :=
    subset_closure_maxSliceLocus hEnorm hC hconn hp.1
  obtain ⟨q, hqPQ, hqN⟩ :=
    mem_closure_iff.1 hpclos (P ∩ Q) (hPopen.inter hQopen) ⟨hpP, hpQ⟩
  have hqP : q ∈ P := hqPQ.1
  obtain ⟨⟨hpT, -, -⟩, -⟩ := hPQ (Set.mk_mem_prod hqP hpQ)
  set Φ := (B.fixed q).hom with hΦdef
  set Ψ := tangentSpaceModelContinuousLinearEquiv (I := I) (M := M) q with hΨdef
  have happ : ∀ u ∈ Φ.source,
      Φ u = expMapIntrinsic (I := I) g hEnorm q (Ψ.symm u) :=
    fun u hu => ((B.fixed q).hom_eq hu).symm
  set K : Submodule ℝ E :=
    Submodule.map (Ψ.toLinearEquiv : TangentSpace I q →ₗ[ℝ] E)
      (sliceTangent I (maxSliceLocus I C) q) with hKdef
  have hmemK : ∀ u : E, u ∈ K ↔ Ψ.symm u ∈ sliceTangent I (maxSliceLocus I C) q := by
    intro u
    rw [hKdef]
    simp [Submodule.mem_map_equiv]
  have hKdim : Module.finrank ℝ K = maxSliceDim I C := by
    rw [hKdef, LinearEquiv.finrank_map_eq]
    exact finrank_sliceTangent_maxSliceLocus hEnorm hC hqN
  have hKclosed : IsClosed (K : Set E) := K.closed_of_finiteDimensional
  have hKmem : ∀ y ∈ maxSliceLocus I C ∩ Q, (Φ.symm y : E) ∈ K := by
    rintro y ⟨hyN, hyQ⟩
    obtain ⟨⟨-, hsrc, hchord⟩, hjoinN⟩ := hPQ (Set.mk_mem_prod hqP hyQ)
    refine (hmemK _).2 (mem_sliceTangent_of_isInnerDirection
      (g := g) (hEnorm := hEnorm) (C := C) ?_)
    rw [isInnerDirection_iff]
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hgeo : intrinsicGeodesic (I := I) g hEnorm q (Ψ.symm (Φ.symm y)) t =
        expMapIntrinsic (I := I) g hEnorm q (t • Ψ.symm (Φ.symm y)) :=
      (intrinsicGeodesic_smul (I := I) g hEnorm q _ t).symm
    rw [hgeo, ← ContinuousLinearEquiv.map_smul, ← happ _ (hsrc t htIcc), hchord t htIcc]
    exact hjoinN hyN hqN t htIcc
  have hUopen : IsOpen (Q ∩ Φ.target) := hQopen.inter Φ.open_target
  have hpU : p ∈ Q ∩ Φ.target := ⟨hpQ, hpT⟩
  have hpclos' : p ∈ closure (maxSliceLocus I C ∩ (Q ∩ Φ.target)) := by
    rw [mem_closure_iff]
    intro O hOopen hpO
    obtain ⟨z, hzmem, hzN⟩ :=
      mem_closure_iff.1 hpclos (O ∩ (Q ∩ Φ.target)) (hOopen.inter hUopen) ⟨hpO, hpU⟩
    exact ⟨z, hzmem.1, hzN, hzmem.2⟩
  have hpZK : (Φ.symm p : E) ∈ K := by
    have hnb : (𝓝[maxSliceLocus I C ∩ (Q ∩ Φ.target)] p).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hpclos'
    have hcontat : ContinuousAt (fun y : M => (Φ.symm y : E)) p := by
      have hcon : ContinuousOn (fun y : M => (Φ.symm y : E)) Φ.target :=
        Φ.symm.contMDiffOn_toFun.continuousOn
      exact hcon.continuousAt (Φ.open_target.mem_nhds hpT)
    have htend : Tendsto (fun y : M => (Φ.symm y : E))
        (𝓝[maxSliceLocus I C ∩ (Q ∩ Φ.target)] p) (𝓝 (Φ.symm p : E)) :=
      hcontat.mono_left nhdsWithin_le_nhds
    refine hKclosed.mem_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hKmem y ⟨hy.1, hy.2.1⟩
  have hpsrc : p ∈ Φ.symm.source := hpT
  have hloc : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ Φ.symm p :=
    Φ.symm.isLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ hpsrc
  refine ⟨Submodule.comap (mfderiv I 𝓘(ℝ, E) Φ.symm p).toLinearMap
    (show Submodule ℝ (TangentSpace 𝓘(ℝ, E) (Φ.symm p)) from K), ?_, ?_⟩
  · have hmapeq : (mfderiv I 𝓘(ℝ, E) Φ.symm p).toLinearMap =
        ((hloc.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv :
          TangentSpace I p →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) (Φ.symm p)) := rfl
    rw [hmapeq, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
    exact hKdim
  · intro v hv
    have hvT : v ∈ sliceTangent I (maxSliceLocus I C) p :=
      mem_sliceTangent_of_isInnerDirection hv
    have hSev : ∀ᶠ y in 𝓝 p, y ∈ maxSliceLocus I C → (Φ.symm y : E) ∈ K := by
      filter_upwards [hQopen.mem_nhds hpQ] with y hyQ hyN
      exact hKmem y ⟨hyN, hyQ⟩
    exact mfderiv_mem_of_eventually_mem hpsrc hKclosed hSev hpZK hvT

theorem hasOpenTangentCone_of_totallyConvex
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hconn : IsPreconnected C) :
    HasOpenTangentCone (I := I) g hEnorm C :=
  hasOpenTangentCone_of_hasTangentConeSpan hEnorm hC
    (hasTangentConeSpan_of_isPreconnected hEnorm hC hconn)

theorem hasSupportingHalfSpaces_relBoundary_of_hasAcuteTangentCone
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hconn : IsPreconnected C)
    (hacute : HasAcuteTangentCone (I := I) g hEnorm C) :
    HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C) :=
  hasSupportingHalfSpaces_relBoundary g hEnorm hsec hC hCclosed
    (hasOpenTangentCone_of_totallyConvex hEnorm hC hconn) hacute

end DifferentialGeometry.Geometry.Topology
