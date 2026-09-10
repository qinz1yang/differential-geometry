import DifferentialGeometry.Geometry.Comparison.ConvexAcuteCone
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Tangent
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData

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

theorem relBoundary_subset_closure_supportingDirections
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C) :
    relBoundary I C ⊆ closure {x | x ∈ relBoundary I C ∧
      ∃ u : TangentSpace I x, IsSupportingDirection (I := I) g hEnorm C x u} := by
  intro p hp
  have hconn : IsPreconnected C :=
    (IsTotallyConvex.isPathConnected g hEnorm hC ⟨p, hp.1⟩).isConnected.isPreconnected
  rw [Metric.mem_closure_iff]
  intro ε hε
  let : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  have hpclos := subset_closure_maxSliceLocus hEnorm hC hconn hp.1
  obtain ⟨q, hqN, hqp⟩ := Metric.mem_closure_iff.1 hpclos (ε / 3) (by positivity)
  obtain ⟨z, hz, hdz⟩ := (isClosed_relBoundary hEnorm hC hCclosed).exists_infDist_eq_dist
    ⟨p, hp⟩ q
  have hzd : dist q z = Metric.infDist q (relBoundary I C) := hdz.symm
  have hdpos : 0 < dist z q := by
    rw [dist_comm, hzd]
    exact infDist_relBoundary_pos hEnorm hC hCclosed ⟨p, hp⟩ hqN
  obtain ⟨u, hu, huq⟩ := soul_unit_minimizing_initial (I := I) g hEnorm z q hdpos
  refine ⟨z, ⟨hz, u, hu, dist z q, hdpos, ?_, ?_⟩, ?_⟩
  · rwa [huq]
  · rw [huq, dist_comm]
    exact hzd.symm
  · have hdle : dist q z ≤ dist q p := by
      rw [hzd]
      exact Metric.infDist_le_dist_of_mem hp
    have htri := dist_triangle p q z
    rw [dist_comm q p] at hdle
    have hε3 : (ε / 3) + (ε / 3) < ε := by linarith
    exact lt_of_le_of_lt htri (lt_of_le_of_lt (add_le_add le_rfl hdle)
      ((add_lt_add hqp hqp).trans hε3))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem riemannian_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]

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

private theorem exists_support_chart
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hconn : IsPreconnected C)
    {p : M} (hp : p ∈ relBoundary I C) :
    ∃ (Φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (K : Submodule ℝ E) (W : Set M),
      IsOpen W ∧ p ∈ W ∧ W ⊆ Φ.source ∧ Module.finrank ℝ K = maxSliceDim I C ∧
      (∀ x ∈ W ∩ C, Φ x ∈ K) ∧
      ∀ x ∈ W ∩ C, ∀ v : TangentSpace I x,
        IsInnerDirection (I := I) g hEnorm C x v → mfderiv I 𝓘(ℝ, E) Φ x v ∈ K := by
  let B := standardDiagonalInverseBranch (I := I) g hEnorm p
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
  have hpclos := subset_closure_maxSliceLocus hEnorm hC hconn hp.1
  obtain ⟨q, hqPQ, hqN⟩ :=
    mem_closure_iff.1 hpclos (P ∩ Q) (hPopen.inter hQopen) ⟨hpP, hpQ⟩
  let Φ := (B.fixed q).hom.symm
  let Ψ := tangentSpaceModelContinuousLinearEquiv (I := I) (M := M) q
  let K : Submodule ℝ E :=
    Submodule.map Ψ.toLinearEquiv.toLinearMap (sliceTangent I (maxSliceLocus I C) q)
  have hmemK (u : E) : u ∈ K ↔ Ψ.symm u ∈ sliceTangent I (maxSliceLocus I C) q := by
    simp [K, Submodule.mem_map_equiv]
  have hKdim : Module.finrank ℝ K = maxSliceDim I C := by
    dsimp only [K]
    rw [LinearEquiv.finrank_map_eq]
    exact finrank_sliceTangent_maxSliceLocus hEnorm hC hqN
  have hKmem : ∀ y ∈ maxSliceLocus I C ∩ Q, Φ y ∈ K := by
    rintro y ⟨hyN, hyQ⟩
    obtain ⟨⟨-, hsrc, hchord⟩, hjoinN⟩ := hPQ (Set.mk_mem_prod hqPQ.1 hyQ)
    refine (hmemK _).2 (mem_sliceTangent_of_isInnerDirection
      (g := g) (hEnorm := hEnorm) (C := C) ?_)
    rw [isInnerDirection_iff]
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have happ : (B.fixed q).hom (t • Φ y) =
        expMapIntrinsic (I := I) g hEnorm q (Ψ.symm (t • Φ y)) :=
      ((B.fixed q).hom_eq (hsrc t htIcc)).symm
    have hgeo : intrinsicGeodesic (I := I) g hEnorm q (Ψ.symm (Φ y)) t =
        expMapIntrinsic (I := I) g hEnorm q (t • Ψ.symm (Φ y)) :=
      (intrinsicGeodesic_smul (I := I) g hEnorm q _ t).symm
    rw [hgeo, ← ContinuousLinearEquiv.map_smul, ← happ, hchord t htIcc]
    exact hjoinN hyN hqN t htIcc
  let W := Q ∩ Φ.source
  have hWopen : IsOpen W := hQopen.inter Φ.open_source
  have hpW : p ∈ W := ⟨hpQ, (hPQ (Set.mk_mem_prod hqPQ.1 hpQ)).1.1⟩
  have hclosed : IsClosed (K : Set E) := K.closed_of_finiteDimensional
  have hxK : ∀ x ∈ W ∩ C, Φ x ∈ K := by
    rintro x ⟨hxW, hxC⟩
    have hxclos := subset_closure_maxSliceLocus hEnorm hC hconn hxC
    have hxclos' : x ∈ closure (maxSliceLocus I C ∩ W) := by
      rw [mem_closure_iff]
      intro O hO hxO
      obtain ⟨z, hz, hzN⟩ :=
        mem_closure_iff.1 hxclos (O ∩ W) (hO.inter hWopen) ⟨hxO, hxW⟩
      exact ⟨z, hz.1, hzN, hz.2⟩
    have : (𝓝[maxSliceLocus I C ∩ W] x).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hxclos'
    have htend := (Φ.contMDiffOn_toFun.continuousOn.continuousAt
      (Φ.open_source.mem_nhds hxW.2)).mono_left
      (show 𝓝[maxSliceLocus I C ∩ W] x ≤ 𝓝 x from nhdsWithin_le_nhds)
    refine hclosed.mem_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hKmem y ⟨hy.1, hy.2.1⟩
  refine ⟨Φ, K, W, hWopen, hpW, fun _ hy => hy.2, hKdim, hxK, ?_⟩
  intro x hx v hv
  refine mfderiv_mem_of_eventually_mem hx.1.2 hclosed ?_ (hxK x hx)
    (mem_sliceTangent_of_isInnerDirection hv)
  filter_upwards [hWopen.mem_nhds hx.1] with y hy hyN
  exact hKmem y ⟨hyN, hy.1⟩

private theorem exists_inner_slice
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hconn : IsPreconnected C)
    {p : M} (hp : p ∈ C) :
    ∃ V : Set E, V.Nonempty ∧ IsEmbeddedSlice 𝓘(ℝ, E) (maxSliceDim I C) V ∧
      ∀ z ∈ V, IsInnerDirection (I := I) g hEnorm C p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm z) := by
  let B := standardDiagonalInverseBranch (I := I) g hEnorm p
  let Ψ := tangentSpaceModelContinuousLinearEquiv (I := I) (M := M) p
  have hmap1 : Tendsto (fun y : M => (p, y)) (𝓝 p) (𝓝 (p, p)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hmap2 : Tendsto (fun y : M => (y, p)) (𝓝 p) (𝓝 (p, p)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hgood : ∀ᶠ y in 𝓝 p,
      y ∈ (B.fixed p).hom.target ∧
      (∀ t ∈ Icc (0 : ℝ) 1, t • (B.fixed p).hom.symm y ∈ (B.fixed p).hom.source) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (B.fixed p).hom (t • (B.fixed p).hom.symm y) =
        minJoin (I := I) g hEnorm p y t) ∧
      (y ∈ maxSliceLocus I C →
        ∀ t ∈ Ioc (0 : ℝ) 1, minJoin (I := I) g hEnorm p y t ∈ maxSliceLocus I C) := by
    filter_upwards [hmap1.eventually (branch_minimizing_pair B),
      hmap2.eventually (maxSliceLocus_pair (C := C) hEnorm hC B)] with y h1 h2
    exact ⟨h1.1, h1.2.2.1, h1.2.2.2, fun hy => h2 hy hp⟩
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.1 hgood
  let V := (B.fixed p).hom.symm '' (maxSliceLocus I C ∩ W)
  obtain ⟨q, hqW, hqN⟩ :=
    mem_closure_iff.1 (subset_closure_maxSliceLocus hEnorm hC hconn hp) W hWopen hpW
  refine ⟨V, ⟨_, ⟨q, ⟨hqN, hqW⟩, rfl⟩⟩,
    ((isEmbeddedSlice_maxSliceLocus hEnorm hC).inter_open hWopen).image
      (B.fixed p).hom.symm (fun y hy => (hWsub hy.2).1), ?_⟩
  rintro z ⟨y, ⟨hyN, hyW⟩, rfl⟩
  obtain ⟨-, hsrc, hchord, hjoin⟩ := hWsub hyW
  rw [isInnerDirection_iff]
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have happ : (B.fixed p).hom (t • (B.fixed p).hom.symm y) =
      expMapIntrinsic (I := I) g hEnorm p
        (Ψ.symm (t • (B.fixed p).hom.symm y)) :=
    ((B.fixed p).hom_eq (hsrc t htIcc)).symm
  have hgeo : intrinsicGeodesic (I := I) g hEnorm p
      (Ψ.symm ((B.fixed p).hom.symm y)) t =
      expMapIntrinsic (I := I) g hEnorm p (t • Ψ.symm ((B.fixed p).hom.symm y)) :=
    (intrinsicGeodesic_smul (I := I) g hEnorm p _ t).symm
  rw [hgeo, ← ContinuousLinearEquiv.map_smul, ← happ, hchord t htIcc]
  exact hjoin hyN t ⟨ht.1, ht.2.le⟩

private theorem exists_inner_covector_pos
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hconn : IsPreconnected C)
    {p : M} (hp : p ∈ C) (D : TangentSpace I p ≃L[ℝ] E)
    (K : Submodule ℝ E) (hKdim : Module.finrank ℝ K = maxSliceDim I C)
    (hKcone : ∀ v, IsInnerDirection (I := I) g hEnorm C p v → D v ∈ K)
    (F : K →L[ℝ] ℝ) (hFne : F ≠ 0)
    (hFnonneg : ∀ v (hv : IsInnerDirection (I := I) g hEnorm C p v),
      0 ≤ F ⟨D v, hKcone v hv⟩) :
    ∃ v, ∃ hv : IsInnerDirection (I := I) g hEnorm C p v,
      0 < F ⟨D v, hKcone v hv⟩ := by
  obtain ⟨V, hVne, hVslice, hVcone⟩ := exists_inner_slice hEnorm hC hconn hp
  let Ψ := tangentSpaceModelContinuousLinearEquiv (I := I) (M := M) p
  let e : E ≃L[ℝ] E := Ψ.symm.trans D
  let Z : Set E := e '' V
  have hZslice : IsEmbeddedSlice 𝓘(ℝ, E) (maxSliceDim I C) Z :=
    hVslice.image e.toDiffeomorph.toPartialDiffeomorph (fun _ _ => mem_univ _)
  have hZK : Z ⊆ (K : Set E) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hKcone _ (hVcone z hz)
  obtain ⟨z, hzV⟩ := hVne
  have hzZ : e z ∈ Z := ⟨z, hzV, rfl⟩
  have hnhds := hZslice.preimage_val_mem_nhds hZK hKdim hzZ
  by_contra h
  have hzero : ∀ v (hv : IsInnerDirection (I := I) g hEnorm C p v),
      F ⟨D v, hKcone v hv⟩ = 0 := by
    intro v hv
    apply le_antisymm _ (hFnonneg v hv)
    exact le_of_not_gt (fun hvpos => h ⟨v, hv, hvpos⟩)
  have hker : (F.ker : Set K) ∈ 𝓝 (⟨e z, hZK hzZ⟩ : K) := by
    refine Filter.mem_of_superset hnhds ?_
    rintro ⟨x, hxK⟩ ⟨v, hv, rfl⟩
    exact hzero _ (hVcone v hv)
  have htop : F.ker = ⊤ := F.ker.eq_top_of_nonempty_interior'
    ⟨_, mem_interior_iff_mem_nhds.2 hker⟩
  apply hFne
  ext x
  exact (show x ∈ F.ker from htop.symm ▸ Submodule.mem_top)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem continuousAt_coord_deriv
    (Φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    {A : Type*} [TopologicalSpace A] {b : A → M}
    {v : (a : A) → TangentSpace I (b a)} {a : A}
    (hv : ContinuousAt (fun a => (⟨b a, v a⟩ : TangentBundle I M)) a)
    (ha : b a ∈ Φ.source) :
    ContinuousAt (fun a => (mfderiv I 𝓘(ℝ, E) Φ (b a) (v a) : E)) a := by
  let T := DifferentialGeometry.PartialDiffeomorph.tangentHome Φ (by simp)
  have hT : ContinuousAt T (⟨b a, v a⟩ : TangentBundle I M) :=
    T.continuousOn.continuousAt (T.open_source.mem_nhds ha)
  have hcoord : Continuous (fun z : TangentBundle 𝓘(ℝ, E) E => (z.snd : E)) :=
    continuous_snd.comp (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).continuous
  let q : A → TangentBundle I M := fun x => ⟨b x, v x⟩
  have hq : ContinuousAt q a := hv
  have hTq : ContinuousAt (T ∘ q) a := hT.comp (f := q) hq
  have hval : ContinuousAt (fun x : A => ((T (q x)).snd : E)) a :=
    hcoord.continuousAt.comp hTq
  refine hval.congr_of_eventuallyEq ?_
  have hb : ContinuousAt b a :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp (f := q) hq
  filter_upwards [hb.preimage_mem_nhds (Φ.open_source.mem_nhds ha)] with x hx
  change mfderiv I 𝓘(ℝ, E) Φ (b x) (v x) =
    mfderivWithin I 𝓘(ℝ, E) Φ Φ.source (b x) (v x)
  rw [mfderivWithin_of_isOpen Φ.open_source hx]

private theorem exists_inner_approximation
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {p : M} {v : TangentSpace I p}
    (hv : IsInnerDirection (I := I) g hEnorm C p v) :
    ∃ (t : ℝ) (V : (x : M) → TangentSpace I x), 0 < t ∧ V p = t • v ∧
      ContinuousAt (fun x => (⟨x, V x⟩ : TangentBundle I M)) p ∧
      ∀ᶠ x in 𝓝 p, x ∈ C → IsInnerDirection (I := I) g hEnorm C x (V x) := by
  let B := standardDiagonalInverseBranch (I := I) g hEnorm p
  have hswap : Tendsto (fun xy : M × M => (xy.2, xy.1)) (𝓝 (p, p)) (𝓝 (p, p)) :=
    (continuous_snd.prodMk continuous_fst).continuousAt
  have hgood : ∀ᶠ xy : M × M in 𝓝 (p, p),
      xy.2 ∈ (B.fixed xy.1).hom.target ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        s • (B.fixed xy.1).hom.symm xy.2 ∈ (B.fixed xy.1).hom.source) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, (B.fixed xy.1).hom (s • (B.fixed xy.1).hom.symm xy.2) =
        minJoin (I := I) g hEnorm xy.1 xy.2 s) ∧
      (xy.2 ∈ maxSliceLocus I C → xy.1 ∈ C →
        ∀ s ∈ Ioc (0 : ℝ) 1, minJoin (I := I) g hEnorm xy.1 xy.2 s ∈ maxSliceLocus I C) := by
    filter_upwards [branch_minimizing_pair B,
      hswap.eventually (maxSliceLocus_pair (C := C) hEnorm hC B)] with xy h1 h2
    exact ⟨h1.1, h1.2.2.1, h1.2.2.2, h2⟩
  obtain ⟨P, Q, hPopen, hpP, hQopen, hpQ, hPQ⟩ := mem_nhds_prod_iff'.1 hgood
  have hgeoQ : ∀ᶠ t in 𝓝 (0 : ℝ), intrinsicGeodesic (I := I) g hEnorm p v t ∈ Q := by
    apply (intrinsicGeodesic_continuous (I := I) g hEnorm p v).continuousAt.preimage_mem_nhds
    rw [intrinsicGeodesic_zero]
    exact hQopen.mem_nhds hpQ
  obtain ⟨A, hA, r, hr, htube⟩ := branch_source_tube B
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), t * Real.sqrt (g.inner p v v) < r :=
    (isOpen_lt (continuous_id.mul continuous_const) continuous_const).mem_nhds
      (by simpa using hr)
  have hsrc : ∀ᶠ t in 𝓝[>] (0 : ℝ), (⟨p, t • v⟩ : TangentBundle I M) ∈ B.hom.source := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htpos
    apply htube p (mem_of_mem_nhds hA)
    rw [sqrt_gInner_smul_self (I := I) g p htpos.le]
    exact ht
  obtain ⟨t, ⟨⟨htN, htQ⟩, htS⟩, htpos⟩ :=
    ((isInnerDirection_iff.1 hv).and (hgeoQ.filter_mono nhdsWithin_le_nhds) |>.and
      hsrc |>.and self_mem_nhdsWithin).exists
  let y := intrinsicGeodesic (I := I) g hEnorm p v t
  let V : (x : M) → TangentSpace I x := fun x => (B.inv (x, y)).snd
  have hdom : ∀ x ∈ P, (x, y) ∈ B.dom := by
    intro x hx
    exact (DiagonalInverseBranch.fixed_target B y).1 (hPQ (Set.mk_mem_prod hx htQ)).1
  have hVp : V p = t • v := by
    have hinv := B.inv_eq_of_exp (show (⟨p, t • v⟩ : TangentBundle I M) ∈ B.hom.source from htS)
      (intrinsicGeodesic_smul (I := I) g hEnorm p v t)
    exact congrArg (fun z : TangentBundle I M => (z.snd : E)) hinv
  refine ⟨t, V, htpos, hVp, (B.inv_vector_contMDiffOn_at_fixed_target hdom).continuousOn.continuousAt
    (hPopen.mem_nhds hpP), ?_⟩
  filter_upwards [hPopen.mem_nhds hpP] with x hx hxC
  obtain ⟨-, hsrc', hchord, hjoin⟩ := hPQ (Set.mk_mem_prod hx htQ)
  rw [isInnerDirection_iff]
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
  have hsIcc : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have happ : (B.fixed x).hom (s • (B.fixed x).hom.symm y) =
      expMapIntrinsic (I := I) g hEnorm x (s • V x) :=
    ((B.fixed x).hom_eq (hsrc' s hsIcc)).symm
  have hgeo : intrinsicGeodesic (I := I) g hEnorm x (V x) s =
      expMapIntrinsic (I := I) g hEnorm x (s • V x) :=
    (intrinsicGeodesic_smul (I := I) g hEnorm x (V x) s).symm
  rw [hgeo, ← happ, hchord s hsIcc]
  exact hjoin htN hxC s ⟨hs.1, hs.2.le⟩

private theorem exists_strict_support_covector
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hconn : IsPreconnected C) {p : M} (hp : p ∈ relBoundary I C) :
    ∃ F : TangentSpace I p →L[ℝ] ℝ, F ≠ 0 ∧
      ∀ v, IsInnerDirection (I := I) g hEnorm C p v → 0 < F v := by
  obtain ⟨Φ, K, W, hWopen, hpW, hWsrc, hKdim, -, hKcone⟩ :=
    exists_support_chart hEnorm hC hconn hp
  let D (x : M) (hx : x ∈ W) : TangentSpace I x ≃L[ℝ] E :=
    (Φ.isLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ (hWsrc hx)).mfderivToContinuousLinearEquiv
      (by simp)
  have hpC : p ∈ C := hp.1
  have hDp (v : TangentSpace I p) (hv : IsInnerDirection (I := I) g hEnorm C p v) :
      D p hpW v ∈ K := hKcone p ⟨hpW, hpC⟩ v hv
  obtain ⟨K', hcompl⟩ := K.exists_isCompl
  let Pj : E →L[ℝ] K := ⟨K.projectionOnto K' hcompl,
    (K.projectionOnto K' hcompl).continuous_of_finiteDimensional⟩
  have hπ (z : E) (hz : z ∈ K) : Pj z = ⟨z, hz⟩ :=
    Submodule.projectionOnto_apply_of_mem_left hcompl hz
  have hopen := hasOpenTangentCone_of_totallyConvex hEnorm hC hconn
  have hacute := hasAcuteTangentCone_of_totallyConvex g hEnorm hsec hC hCclosed
  let A := {x | x ∈ relBoundary I C ∧
    ∃ u : TangentSpace I x, IsSupportingDirection (I := I) g hEnorm C x u}
  have hpA : p ∈ closure (W ∩ A) := by
    have hcl := relBoundary_subset_closure_supportingDirections hEnorm hC hCclosed hp
    rw [mem_closure_iff]
    intro O hO hpO
    obtain ⟨x, hx, hxA⟩ := mem_closure_iff.1 hcl (O ∩ W) (hO.inter hWopen) ⟨hpO, hpW⟩
    exact ⟨x, hx.1, hx.2, hxA⟩
  obtain ⟨x, hx, hxlim⟩ := mem_closure_iff_seq_limit.1 hpA
  have hxW (n : ℕ) : x n ∈ W := (hx n).1
  have hxB (n : ℕ) : x n ∈ relBoundary I C := (hx n).2.1
  have hxC (n : ℕ) : x n ∈ C := (hxB n).1
  choose u hu using fun n => (hx n).2.2
  have hxin (n : ℕ) : IsInnerDirection (I := I) g hEnorm C (x n) (u n) :=
    isInnerDirection_of_isSupportingDirection hC (hx n).2.1.1 (hu n)
  have hDu (n : ℕ) : D (x n) (hxW n) (u n) ∈ K :=
    hKcone (x n) ⟨(hx n).1, (hx n).2.1.1⟩ (u n) (hxin n)
  let G (n : ℕ) : K →L[ℝ] ℝ :=
    ((g.inner (x n) (u n)).comp (D (x n) (hxW n)).symm.toContinuousLinearMap).comp K.subtypeL
  have hGone (n : ℕ) : G n ⟨D (x n) (hxW n) (u n), hDu n⟩ = 1 := by
    change g.inner (x n) (u n) ((D (x n) (hxW n)).symm (D (x n) (hxW n) (u n))) = 1
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (hu n).1
  have hGne (n : ℕ) : G n ≠ 0 := by
    intro h
    have heq := hGone n
    rw [h] at heq
    norm_num at heq
  let Fseq (n : ℕ) : K →L[ℝ] ℝ := ‖G n‖⁻¹ • G n
  have hFseq (n : ℕ) : Fseq n ∈ Metric.sphere (0 : K →L[ℝ] ℝ) 1 := by
    rw [Metric.mem_sphere]
    calc
      dist (Fseq n) 0 = ‖Fseq n‖ := dist_zero_right (Fseq n)
      _ = 1 := norm_smul_inv_norm (𝕜 := ℝ) (E := K →L[ℝ] ℝ) (x := G n) (hGne n)
  let : FiniteDimensional ℝ (K →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  let : ProperSpace (K →L[ℝ] ℝ) := FiniteDimensional.proper ℝ (K →L[ℝ] ℝ)
  obtain ⟨F, hF, σ, hσ, hFlim⟩ := (isCompact_sphere (0 : K →L[ℝ] ℝ) 1).tendsto_subseq hFseq
  have hFne : F ≠ 0 := by
    intro h
    simp [h] at hF
  have hFnonneg : ∀ v (hv : IsInnerDirection (I := I) g hEnorm C p v),
      0 ≤ F ⟨D p hpW v, hDp v hv⟩ := by
    intro v hv
    obtain ⟨t, V, ht, hVp, hVcont, hVinner⟩ := exists_inner_approximation hEnorm hC hv
    let z (n : ℕ) : K := Pj (D (x (σ n)) (hxW (σ n)) (V (x (σ n))))
    have hzlim : Tendsto z atTop (𝓝 (Pj (D p hpW (t • v)))) := by
      have hh := (continuousAt_coord_deriv Φ hVcont (hWsrc hpW)).tendsto
      have hval : mfderiv I 𝓘(ℝ, E) Φ p (V p) = D p hpW (t • v) := by
        rw [hVp]
        rfl
      rw [hval] at hh
      exact Pj.continuous.continuousAt.tendsto.comp (hh.comp (hxlim.comp hσ.tendsto_atTop))
    have hnonneg : ∀ᶠ n in atTop, 0 ≤ (Fseq (σ n)) (z n) := by
      filter_upwards [(hxlim.comp hσ.tendsto_atTop).eventually hVinner] with n hn
      have hinner : IsInnerDirection (I := I) g hEnorm C (x (σ n)) (V (x (σ n))) :=
        hn (hxC (σ n))
      have hmem : D (x (σ n)) (hxW (σ n)) (V (x (σ n))) ∈ K :=
        hKcone (x (σ n)) ⟨hxW (σ n), hxC (σ n)⟩ _ hinner
      dsimp only [z]
      rw [hπ _ hmem]
      have hpos : 0 < g.inner (x (σ n)) (u (σ n)) (V (x (σ n))) := by
        rw [g.symm]
        exact lt_of_not_ge (fun hle =>
          not_isInnerDirection_of_inner_nonpos g hEnorm hsec hC hopen hacute
            (hx (σ n)).2.1 (hu (σ n)) hle hinner)
      have heval : (Fseq (σ n))
          ⟨D (x (σ n)) (hxW (σ n)) (V (x (σ n))), hmem⟩ =
          ‖G (σ n)‖⁻¹ * g.inner (x (σ n)) (u (σ n)) (V (x (σ n))) := by
        change ‖G (σ n)‖⁻¹ *
          g.inner (x (σ n)) (u (σ n))
            ((D (x (σ n)) (hxW (σ n))).symm
              (D (x (σ n)) (hxW (σ n)) (V (x (σ n))))) = _
        rw [ContinuousLinearEquiv.symm_apply_apply]
      rw [heval]
      exact mul_nonneg (inv_nonneg.2 (G (σ n)).opNorm_nonneg) hpos.le
    have hevalcont : Continuous (fun z : (K →L[ℝ] ℝ) × K => z.1 z.2) :=
      continuous_fst.clm_apply continuous_snd
    have hle : 0 ≤ F (Pj (D p hpW (t • v))) :=
      ge_of_tendsto (hevalcont.continuousAt.tendsto.comp
        (hFlim.prodMk_nhds hzlim)) hnonneg
    rw [map_smul, map_smul, map_smul, smul_eq_mul] at hle
    rw [hπ _ (hDp v hv)] at hle
    exact nonneg_of_mul_nonneg_right hle ht
  let Fp : TangentSpace I p →L[ℝ] ℝ := F.comp (Pj.comp (D p hpW).toContinuousLinearMap)
  have hFp (v : TangentSpace I p) (hv : IsInnerDirection (I := I) g hEnorm C p v) :
      Fp v = F ⟨D p hpW v, hDp v hv⟩ := by
    change F (Pj (D p hpW v)) = _
    rw [hπ _ (hDp v hv)]
  have hFpnonneg (v : TangentSpace I p) (hv : IsInnerDirection (I := I) g hEnorm C p v) :
      0 ≤ Fp v := by rw [hFp v hv]; exact hFnonneg v hv
  obtain ⟨w, hw, hwpos⟩ := exists_inner_covector_pos hEnorm hC hconn hpC (D p hpW) K hKdim
    hDp F hFne hFnonneg
  rw [← hFp w hw] at hwpos
  refine ⟨Fp, ?_, ?_⟩
  · intro h
    simp [h] at hwpos
  · intro v hv
    by_contra hvpos
    have hvzero : Fp v = 0 := le_antisymm (le_of_not_gt hvpos) (hFpnonneg v hv)
    obtain ⟨ε, hεin, hεpos⟩ :=
      ((hopen p hp v w hv hw).and_eventually self_mem_nhdsWithin).exists
    have hbad := hFpnonneg (v - ε • w) hεin
    rw [map_sub, map_smul, smul_eq_mul, hvzero, zero_sub] at hbad
    exact (not_le_of_gt (mul_pos hεpos hwpos)) (neg_nonneg.1 hbad)

theorem exists_unit_strict_support_relBoundary
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {p : M} (hp : p ∈ relBoundary I C) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      ∀ v, IsInnerDirection (I := I) g hEnorm C p v → 0 < g.inner p v u := by
  have hconn : IsPreconnected C :=
    (IsTotallyConvex.isPathConnected g hEnorm hC ⟨p, hp.1⟩).isConnected.isPreconnected
  obtain ⟨F, hFne, hFpos⟩ := exists_strict_support_covector hEnorm hsec hC hCclosed hconn hp
  let e := Tensor0SBundle.tangentFlatEquiv (I := I) g p
  let u := e.symm F.toLinearMap
  have heval (v : TangentSpace I p) : g.inner p u v = F v :=
    congrArg (fun f : Module.Dual ℝ (TangentSpace I p) => f v) (e.apply_symm_apply F.toLinearMap)
  have hune : u ≠ 0 := by
    intro h
    apply hFne
    ext v
    rw [← heval, h, map_zero]
  let r := Real.sqrt (g.inner p u u)
  have hr : 0 < r := Real.sqrt_pos.2 (g.pos p u hune)
  refine ⟨r⁻¹ • u, ?_, ?_⟩
  · rw [gInner_smul_self (I := I) g p r⁻¹ u,
      ← Real.sq_sqrt (gInner_self_nonneg (I := I) g p u), inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')]
  · intro v hv
    rw [(g.inner p v).map_smul, smul_eq_mul, g.symm, heval]
    exact mul_pos (inv_pos.2 hr) (hFpos v hv)

end DifferentialGeometry.Geometry.Topology
