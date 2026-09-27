import DifferentialGeometry.Geometry.Comparison.ConvexTangentSpace
import DifferentialGeometry.Geometry.Exponential.Intrinsic.GaussLemma
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation.Basic

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Comparison.Toponogov

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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem tangentBundle_mk_congr {x x' : M} (h : x = x')
    {v : TangentSpace I x} {v' : TangentSpace I x'} (hv : (v : E) = (v' : E)) :
    (⟨x, v⟩ : TangentBundle I M) = ⟨x', v'⟩ := by
  cases h
  exact congrArg (fun u : TangentSpace I x => (⟨x, u⟩ : TangentBundle I M)) hv

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem gInner_congr_base (g : SmoothRiemannianMetric I M) {x x' : M}
    (h : x = x') {a b : TangentSpace I x} {a' b' : TangentSpace I x'}
    (ha : (a : E) = (a' : E)) (hb : (b : E) = (b' : E)) :
    g.inner x a b = g.inner x' a' b' := by
  cases h
  rw [show a = a' from ha, show b = b' from hb]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem mfderiv_apply_mfderiv_symm
    {c : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞} {x : M} (hxc : x ∈ c.target)
    {X : E} (hX : c.symm x = X) (v : TangentSpace I x) :
    mfderiv 𝓘(ℝ, E) I (fun u : E => c u) X (mfderiv I 𝓘(ℝ, E) c.symm x v) = v := by
  subst hX
  have hcx : c.symm x ∈ c.source := c.toPartialEquiv.map_target hxc
  have hsymmdiff : MDifferentiableAt I 𝓘(ℝ, E) c.symm x :=
    c.symm.mdifferentiableAt (by simp) hxc
  have hcdiff : MDifferentiableAt 𝓘(ℝ, E) I c (c.symm x) :=
    c.mdifferentiableAt (by simp) hcx
  have hcomp : mfderiv I I (fun y : M => c (c.symm y)) x =
      (mfderiv 𝓘(ℝ, E) I c (c.symm x)).comp (mfderiv I 𝓘(ℝ, E) c.symm x) :=
    mfderiv_comp x hcdiff hsymmdiff
  have heq : (fun y : M => c (c.symm y)) =ᶠ[𝓝 x] id := by
    filter_upwards [c.open_target.mem_nhds hxc] with y hy
    exact c.toPartialEquiv.right_inv hy
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hcomp.symm

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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem mfderiv_shift {f : ℝ → M} {s : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I f s) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun σ : ℝ => f (s + σ)) 0 1 : E)
      = (mfderiv 𝓘(ℝ, ℝ) I f s 1 : E) := by
  have hline : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun σ : ℝ => s + σ) 0
      (ContinuousLinearMap.id ℝ ℝ) :=
    ((hasFDerivAt_id (0 : ℝ)).const_add s).hasMFDerivAt
  have hf0 : MDifferentiableAt 𝓘(ℝ, ℝ) I f ((fun σ : ℝ => s + σ) 0) := by
    simpa only [add_zero] using hf
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun σ : ℝ => f (s + σ)) 0
      ((mfderiv 𝓘(ℝ, ℝ) I f ((fun σ : ℝ => s + σ) 0)).comp
        (ContinuousLinearMap.id ℝ ℝ)) :=
    HasMFDerivAt.comp (0 : ℝ) hf0.hasMFDerivAt hline
  rw [hcomp.mfderiv]
  exact congrArg (fun t : ℝ => (mfderiv 𝓘(ℝ, ℝ) I f t 1 : E)) (add_zero s)

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem reversed_radial (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (p : M) (w : TangentSpace I p) (r : ℝ)
    {y : M} (hy : intrinsicGeodesic (I := I) g hEnorm p w r = y)
    {X : TangentSpace I y}
    (hX : (X : E) =
      (((-r) • (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p w) r
        1) : TangentSpace I y) : E)) :
    (∀ σ : ℝ, intrinsicGeodesic (I := I) g hEnorm y X σ
        = intrinsicGeodesic (I := I) g hEnorm p w (r - r * σ)) ∧
      expMapIntrinsic (I := I) g hEnorm y X = p ∧
      ((mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm y X) 1 1 : E)
        = (((-r) • w : TangentSpace I p) : E)) := by
  subst hy
  rw [show X = (-r) • (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p w) r 1)
    from hX]
  set U := mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p w) r 1 with hUdef
  have hrad : ∀ σ : ℝ,
      intrinsicGeodesic (I := I) g hEnorm
        (intrinsicGeodesic (I := I) g hEnorm p w r) ((-r) • U) σ
        = intrinsicGeodesic (I := I) g hEnorm p w (r - r * σ) := by
    intro σ
    have h1 : intrinsicGeodesic (I := I) g hEnorm
        (intrinsicGeodesic (I := I) g hEnorm p w r) ((-r) • U) σ
        = intrinsicGeodesic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm p w r) U (-r * σ) :=
      intrinsicGeo_smul_apply (I := I) g hEnorm _ U (-r) σ
    have h2 : intrinsicGeodesic (I := I) g hEnorm
        (intrinsicGeodesic (I := I) g hEnorm p w r) U (-r * σ)
        = intrinsicGeodesic (I := I) g hEnorm p w (-r * σ + r) :=
      (congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm p w r) (-r * σ)).symm
    rw [h1, h2]
    congr 1
    ring
  refine ⟨hrad, ?_, ?_⟩
  · rw [expMapIntrinsic_def, hrad 1, mul_one, sub_self, intrinsicGeodesic_zero]
  · set y : M := intrinsicGeodesic (I := I) g hEnorm
      (intrinsicGeodesic (I := I) g hEnorm p w r) ((-r) • U) 1 with hydef
    set V : TangentSpace I y :=
      mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm
        (intrinsicGeodesic (I := I) g hEnorm p w r) ((-r) • U)) 1 1 with hVdef
    have hcont2 : (fun σ : ℝ => intrinsicGeodesic (I := I) g hEnorm
        (intrinsicGeodesic (I := I) g hEnorm p w r) ((-r) • U) (σ + 1))
        = intrinsicGeodesic (I := I) g hEnorm y V :=
      intrinsicGeodesic_continuation (I := I) g hEnorm _ ((-r) • U) 1
    have hfun : intrinsicGeodesic (I := I) g hEnorm y V
        = intrinsicGeodesic (I := I) g hEnorm p ((-r) • w) := by
      rw [← hcont2]
      funext σ
      rw [hrad (σ + 1)]
      have h3 : intrinsicGeodesic (I := I) g hEnorm p ((-r) • w) σ
          = intrinsicGeodesic (I := I) g hEnorm p w (-r * σ) :=
        intrinsicGeo_smul_apply (I := I) g hEnorm p w (-r) σ
      rw [h3]
      congr 1
      ring
    have h1 : (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm y V) 0 1 : E)
        = (V : E) := intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm y V
    have h2 : (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p ((-r) • w)) 0 1 : E)
        = (((-r) • w : TangentSpace I p) : E) :=
      intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p ((-r) • w)
    rw [← h1, ← h2, hfun]

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem supporting_segment
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) {p : M}
    (hp : p ∈ relBoundary I C) {w : TangentSpace I p} (hwu : g.inner p w w = 1)
    {l : ℝ} (hl : 0 < l)
    (hqN : intrinsicGeodesic (I := I) g hEnorm p w l ∈ maxSliceLocus I C)
    (hqd : Metric.infDist (intrinsicGeodesic (I := I) g hEnorm p w l)
      (relBoundary I C) = l)
    {r : ℝ} (hr0 : 0 < r) (hrl : r ≤ l) :
    intrinsicGeodesic (I := I) g hEnorm p w r ∈ maxSliceLocus I C ∧
      dist p (intrinsicGeodesic (I := I) g hEnorm p w r) = r ∧
      Metric.infDist (intrinsicGeodesic (I := I) g hEnorm p w r)
        (relBoundary I C) = r := by
  set γ := intrinsicGeodesic (I := I) g hEnorm p w with hγdef
  have hpq : dist p (γ l) = l := dist_eq_of_isSupportingDirection hp hwu hl hqd
  have hseg : MapsTo γ (Icc (0 : ℝ) l) C :=
    hC hl.le ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm p w).isGeodesicOn _)
      (intrinsicGeodesic_continuous (I := I) g hEnorm p w).continuousOn
      (by rw [hγdef, intrinsicGeodesic_zero]; exact hp.1) (maxSliceLocus_subset hqN)
  have hspeed₁ : dist (γ 0) (γ r) ≤ r := by
    have h := dist_intrinsicGeodesic_le g hEnorm p w (s := (0 : ℝ)) (t := r) hr0.le
    rw [hwu, Real.sqrt_one, one_mul, sub_zero] at h
    exact h
  have hspeed₂ : dist (γ r) (γ l) ≤ l - r := by
    have h := dist_intrinsicGeodesic_le g hEnorm p w (s := r) (t := l) hrl
    rw [hwu, Real.sqrt_one, one_mul] at h
    exact h
  rw [hγdef, intrinsicGeodesic_zero] at hspeed₁
  have hdpr : dist p (γ r) = r := by
    have htri : dist p (γ l) ≤ dist p (γ r) + dist (γ r) (γ l) := dist_triangle _ _ _
    rw [hpq] at htri
    linarith
  have hNr : γ r ∈ maxSliceLocus I C := by
    by_contra hnot
    have hb : γ r ∈ relBoundary I C := ⟨hseg ⟨hr0.le, hrl⟩, hnot⟩
    have hle : Metric.infDist (γ l) (relBoundary I C) ≤ dist (γ l) (γ r) :=
      Metric.infDist_le_dist_of_mem hb
    rw [hqd, dist_comm] at hle
    linarith
  refine ⟨hNr, hdpr, le_antisymm ?_ ?_⟩
  · have hle : Metric.infDist (γ r) (relBoundary I C) ≤ dist (γ r) p :=
      Metric.infDist_le_dist_of_mem hp
    rw [dist_comm] at hle
    linarith
  · have hlip : Metric.infDist (γ l) (relBoundary I C)
        ≤ Metric.infDist (γ r) (relBoundary I C) + dist (γ l) (γ r) :=
      Metric.infDist_le_infDist_add_dist
    rw [hqd, dist_comm] at hlip
    linarith



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [T2Space (TangentBundle I M)] in
private theorem continuousAt_scaled_bundle {P : Type*} [TopologicalSpace P] {b : P → M}
    {v : (x : P) → TangentSpace I (b x)} {f : P → ℝ} {x : P}
    (hv : ContinuousAt (fun x => (⟨b x, v x⟩ : TangentBundle I M)) x)
    (hf : ContinuousAt f x) :
    ContinuousAt (fun x => (⟨b x, f x • v x⟩ : TangentBundle I M)) x := by
  have hvc := (FiberBundle.continuousAt_totalSpace E _).mp hv
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hvc.1, ?_⟩
  let e := trivializationAt E (TangentSpace I) (b x)
  have he : ∀ᶠ y in 𝓝 x, b y ∈ e.baseSet :=
    hvc.1.preimage_mem_nhds (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ _))
  apply (hf.smul hvc.2).congr_of_eventuallyEq
  filter_upwards [he] with y hy
  exact (e.linear ℝ hy).map_smul (f y) (v y)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [T2Space (TangentBundle I M)] in
private theorem continuousAt_gInner (g : SmoothRiemannianMetric I M)
    {P : Type*} [TopologicalSpace P] {b : P → M}
    {v w : (x : P) → TangentSpace I (b x)} {x : P}
    (hv : ContinuousAt (fun x => (⟨b x, v x⟩ : TangentBundle I M)) x)
    (hw : ContinuousAt (fun x => (⟨b x, w x⟩ : TangentBundle I M)) x) :
    ContinuousAt (fun x => g.inner (b x) (v x) (w x)) x := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact hv.inner_bundle hw

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem gInner_expand (g : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) (s : ℝ) :
    g.inner x (a + s • b) (a + s • b)
      = g.inner x a a + 2 * s * g.inner x a b + s ^ 2 * g.inner x b b := by
  have hsm2 : ∀ c : TangentSpace I x, g.inner x c (s • b) = s * g.inner x c b := by
    intro c
    rw [(g.inner x c).map_smul s b, smul_eq_mul]
  have hadd2 : ∀ c : TangentSpace I x,
      g.inner x c (a + s • b) = g.inner x c a + g.inner x c (s • b) := by
    intro c
    rw [(g.inner x c).map_add a (s • b)]
  rw [(g.inner x).map_add a (s • b)]
  simp only [add_apply, (g.inner x).map_smul s b, smul_apply, smul_eq_mul]
  rw [hadd2 a, hadd2 b, hsm2 a, hsm2 b, g.symm x b a]
  ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem gInner_smul_left (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ)
    (a b : TangentSpace I x) : g.inner x (c • a) b = c * g.inner x a b := by
  rw [(g.inner x).map_smul c a, smul_apply, smul_eq_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem gInner_smul_right (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ)
    (a b : TangentSpace I x) : g.inner x a (c • b) = c * g.inner x a b := by
  rw [(g.inner x a).map_smul c b, smul_eq_mul]



private theorem angle_lower_bound {rho sp th r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hrho1 : 0 < rho) (hrho2 : rho < r) (hsp1 : 0 < sp) (hsp2 : sp < 2)
    (hth : th < -(r * c / 2)) : c / 4 ≤ -rho⁻¹ * (sp⁻¹ * th) := by
  have hthneg : th < 0 := by nlinarith
  have hspinv : (2 : ℝ)⁻¹ ≤ sp⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hsp1 hsp2.le
  have h4 : sp⁻¹ * th ≤ (2 : ℝ)⁻¹ * th := mul_le_mul_of_nonpos_right hspinv hthneg.le
  have h6 : sp⁻¹ * th ≤ -(r * c / 4) := by linarith
  have hrhoinv : r⁻¹ ≤ rho⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hrho1 hrho2.le
  have hpos : 0 < rho⁻¹ := inv_pos.2 hrho1
  have h7 : rho⁻¹ * (r * c / 4) ≤ -rho⁻¹ * (sp⁻¹ * th) := by nlinarith
  have h8 : r⁻¹ * (r * c / 4) ≤ rho⁻¹ * (r * c / 4) :=
    mul_le_mul_of_nonneg_right hrhoinv (by positivity)
  have h9 : r⁻¹ * (r * c / 4) = c / 4 := by
    field_simp
  linarith

private theorem time_upper_bound {t ε r c rho : ℝ} (_hr : 0 < r) (hc : 0 < c) (ht : t ≤ ε)
    (hε : ε ≤ r * c / 4) (hrho : r / 2 ≤ rho) : t ≤ 2 * rho * (c / 4) := by
  nlinarith

private theorem dist_le_of_hinge {d rho t κ κ' : ℝ} (hd : 0 ≤ d) (hrho : 0 < rho)
    (ht : 0 < t) (hκ : κ ≤ κ') (ht2 : t ≤ 2 * rho * κ)
    (hh : d ^ 2 ≤ rho ^ 2 + t ^ 2 - 2 * rho * t * κ') : d ≤ rho := by
  have h1 : t * t ≤ t * (2 * rho * κ) := mul_le_mul_of_nonneg_left ht2 ht.le
  have h2 : 2 * rho * t * κ ≤ 2 * rho * t * κ' :=
    mul_le_mul_of_nonneg_left hκ (by positivity)
  have h3 : d ^ 2 ≤ rho ^ 2 := by nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith



private theorem exists_mem_of_acute_unit
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {p : M} (hp : p ∈ relBoundary I C) {w : TangentSpace I p}
    (hwu : g.inner p w w = 1) {l : ℝ} (hl : 0 < l)
    (hqN : intrinsicGeodesic (I := I) g hEnorm p w l ∈ maxSliceLocus I C)
    (hqd : Metric.infDist (intrinsicGeodesic (I := I) g hEnorm p w l)
      (relBoundary I C) = l)
    {z : TangentSpace I p} (hzu : g.inner p z z = 1)
    (hzT : z ∈ sliceTangent I (maxSliceLocus I C) p)
    (hzw : 0 < g.inner p w z) :
    ∃ ε : ℝ, 0 < ε ∧ intrinsicGeodesic (I := I) g hEnorm p z ε ∈ C := by
  classical
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p w with hγdef
  have hγcont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p w
  have hγ0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p w
  set B := standardDiagonalInverseBranch (I := I) g hEnorm p with hBdef
  obtain ⟨A, hA, rt, hrt, htube⟩ := branch_source_tube (I := I) B
  obtain ⟨A₀, hA₀A, hA₀open, hpA₀⟩ := mem_nhds_iff.1 hA
  have hgood : ∀ᶠ yz : M × M in 𝓝 (p, p),
      (yz.2 ∈ (B.fixed yz.1).hom.target ∧
        (B.fixed yz.1).hom.symm yz.2 =
          (minimizingVec (I := I) g hEnorm yz.1 yz.2 : E)) ∧
      (yz.1 ∈ maxSliceLocus I C → yz.2 ∈ maxSliceLocus I C →
        ∀ t ∈ Icc (0 : ℝ) 1,
          minJoin (I := I) g hEnorm yz.2 yz.1 t ∈ maxSliceLocus I C) := by
    filter_upwards [branch_minimizing_pair (I := I) B,
      maxSliceLocus_minJoin (C := C) hEnorm hC B] with yz h1 h2
    exact ⟨⟨h1.1, h1.2.1⟩, h2⟩
  obtain ⟨P, Q, hPopen, hpP, hQopen, hpQ, hPQ⟩ := mem_nhds_prod_iff'.1 hgood
  have hpre : IsOpen (γ ⁻¹' (P ∩ Q ∩ A₀)) :=
    ((hPopen.inter hQopen).inter hA₀open).preimage hγcont
  have hpre0 : (0 : ℝ) ∈ γ ⁻¹' (P ∩ Q ∩ A₀) := by
    simp only [mem_preimage, hγ0]
    exact ⟨⟨hpP, hpQ⟩, hpA₀⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 hpre 0 hpre0
  obtain ⟨r, hr0, hrl, hrrt, hrmem⟩ :
      ∃ r : ℝ, 0 < r ∧ r ≤ l ∧ r < rt ∧ γ r ∈ P ∩ Q ∩ A₀ := by
    refine ⟨min (δ / 2) (min l (rt / 2)), lt_min (by linarith) (lt_min hl (by linarith)),
      (min_le_right _ _).trans (min_le_left _ _),
      lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith), ?_⟩
    refine hδsub ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_pos (lt_min (by linarith) (lt_min hl (by linarith)))]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set y : M := γ r with hydef
  have hyP : y ∈ P := hrmem.1.1
  have hyQ : y ∈ Q := hrmem.1.2
  have hyA : y ∈ A := hA₀A hrmem.2
  obtain ⟨hyN, hpy, hyinf⟩ :=
    supporting_segment (hEnorm := hEnorm) hC hp hwu hl hqN hqd hr0 hrl
  rw [← hγdef, ← hydef] at hyN hpy hyinf
  set X : TangentSpace I y := (-r) • (mfderiv 𝓘(ℝ, ℝ) I γ r 1) with hXdef
  obtain ⟨hXrad, hXexp, hXvel⟩ :=
    reversed_radial (I := I) g hEnorm p w r (y := y) hydef.symm (X := X) rfl
  have hUsp : g.inner y (mfderiv 𝓘(ℝ, ℝ) I γ r 1) (mfderiv 𝓘(ℝ, ℝ) I γ r 1) = 1 := by
    have h := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p w r
    rw [hwu] at h
    exact h
  have hXsq : g.inner y X X = r ^ 2 := by
    rw [hXdef, gInner_smul_self (I := I) g y (-r) _, hUsp]
    ring
  have hXlen : Real.sqrt (g.inner y X X) = r := by
    rw [hXsq]
    exact Real.sqrt_sq hr0.le
  have hXsrc : (⟨y, X⟩ : TangentBundle I M) ∈ B.hom.source :=
    htube y hyA X (by rw [hXlen]; exact hrrt)
  have hXT : X ∈ sliceTangent I (maxSliceLocus I C) y := by
    have hneg : IsInnerDirection (I := I) g hEnorm C y (-(mfderiv 𝓘(ℝ, ℝ) I γ r 1)) := by
      rw [isInnerDirection_iff]
      filter_upwards [Ioo_mem_nhdsGT hr0] with σ hσ
      have hgeo : intrinsicGeodesic (I := I) g hEnorm y
          (-(mfderiv 𝓘(ℝ, ℝ) I γ r 1)) σ = γ (r - σ) := by
        have h1 : intrinsicGeodesic (I := I) g hEnorm y (-(mfderiv 𝓘(ℝ, ℝ) I γ r 1)) σ
            = intrinsicGeodesic (I := I) g hEnorm y (mfderiv 𝓘(ℝ, ℝ) I γ r 1) (-σ) :=
          intrinsicGeodesic_neg (I := I) g hEnorm y (mfderiv 𝓘(ℝ, ℝ) I γ r 1) σ
        have h2 : intrinsicGeodesic (I := I) g hEnorm y (mfderiv 𝓘(ℝ, ℝ) I γ r 1) (-σ)
            = γ (-σ + r) :=
          (congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm p w r) (-σ)).symm
        rw [h1, h2]
        congr 1
        ring
      rw [hgeo]
      exact (supporting_segment (hEnorm := hEnorm) hC hp hwu hl hqN hqd
        (by linarith [hσ.2] : (0:ℝ) < r - σ) (by linarith [hσ.1] : r - σ ≤ l)).1
    have hmem := mem_sliceTangent_of_isInnerDirection hneg
    have hmem' := (sliceTangent I (maxSliceLocus I C) y).neg_mem hmem
    rw [neg_neg] at hmem'
    rw [hXdef]
    exact (sliceTangent I (maxSliceLocus I C) y).smul_mem (-r) hmem'
  set Φ := (B.fixed y).hom with hΦdef
  set Ψ := tangentSpaceModelContinuousLinearEquiv (I := I) (M := M) y with hΨdef
  have hXsrcΦ : (X : E) ∈ Φ.source := hXsrc
  have hΦX : Φ (X : E) = p := by
    have h : expMapIntrinsic (I := I) g hEnorm y (Ψ.symm (X : E)) = Φ (X : E) :=
      (B.fixed y).hom_eq hXsrcΦ
    rw [← h]
    exact hXexp
  have hpT : p ∈ Φ.target := by
    rw [← hΦX]
    exact Φ.toPartialEquiv.map_source hXsrcΦ
  have hΦsymmp : Φ.symm p = (X : E) :=
    congrArg (fun t : TangentBundle I M => (t.snd : E)) (B.inv_eq_of_exp hXsrc hXexp)
  set K : Submodule ℝ E :=
    Submodule.map (Ψ.toLinearEquiv : TangentSpace I y →ₗ[ℝ] E)
      (sliceTangent I (maxSliceLocus I C) y) with hKdef
  have hmemK : ∀ u : E, u ∈ K ↔ Ψ.symm u ∈ sliceTangent I (maxSliceLocus I C) y := by
    intro u
    rw [hKdef]
    simp [Submodule.mem_map_equiv]
  have hKclosed : IsClosed (K : Set E) := K.closed_of_finiteDimensional
  have hKmem : ∀ y' ∈ maxSliceLocus I C ∩ (P ∩ Q), (Φ.symm y' : E) ∈ K := by
    rintro y' ⟨hy'N, hy'P, hy'Q⟩
    obtain ⟨⟨-, hchart⟩, -⟩ := hPQ (Set.mk_mem_prod hyP hy'Q)
    obtain ⟨-, hjoin⟩ := hPQ (Set.mk_mem_prod hy'P hyQ)
    have hinner : IsInnerDirection (I := I) g hEnorm C y
        (minimizingVec (I := I) g hEnorm y y') := by
      rw [isInnerDirection_iff]
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
      exact hjoin hy'N hyN t ⟨ht.1.le, ht.2.le⟩
    rw [hΦdef, hchart]
    exact (hmemK _).2 (mem_sliceTangent_of_isInnerDirection hinner)
  have hζK : (mfderiv I 𝓘(ℝ, E) Φ.symm p z : E) ∈ K := by
    refine mfderiv_mem_of_eventually_mem (c := Φ.symm) hpT hKclosed ?_ ?_ hzT
    · filter_upwards [(hPopen.inter hQopen).mem_nhds ⟨hpP, hpQ⟩] with y' hy' hy'N
      exact hKmem y' ⟨hy'N, hy'⟩
    · rw [hΦsymmp]
      exact (hmemK _).2 hXT
  set W : TangentSpace I y := (mfderiv I 𝓘(ℝ, E) Φ.symm p z : E) with hWdef
  have hWT : W ∈ sliceTangent I (maxSliceLocus I C) y := (hmemK _).1 hζK
  have hWz : (mfderiv 𝓘(ℝ, E) I
      (fun v : E => expMapIntrinsic (I := I) g hEnorm y (show TangentSpace I y from v))
      (X : E) (W : E) : E) = (z : E) := by
    have hXsrcΦ' : Φ.symm p ∈ Φ.source := by
      rw [hΦsymmp]
      exact hXsrcΦ
    have hfun : (fun v : E => expMapIntrinsic (I := I) g hEnorm y
        (show TangentSpace I y from v)) =ᶠ[𝓝 (Φ.symm p)] (fun u : E => Φ u) := by
      filter_upwards [Φ.open_source.mem_nhds hXsrcΦ'] with u hu
      exact (B.fixed y).hom_eq hu
    have hmf : mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMapIntrinsic (I := I) g hEnorm y (show TangentSpace I y from v))
        (Φ.symm p) = mfderiv 𝓘(ℝ, E) I (fun u : E => Φ u) (Φ.symm p) := hfun.mfderiv_eq
    rw [← hΦsymmp, hmf]
    exact mfderiv_apply_mfderiv_symm (c := Φ) hpT rfl z
  have hgauss : g.inner p ((-r) • w) z = g.inner y X W := by
    have h := intrinsic_gauss (I := I) g hEnorm y (X : E) (W : E)
    rw [← h]
    exact gInner_congr_base g hXexp.symm hXvel.symm hWz.symm
  have hXW : g.inner y X W = -(r * g.inner p w z) := by
    rw [← hgauss, gInner_smul_left]
    ring
  have hXWneg : g.inner y X W < 0 := by
    rw [hXW]
    have : 0 < r * g.inner p w z := mul_pos hr0 hzw
    linarith
  have hWne : (0 : TangentSpace I y) ≠ W := by
    intro h
    rw [← h] at hXW
    have hzero : g.inner y X 0 = 0 := (g.inner y X).map_zero
    rw [hzero] at hXW
    have : 0 < r * g.inner p w z := mul_pos hr0 hzw
    linarith
  have hWpos : 0 < g.inner y W W := g.pos y W (Ne.symm hWne)
  set XW : ℝ → TangentSpace I y := fun s => X + s • W with hXWdef
  set cur : ℝ → M := fun s => intrinsicGeodesic (I := I) g hEnorm y (XW s) 1 with hcurdef
  set Qs : ℝ → ℝ := fun s => g.inner y (XW s) (XW s) with hQsdef
  have hQs : ∀ s : ℝ, Qs s = r ^ 2 + 2 * s * g.inner y X W + s ^ 2 * g.inner y W W := by
    intro s
    change g.inner y (X + s • W) (X + s • W) = _
    rw [gInner_expand, hXsq]
  have hQscont : Continuous Qs := by
    have hpoly : Qs = fun s : ℝ => r ^ 2 + 2 * s * g.inner y X W + s ^ 2 * g.inner y W W := by
      funext s
      exact hQs s
    rw [hpoly]
    fun_prop
  have hQsnonneg : ∀ s : ℝ, 0 ≤ Qs s := fun s => gInner_self_nonneg (I := I) g y (XW s)
  have hQs0 : Qs 0 = r ^ 2 := by
    rw [hQs 0]
    ring
  set s₁ : ℝ := -(g.inner y X W) / g.inner y W W with hs₁def
  have hs₁pos : 0 < s₁ := div_pos (by linarith) hWpos
  have hQslt : ∀ s ∈ Ioc (0 : ℝ) s₁, Qs s < r ^ 2 := by
    intro s hs
    rw [hQs s]
    have h1 : s * g.inner y W W ≤ -(g.inner y X W) := by
      have h2 : s * g.inner y W W ≤ s₁ * g.inner y W W :=
        mul_le_mul_of_nonneg_right hs.2 hWpos.le
      rw [hs₁def, div_mul_cancel₀ _ (ne_of_gt hWpos)] at h2
      exact h2
    nlinarith [hs.1]
  have hρlt : ∀ s ∈ Ioc (0 : ℝ) s₁, Real.sqrt (Qs s) < r := by
    intro s hs
    have h := Real.sqrt_lt_sqrt (hQsnonneg s) (hQslt s hs)
    rwa [Real.sqrt_sq hr0.le] at h
  have hcur0 : cur 0 = p := by
    rw [hcurdef]
    simp only [hXWdef, zero_smul, add_zero]
    rw [← expMapIntrinsic_def]
    exact hXexp
  have hcurcont : Continuous cur := by
    rw [hcurdef]
    exact (expMapIntrinsic_continuous (I := I) g hEnorm y).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hcurN : ∀ s ∈ Ioc (0 : ℝ) s₁, cur s ∈ maxSliceLocus I C := by
    intro s hs
    have hmem : XW s ∈ sliceTangent I (maxSliceLocus I C) y :=
      (sliceTangent I (maxSliceLocus I C) y).add_mem hXT
        ((sliceTangent I (maxSliceLocus I C) y).smul_mem s hWT)
    have hlen : Real.sqrt (g.inner y (XW s) (XW s)) < Metric.infDist y (relBoundary I C) := by
      rw [hyinf]
      exact hρlt s hs
    have h := expMapIntrinsic_mem_maxSliceLocus hEnorm hC hCclosed hyN hmem hlen
    rwa [expMapIntrinsic_def] at h
  have hcursmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ cur := by
    have h := intrinsicVar_smooth (I := I) g hEnorm y (X : E) (W : E)
    exact h.comp (contMDiff_id.prodMk contMDiff_const)
  set Vel : ∀ s : ℝ, TangentSpace I (cur s) :=
    fun s => mfderiv 𝓘(ℝ, ℝ) I cur s 1 with hVeldef
  have hVelcont : Continuous (fun s : ℝ => (⟨cur s, Vel s⟩ : TangentBundle I M)) := by
    have h := MFDerivAlongCurve.continuous_tangentMap_unitLift (I := I) (M := M) (γ := cur)
      (n := ∞) (by exact_mod_cast le_top) hcursmooth
    simp only [tangentMap] at h
    exact h
  have hVel0 : (Vel 0 : E) = (z : E) := by
    have h := intrinsic_jacobi_one (I := I) g hEnorm y (X : E) (W : E)
    rw [← hWz, ← h]
    rfl
  have hVelT : ∀ s ∈ Ioo (0 : ℝ) s₁, Vel s ∈ sliceTangent I (maxSliceLocus I C) (cur s) := by
    intro s hs
    have hshiftsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun σ : ℝ => cur (s + σ)) :=
      hcursmooth.comp (contMDiff_const.add contMDiff_id)
    have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun σ : ℝ => cur (s + σ)) 0 :=
      hshiftsmooth.contMDiffAt.mdifferentiableAt (by simp)
    have hev : ∀ᶠ σ in 𝓝[>] (0 : ℝ), cur (s + σ) ∈ maxSliceLocus I C := by
      filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hs.2)] with σ hσ
      exact hcurN (s + σ) ⟨by linarith [hσ.1, hs.1], by linarith [hσ.2]⟩
    have h := mem_sliceTangent_of_curve (I := I) (S := maxSliceLocus I C)
      (f := fun σ : ℝ => cur (s + σ)) (x := cur s) (by simp) hev hmd
    have hshift := mfderiv_shift (I := I) (f := cur) (s := s)
      (hcursmooth.contMDiffAt.mdifferentiableAt (by simp))
    have heq : Vel s = (mfderiv 𝓘(ℝ, ℝ) I (fun σ : ℝ => cur (s + σ)) 0 1 :
        TangentSpace I (cur s)) := hshift.symm
    rw [heq]
    exact h
  set Rv : ∀ s : ℝ, TangentSpace I (cur s) :=
    fun s => mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm y (XW s)) 1 1
    with hRvdef
  have hRvspeed : ∀ s : ℝ, g.inner (cur s) (Rv s) (Rv s) = Qs s := fun s =>
    intrinsicGeodesic_speedSq_eq (I := I) g hEnorm y (XW s) 1
  have hRv0 : (Rv 0 : E) = (((-r) • w : TangentSpace I p) : E) := by
    rw [← hXvel, hRvdef]
    exact congrArg (fun V : TangentSpace I y =>
      (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm y V) 1 1 : E))
      (show XW 0 = X by rw [hXWdef]; simp)
  have hRvback : ∀ s σ : ℝ, intrinsicGeodesic (I := I) g hEnorm (cur s) (Rv s) σ
      = intrinsicGeodesic (I := I) g hEnorm y (XW s) (σ + 1) := fun s σ =>
    (congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm y (XW s) 1) σ).symm
  have hRvexp : ∀ s : ℝ, expMapIntrinsic (I := I) g hEnorm (cur s) (Rv s)
      = expMapIntrinsic (I := I) g hEnorm y ((2 : ℝ) • XW s) := by
    intro s
    rw [expMapIntrinsic_def, hRvback s 1, expMapIntrinsic_def,
      intrinsicGeodesic_smul (I := I) g hEnorm y (XW s) 2]
    norm_num
  have hT2cont : Continuous
      (fun s : ℝ => expMapIntrinsic (I := I) g hEnorm y ((2 : ℝ) • XW s)) :=
    (expMapIntrinsic_continuous (I := I) g hEnorm y).comp
      (continuous_const.smul (continuous_const.add (continuous_id.smul continuous_const)))
  have hRvsrc : ∀ᶠ s in 𝓝 (0 : ℝ), (⟨cur s, Rv s⟩ : TangentBundle I M) ∈ B.hom.source := by
    have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), cur s ∈ A₀ := by
      refine hcurcont.continuousAt.preimage_mem_nhds ?_
      rw [hcur0]
      exact hA₀open.mem_nhds hpA₀
    have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), Real.sqrt (Qs s) < rt := by
      have hc : ContinuousAt (fun s : ℝ => Real.sqrt (Qs s)) 0 :=
        (Real.continuous_sqrt.comp hQscont).continuousAt
      refine hc.eventually_lt_const ?_
      change Real.sqrt (Qs 0) < rt
      rw [hQs0, Real.sqrt_sq hr0.le]
      exact hrrt
    filter_upwards [h1, h2] with s hs1 hs2
    refine htube (cur s) (hA₀A hs1) (Rv s) ?_
    rw [hRvspeed s]
    exact hs2
  have hRvcont : ContinuousAt (fun s : ℝ => (⟨cur s, Rv s⟩ : TangentBundle I M)) 0 := by
    have hmem0 : (cur 0, expMapIntrinsic (I := I) g hEnorm y ((2 : ℝ) • XW 0))
        ∈ B.hom.target := by
      have hsrc0 := hRvsrc.self_of_nhds
      have h := B.hom.map_source hsrc0
      have heval : B.hom (⟨cur 0, Rv 0⟩ : TangentBundle I M)
          = (cur 0, expMapIntrinsic (I := I) g hEnorm (cur 0) (Rv 0)) := B.hom_eq hsrc0
      rw [heval, hRvexp 0] at h
      exact h
    have hpair : ContinuousAt
        (fun s : ℝ => (cur s, expMapIntrinsic (I := I) g hEnorm y ((2 : ℝ) • XW s))) 0 :=
      hcurcont.continuousAt.prodMk hT2cont.continuousAt
    have hsymm0 : ContinuousAt (fun q : M × M => B.hom.symm q)
        (cur 0, expMapIntrinsic (I := I) g hEnorm y ((2 : ℝ) • XW 0)) :=
      B.hom.continuousOn_symm.continuousAt (B.hom.open_target.mem_nhds hmem0)
    have hsymmcont : ContinuousAt
        ((fun q : M × M => B.hom.symm q) ∘
          fun s : ℝ => (cur s, expMapIntrinsic (I := I) g hEnorm y ((2 : ℝ) • XW s)))
        0 := ContinuousAt.comp (x := (0 : ℝ)) hsymm0 hpair
    refine hsymmcont.congr ?_
    filter_upwards [hRvsrc] with s hs
    exact B.inv_eq_of_exp hs (hRvexp s)
  set sp : ℝ → ℝ := fun s => Real.sqrt (g.inner (cur s) (Vel s) (Vel s)) with hspdef
  have hspcont : ContinuousAt sp 0 :=
    Real.continuous_sqrt.continuousAt.comp
      (continuousAt_gInner g hVelcont.continuousAt hVelcont.continuousAt)
  have hsp0 : sp 0 = 1 := by
    rw [hspdef]
    simp only
    rw [gInner_congr_base g hcur0 hVel0 hVel0, hzu, Real.sqrt_one]
  set θ : ℝ → ℝ := fun s => g.inner (cur s) (Rv s) (Vel s) with hθdef
  have hθcont : ContinuousAt θ 0 := continuousAt_gInner g hRvcont hVelcont.continuousAt
  have hθ0 : θ 0 = -(r * g.inner p w z) := by
    rw [hθdef]
    simp only
    rw [gInner_congr_base g hcur0 hRv0 hVel0, gInner_smul_left]
    ring
  set c : ℝ := g.inner p w z with hcdef
  have hcpos : 0 < c := hzw
  set ε : ℝ := min (r * c / 4) (rt / 2) with hεdef
  have hεpos : 0 < ε := lt_min (by positivity) (by linarith)
  have hεrt : ε < rt := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hmain : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      expMapIntrinsic (I := I) g hEnorm (cur s) (ε • ((sp s)⁻¹ • Vel s)) ∈ C := by
    have hev1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) s₁ := Ioo_mem_nhdsGT hs₁pos
    have hev2 : ∀ᶠ s in 𝓝 (0 : ℝ), r / 2 < Real.sqrt (Qs s) := by
      have hc : ContinuousAt (fun s : ℝ => Real.sqrt (Qs s)) 0 :=
        (Real.continuous_sqrt.comp hQscont).continuousAt
      refine hc.eventually_const_lt ?_
      change r / 2 < Real.sqrt (Qs 0)
      rw [hQs0, Real.sqrt_sq hr0.le]
      linarith
    have hev3 : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < sp s ∧ sp s < 2 := by
      have ha : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < sp s := by
        refine hspcont.eventually_const_lt ?_
        rw [hsp0]
        norm_num
      have hb : ∀ᶠ s in 𝓝 (0 : ℝ), sp s < 2 := by
        refine hspcont.eventually_lt_const ?_
        rw [hsp0]
        norm_num
      filter_upwards [ha, hb] with s h1 h2 using ⟨h1, h2⟩
    have hev4 : ∀ᶠ s in 𝓝 (0 : ℝ), θ s < -(r * c / 2) := by
      refine hθcont.eventually_lt_const ?_
      rw [hθ0]
      have hrc : 0 < r * c := mul_pos hr0 hcpos
      linarith
    have hev5 : ∀ᶠ s in 𝓝 (0 : ℝ), cur s ∈ Q := by
      refine hcurcont.continuousAt.preimage_mem_nhds ?_
      rw [hcur0]
      exact hQopen.mem_nhds hpQ
    filter_upwards [hev1, hev2.filter_mono nhdsWithin_le_nhds,
      hev3.filter_mono nhdsWithin_le_nhds, hev4.filter_mono nhdsWithin_le_nhds,
      hev5.filter_mono nhdsWithin_le_nhds, hRvsrc.filter_mono nhdsWithin_le_nhds]
      with s hs1 hs2 hs3 hs4 hs5 hs6
    have hsIoc : s ∈ Ioc (0 : ℝ) s₁ := ⟨hs1.1, hs1.2.le⟩
    have hρpos : 0 < Real.sqrt (Qs s) := by linarith
    have hρltr : Real.sqrt (Qs s) < r := hρlt s hsIoc
    have hQsq : Qs s = Real.sqrt (Qs s) ^ 2 := (Real.sq_sqrt (hQsnonneg s)).symm
    set ρ : ℝ := Real.sqrt (Qs s) with hρdef
    have hρne : ρ ≠ 0 := ne_of_gt hρpos
    have hspne : sp s ≠ 0 := ne_of_gt hs3.1
    set uy : TangentSpace I (cur s) := (-ρ⁻¹) • Rv s with huydef
    set u : TangentSpace I (cur s) := (sp s)⁻¹ • Vel s with hudef
    have hunit_uy : g.inner (cur s) uy uy = 1 := by
      rw [huydef, gInner_smul_self (I := I) g (cur s) (-ρ⁻¹) (Rv s), hRvspeed s, hQsq]
      field_simp
    have hunit_u : g.inner (cur s) u u = 1 := by
      have hsq : sp s ^ 2 = g.inner (cur s) (Vel s) (Vel s) := by
        rw [hspdef]
        exact Real.sq_sqrt (gInner_self_nonneg (I := I) g (cur s) (Vel s))
      rw [hudef, gInner_smul_self (I := I) g (cur s) (sp s)⁻¹ (Vel s), ← hsq]
      field_simp
    have hyreach : intrinsicGeodesic (I := I) g hEnorm (cur s) uy ρ = y := by
      rw [huydef, intrinsicGeo_smul_apply (I := I) g hEnorm (cur s) (Rv s) (-ρ⁻¹) ρ,
        hRvback s (-ρ⁻¹ * ρ),
        show -ρ⁻¹ * ρ + 1 = 0 by rw [neg_mul, inv_mul_cancel₀ hρne, neg_add_cancel]]
      exact intrinsicGeodesic_zero (I := I) g hEnorm y (XW s)
    have hdisty : dist y (cur s) = ρ := by
      obtain ⟨⟨-, hchart⟩, -⟩ := hPQ (Set.mk_mem_prod hyP hs5)
      have hXWsrc : (⟨y, XW s⟩ : TangentBundle I M) ∈ B.hom.source := by
        refine htube y hyA (XW s) ?_
        exact lt_trans hρltr hrrt
      have hXWexp : expMapIntrinsic (I := I) g hEnorm y (XW s) = cur s := by
        rw [expMapIntrinsic_def]
      have hinv := B.inv_eq_of_exp hXWsrc hXWexp
      have hvec : (minimizingVec (I := I) g hEnorm y (cur s) : E) = (XW s : E) := by
        rw [← hchart]
        exact congrArg (fun t : TangentBundle I M => (t.snd : E)) hinv
      rw [← riemannian_toReal_eq_dist (I := I), ← minimizingVec_len (I := I) g hEnorm y (cur s),
        show minimizingVec (I := I) g hEnorm y (cur s) = XW s from hvec]
    have hangle : c / 4 ≤ g.inner (cur s) uy u := by
      have hval : g.inner (cur s) uy u = -ρ⁻¹ * ((sp s)⁻¹ * θ s) := by
        rw [huydef, hudef, gInner_smul_left, gInner_smul_right, hθdef]
      rw [hval]
      exact angle_lower_bound hr0 hcpos hρpos hρltr hs3.1 hs3.2 hs4
    have hstay : ∀ t ∈ Icc (0 : ℝ) ε,
        intrinsicGeodesic (I := I) g hEnorm (cur s) u t ∈ Metric.ball y r := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with ht0 | ht0
      · rw [← ht0, intrinsicGeodesic_zero, Metric.mem_ball, dist_comm, hdisty]
        exact hρltr
      · have hh := complete_hinge_sq (I := I) g hEnorm hsec (cur s) uy u ρ t hρpos ht0
          hunit_uy hunit_u
          (by rw [hyreach, riemannian_toReal_eq_dist (I := I), dist_comm, hdisty])
        rw [hyreach, riemannian_toReal_eq_dist (I := I)] at hh
        have hbound : t ≤ 2 * ρ * (c / 4) :=
          time_upper_bound hr0 hcpos ht.2 (min_le_left _ _) hs2.le
        have hd : dist y (intrinsicGeodesic (I := I) g hEnorm (cur s) u t) ≤ ρ :=
          dist_le_of_hinge dist_nonneg hρpos ht0 hangle hbound hh
        rw [Metric.mem_ball, dist_comm]
        exact lt_of_le_of_lt hd hρltr
    have huT : u ∈ sliceTangent I (maxSliceLocus I C) (cur s) := by
      rw [hudef]
      exact (sliceTangent I (maxSliceLocus I C) (cur s)).smul_mem _ (hVelT s hs1)
    have hN := mem_maxSliceLocus_of_mem_sliceTangent hEnorm hC hCclosed (hcurN s hsIoc) huT
      (ball_inter_subset_maxSliceLocus (I := I) (C := C) y hyinf.ge) hεpos.le hstay
    have hend := hN ε ⟨hεpos.le, le_rfl⟩
    rw [← expMapIntrinsic_smul_eq_intrinsicGeodesic] at hend
    exact maxSliceLocus_subset hend
  have hlim : Tendsto
      (fun s : ℝ => expMapIntrinsic (I := I) g hEnorm (cur s) (ε • ((sp s)⁻¹ • Vel s)))
      (𝓝[>] (0 : ℝ)) (𝓝 (expMapIntrinsic (I := I) g hEnorm p (ε • z))) := by
    have hbundle : ContinuousAt
        (fun s : ℝ => (⟨cur s, (ε * (sp s)⁻¹) • Vel s⟩ : TangentBundle I M)) 0 :=
      continuousAt_scaled_bundle hVelcont.continuousAt
        (continuousAt_const.mul (hspcont.inv₀ (by rw [hsp0]; norm_num)))
    have hval : (⟨cur 0, (ε * (sp 0)⁻¹) • Vel 0⟩ : TangentBundle I M) = ⟨p, ε • z⟩ := by
      refine tangentBundle_mk_congr hcur0 ?_
      rw [hsp0]
      simp only [inv_one, mul_one]
      exact congrArg (fun v : E => (ε : ℝ) • v) hVel0
    have hsrc : (⟨p, ε • z⟩ : TangentBundle I M) ∈ B.hom.source := by
      refine htube p (mem_of_mem_nhds hA) (ε • z) ?_
      rw [sqrt_gInner_smul_self (I := I) g p hεpos.le z, hzu, Real.sqrt_one, mul_one]
      exact hεrt
    have hcontB : ContinuousAt (fun s : ℝ =>
        B.hom (⟨cur s, (ε * (sp s)⁻¹) • Vel s⟩ : TangentBundle I M)) 0 := by
      refine ContinuousAt.comp ?_ hbundle
      rw [hval]
      exact B.hom.continuousOn.continuousAt (B.hom.open_source.mem_nhds hsrc)
    have hsrcev : ∀ᶠ s in 𝓝 (0 : ℝ),
        (⟨cur s, (ε * (sp s)⁻¹) • Vel s⟩ : TangentBundle I M) ∈ B.hom.source :=
      hbundle.preimage_mem_nhds (by rw [hval]; exact B.hom.open_source.mem_nhds hsrc)
    have heq : ∀ᶠ s in 𝓝 (0 : ℝ),
        (B.hom (⟨cur s, (ε * (sp s)⁻¹) • Vel s⟩ : TangentBundle I M)).2
          = expMapIntrinsic (I := I) g hEnorm (cur s) (ε • ((sp s)⁻¹ • Vel s)) := by
      filter_upwards [hsrcev] with s hs
      have hval : B.hom (⟨cur s, (ε * (sp s)⁻¹) • Vel s⟩ : TangentBundle I M)
          = diagExp (I := I) g hEnorm ⟨cur s, (ε * (sp s)⁻¹) • Vel s⟩ := B.hom_eq hs
      rw [hval, smul_smul]
      rfl
    have hval2 : (B.hom (⟨cur 0, (ε * (sp 0)⁻¹) • Vel 0⟩ : TangentBundle I M)).2
        = expMapIntrinsic (I := I) g hEnorm p (ε • z) := by
      have hpval : B.hom (⟨p, ε • z⟩ : TangentBundle I M)
          = diagExp (I := I) g hEnorm ⟨p, ε • z⟩ := B.hom_eq hsrc
      rw [hval, hpval]
      rfl
    have hsnd : ContinuousAt (fun s : ℝ =>
        (B.hom (⟨cur s, (ε * (sp s)⁻¹) • Vel s⟩ : TangentBundle I M)).2) 0 :=
      continuous_snd.continuousAt.comp hcontB
    rw [ContinuousAt, hval2] at hsnd
    exact (hsnd.congr' heq).mono_left nhdsWithin_le_nhds
  refine ⟨ε, hεpos, ?_⟩
  have hmemC : expMapIntrinsic (I := I) g hEnorm p (ε • z) ∈ C :=
    hCclosed.mem_of_tendsto hlim hmain
  rwa [expMapIntrinsic_smul_eq_intrinsicGeodesic] at hmemC

theorem hasAcuteTangentCone_of_totallyConvex
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C) :
    HasAcuteTangentCone (I := I) g hEnorm C := by
  intro p hp w hw v z hv hspan hzw
  obtain ⟨a, b, hz⟩ := hspan
  obtain ⟨hwu, l, hl, hqN, hqd⟩ := hw
  have hvT : v ∈ sliceTangent I (maxSliceLocus I C) p :=
    mem_sliceTangent_of_isInnerDirection hv
  have hwin : IsInnerDirection (I := I) g hEnorm C p w :=
    isInnerDirection_of_isSupportingDirection hC hp.1 ⟨hwu, l, hl, hqN, hqd⟩
  have hwT : w ∈ sliceTangent I (maxSliceLocus I C) p :=
    mem_sliceTangent_of_isInnerDirection hwin
  have hzT : z ∈ sliceTangent I (maxSliceLocus I C) p := by
    rw [hz]
    exact (sliceTangent I (maxSliceLocus I C) p).add_mem
      ((sliceTangent I (maxSliceLocus I C) p).smul_mem a hvT)
      ((sliceTangent I (maxSliceLocus I C) p).smul_mem b hwT)
  have hwz : 0 < g.inner p w z := by
    rw [g.symm p w z]
    exact hzw
  have hzne : z ≠ 0 := by
    rintro rfl
    rw [(g.inner p w).map_zero] at hwz
    exact lt_irrefl 0 hwz
  have hzz : 0 < g.inner p z z := g.pos p z hzne
  set n : ℝ := Real.sqrt (g.inner p z z) with hndef
  have hn : 0 < n := Real.sqrt_pos.2 hzz
  have hnsq : n ^ 2 = g.inner p z z := Real.sq_sqrt hzz.le
  have hunit : g.inner p (n⁻¹ • z) (n⁻¹ • z) = 1 := by
    rw [gInner_smul_self (I := I) g p n⁻¹ z, ← hnsq, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hn))]
  have hzTn : n⁻¹ • z ∈ sliceTangent I (maxSliceLocus I C) p :=
    (sliceTangent I (maxSliceLocus I C) p).smul_mem n⁻¹ hzT
  have hzwn : 0 < g.inner p w (n⁻¹ • z) := by
    rw [gInner_smul_right]
    exact mul_pos (inv_pos.2 hn) hwz
  obtain ⟨ε, hε, hmem⟩ := exists_mem_of_acute_unit g hEnorm hsec hC hCclosed hp hwu hl hqN hqd
    hunit hzTn hzwn
  have hmemT : intrinsicGeodesic (I := I) g hEnorm p z (n⁻¹ * ε) ∈ C := by
    rw [← intrinsicGeo_smul_apply (I := I) g hEnorm p z n⁻¹ ε]
    exact hmem
  have hT : 0 < n⁻¹ * ε := mul_pos (inv_pos.2 hn) hε
  have hmaps : MapsTo (intrinsicGeodesic (I := I) g hEnorm p z) (Icc (0 : ℝ) (n⁻¹ * ε)) C :=
    hC hT.le ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm p z).isGeodesicOn _)
      (intrinsicGeodesic_continuous (I := I) g hEnorm p z).continuousOn
      (by rw [intrinsicGeodesic_zero]; exact hp.1) hmemT
  filter_upwards [Ioo_mem_nhdsGT hT] with s hs
  exact hmaps ⟨hs.1.le, hs.2.le⟩

theorem hasSupportingHalfSpaces_relBoundary_of_totallyConvex
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hconn : IsPreconnected C) :
    HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C) :=
  hasSupportingHalfSpaces_relBoundary_of_hasAcuteTangentCone g hEnorm hsec hC hCclosed hconn
    (hasAcuteTangentCone_of_totallyConvex g hEnorm hsec hC hCclosed)

end DifferentialGeometry.Geometry.Topology
