import DifferentialGeometry.Geometry.Comparison.Nonnegative.BoundaryConcavityTangent
import DifferentialGeometry.Geometry.Comparison.Nonnegative.BoundaryShift
import DifferentialGeometry.Geometry.Comparison.Nonnegative.FocalJacobi
import DifferentialGeometry.Geometry.Comparison.ConvexTangentParallel
import DifferentialGeometry.Geometry.Comparison.ConvexAcuteCone
import DifferentialGeometry.Geometry.Comparison.Soul.SoulShaving

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation

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
private theorem shiftT_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem shiftT_dist_intrinsicGeodesic_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) {s t : ℝ} (hst : s ≤ t) :
    dist (intrinsicGeodesic (I := I) g hEnorm p v s)
        (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ Real.sqrt (g.inner p v v) * (t - s) := by
  have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p v hst
  rw [← shiftT_toReal_eq_dist (I := I)]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (by linarith))]

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem shiftT_dist_le_radius
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) {t : ℝ} (ht : 0 ≤ t) :
    dist p (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ Real.sqrt (g.inner p v v) * t := by
  have h := shiftT_dist_intrinsicGeodesic_le (I := I) g hEnorm p v ht
  rwa [intrinsicGeodesic_zero, sub_zero] at h

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem shiftT_infDist_of_minimizing
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {B : Set M} {x : M} {u : TangentSpace I x} (hu : g.inner x u u = 1)
    (hmem : intrinsicGeodesic (I := I) g hEnorm x u (Metric.infDist x B) ∈ B)
    {t : ℝ} (ht0 : 0 ≤ t) (htl : t ≤ Metric.infDist x B) :
    dist x (intrinsicGeodesic (I := I) g hEnorm x u t) = t ∧
      Metric.infDist (intrinsicGeodesic (I := I) g hEnorm x u t) B
        = Metric.infDist x B - t := by
  have hsp : Real.sqrt (g.inner x u u) = 1 := by rw [hu, Real.sqrt_one]
  have hτ0 : intrinsicGeodesic (I := I) g hEnorm x u 0 = x :=
    intrinsicGeodesic_zero (I := I) g hEnorm x u
  have hl0 : (0 : ℝ) ≤ Metric.infDist x B := Metric.infDist_nonneg
  have h1 : dist x (intrinsicGeodesic (I := I) g hEnorm x u t) ≤ t := by
    have h := shiftT_dist_intrinsicGeodesic_le (I := I) g hEnorm x u ht0
    rw [hτ0, hsp, one_mul, sub_zero] at h
    exact h
  have h2 : dist (intrinsicGeodesic (I := I) g hEnorm x u t)
      (intrinsicGeodesic (I := I) g hEnorm x u (Metric.infDist x B))
      ≤ Metric.infDist x B - t := by
    have h := shiftT_dist_intrinsicGeodesic_le (I := I) g hEnorm x u htl
    rw [hsp, one_mul] at h
    exact h
  have h3 : dist x (intrinsicGeodesic (I := I) g hEnorm x u (Metric.infDist x B))
      ≤ Metric.infDist x B := by
    have h := shiftT_dist_intrinsicGeodesic_le (I := I) g hEnorm x u hl0
    rw [hτ0, hsp, one_mul, sub_zero] at h
    exact h
  have h4 : Metric.infDist x B
      ≤ dist x (intrinsicGeodesic (I := I) g hEnorm x u (Metric.infDist x B)) :=
    Metric.infDist_le_dist_of_mem hmem
  have h5 : dist x (intrinsicGeodesic (I := I) g hEnorm x u (Metric.infDist x B))
      ≤ dist x (intrinsicGeodesic (I := I) g hEnorm x u t)
        + dist (intrinsicGeodesic (I := I) g hEnorm x u t)
          (intrinsicGeodesic (I := I) g hEnorm x u (Metric.infDist x B)) :=
    dist_triangle _ _ _
  have hxt : dist x (intrinsicGeodesic (I := I) g hEnorm x u t) = t := by linarith
  have htl' : dist (intrinsicGeodesic (I := I) g hEnorm x u t)
      (intrinsicGeodesic (I := I) g hEnorm x u (Metric.infDist x B))
      = Metric.infDist x B - t := by linarith
  refine ⟨hxt, le_antisymm ?_ ?_⟩
  · have := Metric.infDist_le_dist_of_mem
      (x := intrinsicGeodesic (I := I) g hEnorm x u t) hmem
    linarith [this, htl'.le, htl'.ge]
  · have h6 : Metric.infDist x B
        ≤ Metric.infDist (intrinsicGeodesic (I := I) g hEnorm x u t) B
          + dist x (intrinsicGeodesic (I := I) g hEnorm x u t) :=
      Metric.infDist_le_infDist_add_dist
    rw [hxt] at h6
    linarith

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem shiftT_mem_sliceTangent_congr {S : Set M} {x x' : M} (hx : x = x')
    {v : TangentSpace I x} (hv : v ∈ sliceTangent I S x) :
    (v : TangentSpace I x') ∈ sliceTangent I S x' := by
  subst hx
  exact hv

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem shiftT_isParallelPerpUnitField_mono
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {y : M} {u : TangentSpace I y}
    {ξ : ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm y u t)} {L L' : ℝ}
    (hξ : IsParallelPerpUnitField (I := I) g hEnorm y u ξ L) (hL : L' ≤ L) :
    IsParallelPerpUnitField (I := I) g hEnorm y u ξ L' :=
  ⟨fun t ht => hξ.1 t (Icc_subset_Icc le_rfl hL ht),
    fun t ht => hξ.2.1 t (Icc_subset_Icc le_rfl hL ht),
    fun t ht => hξ.2.2.1 t (Icc_subset_Icc le_rfl hL ht),
    fun t ht => hξ.2.2.2 t (Icc_subset_Icc le_rfl hL ht)⟩



omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem shiftT_source_tube
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
  obtain ⟨Cb, hCb, hbound⟩ :=
    eventually_norm_trivializationAt_lt E (fun x : M => TangentSpace I x) p
  change ∀ᶠ y in 𝓝 p, ‖e.continuousLinearMapAt ℝ y‖ < Cb at hbound
  let A := (U ∩ {y | ‖e.continuousLinearMapAt ℝ y‖ < Cb}) ∩ e.baseSet
  have hA : A ∈ 𝓝 p := inter_mem (inter_mem hU hbound) (e.open_baseSet.mem_nhds hpbase)
  refine ⟨A, hA, r / Cb, div_pos hr hCb, ?_⟩
  intro y hy v hv
  have hnorm : ‖v‖ = Real.sqrt (g.inner y v v) := by
    have h := hEnorm y v
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) (Real.sqrt_nonneg _)).1 h
  let w := e.continuousLinearMapAt ℝ y v
  have hw : ‖w‖ < r := by
    calc
      ‖w‖ ≤ ‖e.continuousLinearMapAt ℝ y‖ * ‖v‖ := (e.continuousLinearMapAt ℝ y).le_opNorm v
      _ ≤ Cb * ‖v‖ := mul_le_mul_of_nonneg_right hy.1.2.le (norm_nonneg v)
      _ < Cb * (r / Cb) := mul_lt_mul_of_pos_left (by rwa [hnorm]) hCb
      _ = r := mul_div_cancel₀ r hCb.ne'
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

private theorem shiftT_exists_minimizingVec_radius_near
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g) (p : M) :
    ∃ A ∈ 𝓝 p, ∃ r : ℝ, 0 < r ∧ ∀ y ∈ A, ∀ v : TangentSpace I y,
      Real.sqrt (g.inner y v v) < r →
      minimizingVec (I := I) g hEnorm y (expMapIntrinsic (I := I) g hEnorm y v) = v := by
  obtain ⟨A, hA, r, hr, hsrc⟩ := shiftT_source_tube (standardDiagonalInverseBranch (I := I) g hEnorm p)
  refine ⟨A, hA, r, hr, ?_⟩
  intro y hy v hv
  have hvsrc : (⟨y, v⟩ : TangentBundle I M) ∈ (standardDiagonalInverseBranch (I := I) g hEnorm p).hom.source :=
    hsrc y hy v hv
  have h1 : (standardDiagonalInverseBranch (I := I) g hEnorm p).inv (y, expMapIntrinsic (I := I) g hEnorm y v)
      = (⟨y, v⟩ : TangentBundle I M) :=
    (standardDiagonalInverseBranch (I := I) g hEnorm p).inv_eq_of_exp hvsrc rfl
  have hdist : dist y (expMapIntrinsic (I := I) g hEnorm y v)
      ≤ Real.sqrt (g.inner y v v) := by
    have h := shiftT_dist_le_radius (I := I) g hEnorm y v (show (0 : ℝ) ≤ 1 by norm_num)
    rwa [mul_one, ← expMapIntrinsic_def] at h
  have hlen : Real.sqrt (g.inner y
      (minimizingVec (I := I) g hEnorm y (expMapIntrinsic (I := I) g hEnorm y v))
      (minimizingVec (I := I) g hEnorm y (expMapIntrinsic (I := I) g hEnorm y v)))
      = dist y (expMapIntrinsic (I := I) g hEnorm y v) := by
    rw [minimizingVec_len, shiftT_toReal_eq_dist (I := I)]
  have hmsrc : (⟨y, minimizingVec (I := I) g hEnorm y
      (expMapIntrinsic (I := I) g hEnorm y v)⟩ : TangentBundle I M)
      ∈ (standardDiagonalInverseBranch (I := I) g hEnorm p).hom.source :=
    hsrc y hy _ (by rw [hlen]; exact lt_of_le_of_lt hdist hv)
  have h2 : (standardDiagonalInverseBranch (I := I) g hEnorm p).inv (y, expMapIntrinsic (I := I) g hEnorm y v)
      = (⟨y, minimizingVec (I := I) g hEnorm y (expMapIntrinsic (I := I) g hEnorm y v)⟩ :
        TangentBundle I M) :=
    (standardDiagonalInverseBranch (I := I) g hEnorm p).inv_eq_of_exp hmsrc
      (minimizingVec_exp (I := I) g hEnorm y (expMapIntrinsic (I := I) g hEnorm y v))
  exact congrArg (fun b : TangentBundle I M => (b.snd : E)) (h2.symm.trans h1)

private theorem shiftT_exists_uniform_cone_radius
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) {K : Set M} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ K, p ∈ C → ∀ v : TangentSpace I p,
      Real.sqrt (g.inner p v v) < r →
      expMapIntrinsic (I := I) g hEnorm p v ∈ maxSliceLocus I C →
      ∀ s ∈ Ioc (0 : ℝ) 1,
        expMapIntrinsic (I := I) g hEnorm p (s • v) ∈ maxSliceLocus I C := by
  classical
  have hloc : ∀ c : M, ∃ δ : ℝ, 0 < δ ∧
      (∀ y ∈ Metric.ball c (2 * δ), ∀ v : TangentSpace I y,
        Real.sqrt (g.inner y v v) < 2 * δ →
        minimizingVec (I := I) g hEnorm y (expMapIntrinsic (I := I) g hEnorm y v) = v) ∧
      (∀ q ∈ Metric.ball c (2 * δ), ∀ p ∈ Metric.ball c (2 * δ),
        q ∈ maxSliceLocus I C → p ∈ C → ∀ t ∈ Ioc (0 : ℝ) 1,
          minJoin (I := I) g hEnorm p q t ∈ maxSliceLocus I C) := by
    intro c
    obtain ⟨A, hA, r₀, hr₀, hmin⟩ :=
      shiftT_exists_minimizingVec_radius_near (I := I) g hEnorm c
    obtain ⟨P, Q, hP, hcP, hQ, hcQ, hPQ⟩ := mem_nhds_prod_iff'.1
      (maxSliceLocus_pair (I := I) hEnorm hC (standardDiagonalInverseBranch (I := I) g hEnorm c))
    obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.1 hA
    obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.1 (hP.mem_nhds hcP)
    obtain ⟨ε₃, hε₃, hb₃⟩ := Metric.mem_nhds_iff.1 (hQ.mem_nhds hcQ)
    have hmul : 2 * (min (min ε₁ ε₂) (min ε₃ r₀) / 2) = min (min ε₁ ε₂) (min ε₃ r₀) := by ring
    refine ⟨min (min ε₁ ε₂) (min ε₃ r₀) / 2, by positivity, ?_, ?_⟩
    · intro y hy v hv
      rw [hmul] at hy hv
      exact hmin y (hb₁ (Metric.ball_subset_ball
        (le_trans (min_le_left _ _) (min_le_left _ _)) hy)) v
        (lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _)))
    · intro q hq p hp hqN hpC t ht
      rw [hmul] at hq hp
      exact hPQ (Set.mk_mem_prod
        (hb₂ (Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _)) hq))
        (hb₃ (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _)) hp)))
        hqN hpC t ht
  choose δ hδpos hδmin hδjoin using hloc
  obtain ⟨tt, _, hsub⟩ := hK.elim_nhds_subcover (fun c => Metric.ball c (δ c))
    fun c _ => Metric.ball_mem_nhds c (hδpos c)
  rcases tt.eq_empty_or_nonempty with rfl | htne
  · refine ⟨1, one_pos, ?_⟩
    intro p hp
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty] at hsub
    exact absurd (hsub hp) (by simp)
  refine ⟨tt.inf' htne δ, (Finset.lt_inf'_iff htne).2 fun c _ => hδpos c, ?_⟩
  intro p hp hpC v hv hexp s hs
  obtain ⟨c, hct, hpc⟩ : ∃ c ∈ tt, p ∈ Metric.ball c (δ c) := by
    simpa only [mem_iUnion, exists_prop] using hsub hp
  have hδle : tt.inf' htne δ ≤ δ c := Finset.inf'_le δ hct
  have hpball : p ∈ Metric.ball c (2 * δ c) :=
    Metric.ball_subset_ball (by linarith [hδpos c]) hpc
  have hpq : dist p (expMapIntrinsic (I := I) g hEnorm p v) ≤ Real.sqrt (g.inner p v v) := by
    have h := shiftT_dist_le_radius (I := I) g hEnorm p v (show (0 : ℝ) ≤ 1 by norm_num)
    rwa [mul_one, ← expMapIntrinsic_def] at h
  have hvδ : Real.sqrt (g.inner p v v) < δ c := lt_of_lt_of_le hv hδle
  have hqball : expMapIntrinsic (I := I) g hEnorm p v ∈ Metric.ball c (2 * δ c) := by
    have h1 : dist c p < δ c := by
      rw [dist_comm]
      simpa only [Metric.mem_ball] using hpc
    have h2 : dist c (expMapIntrinsic (I := I) g hEnorm p v)
        ≤ dist c p + dist p (expMapIntrinsic (I := I) g hEnorm p v) := dist_triangle _ _ _
    have h3 : dist (expMapIntrinsic (I := I) g hEnorm p v) c < 2 * δ c := by
      rw [dist_comm]; linarith
    simpa only [Metric.mem_ball] using h3
  have hvmin : minimizingVec (I := I) g hEnorm p (expMapIntrinsic (I := I) g hEnorm p v) = v :=
    hδmin c p hpball v (by linarith [hδpos c])
  have hjoin := hδjoin c _ hqball p hpball hexp hpC s hs
  rw [minJoin, hvmin] at hjoin
  rw [expMapIntrinsic_def, intrinsicGeodesic_smul]
  exact hjoin



private theorem shiftT_no_escape
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    {p : M} (hp : p ∈ maxSliceLocus I C) {v : TangentSpace I p}
    (hv : v ∈ sliceTangent I (maxSliceLocus I C) p) {T : ℝ} (hT : 0 ≤ T)
    (hstay : ∀ s ∈ Icc (0 : ℝ) T,
      intrinsicGeodesic (I := I) g hEnorm p v s ∉ relBoundary I C) :
    ∀ s ∈ Icc (0 : ℝ) T,
      intrinsicGeodesic (I := I) g hEnorm p v s ∈ maxSliceLocus I C := by
  refine mem_maxSliceLocus_of_mem_sliceTangent hEnorm hC hCclosed hp hv
    (O := (relBoundary I C)ᶜ) ?_ hT hstay
  intro z hz
  rw [← diff_relBoundary (I := I) C]
  exact ⟨hz.2, hz.1⟩

private theorem shiftT_locus_propagation
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (q : M) (v : TangentSpace I q)
    (t₀ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s₁ s₂ : ℝ, |s₁ - t₀| < δ → |s₂ - t₀| < δ →
      intrinsicGeodesic (I := I) g hEnorm q v s₁ ∈ maxSliceLocus I C →
      intrinsicGeodesic (I := I) g hEnorm q v s₂ ∈ C →
      ∀ t ∈ Ioc (0 : ℝ) 1,
        intrinsicGeodesic (I := I) g hEnorm q v (t * (s₁ - s₂) + s₂)
          ∈ maxSliceLocus I C := by
  have hcont : Continuous (intrinsicGeodesic (I := I) g hEnorm q v) :=
    intrinsicGeodesic_continuous (I := I) g hEnorm q v
  have h1 := minJoin_intrinsicGeodesic_near (I := I) (g := g) (hEnorm := hEnorm) v t₀
    (standardDiagonalInverseBranch (I := I) g hEnorm (intrinsicGeodesic (I := I) g hEnorm q v t₀))
  have hmap : Tendsto (fun st : ℝ × ℝ => (intrinsicGeodesic (I := I) g hEnorm q v st.1,
        intrinsicGeodesic (I := I) g hEnorm q v st.2)) (𝓝 (t₀, t₀))
      (𝓝 (intrinsicGeodesic (I := I) g hEnorm q v t₀,
        intrinsicGeodesic (I := I) g hEnorm q v t₀)) :=
    ((hcont.comp continuous_fst).continuousAt).prodMk
      ((hcont.comp continuous_snd).continuousAt)
  have h2 := hmap.eventually (maxSliceLocus_pair (I := I) hEnorm hC
    (standardDiagonalInverseBranch (I := I) g hEnorm (intrinsicGeodesic (I := I) g hEnorm q v t₀)))
  obtain ⟨P, Q, hP, hcP, hQ, hcQ, hPQ⟩ := mem_nhds_prod_iff'.1 (h1.and h2)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ((hP.inter hQ).mem_nhds ⟨hcP, hcQ⟩)
  refine ⟨δ, hδ, ?_⟩
  intro s₁ s₂ hs₁ hs₂ hN hCmem t ht
  have hm₁ : s₁ ∈ P ∩ Q := hball (by simpa only [Metric.mem_ball, Real.dist_eq] using hs₁)
  have hm₂ : s₂ ∈ P ∩ Q := hball (by simpa only [Metric.mem_ball, Real.dist_eq] using hs₂)
  obtain ⟨he1, he2⟩ := hPQ (Set.mk_mem_prod hm₁.1 hm₂.2)
  rw [← he1 t]
  exact he2 hN hCmem t ht

private theorem shiftT_mem_of_before_after
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) {q : M} {v : TangentSpace I q}
    {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hbefore : ∀ s : ℝ, 0 ≤ s → s < s₀ →
      intrinsicGeodesic (I := I) g hEnorm q v s ∈ maxSliceLocus I C)
    {s₁ : ℝ} (hs₁ : s₀ < s₁)
    (hafter : ∀ s : ℝ, s₀ ≤ s → s ≤ s₁ → intrinsicGeodesic (I := I) g hEnorm q v s ∈ C) :
    intrinsicGeodesic (I := I) g hEnorm q v s₀ ∈ maxSliceLocus I C := by
  obtain ⟨δ, hδ, hkey⟩ := shiftT_locus_propagation (I := I) g hEnorm hC q v s₀
  set ε : ℝ := min (δ / 2) (s₀ / 2) with hεdef
  set ε' : ℝ := min (δ / 2) ((s₁ - s₀) / 2) with hε'def
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hε'pos : 0 < ε' := lt_min (by linarith) (by linarith)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε'δ : ε' < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεs : ε ≤ s₀ / 2 := min_le_right _ _
  have hε's : ε' ≤ (s₁ - s₀) / 2 := min_le_right _ _
  have hb₁ : |(s₀ - ε) - s₀| < δ := by
    rw [show (s₀ - ε) - s₀ = -ε by ring, abs_neg, abs_of_pos hεpos]
    exact hεδ
  have hb₂ : |(s₀ + ε') - s₀| < δ := by
    rw [show (s₀ + ε') - s₀ = ε' by ring, abs_of_pos hε'pos]
    exact hε'δ
  have hN₁ : intrinsicGeodesic (I := I) g hEnorm q v (s₀ - ε) ∈ maxSliceLocus I C :=
    hbefore _ (by linarith) (by linarith)
  have hC₂ : intrinsicGeodesic (I := I) g hEnorm q v (s₀ + ε') ∈ C :=
    hafter _ (by linarith) (by linarith)
  have hsum : (0 : ℝ) < ε + ε' := by linarith
  have hres := hkey (s₀ - ε) (s₀ + ε') hb₁ hb₂ hN₁ hC₂ (ε' / (ε + ε'))
    ⟨div_pos hε'pos hsum, (div_le_one hsum).2 (by linarith)⟩
  have hval : ε' / (ε + ε') * ((s₀ - ε) - (s₀ + ε')) + (s₀ + ε') = s₀ := by
    field_simp
    ring
  rwa [hval] at hres



theorem hasOrthogonalBoundaryShiftTangent_relBoundary
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hBne : (relBoundary I C).Nonempty)
    (hsupp : HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C))
    (hrauch : HasParallelShiftBound (I := I) g hEnorm)
    (hpar : HasSliceParallelTransport (I := I) g hEnorm C) :
    HasOrthogonalBoundaryShiftTangent (I := I) g hEnorm C (relBoundary I C) := by
  have hBclosed : IsClosed (relBoundary I C) :=
    isClosed_relBoundary (I := I) hEnorm hC hCclosed
  have hproper : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  intro x hx
  have hxN : x ∈ maxSliceLocus I C := by rwa [← diff_relBoundary (I := I) C]
  have hlx : 0 < Metric.infDist x (relBoundary I C) :=
    infDist_relBoundary_pos (I := I) hEnorm hC hCclosed hBne hxN
  set L : ℝ := Metric.infDist x (relBoundary I C) + 1 with hLdef
  have hL : 0 < L := by rw [hLdef]; linarith
  obtain ⟨ρ₂, hρ₂, hrb⟩ := hrauch x L hL
  obtain ⟨r, hr, hcone⟩ := shiftT_exists_uniform_cone_radius (I := I) g hEnorm hC
    (isCompact_closedBall x (L + 1))
  refine ⟨min (min (Metric.infDist x (relBoundary I C) / 2) ρ₂) (min r 1), by positivity, ?_⟩
  intro y hy hxy u w hu hw huw hwT hend h hh0 hhρ
  have hmin1 : min (min (Metric.infDist x (relBoundary I C) / 2) ρ₂) (min r 1)
      ≤ Metric.infDist x (relBoundary I C) / 2 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hmin2 : min (min (Metric.infDist x (relBoundary I C) / 2) ρ₂) (min r 1) ≤ ρ₂ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hmin3 : min (min (Metric.infDist x (relBoundary I C) / 2) ρ₂) (min r 1) ≤ r :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hmin4 : min (min (Metric.infDist x (relBoundary I C) / 2) ρ₂) (min r 1) ≤ 1 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  set l : ℝ := Metric.infDist y (relBoundary I C) with hldef
  have hlpos : 0 < l := (hBclosed.notMem_iff_infDist_pos hBne).1 hy.2
  have hlL : l < L := by
    have h1 : Metric.infDist y (relBoundary I C)
        ≤ Metric.infDist x (relBoundary I C) + dist y x := Metric.infDist_le_infDist_add_dist
    rw [dist_comm] at h1
    have h2 : dist x y < 1 := lt_of_lt_of_le hxy hmin4
    rw [hldef, hLdef]
    linarith
  have hhl : h < l := by
    have h1 : Metric.infDist x (relBoundary I C)
        ≤ Metric.infDist y (relBoundary I C) + dist x y := Metric.infDist_le_infDist_add_dist
    have h2 : dist x y < Metric.infDist x (relBoundary I C) / 2 :=
      lt_of_lt_of_le hxy hmin1
    have h3 : h < Metric.infDist x (relBoundary I C) / 2 := lt_of_lt_of_le hhρ hmin1
    rw [hldef]
    linarith
  rcases hh0.eq_or_lt with hzero | hhpos
  · rw [← hzero, intrinsicGeodesic_zero]
  obtain ⟨ξ, hξ0, hξ⟩ := exists_isParallelPerpUnitField (I := I) g hEnorm u w hw huw hL
  have hlIcc : l ∈ Icc (0 : ℝ) L := ⟨hlpos.le, hlL.le⟩
  have hdistc : ∀ s : ℝ, 0 ≤ s → s < ρ₂ → ∀ t₁ ∈ Icc (0 : ℝ) L, ∀ t₂ ∈ Icc (0 : ℝ) L,
      dist (parallelShift (I := I) g hEnorm y u ξ s t₁)
        (parallelShift (I := I) g hEnorm y u ξ s t₂) ≤ |t₁ - t₂| :=
    fun s hs0 hsρ => hrb y (lt_of_lt_of_le hxy hmin2) u hu ξ hξ s hs0 hsρ
  have hhρ₂ : h < ρ₂ := lt_of_lt_of_le hhρ hmin2
  have hc0 : parallelShift (I := I) g hEnorm y u ξ h 0
      = intrinsicGeodesic (I := I) g hEnorm y w h :=
    parallelShift_zero_time (I := I) g hEnorm y u w ξ hξ0 h
  have hPS : ∀ s t : ℝ, parallelShift (I := I) g hEnorm y u ξ s t
      = intrinsicGeodesic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm y u t) (ξ t) s := fun s t =>
    expMapIntrinsic_smul_eq_intrinsicGeodesic (I := I) g hEnorm _ (ξ t) s
  have hτ0 : intrinsicGeodesic (I := I) g hEnorm y u 0 = y :=
    intrinsicGeodesic_zero (I := I) g hEnorm y u
  have hτfacts : ∀ t : ℝ, 0 ≤ t → t ≤ l →
      dist y (intrinsicGeodesic (I := I) g hEnorm y u t) = t ∧
        Metric.infDist (intrinsicGeodesic (I := I) g hEnorm y u t) (relBoundary I C)
          = l - t := fun t ht0 htl =>
    shiftT_infDist_of_minimizing (I := I) g hEnorm hu hend ht0 htl
  have hτC : ∀ t ∈ Icc (0 : ℝ) l, intrinsicGeodesic (I := I) g hEnorm y u t ∈ C :=
    hC hlpos.le ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm y u).isGeodesicOn _)
      (intrinsicGeodesic_continuous (I := I) g hEnorm y u).continuousOn
      (by rw [hτ0]; exact hy.1) (relBoundary_subset hend)
  have hτN : ∀ t : ℝ, 0 ≤ t → t < l →
      intrinsicGeodesic (I := I) g hEnorm y u t ∈ maxSliceLocus I C := by
    intro t ht0 htl
    rw [← diff_relBoundary (I := I) C]
    refine ⟨hτC t ⟨ht0, htl.le⟩, fun hb => ?_⟩
    have h := (hτfacts t ht0 htl.le).2
    rw [Metric.infDist_zero_of_mem hb] at h
    linarith
  have hξ0T : ξ 0 ∈ sliceTangent I (maxSliceLocus I C)
      (intrinsicGeodesic (I := I) g hEnorm y u 0) := by
    refine shiftT_mem_sliceTangent_congr (S := maxSliceLocus I C) hτ0.symm ?_
    rw [hξ0]
    exact hwT
  have hξT : ∀ t : ℝ, 0 ≤ t → t < l →
      ξ t ∈ sliceTangent I (maxSliceLocus I C)
        (intrinsicGeodesic (I := I) g hEnorm y u t) := by
    intro t ht0 htl
    refine hpar y u ξ t (shiftT_isParallelPerpUnitField_mono hξ (by linarith)) ?_
      hξ0T t ⟨ht0, le_rfl⟩
    exact fun s hs => hτN s hs.1 (lt_of_le_of_lt hs.2 htl)
  have hclN : parallelShift (I := I) g hEnorm y u ξ h l ∉ maxSliceLocus I C := by
    intro hmem
    have hpC : intrinsicGeodesic (I := I) g hEnorm y u l ∈ C := relBoundary_subset hend
    have hyp : dist y (intrinsicGeodesic (I := I) g hEnorm y u l) ≤ l := by
      have h := shiftT_dist_le_radius (I := I) g hEnorm y u hlpos.le
      rwa [hu, Real.sqrt_one, one_mul] at h
    have hpK : intrinsicGeodesic (I := I) g hEnorm y u l ∈ Metric.closedBall x (L + 1) := by
      rw [Metric.mem_closedBall, dist_comm]
      have h2 : dist x (intrinsicGeodesic (I := I) g hEnorm y u l)
          ≤ dist x y + dist y (intrinsicGeodesic (I := I) g hEnorm y u l) := dist_triangle _ _ _
      have h3 : dist x y < 1 := lt_of_lt_of_le hxy hmin4
      linarith
    have hvlen : Real.sqrt (g.inner (intrinsicGeodesic (I := I) g hEnorm y u l)
        (h • ξ l) (h • ξ l)) = h := by
      rw [sqrt_gInner_smul_self (I := I) g _ hh0, hξ.2.2.1 l hlIcc, Real.sqrt_one, mul_one]
    have hmem' : expMapIntrinsic (I := I) g hEnorm
        (intrinsicGeodesic (I := I) g hEnorm y u l) (h • ξ l) ∈ maxSliceLocus I C := by
      rwa [parallelShift_apply] at hmem
    have hstar := hcone _ hpK hpC (h • ξ l)
      (by rw [hvlen]; exact lt_of_lt_of_le hhρ hmin3) hmem'
    have hperp : 0 ≤ g.inner (intrinsicGeodesic (I := I) g hEnorm y u l) (ξ l)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm y u) l) :=
      le_of_eq (hξ.2.2.2 l hlIcc).symm
    have hev := hsupp y hy u hu hend (ξ l) hperp
    have hIoo : Ioo (0 : ℝ) h ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hhpos
    have hcomb : ∀ᶠ z in 𝓝[>] (0 : ℝ),
        (expMapIntrinsic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm y u l) (z • ξ l) ∉ C \ relBoundary I C)
          ∧ z ∈ Ioo (0 : ℝ) h := by
      filter_upwards [hev, hIoo] with z hz1 hz2 using ⟨hz1, hz2⟩
    obtain ⟨s, hs1, hs2⟩ := hcomb.exists
    have hsmall := hstar (s / h) ⟨div_pos hs2.1 hhpos, (div_le_one hhpos).2 hs2.2.le⟩
    rw [smul_smul, div_mul_cancel₀ s (ne_of_gt hhpos)] at hsmall
    rw [diff_relBoundary (I := I) C] at hs1
    exact hs1 hsmall
  set A : Set ℝ := {t : ℝ | t ∈ Icc (0 : ℝ) l ∧ ∃ s ∈ Icc (0 : ℝ) h,
    parallelShift (I := I) g hEnorm y u ξ s t ∈ relBoundary I C} with hAdef
  have hlA : l ∈ A := by
    refine ⟨⟨hlpos.le, le_rfl⟩, 0, ⟨le_rfl, hh0⟩, ?_⟩
    rw [parallelShift_zero]
    exact hend
  have hAne : A.Nonempty := ⟨l, hlA⟩
  have hAbdd : BddBelow A := ⟨0, fun s hs => hs.1.1⟩
  have hAlow : ∀ t ∈ A, l - h ≤ t := by
    rintro t ⟨htIcc, s, hsIcc, hsB⟩
    have hspeed : dist (intrinsicGeodesic (I := I) g hEnorm y u t)
        (parallelShift (I := I) g hEnorm y u ξ s t) ≤ s := by
      rw [hPS s t]
      have h := shiftT_dist_le_radius (I := I) g hEnorm
        (intrinsicGeodesic (I := I) g hEnorm y u t) (ξ t) hsIcc.1
      rwa [hξ.2.2.1 t ⟨htIcc.1, le_trans htIcc.2 hlL.le⟩, Real.sqrt_one, one_mul] at h
    have hle : Metric.infDist (intrinsicGeodesic (I := I) g hEnorm y u t) (relBoundary I C)
        ≤ s := le_trans (Metric.infDist_le_dist_of_mem hsB) hspeed
    rw [(hτfacts t htIcc.1 htIcc.2).2] at hle
    linarith [hsIcc.2]
  set t₀ : ℝ := sInf A with ht₀def
  have ht₀ge : l - h ≤ t₀ := le_csInf hAne hAlow
  have ht₀pos : 0 < t₀ := by linarith
  have ht₀l : t₀ ≤ l := csInf_le hAbdd hlA
  have ht₀L : t₀ ∈ Icc (0 : ℝ) L := ⟨ht₀pos.le, le_trans ht₀l hlL.le⟩
  have hbefore : ∀ t : ℝ, 0 ≤ t → t < t₀ → ∀ s ∈ Icc (0 : ℝ) h,
      parallelShift (I := I) g hEnorm y u ξ s t ∈ maxSliceLocus I C := by
    intro t ht0 htt s hs
    have htl : t < l := lt_of_lt_of_le htt ht₀l
    have hnotA : ¬ ∃ s' ∈ Icc (0 : ℝ) h,
        parallelShift (I := I) g hEnorm y u ξ s' t ∈ relBoundary I C := by
      intro hex
      exact absurd (csInf_le hAbdd (show t ∈ A from ⟨⟨ht0, htl.le⟩, hex⟩)) (not_le.2 htt)
    have hstay : ∀ s' ∈ Icc (0 : ℝ) h,
        intrinsicGeodesic (I := I) g hEnorm
            (intrinsicGeodesic (I := I) g hEnorm y u t) (ξ t) s' ∉ relBoundary I C := by
      intro s' hs' hb
      exact hnotA ⟨s', hs', by rw [hPS s' t]; exact hb⟩
    have h := shiftT_no_escape (I := I) g hEnorm hC hCclosed (hτN t ht0 htl)
      (hξT t ht0 htl) hh0 hstay s hs
    rw [hPS s t]
    exact h
  obtain ⟨s₁, hs₁Icc, hs₁B⟩ : ∃ s ∈ Icc (0 : ℝ) h,
      parallelShift (I := I) g hEnorm y u ξ s t₀ ∈ relBoundary I C := by
    have hgeoeq : (fun s => parallelShift (I := I) g hEnorm y u ξ s t₀)
        = intrinsicGeodesic (I := I) g hEnorm
            (intrinsicGeodesic (I := I) g hEnorm y u t₀) (ξ t₀) := by
      funext s
      exact hPS s t₀
    have hcont : Continuous fun s => parallelShift (I := I) g hEnorm y u ξ s t₀ := by
      rw [hgeoeq]
      exact intrinsicGeodesic_continuous (I := I) g hEnorm _ (ξ t₀)
    have hφcont : Continuous fun s =>
        Metric.infDist (parallelShift (I := I) g hEnorm y u ξ s t₀) (relBoundary I C) :=
      (Metric.continuous_infDist_pt (relBoundary I C)).comp hcont
    obtain ⟨s₁, hs₁mem, hs₁min⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr hh0) hφcont.continuousOn
    refine ⟨s₁, hs₁mem, ?_⟩
    rw [hBclosed.mem_iff_infDist_zero hBne]
    refine le_antisymm ?_ Metric.infDist_nonneg
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨t, htA, htlt⟩ := exists_lt_of_csInf_lt hAne (show t₀ < t₀ + ε by linarith)
    obtain ⟨htIcc, s, hsIcc, hsB⟩ := htA
    have ht₀t : t₀ ≤ t := csInf_le hAbdd ⟨htIcc, s, hsIcc, hsB⟩
    have hd : dist (parallelShift (I := I) g hEnorm y u ξ s t₀)
        (parallelShift (I := I) g hEnorm y u ξ s t) ≤ |t₀ - t| :=
      hdistc s hsIcc.1 (lt_of_le_of_lt hsIcc.2 hhρ₂) t₀ ht₀L t
        ⟨htIcc.1, le_trans htIcc.2 hlL.le⟩
    have h1 : Metric.infDist (parallelShift (I := I) g hEnorm y u ξ s t₀) (relBoundary I C)
        ≤ dist (parallelShift (I := I) g hEnorm y u ξ s t₀)
          (parallelShift (I := I) g hEnorm y u ξ s t) :=
      Metric.infDist_le_dist_of_mem hsB
    have h2 : |t₀ - t| ≤ ε := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have h3 : Metric.infDist (parallelShift (I := I) g hEnorm y u ξ s₁ t₀)
        (relBoundary I C)
        ≤ Metric.infDist (parallelShift (I := I) g hEnorm y u ξ s t₀)
          (relBoundary I C) := hs₁min hsIcc
    linarith
  obtain ⟨tstar, htstarIcc, htstarB⟩ : ∃ t ∈ Icc (0 : ℝ) l,
      parallelShift (I := I) g hEnorm y u ξ h t ∈ relBoundary I C := by
    rcases eq_or_lt_of_le ht₀l with ht₀eq | ht₀lt
    · refine ⟨l, ⟨hlpos.le, le_rfl⟩, ?_⟩
      have hclC : parallelShift (I := I) g hEnorm y u ξ h l ∈ C := by
        have hcl : parallelShift (I := I) g hEnorm y u ξ h l
            ∈ closure (maxSliceLocus I C) := by
          rw [Metric.mem_closure_iff]
          intro ε hε
          have hm0 : (0 : ℝ) ≤ max (l / 2) (l - ε / 2) :=
            le_trans (by linarith) (le_max_left _ _)
          have hmlt : max (l / 2) (l - ε / 2) < t₀ := by
            rw [← ht₀eq]
            exact max_lt (by linarith) (by linarith)
          refine ⟨parallelShift (I := I) g hEnorm y u ξ h (max (l / 2) (l - ε / 2)),
            hbefore _ hm0 hmlt h ⟨hh0, le_rfl⟩, ?_⟩
          have hmle : max (l / 2) (l - ε / 2) ≤ l :=
            max_le (by linarith) (by linarith)
          have hmL : max (l / 2) (l - ε / 2) ∈ Icc (0 : ℝ) L :=
            ⟨hm0, le_trans hmle hlL.le⟩
          have hd := hdistc h hh0 hhρ₂ l hlIcc _ hmL
          have hge : l - ε / 2 ≤ max (l / 2) (l - ε / 2) := le_max_right _ _
          rw [abs_of_nonneg (show (0 : ℝ) ≤ l - max (l / 2) (l - ε / 2) by linarith)] at hd
          linarith
        have h1 : closure (maxSliceLocus I C) ⊆ closure C := closure_mono maxSliceLocus_subset
        rw [hCclosed.closure_eq] at h1
        exact h1 hcl
      exact mem_relBoundary.2 ⟨hclC, hclN⟩
    · refine ⟨t₀, ⟨ht₀pos.le, ht₀l⟩, ?_⟩
      have hCt₀ : ∀ s ∈ Icc (0 : ℝ) h,
          parallelShift (I := I) g hEnorm y u ξ s t₀ ∈ C := by
        intro s hs
        have hcl : parallelShift (I := I) g hEnorm y u ξ s t₀ ∈ closure C := by
          rw [Metric.mem_closure_iff]
          intro ε hε
          have hm0 : (0 : ℝ) ≤ max (t₀ / 2) (t₀ - ε / 2) :=
            le_trans (by linarith) (le_max_left _ _)
          have hmlt : max (t₀ / 2) (t₀ - ε / 2) < t₀ := max_lt (by linarith) (by linarith)
          refine ⟨parallelShift (I := I) g hEnorm y u ξ s (max (t₀ / 2) (t₀ - ε / 2)),
            maxSliceLocus_subset (hbefore _ hm0 hmlt s hs), ?_⟩
          have hmle : max (t₀ / 2) (t₀ - ε / 2) ≤ t₀ :=
            max_le (by linarith) (by linarith)
          have hmL : max (t₀ / 2) (t₀ - ε / 2) ∈ Icc (0 : ℝ) L :=
            ⟨hm0, le_trans hmle ht₀L.2⟩
          have hd := hdistc s hs.1 (lt_of_le_of_lt hs.2 hhρ₂) t₀ ht₀L _ hmL
          have hge : t₀ - ε / 2 ≤ max (t₀ / 2) (t₀ - ε / 2) := le_max_right _ _
          rw [abs_of_nonneg (show (0 : ℝ) ≤ t₀ - max (t₀ / 2) (t₀ - ε / 2) by linarith)] at hd
          linarith
        rwa [hCclosed.closure_eq] at hcl
      set S : Set ℝ := Icc (0 : ℝ) h ∩
        (fun s => parallelShift (I := I) g hEnorm y u ξ s t₀) ⁻¹' (relBoundary I C) with hSdef
      have hScont : Continuous fun s => parallelShift (I := I) g hEnorm y u ξ s t₀ := by
        have hgeoeq : (fun s => parallelShift (I := I) g hEnorm y u ξ s t₀)
            = intrinsicGeodesic (I := I) g hEnorm
                (intrinsicGeodesic (I := I) g hEnorm y u t₀) (ξ t₀) := by
          funext s
          exact hPS s t₀
        rw [hgeoeq]
        exact intrinsicGeodesic_continuous (I := I) g hEnorm _ (ξ t₀)
      have hSclosed : IsClosed S := isClosed_Icc.inter (hBclosed.preimage hScont)
      have hSne : S.Nonempty := ⟨s₁, hs₁Icc, hs₁B⟩
      have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
      set s₀ : ℝ := sInf S with hs₀def
      have hs₀S : s₀ ∈ S := hSclosed.csInf_mem hSne hSbdd
      have hs₀0 : 0 < s₀ := by
        rcases eq_or_lt_of_le hs₀S.1.1 with hz | hz
        · exfalso
          have hb : parallelShift (I := I) g hEnorm y u ξ 0 t₀ ∈ relBoundary I C := by
            rw [hz]
            exact hs₀S.2
          rw [parallelShift_zero] at hb
          exact not_mem_relBoundary_of_mem_maxSliceLocus (hτN t₀ ht₀pos.le ht₀lt) hb
        · exact hz
      have hbeforeS : ∀ s : ℝ, 0 ≤ s → s < s₀ →
          intrinsicGeodesic (I := I) g hEnorm
              (intrinsicGeodesic (I := I) g hEnorm y u t₀) (ξ t₀) s
            ∈ maxSliceLocus I C := by
        intro s hs0 hss
        have hsh : s ≤ h := le_trans hss.le hs₀S.1.2
        have hnotS : s ∉ S := fun hmem => absurd (csInf_le hSbdd hmem) (not_le.2 hss)
        have hnb : parallelShift (I := I) g hEnorm y u ξ s t₀ ∉ relBoundary I C := by
          intro hb
          exact hnotS ⟨⟨hs0, hsh⟩, hb⟩
        rw [← hPS s t₀, ← diff_relBoundary (I := I) C]
        exact ⟨hCt₀ s ⟨hs0, hsh⟩, hnb⟩
      rcases eq_or_lt_of_le hs₀S.1.2 with hs₀h | hs₀h
      · rw [← hs₀h]
        exact hs₀S.2
      · exfalso
        have hafter : ∀ s : ℝ, s₀ ≤ s → s ≤ h →
            intrinsicGeodesic (I := I) g hEnorm
                (intrinsicGeodesic (I := I) g hEnorm y u t₀) (ξ t₀) s ∈ C := by
          intro s hs0 hsh
          rw [← hPS s t₀]
          exact hCt₀ s ⟨le_trans hs₀S.1.1 hs0, hsh⟩
        have hmemN := shiftT_mem_of_before_after (I := I) g hEnorm hC hs₀0 hbeforeS
          hs₀h hafter
        rw [← hPS s₀ t₀] at hmemN
        exact not_mem_relBoundary_of_mem_maxSliceLocus hmemN hs₀S.2
  calc Metric.infDist (intrinsicGeodesic (I := I) g hEnorm y w h) (relBoundary I C)
      = Metric.infDist (parallelShift (I := I) g hEnorm y u ξ h 0) (relBoundary I C) := by
        rw [hc0]
    _ ≤ dist (parallelShift (I := I) g hEnorm y u ξ h 0)
        (parallelShift (I := I) g hEnorm y u ξ h tstar) :=
      Metric.infDist_le_dist_of_mem htstarB
    _ ≤ |(0 : ℝ) - tstar| :=
      hdistc h hh0 hhρ₂ 0 ⟨le_rfl, hL.le⟩ tstar ⟨htstarIcc.1, le_trans htstarIcc.2 hlL.le⟩
    _ = tstar := by rw [zero_sub, abs_neg, abs_of_nonneg htstarIcc.1]
    _ ≤ l := htstarIcc.2



theorem concaveOn_infDist_relBoundary_tangent
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hBne : (relBoundary I C).Nonempty)
    (hsupp : HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C))
    (hrauch : HasParallelShiftBound (I := I) g hEnorm)
    (hpar : HasSliceParallelTransport (I := I) g hEnorm C)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hgeo : Geodesic.IsGeodesicOn (I := I) g γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hmaps : MapsTo γ (Icc a b) C) :
    ConcaveOn ℝ (Icc a b) (fun s => Metric.infDist (γ s) (relBoundary I C)) :=
  concaveOn_infDist_boundary_tangent (I := I) g hEnorm hsec hC
    (isClosed_relBoundary (I := I) hEnorm hC hCclosed) hBne relBoundary_subset
    (diff_relBoundary (I := I) C)
    (hasOrthogonalBoundaryShiftTangent_relBoundary (I := I) g hEnorm hC hCclosed hBne
      hsupp hrauch hpar)
    (hasOpenCore_relBoundary (I := I) g hEnorm hC) hab hgeo hcont hmaps

theorem isTotallyConvex_superlevel_infDist_relBoundary_tangent
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hBne : (relBoundary I C).Nonempty)
    (hsupp : HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C))
    (hrauch : HasParallelShiftBound (I := I) g hEnorm)
    (hpar : HasSliceParallelTransport (I := I) g hEnorm C) (t : ℝ) :
    IsTotallyConvex (I := I) g {z ∈ C | t ≤ Metric.infDist z (relBoundary I C)} :=
  isTotallyConvex_superlevel_infDist_tangent (I := I) g hEnorm hsec hC
    (isClosed_relBoundary (I := I) hEnorm hC hCclosed) hBne relBoundary_subset
    (diff_relBoundary (I := I) C)
    (hasOrthogonalBoundaryShiftTangent_relBoundary (I := I) g hEnorm hC hCclosed hBne
      hsupp hrauch hpar)
    (hasOpenCore_relBoundary (I := I) g hEnorm hC) t



theorem shavingConcavity_of_sec_nonneg
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hpar : ∀ C : Set M, IsTotallyConvex (I := I) g C → IsClosed C →
      HasSliceParallelTransport (I := I) g hEnorm C) :
    ShavingConcavity (I := I) g := fun C hCcomp hCne hconv hBne t =>
  isTotallyConvex_superlevel_infDist_relBoundary_tangent (I := I) g hEnorm hsec
    hconv hCcomp.isClosed hBne
    (hasSupportingHalfSpaces_relBoundary_of_totallyConvex (I := I) g hEnorm hsec hconv
      hCcomp.isClosed ((hconv.isPathConnected g hEnorm hCne).isConnected.isPreconnected))
    (hasParallelShiftBound_of_sec_nonneg (I := I) g hEnorm hsec)
    (hpar C hconv hCcomp.isClosed) t

theorem exists_soul_set_of_sec_nonneg [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hpar : ∀ C : Set M, IsTotallyConvex (I := I) g C → IsClosed C →
      HasSliceParallelTransport (I := I) g hEnorm C) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex (I := I) g S ∧
      relBoundary I S = ∅ ∧ maxSliceDim I S < Module.finrank ℝ E :=
  exists_soul_set (I := I) g hEnorm hsec
    (shavingConcavity_of_sec_nonneg (I := I) g hEnorm hsec hpar) p

end DifferentialGeometry.Geometry.Topology

end
