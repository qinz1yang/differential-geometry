import DifferentialGeometry.Geometry.Comparison.Nonnegative.BoundaryConcavity
import DifferentialGeometry.Geometry.Comparison.Nonnegative.RauchParallel
import DifferentialGeometry.Geometry.Comparison.ConvexBoundarySupport

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
private theorem shift_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem shift_dist_intrinsicGeodesic_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) {s t : ℝ} (hst : s ≤ t) :
    dist (intrinsicGeodesic (I := I) g hEnorm p v s)
        (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ Real.sqrt (g.inner p v v) * (t - s) := by
  have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p v hst
  rw [← shift_toReal_eq_dist (I := I)]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (by linarith))]

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem shift_dist_le_radius
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) {t : ℝ} (ht : 0 ≤ t) :
    dist p (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ Real.sqrt (g.inner p v v) * t := by
  have h := shift_dist_intrinsicGeodesic_le (I := I) g hEnorm p v ht
  rwa [intrinsicGeodesic_zero, sub_zero] at h

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem diff_relBoundary (C : Set M) : C \ relBoundary I C = maxSliceLocus I C := by
  rw [relBoundary, sdiff_sdiff_right_self,
    inter_eq_self_of_subset_right (maxSliceLocus_subset (I := I) (C := C))]

theorem isOpen_maxSliceLocus_of_maxSliceDim
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    (hdim : maxSliceDim I C = Module.finrank ℝ E) :
    IsOpen (maxSliceLocus I C) := by
  have h := isEmbeddedSlice_maxSliceLocus (I := I) hEnorm hC
  rw [hdim] at h
  exact h.isOpen

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem maxSliceDim_eq_finrank_of_interior_nonempty {C : Set M}
    (hC : (interior C).Nonempty) : maxSliceDim I C = Module.finrank ℝ E :=
  le_antisymm (maxSliceDim_le (I := I) C)
    (le_maxSliceDim (I := I)
      ⟨interior C, hC, interior_subset, IsEmbeddedSlice.of_isOpen isOpen_interior⟩)

theorem interior_nonempty_of_maxSliceDim_eq
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCne : C.Nonempty)
    (hdim : maxSliceDim I C = Module.finrank ℝ E) : (interior C).Nonempty := by
  obtain ⟨z, hz⟩ := maxSliceLocus_nonempty (I := I) hCne
  exact ⟨z, ((isOpen_maxSliceLocus_of_maxSliceDim (I := I) hEnorm hC
    hdim).subset_interior_iff).2 maxSliceLocus_subset hz⟩



omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem shift_source_tube
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

private theorem exists_minimizingVec_radius_near
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g) (p : M) :
    ∃ A ∈ 𝓝 p, ∃ r : ℝ, 0 < r ∧ ∀ y ∈ A, ∀ v : TangentSpace I y,
      Real.sqrt (g.inner y v v) < r →
      minimizingVec (I := I) g hEnorm y (expMapIntrinsic (I := I) g hEnorm y v) = v := by
  obtain ⟨A, hA, r, hr, hsrc⟩ := shift_source_tube (standardDiagonalInverseBranch (I := I) g hEnorm p)
  refine ⟨A, hA, r, hr, ?_⟩
  intro y hy v hv
  have hvsrc : (⟨y, v⟩ : TangentBundle I M) ∈ (standardDiagonalInverseBranch (I := I) g hEnorm p).hom.source :=
    hsrc y hy v hv
  have h1 : (standardDiagonalInverseBranch (I := I) g hEnorm p).inv (y, expMapIntrinsic (I := I) g hEnorm y v)
      = (⟨y, v⟩ : TangentBundle I M) :=
    (standardDiagonalInverseBranch (I := I) g hEnorm p).inv_eq_of_exp hvsrc rfl
  have hdist : dist y (expMapIntrinsic (I := I) g hEnorm y v)
      ≤ Real.sqrt (g.inner y v v) := by
    have h := shift_dist_le_radius (I := I) g hEnorm y v (show (0 : ℝ) ≤ 1 by norm_num)
    rwa [mul_one, ← expMapIntrinsic_def] at h
  have hlen : Real.sqrt (g.inner y
      (minimizingVec (I := I) g hEnorm y (expMapIntrinsic (I := I) g hEnorm y v))
      (minimizingVec (I := I) g hEnorm y (expMapIntrinsic (I := I) g hEnorm y v)))
      = dist y (expMapIntrinsic (I := I) g hEnorm y v) := by
    rw [minimizingVec_len, shift_toReal_eq_dist (I := I)]
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

private theorem exists_uniform_cone_radius
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
    obtain ⟨A, hA, r₀, hr₀, hmin⟩ := exists_minimizingVec_radius_near (I := I) g hEnorm c
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
    have h := shift_dist_le_radius (I := I) g hEnorm p v (show (0 : ℝ) ≤ 1 by norm_num)
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



omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem shift_geodesicSegment_eqOn_intrinsic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {gamma : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : Geodesic.IsGeodesicOn (I := I) g gamma (Icc a b))
    (hcont : ContinuousOn gamma (Icc a b)) :
    ∃ (q : M) (v : TangentSpace I q) (r : ℝ),
      EqOn gamma (fun t => intrinsicGeodesic (I := I) g hEnorm q v (t - r)) (Icc a b) := by
  let r : ℝ := (a + b) / 2
  let delta : ℝ → M := fun t => gamma (t + r)
  let q : M := delta 0
  let v : TangentSpace I q := mfderiv 𝓘(ℝ, ℝ) I delta 0 1
  let eta := intrinsicGeodesic (I := I) g hEnorm q v
  have hrleft : a < r := by dsimp [r]; linarith
  have hrright : r < b := by dsimp [r]; linarith
  have hmap : MapsTo (fun t : ℝ => t + r) (Icc (a - r) (b - r)) (Icc a b) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hdcont : ContinuousOn delta (Icc (a - r) (b - r)) :=
    hcont.comp (continuous_id.add continuous_const).continuousOn hmap
  have hdgeo : Geodesic.IsGeodesicOn (I := I) g delta (Ioo (a - r) (b - r)) := by
    have h := Geodesic.isGeodesicOn_comp_affine (I := I) (c := 1) (d := r) hgeo
    intro t ht
    simpa only [one_mul] using h t (by
      change 1 * t + r ∈ Icc a b
      simpa only [one_mul] using hmap (Ioo_subset_Icc_self ht))
  have heq : EqOn delta eta (Ioo (a - r) (b - r)) := by
    apply geo_eqOn_of_initial (I := I) g isOpen_Ioo isPreconnected_Ioo
      (show (0 : ℝ) ∈ Ioo (a - r) (b - r) by constructor <;> linarith)
      hdgeo ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm q v).isGeodesicOn _)
      (hdcont.mono Ioo_subset_Icc_self)
      (intrinsicGeodesic_continuous g hEnorm q v).continuousOn
    · exact (intrinsicGeodesic_zero (I := I) g hEnorm q v).symm
    · exact (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm q v).symm
  have heqClosed : EqOn delta eta (Icc (a - r) (b - r)) := by
    apply heq.of_subset_closure hdcont
      (intrinsicGeodesic_continuous g hEnorm q v).continuousOn Ioo_subset_Icc_self
    rw [closure_Ioo (by linarith : a - r ≠ b - r)]
  refine ⟨q, v, r, ?_⟩
  intro t ht
  have ht' : t - r ∈ Icc (a - r) (b - r) := by constructor <;> linarith [ht.1, ht.2]
  simpa only [delta, sub_add_cancel] using heqClosed ht'

private theorem exists_locus_propagation
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

theorem hasOpenCore_relBoundary
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) :
    HasOpenCore (I := I) g C (relBoundary I C) := by
  intro γ a b _ hgeo hcont hmaps hex t ht
  have hab : a < b := lt_trans ht.1 ht.2
  obtain ⟨q, v, r, heq⟩ :=
    shift_geodesicSegment_eqOn_intrinsic (I := I) g hEnorm hab hgeo hcont
  have hγeq : ∀ y ∈ Icc a b, γ y = intrinsicGeodesic (I := I) g hEnorm q v (y - r) :=
    fun y hy => heq hy
  have hmapsσ : ∀ s : ℝ, s ∈ Icc (a - r) (b - r) →
      intrinsicGeodesic (I := I) g hEnorm q v s ∈ C := by
    intro s hs
    have hmem : s + r ∈ Icc a b := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hC' := hmaps hmem
    rwa [hγeq (s + r) hmem, add_sub_cancel_right] at hC'
  obtain ⟨O, hO, hOeq⟩ := exists_isOpen_inter_eq_maxSliceLocus (I := I) hEnorm hC
  have hUsub : ∀ s : ℝ, s ∈ Icc (a - r) (b - r) →
      intrinsicGeodesic (I := I) g hEnorm q v s ∈ maxSliceLocus I C →
      s ∈ intrinsicGeodesic (I := I) g hEnorm q v ⁻¹' O := by
    intro s _ hsN
    have h : intrinsicGeodesic (I := I) g hEnorm q v s ∈ C ∩ O := by rw [hOeq]; exact hsN
    exact h.2
  set V : Set ℝ := {x : ℝ | ∃ δ : ℝ, 0 < δ ∧
    ∀ z : ℝ, z ∈ Ioo (a - r) (b - r) → |z - x| < δ →
      intrinsicGeodesic (I := I) g hEnorm q v z ∉ maxSliceLocus I C} with hVdef
  have hVopen : IsOpen V := by
    rw [Metric.isOpen_iff]
    intro x hx
    obtain ⟨δ, hδ, hkey⟩ := hx
    refine ⟨δ / 2, by linarith, ?_⟩
    intro x' hx'
    refine ⟨δ / 2, by linarith, fun z hz hzx' => hkey z hz ?_⟩
    have hxx : |x' - x| < δ / 2 := by simpa only [Metric.mem_ball, Real.dist_eq] using hx'
    rw [abs_lt] at hxx hzx' ⊢
    exact ⟨by linarith [hzx'.1, hxx.1], by linarith [hzx'.2, hxx.2]⟩
  have hVmem : ∀ s : ℝ, s ∈ Ioo (a - r) (b - r) →
      intrinsicGeodesic (I := I) g hEnorm q v s ∉ maxSliceLocus I C → s ∈ V := by
    intro s hs hsN
    obtain ⟨δ, hδ, hkey⟩ := exists_locus_propagation (I := I) g hEnorm hC q v s
    refine ⟨min δ (min (s - (a - r)) ((b - r) - s)), lt_min hδ
      (lt_min (by linarith [hs.1]) (by linarith [hs.2])), ?_⟩
    intro z hz hzs hzN
    have hz₁ : |z - s| < δ := lt_of_lt_of_le hzs (min_le_left _ _)
    have hz₂ : |z - s| < s - (a - r) :=
      lt_of_lt_of_le hzs (le_trans (min_le_right _ _) (min_le_left _ _))
    have hz₃ : |z - s| < (b - r) - s :=
      lt_of_lt_of_le hzs (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [abs_lt] at hz₂ hz₃
    have hrefl : |(2 * s - z) - s| < δ := by
      rw [show (2 * s - z) - s = -(z - s) by ring, abs_neg]
      exact hz₁
    have hreflIcc : 2 * s - z ∈ Icc (a - r) (b - r) :=
      ⟨by linarith [hz₃.2], by linarith [hz₂.1]⟩
    have hmid := hkey z (2 * s - z) hz₁ hrefl hzN (hmapsσ _ hreflIcc)
      (1 / 2) ⟨by norm_num, by norm_num⟩
    rw [show (1 / 2 : ℝ) * (z - (2 * s - z)) + (2 * s - z) = s by ring] at hmid
    exact hsN hmid
  have hcover : Ioo (a - r) (b - r) ⊆ (intrinsicGeodesic (I := I) g hEnorm q v ⁻¹' O) ∪ V := by
    intro s hs
    by_cases hsN : intrinsicGeodesic (I := I) g hEnorm q v s ∈ maxSliceLocus I C
    · exact Or.inl (hUsub s (Ioo_subset_Icc_self hs) hsN)
    · exact Or.inr (hVmem s hs hsN)
  have hUne : (Ioo (a - r) (b - r) ∩ (intrinsicGeodesic (I := I) g hEnorm q v ⁻¹' O)).Nonempty := by
    obtain ⟨t₀, ht₀, ht₀B⟩ := hex
    have hs₀N : intrinsicGeodesic (I := I) g hEnorm q v (t₀ - r) ∈ maxSliceLocus I C := by
      have hmem : γ t₀ ∈ maxSliceLocus I C := by
        rw [← diff_relBoundary (I := I) C]
        exact ⟨hmaps ht₀, ht₀B⟩
      rwa [hγeq t₀ ht₀] at hmem
    have hs₀ : t₀ - r ∈ Icc (a - r) (b - r) := ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
    obtain ⟨δ, hδ, hkey⟩ :=
      exists_locus_propagation (I := I) g hEnorm hC q v (t₀ - r)
    set m : ℝ := ((a - r) + (b - r)) / 2 with hm
    have hmIoo : m ∈ Ioo (a - r) (b - r) := ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩
    set η : ℝ := min 1 (δ / (|m - (t₀ - r)| + 1)) with hη
    have hηpos : 0 < η := lt_min one_pos (by positivity)
    have hηle : η ≤ 1 := min_le_left _ _
    have hηbound : |(t₀ - r + η * (m - (t₀ - r))) - (t₀ - r)| < δ := by
      rw [show (t₀ - r + η * (m - (t₀ - r))) - (t₀ - r) = η * (m - (t₀ - r)) by ring,
        abs_mul, abs_of_pos hηpos]
      have hpos : (0 : ℝ) < |m - (t₀ - r)| + 1 := by positivity
      have h1 : η ≤ δ / (|m - (t₀ - r)| + 1) := min_le_right _ _
      have h2 : η * (|m - (t₀ - r)| + 1) ≤ δ := by rw [le_div_iff₀ hpos] at h1; exact h1
      nlinarith [abs_nonneg (m - (t₀ - r)), hηpos]
    have hs₂Icc : t₀ - r + η * (m - (t₀ - r)) ∈ Icc (a - r) (b - r) := by
      constructor
      · nlinarith [hs₀.1, hmIoo.1, hηpos, hηle]
      · nlinarith [hs₀.2, hmIoo.2, hηpos, hηle]
    have hmidN := hkey (t₀ - r) (t₀ - r + η * (m - (t₀ - r)))
      (by simp only [sub_self, abs_zero]; exact hδ) hηbound hs₀N (hmapsσ _ hs₂Icc)
      (1 / 2) ⟨by norm_num, by norm_num⟩
    rw [show (1 / 2 : ℝ) * ((t₀ - r) - (t₀ - r + η * (m - (t₀ - r))))
        + (t₀ - r + η * (m - (t₀ - r))) = t₀ - r + (η / 2) * (m - (t₀ - r)) by ring] at hmidN
    have hmidIoo : t₀ - r + (η / 2) * (m - (t₀ - r)) ∈ Ioo (a - r) (b - r) := by
      constructor
      · nlinarith [hs₀.1, hmIoo.1, hηpos, hηle]
      · nlinarith [hs₀.2, hmIoo.2, hηpos, hηle]
    exact ⟨_, hmidIoo, hUsub _ (Ioo_subset_Icc_self hmidIoo) hmidN⟩
  rw [hγeq t (Ioo_subset_Icc_self ht)]
  intro hmemB
  have htIoo : t - r ∈ Ioo (a - r) (b - r) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htN : intrinsicGeodesic (I := I) g hEnorm q v (t - r) ∉ maxSliceLocus I C :=
    (mem_relBoundary.1 hmemB).2
  obtain ⟨s, hs, hsU, hsV⟩ := isPreconnected_Ioo (intrinsicGeodesic (I := I) g hEnorm q v ⁻¹' O)
    V (hO.preimage (intrinsicGeodesic_continuous (I := I) g hEnorm q v)) hVopen hcover hUne
    ⟨t - r, htIoo, hVmem _ htIoo htN⟩
  obtain ⟨δ, _, hkey⟩ := hsV
  exact hkey s hs (by simp only [sub_self, abs_zero]; assumption)
    (by rw [← hOeq]; exact ⟨hmapsσ s (Ioo_subset_Icc_self hs), hsU⟩)



theorem hasOrthogonalBoundaryShift_relBoundary
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hdim : maxSliceDim I C = Module.finrank ℝ E)
    (hBne : (relBoundary I C).Nonempty)
    (hsupp : HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C))
    (hrauch : HasParallelShiftBound (I := I) g hEnorm) :
    HasOrthogonalBoundaryShift (I := I) g hEnorm C (relBoundary I C) := by
  have hNopen : IsOpen (maxSliceLocus I C) :=
    isOpen_maxSliceLocus_of_maxSliceDim (I := I) hEnorm hC hdim
  have hBclosed : IsClosed (relBoundary I C) := isClosed_relBoundary (I := I) hEnorm hC hCclosed
  have hproper : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  intro x hx
  have hxN : x ∈ maxSliceLocus I C := by rwa [← diff_relBoundary (I := I) C]
  obtain ⟨ρ₁, hρ₁, hball₁⟩ := Metric.isOpen_iff.1 hNopen x hxN
  set L : ℝ := Metric.infDist x (relBoundary I C) + 1 with hLdef
  have hL : 0 < L := by
    have h := Metric.infDist_nonneg (x := x) (s := relBoundary I C)
    rw [hLdef]; linarith
  obtain ⟨ρ₂, hρ₂, hrb⟩ := hrauch x L hL
  obtain ⟨r, hr, hcone⟩ := exists_uniform_cone_radius (I := I) g hEnorm hC
    (isCompact_closedBall x (L + 1))
  refine ⟨min (min (ρ₁ / 2) ρ₂) (min r 1), by positivity, ?_⟩
  intro y hy hxy u w hu hw huw hend h hh0 hhρ
  have hmin1 : min (min (ρ₁ / 2) ρ₂) (min r 1) ≤ ρ₁ / 2 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hmin2 : min (min (ρ₁ / 2) ρ₂) (min r 1) ≤ ρ₂ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hmin3 : min (min (ρ₁ / 2) ρ₂) (min r 1) ≤ r :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hmin4 : min (min (ρ₁ / 2) ρ₂) (min r 1) ≤ 1 :=
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
  rcases hh0.eq_or_lt with hzero | hhpos
  · rw [← hzero, intrinsicGeodesic_zero]
  obtain ⟨ξ, hξ0, hξ⟩ := exists_isParallelPerpUnitField (I := I) g hEnorm u w hw huw hL
  have hlIcc : l ∈ Icc (0 : ℝ) L := ⟨hlpos.le, hlL.le⟩
  have hdistc : ∀ t₁ ∈ Icc (0 : ℝ) L, ∀ t₂ ∈ Icc (0 : ℝ) L,
      dist (parallelShift (I := I) g hEnorm y u ξ h t₁)
        (parallelShift (I := I) g hEnorm y u ξ h t₂) ≤ |t₁ - t₂| :=
    hrb y (lt_of_lt_of_le hxy hmin2) u hu ξ hξ h hh0 (lt_of_lt_of_le hhρ hmin2)
  have hc0 : parallelShift (I := I) g hEnorm y u ξ h 0
      = intrinsicGeodesic (I := I) g hEnorm y w h :=
    parallelShift_zero_time (I := I) g hEnorm y u w ξ hξ0 h
  have hc0N : parallelShift (I := I) g hEnorm y u ξ h 0 ∈ maxSliceLocus I C := by
    refine hball₁ ?_
    rw [Metric.mem_ball, dist_comm]
    have h1 : dist y (parallelShift (I := I) g hEnorm y u ξ h 0) ≤ h := by
      rw [hc0]
      have h := shift_dist_le_radius (I := I) g hEnorm y w hh0
      rwa [hw, Real.sqrt_one, one_mul] at h
    have h2 : dist x (parallelShift (I := I) g hEnorm y u ξ h 0)
        ≤ dist x y + dist y (parallelShift (I := I) g hEnorm y u ξ h 0) := dist_triangle _ _ _
    have h3 : dist x y < ρ₁ / 2 := lt_of_lt_of_le hxy hmin1
    have h4 : h < ρ₁ / 2 := lt_of_lt_of_le hhρ hmin1
    linarith
  have hclN : parallelShift (I := I) g hEnorm y u ξ h l ∉ maxSliceLocus I C := by
    intro hmem
    have hpC : intrinsicGeodesic (I := I) g hEnorm y u l ∈ C := relBoundary_subset hend
    have hyp : dist y (intrinsicGeodesic (I := I) g hEnorm y u l) ≤ l := by
      have h := shift_dist_le_radius (I := I) g hEnorm y u hlpos.le
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
    have hsmall := hstar (s / h) ⟨div_pos hs2.1 hhpos,
      (div_le_one hhpos).2 hs2.2.le⟩
    rw [smul_smul, div_mul_cancel₀ s (ne_of_gt hhpos)] at hsmall
    rw [diff_relBoundary (I := I) C] at hs1
    exact hs1 hsmall
  have hAne : {t : ℝ | t ∈ Icc (0 : ℝ) l ∧
      parallelShift (I := I) g hEnorm y u ξ h t ∉ maxSliceLocus I C}.Nonempty :=
    ⟨l, ⟨hlpos.le, le_rfl⟩, hclN⟩
  have hAbdd : BddBelow {t : ℝ | t ∈ Icc (0 : ℝ) l ∧
      parallelShift (I := I) g hEnorm y u ξ h t ∉ maxSliceLocus I C} :=
    ⟨0, fun s hs => hs.1.1⟩
  set t₀ : ℝ := sInf {t : ℝ | t ∈ Icc (0 : ℝ) l ∧
    parallelShift (I := I) g hEnorm y u ξ h t ∉ maxSliceLocus I C} with ht₀def
  have ht₀cl : t₀ ∈ closure {t : ℝ | t ∈ Icc (0 : ℝ) l ∧
      parallelShift (I := I) g hEnorm y u ξ h t ∉ maxSliceLocus I C} :=
    csInf_mem_closure hAne hAbdd
  have ht₀Icc : t₀ ∈ Icc (0 : ℝ) l := by
    have h := closure_mono
      (show {t : ℝ | t ∈ Icc (0 : ℝ) l ∧
        parallelShift (I := I) g hEnorm y u ξ h t ∉ maxSliceLocus I C} ⊆ Icc (0 : ℝ) l
        from fun s hs => hs.1) ht₀cl
    rwa [isClosed_Icc.closure_eq] at h
  have ht₀L : t₀ ∈ Icc (0 : ℝ) L := ⟨ht₀Icc.1, le_trans ht₀Icc.2 hlL.le⟩
  have ht₀N : parallelShift (I := I) g hEnorm y u ξ h t₀ ∉ maxSliceLocus I C := by
    intro hmem
    obtain ⟨ε, hε, hballε⟩ := Metric.isOpen_iff.1 hNopen _ hmem
    obtain ⟨s, hsA, hsd⟩ := Metric.mem_closure_iff.1 ht₀cl ε hε
    refine hsA.2 (hballε ?_)
    rw [Metric.mem_ball, dist_comm]
    have hsL : s ∈ Icc (0 : ℝ) L := ⟨hsA.1.1, le_trans hsA.1.2 hlL.le⟩
    have hle := hdistc t₀ ht₀L s hsL
    rw [← Real.dist_eq] at hle
    linarith
  have ht₀pos : 0 < t₀ :=
    lt_of_le_of_ne ht₀Icc.1 (by intro h0; exact ht₀N (by rw [← h0]; exact hc0N))
  have hbefore : ∀ s : ℝ, 0 ≤ s → s < t₀ →
      parallelShift (I := I) g hEnorm y u ξ h s ∈ maxSliceLocus I C := by
    intro s hs0 hst
    by_contra hn
    exact absurd (csInf_le hAbdd
      (show s ∈ {t : ℝ | t ∈ Icc (0 : ℝ) l ∧
        parallelShift (I := I) g hEnorm y u ξ h t ∉ maxSliceLocus I C}
        from ⟨⟨hs0, le_trans hst.le ht₀Icc.2⟩, hn⟩)) (not_le.2 hst)
  have hct₀cl : parallelShift (I := I) g hEnorm y u ξ h t₀ ∈ closure (maxSliceLocus I C) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hs0 : (0 : ℝ) ≤ max (t₀ / 2) (t₀ - ε / 2) := le_trans (by linarith) (le_max_left _ _)
    have hslt : max (t₀ / 2) (t₀ - ε / 2) < t₀ := max_lt (by linarith) (by linarith)
    refine ⟨parallelShift (I := I) g hEnorm y u ξ h (max (t₀ / 2) (t₀ - ε / 2)),
      hbefore _ hs0 hslt, ?_⟩
    have hsL : max (t₀ / 2) (t₀ - ε / 2) ∈ Icc (0 : ℝ) L := ⟨hs0, by linarith [ht₀L.2]⟩
    have hle := hdistc t₀ ht₀L _ hsL
    have hge : t₀ - ε / 2 ≤ max (t₀ / 2) (t₀ - ε / 2) := le_max_right _ _
    rw [abs_of_nonneg (by linarith)] at hle
    linarith
  have hct₀C : parallelShift (I := I) g hEnorm y u ξ h t₀ ∈ C := by
    have h1 : closure (maxSliceLocus I C) ⊆ closure C := closure_mono maxSliceLocus_subset
    rw [hCclosed.closure_eq] at h1
    exact h1 hct₀cl
  have hct₀B : parallelShift (I := I) g hEnorm y u ξ h t₀ ∈ relBoundary I C :=
    mem_relBoundary.2 ⟨hct₀C, ht₀N⟩
  calc Metric.infDist (intrinsicGeodesic (I := I) g hEnorm y w h) (relBoundary I C)
      = Metric.infDist (parallelShift (I := I) g hEnorm y u ξ h 0) (relBoundary I C) := by
        rw [hc0]
    _ ≤ dist (parallelShift (I := I) g hEnorm y u ξ h 0)
        (parallelShift (I := I) g hEnorm y u ξ h t₀) :=
      Metric.infDist_le_dist_of_mem hct₀B
    _ ≤ |(0 : ℝ) - t₀| := hdistc 0 ⟨le_rfl, hL.le⟩ t₀ ht₀L
    _ = t₀ := by rw [zero_sub, abs_neg, abs_of_nonneg ht₀pos.le]
    _ ≤ l := ht₀Icc.2



theorem concaveOn_infDist_relBoundary
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hdim : maxSliceDim I C = Module.finrank ℝ E)
    (hBne : (relBoundary I C).Nonempty)
    (hsupp : HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C))
    (hrauch : HasParallelShiftBound (I := I) g hEnorm)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hgeo : Geodesic.IsGeodesicOn (I := I) g γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hmaps : MapsTo γ (Icc a b) C) :
    ConcaveOn ℝ (Icc a b) (fun s => Metric.infDist (γ s) (relBoundary I C)) :=
  concaveOn_infDist_boundary (I := I) g hEnorm hsec hC
    (isClosed_relBoundary (I := I) hEnorm hC hCclosed) hBne relBoundary_subset
    (hasOrthogonalBoundaryShift_relBoundary (I := I) g hEnorm hC hCclosed hdim hBne hsupp hrauch)
    (hasOpenCore_relBoundary (I := I) g hEnorm hC) hab hgeo hcont hmaps

theorem isTotallyConvex_superlevel_infDist_relBoundary
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hdim : maxSliceDim I C = Module.finrank ℝ E)
    (hBne : (relBoundary I C).Nonempty)
    (hsupp : HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C))
    (hrauch : HasParallelShiftBound (I := I) g hEnorm) (t : ℝ) :
    IsTotallyConvex (I := I) g
      {z ∈ C | t ≤ Metric.infDist z (relBoundary I C)} :=
  isTotallyConvex_superlevel_infDist (I := I) g hEnorm hsec hC
    (isClosed_relBoundary (I := I) hEnorm hC hCclosed) hBne relBoundary_subset
    (hasOrthogonalBoundaryShift_relBoundary (I := I) g hEnorm hC hCclosed hdim hBne hsupp hrauch)
    (hasOpenCore_relBoundary (I := I) g hEnorm hC) t

end DifferentialGeometry.Geometry.Topology

end
