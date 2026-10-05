import DifferentialGeometry.Geometry.Comparison.Volume.PolarIntegration
import DifferentialGeometry.Geometry.Exponential.Inverse.Branch

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
abbrev gUnitTangentSphere (g : SmoothRiemannianMetric I M) (x : M) :=
  {u : TangentSpace I x // g.inner x u u = 1}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def cutRadiusSet [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (u : gUnitTangentSphere (I := I) g x) : Set ℝ≥0∞ :=
  {a | ∃ r : ℝ, 0 ≤ r ∧ a = ENNReal.ofReal r ∧
    r • (u : TangentSpace I x) ∈ SegmentDom (I := I) g hEnorm x}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def cutTime [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (u : gUnitTangentSphere (I := I) g x) : ℝ≥0∞ :=
  sSup (cutRadiusSet (I := I) g hEnorm x u)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem expMapIntrinsic_eq_of_left_mem_segInt [ConnectedSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    {v w : TangentSpace I x}
    (hv : v ∈ SegmentInt (I := I) g hEnorm x)
    (hwD : w ∈ SegmentDom (I := I) g hEnorm x)
    (heq : expMapIntrinsic (I := I) g hEnorm x v =
      expMapIntrinsic (I := I) g hEnorm x w) :
    v = w := by
  classical
  have hvD : v ∈ SegmentDom (I := I) g hEnorm x :=
    segmentInt_subset (I := I) g hEnorm x hv
  let L : ℝ := Real.sqrt (g.inner x v v)
  have hlen : Real.sqrt (g.inner x w w) = L := by
    calc
      Real.sqrt (g.inner x w w) =
          (riemannianEDist I x
            (expMapIntrinsic (I := I) g hEnorm x w)).toReal :=
        (mem_segmentDom (I := I)).mp hwD
      _ = (riemannianEDist I x
            (expMapIntrinsic (I := I) g hEnorm x v)).toReal := by
        rw [heq]
      _ = L := ((mem_segmentDom (I := I)).mp hvD).symm
  by_cases hv0 : v = 0
  · subst v
    have hL0 : L = 0 := by
      simp only [L, map_zero, Real.sqrt_zero]
    have hwlen0 : Real.sqrt (g.inner x w w) = 0 := hlen.trans hL0
    have hw0 : w = 0 := by
      by_contra hne
      have hpos : 0 < Real.sqrt (g.inner x w w) :=
        Real.sqrt_pos.mpr (g.pos x w hne)
      linarith
    exact hw0.symm
  have hw0 : w ≠ 0 := by
    intro hwz
    subst w
    have hwlen0 : Real.sqrt (g.inner x (0 : TangentSpace I x) 0) = 0 := by
      simp
    have hL0 : L = 0 := hlen.symm.trans hwlen0
    have hLpos : 0 < L := Real.sqrt_pos.mpr (g.pos x v hv0)
    linarith
  have hLpos : 0 < L := Real.sqrt_pos.mpr (g.pos x v hv0)
  have hLne : L ≠ 0 := hLpos.ne'
  let u : TangentSpace I x := L⁻¹ • v
  let z : TangentSpace I x := L⁻¹ • w
  have hvinner : g.inner x v v = L ^ 2 := by
    have hsq := Real.sq_sqrt (gInner_self_nonneg (I := I) g x v)
    simpa only [L] using hsq.symm
  have hwinner : g.inner x w w = L ^ 2 := by
    have hsq := Real.sq_sqrt (gInner_self_nonneg (I := I) g x w)
    rw [hlen] at hsq
    exact hsq.symm
  have hu_unit : g.inner x u u = 1 := by
    dsimp only [u]
    rw [gInner_smul_self (I := I) g x, hvinner]
    field_simp [hLne]
  have hz_unit : g.inner x z z = 1 := by
    dsimp only [z]
    rw [gInner_smul_self (I := I) g x, hwinner]
    field_simp [hLne]
  have hLu : L • u = v := by
    dsimp only [u]
    rw [smul_smul]
    field_simp [hLne]
    simp
  have hLz : L • z = w := by
    dsimp only [z]
    rw [smul_smul]
    field_simp [hLne]
    simp
  obtain ⟨c, hc, hcv⟩ := hv
  have hc0 : 0 < c := one_pos.trans hc
  let ell : ℝ := (c - 1) * L
  have hell : 0 < ell := mul_pos (sub_pos.mpr hc) hLpos
  have hLell : L + ell = c * L := by
    dsimp only [ell]
    ring
  let γv : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x u
  let γw : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x z
  have hγv_geo : IsGeodesic (I := I) g γv :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm x u
  have hγw_geo : IsGeodesic (I := I) g γw :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm x z
  have hγv_cont : Continuous γv :=
    intrinsicGeodesic_continuous (I := I) g hEnorm x u
  have hγw_cont : Continuous γw :=
    intrinsicGeodesic_continuous (I := I) g hEnorm x z
  have hγv_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γv :=
    isGeodesic_contMDiff (I := I) g hγv_geo hγv_cont
  have hγw_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γw :=
    isGeodesic_contMDiff (I := I) g hγw_geo hγw_cont
  have hγv_unit (t : ℝ) :
      g.inner (γv t) (mfderiv 𝓘(ℝ, ℝ) I γv t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γv t 1) = 1 := by
    simpa only [γv, hu_unit] using
      (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x u t)
  have hγw_unit (t : ℝ) :
      g.inner (γw t) (mfderiv 𝓘(ℝ, ℝ) I γw t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γw t 1) = 1 := by
    simpa only [γw, hz_unit] using
      (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x z t)
  have hγvL : γv L = expMapIntrinsic (I := I) g hEnorm x v := by
    calc
      γv L = intrinsicGeodesic (I := I) g hEnorm x (L • u) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm x u L).symm
      _ = expMapIntrinsic (I := I) g hEnorm x v := by
        rw [hLu]
        rfl
  have hγwL : γw L = expMapIntrinsic (I := I) g hEnorm x w := by
    calc
      γw L = intrinsicGeodesic (I := I) g hEnorm x (L • z) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm x z L).symm
      _ = expMapIntrinsic (I := I) g hEnorm x w := by
        rw [hLz]
        rfl
  let a : TangentSpace I (γv L) := mfderiv 𝓘(ℝ, ℝ) I γv L (1 : ℝ)
  let σ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm (γv L) a
  have hσ_geo : IsGeodesic (I := I) g σ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm (γv L) a
  have hσ_cont : Continuous σ :=
    intrinsicGeodesic_continuous (I := I) g hEnorm (γv L) a
  have hσ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ σ :=
    isGeodesic_contMDiff (I := I) g hσ_geo hσ_cont
  have ha_unit : g.inner (γv L) a a = 1 := by
    convert hγv_unit L using 1
  have hσ_unit (t : ℝ) :
      g.inner (σ t) (mfderiv 𝓘(ℝ, ℝ) I σ t 1)
        (mfderiv 𝓘(ℝ, ℝ) I σ t 1) = 1 := by
    simpa only [σ, ha_unit] using
      (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm (γv L) a t)
  have hcontv : (fun s => γv (s + L)) = σ := by
    simpa only [γv, a, σ] using
      (intrinsicGeodesic_continuation (I := I) g hEnorm x u L)
  have hcvscale : (c * L) • u = c • v := by
    rw [mul_smul, hLu]
  have hσell : σ ell = expMapIntrinsic (I := I) g hEnorm x (c • v) := by
    calc
      σ ell = γv (ell + L) := by rw [← congrFun hcontv ell]
      _ = γv (c * L) := by rw [add_comm ell L, hLell]
      _ = intrinsicGeodesic (I := I) g hEnorm x ((c * L) • u) 1 :=
        (intrinsicGeodesic_smul (I := I) g hEnorm x u (c * L)).symm
      _ = expMapIntrinsic (I := I) g hEnorm x (c • v) := by
        rw [hcvscale]
        rfl
  have hdistc : riemannianEDist I x
      (expMapIntrinsic (I := I) g hEnorm x (c • v)) =
      ENNReal.ofReal (c * L) := by
    have hreal : c * L = (riemannianEDist I x
        (expMapIntrinsic (I := I) g hEnorm x (c • v))).toReal := by
      calc
        c * L = Real.sqrt (g.inner x (c • v) (c • v)) := by
          rw [sqrt_gInner_smul_self (I := I) g x hc0.le v]
        _ = (riemannianEDist I x
            (expMapIntrinsic (I := I) g hEnorm x (c • v))).toReal :=
          (mem_segmentDom (I := I)).mp hcv
    rw [← ENNReal.ofReal_toReal
      (riemannianEDist_ne_top (I := I) x
        (expMapIntrinsic (I := I) g hEnorm x (c • v)))]
    congr 1
    exact hreal.symm
  have hγw0 : γw 0 = x := intrinsicGeodesic_zero (I := I) g hEnorm x z
  have hσ0 : σ 0 = γv L :=
    intrinsicGeodesic_zero (I := I) g hEnorm (γv L) a
  have hjunc : γw L = σ 0 := by
    rw [hγwL, hσ0, hγvL, ← heq]
  have hmin : riemannianEDist I (γw 0) (σ ell) =
      ENNReal.ofReal (L + ell) := by
    rw [hγw0, hσell, hdistc, hLell]
  have hmatch : mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℝ) I σ 0 (1 : ℝ) :=
    broken_minimizer_velocity_match (I := I) g hEnorm hLpos hell
      (hγw_geo.isGeodesicOn (Icc 0 L))
      (hσ_geo.isGeodesicOn (Icc 0 ell)) hγw_smooth hσ_smooth
      (fun t _ => hγw_unit t) (fun t _ => hσ_unit t) hjunc hmin
  have hσvel : (mfderiv 𝓘(ℝ, ℝ) I σ 0 (1 : ℝ) : E) = (a : E) := by
    simpa only [σ] using
      (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm (γv L) a)
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, ℝ) I γv L (1 : ℝ) : E) := by
    rw [hmatch, hσvel]
  have hcontw := intrinsicGeodesic_continuation (I := I) g hEnorm x z L
  have hfoot : γw L = γv L := hγwL.trans (heq.symm.trans hγvL.symm)
  have hcontw' : (fun s => γw (s + L)) = σ := by
    calc
      (fun s => γw (s + L)) = intrinsicGeodesic (I := I) g hEnorm (γw L)
          (mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ)) := by
        simpa only [γw] using hcontw
      _ = σ := by
        rw [hfoot]
        change intrinsicGeodesic (I := I) g hEnorm (γv L)
            (mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ)) =
          intrinsicGeodesic (I := I) g hEnorm (γv L) a
        rw [show (mfderiv 𝓘(ℝ, ℝ) I γw L (1 : ℝ) :
              TangentSpace I (γv L)) = a by
          exact hvel]
  have hshift : (fun s => γw (s + L)) = fun s => γv (s + L) :=
    hcontw'.trans hcontv.symm
  have hcurves : γw = γv := by
    funext t
    have ht := congrFun hshift (t - L)
    simpa only [sub_add_cancel] using ht
  have huz : (z : E) = (u : E) := by
    have hderiv := congrArg
      (fun γ : ℝ → M => (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E)) hcurves
    have hγw0' : (mfderiv 𝓘(ℝ, ℝ) I γw 0 (1 : ℝ) : E) = (z : E) := by
      change (mfderiv 𝓘(ℝ, ℝ) I
        (intrinsicGeodesic (I := I) g hEnorm x z) 0 (1 : ℝ) : E) = (z : E)
      exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x z
    have hγv0 : (mfderiv 𝓘(ℝ, ℝ) I γv 0 (1 : ℝ) : E) = (u : E) := by
      change (mfderiv 𝓘(ℝ, ℝ) I
        (intrinsicGeodesic (I := I) g hEnorm x u) 0 (1 : ℝ) : E) = (u : E)
      exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x u
    exact hγw0'.symm.trans (hderiv.trans hγv0)
  calc
    v = L • u := hLu.symm
    _ = L • z := congrArg (fun y : E => L • y) huz.symm
    _ = w := hLz

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem exists_isOpen_subset_segDom_of_mem_segInt [ConnectedSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    {v : TangentSpace I x} (hv : v ∈ SegmentInt (I := I) g hEnorm x) :
    ∃ U : Set E, IsOpen U ∧ (v : E) ∈ U ∧
      ∀ w : E, w ∈ U →
        (show TangentSpace I x from w) ∈ SegmentDom (I := I) g hEnorm x := by
  classical
  let L : TangentSpace I x ≃L[ℝ] E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) x
  let φ : E → E := fun w => L (show TangentSpace I x from w)
  let F : E → M := fun w =>
    expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from w)
  have hφ_cont : Continuous φ := by
    dsimp only [φ]
    exact L.continuous.comp (by with_unfolding_all exact continuous_id)
  have hF_cont : Continuous F := by
    dsimp only [F]
    exact (expMapIntrinsic_continuous (I := I) g hEnorm x).comp
      (by with_unfolding_all exact continuous_id)
  have hv_no_conj : ¬ IsConjVec (I := I) g hEnorm x (L v) := by
    simpa only [L, tangentSpaceModelContinuousLinearEquiv_apply] using
      segmentInt_no_conj (I := I) g hEnorm hv
  obtain ⟨B, hv_source⟩ :=
    branch_of_not_conj (I := I) g hEnorm hv_no_conj
  let source : Set E := φ ⁻¹' B.hom.source
  have hsource_open : IsOpen source := B.hom.open_source.preimage hφ_cont
  have hv_source' : (v : E) ∈ source := by
    change φ (v : E) ∈ B.hom.source
    change L v ∈ B.hom.source
    exact hv_source
  let R : ℝ := Real.sqrt (g.inner x v v) + 1
  let K : Set E :=
    ({w : E | (show TangentSpace I x from w) ∈ SegmentDom (I := I) g hEnorm x} ∩
      closedGBall (I := I) g x R) ∩ sourceᶜ
  have hseg_closed : IsClosed
      {w : E | (show TangentSpace I x from w) ∈ SegmentDom (I := I) g hEnorm x} :=
    (isClosed_segmentDom (I := I) g hEnorm x).preimage
      (by with_unfolding_all exact continuous_id)
  have hK_compact : IsCompact K := by
    refine (isCompact_closedGBall (I := I) g x R).of_isClosed_subset
      ((hseg_closed.inter (isClosed_closedGBall (I := I) g x R)).inter
        hsource_open.isClosed_compl) ?_
    intro w hw
    exact hw.1.2
  have hFK_closed : IsClosed (F '' K) := (hK_compact.image hF_cont).isClosed
  have hv_not_image : F (v : E) ∉ F '' K := by
    rintro ⟨w, hwK, hwF⟩
    have hvw : v = (show TangentSpace I x from w) :=
      expMapIntrinsic_eq_of_left_mem_segInt (I := I) g hEnorm x hv hwK.1.1 (by
        simpa only [F] using hwF.symm)
    apply hwK.2
    have hvwE : (v : E) = w := congrArg (fun z : TangentSpace I x => (z : E)) hvw
    exact hvwE ▸ hv_source'
  have hdist_cont : Continuous (fun q : M => (riemannianEDist I x q).toReal) := by
    have hbase : Continuous (fun q : M => riemannianEDist I q x) :=
      continuous_riemannianEDist_to (I := I) x
    have hedist : Continuous (fun q : M => riemannianEDist I x q) :=
      hbase.congr fun q => Manifold.riemannianEDist_comm
    exact ENNReal.continuousOn_toReal.comp_continuous hedist
      (fun q => riemannianEDist_ne_top (I := I) x q)
  let target : Set M :=
    (B.hom.target ∩ (F '' K)ᶜ) ∩
      {q : M | (riemannianEDist I x q).toReal < R}
  have htarget_open : IsOpen target := by
    exact (B.hom.open_target.inter hFK_closed.isOpen_compl).inter
      (isOpen_lt hdist_cont continuous_const)
  have hvD : v ∈ SegmentDom (I := I) g hEnorm x :=
    segmentInt_subset (I := I) g hEnorm x hv
  have hFv_target : F (v : E) ∈ target := by
    refine ⟨⟨?_, hv_not_image⟩, ?_⟩
    · have hmap : B.hom (L v) ∈ B.hom.target := B.hom.map_source hv_source
      have heq : F (v : E) = B.hom (L v) := by
        calc
          F (v : E) = expMapIntrinsic (I := I) g hEnorm x v := rfl
          _ = expMapIntrinsic (I := I) g hEnorm x (L.symm (L v)) := by
            rw [L.symm_apply_apply]
          _ = B.hom (L v) := B.hom_eq hv_source
      exact heq.symm ▸ hmap
    · calc
        (riemannianEDist I x (F (v : E))).toReal =
            Real.sqrt (g.inner x v v) := by
          simpa only [F] using ((mem_segmentDom (I := I)).mp hvD).symm
        _ < R := by simp only [R]; linarith
  let U : Set E := source ∩ F ⁻¹' target
  have hU_open : IsOpen U := hsource_open.inter (htarget_open.preimage hF_cont)
  have hvU : (v : E) ∈ U := ⟨hv_source', hFv_target⟩
  refine ⟨U, hU_open, hvU, ?_⟩
  intro w hwU
  obtain ⟨m, hm_exp, hm_len⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm x (F w)
  have hmD : m ∈ SegmentDom (I := I) g hEnorm x :=
    (mem_segmentDom (I := I)).mpr (by rw [hm_exp]; exact hm_len)
  have hm_ball : (m : E) ∈ closedGBall (I := I) g x R := by
    change Real.sqrt (g.inner x m m) ≤ R
    rw [hm_len]
    exact le_of_lt hwU.2.2
  have hm_source : (m : E) ∈ source := by
    by_contra hm_not_source
    have hmK : (m : E) ∈ K := ⟨⟨hmD, hm_ball⟩, hm_not_source⟩
    exact hwU.2.1.2 ⟨(m : E), hmK, by simpa only [F] using hm_exp⟩
  have hcoord : φ w = φ (m : E) := by
    have hwB : φ w ∈ B.hom.source := hwU.1
    have hmB : φ (m : E) ∈ B.hom.source := hm_source
    have hw_left : B.inv (F w) = φ w := by
      calc
        B.inv (F w) = B.inv (expMapIntrinsic (I := I) g hEnorm x
            (L.symm (φ w))) := by
          congr 2
        _ = φ w := B.left_inv hwB
    have hm_left : B.inv (expMapIntrinsic (I := I) g hEnorm x m) =
        φ (m : E) := by
      calc
        B.inv (expMapIntrinsic (I := I) g hEnorm x m) =
            B.inv (expMapIntrinsic (I := I) g hEnorm x
              (L.symm (φ (m : E)))) := by
          congr 2
        _ = φ (m : E) := B.left_inv hmB
    exact hw_left.symm.trans ((congrArg B.inv hm_exp.symm).trans hm_left)
  have hwm : (show TangentSpace I x from w) = m := by
    apply L.injective
    simpa only [φ] using hcoord
  simpa only [hwm] using hmD

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
@[simp] theorem gUnitTangentSphere_inner
    (g : SmoothRiemannianMetric I M) (x : M)
    (u : gUnitTangentSphere (I := I) g x) :
    g.inner x (u : TangentSpace I x) u = 1 :=
  u.property

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem ofReal_le_cutTime_of_smul_mem_segmentDom
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (u : gUnitTangentSphere (I := I) g x) {r : ℝ} (hr : 0 ≤ r)
    (hseg : r • (u : TangentSpace I x) ∈ SegmentDom (I := I) g hEnorm x) :
    ENNReal.ofReal r ≤ cutTime (I := I) g hEnorm x u := by
  exact le_sSup ⟨r, hr, rfl, hseg⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem smul_mem_segmentDom_of_le
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (u : gUnitTangentSphere (I := I) g x) {s r : ℝ}
    (hs : 0 ≤ s) (hsr : s ≤ r)
    (hrseg : r • (u : TangentSpace I x) ∈ SegmentDom (I := I) g hEnorm x) :
    s • (u : TangentSpace I x) ∈ SegmentDom (I := I) g hEnorm x := by
  by_cases hr0 : r = 0
  · have hs0 : s = 0 := le_antisymm (hr0 ▸ hsr) hs
    subst s
    simpa using segmentDom_zero (I := I) g hEnorm x
  · have hrnonneg : 0 ≤ r := hs.trans hsr
    have hrpos : 0 < r := lt_of_le_of_ne hrnonneg (Ne.symm hr0)
    have hratio0 : 0 ≤ s / r := div_nonneg hs hrpos.le
    have hratio1 : s / r ≤ 1 := (div_le_one hrpos).2 hsr
    have hscaled := segmentDom_smul (I := I) g hEnorm hrseg hratio0 hratio1
    simpa only [smul_smul, div_mul_cancel₀ s hr0] using hscaled

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem smul_mem_segmentDom_iff_forall_le
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (u : gUnitTangentSphere (I := I) g x) {r : ℝ} (hr : 0 ≤ r) :
    r • (u : TangentSpace I x) ∈ SegmentDom (I := I) g hEnorm x ↔
      ∀ s : ℝ, 0 ≤ s → s ≤ r →
        s • (u : TangentSpace I x) ∈ SegmentDom (I := I) g hEnorm x := by
  constructor
  · intro hseg s hs hsr
    exact smul_mem_segmentDom_of_le (I := I) g hEnorm x u hs hsr hseg
  · intro h
    exact h r hr le_rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem ofReal_lt_cutTime_iff_smul_mem_segInt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (u : gUnitTangentSphere (I := I) g x) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal r < cutTime (I := I) g hEnorm x u ↔
      r • (u : TangentSpace I x) ∈ SegmentInt (I := I) g hEnorm x := by
  constructor
  · intro hcut
    rcases lt_sSup_iff.mp hcut with ⟨a, ⟨s, hs, rfl, hsseg⟩, hrs⟩
    have hspos : 0 < s := by
      apply ENNReal.ofReal_pos.mp
      exact (ENNReal.ofReal_pos.mpr hr).trans hrs
    have hrsReal : r < s :=
      (ENNReal.ofReal_lt_ofReal_iff hspos).mp hrs
    refine ⟨s / r, (one_lt_div hr).2 hrsReal, ?_⟩
    simpa only [smul_smul, div_mul_cancel₀ s hr.ne'] using hsseg
  · rintro ⟨c, hc, hcseg⟩
    have hcpos : 0 < c := one_pos.trans hc
    have hcrpos : 0 < c * r := mul_pos hcpos hr
    have hscaled : (c * r) • (u : TangentSpace I x) ∈
        SegmentDom (I := I) g hEnorm x := by
      simpa only [smul_smul] using hcseg
    have hle : ENNReal.ofReal (c * r) ≤ cutTime (I := I) g hEnorm x u :=
      ofReal_le_cutTime_of_smul_mem_segmentDom
        (I := I) g hEnorm x u hcrpos.le hscaled
    refine (ENNReal.ofReal_lt_ofReal_iff hcrpos).2 ?_ |>.trans_le hle
    calc
      r = 1 * r := (one_mul r).symm
      _ < c * r := mul_lt_mul_of_pos_right hc hr

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_uniform_pos_le_cutTime [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : gUnitTangentSphere (I := I) g x,
      ENNReal.ofReal ρ ≤ cutTime (I := I) g hEnorm x u := by
  obtain ⟨ρ0, hρ0, hsmall⟩ :=
    radial_riemannianEDist_eq_of_small (I := I) g hEnorm x
  refine ⟨ρ0 / 2, by positivity, fun u => ?_⟩
  have hρ : 0 < ρ0 / 2 := by positivity
  have hseg : (ρ0 / 2) • (u : TangentSpace I x) ∈
      SegmentDom (I := I) g hEnorm x := by
    rw [mem_segmentDom,
      sqrt_gInner_smul_self (I := I) g x hρ.le (u : TangentSpace I x),
      u.property, Real.sqrt_one, mul_one,
      hsmall u.property hρ.le (by linarith),
      ENNReal.toReal_ofReal hρ.le]
  exact ofReal_le_cutTime_of_smul_mem_segmentDom
    (I := I) g hEnorm x u hρ.le hseg

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem cutTime_pos [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (u : gUnitTangentSphere (I := I) g x) :
    0 < cutTime (I := I) g hEnorm x u := by
  obtain ⟨ρ, hρ, hle⟩ := exists_uniform_pos_le_cutTime (I := I) g hEnorm x
  exact (ENNReal.ofReal_pos.mpr hρ).trans_le (hle u)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem isOpen_segInt [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    IsOpen (SegmentInt (I := I) g hEnorm x) := by
  rw [isOpen_iff_forall_mem_open]
  intro v hv
  obtain ⟨c, hc, hcv⟩ := hv
  let d : ℝ := (1 + c) / 2
  have hd : 1 < d := by dsimp only [d]; linarith
  have hdc : d < c := by dsimp only [d]; linarith
  have hd0 : 0 < d := one_pos.trans hd
  have hdv : d • v ∈ SegmentInt (I := I) g hEnorm x := by
    refine ⟨c / d, (one_lt_div hd0).2 hdc, ?_⟩
    simpa only [smul_smul, div_mul_cancel₀ c hd0.ne'] using hcv
  obtain ⟨U, hU_open, hdvU, hU_seg⟩ :=
    exists_isOpen_subset_segDom_of_mem_segInt
      (I := I) g hEnorm x hdv
  let V : Set E := (fun w : E => d • w) ⁻¹' U
  refine ⟨V, ?_, ?_, ?_⟩
  · intro w hwV
    refine ⟨d, hd, ?_⟩
    exact hU_seg (d • (w : E)) hwV
  · exact hU_open.preimage (continuous_const_smul d)
  · exact hdvU

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem isOpen_cutTime_superlevel_of_isOpen_segInt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (hOpen : IsOpen (SegmentInt (I := I) g hEnorm x))
    {r : ℝ} (hr : 0 < r) :
    IsOpen {u : gUnitTangentSphere (I := I) g x |
      ENNReal.ofReal r < cutTime (I := I) g hEnorm x u} := by
  rw [show {u : gUnitTangentSphere (I := I) g x |
      ENNReal.ofReal r < cutTime (I := I) g hEnorm x u} =
      (fun u : gUnitTangentSphere (I := I) g x =>
        r • (u : TangentSpace I x)) ⁻¹' SegmentInt (I := I) g hEnorm x by
    ext u
    exact ofReal_lt_cutTime_iff_smul_mem_segInt
      (I := I) g hEnorm x u hr]
  exact hOpen.preimage
    (continuous_const_smul r |>.comp continuous_subtype_val)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem cutTime_lowerSemicontinuous_of_isOpen_segInt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (hOpen : IsOpen (SegmentInt (I := I) g hEnorm x)) :
    LowerSemicontinuous (cutTime (I := I) g hEnorm x) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro a
  by_cases hatop : a = ⊤
  · subst a
    simp
  by_cases ha0 : a = 0
  · subst a
    have heq : cutTime (I := I) g hEnorm x ⁻¹' Ioi (0 : ℝ≥0∞) = Set.univ := by
      ext u
      simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      exact cutTime_pos (I := I) g hEnorm x u
    rw [heq]
    exact isOpen_univ
  have hapos : 0 < a.toReal := (ENNReal.toReal_pos_iff).2
    ⟨bot_lt_iff_ne_bot.2 ha0, lt_top_iff_ne_top.mpr hatop⟩
  rw [← ENNReal.ofReal_toReal hatop]
  exact isOpen_cutTime_superlevel_of_isOpen_segInt
    (I := I) g hEnorm x hOpen hapos

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem cutTime_lowerSemicontinuous [ConnectedSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    LowerSemicontinuous (cutTime (I := I) g hEnorm x) :=
  cutTime_lowerSemicontinuous_of_isOpen_segInt (I := I) g hEnorm x
    (isOpen_segInt (I := I) g hEnorm x)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
