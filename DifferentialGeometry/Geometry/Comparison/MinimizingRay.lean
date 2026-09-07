import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

section IsMinimizingRayDef

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
def IsMinimizingRay
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (gamma : ℝ → M) : Prop :=
  gamma 0 = p ∧
    IsGeodesicOn (I := I) g gamma (Set.Ici 0) ∧
    ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t →
      riemannianEDist I (gamma s) (gamma t) = ENNReal.ofReal (t - s)

end IsMinimizingRayDef

namespace IsMinimizingRay

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem start_eq
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {p : M} {gamma : ℝ → M}
    (hgamma : IsMinimizingRay (I := I) g p gamma) :
    gamma 0 = p :=
  hgamma.1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem isGeodesicOn
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {p : M} {gamma : ℝ → M}
    (hgamma : IsMinimizingRay (I := I) g p gamma) :
    IsGeodesicOn (I := I) g gamma (Set.Ici 0) :=
  hgamma.2.1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem edist_eq
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {p : M} {gamma : ℝ → M}
    (hgamma : IsMinimizingRay (I := I) g p gamma)
    ⦃s t : ℝ⦄ (hs : 0 ≤ s) (hst : s ≤ t) :
    riemannianEDist I (gamma s) (gamma t) = ENNReal.ofReal (t - s) :=
  hgamma.2.2 hs hst

end IsMinimizingRay

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private theorem radial_eq_of_end
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    {r L : ℝ} (hr : 0 ≤ r) (hrL : r ≤ L)
    (hL : riemannianEDist I p
      (expMapIntrinsic (I := I) g hEnorm p (L • u)) = ENNReal.ofReal L) :
    riemannianEDist I p
      (expMapIntrinsic (I := I) g hEnorm p (r • u)) = ENNReal.ofReal r := by
  have hupper :
      riemannianEDist I p
          (expMapIntrinsic (I := I) g hEnorm p (r • u)) ≤ ENNReal.ofReal r := by
    have h := intrinsicGeodesic_riemannianEDist_le
      (I := I) g hEnorm p u (s := 0) (t := r) hr
    rw [intrinsicGeodesic_zero (I := I) g hEnorm p u, hu, Real.sqrt_one,
      one_mul, sub_zero] at h
    simpa only [expMapIntrinsic_def,
      intrinsicGeodesic_smul (I := I) g hEnorm p u r] using h
  have htail :
      riemannianEDist I
          (expMapIntrinsic (I := I) g hEnorm p (r • u))
          (expMapIntrinsic (I := I) g hEnorm p (L • u)) ≤
        ENNReal.ofReal (L - r) := by
    have h := intrinsicGeodesic_riemannianEDist_le
      (I := I) g hEnorm p u (s := r) (t := L) hrL
    rw [hu, Real.sqrt_one, one_mul] at h
    simpa only [expMapIntrinsic_def,
      intrinsicGeodesic_smul (I := I) g hEnorm p u r,
      intrinsicGeodesic_smul (I := I) g hEnorm p u L] using h
  have htri :
      ENNReal.ofReal L ≤
        riemannianEDist I p
            (expMapIntrinsic (I := I) g hEnorm p (r • u)) +
          riemannianEDist I
            (expMapIntrinsic (I := I) g hEnorm p (r • u))
            (expMapIntrinsic (I := I) g hEnorm p (L • u)) := by
    rw [← hL]
    exact riemannianEDist_triangle
  have hlower_sum :
      ENNReal.ofReal L ≤
        riemannianEDist I p
            (expMapIntrinsic (I := I) g hEnorm p (r • u)) +
          ENNReal.ofReal (L - r) :=
    htri.trans (add_le_add (le_refl _) htail)
  have hsplit :
      ENNReal.ofReal L = ENNReal.ofReal r + ENNReal.ofReal (L - r) := by
    rw [← ENNReal.ofReal_add hr (sub_nonneg.mpr hrL)]
    congr 1
    ring
  rw [hsplit] at hlower_sum
  have hlower :
      ENNReal.ofReal r ≤ riemannianEDist I p
        (expMapIntrinsic (I := I) g hEnorm p (r • u)) :=
    (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hlower_sum
  exact le_antisymm hupper hlower

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private theorem pair_eq_of_radial
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hradial : ∀ ⦃t : ℝ⦄, 0 ≤ t →
      riemannianEDist I p
        (expMapIntrinsic (I := I) g hEnorm p (t • u)) = ENNReal.ofReal t)
    ⦃s t : ℝ⦄ (hs : 0 ≤ s) (hst : s ≤ t) :
    riemannianEDist I
        (expMapIntrinsic (I := I) g hEnorm p (s • u))
        (expMapIntrinsic (I := I) g hEnorm p (t • u)) =
      ENNReal.ofReal (t - s) := by
  have hupper :
      riemannianEDist I
          (expMapIntrinsic (I := I) g hEnorm p (s • u))
          (expMapIntrinsic (I := I) g hEnorm p (t • u)) ≤
        ENNReal.ofReal (t - s) := by
    have h := intrinsicGeodesic_riemannianEDist_le
      (I := I) g hEnorm p u (s := s) (t := t) hst
    rw [hu, Real.sqrt_one, one_mul] at h
    simpa only [expMapIntrinsic_def,
      intrinsicGeodesic_smul (I := I) g hEnorm p u s,
      intrinsicGeodesic_smul (I := I) g hEnorm p u t] using h
  have htri :
      ENNReal.ofReal t ≤ ENNReal.ofReal s +
        riemannianEDist I
          (expMapIntrinsic (I := I) g hEnorm p (s • u))
          (expMapIntrinsic (I := I) g hEnorm p (t • u)) := by
    rw [← hradial hs, ← hradial (hs.trans hst)]
    exact riemannianEDist_triangle
  have hsplit :
      ENNReal.ofReal t = ENNReal.ofReal s + ENNReal.ofReal (t - s) := by
    rw [← ENNReal.ofReal_add hs (sub_nonneg.mpr hst)]
    congr 1
    ring
  rw [hsplit] at htri
  have hlower :
      ENNReal.ofReal (t - s) ≤
        riemannianEDist I
          (expMapIntrinsic (I := I) g hEnorm p (s • u))
          (expMapIntrinsic (I := I) g hEnorm p (t • u)) :=
    (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp htri
  exact le_antisymm hupper hlower

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_minimizing_ray
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [ConnectedSpace M] [NoncompactSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    ∃ gamma : ℝ → M, IsMinimizingRay (I := I) g p gamma := by
  classical
  have hball_compact (R : ℝ) (hR : 0 ≤ R) :
      IsCompact {q : M | riemannianEDist I p q ≤ ENNReal.ofReal R} := by
    have himg : IsCompact
        ((fun v : E ↦ expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from v)) ''
          {v : E | Real.sqrt (g.inner p v v) ≤ R}) :=
      (gLenBall_isCompact (I := I) g p R).image
        (expMapIntrinsic_continuous (I := I) g hEnorm p)
    have hdist : Continuous (fun q : M ↦ riemannianEDist I p q) := by
      simpa only [riemannianEDist_comm] using
        (continuous_riemannianEDist_to (I := I) p)
    have hclosed :
        IsClosed {q : M | riemannianEDist I p q ≤ ENNReal.ofReal R} :=
      isClosed_le hdist continuous_const
    refine himg.of_isClosed_subset hclosed ?_
    intro q hq
    have hfin : riemannianEDist I p q ≠ ⊤ :=
      riemannianEDist_ne_top (I := I) p q
    obtain ⟨v, hv_exp, hv_len⟩ :=
      minExp_of_ne_top (I := I) g hEnorm p q hfin
    refine ⟨v, ?_, hv_exp⟩
    change Real.sqrt (g.inner p v v) ≤ R
    rw [hv_len]
    have hreal :=
      (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).2 hq
    simpa only [ENNReal.toReal_ofReal hR] using hreal
  have hfar (R : ℝ) (hR : 0 ≤ R) :
      ∃ q : M, ENNReal.ofReal R < riemannianEDist I p q := by
    have hne := (hball_compact R hR).ne_univ
    obtain ⟨q, hq⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
    exact ⟨q, lt_of_not_ge hq⟩
  let radius : ℕ → ℝ := fun n ↦ n + 1
  have radius_pos (n : ℕ) : 0 < radius n := by
    change 0 < (n : ℝ) + 1
    positivity
  let K : ℕ → Set (TangentSpace I p) := fun n ↦
    {u | g.inner p u u = 1 ∧
      riemannianEDist I p
        (expMapIntrinsic (I := I) g hEnorm p (radius n • u)) =
          ENNReal.ofReal (radius n)}
  have hK_closed (n : ℕ) : IsClosed (K n) := by
    have hexp : Continuous (fun u : TangentSpace I p ↦
        expMapIntrinsic (I := I) g hEnorm p (radius n • u)) :=
      (expMapIntrinsic_continuous (I := I) g hEnorm p).comp
        (continuous_const_smul (radius n))
    have hdist : Continuous (fun q : M ↦ riemannianEDist I p q) := by
      simpa only [riemannianEDist_comm] using
        (continuous_riemannianEDist_to (I := I) p)
    have heq : IsClosed {u : TangentSpace I p |
        riemannianEDist I p
          (expMapIntrinsic (I := I) g hEnorm p (radius n • u)) =
            ENNReal.ofReal (radius n)} :=
      isClosed_eq (hdist.comp hexp) continuous_const
    have hunit := gUnitSphere_isClosed (I := I) g p
    rw [show K n =
        {u : TangentSpace I p | g.inner p u u = 1} ∩
          {u : TangentSpace I p |
            riemannianEDist I p
              (expMapIntrinsic (I := I) g hEnorm p (radius n • u)) =
                ENNReal.ofReal (radius n)} by
      ext u
      simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff]]
    exact hunit.inter heq
  have hK_nonempty (n : ℕ) : (K n).Nonempty := by
    obtain ⟨q, hqfar⟩ := hfar (radius n) (radius_pos n).le
    have hfin : riemannianEDist I p q ≠ ⊤ := riemannianEDist_ne_top (I := I) p q
    obtain ⟨v, hv_exp, hv_len⟩ := minExp_of_ne_top (I := I) g hEnorm p q hfin
    let L : ℝ := (riemannianEDist I p q).toReal
    have hRL : radius n < L := by
      have hreal :=
        (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfin).2 hqfar
      simpa only [L, ENNReal.toReal_ofReal (radius_pos n).le] using hreal
    have hL_pos : 0 < L := (radius_pos n).trans hRL
    have hL_ne : L ≠ 0 := ne_of_gt hL_pos
    let u : TangentSpace I p := L⁻¹ • v
    have hinner_v : g.inner p v v = L ^ 2 := by
      rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g p v), hv_len]
    have hu : g.inner p u u = 1 := by
      change g.inner p (L⁻¹ • v) (L⁻¹ • v) = 1
      rw [gInner_smul_self (I := I) g p L⁻¹ v, hinner_v]
      rw [← mul_pow, inv_mul_cancel₀ hL_ne, one_pow]
    have hscale : L • u = v := by
      change L • (L⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ hL_ne, one_smul]
    have hL_end : riemannianEDist I p
        (expMapIntrinsic (I := I) g hEnorm p (L • u)) = ENNReal.ofReal L := by
      rw [hscale, hv_exp]
      exact (ENNReal.ofReal_toReal hfin).symm
    refine ⟨u, ?_⟩
    change g.inner p u u = 1 ∧
      riemannianEDist I p
        (expMapIntrinsic (I := I) g hEnorm p (radius n • u)) =
          ENNReal.ofReal (radius n)
    exact ⟨hu, radial_eq_of_end (I := I) g hEnorm p u hu
      (radius_pos n).le hRL.le hL_end⟩
  have hK_succ (n : ℕ) : K (n + 1) ⊆ K n := by
    intro u hu
    change g.inner p u u = 1 ∧
      riemannianEDist I p
        (expMapIntrinsic (I := I) g hEnorm p (radius (n + 1) • u)) =
          ENNReal.ofReal (radius (n + 1)) at hu
    change g.inner p u u = 1 ∧
      riemannianEDist I p
        (expMapIntrinsic (I := I) g hEnorm p (radius n • u)) =
          ENNReal.ofReal (radius n)
    refine ⟨hu.1, ?_⟩
    exact radial_eq_of_end (I := I) g hEnorm p u hu.1
      (radius_pos n).le (by simp [radius]) hu.2
  have hK0 : IsCompact (K 0) :=
    (gUnitSphere_isCompact (I := I) g p).of_isClosed_subset
      (hK_closed 0) (fun u hu ↦ by
        change g.inner p u u = 1 ∧
          riemannianEDist I p
            (expMapIntrinsic (I := I) g hEnorm p (radius 0 • u)) =
              ENNReal.ofReal (radius 0) at hu
        exact hu.1)
  obtain ⟨u, huK⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      K hK_succ hK_nonempty hK0 hK_closed
  have hu_mem (n : ℕ) : u ∈ K n := Set.mem_iInter.mp huK n
  have hu0 := hu_mem 0
  change g.inner p u u = 1 ∧
    riemannianEDist I p
      (expMapIntrinsic (I := I) g hEnorm p (radius 0 • u)) =
        ENNReal.ofReal (radius 0) at hu0
  have hu : g.inner p u u = 1 := hu0.1
  have hradial : ∀ ⦃t : ℝ⦄, 0 ≤ t →
      riemannianEDist I p
        (expMapIntrinsic (I := I) g hEnorm p (t • u)) = ENNReal.ofReal t := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_nat_ge t
    have htR : t ≤ radius n := hn.trans (by simp [radius])
    have hun := hu_mem n
    change g.inner p u u = 1 ∧
      riemannianEDist I p
        (expMapIntrinsic (I := I) g hEnorm p (radius n • u)) =
          ENNReal.ofReal (radius n) at hun
    exact radial_eq_of_end (I := I) g hEnorm p u hu ht htR hun.2
  let gamma : ℝ → M := fun t ↦ expMapIntrinsic (I := I) g hEnorm p (t • u)
  refine ⟨gamma, ?_, ?_, ?_⟩
  · simp only [gamma, zero_smul]
    exact expMapIntrinsic_zero (I := I) g hEnorm p
  · have hgamma : gamma = intrinsicGeodesic (I := I) g hEnorm p u := by
      funext t
      change expMapIntrinsic (I := I) g hEnorm p (t • u) =
        intrinsicGeodesic (I := I) g hEnorm p u t
      rw [expMapIntrinsic_def,
        intrinsicGeodesic_smul (I := I) g hEnorm p u t]
    rw [hgamma]
    exact (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u).isGeodesicOn
      (Set.Ici 0)
  · intro s t hs hst
    exact pair_eq_of_radial (I := I) g hEnorm p u hu hradial hs hst

end Riemannian
end Geometry
end DifferentialGeometry

end
