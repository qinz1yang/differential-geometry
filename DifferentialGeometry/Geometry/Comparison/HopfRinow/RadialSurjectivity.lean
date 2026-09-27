import DifferentialGeometry.Geometry.Exponential.GaussLemma.Basic
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Exponential.CompactBall
import DifferentialGeometry.Geometry.Comparison.HopfRinow.CompactBall
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Basic
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates.Basic
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Convex.PathConnected
open DifferentialGeometry.Geometry.Curvature

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace RadialSurjectivity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable (g : SmoothRiemannianMetric I M)
variable [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private def gBall (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    Set (TangentSpace I p) :=
  {v : TangentSpace I p | Real.sqrt (g.inner p v v) ≤ R}

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private lemma zero_mem_gBall (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hR : 0 ≤ R) : (0 : TangentSpace I p) ∈ gBall (I := I) g p R := by
  have h0 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by
    simp
  change Real.sqrt (g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p)) ≤ R
  rw [h0, Real.sqrt_zero]
  exact hR

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private lemma starConvex_gBall (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    StarConvex ℝ (0 : TangentSpace I p) (gBall (I := I) g p R) := by
  intro y hy a b ha hb hab
  have hb_le_one : b ≤ 1 := by linarith
  have hy' : Real.sqrt (g.inner p y y) ≤ R := hy
  have hsqrt_nonneg : 0 ≤ Real.sqrt (g.inner p y y) := Real.sqrt_nonneg _
  change Real.sqrt (g.inner p (a • (0 : TangentSpace I p) + b • y)
      (a • (0 : TangentSpace I p) + b • y)) ≤ R
  rw [smul_zero, zero_add]
  rw [sqrt_gInner_smul_self (I := I) g p hb y]
  calc b * Real.sqrt (g.inner p y y)
      ≤ 1 * Real.sqrt (g.inner p y y) :=
        mul_le_mul_of_nonneg_right hb_le_one hsqrt_nonneg
    _ = Real.sqrt (g.inner p y y) := one_mul _
    _ ≤ R := hy'

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem gBall_isPreconnected (g : SmoothRiemannianMetric I M) (p : M)
    {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected (gBall (I := I) g p R) :=
  ((starConvex_gBall (I := I) g p R).isPathConnected
    (zero_mem_gBall (I := I) g p hR)).isConnected.isPreconnected

private def radialMinSet (g : SmoothRiemannianMetric I M) (p : M) : Set M :=
  {q : M | ∃ v : TangentSpace I p,
    expMap (I := I) g p v = q ∧
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) = riemannianEDist I p q}

omit [NeZero (Module.finrank ℝ E)] in
private theorem p_mem_radialMinSet [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) :
    p ∈ radialMinSet (I := I) g p := by
  refine ⟨(0 : TangentSpace I p), expMap_zero (I := I) g p, ?_⟩
  have h0 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by
    simp
  rw [h0, Real.sqrt_zero, ENNReal.ofReal_zero, riemannianEDist_self]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)] in
private lemma gInner_self_nonneg (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : 0 ≤ g.inner p v v := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp
  · exact (g.pos p v hv).le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
private lemma continuous_gInner_self (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (fun v : TangentSpace I p => g.inner p v v) :=
  (g.inner p).continuous.clm_apply continuous_id

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
private lemma continuous_sqrt_gInner_self (g : SmoothRiemannianMetric I M)
    (p : M) :
    Continuous (fun v : TangentSpace I p => Real.sqrt (g.inner p v v)) :=
  Real.continuous_sqrt.comp (continuous_gInner_self (I := I) g p)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
private lemma isClosed_gBall (g : SmoothRiemannianMetric I M) (p : M)
    (R : ℝ) : IsClosed (gBall (I := I) g p R) := by
  have hpre : gBall (I := I) g p R =
      (fun v : TangentSpace I p => Real.sqrt (g.inner p v v)) ⁻¹' Set.Iic R := by
    ext v; simp only [gBall, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic]
  rw [hpre]
  exact IsClosed.preimage (continuous_sqrt_gInner_self (I := I) g p) isClosed_Iic

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
private lemma isBounded_gBall (g : SmoothRiemannianMetric I M) (p : M)
    (R : ℝ) : Bornology.IsBounded (gBall (I := I) g p R) := by
  rcases lt_or_ge R 0 with hR | hR
  · have hempty : gBall (I := I) g p R = ∅ := by
      ext v
      simp only [gBall, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hR (Real.sqrt_nonneg _)
    rw [hempty]; exact Bornology.isBounded_empty
  · obtain ⟨r, hr⟩ :=
      (NormedSpace.isVonNBounded_iff' ℝ (E := TangentSpace I p)).1 (g.isVonNBounded p)
    rw [isBounded_iff_forall_norm_le]
    refine ⟨(R + 1) * r, fun v hv => ?_⟩
    have hsqrt : Real.sqrt (g.inner p v v) ≤ R := hv
    have hnonneg : 0 ≤ g.inner p v v := gInner_self_nonneg (I := I) g p v
    have hgvv : g.inner p v v ≤ R ^ 2 := by
      nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (g.inner p v v), hsqrt]
    have hRpos : (0 : ℝ) < R + 1 := by linarith
    set w : TangentSpace I p := (R + 1)⁻¹ • v with hw
    have hgw : g.inner p w w < 1 := by
      have hsmul : g.inner p w w = (R + 1)⁻¹ ^ 2 * g.inner p v v :=
        gInner_smul_self (I := I) g p _ v
      rw [hsmul]
      have hinv_sq_pos : (0 : ℝ) < (R + 1)⁻¹ ^ 2 :=
        pow_pos (inv_pos.mpr hRpos) 2
      have hge : 0 ≤ R / (R + 1) := div_nonneg hR hRpos.le
      have hlt : R / (R + 1) < 1 := by rw [div_lt_one hRpos]; linarith
      calc (R + 1)⁻¹ ^ 2 * g.inner p v v
          ≤ (R + 1)⁻¹ ^ 2 * R ^ 2 :=
            mul_le_mul_of_nonneg_left hgvv hinv_sq_pos.le
        _ = (R / (R + 1)) ^ 2 := by
            rw [div_pow]; field_simp
        _ < 1 := by nlinarith [hlt, hge]
    have hwnorm : ‖w‖ ≤ r := hr w hgw
    have hv_eq : v = (R + 1) • w := by
      rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt hRpos), one_smul]
    rw [hv_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
    exact mul_le_mul_of_nonneg_left hwnorm hRpos.le

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma isCompact_gBall (g : SmoothRiemannianMetric I M) (p : M)
    (R : ℝ) : IsCompact (gBall (I := I) g p R) := by
  have : ProperSpace (TangentSpace I p) := FiniteDimensional.proper_real (TangentSpace I p)
  exact Metric.isCompact_of_isClosed_isBounded
    (isClosed_gBall (I := I) g p R) (isBounded_gBall (I := I) g p R)

variable [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [PseudoEMetricSpace M] [T2Space (TangentBundle I M)]
variable [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
variable [IsRiemannianManifold I M] [CompleteSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M]
    [PseudoEMetricSpace M] [T2Space (TangentBundle I M)] [IsRiemannianManifold I M]
    [CompleteSpace M] in
private lemma continuous_riemannianEDist_ambient
    (p : M) : Continuous (fun q : M => riemannianEDist I p q) := by
  have : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  have : RegularSpace M := inferInstance
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact (continuous_const.edist continuous_id)

omit [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] in
private theorem sphere_jump_raw
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x q : M) {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hxq : riemannianEDist I x q = ENNReal.ofReal ρ) :
    ∃ R : ℝ, 0 < R ∧ ∀ {δ : ℝ}, 0 < δ → δ < R → δ < ρ →
      ∃ (y : M) (w : TangentSpace I x), g.inner x w w = 1 ∧
        δ • w ∈ expDomain (I := I) g x ∧
        y = expMap (I := I) g x (δ • w) ∧
        riemannianEDist I x y = ENNReal.ofReal δ ∧
        riemannianEDist I y q = ENNReal.ofReal (ρ - δ) := by
  classical
  let _ : MeasurableSpace M := borel M
  have _ : BorelSpace M := ⟨rfl⟩
  refine ⟨metricCoerciveExpRadius (I := I) g x,
    metricCoerciveExpRadius_pos (I := I) g x, ?_⟩
  intro δ hδ_pos hδ_R hδ_lt_ρ
  set F : E → M := fun u : E =>
    (expMap (I := I) g x (show TangentSpace I x from u) : M) with hF_def
  set f : TangentSpace I x → M := fun w => F (δ • (w : E)) with hf_def
  set sph : Set (TangentSpace I x) :=
    {w : TangentSpace I x | g.inner x w w = 1} with hsph_def
  have hsph_ne : sph.Nonempty := by
    have hfin_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
    let _ : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
    obtain ⟨a, ha_ne⟩ : ∃ a : TangentSpace I x, a ≠ 0 :=
      ⟨(exists_ne (0 : E)).choose, (exists_ne (0 : E)).choose_spec⟩
    have hc_pos : 0 < g.inner x a a := g.pos x a ha_ne
    set s : ℝ := Real.sqrt (g.inner x a a)⁻¹ with hs_def
    have hs_sq : s * s = (g.inner x a a)⁻¹ :=
      Real.mul_self_sqrt (inv_nonneg.mpr hc_pos.le)
    refine ⟨s • a, ?_⟩
    change g.inner x (s • a) (s • a) = 1
    rw [gInner_smul_self (I := I) g x s a, show s ^ 2 = s * s by ring,
      hs_sq, inv_mul_cancel₀ (ne_of_gt hc_pos)]
  have hsph_compact : IsCompact sph := by
    have hsph_closed : IsClosed sph := by
      rw [hsph_def]
      exact isClosed_eq (continuous_gInner_self (I := I) g x) continuous_const
    refine (gUnitSphere_isCompact (I := I) g x).of_isClosed_subset hsph_closed ?_
    intro w hw
    exact hw
  have hsphnorm : ∀ w ∈ sph,
      Real.sqrt (g.inner x ((δ • w : TangentSpace I x) : E)
        ((δ • w : TangentSpace I x) : E)) = δ := by
    intro w hw
    rw [sqrt_gInner_smul_self (I := I) g x hδ_pos.le w, hw,
      Real.sqrt_one, mul_one]
  have hf_contOn : ContinuousOn f sph := by
    intro w₀ hw₀
    have hball : Real.sqrt (g.inner x ((δ • w₀ : TangentSpace I x) : E)
        ((δ • w₀ : TangentSpace I x) : E)) <
        metricCoerciveExpRadius (I := I) g x := by
      rw [hsphnorm w₀ hw₀]
      exact hδ_R
    have hEucl :=
      norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g x hball
    have hcontAt : ContinuousAt F ((δ • (w₀ : E)) : E) :=
      (expMap_contMDiffAt2_of_norm_lt_radius (I := I) g x hEucl).continuousAt
    have hscale : ContinuousAt
        (fun w : TangentSpace I x => ((δ • (w : E)) : E)) w₀ :=
      (continuous_const_smul δ).continuousAt
    exact (hcontAt.comp hscale).continuousWithinAt
  have hS_compact : IsCompact (f '' sph) :=
    hsph_compact.image_of_continuousOn hf_contOn
  have hS_ne : (f '' sph).Nonempty := hsph_ne.image f
  have hdist_cont : Continuous (fun z : M => riemannianEDist I z q) := by
    simpa only [riemannianEDist_comm] using
      continuous_riemannianEDist_ambient (I := I) (M := M) q
  obtain ⟨y₀, hy₀_mem, hy₀_min⟩ :=
    hS_compact.exists_isMinOn hS_ne hdist_cont.continuousOn
  obtain ⟨w, hw_unit, hw_eq⟩ := hy₀_mem
  simp only [hf_def, hF_def] at hw_eq
  have hw_small : Real.sqrt (g.inner x ((δ • w : TangentSpace I x) : E)
      ((δ • w : TangentSpace I x) : E)) < metricCoerciveExpRadius (I := I) g x := by
    rw [hsphnorm w hw_unit]
    exact hδ_R
  have hw_dom : δ • w ∈ expDomain (I := I) g x :=
    mem_expDomain_of_norm_lt_radius (I := I) g x
      (norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g x hw_small)
  have hdxy : riemannianEDist I x y₀ = ENNReal.ofReal δ := by
    rw [← hw_eq]
    have hradial := edist_exp_eq_radius (I := I) g x hEnorm hw_small
    rw [hsphnorm w hw_unit] at hradial
    exact hradial
  refine ⟨y₀, w, hw_unit, hw_dom, hw_eq.symm, hdxy, ?_⟩
  have hρδ_nn : 0 ≤ ρ - δ := sub_nonneg.mpr hδ_lt_ρ.le
  have hδ_nn : 0 ≤ δ := hδ_pos.le
  have hge : ENNReal.ofReal (ρ - δ) ≤ riemannianEDist I y₀ q := by
    have htri : riemannianEDist I x q ≤
        riemannianEDist I x y₀ + riemannianEDist I y₀ q :=
      riemannianEDist_triangle
    rw [hxq, hdxy] at htri
    have hsplit : ENNReal.ofReal ρ =
        ENNReal.ofReal δ + ENNReal.ofReal (ρ - δ) := by
      rw [← ENNReal.ofReal_add hδ_nn hρδ_nn]
      congr 1
      ring
    rw [hsplit] at htri
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp htri
  have hdist_from_x : Continuous (fun z : M => riemannianEDist I x z) :=
    continuous_riemannianEDist_ambient (I := I) (M := M) x
  have hcore : ∀ ε : ℝ, 0 < ε →
      riemannianEDist I y₀ q ≤ ENNReal.ofReal (ρ - δ + ε) := by
    intro ε hε
    have hlt : riemannianEDist I x q < ENNReal.ofReal (ρ + ε) := by
      rw [hxq]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hρ_pos.le).mpr (by linarith)
    obtain ⟨P, hP0, hP1, hP_C1, hP_len⟩ :=
      exists_lt_of_riemannianEDist_lt hlt
    set h : ℝ → ℝ := fun t => (riemannianEDist I x (P t)).toReal with hh_def
    have hP_contOn : ContinuousOn P (Set.Icc (0 : ℝ) 1) := hP_C1.continuousOn
    have hP_fin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        riemannianEDist I x (P t) ≠ ⊤ := by
      intro t ht
      have hC1_sub : ContMDiffOn 𝓘(ℝ, ℝ) I 1 P (Set.Icc 0 t) :=
        hP_C1.mono (Set.Icc_subset_Icc le_rfl ht.2)
      have hdist_le : riemannianEDist I x (P t) ≤ pathELength I P 0 t :=
        riemannianEDist_le_pathELength (I := I) (γ := P) (a := 0) (b := t)
          hC1_sub hP0 rfl ht.1
      have hlen_le : pathELength I P 0 t ≤ pathELength I P 0 1 :=
        pathELength_mono le_rfl ht.2
      exact ne_of_lt ((hdist_le.trans hlen_le).trans_lt
        (hP_len.trans ENNReal.ofReal_lt_top))
    have hh_contOn : ContinuousOn h (Set.Icc (0 : ℝ) 1) := by
      have hdistP : ContinuousOn
          (fun t : ℝ => riemannianEDist I x (P t)) (Set.Icc 0 1) :=
        hdist_from_x.comp_continuousOn hP_contOn
      refine ENNReal.continuousOn_toReal.comp' hdistP ?_
      intro t ht
      exact hP_fin t ht
    have hh0 : h 0 = 0 := by
      simp only [hh_def, hP0, riemannianEDist_self, ENNReal.toReal_zero]
    have hh1 : h 1 = ρ := by
      simp only [hh_def, hP1, hxq, ENNReal.toReal_ofReal hρ_pos.le]
    have hδ_mem : δ ∈ Set.Icc (h 0) (h 1) := by
      rw [hh0, hh1]
      exact ⟨hδ_nn, hδ_lt_ρ.le⟩
    obtain ⟨ts, hts_mem, hts_eq⟩ :=
      intermediate_value_Icc (zero_le_one) hh_contOn hδ_mem
    set z : M := P ts with hz_def
    have hz_fin : riemannianEDist I x z ≠ ⊤ := hP_fin ts hts_mem
    have hdxz : riemannianEDist I x z = ENNReal.ofReal δ := by
      have hreal : (riemannianEDist I x z).toReal = δ := hts_eq
      rw [← hreal, ENNReal.ofReal_toReal hz_fin]
    have hdxz_real : (riemannianEDist I x z).toReal = δ := hts_eq
    have hz_lt_R : (riemannianEDist I x z).toReal <
        metricCoerciveExpRadius (I := I) g x := by
      rw [hdxz_real]
      exact hδ_R
    obtain ⟨vz, _hvz_target, _hvz_dom, hvz_norm, hz_eq⟩ :=
      metricBall_subset_normalBall (I := I) g x hEnorm hz_fin hz_lt_R
    rw [hdxz_real] at hvz_norm
    set wz : TangentSpace I x :=
      (δ⁻¹ : ℝ) • (show TangentSpace I x from vz) with hwz_def
    have hgvz : g.inner x (show TangentSpace I x from vz)
        (show TangentSpace I x from vz) = δ ^ 2 := by
      have hsquare := Real.sq_sqrt
        (gInner_self_nonneg (I := I) g x (show TangentSpace I x from vz))
      rw [hvz_norm] at hsquare
      linarith
    have hwz_unit : g.inner x wz wz = 1 := by
      rw [hwz_def, gInner_smul_self (I := I) g x δ⁻¹
        (show TangentSpace I x from vz), hgvz,
        show (δ⁻¹) ^ 2 = (δ ^ 2)⁻¹ by rw [inv_pow]]
      exact inv_mul_cancel₀ (by positivity)
    have hδwz : (δ : ℝ) • wz = (show TangentSpace I x from vz) := by
      rw [hwz_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hδ_pos), one_smul]
    have hz_in_S : z ∈ f '' sph := by
      refine ⟨wz, hwz_unit, ?_⟩
      change expMap (I := I) g x (δ • wz) = z
      rw [hδwz, ← hz_eq]
    have hmin_z : riemannianEDist I y₀ q ≤ riemannianEDist I z q :=
      hy₀_min hz_in_S
    have hts_le_one : ts ≤ 1 := hts_mem.2
    have hts_nn : 0 ≤ ts := hts_mem.1
    have hC1_left : ContMDiffOn 𝓘(ℝ, ℝ) I 1 P (Set.Icc 0 ts) :=
      hP_C1.mono (Set.Icc_subset_Icc le_rfl hts_le_one)
    have hC1_right : ContMDiffOn 𝓘(ℝ, ℝ) I 1 P (Set.Icc ts 1) :=
      hP_C1.mono (Set.Icc_subset_Icc hts_nn le_rfl)
    have hdxz_path : riemannianEDist I x z ≤ pathELength I P 0 ts :=
      riemannianEDist_le_pathELength (I := I) (γ := P) (a := 0) (b := ts)
        hC1_left hP0 rfl hts_nn
    have hdzq_path : riemannianEDist I z q ≤ pathELength I P ts 1 :=
      riemannianEDist_le_pathELength (I := I) (γ := P) (a := ts) (b := 1)
        hC1_right rfl hP1 hts_le_one
    have hadd : pathELength I P 0 ts + pathELength I P ts 1 =
        pathELength I P 0 1 := Manifold.pathELength_add hts_nn hts_le_one
    have hsum_lt : ENNReal.ofReal δ + riemannianEDist I z q <
        ENNReal.ofReal (ρ + ε) := by
      calc
        ENNReal.ofReal δ + riemannianEDist I z q =
            riemannianEDist I x z + riemannianEDist I z q := by rw [hdxz]
        _ ≤ pathELength I P 0 ts + pathELength I P ts 1 :=
          add_le_add hdxz_path hdzq_path
        _ = pathELength I P 0 1 := hadd
        _ < ENNReal.ofReal (ρ + ε) := hP_len
    have hsplit2 : ENNReal.ofReal (ρ + ε) =
        ENNReal.ofReal δ + ENNReal.ofReal (ρ - δ + ε) := by
      rw [← ENNReal.ofReal_add hδ_nn (by linarith)]
      congr 1
      ring
    rw [hsplit2] at hsum_lt
    have hzq_lt : riemannianEDist I z q < ENNReal.ofReal (ρ - δ + ε) :=
      (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).mp hsum_lt
    exact hmin_z.trans hzq_lt.le
  have hle : riemannianEDist I y₀ q ≤ ENNReal.ofReal (ρ - δ) := by
    refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    have h1 : riemannianEDist I y₀ q ≤
        ENNReal.ofReal (ρ - δ + (ε : ℝ)) := hcore ε (by exact_mod_cast hε)
    refine h1.trans ?_
    rw [ENNReal.ofReal_add hρδ_nn (le_of_lt (by exact_mod_cast hε))]
    gcongr
    rw [ENNReal.ofReal_coe_nnreal]
  exact le_antisymm hle hge

omit [ConnectedSpace M] [CompleteSpace M] in
private theorem sphere_jump_cpt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) {ρ R : ℝ} (hρ_pos : 0 < ρ)
    (hpq : riemannianEDist I p q = ENNReal.ofReal ρ)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R))) :
    ∃ (δ : ℝ) (y : M) (u : TangentSpace I p),
      0 < δ ∧ δ < ρ ∧ g.inner p u u = 1 ∧
        δ • u ∈ expDomain (I := I) g p ∧
        y = expMap (I := I) g p (δ • u) ∧
        riemannianEDist I p y = ENNReal.ofReal δ ∧
        riemannianEDist I y q = ENNReal.ofReal (ρ - δ) ∧
        ∀ {t : ℝ}, 0 < t → t < R → t • u ∈ expDomain (I := I) g p := by
  obtain ⟨R₀, hR₀_pos, hjump⟩ :=
    sphere_jump_raw (I := I) g hEnorm p q hρ_pos hpq
  let δ : ℝ := min (R₀ / 2) (ρ / 2)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ_R₀ : δ < R₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ_ρ : δ < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨y, u, hu, hδ_dom, hy, hpy, hyq⟩ :=
    hjump hδ_pos hδ_R₀ hδ_ρ
  refine ⟨δ, y, u, hδ_pos, hδ_ρ, hu, hδ_dom, hy, hpy, hyq, ?_⟩
  intro t ht_pos ht_R
  apply mem_expDomain_of_isCompact_closedEBall (I := I) g hEnorm p (t • u)
    (by
      rw [sqrt_gInner_smul_self (I := I) g p ht_pos.le u, hu,
        Real.sqrt_one, mul_one]
      exact ht_R) hcpt

omit [NeZero (Module.finrank ℝ E)]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [ConnectedSpace M] [CompleteSpace M] in
private lemma geoOn_data
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} {p : M} {v : TangentSpace I p}
    (hJ : IsOpen J)
    (hγ : IsGeodesicOnWithInitial (I := I) g γ J p v) :
    IsGeodesicOn (I := I) g γ J ∧ ContinuousOn γ J ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J := by
  have hgeo : IsGeodesicOn (I := I) g γ J := by
    intro t ht
    exact (hγ.isGeodesicAt (hJ.mem_nhds ht)).hasGeodesicEquationAt g
  obtain ⟨f, hproj, _hf0, hf⟩ := hγ
  have hcontLift : ContinuousOn f J := hf.continuousOn
  have hcont : ContinuousOn γ J := by
    have hprojCont : ContinuousOn (fun t => (f t).proj) J :=
      (FiberBundle.continuous_proj E (TangentSpace I)).comp_continuousOn hcontLift
    exact hprojCont.congr (fun t _ht => (hproj t).symm)
  exact ⟨hgeo, hcont, Geodesic.isGeodesicOn_contMDiffOn_infty
    (I := I) g hJ hgeo hcont⟩

omit [NeZero (Module.finrank ℝ E)]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [ConnectedSpace M] [CompleteSpace M] in
private lemma geo_init_deriv
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} {p : M} {v : TangentSpace I p}
    (hJ : IsOpen J) (h0J : (0 : ℝ) ∈ J)
    (hγ : IsGeodesicOnWithInitial (I := I) g γ J p v) :
    mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) = v := by
  obtain ⟨f, hproj, hf0, hf⟩ := hγ
  have hf_at : IsMIntegralCurveAt f (geodesicVectorField (I := I) g) 0 :=
    hf.isMIntegralCurveAt (hJ.mem_nhds h0J)
  have hproj_cont : ContinuousAt (fun t => (f t).proj) 0 :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp
      hf_at.continuousAt
  have hsrc0 : (f 0).proj ∈ (chartAt H p).source := by
    rw [hf0]
    exact mem_chart_source H p
  have hsrc : (fun t => (f t).proj) ⁻¹' (chartAt H p).source ∈ 𝓝 (0 : ℝ) :=
    hproj_cont.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hsrc0)
  have hf_chart :
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) 0 := by
    rw [isMIntegralCurveAt_iff]
    refine ⟨J ∩ (fun t => (f t).proj) ⁻¹' (chartAt H p).source,
      inter_mem (hJ.mem_nhds h0J) hsrc, ?_⟩
    apply (isMIntegralCurveOn_geodesicVectorFieldChart_iff (I := I) g p
      (fun _ ht => ht.2)).mpr
    exact hf.mono inter_subset_left
  have hvel := hf_chart.mfderiv_proj_one (I := I) hsrc0
  have hfun : (fun t => (f t).proj) = γ := funext hproj
  rw [hfun, hf0] at hvel
  exact hvel

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [IsManifold I ∞ M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [ConnectedSpace M] [CompleteSpace M] in
private lemma globalize_geo_seg
    {γ : ℝ → M} {J : Set ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hJ : IsOpen J) (hseg : Set.Icc (0 : ℝ) ℓ ⊆ J)
    (hγsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J) :
    ∃ γg : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γg ∧
      ∀ t ∈ Set.Icc (0 : ℝ) ℓ, γg =ᶠ[nhds t] γ := by
  obtain ⟨margin, hmargin, hbuffer⟩ :=
    isCompact_Icc.exists_cthickening_subset_open hJ hseg
  let a : ℝ := -(margin / 2)
  let d : ℝ := ℓ + margin / 2
  let eps : ℝ := margin / 4
  have ha0 : a < 0 := by dsimp only [a]; linarith
  have hℓd : ℓ < d := by dsimp only [d]; linarith
  have had : a < d := lt_trans ha0 (hℓ.trans hℓd)
  have heps : 0 < eps := by dsimp only [eps]; linarith
  obtain ⟨rho, hrho, hrho_id, _hrho_deriv, hrho_range⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp a d eps had heps
  have hrhoJ : ∀ s : ℝ, rho s ∈ J := by
    intro s
    apply hbuffer
    by_cases hs0 : rho s ≤ 0
    · refine Metric.mem_cthickening_of_dist_le (rho s) 0 margin
        (Set.Icc (0 : ℝ) ℓ) ⟨le_rfl, hℓ.le⟩ ?_
      rw [Real.dist_eq, sub_zero, abs_of_nonpos hs0]
      have hlo := (hrho_range s).1
      dsimp only [a, eps] at hlo
      linarith
    · by_cases hsℓ : rho s ≤ ℓ
      · refine Metric.mem_cthickening_of_dist_le (rho s) (rho s) margin
          (Set.Icc (0 : ℝ) ℓ) ⟨(not_le.mp hs0).le, hsℓ⟩ ?_
        simpa using hmargin.le
      · refine Metric.mem_cthickening_of_dist_le (rho s) ℓ margin
          (Set.Icc (0 : ℝ) ℓ) ⟨hℓ.le, le_rfl⟩ ?_
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (not_le.mp hsℓ).le)]
        have hhi := (hrho_range s).2
        dsimp only [d, eps] at hhi
        linarith
  have hrhoM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ rho := by
    rw [contMDiff_iff_contDiff]
    exact hrho
  let γg : ℝ → M := fun s => γ (rho s)
  have hγg : ContMDiff 𝓘(ℝ, ℝ) I ∞ γg :=
    hγsmooth.comp_contMDiff hrhoM hrhoJ
  refine ⟨γg, hγg, ?_⟩
  intro t ht
  have hIoo : Set.Ioo a d ∈ nhds t :=
    Ioo_mem_nhds (lt_of_lt_of_le ha0 ht.1) (lt_of_le_of_lt ht.2 hℓd)
  filter_upwards [hIoo] with s hs
  change γ (rho s) = γ s
  rw [hrho_id s ⟨hs.1.le, hs.2.le⟩]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [ConnectedSpace M] [CompleteSpace M] in
theorem minExp_of_cptBall
    [hNeZero : NeZero (Module.finrank ℝ E)] [hBoundaryless : I.Boundaryless]
    [hT2M : T2Space M] [hSigma : SigmaCompactSpace M]
    [hT2Tangent : T2Space (TangentBundle I M)]
    [hContinuous : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x)]
    [hRiemannian : IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p q : M) {R : ℝ}
    (hpqR : riemannianEDist I p q < ENNReal.ofReal R)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R))) :
    ∃ v : TangentSpace I p, v ∈ expDomain (I := I) g p ∧
      expMap (I := I) g p v = q ∧
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) = riemannianEDist I p q := by
  let _ := hNeZero
  let _ := hBoundaryless
  let _ := hT2M
  let _ := hSigma
  let _ := hT2Tangent
  let _ := hContinuous
  let _ := hRiemannian
  classical
  rcases eq_or_ne (riemannianEDist I p q) 0 with hpq0 | hpq0
  · have hpq : p = q := riemannianEDist_eq_zero_imp_eq (I := I) p q hpq0
    refine ⟨0, zero_mem_expDomain (I := I) g p, ?_, ?_⟩
    · rw [expMap_zero (I := I), hpq]
    · simp only [map_zero, Real.sqrt_zero, ENNReal.ofReal_zero, hpq0]
  · have hfin : riemannianEDist I p q ≠ ⊤ :=
      ne_of_lt (lt_trans hpqR ENNReal.ofReal_lt_top)
    let r : ℝ := (riemannianEDist I p q).toReal
    have hr_pos : 0 < r := ENNReal.toReal_pos hpq0 hfin
    have hpq : riemannianEDist I p q = ENNReal.ofReal r := by
      simpa only [r] using (ENNReal.ofReal_toReal hfin).symm
    have hrR : r < R := by
      rw [hpq] at hpqR
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr_pos.le).mp hpqR
    obtain ⟨δ, y, u, hδ_pos, hδr, hu, hδdom, hy, hpy, hyq, hdom⟩ :=
      sphere_jump_cpt (I := I) g hEnorm p q hr_pos hpq hcpt
    obtain ⟨γ, J, hJopen, hJconn, hsegJu, hγinit, hγexp⟩ :=
      Exponential.exists_isGeodesicOnWithInitial_eqOn_expMap (I := I) (g := g) (p := p) (v := u)
        (hdom hr_pos hrR)
    have hsegJ : Set.Icc (0 : ℝ) r ⊆ J := by
      simpa only [uIcc_of_le hr_pos.le] using hsegJu
    obtain ⟨hγgeo, hγcont, hγsmooth⟩ := geoOn_data (I := I) g hJopen hγinit
    have h0J : (0 : ℝ) ∈ J := hsegJ ⟨le_rfl, hr_pos.le⟩
    have hγzero : γ 0 = p := hγinit.start_eq
    have hγderiv : mfderiv (modelWithCornersSelf ℝ ℝ) I γ 0 (1 : ℝ) = u :=
      geo_init_deriv (I := I) g hJopen h0J hγinit
    have hγunit : ∀ t ∈ Set.Icc (0 : ℝ) r,
        g.inner (γ t) (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t 1)
          (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t 1) = 1 := by
      intro t ht
      have hsub : Set.Icc (min 0 t) (max 0 t) ⊆ J := by
        simpa [min_eq_left ht.1, max_eq_right ht.1] using
          (Set.Icc_subset_Icc le_rfl ht.2).trans hsegJ
      have hconst := HopfRinow.isGeodesicOn_speedSq_const (I := I) g hJopen hγgeo
        (hγsmooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) hsub
      rw [← hconst]
      subst p
      calc
        g.inner (γ 0) (mfderiv (modelWithCornersSelf ℝ ℝ) I γ 0 1)
            (mfderiv (modelWithCornersSelf ℝ ℝ) I γ 0 1) =
            g.inner (γ 0) u u :=
          congrArg (fun v : TangentSpace I (γ 0) => g.inner (γ 0) v v) hγderiv
        _ = 1 := hu
    let A : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) r ∧
      riemannianEDist I (γ t) q = ENNReal.ofReal (r - t)}
    have hAclosed : IsClosed A := by
      dsimp only [A]
      have hdist : ContinuousOn (fun t : ℝ => riemannianEDist I (γ t) q)
          (Set.Icc (0 : ℝ) r) := by
        have hdistM : Continuous (fun z : M => riemannianEDist I z q) := by
          simpa only [riemannianEDist_comm] using
            continuous_riemannianEDist_ambient (I := I) (M := M) q
        exact hdistM.comp_continuousOn (hγcont.mono hsegJ)
      have hrhs : ContinuousOn (fun t : ℝ => ENNReal.ofReal (r - t))
          (Set.Icc (0 : ℝ) r) :=
        ENNReal.continuous_ofReal.comp_continuousOn
          (continuous_const.sub continuous_id).continuousOn
      exact isClosed_Icc.isClosed_eq hdist hrhs
    have h0A : (0 : ℝ) ∈ A := by
      refine ⟨⟨le_rfl, hr_pos.le⟩, ?_⟩
      rw [hγzero, sub_zero, hpq]
    have hδA : δ ∈ A := by
      have hδIcc : δ ∈ Set.Icc (0 : ℝ) r := ⟨hδ_pos.le, hδr.le⟩
      refine ⟨hδIcc, ?_⟩
      rw [hγexp (hsegJ hδIcc)]
      change riemannianEDist I (expMap (I := I) g p (δ • u)) q = _
      rw [← hy, hyq]
    have hAne : A.Nonempty := ⟨0, h0A⟩
    have hAsub : A ⊆ Set.Icc (0 : ℝ) r := fun _ ht => ht.1
    have hAbdd : BddAbove A := ⟨r, fun _ ht => (hAsub ht).2⟩
    let t₀ : ℝ := sSup A
    have ht₀mem : t₀ ∈ A := hAclosed.csSup_mem hAne hAbdd
    have ht₀Icc : t₀ ∈ Set.Icc (0 : ℝ) r := hAsub ht₀mem
    have ht₀pos : 0 < t₀ :=
      lt_of_lt_of_le hδ_pos (le_csSup hAbdd hδA)
    have ht₀dist : riemannianEDist I (γ t₀) q = ENNReal.ofReal (r - t₀) :=
      ht₀mem.2
    have ht₀eq : t₀ = r := by
      by_contra ht₀ne
      have ht₀lt : t₀ < r := lt_of_le_of_ne ht₀Icc.2 ht₀ne
      let c : M := γ t₀
      let ρc : ℝ := r - t₀
      have hρc_pos : 0 < ρc := by dsimp only [ρc]; linarith
      have hcq : riemannianEDist I c q = ENNReal.ofReal ρc := by
        simpa only [c, ρc] using ht₀dist
      have hγspeed : ∀ t ∈ Set.Icc (0 : ℝ) r,
          ‖mfderiv (modelWithCornersSelf ℝ ℝ) I γ t (1 : ℝ)‖ₑ ≤ ENNReal.ofReal 1 := by
        intro t ht
        rw [hEnorm]
        apply ENNReal.ofReal_le_ofReal
        calc
          Real.sqrt (g.inner (γ t)
              (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t 1)
              (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t 1)) ≤ Real.sqrt 1 :=
            Real.sqrt_le_sqrt (hγunit t ht).le
          _ = 1 := Real.sqrt_one
      have hpc_le : riemannianEDist I p c ≤ ENNReal.ofReal t₀ := by
        have hdist := HopfRinow.curve_edist_le_speed_mul_time (I := I) (c := (1 : ℝ))
          zero_le_one ht₀Icc.1
          ((hγsmooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).mono
            ((Set.Icc_subset_Icc le_rfl ht₀Icc.2).trans hsegJ))
          (fun t ht => hγspeed t ⟨ht.1, ht.2.trans ht₀Icc.2⟩)
        simpa only [hγzero, c, one_mul, sub_zero] using hdist
      have hpc_ge : ENNReal.ofReal t₀ ≤ riemannianEDist I p c := by
        have htri : riemannianEDist I p q ≤
            riemannianEDist I p c + riemannianEDist I c q :=
          riemannianEDist_triangle
        rw [hpq, hcq] at htri
        have hsplit : ENNReal.ofReal r =
            ENNReal.ofReal t₀ + ENNReal.ofReal ρc := by
          rw [← ENNReal.ofReal_add ht₀Icc.1 hρc_pos.le]
          congr 1
          dsimp only [ρc]
          ring
        rw [hsplit] at htri
        exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp htri
      have hpc : riemannianEDist I p c = ENNReal.ofReal t₀ :=
        le_antisymm hpc_le hpc_ge
      have hRt₀ : 0 < R - t₀ := by linarith
      have hcptc : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
          (Metric.closedEBall c (ENNReal.ofReal (R - t₀))) := by
        have hclosed : @IsClosed M
            PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
            (Metric.closedEBall c (ENNReal.ofReal (R - t₀))) := by
          let _ : TopologicalSpace M :=
            PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
          exact Metric.isClosed_closedEBall
        apply @IsCompact.of_isClosed_subset M
          PseudoEMetricSpace.toUniformSpace.toTopologicalSpace _ _ hcpt hclosed
        intro z hz
        rw [Metric.mem_closedEBall'] at hz ⊢
        rw [IsRiemannianManifold.out (I := I) c z] at hz
        rw [IsRiemannianManifold.out (I := I) p z]
        have htri : riemannianEDist I p z ≤
            riemannianEDist I p c + riemannianEDist I c z :=
          riemannianEDist_triangle
        calc
          riemannianEDist I p z ≤ riemannianEDist I p c + riemannianEDist I c z := htri
          _ ≤ ENNReal.ofReal t₀ + ENNReal.ofReal (R - t₀) :=
            add_le_add hpc.le hz
          _ = ENNReal.ofReal R := by
            rw [← ENNReal.ofReal_add ht₀Icc.1 hRt₀.le]
            congr 1
            ring
      obtain ⟨δ', y₁, w₂, hδ'pos, hδ'ρc, hw₂, hδ'dom, hy₁, hcy₁, hy₁q, _⟩ :=
        sphere_jump_cpt (I := I) g hEnorm c q hρc_pos hcq hcptc
      obtain ⟨σ, Jσ, hJσopen, hJσconn, hsegJσu, hσinit, hσend⟩ :=
        Exponential.exists_isGeodesicOnWithInitial_eqOn_expMap (I := I) (g := g) (p := c) (v := w₂) hδ'dom
      have hsegJσ : Set.Icc (0 : ℝ) δ' ⊆ Jσ := by
        simpa only [uIcc_of_le hδ'pos.le] using hsegJσu
      obtain ⟨hσgeo, hσcont, hσsmooth⟩ := geoOn_data (I := I) g hJσopen hσinit
      have h0Jσ : (0 : ℝ) ∈ Jσ := hsegJσ ⟨le_rfl, hδ'pos.le⟩
      have hσzero : σ 0 = c := hσinit.start_eq
      have hσderiv : mfderiv (modelWithCornersSelf ℝ ℝ) I σ 0 (1 : ℝ) = w₂ :=
        geo_init_deriv (I := I) g hJσopen h0Jσ hσinit
      have hσunit : ∀ t ∈ Set.Icc (0 : ℝ) δ',
          g.inner (σ t) (mfderiv (modelWithCornersSelf ℝ ℝ) I σ t 1)
            (mfderiv (modelWithCornersSelf ℝ ℝ) I σ t 1) = 1 := by
        intro t ht
        have hsub : Set.Icc (min 0 t) (max 0 t) ⊆ Jσ := by
          simpa [min_eq_left ht.1, max_eq_right ht.1] using
            (Set.Icc_subset_Icc le_rfl ht.2).trans hsegJσ
        have hconst := HopfRinow.isGeodesicOn_speedSq_const (I := I) g hJσopen hσgeo
          (hσsmooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) hsub
        rw [← hconst]
        calc
          g.inner (σ 0) (mfderiv (modelWithCornersSelf ℝ ℝ) I σ 0 1)
              (mfderiv (modelWithCornersSelf ℝ ℝ) I σ 0 1) =
              g.inner (σ 0) w₂ w₂ :=
            congrArg (fun v : TangentSpace I (σ 0) => g.inner (σ 0) v v) hσderiv
          _ = g.inner c w₂ w₂ := by rw [hσzero]
          _ = 1 := hw₂
      have hpy₁_le : riemannianEDist I p y₁ ≤ ENNReal.ofReal (t₀ + δ') := by
        calc
          riemannianEDist I p y₁ ≤ riemannianEDist I p c + riemannianEDist I c y₁ :=
            riemannianEDist_triangle
          _ = ENNReal.ofReal t₀ + ENNReal.ofReal δ' := by rw [hpc, hcy₁]
          _ = ENNReal.ofReal (t₀ + δ') :=
            (ENNReal.ofReal_add ht₀Icc.1 hδ'pos.le).symm
      have hpy₁_ge : ENNReal.ofReal (t₀ + δ') ≤ riemannianEDist I p y₁ := by
        have htri : riemannianEDist I p q ≤
            riemannianEDist I p y₁ + riemannianEDist I y₁ q :=
          riemannianEDist_triangle
        rw [hpq, hy₁q] at htri
        have hsplit : ENNReal.ofReal r = ENNReal.ofReal (t₀ + δ') +
            ENNReal.ofReal (ρc - δ') := by
          rw [← ENNReal.ofReal_add (by positivity) (sub_nonneg.mpr hδ'ρc.le)]
          congr 1
          dsimp only [ρc]
          ring
        rw [hsplit] at htri
        exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp htri
      have hpy₁ : riemannianEDist I p y₁ = ENNReal.ofReal (t₀ + δ') :=
        le_antisymm hpy₁_le hpy₁_ge
      have hσδ' : σ δ' = y₁ :=
        (hσend (hsegJσ ⟨hδ'pos.le, le_rfl⟩)).trans hy₁.symm
      obtain ⟨γg, hγgSmooth, hγgerm⟩ :=
        globalize_geo_seg (I := I) hr_pos hJopen hsegJ hγsmooth
      obtain ⟨σg, hσgSmooth, hσgerm⟩ :=
        globalize_geo_seg (I := I) hδ'pos hJσopen hsegJσ hσsmooth
      have hγgGeo : IsGeodesicOn (I := I) g γg (Set.Icc 0 t₀) := by
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) r := ⟨ht.1, ht.2.trans ht₀Icc.2⟩
        have heq := hγgerm t ht'
        exact HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
          heq.eq_of_nhds heq (hγgeo t (hsegJ ht'))
      have hσgGeo : IsGeodesicOn (I := I) g σg (Set.Icc 0 δ') := by
        intro t ht
        have heq := hσgerm t ht
        exact HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
          heq.eq_of_nhds heq (hσgeo t (hsegJσ ht))
      have hγgUnit : ∀ t ∈ Set.Icc (0 : ℝ) t₀,
          g.inner (γg t) (mfderiv (modelWithCornersSelf ℝ ℝ) I γg t 1)
            (mfderiv (modelWithCornersSelf ℝ ℝ) I γg t 1) = 1 := by
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) r := ⟨ht.1, ht.2.trans ht₀Icc.2⟩
        have heq := hγgerm t ht'
        rw [heq.eq_of_nhds, heq.mfderiv_eq]
        exact hγunit t ht'
      have hσgUnit : ∀ t ∈ Set.Icc (0 : ℝ) δ',
          g.inner (σg t) (mfderiv (modelWithCornersSelf ℝ ℝ) I σg t 1)
            (mfderiv (modelWithCornersSelf ℝ ℝ) I σg t 1) = 1 := by
        intro t ht
        have heq := hσgerm t ht
        rw [heq.eq_of_nhds, heq.mfderiv_eq]
        exact hσunit t ht
      have hjuncg : γg t₀ = σg 0 := by
        rw [(hγgerm t₀ ht₀Icc).eq_of_nhds,
          (hσgerm 0 ⟨le_rfl, hδ'pos.le⟩).eq_of_nhds, hσzero]
      have hming : riemannianEDist I (γg 0) (σg δ') =
          ENNReal.ofReal (t₀ + δ') := by
        rw [(hγgerm 0 ⟨le_rfl, hr_pos.le⟩).eq_of_nhds,
          (hσgerm δ' ⟨hδ'pos.le, le_rfl⟩).eq_of_nhds,
          hγzero, hσδ']
        exact hpy₁
      have hvmatchg := Exponential.broken_minimizer_velocity_match (I := I) g hEnorm
        ht₀pos hδ'pos hγgGeo hσgGeo hγgSmooth hσgSmooth
        hγgUnit hσgUnit hjuncg hming
      have hvmatch : mfderiv (modelWithCornersSelf ℝ ℝ) I γ t₀ (1 : ℝ) =
          mfderiv (modelWithCornersSelf ℝ ℝ) I σ 0 (1 : ℝ) := by
        rw [← (hγgerm t₀ ht₀Icc).mfderiv_eq,
          ← (hσgerm 0 ⟨le_rfl, hδ'pos.le⟩).mfderiv_eq]
        exact hvmatchg
      have hγlift := Geodesic.isMIntegralCurveOn_velocityLift (I := I) g hJopen hγgeo hγcont
      have hσlift := Geodesic.isMIntegralCurveOn_velocityLift (I := I) g hJσopen hσgeo hσcont
      let Jshift : Set ℝ := {s : ℝ | s + t₀ ∈ J}
      let K : Set ℝ := Jshift ∩ Jσ
      have hJshiftOpen : IsOpen Jshift :=
        hJopen.preimage (continuous_id.add continuous_const)
      have hJshiftConn : IsPreconnected Jshift :=
        (hJconn.ordConnected.preimage_mono (f := fun s : ℝ => s + t₀)
          (fun _ _ hst => by linarith)).isPreconnected
      have hKopen : IsOpen K := hJshiftOpen.inter hJσopen
      have hKconn : IsPreconnected K :=
        (hJshiftConn.ordConnected.inter hJσconn.ordConnected).isPreconnected
      have h0K : (0 : ℝ) ∈ K := by
        refine ⟨?_, h0Jσ⟩
        change 0 + t₀ ∈ J
        simpa using hsegJ ht₀Icc
      have hδ'K : δ' ∈ K := by
        refine ⟨?_, hsegJσ ⟨hδ'pos.le, le_rfl⟩⟩
        change δ' + t₀ ∈ J
        apply hsegJ
        constructor
        · positivity
        · rw [add_comm]
          dsimp only [ρc] at hδ'ρc
          linarith
      have hLift0 :
          (velocityLift (I := I) γ ∘ fun s : ℝ => s + t₀) 0 =
            velocityLift (I := I) σ 0 := by
        simp only [Function.comp_apply, zero_add]
        apply TotalSpace.ext
        · exact hσzero.symm
        · apply heq_of_eq
          exact hvmatch
      have hliftEq := Geodesic.integralCurve_eqOn (I := I) g hKopen hKconn h0K
        ((hγlift.comp_add t₀).mono inter_subset_left)
        (hσlift.mono inter_subset_right) hLift0
      have hcontinue : γ (t₀ + δ') = y₁ := by
        have hprojEq := congrArg (fun z : TangentBundle I M => z.proj) (hliftEq hδ'K)
        simp only [Function.comp_apply, velocityLift_proj] at hprojEq
        rw [add_comm, hprojEq, hσδ']
      have hnewA : t₀ + δ' ∈ A := by
        have hnewIcc : t₀ + δ' ∈ Set.Icc (0 : ℝ) r := by
          constructor
          · positivity
          · dsimp only [ρc] at hδ'ρc
            linarith
        refine ⟨hnewIcc, ?_⟩
        rw [hcontinue, hy₁q]
        congr 1
        dsimp only [ρc]
        ring
      have := le_csSup hAbdd hnewA
      linarith
    have hrA : r ∈ A := by simpa only [ht₀eq] using ht₀mem
    have hγr : γ r = q := by
      have hzero : riemannianEDist I (γ r) q = 0 := by
        simpa only [sub_self, ENNReal.ofReal_zero] using hrA.2
      exact riemannianEDist_eq_zero_imp_eq (I := I) (γ r) q hzero
    refine ⟨r • u, hdom hr_pos hrR, ?_, ?_⟩
    · exact (hγexp (hsegJ ⟨hr_pos.le, le_rfl⟩)).symm.trans hγr
    · rw [sqrt_gInner_smul_self (I := I) g p hr_pos.le u, hu,
        Real.sqrt_one, mul_one]
      exact hpq.symm

end RadialSurjectivity
end Riemannian
end Geometry
end DifferentialGeometry

end
