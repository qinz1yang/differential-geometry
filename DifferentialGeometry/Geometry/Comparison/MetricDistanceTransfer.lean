import DifferentialGeometry.Geometry.Comparison.BallCapture
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Filter Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Riemannian
open scoped Topology Manifold ContDiff ENNReal

section Maps

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricPathELength_map_le (h : SmoothRiemannianMetric J N)
    (g : SmoothRiemannianMetric I M) (F : N → M)
    {gamma : ℝ → N} {a b L : ℝ} (hL : 0 ≤ L)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) J 1 gamma (Icc a b))
    (hF : ∀ s ∈ Ioo a b, MDifferentiableAt J I F (gamma s))
    (hupper : ∀ s ∈ Ioo a b, ∀ v : TangentSpace J (gamma s),
      g.inner (F (gamma s)) (mfderiv J I F (gamma s) v)
        (mfderiv J I F (gamma s) v) ≤ L ^ 2 * h.inner (gamma s) v v) :
    metricPathELength g (F ∘ gamma) a b ≤
      ENNReal.ofReal L * metricPathELength h gamma a b := by
  rw [metricPathELength_eq, metricPathELength_eq,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  have hgd := (hgamma.contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  rw [← ENNReal.ofReal_mul hL]
  apply ENNReal.ofReal_le_ofReal
  change Real.sqrt (g.inner (F (gamma s))
    (mfderiv 𝓘(ℝ, ℝ) I (F ∘ gamma) s 1)
    (mfderiv 𝓘(ℝ, ℝ) I (F ∘ gamma) s 1)) ≤ _
  rw [mfderiv_comp_apply s (hF s hs) hgd]
  calc
    _ ≤ Real.sqrt (L ^ 2 * h.inner (gamma s)
        (mfderiv 𝓘(ℝ, ℝ) J gamma s 1) (mfderiv 𝓘(ℝ, ℝ) J gamma s 1)) :=
      Real.sqrt_le_sqrt (hupper s hs _)
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricPathELength_map_ge (h : SmoothRiemannianMetric J N)
    (g : SmoothRiemannianMetric I M) (F : N → M)
    {gamma : ℝ → N} {a b L : ℝ} (hL : 0 ≤ L)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) J 1 gamma (Icc a b))
    (hF : ∀ s ∈ Ioo a b, MDifferentiableAt J I F (gamma s))
    (hlower : ∀ s ∈ Ioo a b, ∀ v : TangentSpace J (gamma s),
      L ^ 2 * h.inner (gamma s) v v ≤
        g.inner (F (gamma s)) (mfderiv J I F (gamma s) v)
          (mfderiv J I F (gamma s) v)) :
    ENNReal.ofReal L * metricPathELength h gamma a b ≤
      metricPathELength g (F ∘ gamma) a b := by
  rw [metricPathELength_eq, metricPathELength_eq,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  have hgd := (hgamma.contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  rw [← ENNReal.ofReal_mul hL]
  apply ENNReal.ofReal_le_ofReal
  change _ ≤ Real.sqrt (g.inner (F (gamma s))
    (mfderiv 𝓘(ℝ, ℝ) I (F ∘ gamma) s 1)
    (mfderiv 𝓘(ℝ, ℝ) I (F ∘ gamma) s 1))
  rw [mfderiv_comp_apply s (hF s hs) hgd]
  calc
    _ = Real.sqrt (L ^ 2 * h.inner (gamma s)
        (mfderiv 𝓘(ℝ, ℝ) J gamma s 1) (mfderiv 𝓘(ℝ, ℝ) J gamma s 1)) := by
      rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]
    _ ≤ _ := Real.sqrt_le_sqrt (hlower s hs _)

end Maps

section CrossModel

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem edistOf_triangle (g : SmoothRiemannianMetric I M) (x y z : M) :
    riemannianEDistOf (I := I) g x z ≤
      riemannianEDistOf (I := I) g x y + riemannianEDistOf (I := I) g y z := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem edistOf_comm (g : SmoothRiemannianMetric I M) (x y : M) :
    riemannianEDistOf (I := I) g x y = riemannianEDistOf (I := I) g y x := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem metricPathELength_congr_curve (g : SmoothRiemannianMetric I M)
    {gamma gamma' : ℝ → M} {a b : ℝ} (heq : EqOn gamma gamma' (Icc a b)) :
    metricPathELength (I := I) g gamma a b = metricPathELength (I := I) g gamma' a b := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.pathELength_congr heq


private theorem edistOf_le_of_mem_closedBall (h : SmoothRiemannianMetric J N) (p : N)
    {rho : ℝ} (hrho : 0 ≤ rho) {a b : N}
    (ha : a ∈ riemannianClosedBallOf h p rho) (hb : b ∈ riemannianClosedBallOf h p rho) :
    riemannianEDistOf (I := J) h a b ≤ ENNReal.ofReal (rho + rho) := by
  have ha' : riemannianEDistOf (I := J) h p a ≤ ENNReal.ofReal rho := ha
  have hb' : riemannianEDistOf (I := J) h p b ≤ ENNReal.ofReal rho := hb
  calc riemannianEDistOf (I := J) h a b
      ≤ riemannianEDistOf (I := J) h a p + riemannianEDistOf (I := J) h p b :=
        edistOf_triangle h a p b
    _ = riemannianEDistOf (I := J) h p a + riemannianEDistOf (I := J) h p b := by
        rw [edistOf_comm h a p]
    _ ≤ ENNReal.ofReal rho + ENNReal.ofReal rho := add_le_add ha' hb'
    _ = ENNReal.ofReal (rho + rho) := (ENNReal.ofReal_add hrho hrho).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem crossModel_edist_le_of_metric_upper
    (h : SmoothRiemannianMetric J N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph J I N M ∞) (p : N) {R L rho : ℝ}
    (hL : 0 < L) (hrho : 0 ≤ rho) (hroom : 3 * rho < R)
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hupper : ∀ y ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace J y,
      g.inner (F y) (mfderiv J I (F : N → M) y v) (mfderiv J I (F : N → M) y v) ≤
        L ^ 2 * h.inner y v v)
    {a b : N} (ha : a ∈ riemannianClosedBallOf h p rho)
    (hb : b ∈ riemannianClosedBallOf h p rho) :
    riemannianEDistOf (I := I) g (F a) (F b) ≤
      ENNReal.ofReal L * riemannianEDistOf (I := J) h a b := by
  have ha' : riemannianEDistOf (I := J) h p a ≤ ENNReal.ofReal rho := ha
  have hkey : ∀ r : ℝ, riemannianEDistOf (I := J) h a b < ENNReal.ofReal r →
      rho + r ≤ R →
      riemannianEDistOf (I := I) g (F a) (F b) ≤ ENNReal.ofReal L * ENNReal.ofReal r := by
    intro r hr hrR
    have hr0 : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (by simp) hr)
    obtain ⟨gamma, hstart, hend, hgamma, hlen⟩ := exists_lt_of_edistOf_lt h hr
    have hstay : ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ riemannianClosedBallOf h p R := by
      intro s hs
      have hd := edistOf_le_metricPathELength h hs.1
        (hgamma.mono (Icc_subset_Icc le_rfl hs.2))
      rw [hstart] at hd
      have h1 : riemannianEDistOf (I := J) h a (gamma s) ≤ ENNReal.ofReal r :=
        ((hd.trans (metricPathELength_mono h gamma le_rfl hs.2)).trans_lt hlen).le
      change riemannianEDistOf (I := J) h p (gamma s) ≤ ENNReal.ofReal R
      calc riemannianEDistOf (I := J) h p (gamma s)
          ≤ riemannianEDistOf (I := J) h p a + riemannianEDistOf (I := J) h a (gamma s) :=
            edistOf_triangle h p a (gamma s)
        _ ≤ ENNReal.ofReal rho + ENNReal.ofReal r := add_le_add ha' h1
        _ = ENNReal.ofReal (rho + r) := (ENNReal.ofReal_add hrho hr0.le).symm
        _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal hrR
    have hFgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 ((F : N → M) ∘ gamma) (Icc 0 1) :=
      (F.contMDiffOn_toFun.of_le (by simp)).comp hgamma fun s hs => hsource (hstay s hs)
    have hlength := metricPathELength_map_le h g (F : N → M) hL.le hgamma
      (fun s hs => F.mdifferentiableAt (by simp) (hsource (hstay s ⟨hs.1.le, hs.2.le⟩)))
      (fun s hs => hupper (gamma s) (hstay s ⟨hs.1.le, hs.2.le⟩))
    have hd := edistOf_le_metricPathELength g (by norm_num : (0 : ℝ) ≤ 1) hFgamma
    simp only [Function.comp_apply, hstart, hend] at hd
    calc riemannianEDistOf (I := I) g (F a) (F b)
        ≤ metricPathELength (I := I) g ((F : N → M) ∘ gamma) 0 1 := hd
      _ ≤ ENNReal.ofReal L * metricPathELength (I := J) h gamma 0 1 := hlength
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal r := mul_le_mul' le_rfl hlen.le
  have hab := edistOf_le_of_mem_closedBall h p hrho ha hb
  have habfin : riemannianEDistOf (I := J) h a b ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hab
  obtain ⟨D, hD0, hDeq⟩ : ∃ D : ℝ, 0 ≤ D ∧
      riemannianEDistOf (I := J) h a b = ENNReal.ofReal D :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal habfin).symm⟩
  rw [hDeq] at hab ⊢
  have hDle : D ≤ rho + rho :=
    (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hab
  rw [← ENNReal.ofReal_mul hL.le]
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro eta heta _
  have hetaR : (0 : ℝ) < (eta : ℝ) := heta
  have hdpos : 0 < min (R - 3 * rho) ((eta : ℝ) / L) :=
    lt_min (by linarith) (div_pos hetaR hL)
  have hd1 : min (R - 3 * rho) ((eta : ℝ) / L) ≤ R - 3 * rho := min_le_left _ _
  have hd2 : min (R - 3 * rho) ((eta : ℝ) / L) ≤ (eta : ℝ) / L := min_le_right _ _
  have hmul : L * min (R - 3 * rho) ((eta : ℝ) / L) ≤ (eta : ℝ) := by
    have h2 := mul_le_mul_of_nonneg_left hd2 hL.le
    have h3 : L * ((eta : ℝ) / L) = (eta : ℝ) := by field_simp
    linarith
  have hstep := hkey (D + min (R - 3 * rho) ((eta : ℝ) / L))
    (by rw [hDeq]; exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hD0).mpr (by linarith))
    (by linarith)
  refine hstep.trans ?_
  rw [← ENNReal.ofReal_mul hL.le,
    show L * (D + min (R - 3 * rho) ((eta : ℝ) / L)) =
      L * D + L * min (R - 3 * rho) ((eta : ℝ) / L) from by ring]
  refine ENNReal.ofReal_add_le.trans (add_le_add le_rfl ?_)
  calc ENNReal.ofReal (L * min (R - 3 * rho) ((eta : ℝ) / L))
      ≤ ENNReal.ofReal ((eta : ℝ)) := ENNReal.ofReal_le_ofReal hmul
    _ = (eta : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem crossModel_edist_ge_of_metric_equiv [FiniteDimensional ℝ E'] [T2Space M] [T2Space N]
    (h : SmoothRiemannianMetric J N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph J I N M ∞) (p : N) {R eps rho : ℝ}
    (hR : 0 < R) (heps0 : 0 ≤ eps) (heps1 : eps < 1) (hrho : 0 ≤ rho)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hequiv : ∀ y ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace J y,
      (1 - eps) * h.inner y v v ≤
          g.inner (F y) (mfderiv J I (F : N → M) y v) (mfderiv J I (F : N → M) y v) ∧
        g.inner (F y) (mfderiv J I (F : N → M) y v) (mfderiv J I (F : N → M) y v) ≤
          (1 + eps) * h.inner y v v)
    (hroom : Real.sqrt (1 + eps) * (3 * rho) < Real.sqrt (1 - eps) * R)
    {a b : N} (ha : a ∈ riemannianClosedBallOf h p rho)
    (hb : b ∈ riemannianClosedBallOf h p rho) :
    ENNReal.ofReal (Real.sqrt (1 - eps)) * riemannianEDistOf (I := J) h a b ≤
      riemannianEDistOf (I := I) g (F a) (F b) := by
  have h1e : (0 : ℝ) < 1 - eps := by linarith
  have hLm : (0 : ℝ) < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr h1e
  have hLp : (0 : ℝ) < Real.sqrt (1 + eps) := Real.sqrt_pos.mpr (by linarith)
  have hLm1 : Real.sqrt (1 - eps) ≤ 1 := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) - eps ≤ 1 by linarith)
    rwa [Real.sqrt_one] at this
  have hLp1 : (1 : ℝ) ≤ Real.sqrt (1 + eps) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + eps by linarith)
    rwa [Real.sqrt_one] at this
  have h3rho : 3 * rho < R := by
    have h1 : 3 * rho ≤ Real.sqrt (1 + eps) * (3 * rho) := by nlinarith
    have h2 : Real.sqrt (1 - eps) * R ≤ R := by nlinarith
    linarith
  have hrhoR : rho ≤ R := by linarith
  have hRmem := riemannianClosedBallOf_mono h p hrhoR
  have hupper : ∀ y ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace J y,
      g.inner (F y) (mfderiv J I (F : N → M) y v) (mfderiv J I (F : N → M) y v) ≤
        Real.sqrt (1 + eps) ^ 2 * h.inner y v v := by
    intro y hy v
    rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + eps)]
    exact (hequiv y hy v).2
  have hpmem : p ∈ riemannianClosedBallOf h p rho := by
    change riemannianEDistOf (I := J) h p p ≤ ENNReal.ofReal rho
    rw [riemannianEDistOf_self]
    exact bot_le
  have hpa : riemannianEDistOf (I := I) g (F p) (F a) ≤
      ENNReal.ofReal (Real.sqrt (1 + eps) * rho) := by
    have ha' : riemannianEDistOf (I := J) h p a ≤ ENNReal.ofReal rho := ha
    calc riemannianEDistOf (I := I) g (F p) (F a)
        ≤ ENNReal.ofReal (Real.sqrt (1 + eps)) * riemannianEDistOf (I := J) h p a :=
          crossModel_edist_le_of_metric_upper h g F p hLp hrho h3rho hsource hupper hpmem ha
      _ ≤ ENNReal.ofReal (Real.sqrt (1 + eps)) * ENNReal.ofReal rho := mul_le_mul' le_rfl ha'
      _ = ENNReal.ofReal (Real.sqrt (1 + eps) * rho) := (ENNReal.ofReal_mul hLp.le).symm
  have hgab : riemannianEDistOf (I := I) g (F a) (F b) ≤
      ENNReal.ofReal (Real.sqrt (1 + eps) * (rho + rho)) := by
    calc riemannianEDistOf (I := I) g (F a) (F b)
        ≤ ENNReal.ofReal (Real.sqrt (1 + eps)) * riemannianEDistOf (I := J) h a b :=
          crossModel_edist_le_of_metric_upper h g F p hLp hrho h3rho hsource hupper ha hb
      _ ≤ ENNReal.ofReal (Real.sqrt (1 + eps)) * ENNReal.ofReal (rho + rho) :=
          mul_le_mul' le_rfl (edistOf_le_of_mem_closedBall h p hrho ha hb)
      _ = ENNReal.ofReal (Real.sqrt (1 + eps) * (rho + rho)) :=
          (ENNReal.ofReal_mul hLp.le).symm
  have hne : (1 : ℝ) - eps ≠ 0 := ne_of_gt h1e
  have hLinv : (0 : ℝ) < (Real.sqrt (1 - eps))⁻¹ := inv_pos.mpr hLm
  have hlow : ∀ y ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace J y,
      h.inner y v v ≤ ((Real.sqrt (1 - eps))⁻¹) ^ 2 *
        g.inner (F y) (mfderiv J I (F : N → M) y v) (mfderiv J I (F : N → M) y v) := by
    intro y hy v
    rw [inv_pow, Real.sq_sqrt h1e.le]
    calc h.inner y v v = (1 - eps)⁻¹ * ((1 - eps) * h.inner y v v) := by
          rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      _ ≤ (1 - eps)⁻¹ *
            g.inner (F y) (mfderiv J I (F : N → M) y v) (mfderiv J I (F : N → M) y v) :=
          mul_le_mul_of_nonneg_left (hequiv y hy v).1 (inv_pos.mpr h1e).le
  have hcapture : riemannianBallOf (I := I) g (F p) (Real.sqrt (1 - eps) * R) ⊆
      (F : N → M) '' riemannianClosedBallOf h p R := by
    have hmain :=
      _root_.DifferentialGeometry.PartialDiffeomorph.ball_subset_image_closedBall_of_metric_lower h g F p hR hLinv hcpt hsource hlow
    have hrad : R / (Real.sqrt (1 - eps))⁻¹ = Real.sqrt (1 - eps) * R := by
      rw [div_eq_mul_inv, inv_inv]; ring
    rwa [hrad] at hmain
  have hkey : ∀ r : ℝ, riemannianEDistOf (I := I) g (F a) (F b) < ENNReal.ofReal r →
      Real.sqrt (1 + eps) * rho + r < Real.sqrt (1 - eps) * R →
      ENNReal.ofReal (Real.sqrt (1 - eps)) * riemannianEDistOf (I := J) h a b ≤
        ENNReal.ofReal r := by
    intro r hr hrR
    have hr0 : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (by simp) hr)
    obtain ⟨gamma, hstart, hend, hgamma, hlen⟩ := exists_lt_of_edistOf_lt g hr
    have hstay : ∀ s ∈ Icc (0 : ℝ) 1,
        gamma s ∈ (F : N → M) '' riemannianClosedBallOf h p R := by
      intro s hs
      apply hcapture
      have hd := edistOf_le_metricPathELength g hs.1
        (hgamma.mono (Icc_subset_Icc le_rfl hs.2))
      rw [hstart] at hd
      have h1 : riemannianEDistOf (I := I) g (F a) (gamma s) ≤ ENNReal.ofReal r :=
        ((hd.trans (metricPathELength_mono g gamma le_rfl hs.2)).trans_lt hlen).le
      change riemannianEDistOf (I := I) g (F p) (gamma s) <
        ENNReal.ofReal (Real.sqrt (1 - eps) * R)
      calc riemannianEDistOf (I := I) g (F p) (gamma s)
          ≤ riemannianEDistOf (I := I) g (F p) (F a) +
              riemannianEDistOf (I := I) g (F a) (gamma s) :=
            edistOf_triangle g (F p) (F a) (gamma s)
        _ ≤ ENNReal.ofReal (Real.sqrt (1 + eps) * rho) + ENNReal.ofReal r :=
            add_le_add hpa h1
        _ = ENNReal.ofReal (Real.sqrt (1 + eps) * rho + r) :=
            (ENNReal.ofReal_add (by positivity) hr0.le).symm
        _ < ENNReal.ofReal (Real.sqrt (1 - eps) * R) :=
            (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hrR
    have htarget : ∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ F.target := by
      intro s hs
      obtain ⟨y, hy, hFy⟩ := hstay s hs
      rw [← hFy]
      exact F.map_source' (hsource hy)
    have hbmem : ∀ s ∈ Icc (0 : ℝ) 1,
        ((F.symm : M → N) ∘ gamma) s ∈ riemannianClosedBallOf h p R := by
      intro s hs
      obtain ⟨y, hy, hFy⟩ := hstay s hs
      have hleft : (F.symm : M → N) ((F : N → M) y) = y := F.left_inv' (hsource hy)
      change (F.symm : M → N) (gamma s) ∈ riemannianClosedBallOf h p R
      rw [← hFy, hleft]
      exact hy
    have hbsmooth : ContMDiffOn 𝓘(ℝ, ℝ) J 1 ((F.symm : M → N) ∘ gamma) (Icc 0 1) :=
      (F.symm.contMDiffOn_toFun.of_le (by simp)).comp hgamma fun s hs => htarget s hs
    have hFbeta : ∀ s ∈ Icc (0 : ℝ) 1,
        ((F : N → M) ∘ (F.symm : M → N) ∘ gamma) s = gamma s :=
      fun s hs => F.right_inv' (htarget s hs)
    have ha0 : ((F.symm : M → N) ∘ gamma) 0 = a := by
      have hleft : (F.symm : M → N) ((F : N → M) a) = a := F.left_inv' (hsource (hRmem ha))
      change (F.symm : M → N) (gamma 0) = a
      rw [hstart, hleft]
    have hb1 : ((F.symm : M → N) ∘ gamma) 1 = b := by
      have hleft : (F.symm : M → N) ((F : N → M) b) = b := F.left_inv' (hsource (hRmem hb))
      change (F.symm : M → N) (gamma 1) = b
      rw [hend, hleft]
    have hlengthge := metricPathELength_map_ge h g (F : N → M) (Real.sqrt_nonneg _) hbsmooth
      (fun s hs => F.mdifferentiableAt (by simp) (hsource (hbmem s ⟨hs.1.le, hs.2.le⟩)))
      (fun s hs v => by
        rw [Real.sq_sqrt h1e.le]
        exact (hequiv (((F.symm : M → N) ∘ gamma) s)
          (hbmem s ⟨hs.1.le, hs.2.le⟩) v).1)
    have hsame : metricPathELength (I := I) g ((F : N → M) ∘ (F.symm : M → N) ∘ gamma) 0 1 =
        metricPathELength (I := I) g gamma 0 1 :=
      metricPathELength_congr_curve g fun s hs => hFbeta s hs
    have hdistb := edistOf_le_metricPathELength h (by norm_num : (0 : ℝ) ≤ 1) hbsmooth
    rw [ha0, hb1] at hdistb
    calc ENNReal.ofReal (Real.sqrt (1 - eps)) * riemannianEDistOf (I := J) h a b
        ≤ ENNReal.ofReal (Real.sqrt (1 - eps)) *
            metricPathELength (I := J) h ((F.symm : M → N) ∘ gamma) 0 1 :=
          mul_le_mul' le_rfl hdistb
      _ ≤ metricPathELength (I := I) g ((F : N → M) ∘ (F.symm : M → N) ∘ gamma) 0 1 :=
          hlengthge
      _ = metricPathELength (I := I) g gamma 0 1 := hsame
      _ ≤ ENNReal.ofReal r := hlen.le
  have hgfin : riemannianEDistOf (I := I) g (F a) (F b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgab
  obtain ⟨Dg, hDg0, hDgeq⟩ : ∃ D : ℝ, 0 ≤ D ∧
      riemannianEDistOf (I := I) g (F a) (F b) = ENNReal.ofReal D :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hgfin).symm⟩
  have hDgle : Dg ≤ Real.sqrt (1 + eps) * (rho + rho) := by
    rw [hDgeq] at hgab
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hgab
  have hLpid : Real.sqrt (1 + eps) * rho + Real.sqrt (1 + eps) * (rho + rho) =
      Real.sqrt (1 + eps) * (3 * rho) := by ring
  rw [hDgeq]
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro eta heta _
  have hetaR : (0 : ℝ) < (eta : ℝ) := heta
  have hdpos : 0 < min ((Real.sqrt (1 - eps) * R - Real.sqrt (1 + eps) * (3 * rho)) / 2)
      ((eta : ℝ)) := lt_min (by linarith) hetaR
  have hd1 : min ((Real.sqrt (1 - eps) * R - Real.sqrt (1 + eps) * (3 * rho)) / 2)
      ((eta : ℝ)) ≤ (Real.sqrt (1 - eps) * R - Real.sqrt (1 + eps) * (3 * rho)) / 2 :=
    min_le_left _ _
  have hstep := hkey (Dg + min ((Real.sqrt (1 - eps) * R -
      Real.sqrt (1 + eps) * (3 * rho)) / 2) ((eta : ℝ)))
    (by rw [hDgeq]; exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hDg0).mpr (by linarith))
    (by linarith)
  refine hstep.trans (ENNReal.ofReal_add_le.trans (add_le_add le_rfl ?_))
  calc ENNReal.ofReal (min ((Real.sqrt (1 - eps) * R -
        Real.sqrt (1 + eps) * (3 * rho)) / 2) ((eta : ℝ)))
      ≤ ENNReal.ofReal ((eta : ℝ)) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = (eta : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem crossModel_edist_transfer [FiniteDimensional ℝ E'] [T2Space M] [T2Space N]
    (h : SmoothRiemannianMetric J N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph J I N M ∞) (p : N) {R eps rho : ℝ}
    (hR : 0 < R) (heps0 : 0 ≤ eps) (heps1 : eps < 1) (hrho : 0 ≤ rho)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hequiv : ∀ y ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace J y,
      (1 - eps) * h.inner y v v ≤
          g.inner (F y) (mfderiv J I (F : N → M) y v) (mfderiv J I (F : N → M) y v) ∧
        g.inner (F y) (mfderiv J I (F : N → M) y v) (mfderiv J I (F : N → M) y v) ≤
          (1 + eps) * h.inner y v v)
    (hroom : Real.sqrt (1 + eps) * (3 * rho) < Real.sqrt (1 - eps) * R) :
    ∀ a ∈ riemannianClosedBallOf h p rho, ∀ b ∈ riemannianClosedBallOf h p rho,
      ENNReal.ofReal (Real.sqrt (1 - eps)) * riemannianEDistOf (I := J) h a b ≤
          riemannianEDistOf (I := I) g (F a) (F b) ∧
        riemannianEDistOf (I := I) g (F a) (F b) ≤
          ENNReal.ofReal (Real.sqrt (1 + eps)) * riemannianEDistOf (I := J) h a b := by
  have hLp : (0 : ℝ) < Real.sqrt (1 + eps) := Real.sqrt_pos.mpr (by linarith)
  have hLm1 : Real.sqrt (1 - eps) ≤ 1 := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) - eps ≤ 1 by linarith)
    rwa [Real.sqrt_one] at this
  have hLp1 : (1 : ℝ) ≤ Real.sqrt (1 + eps) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + eps by linarith)
    rwa [Real.sqrt_one] at this
  have h3rho : 3 * rho < R := by
    have h1 : 3 * rho ≤ Real.sqrt (1 + eps) * (3 * rho) := by nlinarith
    have h2 : Real.sqrt (1 - eps) * R ≤ R := by nlinarith
    linarith
  have hupper : ∀ y ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace J y,
      g.inner (F y) (mfderiv J I (F : N → M) y v) (mfderiv J I (F : N → M) y v) ≤
        Real.sqrt (1 + eps) ^ 2 * h.inner y v v := by
    intro y hy v
    rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + eps)]
    exact (hequiv y hy v).2
  intro a ha b hb
  exact ⟨crossModel_edist_ge_of_metric_equiv h g F p hR heps0 heps1 hrho hcpt hsource
      hequiv hroom ha hb,
    crossModel_edist_le_of_metric_upper h g F p hLp hrho h3rho hsource hupper ha hb⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem crossModel_toReal_transfer [FiniteDimensional ℝ E'] [T2Space M] [T2Space N]
    (h : SmoothRiemannianMetric J N) (g : SmoothRiemannianMetric I M)
    (F : PartialDiffeomorph J I N M ∞) (p : N) {R eps rho : ℝ}
    (hR : 0 < R) (heps0 : 0 ≤ eps) (heps1 : eps < 1) (hrho : 0 ≤ rho)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hequiv : ∀ y ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace J y,
      (1 - eps) * h.inner y v v ≤
          g.inner (F y) (mfderiv J I (F : N → M) y v) (mfderiv J I (F : N → M) y v) ∧
        g.inner (F y) (mfderiv J I (F : N → M) y v) (mfderiv J I (F : N → M) y v) ≤
          (1 + eps) * h.inner y v v)
    (hroom : Real.sqrt (1 + eps) * (3 * rho) < Real.sqrt (1 - eps) * R) :
    ∀ a ∈ riemannianClosedBallOf h p rho, ∀ b ∈ riemannianClosedBallOf h p rho,
      Real.sqrt (1 - eps) * (riemannianEDistOf (I := J) h a b).toReal ≤
          (riemannianEDistOf (I := I) g (F a) (F b)).toReal ∧
        (riemannianEDistOf (I := I) g (F a) (F b)).toReal ≤
          Real.sqrt (1 + eps) * (riemannianEDistOf (I := J) h a b).toReal := by
  have hLm : (0 : ℝ) ≤ Real.sqrt (1 - eps) := Real.sqrt_nonneg _
  have hLp : (0 : ℝ) ≤ Real.sqrt (1 + eps) := Real.sqrt_nonneg _
  intro a ha b hb
  obtain ⟨hlower, hupper⟩ := crossModel_edist_transfer h g F p hR heps0 heps1 hrho hcpt
    hsource hequiv hroom a ha b hb
  have habfin : riemannianEDistOf (I := J) h a b ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (edistOf_le_of_mem_closedBall h p hrho ha hb)
  have hgfin : riemannianEDistOf (I := I) g (F a) (F b) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top habfin) hupper
  constructor
  · have := ENNReal.toReal_mono hgfin hlower
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hLm] at this
  · have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top habfin) hupper
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hLp] at this

end CrossModel

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
