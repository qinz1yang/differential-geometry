import DifferentialGeometry.Geometry.Metric.Distance.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseGeometry


set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem distance_toReal_oscillation_le
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (g : SmoothRiemannianMetric I3 M) (p v z : M)
    (hvz : riemannianEDistOf g v z ≠ ⊤) :
    |(riemannianEDistOf g p z).toReal - (riemannianEDistOf g p v).toReal| ≤
      (riemannianEDistOf g v z).toReal := by
  have hzv : riemannianEDistOf g z v ≠ ⊤ := by
    simpa only [riemannianEDistOf_comm g z v] using hvz
  by_cases hpv : riemannianEDistOf g p v = ⊤
  · have hpz : riemannianEDistOf g p z = ⊤ := by
      by_contra hpz
      have hfinite : riemannianEDistOf g p v ≠ ⊤ := ne_top_of_le_ne_top
        (ENNReal.add_ne_top.mpr ⟨hpz, hzv⟩) (riemannianEDistOf_triangle g p z v)
      exact hfinite hpv
    rw [hpz, hpv, ENNReal.toReal_top, sub_self, abs_zero]
    exact ENNReal.toReal_nonneg
  · have hpz : riemannianEDistOf g p z ≠ ⊤ := ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨hpv, hvz⟩) (riemannianEDistOf_triangle g p v z)
    have hupper := riemannianEDistOf_toReal_triangle g p v z hpv hvz
    have hlower := riemannianEDistOf_toReal_triangle g p z v hpz hzv
    rw [riemannianEDistOf_comm g z v] at hlower
    exact abs_le.mpr ⟨by linarith, by linarith⟩

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]


theorem rescaledMetric_zero {J : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) J)
    (t Q : ℝ) (hQ : 0 < Q) :
    rescaledMetric S t Q hQ 0 = scaleMetric Q hQ (S.base.metric t) := by
  simp only [rescaledMetric, parabolicTime_zero]


theorem edistOf_rescaledMetric_zero {J : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) J) (t Q : ℝ) (hQ : 0 < Q) (y z : M) :
    riemannianEDistOf (rescaledMetric S t Q hQ 0) y z =
      ENNReal.ofReal (Real.sqrt Q) * riemannianEDistOf (S.base.metric t) y z := by
  rw [rescaledMetric_zero S t Q hQ, edistOf_scale]


theorem MinimizingArm.edistOf_start {g : SmoothRiemannianMetric I3 M} {x : M}
    (a : MinimizingArm g x) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) a.length) :
    riemannianEDistOf g x (a.point s) = ENNReal.ofReal s := by
  have hd : (riemannianEDistOf g x (a.point s)).toReal = s := by
    have h := a.minimizing 0 ⟨le_rfl, a.length_pos.le⟩ s hs
    rw [a.start] at h
    have h' : (riemannianEDistOf g x (a.point s)).toReal = |0 - s| := h
    rwa [zero_sub, abs_neg, abs_of_nonneg hs.1] at h'
  rcases eq_or_ne (riemannianEDistOf g x (a.point s)) ⊤ with htop | hne
  · exfalso
    rw [htop, ENNReal.toReal_top] at hd
    rw [← hd, a.start, riemannianEDistOf_self] at htop
    exact (by simp : (0 : ℝ≥0∞) ≠ ⊤) htop
  · exact (ENNReal.ofReal_toReal hne).symm.trans (congrArg ENNReal.ofReal hd)


theorem exists_fixed_neck_central_diameter :
    ∃ Dc : ℝ, 0 < Dc ∧ ∀ (J : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) J)
      (eps : ℝ) (x : M) (t : ℝ) (neck : StrongNeck S eps x t) (p q : Sphere 2),
      riemannianEDistOf (rescaledMetric S t (S.scalar t x) neck.Q_pos 0)
        (neck.map (p, 0)) (neck.map (q, 0)) ≤ ENNReal.ofReal Dc := by
  obtain ⟨Dc, hDc, hshort⟩ := exists_uniform_transverse_shortcuts (M := M)
  refine ⟨Dc, hDc, ?_⟩
  intro J S eps x t neck p q
  have hinv : 0 < eps⁻¹ := inv_pos.mpr neck.eps_pos
  have hlevel : ∀ y : Sphere 2, (y, (0 : ℝ)) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro y
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  obtain ⟨gamma, hstart, hend, hgamma, -, hlen⟩ :=
    hshort neck.cylinder neck.cylinder.metric
      (rescaledMetric S t (S.scalar t x) neck.Q_pos) neck.map
      (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) (Icc (-1) 0) ⌈eps⁻¹⌉₊ eps 0
      neck.comparison rfl neck.eps_pos.le (by linarith [neck.eps_small])
      ⟨by norm_num, le_rfl⟩ neck.domain hlevel p q
  have hdist := edistOf_le_metricPathELength
    (rescaledMetric S t (S.scalar t x) neck.Q_pos 0) (by norm_num : (0 : ℝ) ≤ 1) hgamma
  rw [hstart, hend] at hdist
  exact hdist.trans hlen


theorem StrongNeck.centralSphere_distance_sub_center_le
    {J : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) J}
    {eps : ℝ} {v : M} {t : ℝ} (neck : StrongNeck S eps v t)
    {Dc : ℝ} (hDc : 0 ≤ Dc)
    (hdiam : ∀ y z : Sphere 2,
      riemannianEDistOf (rescaledMetric S t (S.scalar t v) neck.Q_pos 0)
        (neck.map (y, 0)) (neck.map (z, 0)) ≤ ENNReal.ofReal Dc)
    (p : M) {z : M} (hz : z ∈ neck.map '' (univ ×ˢ ({0} : Set ℝ))) :
    |metricDistance (S.base.metric t) p z - metricDistance (S.base.metric t) p v| ≤
      Dc / Real.sqrt (S.scalar t v) := by
  obtain ⟨y, hy, rfl⟩ := hz
  have hy0 : y.2 = 0 := hy.2
  have hyform : ((y.1, (0 : ℝ)) : Cylinder) = y := Prod.ext rfl hy0.symm
  have hpair := hdiam neck.center y.1
  rw [neck.center_eq, hyform, edistOf_rescaledMetric_zero] at hpair
  have hsqrt : 0 < Real.sqrt (S.scalar t v) := Real.sqrt_pos.mpr neck.Q_pos
  have hfinite : riemannianEDistOf (S.base.metric t) v (neck.map y) ≠ ⊤ := by
    intro hinf
    rw [hinf, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hsqrt)] at hpair
    exact (not_le_of_gt ENNReal.ofReal_lt_top) hpair
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpair
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hsqrt.le,
    ENNReal.toReal_ofReal hDc] at hreal
  have hbound : (riemannianEDistOf (S.base.metric t) v (neck.map y)).toReal ≤
      Dc / Real.sqrt (S.scalar t v) := by
    apply (le_div_iff₀ hsqrt).mpr
    simpa only [mul_comm] using hreal
  exact (distance_toReal_oscillation_le (S.base.metric t) p v (neck.map y) hfinite).trans hbound



theorem StrongNeck.le_edistOf_of_height [T2Space M] {J : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) J} {eps : ℝ} {x : M} {t : ℝ}
    (neck : StrongNeck S eps x t) {R : ℝ} (hR : 0 < R) {q : Sphere 2} {l : ℝ}
    (hRl : R < |l|) (hl : |l| < eps⁻¹) :
    ENNReal.ofReal (R / 2) ≤
      riemannianEDistOf (rescaledMetric S t (S.scalar t x) neck.Q_pos 0) x
        (neck.map (q, l)) := by
  have hRe : R < eps⁻¹ := hRl.trans hl
  have hslab : (univ : Set (Sphere 2)) ×ˢ Icc (-R) R ⊆
      (univ : Set (Sphere 2)) ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    rintro ⟨y, c⟩ ⟨-, hc⟩
    have hc1 : -R ≤ c := hc.1
    have hc2 : c ≤ R := hc.2
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  have hcap := collar_ball_subset_image neck.cylinder
    (rescaledMetric S t (S.scalar t x) neck.Q_pos) neck.map neck.comparison rfl
    (by linarith [neck.eps_small] : eps ≤ 1 / 2) ⟨by norm_num, le_rfl⟩ hR neck.domain hslab
    neck.center
  rw [neck.center_eq] at hcap
  by_contra hlt
  have hball : neck.map (q, l) ∈
      riemannianBallOf (rescaledMetric S t (S.scalar t x) neck.Q_pos 0) x (R / 2) :=
    not_le.mp hlt
  obtain ⟨z, hz, hzeq⟩ := hcap hball
  have hqsrc : ((q, l) : Cylinder) ∈ neck.map.source :=
    neck.domain ⟨mem_univ _, abs_lt.mp hl⟩
  have hzsrc : z ∈ neck.map.source := neck.domain (hslab hz)
  have hzq : z = (q, l) := by
    have h1 := neck.map.left_inv' hzsrc
    rw [hzeq] at h1
    exact h1.symm.trans (neck.map.left_inv' hqsrc)
  rw [hzq] at hz
  have hb : |l| ≤ R := abs_le.mpr ⟨hz.2.1, hz.2.2⟩
  linarith


theorem MinimizingArm.not_mem_centralSphere_of_far [T2Space M] {J : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) J} {eps : ℝ} {x : M} {t : ℝ}
    (a : MinimizingArm (S.base.metric t) x) (neck : StrongNeck S eps x t)
    {Dc : ℝ} (hDc : 0 ≤ Dc)
    (hdiam : ∀ p q : Sphere 2,
      riemannianEDistOf (rescaledMetric S t (S.scalar t x) neck.Q_pos 0)
        (neck.map (p, 0)) (neck.map (q, 0)) ≤ ENNReal.ofReal Dc)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) a.length) {q : Sphere 2} {l : ℝ}
    (hpt : a.point s₀ = neck.map (q, l)) (hl : 2 * Dc + 2 < |l|) (hl' : |l| < eps⁻¹) :
    ∀ w ∈ Icc s₀ a.length, a.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ)) := by
  intro w hw hmem
  obtain ⟨z, hz, hzeq⟩ := hmem
  have hz2 : z.2 = 0 := hz.2
  have hzform : ((z.1, (0 : ℝ)) : Cylinder) = z := Prod.ext rfl hz2.symm
  have hw0 : w ∈ Icc (0 : ℝ) a.length := ⟨hs₀.1.trans hw.1, hw.2⟩
  have hupper : Real.sqrt (S.scalar t x) * w ≤ Dc := by
    have h := hdiam neck.center z.1
    rw [neck.center_eq, hzform, hzeq, edistOf_rescaledMetric_zero, a.edistOf_start hw0,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg (S.scalar t x))] at h
    exact (ENNReal.ofReal_le_ofReal_iff hDc).mp h
  have hlower : Dc + 1 ≤ Real.sqrt (S.scalar t x) * s₀ := by
    have h := neck.le_edistOf_of_height (R := 2 * Dc + 2) (q := q) (by linarith) hl hl'
    rw [← hpt, edistOf_rescaledMetric_zero, a.edistOf_start hs₀,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg (S.scalar t x))] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (Real.sqrt_nonneg (S.scalar t x)) hs₀.1)).mp h
    linarith
  have hmono : Real.sqrt (S.scalar t x) * s₀ ≤ Real.sqrt (S.scalar t x) * w :=
    mul_le_mul_of_nonneg_left hw.1 (Real.sqrt_nonneg (S.scalar t x))
  linarith


theorem exists_fixed_neck_arm_no_return_depth [T2Space M] :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (J : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) J)
      (eps : ℝ) (x : M) (t : ℝ) (neck : StrongNeck S eps x t)
      (a : MinimizingArm (S.base.metric t) x) (s₀ : ℝ), s₀ ∈ Icc (0 : ℝ) a.length →
      ∀ (q : Sphere 2) (l : ℝ), a.point s₀ = neck.map (q, l) → H₀ ≤ |l| → |l| < eps⁻¹ →
      ∀ w ∈ Icc s₀ a.length, a.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ)) := by
  obtain ⟨Dc, hDc, hdiam⟩ := exists_fixed_neck_central_diameter (M := M)
  refine ⟨2 * Dc + 3, by linarith, ?_⟩
  intro J S eps x t neck a s₀ hs₀ q l hpt hl hl'
  exact a.not_mem_centralSphere_of_far neck hDc.le (hdiam J S eps x t neck) hs₀ hpt
    (by linarith) hl'


theorem exists_fixed_neck_two_arm_no_return_depth [T2Space M] :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (J : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) J)
      (eps : ℝ) (x : M) (t : ℝ) (neck : StrongNeck S eps x t)
      (a b : MinimizingArm (S.base.metric t) x) (s v : ℝ),
      s ∈ Icc (0 : ℝ) a.length → v ∈ Icc (0 : ℝ) b.length →
      ∀ (p q : Sphere 2) (k l : ℝ),
      a.point s = neck.map (p, k) → b.point v = neck.map (q, l) →
      H₀ ≤ |k| → |k| < eps⁻¹ → H₀ ≤ |l| → |l| < eps⁻¹ →
      (∀ w ∈ Icc s a.length, a.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
      (∀ w ∈ Icc v b.length, b.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) := by
  obtain ⟨H₀, hH₀, hone⟩ := exists_fixed_neck_arm_no_return_depth (M := M)
  refine ⟨H₀, hH₀, ?_⟩
  intro J S eps x t neck a b s v hs hv p q k l hak hbl hk hk' hl hl'
  exact ⟨hone J S eps x t neck a s hs p k hak hk hk',
    hone J S eps x t neck b v hv q l hbl hl hl'⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
