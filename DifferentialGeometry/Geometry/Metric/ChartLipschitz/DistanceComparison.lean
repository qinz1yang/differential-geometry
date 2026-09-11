import DifferentialGeometry.Geometry.Metric.ChartDistanceComparison
import DifferentialGeometry.Geometry.Metric.EuclideanChart
import Mathlib.Topology.EMetricSpace.Lipschitz

set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set DifferentialGeometry
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem edist_metricChartEuclideanEquiv (g : SmoothRiemannianMetric I M)
    (p x y : M) :
    edist (metricChartEuclideanEquiv g p (extChartAt I p x))
      (metricChartEuclideanEquiv g p (extChartAt I p y)) =
      let e := trivializationAt E (TangentSpace I) p
      let w := e.symmL ℝ p (extChartAt I p y - extChartAt I p x)
      ENNReal.ofReal (Real.sqrt (g.inner p w w)) := by
  rw [edist_comm, edist_dist, dist_eq_norm, ← map_sub, metricChartEuclideanEquiv_norm]

variable {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem continuousAt_of_local_riemannianEDistOf_le [RegularSpace M] [RegularSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (p : M)
    (hf : ∃ L : ℝ≥0, ∃ t ∈ 𝓝 p, ∀ x ∈ t, ∀ y ∈ t,
      riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y) :
    ContinuousAt f p := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace N := .ofRiemannianMetric J N
  obtain ⟨L, t, ht, hbound⟩ := hf
  have hLip : LipschitzOnWith L f t := by
    intro x hx y hy
    exact hbound x hx y hy
  exact (hLip.continuousOn p (mem_of_mem_nhds ht)).continuousAt ht

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem locallyLipschitz_iff_local_riemannianEDistOf_le [RegularSpace M] [RegularSpace N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (f : M → N) :
    (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
       ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
     letI : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
       ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace N := .ofRiemannianMetric J N
     LocallyLipschitz f) ↔
      ∀ p, ∃ L : ℝ≥0, ∃ t ∈ 𝓝 p, ∀ x ∈ t, ∀ y ∈ t,
        riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y := by
  rfl

theorem exists_ball_lipschitzOnWith_euclideanChartExpression
    [RegularSpace M] [RegularSpace N] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (p : M) {K : ℝ≥0} (hK : 1 < K)
    (hf : ∃ L : ℝ≥0, ∃ t ∈ 𝓝 p, ∀ x ∈ t, ∀ y ∈ t,
      riemannianEDistOf h (f x) (f y) ≤ L * riemannianEDistOf g x y)
    (s : Set M) (hs : s ∈ 𝓝 p) :
    let A := metricChartEuclideanEquiv g p
    let φ := extChartAt I p
    let ψ := extChartAt J (f p)
    ∃ r : ℝ, 0 < r ∧ ∃ L' : ℝ≥0,
      let B := Metric.ball (A (φ p)) r
      let U := φ.source ∩ (fun x => A (φ x)) ⁻¹' B
      IsOpen U ∧ p ∈ U ∧
      (∀ z ∈ B, A.symm z ∈ φ.target ∧
        φ.symm (A.symm z) ∈ s ∧ φ.symm (A.symm z) ∈ φ.source ∧
        f (φ.symm (A.symm z)) ∈ ψ.source) ∧
      LipschitzOnWith L' (euclideanChartExpression g h f p (f p)) B ∧
      ∀ C : ℝ≥0, LipschitzOnWith C (euclideanChartExpression g h f p (f p)) B →
        ∀ x ∈ U, ∀ y ∈ U,
          riemannianEDistOf h (f x) (f y) ≤ (K ^ 2 * C : ℝ≥0) * riemannianEDistOf g x y := by
  let A := metricChartEuclideanEquiv g p
  let D := metricChartEuclideanEquiv h (f p)
  let φ := extChartAt I p
  let ψ := extChartAt J (f p)
  let χ := φ.symm ∘ A.symm
  let center := A (φ p)
  have hKreal : (1 : ℝ) < K := by exact_mod_cast hK
  have hc := continuousAt_of_local_riemannianEDistOf_le g h f p hf
  obtain ⟨L, t, ht, hLip⟩ := hf
  obtain ⟨Ug, hpg, hgchart, hgcomp⟩ := exists_open_riemannianEDistOf_comparison g p hKreal
  obtain ⟨Uh, hph, hhchart, hhcomp⟩ := exists_open_riemannianEDistOf_comparison h (f p) hKreal
  have hg (x : M) (hx : x ∈ Ug) (y : M) (hy : y ∈ Ug) :
      edist (A (φ x)) (A (φ y)) ≤ (K : ℝ≥0∞) * riemannianEDistOf g x y ∧
      riemannianEDistOf g x y ≤ (K : ℝ≥0∞) * edist (A (φ x)) (A (φ y)) := by
    rw [edist_metricChartEuclideanEquiv]
    simpa only [ENNReal.ofReal_coe_nnreal] using hgcomp x hx y hy
  have hh (x : N) (hx : x ∈ Uh) (y : N) (hy : y ∈ Uh) :
      edist (D (ψ x)) (D (ψ y)) ≤ (K : ℝ≥0∞) * riemannianEDistOf h x y ∧
      riemannianEDistOf h x y ≤ (K : ℝ≥0∞) * edist (D (ψ x)) (D (ψ y)) := by
    rw [edist_metricChartEuclideanEquiv]
    simpa only [ENNReal.ofReal_coe_nnreal] using hhcomp x hx y hy
  let V := s ∩ (t ∩ ((Ug : Set M) ∩ f ⁻¹' (Uh : Set N)))
  have hV : V ∈ 𝓝 p :=
    inter_mem hs (inter_mem ht (inter_mem (Ug.isOpen.mem_nhds hpg)
      (hc.preimage_mem_nhds (Uh.isOpen.mem_nhds hph))))
  have hχcenter : χ center = p := by
    dsimp [χ, center]
    rw [A.symm_apply_apply]
    exact φ.left_inv (mem_extChartAt_source p)
  have hχ : ContinuousAt χ center := by
    have ho : ContinuousAt φ.symm (A.symm center) := by
      simpa only [center, ContinuousLinearEquiv.symm_apply_apply] using
        continuousAt_extChartAt_symm (I := I) p
    exact ho.comp (x := center) A.symm.continuousAt
  have hpre : χ ⁻¹' V ∈ 𝓝 center :=
    hχ.preimage_mem_nhds (by rwa [hχcenter])
  have htarget : A.symm ⁻¹' φ.target ∈ 𝓝 center := by
    apply A.symm.continuousAt.preimage_mem_nhds
    simpa only [center, ContinuousLinearEquiv.symm_apply_apply] using
      extChartAt_target_mem_nhds (I := I) p
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem htarget hpre)
  let B := Metric.ball center r
  let U := φ.source ∩ (fun x => A (φ x)) ⁻¹' B
  have hcoord (z) (hz : z ∈ B) : A (φ (χ z)) = z := by
    rw [show φ (χ z) = A.symm z from φ.right_inv (hball hz).1, A.apply_symm_apply]
  have hUopen : IsOpen U :=
    isOpen_extChartAt_preimage' p (Metric.isOpen_ball.preimage A.continuous)
  have hpU : p ∈ U := ⟨mem_extChartAt_source p, Metric.mem_ball_self hr⟩
  refine ⟨r, hr, K ^ 2 * L, hUopen, hpU, ?_, ?_, ?_⟩
  · intro z hz
    have hzV := (hball hz).2
    exact ⟨(hball hz).1, hzV.1, φ.map_target (hball hz).1,
      by simpa only [ψ, χ, Function.comp_apply, φ, A, extChartAt_source] using
        hhchart hzV.2.2.2⟩
  · intro z hz w hw
    have hzV := (hball hz).2
    have hwV := (hball hw).2
    change edist (D (ψ (f (χ z)))) (D (ψ (f (χ w)))) ≤ _
    calc
      _ ≤ (K : ℝ≥0∞) * riemannianEDistOf h (f (χ z)) (f (χ w)) :=
        (hh _ hzV.2.2.2 _ hwV.2.2.2).1
      _ ≤ (K : ℝ≥0∞) * (L * riemannianEDistOf g (χ z) (χ w)) :=
        mul_right_mono (hLip _ hzV.2.1 _ hwV.2.1)
      _ ≤ (K : ℝ≥0∞) * (L * (K * edist (A (φ (χ z))) (A (φ (χ w))))) :=
        mul_right_mono (mul_right_mono (hg _ hzV.2.2.1 _ hwV.2.2.1).2)
      _ = ((K ^ 2 * L : ℝ≥0) : ℝ≥0∞) * edist z w := by
        rw [hcoord z hz, hcoord w hw, ENNReal.coe_mul, ENNReal.coe_pow]
        ring
  · intro C hC x hx y hy
    have hxinv : χ (A (φ x)) = x := by
      dsimp only [χ, Function.comp_apply]
      rw [A.symm_apply_apply, φ.left_inv hx.1]
    have hyinv : χ (A (φ y)) = y := by
      dsimp only [χ, Function.comp_apply]
      rw [A.symm_apply_apply, φ.left_inv hy.1]
    have hxV : x ∈ V := by
      have hv := (hball hx.2).2
      change χ (A (φ x)) ∈ V at hv
      rwa [hxinv] at hv
    have hyV : y ∈ V := by
      have hv := (hball hy.2).2
      change χ (A (φ y)) ∈ V at hv
      rwa [hyinv] at hv
    have hCxy : edist (D (ψ (f x))) (D (ψ (f y))) ≤
        (C : ℝ≥0∞) * edist (A (φ x)) (A (φ y)) := by
      have hcxy := hC hx.2 hy.2
      change edist (D (ψ (f (χ (A (φ x)))))) (D (ψ (f (χ (A (φ y)))))) ≤ _ at hcxy
      rwa [hxinv, hyinv] at hcxy
    calc
      _ ≤ (K : ℝ≥0∞) * edist (D (ψ (f x))) (D (ψ (f y))) :=
        (hh _ hxV.2.2.2 _ hyV.2.2.2).2
      _ ≤ (K : ℝ≥0∞) * (C * edist (A (φ x)) (A (φ y))) :=
        mul_right_mono hCxy
      _ ≤ (K : ℝ≥0∞) * (C * (K * riemannianEDistOf g x y)) :=
        mul_right_mono (mul_right_mono (hg _ hxV.2.2.1 _ hyV.2.2.1).1)
      _ = ((K ^ 2 * C : ℝ≥0) : ℝ≥0∞) * riemannianEDistOf g x y := by
        rw [ENNReal.coe_mul, ENNReal.coe_pow]
        ring

end DifferentialGeometry.Geometry.Metric
