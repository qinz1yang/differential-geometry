import DifferentialGeometry.Geometry.Comparison.InjectivityRadius.Intrinsic
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse
import DifferentialGeometry.Geometry.Metric.Construction.CompactPerturbationCompleteness

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

def intrinsicInjectivityRadius (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hg : RiemannianMetricComplete g) (p : E) : ℝ≥0∞ := by
  letI : RiemannianBundle (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let metricSpace : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  letI : PseudoEMetricSpace E := metricSpace.toPseudoEMetricSpace
  letI : @CompleteSpace E metricSpace.toUniformSpace := hg.complete
  have hnorm : ∀ (x : E) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  exact intrinsicInjRadius g hnorm p

theorem exists_pos_le_intrinsicInjectivityRadius_on_compact (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hg : RiemannianMetricComplete g) {K : Set E} (hK : IsCompact K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p ∈ K, ENNReal.ofReal ρ ≤ intrinsicInjectivityRadius g hg p := by
  classical
  have hflat : ∀ x v : E, (flatModelMetric E).inner x v v = ‖v‖ ^ 2 := by
    intro x v
    exact real_inner_self_eq_norm_sq v
  let : RiemannianBundle (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let metricSpace : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  let : PseudoEMetricSpace E := metricSpace.toPseudoEMetricSpace
  let : @CompleteSpace E metricSpace.toUniformSpace := hg.complete
  have hnorm : ∀ (x : E) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hsource : ∀ p : E, ∃ δ : ℝ, 0 < δ ∧
      ∀ q v : E, dist q p < δ → ‖v‖ < δ →
        (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) E) ∈ (standardDiagonalInverseBranch g hnorm p).hom.source := by
    intro p
    let B := standardDiagonalInverseBranch g hnorm p
    let Φ := (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm
    have hzero : (p, (0 : E)) ∈ Φ ⁻¹' B.hom.source := B.zero_mem
    have hopen : IsOpen (Φ ⁻¹' B.hom.source) := B.hom.open_source.preimage Φ.continuous
    obtain ⟨δ, hδ, hball⟩ := (Metric.mem_nhds_iff (α := E × E)).mp (hopen.mem_nhds hzero)
    refine ⟨δ, hδ, fun q v hq hv => ?_⟩
    have hz : (q, v) ∈ Φ ⁻¹' B.hom.source := hball (by
      change dist (q, v) (p, (0 : E)) < δ
      simpa only [Prod.dist_eq, dist_zero_right, max_lt_iff] using And.intro hq hv)
    exact hz
  choose δ hδ hsource using hsource
  obtain ⟨t, _htK, hcover⟩ := hK.elim_nhds_subcover (fun p => Metric.ball p (δ p))
    (fun p _ => Metric.ball_mem_nhds p (hδ p))
  by_cases hne : t.Nonempty
  · let a := t.inf' hne δ
    have ha : 0 < a := (Finset.lt_inf'_iff hne).mpr (fun p _ => hδ p)
    obtain ⟨c, hc, hlower⟩ := metric_lower_on hK g (flatModelMetric E)
    let ρ := Real.sqrt c * a
    have hρ : 0 < ρ := mul_pos (Real.sqrt_pos.mpr hc) ha
    refine ⟨ρ, hρ, fun p hp => ?_⟩
    change ENNReal.ofReal ρ ≤ intrinsicInjRadius g hnorm p
    apply le_intrInjRadius g hnorm p
    change Set.InjOn (intrinsicFramedExp g hnorm p) _
    rw [Metric.eball_ofReal]
    intro v hv w hw heq
    obtain ⟨q, hqt, hpq⟩ := Set.mem_iUnion₂.mp (hcover hp)
    have hvel : ∀ u : E, ‖u‖ < ρ → ‖intrinsicFrameCLM g p u‖ < a := by
      intro u hu
      have hbound : c * ‖intrinsicFrameCLM g p u‖ ^ 2 ≤ ‖u‖ ^ 2 := calc
        c * ‖intrinsicFrameCLM g p u‖ ^ 2 =
            c * (flatModelMetric E).inner p (normalFrame g p u) (normalFrame g p u) :=
          congrArg (fun z => c * z) (hflat p (intrinsicFrameCLM g p u)).symm
        _ ≤ g.inner p (normalFrame g p u) (normalFrame g p u) :=
          hlower p hp (normalFrame g p u)
        _ = ‖u‖ ^ 2 := normalFrame_normSq g p u
      have hsq : (Real.sqrt c * ‖intrinsicFrameCLM g p u‖) ^ 2 ≤ ‖u‖ ^ 2 := by
        rwa [mul_pow, Real.sq_sqrt hc.le]
      have hle := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg _))
        (norm_nonneg u)).mp hsq
      exact (mul_lt_mul_iff_right₀ (Real.sqrt_pos.mpr hc)).mp (hle.trans_lt hu)
    have hsrcv := hsource q p (normalFrame g p v) hpq
      ((hvel v (by simpa only [Metric.mem_ball, dist_zero_right] using hv)).trans_le
        (Finset.inf'_le δ hqt))
    have hsrcw := hsource q p (normalFrame g p w) hpq
      ((hvel w (by simpa only [Metric.mem_ball, dist_zero_right] using hw)).trans_le
        (Finset.inf'_le δ hqt))
    have hdiag : diagExp g hnorm (⟨p, normalFrame g p v⟩ : TangentBundle 𝓘(ℝ, E) E) =
        diagExp g hnorm (⟨p, normalFrame g p w⟩ : TangentBundle 𝓘(ℝ, E) E) :=
      Prod.ext rfl heq
    have htotal := (standardDiagonalInverseBranch g hnorm q).hom.injOn hsrcv hsrcw
      (((standardDiagonalInverseBranch g hnorm q).hom_eq hsrcv).trans
        (hdiag.trans ((standardDiagonalInverseBranch g hnorm q).hom_eq hsrcw).symm))
    apply (normalFrame g p).injective
    exact congrArg (fun u : TangentBundle 𝓘(ℝ, E) E => (u.2 : E)) htotal
  · refine ⟨1, zero_lt_one, fun p hp => ?_⟩
    have hno := Finset.not_nonempty_iff_eq_empty.mp hne
    have hempty : p ∈ (∅ : Set E) := by
      simpa only [hno, Finset.notMem_empty, iUnion_of_empty, iUnion_empty] using hcover hp
    exact hempty.elim

theorem intrinsicInjectivityRadius_pos (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (hg : RiemannianMetricComplete g) (p : E) :
    0 < intrinsicInjectivityRadius g hg p := by
  obtain ⟨ρ, hρ, hbound⟩ :=
    exists_pos_le_intrinsicInjectivityRadius_on_compact g hg (K := {p}) isCompact_singleton
  exact (ENNReal.ofReal_pos.mpr hρ).trans_le (hbound p (mem_singleton p))

end DifferentialGeometry.Geometry.Riemannian
