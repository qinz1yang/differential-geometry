import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.DistanceScaling
import DifferentialGeometry.Geometry.Metric.Pullback

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry

open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem pullback_path_length_symm
    (g : SmoothRiemannianMetric I M) (Φ : Diffeomorph I I M M ∞)
    {x y : M} (γ : Path (Φ x) (Φ y)) (hγ : CMDiff 1 γ) :
    (∫⁻ t, ENNReal.ofReal (Real.sqrt
      ((Diffeomorph.pullbackMetric g Φ).inner ((γ.map Φ.symm.continuous) t)
        (mfderiv% (γ.map Φ.symm.continuous) t 1)
        (mfderiv% (γ.map Φ.symm.continuous) t 1)))) =
    (∫⁻ t, ENNReal.ofReal (Real.sqrt
      (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1)))) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  have hγ' : CMDiff 1 (γ.map Φ.symm.continuous) := by
    simpa only [Path.map_coe, Function.comp_def] using
      (Φ.symm.contMDiff.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp hγ
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [] with t
  have hder := mfderiv_comp_apply t
    ((Φ.symm.contMDiff.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contMDiffAt.mdifferentiableAt
      (by norm_num))
    (hγ.contMDiffAt.mdifferentiableAt (by norm_num)) 1
  have hpath : (γ.map Φ.symm.continuous) t = Φ.symm (γ t) := by
    rfl
  rw [hpath]
  change ENNReal.ofReal (Real.sqrt
      ((Diffeomorph.pullbackMetric g Φ).inner (Φ.symm (γ t))
        (mfderiv% (Φ.symm ∘ γ) t 1) (mfderiv% (Φ.symm ∘ γ) t 1))) = _
  rw [hder]
  rw [Diffeomorph.pullbackMetric_inner]
  have hcomp := mfderiv_comp_apply (γ t)
    (Φ.contMDiff.contMDiffAt.mdifferentiableAt (by norm_num))
    (Φ.symm.contMDiff.contMDiffAt.mdifferentiableAt (by norm_num))
    ((mfderiv% γ t) 1)
  rw [← hcomp]
  have hfun : (Φ : M → M) ∘ Φ.symm = id := by
    funext z
    simp
  rw [hfun, mfderiv_id]
  rw [Φ.apply_symm_apply]
  simp

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem pullback_path_length
    (g : SmoothRiemannianMetric I M) (Φ : Diffeomorph I I M M ∞)
    {x y : M} (γ : Path x y) (hγ : CMDiff 1 γ) :
    (∫⁻ t, ENNReal.ofReal (Real.sqrt
      ((Diffeomorph.pullbackMetric g Φ).inner (γ t)
        (mfderiv% γ t 1) (mfderiv% γ t 1)))) =
    (∫⁻ t, ENNReal.ofReal (Real.sqrt
      (g.inner ((γ.map Φ.continuous) t)
        (mfderiv% (γ.map Φ.continuous) t 1)
        (mfderiv% (γ.map Φ.continuous) t 1)))) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  have hγ' : CMDiff 1 (γ.map Φ.continuous) := by
    simpa only [Path.map_coe, Function.comp_def] using
      (Φ.contMDiff.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp hγ
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [] with t
  have hder := mfderiv_comp_apply t
    ((Φ.contMDiff.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contMDiffAt.mdifferentiableAt
      (by norm_num))
    (hγ.contMDiffAt.mdifferentiableAt (by norm_num)) 1
  change ENNReal.ofReal (Real.sqrt
      ((Diffeomorph.pullbackMetric g Φ).inner (γ t)
        (mfderiv% γ t 1) (mfderiv% γ t 1))) = _
  rw [Diffeomorph.pullbackMetric_inner]
  have hmap : (γ.map Φ.continuous : unitInterval → M) = Φ ∘ γ := by
    rw [Path.map_coe]
  rw [hmap]
  rw [hder]
  rfl

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem Diffeomorph.pullbackMetric_edist
    (g : SmoothRiemannianMetric I M) (Φ : Diffeomorph I I M M ∞)
    (x y : M) :
    riemannianEDistOf (I := I) (Diffeomorph.pullbackMetric g Φ) x y =
      riemannianEDistOf (I := I) g (Φ x) (Φ y) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  rw [edistOf_iInf, edistOf_iInf]
  apply le_antisymm
  · refine le_iInf fun γ => ?_
    refine le_iInf fun hγ => ?_
    let γ' : Path x y := {
      toContinuousMap := (γ.map Φ.symm.continuous).toContinuousMap
      source' := by simp
      target' := by simp }
    have hγmap : CMDiff 1 (γ.map Φ.symm.continuous) := by
      simpa only [Path.map_coe, Function.comp_def] using
        ((Φ.symm.contMDiff.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp hγ)
    have hγ' : CMDiff 1 γ' := by
      change CMDiff 1 (γ.map Φ.symm.continuous)
      exact hγmap
    have hfun : (γ' : unitInterval → M) = γ.map Φ.symm.continuous := by
      funext t
      change (γ.map Φ.symm.continuous) t = (γ.map Φ.symm.continuous) t
      rfl
    calc
      _ ≤ (∫⁻ t, ENNReal.ofReal (Real.sqrt
          ((Diffeomorph.pullbackMetric g Φ).inner (γ' t)
            (mfderiv% γ' t 1) (mfderiv% γ' t 1)))) :=
        iInf_le_of_le γ' (iInf_le_of_le hγ' le_rfl)
      _ = _ := by
        rw [hfun]
        exact pullback_path_length_symm (I := I) g Φ γ hγ
  · refine le_iInf fun γ => ?_
    refine le_iInf fun hγ => ?_
    let γ' : Path (Φ x) (Φ y) := γ.map Φ.continuous
    have hγ' : CMDiff 1 γ' := by
      simpa [γ'] using
        ((Φ.contMDiff.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp hγ)
    calc
      _ ≤ (∫⁻ t, ENNReal.ofReal (Real.sqrt
          (g.inner (γ' t) (mfderiv% γ' t 1) (mfderiv% γ' t 1)))) :=
        iInf_le_of_le γ' (iInf_le_of_le hγ' le_rfl)
      _ = _ := (pullback_path_length (I := I) g Φ γ hγ).symm

omit [NeZero (Module.finrank Real E)] [ConnectedSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem RiemannianMetricComplete.pullbackMetric
    (g : SmoothRiemannianMetric I M) (Φ : Diffeomorph I I M M ∞)
    (hg : RiemannianMetricComplete (I := I) g) :
    RiemannianMetricComplete (I := I) (Diffeomorph.pullbackMetric g Φ) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  refine ⟨?_⟩
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨(Diffeomorph.pullbackMetric g Φ).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x) :=
    ⟨(Diffeomorph.pullbackMetric g Φ).inner,
      (Diffeomorph.pullbackMetric g Φ).contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  refine EMetric.complete_of_cauchySeq_tendsto (α := M) fun s hs => ?_
  have hsTarget : ∀ ε > (0 : ENNReal), ∃ N,
      ∀ m, N ≤ m → ∀ n, N ≤ n →
        riemannianEDistOf (I := I) (Diffeomorph.pullbackMetric g Φ) (s m) (s n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change edist (s m) (s n) < ε
    exact hN m hm n hn
  change ∃ x, Filter.Tendsto s Filter.atTop (𝓝 x)
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  have hsSource : CauchySeq (fun n => Φ (s n)) := by
    apply EMetric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hsTarget ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change riemannianEDistOf (I := I) g (Φ (s m)) (Φ (s n)) < ε
    rw [← Diffeomorph.pullbackMetric_edist (I := I) g Φ]
    exact hN m hm n hn
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hsSource
  refine ⟨Φ.symm x, ?_⟩
  have hcont : Continuous Φ.symm := Φ.symm.continuous
  have hseq : (Φ.symm ∘ fun n => Φ (s n)) = s := by
    funext n
    simp
  rw [← hseq]
  exact (hcont.tendsto _).comp hx

end DifferentialGeometry
