import DifferentialGeometry.Geometry.Metric.PullbackCross
import DifferentialGeometry.Geometry.Metric.Completeness

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [T2Space N]

omit [FiniteDimensional ℝ F] [T2Space N] in
private theorem pullback_path_integral_eq
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    {x y : M} (γ : Path x y) (hγ : CMDiff 1 γ) :
    (∫⁻ t, ENNReal.ofReal (Real.sqrt
      ((Diffeomorph.pullbackMetricCross g Φ).inner (γ t)
        (mfderiv% γ t 1) (mfderiv% γ t 1)))) =
      ∫⁻ t, ENNReal.ofReal (Real.sqrt
        (g.inner ((Path.map γ Φ.continuous) t)
          (mfderiv% (Path.map γ Φ.continuous) t 1)
          (mfderiv% (Path.map γ Φ.continuous) t 1))) := by
  apply lintegral_congr
  intro t
  rw [Diffeomorph.pullbackMetricCross_inner]
  have hΦMD : MDifferentiableAt I J (Φ : M → N) (γ t) :=
    (Φ.contMDiff (γ t)).mdifferentiableAt (by simp)
  have hγMD : MDifferentiableAt _ I (γ : unitInterval → M) t :=
    (hγ t).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp t hΦMD hγMD
  change _ = ENNReal.ofReal (Real.sqrt
    (g.inner (Φ (γ t))
      (mfderiv _ J ((Φ : M → N) ∘ (γ : unitInterval → M)) t 1)
      (mfderiv _ J ((Φ : M → N) ∘ (γ : unitInterval → M)) t 1)))
  rw [hcomp]
  rfl

omit [FiniteDimensional ℝ F] [T2Space N] in
theorem riemannianEDistOf_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (x y : M) :
    riemannianEDistOf (I := I) (Diffeomorph.pullbackMetricCross g Φ) x y =
      riemannianEDistOf (I := J) g (Φ x) (Φ y) := by
  rw [edistOf_iInf, edistOf_iInf]
  apply le_antisymm
  · apply le_iInf
    intro δ
    apply le_iInf
    intro hδ
    let γ : Path x y :=
      (Path.map δ Φ.symm.continuous).cast
        (Φ.symm_apply_apply x).symm (Φ.symm_apply_apply y).symm
    have hγ : CMDiff 1 γ := by
      rw [show (γ : unitInterval → M) =
          (Φ.symm : N → M) ∘ (δ : unitInterval → N) by
        exact Path.cast_coe _ _ _]
      exact (Φ.symm.contMDiff.of_le (by norm_num)).comp hδ
    refine iInf_le_of_le γ (iInf_le_of_le hγ ?_)
    rw [pullback_path_integral_eq g Φ γ hγ]
    have hmap : Path.map γ Φ.continuous = δ := by
      apply Path.ext
      funext t
      simp [γ, Path.cast_coe]
    rw [hmap]
  · apply le_iInf
    intro γ
    apply le_iInf
    intro hγ
    let δ : Path (Φ x) (Φ y) := Path.map γ Φ.continuous
    have hδ : CMDiff 1 δ :=
      (Φ.contMDiff.of_le (by norm_num)).comp hγ
    refine iInf_le_of_le δ (iInf_le_of_le hδ ?_)
    exact (pullback_path_integral_eq g Φ γ hγ).symm.le

namespace RiemannianMetricComplete

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem pullbackCross
    [SigmaCompactSpace M] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (hg : RiemannianMetricComplete (I := J) g) :
    RiemannianMetricComplete (I := I)
      (Diffeomorph.pullbackMetricCross g Φ) := by
  let : IsManifold I 1 M := IsManifold.of_le
    (I := I) (M := M) (n := ∞) (by norm_num)
  let : IsManifold J 1 N := IsManifold.of_le
    (I := J) (M := N) (n := ∞) (by norm_num)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace J N
  let : T3Space M := inferInstance
  let : T3Space N := inferInstance
  refine ⟨?_⟩
  let h := Diffeomorph.pullbackMetricCross g Φ
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨h.inner, h.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : RiemannianBundle (fun x : N => TangentSpace J x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (fun x : N => TangentSpace J x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric J N
  let e : M ≃ᵢ N :=
    { toEquiv := Φ.toEquiv
      isometry_toFun := by
        intro x y
        change riemannianEDistOf (I := J) g (Φ x) (Φ y) =
          riemannianEDistOf (I := I) h x y
        exact (riemannianEDistOf_pullbackMetricCross g Φ x y).symm }
  exact e.completeSpace_iff.mpr hg.complete

end RiemannianMetricComplete

end DifferentialGeometry
