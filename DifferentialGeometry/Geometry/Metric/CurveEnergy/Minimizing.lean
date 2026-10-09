import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Metric.CurveEnergy
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Topology.Manifold.ZeroDimensional
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_contMDiff_curve_energy_eq_riemannianEDistOf_sq_div
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (x y : M) (hfin : riemannianEDistOf g x y ≠ ⊤) (b : ℝ) (hb : 0 < b) :
    ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ α ∧ α 0 = x ∧ α b = y ∧
      curveEnergy g α 0 b = (riemannianEDistOf g x y).toReal ^ 2 / b := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : T2Space (TangentBundle I M) := inferInstance
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun z : M => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun z : M => TangentSpace I z) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : CompleteSpace M := hg.complete
  have hEnorm : IsMetricNorm (I := I) g :=
    fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g z v
  have hd : riemannianEDistOf g x y = riemannianEDist I x y :=
    riemannianEDistOf_eq_riemannianEDist g hEnorm x y
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : DiscreteTopology M := DifferentialGeometry.discrete_topology_of_finrank_eq_zero I hdim
    have hf : riemannianEDist I x y < ⊤ := lt_top_iff_ne_top.mpr (hd ▸ hfin)
    obtain ⟨γ, h0, h1, hγ, _⟩ := exists_lt_of_riemannianEDist_lt hf
    have hc : Continuous (fun s : Icc (0 : ℝ) 1 => γ s.val) := hγ.continuousOn.domRestrict
    have heq : x = y := by
      have hh := (IsLocallyConstant.iff_continuous _).mpr hc
      have hh' := hh.apply_eq_of_preconnectedSpace
        (⟨0, by simp⟩ : Icc (0 : ℝ) 1) (⟨1, by simp⟩ : Icc (0 : ℝ) 1)
      exact h0.symm.trans (hh'.trans h1)
    rw [← heq]
    refine ⟨fun _ => x, contMDiff_const, rfl, rfl, ?_⟩
    rw [riemannianEDistOf_self]
    simp only [ENNReal.toReal_zero, zero_pow two_ne_zero, zero_div]
    calc
      curveEnergy g (fun _ : ℝ => x) 0 b = ∫ _t in (0 : ℝ)..b, (0 : ℝ) := by
        unfold curveEnergy
        apply intervalIntegral.integral_congr
        intro t _
        change g.inner x
          (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) t (1 : ℝ)) = 0
        have hv : mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) t (1 : ℝ) = 0 := by
          rw [mfderiv_const]
          rfl
        rw [hv]
        exact map_zero _
      _ = 0 := by simp
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    obtain ⟨v, hv, hvnorm⟩ := minExp_of_ne_top g hEnorm x y (hd ▸ hfin)
    let w : TangentSpace I x := b⁻¹ • v
    let α : ℝ → M := intrinsicGeodesic g hEnorm x w
    have hα : ContMDiff 𝓘(ℝ, ℝ) I ∞ α :=
      isGeodesic_contMDiff g (intrinsicGeodesic_isGeodesic g hEnorm x w)
        (intrinsicGeodesic_continuous g hEnorm x w)
    have h0 : α 0 = x := intrinsicGeodesic_zero g hEnorm x w
    have hbwv : b • w = v := by simp [w, smul_smul, hb.ne']
    have h1 : α b = y := by
      change intrinsicGeodesic g hEnorm x w b = y
      rw [← intrinsicGeodesic_smul, ← expMapIntrinsic_def, hbwv]
      exact hv
    have hvv : g.inner x v v = (riemannianEDistOf g x y).toReal ^ 2 := by
      rw [hd]
      exact (Real.sq_sqrt (DifferentialGeometry.metric_inner_self_nonneg g x v)).symm.trans
        (congrArg (fun z : ℝ => z ^ 2) hvnorm)
    have hspeed (s : ℝ) : g.inner (α s) (mfderiv 𝓘(ℝ, ℝ) I α s 1)
        (mfderiv 𝓘(ℝ, ℝ) I α s 1) = (riemannianEDistOf g x y).toReal ^ 2 / b ^ 2 := by
      rw [intrinsicGeodesic_speedSq_eq]
      change g.inner x (b⁻¹ • v) (b⁻¹ • v) = _
      rw [gInner_smul_self, hvv]
      simp only [div_eq_mul_inv, inv_pow, mul_comm]
    refine ⟨α, hα, h0, h1, ?_⟩
    have hi : curveEnergy g α 0 b =
        ∫ _s in (0 : ℝ)..b, (riemannianEDistOf g x y).toReal ^ 2 / b ^ 2 := by
      unfold curveEnergy
      apply intervalIntegral.integral_congr
      intro s _
      exact hspeed s
    rw [hi, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    field_simp [hb.ne']

end DifferentialGeometry.Geometry.Riemannian
