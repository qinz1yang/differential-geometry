import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsometryComp
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsometryDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsometryCompHigher
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiRestrictOpen
import DifferentialGeometry.Tensor.RSTensor.Coordinates.OpensRestrict
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

omit [CompleteSpace E] in
theorem exists_pullbackField
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ Φ.source)
    (h : SmoothRiemannianMetric I N) (gM : SmoothRiemannianMetric I M) :
    ∃ (P : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2) (G : SmoothRiemannianMetric I M),
      P = Tensor0SBundle.metricTensorField (I := I) G ∧
      (∀ x ∈ K, ∀ v w : TangentSpace I x,
        G.inner x v w = h.inner ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w)) ∧
      ∀ x ∈ K, ∀ v : Fin 2 → TangentSpace I x,
        P x v = h.inner ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x (v 0)) (mfderiv I I (Φ : M → N) x (v 1)) := by
  classical
  obtain ⟨χ, P₀, hP₀smooth, hχ, hχK, hχsupp, hχ01, hP₀def⟩ :=
    exists_pullbackInner (I := I) Φ hK hKs h
  set G : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := fun x =>
    P₀ x + (1 - χ x) • gM.inner x with hG
  have hGapply : ∀ (x : M) (v w : TangentSpace I x),
      G x v w = χ x * (h.inner ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w))
        + (1 - χ x) * gM.inner x v w := by
    intro x v w
    simp only [hG, hP₀def x, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply, smul_eq_mul]
  have hGpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < G x v v := by
    intro x v hv
    rw [hGapply]
    have ha : 0 ≤ χ x := (hχ01 x).1
    have hb : 0 ≤ 1 - χ x := by linarith [(hχ01 x).2]
    have hgM := gM.pos x v hv
    rcases lt_or_eq_of_le ha with ha' | ha'
    · have hxs : x ∈ Φ.source :=
        hχsupp (subset_tsupport χ (Function.mem_support.mpr (ne_of_gt ha')))
      have hpull := pullInner_pos (I := I) Φ hxs h v hv
      nlinarith
    · rw [← ha']
      simpa using hgM
  set Gmetric : SmoothRiemannianMetric I M :=
    { inner := G
      symm := by
        intro x v w
        rw [hGapply, hGapply, gM.symm x v w, h.symm]
      pos := hGpos
      isVonNBounded := fun x =>
        DifferentialGeometry.Geometry.posDef_isVonNBounded (E := E)
          ((G x : E →L[ℝ] E →L[ℝ] ℝ)) (fun v hv => hGpos x v hv)
      contMDiff := by
        have hgM' : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (∞ : WithTop ℕ∞)
            (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
              (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
              x ((1 - χ x) • gM.inner x)) := by
          have hcoef : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) (fun x : M => 1 - χ x) :=
            contMDiff_const.sub hχ
          exact fun x₀ => (hcoef.contMDiffAt).smul_section (gM.contMDiff x₀)
        exact fun x₀ => (hP₀smooth x₀).add_section (hgM' x₀) }
    with hGmetric
  have hGinner : ∀ x ∈ K, ∀ v w : TangentSpace I x,
      Gmetric.inner x v w = h.inner ((Φ : M → N) x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w) := by
    intro x hx v w
    change G x v w = _
    rw [hGapply, hχK hx]
    simp
  refine ⟨Tensor0SBundle.metricTensorField (I := I) Gmetric, Gmetric, rfl, hGinner, ?_⟩
  intro x hx v
  rw [Tensor0SBundle.metricTensorField_apply]
  exact hGinner x hx (v 0) (v 1)


end HCGCompactness
end DifferentialGeometry
