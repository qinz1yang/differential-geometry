import DifferentialGeometry.Geometry.Metric.Pullback.FiniteRegularityProof
import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetricSmooth
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Curvature
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# Finite metric pullback on actual inverse patches

The source and target opens of a finite partial diffeomorphism give a genuine finite
bijection. Its pullback metric and sectional curvature retain the original patch derivative.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {s : ℕ∞ω} {m : ℕ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem finite_codRestrict_smoothAt {V : Opens N} {f : M → V} {x : M}
    (hf : ContMDiffAt I J s (fun y => (f y : N)) x) : ContMDiffAt I J s f x := by
  rw [contMDiffAt_iff] at hf ⊢
  exact ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hf.1, hf.2⟩

def finitePatchDiffeomorph (Φ : PartialDiffeomorph I J M N s) :
    Diffeomorph I J (⟨Φ.source, Φ.open_source⟩ : Opens M)
      (⟨Φ.target, Φ.open_target⟩ : Opens N) s where
  toFun x := ⟨Φ x, Φ.map_source x.property⟩
  invFun y := ⟨Φ.symm y, Φ.map_target y.property⟩
  left_inv x := Subtype.ext (Φ.left_inv' x.property)
  right_inv y := Subtype.ext (Φ.right_inv' y.property)
  contMDiff_toFun := by
    intro x
    apply finite_codRestrict_smoothAt
    change ContMDiffAt I J s
      (fun y : (⟨Φ.source, Φ.open_source⟩ : Opens M) => Φ (y : M)) x
    rw [contMDiffAt_subtype_iff]
    exact Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds x.property)
  contMDiff_invFun := by
    intro y
    apply finite_codRestrict_smoothAt
    change ContMDiffAt J I s
      (fun x : (⟨Φ.target, Φ.open_target⟩ : Opens N) => Φ.symm (x : N)) y
    rw [contMDiffAt_subtype_iff]
    exact Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds y.property)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem finitePatchDiffeomorph_mfderiv (Φ : PartialDiffeomorph I J M N s)
    (x : (⟨Φ.source, Φ.open_source⟩ : Opens M)) (v : TangentSpace I x) :
    mfderiv I J (finitePatchDiffeomorph Φ) x v = mfderiv I J Φ (x : M) v := by
  rw [← DifferentialGeometry.mfderiv_subtypeVal_comp (finitePatchDiffeomorph Φ)]
  change mfderiv I J (fun y : (⟨Φ.source, Φ.open_source⟩ : Opens M) => Φ (y : M)) x v = _
  rw [DifferentialGeometry.mfderiv_restrict_open]
  rfl

variable [T2Space N]

def finitePatchPullbackMetric (g : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N s) (hms : (m : ℕ∞ω) + 1 ≤ s) :
    ContMDiffRiemannianMetric I m E
      (TangentSpace I : (⟨Φ.source, Φ.open_source⟩ : Opens M) → Type _) :=
  finitePullbackMetric (g.restrictOpen ⟨Φ.target, Φ.open_target⟩)
    (finitePatchDiffeomorph Φ) (by simp) hms

theorem finitePatchPullbackMetric_inner (g : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N s) (hms : (m : ℕ∞ω) + 1 ≤ s)
    (x : (⟨Φ.source, Φ.open_source⟩ : Opens M)) (v w : TangentSpace I x) :
    (finitePatchPullbackMetric g Φ hms).inner x v w =
      g.inner (Φ x) (mfderiv I J Φ (x : M) v) (mfderiv I J Φ (x : M) w) := by
  rw [finitePatchPullbackMetric, finitePullbackMetric_inner]
  rw [finitePatchDiffeomorph_mfderiv Φ,
    finitePatchDiffeomorph_mfderiv Φ]
  rfl

section Sectional

variable {J₀ : ModelWithCorners ℝ E H'} [I.Boundaryless] [J₀.Boundaryless]
  [IsManifold J₀ ∞ N]

theorem finitePatchPullbackMetric_sectional
    (g : SmoothRiemannianMetric J₀ N) (Φ : PartialDiffeomorph I J₀ M N s)
    (hms : (m : ℕ∞ω) + 1 ≤ s) (hm : 2 ≤ m)
    (x : (⟨Φ.source, Φ.open_source⟩ : Opens M)) (v w : TangentSpace I x) :
    (finitePatchPullbackMetric g Φ hms).sectionalCurvature x v w =
      (g.restrictOpen ⟨Φ.target, Φ.open_target⟩).sectionalCurvature
        (finitePatchDiffeomorph Φ x) (mfderiv I J₀ Φ (x : M) v)
        (mfderiv I J₀ Φ (x : M) w) := by
  have hs : (3 : ℕ∞ω) ≤ s :=
    (show (3 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 by exact_mod_cast Nat.succ_le_succ hm).trans hms
  let f : (⟨Φ.source, Φ.open_source⟩ : Opens M) ≃ₘ^3⟮I, J₀⟯
      (⟨Φ.target, Φ.open_target⟩ : Opens N) :=
    { toEquiv := (finitePatchDiffeomorph Φ).toEquiv
      contMDiff_toFun := (finitePatchDiffeomorph Φ).contMDiff_toFun.of_le hs
      contMDiff_invFun := (finitePatchDiffeomorph Φ).contMDiff_invFun.of_le hs }
  have hmetric (y : (⟨Φ.source, Φ.open_source⟩ : Opens M))
      (a b : TangentSpace I y) :
      (finitePatchPullbackMetric g Φ hms).inner y a b =
        (g.restrictOpen ⟨Φ.target, Φ.open_target⟩).inner (f y)
          (mfderiv I J₀ f y a) (mfderiv I J₀ f y b) := by
    exact finitePullbackMetric_inner _ _ _ _ y a b
  have h := Bundle.ContMDiffRiemannianMetric.sectionalCurvature_eq_of_pullback
    (finitePatchPullbackMetric g Φ hms) (g.restrictOpen ⟨Φ.target, Φ.open_target⟩)
    (by exact_mod_cast hm) (by simp) f hmetric x v w
  change _ = (g.restrictOpen ⟨Φ.target, Φ.open_target⟩).sectionalCurvature
    (finitePatchDiffeomorph Φ x) (mfderiv I J₀ (finitePatchDiffeomorph Φ) x v)
      (mfderiv I J₀ (finitePatchDiffeomorph Φ) x w) at h
  simpa only [finitePatchDiffeomorph_mfderiv] using h

private theorem smooth_sectional_mul_gram {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] [T2Space P]
    (g : SmoothRiemannianMetric I P) (x : P) (v w : TangentSpace I x) :
    g.sectionalCurvature x v w *
        (g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2) =
      Curvature.metricRm04StandardAt g x v w w v := by
  by_cases hden : g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 = 0
  · have hdep : ¬LinearIndependent ℝ ![v, w] := by
      intro hind
      have hp := Analysis.bilin_gram_pos_of_linearIndependent
        (B := (g.inner x : E →L[ℝ] E →L[ℝ] ℝ)) (g.symm x)
        (ContinuousLinearMap.isCoercive_of_posDef _ fun a ha => g.pos x a ha) hind
      exact hp.ne' hden
    rw [hden, mul_zero, metricRm04StandardAt_eq_zero_of_not_linearIndependent g x v w hdep]
  · rw [Bundle.ContMDiffRiemannianMetric.sectionalCurvature_eq_smooth,
      Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div,
      div_mul_cancel₀ _ hden]

theorem finitePatchPullbackMetric_numerator
    (g : SmoothRiemannianMetric J₀ N) (Φ : PartialDiffeomorph I J₀ M N s)
    (hms : (m : ℕ∞ω) + 1 ≤ s) (hm : 2 ≤ m)
    (x : (⟨Φ.source, Φ.open_source⟩ : Opens M)) (v w : TangentSpace I x) :
    let h := finitePatchPullbackMetric g Φ hms
    h.sectionalCurvature x v w *
        (h.inner x v v * h.inner x w w - (h.inner x v w) ^ 2) =
      Curvature.metricRm04StandardAt g (Φ x) (mfderiv I J₀ Φ (x : M) v)
        (mfderiv I J₀ Φ (x : M) w) (mfderiv I J₀ Φ (x : M) w)
        (mfderiv I J₀ Φ (x : M) v) := by
  dsimp only
  rw [finitePatchPullbackMetric_sectional g Φ hms hm]
  have h := smooth_sectional_mul_gram (I := J₀)
    (g.restrictOpen ⟨Φ.target, Φ.open_target⟩) (finitePatchDiffeomorph Φ x)
    (mfderiv I J₀ Φ (x : M) v) (mfderiv I J₀ Φ (x : M) w)
  rw [finitePatchPullbackMetric_inner, finitePatchPullbackMetric_inner,
    finitePatchPullbackMetric_inner]
  change _ = _ at h
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hrestrict := Curvature.metricRm04StandardAt_restrictOpen g
    (⟨Φ.target, Φ.open_target⟩ : Opens N) (finitePatchDiffeomorph Φ x)
    (mfderiv I J₀ Φ (x : M) v) (mfderiv I J₀ Φ (x : M) w)
    (mfderiv I J₀ Φ (x : M) w) (mfderiv I J₀ Φ (x : M) v)
  rw [DifferentialGeometry.mfderiv_subtype_val (I := J₀)
    (⟨Φ.target, Φ.open_target⟩ : Opens N) (finitePatchDiffeomorph Φ x)] at hrestrict
  exact h.trans (hrestrict.trans (by rfl))

end Sectional

end DifferentialGeometry.Geometry
