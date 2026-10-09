import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientVolumeComparison

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold ContDiff

private theorem square_retiming_bounds {b c a s : ℝ}
    (hc : 1 ≤ c) (hs : s ∈ Icc 0 a)
    (hbound : (c ^ 2 - 1) * a ^ 2 ≤ -b) :
    b - s ^ 2 ≤ -((c * s) ^ 2) ∧
      -((c * s) ^ 2) ≤ 0 ∧
      -((c * s) ^ 2) - (b - s ^ 2) ≤ -b := by
  have hcoef : 0 ≤ c ^ 2 - 1 := by nlinarith
  have hsquare : s ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hscaled : (c ^ 2 - 1) * s ^ 2 ≤ -b :=
    (mul_le_mul_of_nonneg_left hsquare hcoef).trans hbound
  have hscaled_nonneg : 0 ≤ (c ^ 2 - 1) * s ^ 2 :=
    mul_nonneg hcoef (sq_nonneg s)
  refine ⟨?_, neg_nonpos.mpr (sq_nonneg (c * s)), ?_⟩
  · nlinarith only [hscaled]
  · nlinarith only [hscaled_nonneg]

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth

theorem exists_ancientKappa_metric_inner_le_exp_mul_sq
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b c a : ℝ, 1 ≤ c →
      (c ^ 2 - 1) * a ^ 2 ≤ -b → ∀ s ∈ Icc 0 a,
      ∀ x : F.M, ∀ v : TangentSpace I x,
      (F.S.base.metric (b - s ^ 2)).inner x v v ≤
        Real.exp (C * (-b)) * (F.S.base.metric (-((c * s) ^ 2))).inner x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨K, hK, hmetric⟩ := exists_ancientKappa_metric_inner_le_exp F hF
  refine ⟨2 * K, mul_nonneg (by norm_num) hK, ?_⟩
  intro b c a hc hbound s hs x v
  obtain ⟨horder, htime, hgap⟩ := square_retiming_bounds hc hs hbound
  apply (hmetric (b - s ^ 2) (-((c * s) ^ 2)) horder htime x v).trans
  apply mul_le_mul_of_nonneg_right _ (metric_inner_self_nonneg _ _ _)
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hgap (mul_nonneg (by norm_num) hK))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
