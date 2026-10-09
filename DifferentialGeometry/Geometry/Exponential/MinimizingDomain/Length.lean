import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PathLength

noncomputable section
open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold
namespace DifferentialGeometry.Geometry.Riemannian.Exponential
open Variation Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]

theorem arcLength_expMap_smul
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) {L : ℝ}
    (hdom : (show TangentSpace I p from L • u) ∈ expDomain (I := I) g p) :
    arcLength (I := I) g (fun t => expMap (I := I) g p (show TangentSpace I p from t • u)) 0 L =
      L * Real.sqrt (g.inner p u u) := by
  obtain ⟨η, S, hS, hconn, h0S, hLS, hη⟩ := smul_mem_expDomain_iff.mp hdom
  have hseg (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) L) :
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p :=
    smul_mem_expDomain_iff.mpr
      ⟨η, S, hS, hconn, h0S, hconn.ordConnected.uIcc_subset h0S hLS ht, hη⟩
  unfold arcLength
  calc
    _ = ∫ _t in (0 : ℝ)..L, Real.sqrt (g.inner p u u) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact congrArg Real.sqrt (inner_curveVelocity_expMap_smul (I := I) g p u (hseg t ht))
    _ = L * Real.sqrt (g.inner p u u) := by simp

section
variable [(y : M) → ENorm (TangentSpace I y)]

theorem arcLength_expMap_smul_le_of_le_riemannianEDist
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (p : M) (u : E) {L : ℝ} (hL : 0 ≤ L)
    (hdom : (show TangentSpace I p from L • u) ∈ expDomain (I := I) g p)
    (hmin : ENNReal.ofReal (Real.sqrt (g.inner p (L • u) (L • u))) ≤
      riemannianEDist I p (expMap (I := I) g p (show TangentSpace I p from L • u)))
    {η : ℝ → M} (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L))
    (hη0 : η 0 = p) (hηL : η L = expMap (I := I) g p (show TangentSpace I p from L • u)) :
    arcLength (I := I) g (fun t => expMap (I := I) g p (show TangentSpace I p from t • u)) 0 L ≤
      arcLength (I := I) g η 0 L := by
  let : (y : M) → ENormSMulClass ℝ (TangentSpace I y) := fun y => ⟨fun r v => by
    rw [hEnorm, hEnorm, Real.enorm_eq_ofReal_abs]
    rw [gInner_smul_self (I := I) g y r v, Real.sqrt_mul (sq_nonneg r),
      Real.sqrt_sq_eq_abs, ENNReal.ofReal_mul (abs_nonneg r)]⟩
  have hd := riemannianEDist_le_arcLength_of_enorm_eq (I := I) g hL hη
    (fun t _ => hEnorm (η t) (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)))
  have hd' : riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from L • u)) ≤
        ENNReal.ofReal (arcLength (I := I) g η 0 L) := by
    simpa only [hη0, hηL] using! hd
  have hn : 0 ≤ arcLength (I := I) g η 0 L :=
    intervalIntegral.integral_nonneg hL (fun _ _ => Real.sqrt_nonneg _)
  rw [arcLength_expMap_smul g p u hdom]
  have hnorm : Real.sqrt (g.inner p (L • u) (L • u)) =
      L * Real.sqrt (g.inner p u u) := by
    simpa only using! sqrt_gInner_smul_self (I := I) g p hL (show TangentSpace I p from u)
  rw [hnorm] at hmin
  exact (ENNReal.ofReal_le_ofReal_iff hn).mp (hmin.trans hd')
end

section
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance tangentSpaceNormedAddCommGroup
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

theorem arcLength_expMap_smul_le_of_mem_minimizingDomain
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : E) {L : ℝ} (hL : 0 ≤ L)
    (hmin : L • u ∈ minimizingDomain (I := I) g p)
    {η : ℝ → M} (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L))
    (hη0 : η 0 = p) (hηL : η L = expMap (I := I) g p (show TangentSpace I p from L • u)) :
    arcLength (I := I) g (fun t => expMap (I := I) g p (show TangentSpace I p from t • u)) 0 L ≤
      arcLength (I := I) g η 0 L := by
  exact arcLength_expMap_smul_le_of_le_riemannianEDist (I := I) g hEnorm p u hL
    (minimizingDomain_subset_expDomain (I := I) g p hmin) hmin.le hη hη0 hηL
end

end DifferentialGeometry.Geometry.Riemannian.Exponential
