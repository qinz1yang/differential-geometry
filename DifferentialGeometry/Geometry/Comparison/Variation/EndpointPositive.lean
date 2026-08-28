import DifferentialGeometry.Analysis.ODE.IndexFormPositive
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrameIndex

set_option autoImplicit false

open Set Function Manifold Bundle
open scoped Topology Manifold ContDiff RealInnerProductSpace Bundle

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
omit [InnerProductSpace ℝ E] in
omit [SigmaCompactSpace M] in
theorem jacobi_pair_pos
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (J : ∀ t : ℝ, TangentSpace I (γ t))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) 1))
    (hJdiff : ∀ t, DifferentiableAt ℝ
      (chartRepAt (I := I) γ J t) t)
    (hDJdiff : ∀ t, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hJac : ∀ t ∈ Icc (0 : ℝ) 1, IsJacobiAt (I := I) g γ J t)
    (hJ0 : J 0 = 0) (hJ1 : J 1 ≠ 0)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t))
    (hJperp : ∀ t ∈ Icc (0 : ℝ) 1,
      g.inner (γ t) (J t) (curveVelocity (I := I) γ t) = 0)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκπ : κ < (Real.pi / 2) ^ 2)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) 1,
      g.inner (γ t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita
                (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t))
          (J t) ≤
        κ * g.inner (γ t) (J t) (J t)) :
    0 < g.inner (γ 1) (covDerivAlong (I := I) g γ J 1) (J 1) := by
  classical
  let DJ : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t => covDerivAlong (I := I) g γ J t
  obtain ⟨F, hFdiff, hFpar, hON, hFperp, hFbundle⟩ :=
    exists_perp_par_pos (I := I) g γ hγ
      (L := (1 : ℝ)) zero_lt_one hgeo
      (hspeed 0 ⟨le_rfl, zero_le_one⟩)
  let e : Fin (Module.finrank ℝ E - 1) →
      ∀ t : ℝ, TangentSpace I (γ t) :=
    fun i => (F i).toFun
  let R : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCurvOp (I := I) g γ e
  let y : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCoeff (I := I) g e J
  let v : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCoeff (I := I) g e DJ
  have hode (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt y (v t) t ∧ HasDerivAt v (-(R t) (y t)) t := by
    simpa only [y, v, R, e, DJ] using
      perpCoeff_ode (I := I) (n := ∞) (by simp) g γ e J t
        hγ.contMDiffAt
        (fun i => hFdiff i t ht)
        (hJdiff t) (hDJdiff t)
        (fun i => hFpar i t ht)
        (hJac t ht) (by simp) (hspeed t ht)
        (fun i => hFperp t ht i)
        (hJperp t ht) (fun i j => hON t ht i j)
  have hsol : IsJacobiSolOn R 0 1 y v :=
    { deriv_fst := fun t ht => (hode t ht).1.hasDerivWithinAt
      deriv_snd := fun t ht => (hode t ht).2.hasDerivWithinAt }
  have hRcont : ContinuousOn R (Icc (0 : ℝ) 1) := by
    exact (perpCurv_smooth (I := I) g γ hγ e
      (fun i => hFbundle i)).continuous.continuousOn
  have hy0 : y 0 = 0 :=
    perpCoeff_zero (I := I) g e J 0 hJ0
  have hy1 : y 1 ≠ 0 := by
    exact perpCoeff_ne_zero (I := I) g e J 1 (by simp)
      (hspeed 1 ⟨zero_le_one, le_rfl⟩)
      (fun i => hFperp 1 ⟨zero_le_one, le_rfl⟩ i)
      (hJperp 1 ⟨zero_le_one, le_rfl⟩)
      (fun i j => hON 1 ⟨zero_le_one, le_rfl⟩ i j) hJ1
  have hupper : ∀ t ∈ Icc (0 : ℝ) 1,
      ⟪R t (y t), y t⟫ ≤ κ * ‖y t‖ ^ 2 := by
    intro t ht
    have hJlift :
        (∑ i, y t i • e i t) = J t := by
      simpa only [perpFrameLift, y] using
        perpLift_coeff (I := I) g e J t (by simp)
          (hspeed t ht) (fun i => hFperp t ht i)
          (hJperp t ht) (fun i j => hON t ht i j)
    have hinner :
        g.inner (γ t) (J t) (J t) = inner ℝ (y t) (y t) := by
      rw [← hJlift]
      exact perpLift_inner (I := I) g e (y t) (y t) t
        (fun i j => hON t ht i j)
    calc
      ⟪R t (y t), y t⟫ =
          g.inner (γ t)
            ((DifferentialGeometry.Geometry.Curvature.riemannOp
                (DifferentialGeometry.Geometry.Connection.LeviCivita
                  (I := I) g) (γ t))
              (∑ i, y t i • e i t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t))
            (∑ i, y t i • e i t) :=
        perpCurv_inner (I := I) g γ e (y t) (y t) t
      _ = g.inner (γ t)
            ((DifferentialGeometry.Geometry.Curvature.riemannOp
                (DifferentialGeometry.Geometry.Connection.LeviCivita
                  (I := I) g) (γ t))
              (J t) (curveVelocity (I := I) γ t)
              (curveVelocity (I := I) γ t))
            (J t) := by rw [hJlift]
      _ ≤ κ * g.inner (γ t) (J t) (J t) := hcurv t ht
      _ = κ * ‖y t‖ ^ 2 := by
        rw [hinner, real_inner_self_eq_norm_sq]
  have hpair :
      0 < inner ℝ (v 1) (y 1) :=
    hsol.end_pair_pos hRcont hy0 hy1 hκ0 hκπ hupper
  have hJlift :
      (∑ i, y 1 i • e i 1) = J 1 := by
    simpa only [perpFrameLift, y] using
      perpLift_coeff (I := I) g e J 1 (by simp)
        (hspeed 1 ⟨zero_le_one, le_rfl⟩)
        (fun i => hFperp 1 ⟨zero_le_one, le_rfl⟩ i)
        (hJperp 1 ⟨zero_le_one, le_rfl⟩)
        (fun i j => hON 1 ⟨zero_le_one, le_rfl⟩ i j)
  have hread :
      g.inner (γ 1) (DJ 1) (J 1) = inner ℝ (v 1) (y 1) := by
    rw [← hJlift, map_sum, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show v 1 i = g.inner (γ 1) (e i 1) (DJ 1) by
        simp only [v, perpCoeff_apply],
      g.symm (γ 1) (e i 1) (DJ 1)]
    rw [map_smul]
    simp [RCLike.inner_apply]
  rw [hread]
  exact hpair

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
