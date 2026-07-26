import DifferentialGeometry.Geometry.Comparison.Volume.RadialGronwall

set_option linter.unusedSectionVars false

/-!
# Explicit radial-Jacobi radius packages

This file gives the radial Rm04 package a named source radius.  The older
existential declarations in `RadialGronwall` remain compatibility APIs; the
quantitative H6 route should use the declarations here so that radius bounds
can be compared across a sequence.
-/

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

section Radial

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The differentiability and Rm04 ODE data used by the radial endpoint
comparison, available on one prescribed source radius. -/
def Rm04DataAt
    (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) : Prop :=
  ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
    ∀ {K R Vb b : ℝ}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
    Real.sqrt (g.inner p x x) ≤ Vb →
    Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : ℝ)) *
        R * Vb ^ 2 ≤ K →
    (∀ t (_ht : t ∈ Ioo (0 : ℝ) b),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
    (∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t) ∧
    (∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g
            (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t) t) ∧
    ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g
            (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g
            (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t) ≤
      K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)

/-- The canonical Jacobi launch radius lies inside the exponential smoothness
radius used to construct it. -/
lemma jacobi_radius_le_c2
    (g : SmoothRiemannianMetric I M) (p : M) :
    jacobiVarRadius (I := I) g p ≤ expMapC2Radius (I := I) g p := by
  rw [jacobiVarRadius]
  have hpos := expMapC2Radius_pos (I := I) g p
  linarith

private lemma jacobiRadius_lt_exp
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hx : ‖x‖ < jacobiVarRadius (I := I) g p) :
    ‖x‖ < expMapC2Radius (I := I) g p :=
  hx.trans_le (jacobi_radius_le_c2 (I := I) g p)

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The canonical clamped Jacobi radius supplies the complete radial Rm04 data
package, with no additional existential radius choice. -/
theorem rm04Data_jacobi
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    Rm04DataAt (I := I) g p (jacobiVarRadius (I := I) g p) := by
  classical
  intro x w hx hw K R Vb b hK hVb hb hlaunch hKbound hRm
  have hdiff := jacobi_diff_of_lt (I := I) g p hx hw hb
  refine ⟨?_, ?_, ?_⟩
  · simpa [radialCurve, radialJacobiField] using hdiff.1
  · simpa [radialCurve, radialJacobiField] using hdiff.2
  · have hJac : ∀ t ∈ Ioo (0 : ℝ) b,
        IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t := by
      intro t ht
      have ht01 : t ∈ Ioo (0 : ℝ) 1 :=
        ⟨ht.1, lt_of_lt_of_le ht.2 hb⟩
      simpa [radialCurve, radialJacobiField] using
        (radial_jacobi_of_lt (I := I) g p hx hw t ht01)
    have hJac0 :
        IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) 0 := by
      simpa [radialCurve, radialJacobiField] using
        (jacobi_zero_of_lt (I := I) g hEnorm p hx hw)
    have hxrad : ‖x‖ < expMapC2Radius (I := I) g p :=
      jacobiRadius_lt_exp (I := I) g p hx
    have hbasis :
        ∀ t : ℝ, t ∈ Ioo (0 : ℝ) b →
          ∃ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ
              (TangentSpace I (radialCurve (I := I) g p x t)),
            ∀ i j,
              g.inner (radialCurve (I := I) g p x t)
                  (basis i) (basis j) =
                if i = j then (1 : ℝ) else 0 := by
      intro t _ht
      simpa [show Module.finrank ℝ
          (TangentSpace I (radialCurve (I := I) g p x t)) =
            Module.finrank ℝ E from rfl] using
        (DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis
          (I := I) g (radialCurve (I := I) g p x t))
    choose basis hON using hbasis
    have hcurv : ∀ t ∈ Ioo (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
            ((DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
                (radialCurve (I := I) g p x t))
              (radialJacobiField (I := I) g p x w t)
              (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
              (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
            ((DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
                (radialCurve (I := I) g p x t))
              (radialJacobiField (I := I) g p x w t)
              (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
              (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤
          K ^ 2 * g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x w t)
            (radialJacobiField (I := I) g p x w t) := by
      refine curv_sq_of_rm04_velocity_Ioo (I := I) g p x w hK hVb basis
        (fun t ht i j => hON t ht i j)
        (radial_speed_le (I := I) g p x hxrad hb hlaunch) ?_
      intro t ht
      set C : ℝ :=
        Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : ℝ))
      set A : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t)))
      have hCnn : 0 ≤ C := Real.sqrt_nonneg _
      have hVsq : 0 ≤ Vb ^ 2 := sq_nonneg Vb
      have hA_le_R : A ≤ R := hRm t ht
      have hmul : C * A * Vb ^ 2 ≤ C * R * Vb ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA_le_R hCnn) hVsq
      exact hmul.trans hKbound
    exact ode_Ico_of_Ioo_d2 (I := I) g p x w hJac hcurv
      (d2_zero_of_jac0 (I := I) g p x w hJac0)

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Upper endpoint estimate for one arbitrary direction on the canonical
Jacobi launch radius. -/
theorem rm04_one_le
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (x w : E)
    {a K R Vb b A B : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hVb : 0 ≤ Vb)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h1b : (1 : ℝ) ≤ b)
    (hx : ‖x‖ < jacobiVarRadius (I := I) g p)
    (hw : ‖a • w‖ < jacobiVarRadius (I := I) g p)
    (hlaunch : Real.sqrt (g.inner p x x) ≤ Vb)
    (hKbound :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : ℝ)) *
          R * Vb ^ 2 ≤ K)
    (hRm : ∀ t (_ht : t ∈ Ioo (0 : ℝ) b),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι =
        Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hinit : Real.sqrt (g.inner p (a • w) (a • w)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B) :
    Real.sqrt (g.inner
      (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤ B := by
  have hdata := rm04Data_jacobi (I := I) g hEnorm p
  obtain ⟨hJdiff, hDJdiff, hODE⟩ :=
    hdata x (a • w) hx hw hK hVb hb1 hlaunch hKbound hRm
  have hderiv : ∀ y z : E,
      ‖y‖ < jacobiVarRadius (I := I) g p →
      ‖z‖ < jacobiVarRadius (I := I) g p →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from (v • y)) : M))
        (radialJacobiField (I := I) g p y z) 0 : E) = z := by
    intro y z hy hz
    simpa [radialJacobiField] using
      (radial_deriv_of_lt (I := I) g p hy hz)
  exact radialJacobi_one_le_of_scaled_radius_at (I := I) g p x w
    ha hK hb0 h1b hγ hcard F hpar hON hFdiff hJdiff hDJdiff hODE
    hderiv hx hw hinit hmodel (jacobiRadius_lt_exp (I := I) g p hx)

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Lower endpoint estimate for one arbitrary direction on the canonical
Jacobi launch radius. -/
theorem rm04_one_ge
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (x w : E)
    {a K R Vb b B : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hVb : 0 ≤ Vb)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h1b : (1 : ℝ) ≤ b)
    (hx : ‖x‖ < jacobiVarRadius (I := I) g p)
    (hw : ‖a • w‖ < jacobiVarRadius (I := I) g p)
    (hlaunch : Real.sqrt (g.inner p x x) ≤ Vb)
    (hKbound :
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : ℝ)) *
          R * Vb ^ 2 ≤ K)
    (hRm : ∀ t (_ht : t ∈ Ioo (0 : ℝ) b),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι =
        Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hmodel :
      a * B ≤ Real.sqrt (g.inner p (a • w) (a • w)) -
        gronwallBound 0 (max K 1)
          (K * (b * Real.sqrt (g.inner p (a • w) (a • w)))) 1) :
    B ≤ Real.sqrt (g.inner
      (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) := by
  have hdata := rm04Data_jacobi (I := I) g hEnorm p
  obtain ⟨hJdiff, hDJdiff, hODE⟩ :=
    hdata x (a • w) hx hw hK hVb hb1 hlaunch hKbound hRm
  have hderiv : ∀ y z : E,
      ‖y‖ < jacobiVarRadius (I := I) g p →
      ‖z‖ < jacobiVarRadius (I := I) g p →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from (v • y)) : M))
        (radialJacobiField (I := I) g p y z) 0 : E) = z := by
    intro y z hy hz
    simpa [radialJacobiField] using
      (radial_deriv_of_lt (I := I) g p hy hz)
  exact radialJacobi_one_ge_of_scaled_radius_at (I := I) g p x w
    ha hK hb0 h1b hγ hcard F hpar hON hFdiff hJdiff hDJdiff hODE
    hderiv hx hw hmodel (jacobiRadius_lt_exp (I := I) g p hx)

end Radial

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
