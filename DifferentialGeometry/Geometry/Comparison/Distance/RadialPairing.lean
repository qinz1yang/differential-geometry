import DifferentialGeometry.Geometry.Operator.DirectionalDerivative
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import DifferentialGeometry.Geometry.Comparison.Distance.Gradient
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Gradient

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open Geometry.Riemannian
open Geometry.Riemannian.Exponential
open Geometry.Riemannian.VolumeComparison

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

theorem dist_action_radial
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (φ : C^∞⟮I, M; Real⟯) {p : M} {v : TangentSpace I p}
    (hv : v ∈ SegmentInt (I := I) g hEnorm p) (hv0 : v ≠ 0) :
    let q := expMapIntrinsic (I := I) g hEnorm p v
    let ρ : M → Real := fun y => (riemannianEDist I p y).toReal
    tangentSectionAction (I := I) (gradG (I := I) g φ) ρ q =
      (Real.sqrt (g.inner p v v))⁻¹ *
        NormedSpace.fromTangentSpace (φ q)
          (mfderiv I 𝓘(Real, Real) φ q
            (intrinsicVelocityLift (I := I) g hEnorm p v 1).snd) := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let q := expMapIntrinsic (I := I) g hEnorm p v
  let ρ : M → Real := fun y => (riemannianEDist I p y).toReal
  have hrad := dist_grad_radial (I := I) g hEnorm hv hv0
  change mfderiv I 𝓘(Real, Real) ρ q
      ((gradG (I := I) g φ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) q) = _
  rw [← inner_gradFun_right (I := I) g ρ q]
  have hrad' : gradientFun (I := I) g ρ q =
      (Real.sqrt (g.inner p v v))⁻¹ •
        (intrinsicVelocityLift (I := I) g hEnorm p v 1).snd := by
    simpa only [ρ, q] using hrad.2
  rw [DifferentialGeometry.Geometry.Connection.gradient_eq_gradFun (I := I) g ρ q] at hrad'
  rw [hrad']
  let a := (Real.sqrt (g.inner p v v))⁻¹
  let V : TangentSpace I q :=
    (intrinsicVelocityLift (I := I) g hEnorm p v 1).snd
  let X : TangentSpace I q :=
    (gradG (I := I) g φ :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) q
  change g.inner q X (a • V) = a * _
  calc
    g.inner q X (a • V) = g.inner q (a • V) X := g.symm q X (a • V)
    _ = (a • g.inner q V) X := by
      exact congrArg (fun L : TangentSpace I q →L[Real] Real => L X)
        ((g.inner q).map_smul a V)
    _ = a * g.inner q V X := by
      rw [smul_apply, smul_eq_mul]
    _ = a * g.inner q X V := by rw [g.symm q V X]
    _ = a * NormedSpace.fromTangentSpace (φ q)
        (mfderiv I 𝓘(Real, Real) φ q V) := by
      change a * g.inner q
          ((gradG (I := I) g φ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) q) V = _
      rw [grad_g_apply, inner_gradFun (I := I) g φ q]
      rfl

theorem dist_action_scaled
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (φ : C^∞⟮I, M; Real⟯) {p : M} (u : TangentSpace I p)
    (hu : 0 < g.inner p u u) {r : Real} (hr : 0 < r)
    (hv : (r • u : TangentSpace I p) ∈ SegmentInt (I := I) g hEnorm p) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let ρ : M → Real := fun y ↦ (riemannianEDist I p y).toReal
    tangentSectionAction (I := I) (gradG (I := I) g φ) ρ (γ r) =
      (Real.sqrt (g.inner p u u))⁻¹ * deriv (fun s ↦ φ (γ s)) r := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let γ := intrinsicGeodesic (I := I) g hEnorm p u
  let γr := intrinsicGeodesic (I := I) g hEnorm p (r • u)
  let ρ : M → Real := fun y ↦ (riemannianEDist I p y).toReal
  dsimp only
  have hu0 : u ≠ 0 := by
    intro huz
    subst u
    simp at hu
  have hru0 : (r • u : TangentSpace I p) ≠ 0 := smul_ne_zero hr.ne' hu0
  have hq : expMapIntrinsic (I := I) g hEnorm p (r • u) = γ r := by
    simpa only [expMapIntrinsic_def, γ, mul_one] using
      (intrinsicGeodesic_smul (I := I) g hEnorm p u r)
  have hrad := dist_action_radial (I := I) g hEnorm φ hv hru0
  dsimp only at hrad
  have hφ (x : M) : MDifferentiableAt I 𝓘(Real, Real) (φ : M → Real) x :=
    φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hγ : MDifferentiableAt 𝓘(Real, Real) I γ r :=
    (intrinsicGeodesic_contMDiff (I := I) g hEnorm p u).contMDiffAt.mdifferentiableAt
      (by simp)
  have hγr : MDifferentiableAt 𝓘(Real, Real) I γr 1 :=
    (intrinsicGeodesic_contMDiff (I := I) g hEnorm p (r • u)).contMDiffAt.mdifferentiableAt
      (by simp)
  have hDu := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
    I (φ : M → Real) γ r (hφ (γ r)) hγ
  have hDr := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
    I (φ : M → Real) γr 1 (hφ (γr 1)) hγr
  have hscale : HasDerivAt (fun s : Real ↦ r * s) r 1 := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id (x := (1 : Real))).const_mul r
  have hDu1 : HasDerivAt (fun s ↦ φ (γ s))
      (NormedSpace.fromTangentSpace (φ (γ r))
        (mfderiv I 𝓘(Real, Real) φ (γ r)
        (mfderiv 𝓘(Real, Real) I γ r
          (DifferentialGeometry.Analysis.Calculus.realTangentOne r)))) (r * 1) := by
    simpa only [mul_one] using hDu
  have hcomp := hDu1.comp 1 hscale
  have hscaled : deriv (fun s ↦ φ (γ (r * s))) 1 =
      r * deriv (fun s ↦ φ (γ s)) r := by
    calc
      deriv (fun s ↦ φ (γ (r * s))) 1 =
          (NormedSpace.fromTangentSpace (φ (γ r))
            (mfderiv I 𝓘(Real, Real) φ (γ r)
              (mfderiv 𝓘(Real, Real) I γ r
                (DifferentialGeometry.Analysis.Calculus.realTangentOne r)))) * r := hcomp.deriv
      _ = r * deriv (fun s ↦ φ (γ s)) r := by
        rw [← hDu.deriv]
        ring
  have hφscale : (fun s ↦ φ (γr s)) = fun s ↦ φ (γ (r * s)) := by
    funext s
    dsimp only [γr, γ]
    rw [← intrinsicGeodesic_smul (I := I) g hEnorm p (r • u) s]
    exact congrArg (fun x : M ↦ φ x) <| by
      simpa only [smul_smul, mul_comm] using
        (intrinsicGeodesic_smul (I := I) g hEnorm p u (r * s))
  have hnorm : Real.sqrt (g.inner p (r • u) (r • u)) =
      r * Real.sqrt (g.inner p u u) :=
    sqrt_gInner_smul_self (I := I) g p hr.le u
  have hspeed : 0 < Real.sqrt (g.inner p u u) := Real.sqrt_pos.mpr hu
  calc
    tangentSectionAction (I := I) (gradG (I := I) g φ) ρ (γ r) =
        tangentSectionAction (I := I) (gradG (I := I) g φ) ρ
          (expMapIntrinsic (I := I) g hEnorm p (r • u)) := by rw [hq]
    _ = (Real.sqrt (g.inner p (r • u) (r • u)))⁻¹ *
        NormedSpace.fromTangentSpace
          (φ (expMapIntrinsic (I := I) g hEnorm p (r • u)))
          (mfderiv I 𝓘(Real, Real) φ
            (expMapIntrinsic (I := I) g hEnorm p (r • u))
            (intrinsicVelocityLift (I := I) g hEnorm p (r • u) 1).snd) := hrad
    _ = (Real.sqrt (g.inner p (r • u) (r • u)))⁻¹ *
        deriv (fun s ↦ φ (γr s)) 1 := by
      rw [hDr.deriv]
      rfl
    _ = (Real.sqrt (g.inner p (r • u) (r • u)))⁻¹ *
        deriv (fun s ↦ φ (γ (r * s))) 1 := by rw [hφscale]
    _ = (Real.sqrt (g.inner p (r • u) (r • u)))⁻¹ *
        (r * deriv (fun s ↦ φ (γ s)) r) := by rw [hscaled]
    _ = (Real.sqrt (g.inner p u u))⁻¹ * deriv (fun s ↦ φ (γ s)) r := by
      rw [hnorm]
      field_simp [hr.ne', hspeed.ne']

theorem dist_action_param
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (φ : C^∞⟮I, M; Real⟯) {p : M} (u : TangentSpace I p)
    (hu : g.inner p u u = 1) {r : Real} (hr : 0 < r)
    (hv : (r • u : TangentSpace I p) ∈ SegmentInt (I := I) g hEnorm p) :
    let γ := intrinsicGeodesic (I := I) g hEnorm p u
    let ρ : M → Real := fun y ↦ (riemannianEDist I p y).toReal
    tangentSectionAction (I := I) (gradG (I := I) g φ) ρ (γ r) =
      deriv (fun s ↦ φ (γ s)) r := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  have huPos : 0 < g.inner p u u := by rw [hu]; exact zero_lt_one
  simpa only [hu, Real.sqrt_one, inv_one, one_mul] using
    dist_action_scaled (I := I) g hEnorm φ u huPos hr hv

end DifferentialGeometry.Geometry.Riemannian
