import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5EvolutionCommutator
import DifferentialGeometry.Geometry.Operator.Hessian.TimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Intrinsic

/-!
# The time derivative of the Hessian along a surface Ricci flow

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (potential gauge, design D18 (ii),
review 18 §1.2, second input).

Along a Ricci flow `∂ₜ g = -2 Ric = -R g` of surfaces, for a function family `f` jointly smooth on
`(0, T) × M` with time derivative `fₜ` at `t`:
* `surfaceFlow_nablaRicci_eq`: `∇Ric = ½ dR ⊗ g` (`covStep_two_of_eq_smul_metric`);
* `surfaceFlow_leviCivitaVariation_pair`: `g(∂ₜΓ(w, v), z) = ½ (-dR(v) g(w, z) - dR(w) g(v, z)
  + dR(z) g(v, w))` (`leviCivita_variation_pair_eq_neg_ricci_cov_deriv`);
* `surfaceFlow_hessFun_hasDerivAt`: `∂ₜ ∇²f = ∇²fₜ + 𝔅` with
  `𝔅(v, w) = ½ (dR(v) df(w) + df(v) dR(w) - ⟨∇R, ∇f⟩ g(v, w))`, from
  `hessianSec_leviCivita_hasDerivAt` (`∂ₜ Hess = Hess(∂ₜ f) - df(∂ₜΓ)`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open Bundle Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {T : ℝ} {hT : 0 < T}

theorem surfaceFlow_nablaRicci_eq (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (t : ℝ) (x : M)
    (a b c : TangentSpace I x) :
    totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x (Fin.cons a (vec2 b c)) =
      mvfderiv (I := I) (S.scalar t) x a / 2 * (S.family.metric t).inner x b c := by
  have hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => S.scalar t y / 2) :=
    (scalarSmoothOfSolution S t).div_const 2
  have hP : ∀ y (v w : TangentSpace I y), S.ricci t y ![v, w] =
      S.scalar t y / 2 * (S.family.metric t).inner y v w := by
    intro y v w
    have e : (![v, w] : Fin 2 → TangentSpace I y) = vec2 v w := by
      funext i; fin_cases i <;> rfl
    rw [e]
    simp only [SolutionOn.ricci, SolutionFamily.ricci, metricRicci_apply,
      metricRicciAt_apply_eq_ricciTensor, SolutionOn.scalar, SolutionFamily.scalar,
      SolutionOn.family_metric]
    exact ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two _ hdim _ _ _
  have h := covStep_two_of_eq_smul_metric (S.family.metric t) (S.ricci t) hφ hP x a b c
  have e : (Fin.cons a (vec2 b c) : Fin 3 → TangentSpace I x) = ![a, b, c] := by
    funext i; fin_cases i <;> rfl
  rw [e]
  refine h.trans ?_
  congr 1
  have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (S.scalar t) x :=
    (scalarSmoothOfSolution S t x).mdifferentiableAt (by simp)
  have hfun : (fun y => S.scalar t y / 2) = fun y => (1 / 2 : ℝ) * S.scalar t y := by
    funext y; ring
  rw [hfun, mvfderiv_const_mul I _ hmd]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem surfaceFlow_leviCivitaVariation_pair (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : M) (v w z : TangentSpace I x) :
    (S.family.metric t).inner x (leviCivitaVariation S.family.metric t x w v) z =
      (-(mvfderiv (I := I) (S.scalar t) x v * (S.family.metric t).inner x w z) -
        mvfderiv (I := I) (S.scalar t) x w * (S.family.metric t).inner x v z +
        mvfderiv (I := I) (S.scalar t) x z * (S.family.metric t).inner x v w) / 2 := by
  have hreg : t ∈ (RealTimeInterval.closedOpen 0 T hT).regular := ht
  have h := leviCivita_variation_pair_eq_neg_ricci_cov_deriv S hS ⟨t, hreg⟩ x v w z
  change _ = -totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
        (Fin.cons v (vec2 w z)) -
      totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
        (Fin.cons w (vec2 v z)) +
      totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
        (Fin.cons z (vec2 v w)) at h
  rw [h, surfaceFlow_nablaRicci_eq hdim, surfaceFlow_nablaRicci_eq hdim,
    surfaceFlow_nablaRicci_eq hdim]
  ring

theorem surfaceFlow_hessFun_hasDerivAt (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    {t : ℝ} (ht : t ∈ Ioo 0 T) (ft : M → ℝ) (hft : ContMDiff I 𝓘(ℝ, ℝ) ∞ ft)
    (hderiv : ∀ y, HasDerivAt (fun s => f s y) (ft y) t) (x : M) (v w : TangentSpace I x) :
    HasDerivAt (fun s => hessFun (S.family.metric s) (f s) x v w)
      (hessFun (S.family.metric t) ft x v w +
        (mvfderiv (I := I) (S.scalar t) x v * mvfderiv (I := I) (f t) x w +
          mvfderiv (I := I) (f t) x v * mvfderiv (I := I) (S.scalar t) x w -
          mvfderiv (I := I) (S.scalar t) x (gradFun (S.family.metric t) (f t) x) *
            (S.family.metric t).inner x v w) / 2) t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hreg : t ∈ (RealTimeInterval.closedOpen 0 T hT).regular := ht
  have hregN : (RealTimeInterval.closedOpen 0 T hT).regular ∈ 𝓝 t :=
    (RealTimeInterval.closedOpen 0 T hT).regular_isOpen.mem_nhds hreg
  have hg : ∀ y (a b : TangentSpace I y), HasDerivAt (fun r => (S.family.metric r).inner y a b)
      (((-2 : ℝ) • S.ricci t) y (vec2 a b)) t := by
    intro y a b
    simpa [ContMDiffSection.coe_smul, Tensor0SSpace.smul_apply, SolutionOn.ricci,
      SolutionOn.ricciAt] using metricDerivAt S hS ⟨t, hreg⟩ y a b
  have hgs : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ y,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (S.family.metric p.1).inner p.2 (Y p.2) (Z p.2)) (t, y) := by
    intro Y Z y
    exact (hS.smoothMetric.pairSmoothAt (x := y) hregN ![Y, Z]).of_le (by decide)
  have hfj : ∀ y, ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (t, y) := fun y =>
    hf.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ y⟩)
  have h := hessianSec_leviCivita_hasDerivAt S.family.metric ((-2 : ℝ) • S.ricci t) t hg hgs
    (fun s y => f s y) (fun r => (f r).contMDiff) ft hft hfj hderiv x (vec2 v w)
  have hconv : ∀ (g : SmoothRiemannianMetric I M) (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u),
      hessianSec (LeviCivita g) (leviCivita_contMDiffCovariantDerivativeLocally g) u hu x
        (vec2 v w) = hessFun g u x v w := fun g u hu =>
    hessianSec_metricCov_eq_hessFun g hu x v w
  simp only [hconv] at h
  rw [Tensor0SSpace.sub_apply, hconv] at h
  convert h using 1
  have hcomp := bilinearCovectorComp_apply (leviCivitaVariation S.family.metric t x)
    (duSec (f t) (f t).contMDiff x) (vec2 v w)
  change _ = _ - Tensor0SSpace.eval (bilinearCovectorComp (leviCivitaVariation S.family.metric t x)
    (duSec (f t) (f t).contMDiff x)) (vec2 v w)
  rw [hcomp]
  have hev : Tensor0SSpace.eval (duSec (f t) (f t).contMDiff x)
      (fun _ : Fin 1 => leviCivitaVariation S.family.metric t x (vec2 v w 1) (vec2 v w 0)) =
      mvfderiv (I := I) (f t) x (leviCivitaVariation S.family.metric t x w v) := by
    have e : (fun _ : Fin 1 =>
        leviCivitaVariation S.family.metric t x (vec2 v w 1) (vec2 v w 0)) =
        ![leviCivitaVariation S.family.metric t x w v] := by
      funext i; fin_cases i; rfl
    rw [e]
    exact duSec_apply_vec (f t) (f t).contMDiff x _
  rw [hev]
  have hgrad : ∀ u : TangentSpace I x, mvfderiv (I := I) (f t) x u =
      (S.family.metric t).inner x u (gradFun (S.family.metric t) (f t) x) := by
    intro u
    rw [(S.family.metric t).symm, inner_gradFun]
    rfl
  simp only [hgrad]
  rw [surfaceFlow_leviCivitaVariation_pair hdim S hS ht x v w]
  ring

end GC.Geometry
