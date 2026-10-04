import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5EvolutionTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyDerivative

/-!
# The evolution of the traceless Hessian of the potential along a surface Ricci flow

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (potential gauge, design D18 (ii-T),
§5 of D18 and review 18 §1.2).

Let `f` be the potential, `Δ_{g(t)} f = R - r` with `r = 1 / (T* - t)`, `∂ₜ f = R + r f + a(t)`,
and `M = ∇²f - ½ (Δf) g` (`tracelessHessAt`). Then
`surfaceFlow_tracelessHess_tensor_evolution` (D18 (ii-T), frozen): `(∂ₜ - Δ) M = (r - 2 R) M`,
with `∂ₜ` the plain time derivative of the components and `Δ` the rough Laplacian
`roughLap0STensor g (iterCov g 2 M 2)`.

* time side: `∂ₜ ∇²f = ∇²R + r ∇²f + 𝔅` (`surfaceFlow_hessFun_hasDerivAt`), `∂ₜ R = ΔR + R²`,
  `∂ₜ r = r²`, `∂ₜ g = -R g`;
* space side: `M = ∇²f - P` with `P = (Δf / 2) g`; `ΔP = (ΔR / 2) g`
  (`covStep_two_of_eq_smul_metric`, `covStep_three_of_eq_dsmul_metric`) and
  `Δ∇²f = ∇²Δf + 2 R ∇²f - R (Δf) g + 𝔅` (`roughLap_iterCov_hessian`).
* `hessFun_add_mul_add_const`, `hessFun_mul_add_const`: linearity of `hessFun` on smooth functions.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Bundle Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {T : ℝ} {hT : 0 < T}

theorem hessFun_add_mul_add_const (g : SmoothRiemannianMetric I M) {u w : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (hw : ContMDiff I 𝓘(ℝ, ℝ) ∞ w) (β c : ℝ) (x : M)
    (a b : TangentSpace I x) :
    hessFun g (fun y => u y + β * w y + c) x a b =
      hessFun g u x a b + β * hessFun g w x a b := by
  have hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => u y + β * w y + c) :=
    (hu.add (contMDiff_const.mul hw)).add contMDiff_const
  rw [← covStep_duSec_apply_vec g _ hF, ← covStep_duSec_apply_vec g u hu,
    ← covStep_duSec_apply_vec g w hw]
  have hfield : duSec (fun y => u y + β * w y + c) hF = duSec u hu + β • duSec w hw := by
    refine ContMDiffSection.ext fun y => ?_
    refine tensor0SSpace_ext (I := I) 1 y fun s => ?_
    have hs : s = ![s 0] := by funext i; fin_cases i; rfl
    change duSec _ hF y s = (duSec u hu y + β • duSec w hw y) s
    rw [hs, Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, duSec_apply_vec, duSec_apply_vec,
      duSec_apply_vec]
    have hmu : MDifferentiableAt I 𝓘(ℝ, ℝ) u y := (hu y).mdifferentiableAt (by simp)
    have hmw : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => β * w y) y :=
      mdifferentiableAt_const.mul ((hw y).mdifferentiableAt (by simp))
    have hmuw : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => u y + β * w y) y := hmu.add hmw
    rw [mvfderiv_fun_add hmuw mdifferentiableAt_const, mvfderiv_fun_add hmu hmw,
      mvfderiv_const_mul I β ((hw y).mdifferentiableAt (by simp)), mvfderiv_const]
    simp
  rw [hfield, covStep_add, covStep_smul]
  rfl

theorem hessFun_mul_add_const (g : SmoothRiemannianMetric I M) {w : M → ℝ}
    (hw : ContMDiff I 𝓘(ℝ, ℝ) ∞ w) (β c : ℝ) (x : M) (a b : TangentSpace I x) :
    hessFun g (fun y => β * w y + c) x a b = β * hessFun g w x a b := by
  have h := hessFun_add_mul_add_const g (contMDiff_const (c := (0 : ℝ))) hw β c x a b
  have h0 : hessFun g (fun _ : M => (0 : ℝ)) x a b = 0 := by
    have h1 := hessFun_smul g 0 w
    rw [zero_smul, zero_smul] at h1
    have h2 : (fun _ : M => (0 : ℝ)) = (0 : M → ℝ) := rfl
    rw [h2, h1]
    rfl
  simp only [zero_add] at h
  rw [h, h0, zero_add]

theorem surfaceFlow_tracelessHess_tensor_evolution [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [ConnectedSpace M] (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    (hfeq : ∀ t ∈ Ioo 0 T, ∀ x,
      ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t))
    {a : ℝ → ℝ} (hft : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => f s x)
      (S.scalar t x + f t x / (flowExtinctionTime S - t) + a t) t)
    (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x) :
    ∀ t ∈ Ioo 0 T, ∀ x (v : Fin 2 → TangentSpace I x),
      HasDerivAt (fun s => Mf s x v)
        (roughLap0STensor (S.family.metric t) (iterCov (S.family.metric t) 2 (Mf t) 2 x) v +
          (1 / (flowExtinctionTime S - t) - 2 * S.scalar t x) * Mf t x v) t := by
  intro t ht x v
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  set g := S.family.metric t with hgdef
  set Tst := flowExtinctionTime S with hTst
  have hTT : T ≤ Tst := surfaceFlow_le_extinctionTime hT S hS hdim hscal
  have hgap : 0 < Tst - t := by linarith [ht.2]
  set a0 := v 0
  set a1 := v 1
  have hv : v = ![a0, a1] := by funext i; fin_cases i <;> rfl
  have hv2 : v = vec2 a0 a1 := by funext i; fin_cases i <;> rfl
  have hreg : t ∈ (RealTimeInterval.closedOpen 0 T hT).regular := ht
  have hMform : ∀ s ∈ Ioo 0 T, Mf s x v =
      hessFun (S.family.metric s) (f s) x a0 a1 -
        (S.scalar s x - 1 / (Tst - s)) / 2 * (S.family.metric s).inner x a0 a1 := by
    intro s hs
    rw [hM s hs, hv2, tracelessHessAt_vec2, hfeq s hs]
  have hRsm := scalarSmoothOfSolution S t
  have hftsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => S.scalar t y + f t y / (Tst - t) + a t) :=
    (hRsm.add ((f t).contMDiff.div_const _)).add contMDiff_const
  have hH := surfaceFlow_hessFun_hasDerivAt hdim S hS f hf ht _ hftsm (hft t ht) x a0 a1
  have hRd := surfaceScalar_hasDerivAt S hS hdim hreg x
  have hrd : HasDerivAt (fun s => 1 / (Tst - s)) ((1 / (Tst - t)) ^ 2) t := by
    have hd : HasDerivAt (fun s : ℝ => Tst - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub Tst
    have h := hd.inv hgap.ne'
    simp only [one_div]
    convert h using 1
    field_simp
  have hgd := metricDerivAt S hS ⟨t, hreg⟩ x a0 a1
  have htot := hH.sub (((hRd.sub hrd).div_const 2).mul hgd)
  refine (htot.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hMform s hs
  set Hf := covStep g 1 (duSec (f t) (f t).contMDiff) with hHf
  set P := Hf - Mf t with hPdef
  have hMt : Mf t = Hf - P := by rw [hPdef, sub_sub_cancel]
  have hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => ΔG g (f t) y / 2) :=
    (Δ_g_contMDiff g (f t)).div_const 2
  have hP : ∀ y (b c : TangentSpace I y), P y ![b, c] = ΔG g (f t) y / 2 * g.inner y b c := by
    intro y b c
    rw [hPdef, ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply, hHf,
      covStep_duSec_apply_vec, hM t ht y]
    have e : (![b, c] : Fin 2 → TangentSpace I y) = vec2 b c := by
      funext i; fin_cases i <;> rfl
    rw [e, tracelessHessAt_vec2]
    ring
  have hP1 : ∀ y (a' b c : TangentSpace I y), covStep g 2 P y ![a', b, c] =
      mvfderiv (I := I) (fun y => ΔG g (f t) y / 2) y a' * g.inner y b c :=
    fun y => covStep_two_of_eq_smul_metric g P hφ hP y
  have hP2 : ∀ e : TangentSpace I x, iterCov g 2 P 2 x ![e, e, a0, a1] =
      hessFun g (fun y => ΔG g (f t) y / 2) x e e * g.inner x a0 a1 := by
    intro e
    have h := covStep_three_of_eq_dsmul_metric g (covStep g 2 P) hφ hP1 x e e a0 a1
    rw [covStep_duSec_apply_vec] at h
    exact h
  have hΔf : ΔG g (f t) = fun y => 1 * S.scalar t y + -(1 / (Tst - t)) := by
    funext y
    rw [hfeq t ht y]
    ring
  have hφfun : (fun y => ΔG g (f t) y / 2) =
      fun y => (1 / 2 : ℝ) * S.scalar t y + -(1 / (Tst - t)) / 2 := by
    funext y
    rw [hfeq t ht y]
    ring
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  have hin : ∀ i, metricTraceInput (b i) (b i) v = ![b i, b i, a0, a1] := by
    intro i; rw [hv]; funext k; fin_cases k <;> rfl
  have hin' : ∀ i, metricTraceInput (b i) (b i) ![a0, a1] = ![b i, b i, a0, a1] := by
    intro i; funext k; fin_cases k <;> rfl
  have hlapM : roughLap0STensor g (iterCov g 2 (Mf t) 2 x) v =
      roughLap0STensor g (iterCov g 2 Hf 2 x) ![a0, a1] -
        ∑ i, iterCov g 2 P 2 x ![b i, b i, a0, a1] := by
    rw [roughLap0STensor_apply, roughLap0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_orthonormal g b hb,
      metricTraceFirstTwo0SAt_eq_sum_orthonormal g b hb, hMt, iterCov_sub]
    simp only [hin, hin', ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
      Finset.sum_sub_distrib]
  have hsumR : ∑ i, hessFun g (S.scalar t) x (b i) (b i) =
      ΔG g ⟨S.scalar t, scalarSmoothOfSolution S t⟩ x :=
    (laplacian_eq_sum_hessFun g (S.scalar t) hRsm x b hb).symm.trans
      (laplacian_levi_eq g hRsm x)
  have hsumP : ∑ i, iterCov g 2 P 2 x ![b i, b i, a0, a1] =
      ΔG g ⟨S.scalar t, scalarSmoothOfSolution S t⟩ x / 2 * g.inner x a0 a1 := by
    simp only [hP2, hφfun, hessFun_mul_add_const g hRsm, ← Finset.sum_mul, ← Finset.mul_sum,
      hsumR]
    ring
  rw [hlapM, hsumP, roughLap_iterCov_hessian hdim g (f t) x a0 a1, hΔf,
    hessFun_mul_add_const g hRsm, hMform t ht]
  have hftfun : (fun y => S.scalar t y + f t y / (Tst - t) + a t) =
      fun y => S.scalar t y + 1 / (Tst - t) * f t y + a t := by
    funext y; ring
  rw [hftfun, hessFun_add_mul_add_const g hRsm (f t).contMDiff]
  have hric : S.ricciAt t x (vec2 a0 a1) = S.scalar t x / 2 * g.inner x a0 a1 := by
    simp only [SolutionOn.ricciAt, SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor,
      SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.family_metric, hgdef]
    exact ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two _ hdim _ _ _
  rw [hric]
  have hRf : (fun y => metricScalarAt (S.family.metric t) y) = S.scalar t := rfl
  have hRx : metricScalarAt (S.family.metric t) x = S.scalar t x := rfl
  simp only [Pi.sub_apply, hgdef, hRf, hRx]
  ring

end GC.Geometry
