import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5Evolution
import DifferentialGeometry.Geometry.Operator.WeightedLaplacianTensorNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CovariantTimeNorm

/-!
# The evolution of the squared norm of the traceless Hessian along a surface Ricci flow

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (potential gauge, design D18 (ii),
review 18 §1.2).

* `laplacian_normSq0S_eq`: `Δ|A|² = 2 ⟨ΔA, A⟩ + 2 |∇A|²` for a smooth `(0, s)`-tensor field
  (`weightedLaplacian_normSq0S` with zero weight).
* `ricciTimeCorrection_of_finrank_eq_two`: in dimension two `Ric♯ = (R / 2) id`, so the Ricci
  correction of a `(0, 2)`-tensor is `R A`.
* `surfaceFlow_tracelessHess_normSq_evolution` (D18 (ii), frozen): from (ii-T),
  `∂ₜ |M|² = 2 R |M|² + 2 ⟨∂ₜ M, M⟩` (`hasDerivWithinAt_normSq0S_covariantTime`) gives
  `(∂ₜ - Δ) |M|² = (2 / (T* - t) - 2 R) |M|² - 2 |∇M|²`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Tensor.RSTensor
open Bundle Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {T : ℝ} {hT : 0 < T}

theorem laplacian_normSq0S_eq (g : SmoothRiemannianMetric I M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    ΔG g (⟨fun y => normSq0S g y s (A y), normSq0S_smooth g A⟩ : C^∞⟮I, M; ℝ⟯) x =
      2 * inner0S g x s (roughLap0STensor g (iterCov g s A 2 x)) (A x) +
        2 * normSq0S g x (s + 1) (iterCov g s A 1 x) := by
  have h : weightedLaplacian g (0 : C^∞⟮I, M; ℝ⟯)
      (⟨fun y => normSq0S g y s (A y), normSq0S_smooth g A⟩ : C^∞⟮I, M; ℝ⟯) x =
      2 * inner0S g x s (weightedRoughLaplacian0S g 0 A x) (A x) +
        2 * normSq0S g x (s + 1) (iterCov g s A 1 x) :=
    weightedLaplacian_normSq0S g (0 : C^∞⟮I, M; ℝ⟯) A x
  have hgrad0 : gradFun g ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 := by
    apply SmoothRiemannianMetric.eq_of_inner_eq g
    intro u
    rw [inner_gradFun]
    have h0 : ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) = fun _ => 0 := rfl
    rw [h0, mfderiv_const]
    simp only [zero_apply, map_zero]
    rfl
  have h2 : ΔG g (⟨fun y => normSq0S g y s (A y), normSq0S_smooth g A⟩ : C^∞⟮I, M; ℝ⟯) x -
      g.inner x (gradFun g ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
        (gradFun g (fun y => normSq0S g y s (A y)) x) =
      2 * inner0S g x s (roughLap0STensor g (iterCov g s A 2 x) -
        tensor0SCurry s x (iterCov g s A 1 x) (gradFun g ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
          (A x) + 2 * normSq0S g x (s + 1) (iterCov g s A 1 x) := h
  rw [hgrad0, map_zero, zero_apply, sub_zero, map_zero, sub_zero] at h2
  exact h2

theorem ricciTimeCorrection_of_finrank_eq_two (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) {x : M}
    (A : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 x) :
    ricciTimeCorrection g A = metricScalarAt g x • A := by
  have hsharp : ∀ w : TangentSpace I x, ricciSharp g x w = (metricScalarAt g x / 2) • w := by
    intro w
    apply SmoothRiemannianMetric.eq_of_inner_eq g
    intro u
    rw [inner_ricciSharp, ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two g hdim,
      map_smul, smul_apply, smul_eq_mul]
  refine tensor0SSpace_ext 2 x fun v => ?_
  rw [ricciTimeCorrection_apply, Fin.sum_univ_two, Tensor0SSpace.smul_apply, hsharp, hsharp,
    A.map_update_smul, A.map_update_smul, Function.update_eq_self, Function.update_eq_self]
  simp only [smul_eq_mul]
  ring

theorem surfaceFlow_tracelessHess_normSq_evolution [NeZero (Module.finrank ℝ E)]
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
    ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => normSq0S (S.family.metric s) x 2 (Mf s x))
      (laplacianAt (flowG S) t (fun y => normSq0S (S.family.metric t) y 2 (Mf t y)) x +
        (2 / (flowExtinctionTime S - t) - 2 * S.scalar t x) *
          normSq0S (S.family.metric t) x 2 (Mf t x) -
        2 * normSq0S (S.family.metric t) x (2 + 1)
          (iterCov (S.family.metric t) 2 (Mf t) 1 x)) t := by
  intro t ht x
  set g := S.family.metric t with hgdef
  set c := 1 / (flowExtinctionTime S - t) - 2 * S.scalar t x with hc
  set Mdot : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 x :=
    roughLap0STensor g (iterCov g 2 (Mf t) 2 x) + c • Mf t x with hMdot
  have hreg : t ∈ (RealTimeInterval.closedOpen 0 T hT).regular := ht
  have hT' : ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r => Mf r x v) (Mdot v) univ t := by
    intro v
    have h := surfaceFlow_tracelessHess_tensor_evolution hdim S hS hscal f hf hfeq hft Mf hM t ht
      x v
    rw [hMdot, Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
    exact h.hasDerivWithinAt
  have hflow : ∀ v w : TangentSpace I x, HasDerivWithinAt
      (fun r => (S.family.metric r).inner x v w) (-2 * ricciTensor g x v w) univ t := by
    intro v w
    have h := metricDerivAt S hS ⟨t, hreg⟩ x v w
    simp only [SolutionOn.ricciAt, SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor,
      SolutionOn.family_metric] at h
    exact h.hasDerivWithinAt
  obtain ⟨b, hb⟩ := exists_orthonormal_basis g x
  have hd := hasDerivWithinAt_normSq0S_covariantTime S.family.metric (fun r => Mf r x) Mdot univ
    t uniqueDiffWithinAt_univ b hb hflow hT'
  have he : covariantTimeDerivWithin S.family.metric (fun r => Mf r x) univ t =
      Mdot + metricScalarAt g x • Mf t x := by
    have hh : derivWithin (fun r => Mf r x) univ t = Mdot :=
      (hasDerivWithinAt_tensor0S_of_eval (fun r => Mf r x) Mdot univ t hT').derivWithin
        uniqueDiffWithinAt_univ
    rw [covariantTimeDerivWithin, hh, ricciTimeCorrection_of_finrank_eq_two hdim]
  rw [he, hasDerivWithinAt_univ] at hd
  refine hd.congr_deriv ?_
  have hlap : laplacianAt (flowG S) t (fun y => normSq0S g y 2 (Mf t y)) x =
      ΔG g (⟨fun y => normSq0S g y 2 (Mf t y), normSq0S_smooth g (Mf t)⟩ : C^∞⟮I, M; ℝ⟯) x :=
    laplacian_levi_eq g (normSq0S_smooth g (Mf t)) x
  rw [hlap, laplacian_normSq0S_eq, hMdot, inner0S_add_left, inner0S_add_left, inner0S_smul_left,
    inner0S_smul_left]
  have hRx : metricScalarAt g x = S.scalar t x := rfl
  rw [hRx, hc]
  unfold normSq0S
  ring

end GC.Geometry
