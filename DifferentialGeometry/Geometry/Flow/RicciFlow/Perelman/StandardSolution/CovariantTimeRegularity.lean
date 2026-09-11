import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MetricCompatibleTimeDerivative
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tensor0S_contDiffOn_of_components {ι : Type*} [Finite ι] {s : ℕ} {x : M}
    (basis : Module.Basis ι ℝ (TangentSpace I x)) (T : ℝ → Tensor0SSpace s I x) (J : Set ℝ)
    (hT : ∀ m : Fin s → ι, ContDiffOn ℝ ∞ (fun t => component0S basis (T t) m) J) :
    ContDiffOn ℝ ∞ T J := by
  classical
  let _ := Fintype.ofFinite ι
  let b := tensor0SBasis (I := I) basis s
  have hh := ContDiffOn.sum (fun (m : Fin s → ι) (_ : m ∈ Finset.univ) => (hT m).smul (contDiffOn_const (c := b m)))
  have he : (fun t => ∑ m : Fin s → ι, component0S basis (T t) m • b m) = T := by
    funext t
    simpa only [b, ← tensor0SBasis_repr] using (tensor0SBasis (I := I) basis s).sum_repr (T t)
  exact he ▸ hh

variable [T2Space M] [BoundarylessManifold I M]

theorem ricciTimeCorrection_component_in_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} {x : M} (g : SmoothRiemannianMetric I M) (T : Tensor0SSpace s I x)
    (basis : Module.Basis ι ℝ (TangentSpace I x)) (B : ι → ι → ℝ)
    (hB : MetricInverseInBasis g x basis B) (m : Fin s → ι) :
    component0S basis (ricciTimeCorrection g T) m =
      ∑ q : Fin s, ∑ i : ι, (∑ j : ι, B i j * ricciTensor g x (basis (m q)) (basis j)) *
        component0S basis T (Function.update m q i) := by
  classical
  have hexp (k : ι) : ricciSharp g x (basis k) =
      ∑ i : ι, (∑ j : ι, B i j * ricciTensor g x (basis k) (basis j)) • basis i := by
    conv_lhs => rw [← basis.sum_repr (ricciSharp g x (basis k))]
    apply Finset.sum_congr rfl
    intro i _
    rw [basis_repr_eq_sum_inv_inner g x basis B hB]
    simp only [inner_ricciSharp]
  rw [component0S_apply, ricciTimeCorrection_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [hexp (m q)]
  have hs := T.toModel.toMultilinearMap.map_update_sum Finset.univ q
    (fun i => (∑ j : ι, B i j * ricciTensor g x (basis (m q)) (basis j)) • basis i)
    (fun a => basis (m a))
  change T (Function.update (fun a => basis (m a)) q
    (∑ i : ι, (∑ j : ι, B i j * ricciTensor g x (basis (m q)) (basis j)) • basis i)) =
      ∑ i : ι, T (Function.update (fun a => basis (m a)) q
        ((∑ j : ι, B i j * ricciTensor g x (basis (m q)) (basis j)) • basis i)) at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [T.map_update_smul, smul_eq_mul]
  congr 1
  apply congrArg T
  funext a
  by_cases ha : a = q
  · subst a
    simp only [Function.update_self]
  · simp only [Function.update_of_ne ha]

theorem ricciTimeCorrection_contDiffOn {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ → Tensor0SSpace s I x)
    (basis : Module.Basis ι ℝ (TangentSpace I x)) (B : ℝ → ι → ι → ℝ) (J : Set ℝ)
    (hB : ∀ t ∈ J, MetricInverseInBasis (g t) x basis (B t))
    (hBs : ∀ i j, ContDiffOn ℝ ∞ (fun t => B t i j) J)
    (hR : ∀ i j, ContDiffOn ℝ ∞ (fun t => ricciTensor (g t) x (basis i) (basis j)) J)
    (hT : ContDiffOn ℝ ∞ T J) :
    ContDiffOn ℝ ∞ (fun t => ricciTimeCorrection (g t) (T t)) J := by
  classical
  apply tensor0S_contDiffOn_of_components basis
  intro m
  have hc (n : Fin s → ι) : ContDiffOn ℝ ∞ (fun t => component0S basis (T t) n) J :=
    (tensor0SEvalCLM (I := I) (fun a => basis (n a))).contDiff.comp_contDiffOn hT
  have hh := ContDiffOn.sum (fun (q : Fin s) (_ : q ∈ Finset.univ) =>
    ContDiffOn.sum (fun (i : ι) (_ : i ∈ Finset.univ) =>
      (ContDiffOn.sum (fun (j : ι) (_ : j ∈ Finset.univ) => (hBs i j).mul (hR (m q) j))).mul
        (hc (Function.update m q i))))
  apply hh.congr
  intro t ht
  exact ricciTimeCorrection_component_in_basis (g t) (T t) basis (B t) (hB t ht) m

theorem covariantTimeDerivWithin_contDiffOn {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ → Tensor0SSpace s I x)
    (basis : Module.Basis ι ℝ (TangentSpace I x)) (B : ℝ → ι → ι → ℝ) (J : Set ℝ)
    (hJ : UniqueDiffOn ℝ J)
    (hB : ∀ t ∈ J, MetricInverseInBasis (g t) x basis (B t))
    (hBs : ∀ i j, ContDiffOn ℝ ∞ (fun t => B t i j) J)
    (hR : ∀ i j, ContDiffOn ℝ ∞ (fun t => ricciTensor (g t) x (basis i) (basis j)) J)
    (hT : ContDiffOn ℝ ∞ T J) :
    ContDiffOn ℝ ∞ (covariantTimeDerivWithin g T J) J :=
  (hT.derivWithin hJ (by simp)).add (ricciTimeCorrection_contDiffOn g T basis B J hB hBs hR hT)

def iteratedCovariantTimeDerivWithin {s : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ → Tensor0SSpace s I x) (J : Set ℝ) :
    ℕ → ℝ → Tensor0SSpace s I x
  | 0 => T
  | b + 1 => covariantTimeDerivWithin g (iteratedCovariantTimeDerivWithin g T J b) J

theorem iteratedCovariantTimeDerivWithin_contDiffOn {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ → Tensor0SSpace s I x)
    (basis : Module.Basis ι ℝ (TangentSpace I x)) (B : ℝ → ι → ι → ℝ) (J : Set ℝ)
    (hJ : UniqueDiffOn ℝ J)
    (hB : ∀ t ∈ J, MetricInverseInBasis (g t) x basis (B t))
    (hBs : ∀ i j, ContDiffOn ℝ ∞ (fun t => B t i j) J)
    (hR : ∀ i j, ContDiffOn ℝ ∞ (fun t => ricciTensor (g t) x (basis i) (basis j)) J)
    (hT : ContDiffOn ℝ ∞ T J) (b : ℕ) :
    ContDiffOn ℝ ∞ (iteratedCovariantTimeDerivWithin g T J b) J := by
  induction b with
  | zero => exact hT
  | succ b ih => exact covariantTimeDerivWithin_contDiffOn g _ basis B J hJ hB hBs hR ih

omit [T2Space M] [BoundarylessManifold I M] in
theorem normSq0S_contDiffOn_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ → Tensor0SSpace s I x)
    (basis : Module.Basis ι ℝ (TangentSpace I x)) (B : ℝ → ι → ι → ℝ) (J : Set ℝ)
    (hB : ∀ t ∈ J, MetricInverseInBasis (g t) x basis (B t))
    (hBs : ∀ i j, ContDiffOn ℝ ∞ (fun t => B t i j) J)
    (hT : ContDiffOn ℝ ∞ T J) :
    ContDiffOn ℝ ∞ (fun t => normSq0S (g t) x s (T t)) J := by
  classical
  have hc (m : Fin s → ι) : ContDiffOn ℝ ∞ (fun t => tensor0SComponent (T t) (fun i => basis i) m) J :=
    (tensor0SEvalCLM (I := I) (fun a => basis (m a))).contDiff.comp_contDiffOn hT
  have hh := ContDiffOn.sum (fun (n : Fin s → ι) (_ : n ∈ Finset.univ) =>
    ContDiffOn.sum (fun (m : Fin s → ι) (_ : m ∈ Finset.univ) =>
      ((contDiffOn_prod (fun (a : Fin s) (_ : a ∈ Finset.univ) => hBs (n a) (m a))).mul (hc n)).mul (hc m)))
  apply hh.congr
  intro t ht
  rw [normSq0S_eq_coord (g t) x s basis (B t) (hB t ht)]
  rfl
end DifferentialGeometry.PDE.RicciFlow
