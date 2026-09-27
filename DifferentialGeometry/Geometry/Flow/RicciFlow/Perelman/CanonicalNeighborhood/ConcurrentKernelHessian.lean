import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeRadialCurvature
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic
import DifferentialGeometry.Geometry.Connection.Coordinates.CovariantDerivativeRealization
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

set_option autoImplicit false
noncomputable section
open Bundle Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.TensorLieDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] in
private theorem eval_pair_sections
    (X Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    (fun a : Fin 2 => (![X, Y] a) x) = vec2 (X x) (Y x) := by
  funext a
  fin_cases a <;> rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] in
private theorem eval_triple_sections
    (X Y Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    (fun a : Fin 3 => (![X, Y, Z] a) x) = vec3 (X x) (Y x) (Z x) := by
  funext a
  fin_cases a <;> rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem cons_vec2 {x : M} (u v w : TangentSpace I x) :
    Fin.cons u (vec2 v w) = vec3 u v w := by
  funext a
  fin_cases a <;> rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem cons_vec3 {x : M} (u v w z : TangentSpace I x) :
    Fin.cons u (vec3 v w z) = vec4 u v w z := by
  funext a
  fin_cases a <;> rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem update_vec2_zero {x : M} (u v w : TangentSpace I x) :
    Function.update (vec2 u v) (0 : Fin 2) w = vec2 w v := by
  funext a
  fin_cases a <;> rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem update_vec2_one {x : M} (u v w : TangentSpace I x) :
    Function.update (vec2 u v) (1 : Fin 2) w = vec2 u w := by
  funext a
  fin_cases a <;> rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem update_vec3_zero {x : M} (u v w z : TangentSpace I x) :
    Function.update (vec3 u v w) (0 : Fin 3) z = vec3 z v w := by
  funext a
  fin_cases a <;> rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem update_vec3_one {x : M} (u v w z : TangentSpace I x) :
    Function.update (vec3 u v w) (1 : Fin 3) z = vec3 u z w := by
  funext a
  fin_cases a <;> rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem update_vec3_two {x : M} (u v w z : TangentSpace I x) :
    Function.update (vec3 u v w) (2 : Fin 3) z = vec3 u v z := by
  funext a
  fin_cases a <;> rfl

private theorem firstCovDeriv_concurrent_kernel_left
    (g : SmoothRiemannianMetric I M)
    (Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (DA : Tensor0SField (I := I) (M := M) (n := ∞) 3)
    (hDA : TotalNabla0SRealizes 2 (metricCov g) A DA) {x : M}
    (hZ : ∀ v : TangentSpace I x, metricCov g Z x v = v)
    (hker : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y,
      A y (vec2 (Z y) v) = 0 ∧ A y (vec2 v (Z y)) = 0)
    (u v : TangentSpace I x) :
    DA x (vec3 u (Z x) v) = -A x (vec2 u v) := by
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  have hzero : (fun y => A y (vec2 (Z y) (Y y))) =ᶠ[𝓝 x] (fun _ => 0) :=
    hker.mono fun y hy => (hy (Y y)).1
  have hdiff : mvfderiv (I := I) (fun y => A y (vec2 (Z y) (Y y))) x u = 0 := by
    rw [mvfderiv_eventuallyEq_congr u hzero, mvfderiv_const, zero_apply]
  have h := hDA.eval_smooth_slots X ![Z, Y] x
  have heval : DA x (vec3 u (Z x) v) =
      mvfderiv (I := I) (fun y => A y (vec2 (Z y) (Y y))) x u -
        (A x (vec2 (metricCov g Z x u) v) +
          A x (vec2 (Z x) (metricCov g Y x u))) := by
    simpa only [eval_pair_sections, cons_vec2, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, update_vec2_zero, update_vec2_one,
      hX, hY] using h
  rw [hdiff, hZ, (hker.self_of_nhds _).1] at heval
  simpa using heval

private theorem firstCovDeriv_concurrent_kernel_right
    (g : SmoothRiemannianMetric I M)
    (Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (DA : Tensor0SField (I := I) (M := M) (n := ∞) 3)
    (hDA : TotalNabla0SRealizes 2 (metricCov g) A DA) {x : M}
    (hZ : ∀ v : TangentSpace I x, metricCov g Z x v = v)
    (hker : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y,
      A y (vec2 (Z y) v) = 0 ∧ A y (vec2 v (Z y)) = 0)
    (u v : TangentSpace I x) :
    DA x (vec3 u v (Z x)) = -A x (vec2 v u) := by
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  have hzero : (fun y => A y (vec2 (Y y) (Z y))) =ᶠ[𝓝 x] (fun _ => 0) :=
    hker.mono fun y hy => (hy (Y y)).2
  have hdiff : mvfderiv (I := I) (fun y => A y (vec2 (Y y) (Z y))) x u = 0 := by
    rw [mvfderiv_eventuallyEq_congr u hzero, mvfderiv_const, zero_apply]
  have h := hDA.eval_smooth_slots X ![Y, Z] x
  have heval : DA x (vec3 u v (Z x)) =
      mvfderiv (I := I) (fun y => A y (vec2 (Y y) (Z y))) x u -
        (A x (vec2 (metricCov g Y x u) (Z x)) +
          A x (vec2 v (metricCov g Z x u))) := by
    simpa only [eval_pair_sections, cons_vec2, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, update_vec2_zero, update_vec2_one,
      hX, hY] using h
  rw [hdiff, hZ, (hker.self_of_nhds _).2] at heval
  simpa using heval

theorem secondCovDeriv_concurrent_kernel
    (g : SmoothRiemannianMetric I M)
    (Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (DA : Tensor0SField (I := I) (M := M) (n := ∞) 3)
    (DDA : Tensor0SField (I := I) (M := M) (n := ∞) 4)
    (hDA : TotalNabla0SRealizes 2 (metricCov g) A DA)
    (hDDA : TotalNabla0SRealizes 3 (metricCov g) DA DDA) {x : M}
    (hZ : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y, metricCov g Z y v = v)
    (hker : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y,
      A y (vec2 (Z y) v) = 0 ∧ A y (vec2 v (Z y)) = 0)
    (u v : TangentSpace I x) :
    DDA x (vec4 u v (Z x) (Z x)) = A x (vec2 u v) + A x (vec2 v u) := by
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  have hfirst_zero (w : TangentSpace I x) : DA x (vec3 w (Z x) (Z x)) = 0 := by
    rw [firstCovDeriv_concurrent_kernel_left g Z A DA hDA hZ.self_of_nhds hker,
      (hker.self_of_nhds _).2, neg_zero]
  have hzero : (fun y => DA y (vec3 (Y y) (Z y) (Z y))) =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hZ, eventually_eventually_nhds.mpr hker] with y hy hky
    rw [firstCovDeriv_concurrent_kernel_left g Z A DA hDA hy hky,
      (hky.self_of_nhds _).2, neg_zero]
  have hdiff : mvfderiv (I := I) (fun y => DA y (vec3 (Y y) (Z y) (Z y))) x u = 0 := by
    rw [mvfderiv_eventuallyEq_congr u hzero, mvfderiv_const, zero_apply]
  have h := hDDA.eval_smooth_slots X ![Y, Z, Z] x
  have heval : DDA x (vec4 u v (Z x) (Z x)) =
      mvfderiv (I := I) (fun y => DA y (vec3 (Y y) (Z y) (Z y))) x u -
        (DA x (vec3 (metricCov g Y x u) (Z x) (Z x)) +
          DA x (vec3 v (metricCov g Z x u) (Z x)) +
          DA x (vec3 v (Z x) (metricCov g Z x u))) := by
    simpa [eval_triple_sections, cons_vec3, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      update_vec3_zero, update_vec3_one, update_vec3_two, hX, hY, add_assoc] using h
  rw [hdiff, hZ.self_of_nhds, hfirst_zero,
    firstCovDeriv_concurrent_kernel_right g Z A DA hDA hZ.self_of_nhds hker,
    firstCovDeriv_concurrent_kernel_left g Z A DA hDA hZ.self_of_nhds hker] at heval
  linarith

theorem sum_secondCovDeriv_concurrent_kernel
    (g : SmoothRiemannianMetric I M)
    (Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (DA : Tensor0SField (I := I) (M := M) (n := ∞) 3)
    (DDA : Tensor0SField (I := I) (M := M) (n := ∞) 4)
    (hDA : TotalNabla0SRealizes 2 (metricCov g) A DA)
    (hDDA : TotalNabla0SRealizes 3 (metricCov g) DA DDA) {x : M}
    (hZ : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y, metricCov g Z y v = v)
    (hker : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y,
      A y (vec2 (Z y) v) = 0 ∧ A y (vec2 v (Z y)) = 0)
    {J : Type*} [Fintype J] (basis : J → TangentSpace I x) :
    (∑ j, DDA x (vec4 (basis j) (basis j) (Z x) (Z x))) =
      2 * ∑ j, A x (vec2 (basis j) (basis j)) := by
  classical
  simp_rw [secondCovDeriv_concurrent_kernel g Z A DA DDA hDA hDDA hZ hker,
    ← two_mul]
  exact (Finset.mul_sum ..).symm

theorem metricNabla2Ric_concurrent
    (g : SmoothRiemannianMetric I M)
    (Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) {x : M}
    (hZ : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y, metricCov g Z y v = v)
    (u v : TangentSpace I x) :
    metricNabla2Ric g x (vec4 u v (Z x) (Z x)) =
      2 * metricRicciAt g x (vec2 u v) := by
  have hfirst : TotalNabla0SRealizes 2 (metricCov g) (metricRicci g) (metricNablaRic g) :=
    totalNabla0S_realizes 2 (metricCov g) (metricRicci g) _
  have hsecond : TotalNabla0SRealizes 3 (metricCov g) (metricNablaRic g)
      (metricNabla2Ric g) :=
    totalNabla0S_realizes 3 (metricCov g) (metricNablaRic g) _
  have hker : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y,
      metricRicci g y (vec2 (Z y) v) = 0 ∧ metricRicci g y (vec2 v (Z y)) = 0 := by
    filter_upwards [eventually_eventually_nhds.mpr hZ] with y hy
    intro v
    simp only [metricRicci_apply]
    have hk := metricRicci_concurrent_eq_zero g Z hy v
    exact ⟨(metricRicciAt_symm g y (Z y) v).trans hk, hk⟩
  have h := secondCovDeriv_concurrent_kernel g Z (metricRicci g) (metricNablaRic g)
    (metricNabla2Ric g) hfirst hsecond hZ hker u v
  rw [metricRicci_apply, metricRicciAt_symm g x v u] at h
  simpa only [two_mul] using h

theorem trace_metricNabla2Ric_concurrent
    (g : SmoothRiemannianMetric I M)
    (Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) {x : M}
    (hZ : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y, metricCov g Z y v = v)
    {J : Type*} [Fintype J] [DecidableEq J]
    (basis : Module.Basis J ℝ (TangentSpace I x)) (gInv : J → J → ℝ)
    (hinv : MetricInverseInBasis g x basis gInv) :
    (∑ i, ∑ j, gInv i j * metricNabla2Ric g x
      (vec4 (basis i) (basis j) (Z x) (Z x))) = 2 * metricScalarAt g x := by
  classical
  rw [metricScalarAt_def,
    DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis g basis gInv hinv]
  simp_rw [metricNabla2Ric_concurrent g Z hZ]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
