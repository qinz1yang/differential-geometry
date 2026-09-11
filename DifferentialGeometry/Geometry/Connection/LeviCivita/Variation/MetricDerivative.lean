import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.DifferenceKoszulDerivative
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.TimeDerivative
import DifferentialGeometry.Analysis.Calculus.FiniteDimension
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.Interior

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

omit [T2Space M] in
private theorem metric_inner_hasDerivAt_mvfderiv
    (g : ℝ → SmoothRiemannianMetric I M)
    (h : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2) (t : ℝ)
    (hderiv : ∀ x v w, HasDerivAt (fun s => (g s).inner x v w) (h x (vec2 v w)) t)
    (hsmooth : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ x,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)) (t, x))
    (Y Z : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : TangentSpace I x) :
    HasDerivAt
      (fun s => mvfderiv (I := I) (fun y => (g s).inner y (Y y) (Z y)) x v)
      (mvfderiv (I := I) (fun y => h y (vec2 (Y y) (Z y))) x v) t := by
  have hYZ (y : M) : (fun a : Fin 2 => (![Y, Z] a) y) = vec2 (Y y) (Z y) := by
    funext a
    fin_cases a <;> rfl
  apply hasDerivAt_mvfderiv_of_contMDiffAt
    (F := fun s y => (g s).inner y (Y y) (Z y))
    (Ft := fun y => h y (vec2 (Y y) (Z y)))
    BoundarylessManifold.isInteriorPoint (hsmooth Y Z x) ?_ ?_ ?_ v
  · intro s
    simpa [hYZ, metricTensorField_apply, vec2] using
      (tensor0SField_eval_smooth_slots_contMDiffAt
        (metricTensorField (I := I) (g s)) ![Y, Z] x).mdifferentiableAt (by simp)
  · simpa only [hYZ] using
      (tensor0SField_eval_smooth_slots_contMDiffAt h ![Y, Z] x).mdifferentiableAt (by simp)
  · exact fun y => hderiv y (Y y) (Z y)

omit [T2Space M] in
private theorem metric_nabla_hasDerivAt
    (g : ℝ → SmoothRiemannianMetric I M)
    (h : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2) (t : ℝ)
    (hderiv : ∀ x v w, HasDerivAt (fun s => (g s).inner x v w) (h x (vec2 v w)) t)
    (hsmooth : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ x,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)) (t, x))
    (X Y Z : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) :
    HasDerivAt
      (fun s => nabla0SFun 2 (LeviCivita (g t)) X (metricTensorField (I := I) (g s)) x
        (vec2 (Y x) (Z x)))
      (nabla0SFun 2 (LeviCivita (g t)) X h x (vec2 (Y x) (Z x))) t := by
  have hYZ (y : M) : (fun a : Fin 2 => (![Y, Z] a) y) = vec2 (Y y) (Z y) := by
    funext a
    fin_cases a <;> rfl
  have hv (v : Fin 2 → TangentSpace I x) : vec2 (v 0) (v 1) = v := by
    funext a
    fin_cases a <;> rfl
  have hswap := metric_inner_hasDerivAt_mvfderiv g h t hderiv hsmooth Y Z x (X x)
  have hd := nabla0SFun_hasDerivWithinAt_pt (I := I) (LeviCivita (g t)) X ![Y, Z]
    (fun s => metricTensorField (I := I) (g s)) (fun _ => h) Set.univ x t
    (by simpa [hYZ, metricTensorField_apply, vec2] using hswap) ?_
  · simpa only [hYZ, hasDerivWithinAt_univ] using hd
  · intro a
    simpa only [metricTensorField_apply, hv] using
      (hderiv x
        ((Function.update (fun b : Fin 2 => (![Y, Z] b) x) a
          ((LeviCivita (g t)) (fun y => (![Y, Z] a) y) x (X x))) 0)
        ((Function.update (fun b : Fin 2 => (![Y, Z] b) x) a
          ((LeviCivita (g t)) (fun y => (![Y, Z] a) y) x (X x))) 1)).hasDerivWithinAt

private theorem metric_difference_pair_hasDerivAt
    (g : ℝ → SmoothRiemannianMetric I M)
    (h : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2) (t : ℝ)
    (hderiv : ∀ x v w, HasDerivAt (fun s => (g s).inner x v w) (h x (vec2 v w)) t)
    (hsmooth : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ x,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)) (t, x))
    (X Y Z : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) :
    HasDerivAt
      (fun s => (g s).inner x
        ((LeviCivita (g s)) Y x (X x) - (LeviCivita (g t)) Y x (X x)) (Z x))
      ((1 / 2) * nabla0SFun 2 (LeviCivita (g t)) X h x (vec2 (Y x) (Z x)) +
        (1 / 2) * nabla0SFun 2 (LeviCivita (g t)) Y h x (vec2 (X x) (Z x)) -
        (1 / 2) * nabla0SFun 2 (LeviCivita (g t)) Z h x (vec2 (X x) (Y x))) t := by
  have heq (s : ℝ) := connectionDifference_koszul_nabla (g s) (g t) X Y Z (x := x)
  have hdiff (s : ℝ) :
      CovariantDerivative.difference (LeviCivita (g s)) (LeviCivita (g t)) x (Y x) (X x) =
        (LeviCivita (g s)) Y x (X x) - (LeviCivita (g t)) Y x (X x) := by
    change (IsCovariantDerivativeOn.difference _ _ x) (Y x) (X x) = _
    rw [IsCovariantDerivativeOn.difference_apply _ _ (Set.mem_univ x) Y.mdifferentiableAt]
    rfl
  simp_rw [hdiff] at heq
  simp_rw [heq]
  exact
    (((metric_nabla_hasDerivAt g h t hderiv hsmooth X Y Z x).const_mul (1 / 2)).add
      ((metric_nabla_hasDerivAt g h t hderiv hsmooth Y X Z x).const_mul (1 / 2))).sub
      ((metric_nabla_hasDerivAt g h t hderiv hsmooth Z X Y x).const_mul (1 / 2))

private theorem leviCivita_differentiableAt_of_metric_deriv
    (g : ℝ → SmoothRiemannianMetric I M)
    (h : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2) (t : ℝ)
    (hderiv : ∀ x v w, HasDerivAt (fun s => (g s).inner x v w) (h x (vec2 v w)) t)
    (hsmooth : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ x,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)) (t, x))
    (X Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) :
    DifferentiableAt ℝ (fun s => (LeviCivita (g s)) Y x (X x)) t := by
  let A (s : ℝ) := (LeviCivita (g s)) Y x (X x) - (LeviCivita (g t)) Y x (X x)
  let L (s : ℝ) := (g s).inner x (A s)
  have hL : DifferentiableAt ℝ L t := by
    apply differentiableAt_clm_apply.mpr
    intro z
    obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := TangentSpace I) x z
    simpa only [L, A, hZ] using
      (metric_difference_pair_hasDerivAt g h t hderiv hsmooth X Y Z x).differentiableAt
  have hg : DifferentiableAt ℝ (fun s => (g s).inner x) t := by
    apply differentiableAt_clm_apply.mpr
    intro v
    apply differentiableAt_clm_apply.mpr
    exact fun w => (hderiv x v w).differentiableAt
  have hinv (s : ℝ) : ((g s).inner x).IsInvertible := by
    let e := ((Geometry.Operator.metricFlatMap (I := I) (g s) x).trans
      LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
    exact ⟨e, by ext v w; rfl⟩
  let _ : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  have hmap : DifferentiableAt ℝ
      (ContinuousLinearMap.inverse :
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) →
          (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x) ((g t).inner x) :=
    ((hinv t).contDiffAt_map_inverse (n := 1)).differentiableAt (by simp)
  have hgi := DifferentiableAt.comp t hmap hg
  change DifferentiableAt ℝ (fun s => ((g s).inner x).inverse) t at hgi
  have hA : DifferentiableAt ℝ A t := by
    simpa only [L, ContinuousLinearMap.IsInvertible.inverse_apply_self (hinv _)] using
      hgi.clm_apply hL
  have hres := hA.add (differentiableAt_const ((LeviCivita (g t)) Y x (X x)))
  change DifferentiableAt ℝ (fun s => A s + (LeviCivita (g t)) Y x (X x)) t at hres
  simpa only [A, sub_add_cancel] using hres

def leviCivitaVariation (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  deriv (fun s => CovariantDerivative.difference (LeviCivita (g s)) (LeviCivita (g t)) x) t

theorem leviCivita_difference_hasDerivAt
    (g : ℝ → SmoothRiemannianMetric I M)
    (h : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2) (t : ℝ)
    (hderiv : ∀ x v w, HasDerivAt (fun s => (g s).inner x v w) (h x (vec2 v w)) t)
    (hsmooth : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ x,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)) (t, x))
    (x : M) :
    HasDerivAt
      (fun s => CovariantDerivative.difference (LeviCivita (g s)) (LeviCivita (g t)) x)
      (leviCivitaVariation g t x) t := by
  apply DifferentiableAt.hasDerivAt
  apply differentiableAt_clm_apply.mpr
  intro y
  apply differentiableAt_clm_apply.mpr
  intro v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := TangentSpace I) x y
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := TangentSpace I) x v
  have heq (s : ℝ) :
      CovariantDerivative.difference (LeviCivita (g s)) (LeviCivita (g t)) x y v =
        (LeviCivita (g s)) Y x (X x) - (LeviCivita (g t)) Y x (X x) := by
    rw [← hY, ← hX]
    change (IsCovariantDerivativeOn.difference _ _ x) (Y x) (X x) = _
    rw [IsCovariantDerivativeOn.difference_apply _ _ (Set.mem_univ x) Y.mdifferentiableAt]
    rfl
  simp_rw [heq]
  exact (leviCivita_differentiableAt_of_metric_deriv g h t hderiv hsmooth X Y x).sub_const _

theorem leviCivita_variation_koszul
    (g : ℝ → SmoothRiemannianMetric I M)
    (h : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2) (t : ℝ)
    (hderiv : ∀ x v w, HasDerivAt (fun s => (g s).inner x v w) (h x (vec2 v w)) t)
    (hsmooth : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ x,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)) (t, x))
    (x : M) (v w z : TangentSpace I x) :
    2 * (g t).inner x (leviCivitaVariation g t x w v) z =
      totalNabla0SFun 2 (LeviCivita (g t)) h x (Fin.cons v (vec2 w z)) +
      totalNabla0SFun 2 (LeviCivita (g t)) h x (Fin.cons w (vec2 v z)) -
      totalNabla0SFun 2 (LeviCivita (g t)) h x (Fin.cons z (vec2 v w)) := by
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := TangentSpace I) x v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := TangentSpace I) x w
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := TangentSpace I) x z
  have heq (s : ℝ) :
      CovariantDerivative.difference (LeviCivita (g s)) (LeviCivita (g t)) x w v =
        (LeviCivita (g s)) Y x (X x) - (LeviCivita (g t)) Y x (X x) := by
    rw [← hY, ← hX]
    change (IsCovariantDerivativeOn.difference _ _ x) (Y x) (X x) = _
    rw [IsCovariantDerivativeOn.difference_apply _ _ (Set.mem_univ x) Y.mdifferentiableAt]
    rfl
  have hd := ((leviCivita_difference_hasDerivAt g h t hderiv hsmooth x).clm_apply
    (hasDerivAt_const t w)).clm_apply (hasDerivAt_const t v)
  simp only [ContinuousLinearMap.map_zero, add_zero, heq] at hd
  have hg : DifferentiableAt ℝ (fun s => (g s).inner x) t := by
    apply differentiableAt_clm_apply.mpr
    intro a
    apply differentiableAt_clm_apply.mpr
    exact fun b => (hderiv x a b).differentiableAt
  have hp := (hg.hasDerivAt.clm_apply hd).clm_apply (hasDerivAt_const t z)
  simp only [sub_self, ContinuousLinearMap.map_zero, zero_add,
    zero_apply, add_zero] at hp
  have hc := metric_difference_pair_hasDerivAt g h t hderiv hsmooth X Y Z x
  rw [hZ] at hc
  have hv := hp.unique hc
  rw [← hX, ← hY, ← hZ, totalNabla0SFun_apply_section,
    totalNabla0SFun_apply_section, totalNabla0SFun_apply_section]
  rw [← hX, ← hY, ← hZ] at hv
  linarith

theorem leviCivita_hasDerivAt_of_metric_deriv
    (g : ℝ → SmoothRiemannianMetric I M)
    (h : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2) (t : ℝ)
    (hderiv : ∀ x v w, HasDerivAt (fun s => (g s).inner x v w) (h x (vec2 v w)) t)
    (hsmooth : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ x,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)) (t, x))
    {Y : (x : M) → TangentSpace I x} {x : M}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x)
    (v : TangentSpace I x) :
    HasDerivAt (fun s => (LeviCivita (g s)) Y x v)
      (leviCivitaVariation g t x (Y x) v) t := by
  have heq (s : ℝ) :
      CovariantDerivative.difference (LeviCivita (g s)) (LeviCivita (g t)) x (Y x) v =
        (LeviCivita (g s)) Y x v - (LeviCivita (g t)) Y x v := by
    change (IsCovariantDerivativeOn.difference _ _ x) (Y x) v = _
    rw [IsCovariantDerivativeOn.difference_apply _ _ (Set.mem_univ x) hY]
    rfl
  have hd := ((leviCivita_difference_hasDerivAt g h t hderiv hsmooth x).clm_apply
    (hasDerivAt_const t (Y x))).clm_apply (hasDerivAt_const t v)
  simp only [ContinuousLinearMap.map_zero, add_zero, heq] at hd
  have ha := hd.add_const ((LeviCivita (g t)) Y x v)
  change HasDerivAt
    (fun s => ((LeviCivita (g s)) Y x v - (LeviCivita (g t)) Y x v) +
      (LeviCivita (g t)) Y x v) _ t at ha
  simpa only [sub_add_cancel] using ha

theorem leviCivita_difference_hasDerivAt_of_metricFamilySmoothOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn (I := I) D g) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    (h : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2)
    (hderiv : ∀ x v w, HasDerivAt (fun s => (g s).inner x v w) (h x (vec2 v w)) t)
    (x : M) :
    HasDerivAt
      (fun s => CovariantDerivative.difference (LeviCivita (g s)) (LeviCivita (g t)) x)
      (leviCivitaVariation g t x) t := by
  apply leviCivita_difference_hasDerivAt g h t hderiv
  intro Y Z y
  simpa using (hg.pairSmoothAt (x := y) ht ![Y, Z]).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ from by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)

theorem leviCivita_variation_koszul_of_metricFamilySmoothOn
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn (I := I) D g) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    (h : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2)
    (hderiv : ∀ x v w, HasDerivAt (fun s => (g s).inner x v w) (h x (vec2 v w)) t)
    (x : M) (v w z : TangentSpace I x) :
    2 * (g t).inner x (leviCivitaVariation g t x w v) z =
      totalNabla0SFun 2 (LeviCivita (g t)) h x (Fin.cons v (vec2 w z)) +
      totalNabla0SFun 2 (LeviCivita (g t)) h x (Fin.cons w (vec2 v z)) -
      totalNabla0SFun 2 (LeviCivita (g t)) h x (Fin.cons z (vec2 v w)) := by
  apply leviCivita_variation_koszul g h t hderiv
  intro Y Z y
  simpa using (hg.pairSmoothAt (x := y) ht ![Y, Z]).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ from by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)

end DifferentialGeometry.Geometry.Connection
