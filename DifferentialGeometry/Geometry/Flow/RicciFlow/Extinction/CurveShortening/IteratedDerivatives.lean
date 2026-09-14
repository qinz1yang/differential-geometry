import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] {D : RealTimeInterval} {a b s u : ℝ}

namespace CurveMap

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem Field.smoothOn_iteratedDs
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (hJun : UniqueDiffOn ℝ J)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (V : c.Field (I := I)) (hV : V.SmoothOn (I := I) J) (m : ℕ) :
    CurveMap.Field.SmoothOn (I := I) (c.iteratedDs g m V) J := by
  induction m with
  | zero => exact hV
  | succ m ih =>
    simp only [iteratedDs, Function.iterate_succ_apply']
    exact Field.smoothOn_Ds g hG hJ hJun c hc hi (c.iteratedDs g m V) ih

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem Ds_contMDiff (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (V : c.Field (I := I)) (t : ℝ) (ht : t ∈ J)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => (⟨c.lift x t, V x t⟩ : TangentBundle I M))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => (⟨c.lift x t, c.Ds g V x t⟩ : TangentBundle I M)) := by
  have hs := (c.speed_contDiff g J hc hi t ht).inv (fun x => (c.speed_pos g hi x t ht).ne')
  exact hs.contMDiff.smul_bundle (contMDiff_covDerivAlong (g t) hV (m := ⊤) (by simp))

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem iteratedDs_contMDiff (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (V : c.Field (I := I)) (t : ℝ) (ht : t ∈ J)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => (⟨c.lift x t, V x t⟩ : TangentBundle I M))) (m : ℕ) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => (⟨c.lift x t, c.iteratedDs g m V x t⟩ : TangentBundle I M)) := by
  induction m with
  | zero => exact hV
  | succ m ih =>
    simp only [iteratedDs, Function.iterate_succ_apply']
    exact c.Ds_contMDiff g hc hi (c.iteratedDs g m V) t ht ih

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem iterated_ds_inner
    (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ}
    (c : CurveMap M) (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (V W : c.Field (I := I)) (t : ℝ) (ht : t ∈ J)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun x => (⟨c.lift x t, V x t⟩ : TangentBundle I M)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun x => (⟨c.lift x t, W x t⟩ : TangentBundle I M)))
    (m : ℕ) (x : ℝ) :
    (c.ds g)^[m] (fun y τ => (g τ).inner (c.lift y τ) (V y τ) (W y τ)) x t =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (g t).inner (c.lift x t) (c.iteratedDs g i V x t) (c.iteratedDs g (m - i) W x t) := by
  let Vj := fun i => c.iteratedDs g i V
  let Wj := fun i => c.iteratedDs g i W
  let f := fun i j y τ => (g τ).inner (c.lift y τ) (Vj i y τ) (Wj j y τ)
  have hVs (i : ℕ) : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun y => (⟨c.lift y t, Vj i y t⟩ : TangentBundle I M)) :=
    c.iteratedDs_contMDiff g hc hi V t ht hV i
  have hWs (i : ℕ) : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun y => (⟨c.lift y t, Wj i y t⟩ : TangentBundle I M)) :=
    c.iteratedDs_contMDiff g hc hi W t ht hW i
  have hd (i j : ℕ) (y : ℝ) : DifferentiableAt ℝ (fun z => f i j z t) y :=
    c.differentiableAt_inner_slice g J hc (Vj i) (Wj j) y t ht (hVs i) (hWs j)
  have hds (i j : ℕ) (y : ℝ) : c.ds g (f i j) y t = f (i + 1) j y t + f i (j + 1) y t := by
    have hh := c.ds_inner g J hc (Vj i) (Wj j) y t ht (hVs i) (hWs j)
    simpa only [f, Vj, Wj, iteratedDs, Function.iterate_succ_apply'] using hh
  change (c.ds g)^[m] (f 0 0) x t =
    ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * f i (m - i) x t
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    change (c.speed g x t)⁻¹ * deriv (fun y => (c.ds g)^[m] (f 0 0) y t) x = _
    rw [funext ih, deriv_fun_sum (fun i _ => (hd i (m - i) x).const_mul (m.choose i : ℝ)), Finset.mul_sum]
    calc
      _ = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (c.ds g (f i (m - i)) x t) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [deriv_const_mul_field]
        dsimp only [ds]
        ring
      _ = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (f (i + 1) (m - i) x t + f i (m - i + 1) x t) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hds]
      _ = _ := by
        rw [Finset.sum_choose_succ_mul (fun i j => f i j x t) m, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hle : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        rw [show m + 1 - i = m - i + 1 by omega]
        ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [I.Boundaryless] [T2Space M] in
theorem iterated_ds_contDiff (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (a : ℝ → ℝ → ℝ) (t : ℝ) (ht : t ∈ J) (ha : ContDiff ℝ ∞ (fun x => a x t)) (m : ℕ) :
    ContDiff ℝ ∞ (fun x => (c.ds g)^[m] a x t) := by
  have hs := (c.speed_contDiff g J hc hi t ht).inv (fun x => (c.speed_pos g hi x t ht).ne')
  induction m with
  | zero => exact ha
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    change ContDiff ℝ ∞ (fun x => (c.speed g x t)⁻¹ * deriv (fun y => (c.ds g)^[m] a y t) x)
    exact hs.mul ih.deriv'

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem iteratedDs_smul
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (c : CurveMap M) (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (a : ℝ → ℝ → ℝ) (V : c.Field (I := I)) (t : ℝ) (ht : t ∈ J)
    (ha : ContDiff ℝ ∞ (fun x => a x t))
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun x => (⟨c.lift x t, V x t⟩ : TangentBundle I M)))
    (m : ℕ) (x : ℝ) :
    c.iteratedDs g m (fun y τ => a y τ • V y τ) x t =
      ∑ i ∈ Finset.range (m + 1), ((m.choose i : ℝ) * (c.ds g)^[i] a x t) •
        c.iteratedDs g (m - i) V x t := by
  let aj := fun i => (c.ds g)^[i] a
  let Vj := fun i => c.iteratedDs g i V
  have has (i : ℕ) : ContDiff ℝ ∞ (fun y => aj i y t) :=
    c.iterated_ds_contDiff g hc hi a t ht ha i
  have hVs (i : ℕ) : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun y => (⟨c.lift y t, Vj i y t⟩ : TangentBundle I M)) :=
    c.iteratedDs_contMDiff g hc hi V t ht hV i
  change c.iteratedDs g m (fun y τ => a y τ • V y τ) x t =
    ∑ i ∈ Finset.range (m + 1), ((m.choose i : ℝ) * aj i x t) • Vj (m - i) x t
  induction m generalizing x with
  | zero => simp [aj, Vj, iteratedDs]
  | succ m ih =>
    have hcoeff (i : ℕ) : DifferentiableAt ℝ (fun y => (m.choose i : ℝ) * aj i y t) x :=
      ((has i).differentiable (by simp) x).const_mul _
    have hrep (i : ℕ) : DifferentiableAt ℝ
        (chartRepAt (I := I) (fun y => c.lift y t) (fun y => Vj (m - i) y t) x) x :=
      chartRep_diff (I := I) _ _ (hVs (m - i)) x
    have hprod (i : ℕ) : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
        (fun y => (⟨c.lift y t, ((m.choose i : ℝ) * aj i y t) • Vj (m - i) y t⟩ : TangentBundle I M)) :=
      ((contDiff_const.mul (has i)).contMDiff).smul_bundle (hVs (m - i))
    have hsum := covDerivAlong_sum (g t) (fun y => c.lift y t) (Finset.range (m + 1))
      (fun i y => ((m.choose i : ℝ) * aj i y t) • Vj (m - i) y t) x
      (fun i _ => chartRep_diff (I := I) _ _ (hprod i) x)
    rw [show c.iteratedDs g (m + 1) (fun y τ => a y τ • V y τ) =
      c.Ds g (c.iteratedDs g m (fun y τ => a y τ • V y τ)) by
        simp only [iteratedDs, Function.iterate_succ_apply']]
    change (c.speed g x t)⁻¹ • covDerivAlong (g t) (fun y => c.lift y t)
      (fun y => c.iteratedDs g m (fun z τ => a z τ • V z τ) y t) x = _
    rw [funext ih, hsum, Finset.smul_sum]
    calc
      _ = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) •
          (aj (i + 1) x t • Vj (m - i) x t + aj i x t • Vj (m - i + 1) x t) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [covDerivAlong_smulFun (g t) (fun y => c.lift y t)
          (fun y => (m.choose i : ℝ) * aj i y t) (fun y => Vj (m - i) y t) x (hcoeff i) (hrep i),
          deriv_const_mul_field]
        have hasucc : aj (i + 1) = c.ds g (aj i) := Function.iterate_succ_apply' _ _ _
        have hVsucc : Vj (m - i + 1) = c.Ds g (Vj (m - i)) := Function.iterate_succ_apply' _ _ _
        rw [hasucc, hVsucc]
        dsimp only [ds, Ds, Dx]
        module
      _ = _ := by
        have hrec := Finset.sum_choose_succ_nsmul (fun i j => aj i x t • Vj j x t) m
        simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul] at hrec
        rw [hrec, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hle : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        rw [show m + 1 - i = m - i + 1 by omega]
        module

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
