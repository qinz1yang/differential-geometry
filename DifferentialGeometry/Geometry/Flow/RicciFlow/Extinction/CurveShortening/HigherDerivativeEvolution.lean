import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.IteratedDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.DerivativeEvolution

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] {D : RealTimeInterval} {a b s u : ℝ}

namespace CurveMap

theorem iteratedDs_curvature_forcing_succ
    (B : RicciBackground (I := I) (M := M) D a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (m : ℕ) (x t : ℝ) (ht : t ∈ Icc s u) :
    let g := B.family.metric
    let V := fun j => c.iteratedDs g j (c.curvatureVector g)
    c.Dt g (Icc s u) (V (m + 1)) x t - V (m + 3) x t =
      c.Ds g (fun y τ => c.Dt g (Icc s u) (V m) y τ - V (m + 2) y τ) x t +
      c.q B.family x t • V (m + 1) x t +
      riemannVector B.family t (c.lift x t) (c.curvatureVector g x t) (c.unitTangent g x t) (V m x t) +
      connectionVariation B.family (Icc a b) t (c.lift x t) (c.unitTangent g x t) (V m x t) := by
  let g := B.family.metric
  let V := fun j => c.iteratedDs g j (c.curvatureVector g)
  let R : c.Field (I := I) := fun y τ => c.Dt g (Icc s u) (V m) y τ - V (m + 2) y τ
  change c.Dt g (Icc s u) (V (m + 1)) x t - V (m + 3) x t =
    c.Ds g R x t + c.q B.family x t • V (m + 1) x t + _ + _
  have hJ : Icc s u ⊆ D.regular := fun τ hτ => B.regular (hwindow hτ)
  have hH := Field.smoothOn_curvatureVector g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed
  have hV (j : ℕ) : (V j).SmoothOn (I := I) (Icc s u) :=
    Field.smoothOn_iteratedDs g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed
      (c.curvatureVector g) hH j
  have hDt := Field.smoothOn_Dt g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth (V m) (hV m)
  have hR : R.SmoothOn (I := I) (Icc s u) :=
    Field.smoothOn_sub hc.smooth (c.Dt g (Icc s u) (V m)) (V (m + 2)) hDt (hV (m + 2))
  have hsmooth (W : c.Field (I := I)) (hW : W.SmoothOn (I := I) (Icc s u)) :
      ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, W y t⟩ : TangentBundle I M)) :=
    fun y => contMDiffWithinAt_univ.mp (CurveShortening.Field.space_slice_contMDiffWithinAt c _ W hW y t ht)
  have hsum := c.Ds_add g R (V (m + 2)) x t
    (chartRep_diff (I := I) _ _ (hsmooth R hR) x)
    (chartRep_diff (I := I) _ _ (hsmooth (V (m + 2)) (hV (m + 2))) x)
  have heq : (fun y τ => R y τ + V (m + 2) y τ) = c.Dt g (Icc s u) (V m) := by
    funext y τ
    exact sub_add_cancel _ _
  rw [heq] at hsum
  have hsucc (j : ℕ) : V (j + 1) = c.Ds g (V j) := by
    simp only [V, iteratedDs, Function.iterate_succ_apply']
  have hcomm := c.Dt_Ds_commutator B hsu hwindow hc (V m) (hV m) x t ht
  have hvpos := c.speed_pos g hc.immersed x t ht
  have hX : c.X x t = c.speed g x t • c.unitTangent g x t := by
    rw [unitTangent, smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
  have hRm : riemannVector B.family t (c.lift x t) (c.velocity (Icc s u) x t) (c.X x t) (V m x t) =
      c.speed g x t • riemannVector B.family t (c.lift x t) (c.curvatureVector g x t)
        (c.unitTangent g x t) (V m x t) := by
    rw [hc.equation x t ht, hX, riemannVector_eq_riemannOp, riemannVector_eq_riemannOp, map_smul, smul_apply]
  have hP : connectionVariation B.family (Icc s u) t (c.lift x t) (c.X x t) (V m x t) =
      c.speed g x t • connectionVariation B.family (Icc a b) t (c.lift x t) (c.unitTangent g x t) (V m x t) := by
    rw [connectionVariation_congr_set B hsu hwindow t ht, hX,
      (connectionVariation_tensor B t (hwindow ht) (c.lift x t)).2.2]
  rw [hRm, hP, ← smul_add, smul_smul, inv_mul_cancel₀ hvpos.ne', one_smul] at hcomm
  rw [hsucc m, hsucc (m + 2), hcomm, hsum]
  module

theorem iteratedDs_curvature_forcing_pairing_succ
    (B : RicciBackground (I := I) (M := M) D a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (W : c.Field (I := I)) (hW : W.SmoothOn (I := I) (Icc s u))
    (m : ℕ) (x t : ℝ) (ht : t ∈ Icc s u) :
    let g := B.family.metric
    let V := fun j => c.iteratedDs g j (c.curvatureVector g)
    let R : ℕ → c.Field (I := I) := fun j y τ => c.Dt g (Icc s u) (V j) y τ - V (j + 2) y τ
    (g t).inner (c.lift x t) (R (m + 1) x t) (W x t) =
      c.ds g (fun y τ => (g τ).inner (c.lift y τ) (R m y τ) (W y τ)) x t -
      (g t).inner (c.lift x t) (R m x t) (c.Ds g W x t) +
      c.q B.family x t * (g t).inner (c.lift x t) (V (m + 1) x t) (W x t) +
      B.family.rm04At t (c.lift x t)
        (vec4 (c.curvatureVector g x t) (c.unitTangent g x t) (V m x t) (W x t)) -
      nablaRicci B.family t (c.lift x t) (c.unitTangent g x t) (V m x t) (W x t) -
      nablaRicci B.family t (c.lift x t) (V m x t) (c.unitTangent g x t) (W x t) +
      nablaRicci B.family t (c.lift x t) (W x t) (c.unitTangent g x t) (V m x t) := by
  let g := B.family.metric
  let V := fun j => c.iteratedDs g j (c.curvatureVector g)
  let R : ℕ → c.Field (I := I) := fun j y τ => c.Dt g (Icc s u) (V j) y τ - V (j + 2) y τ
  have hJ : Icc s u ⊆ D.regular := fun τ hτ => B.regular (hwindow hτ)
  have hH := Field.smoothOn_curvatureVector g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed
  have hV (j : ℕ) : (V j).SmoothOn (I := I) (Icc s u) :=
    Field.smoothOn_iteratedDs g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed
      (c.curvatureVector g) hH j
  have hDt := Field.smoothOn_Dt g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth (V m) (hV m)
  have hR : (R m).SmoothOn (I := I) (Icc s u) :=
    Field.smoothOn_sub hc.smooth (c.Dt g (Icc s u) (V m)) (V (m + 2)) hDt (hV (m + 2))
  have hsmooth (Z : c.Field (I := I)) (hZ : Z.SmoothOn (I := I) (Icc s u)) :
      ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, Z y t⟩ : TangentBundle I M)) :=
    fun y => contMDiffWithinAt_univ.mp (CurveShortening.Field.space_slice_contMDiffWithinAt c _ Z hZ y t ht)
  have hds := c.ds_inner g (Icc s u) hc.smooth (R m) W x t ht (hsmooth (R m) hR) (hsmooth W hW)
  have hforce := c.iteratedDs_curvature_forcing_succ B hsu hwindow hc m x t ht
  have hh := congrArg (fun Z => (g t).inner (c.lift x t) Z (W x t)) hforce
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul] at hh
  rw [inner_riemannVector_eq_rm04 B.family, rfs_csf_connection B t (hwindow ht)] at hh
  change (g t).inner (c.lift x t) (R (m + 1) x t) (W x t) = _
  rw [hh, hds]
  ring

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
