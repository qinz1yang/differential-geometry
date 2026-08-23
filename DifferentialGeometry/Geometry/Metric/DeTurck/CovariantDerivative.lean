import DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem orthoFrame_expand (g : SmoothRiemannianMetric I M) (x : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    u = ∑ i : Fin (Module.finrank ℝ E), g.inner x u (B i) • B i := by
  classical
  set c : Fin (Module.finrank ℝ E) → ℝ := fun i => g.inner x u (B i) with hc
  set S : TangentSpace I x := ∑ i, c i • B i with hS
  have hsecond : ∀ w : TangentSpace I x,
      g.inner x w S = ∑ i, c i * g.inner x w (B i) := by
    intro w
    rw [hS, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have hfirst : ∀ w : TangentSpace I x,
      g.inner x S w = ∑ i, c i * g.inner x (B i) w := by
    intro w
    rw [hS, map_sum, ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have huu : g.inner x u u = ∑ i, c i * c i := by
    rw [g_inner_eq_orthonormal_parseval_sum (I := I) g x u u B hB]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]; rw [g.symm x (B i) u]
  have huS : g.inner x u S = ∑ i, c i * c i := by
    rw [hsecond u]
  have hSu : g.inner x S u = ∑ i, c i * c i := by
    rw [hfirst u]
    exact Finset.sum_congr rfl fun i _ => by rw [g.symm x (B i) u]
  have hBS : ∀ i, g.inner x (B i) S = c i := by
    intro i
    rw [hsecond (B i)]
    rw [Finset.sum_congr rfl (fun j _ => by rw [hB i j]; split_ifs <;> simp :
      ∀ j ∈ Finset.univ, c j * g.inner x (B i) (B j) =
        if i = j then c j else 0)]
    simp
  have hSS : g.inner x S S = ∑ i, c i * c i := by
    rw [hfirst S]
    exact Finset.sum_congr rfl fun i _ => by rw [hBS i]
  have hlin : ∀ w : TangentSpace I x,
      g.inner x (u - S) w = g.inner x u w - g.inner x S w := by
    intro w
    rw [map_sub (g.inner x) u S, ContinuousLinearMap.sub_apply]
  have hzero : g.inner x (u - S) (u - S) = 0 := by
    rw [map_sub (g.inner x (u - S)) u S, hlin u, hlin S, huu, huS, hSu, hSS]
    ring
  by_contra hne
  have hsub : u - S ≠ 0 := sub_ne_zero.mpr hne
  have := g.pos x (u - S) hsub
  rw [hzero] at this
  exact lt_irrefl 0 this

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem frameDiag_indep (g : SmoothRiemannianMetric I M) (x : M)
    (B B' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (hB' : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B' i) (B' j) = if i = j then (1 : ℝ) else 0)
    (A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E), A (B i) (B i) =
      ∑ j : Fin (Module.finrank ℝ E), A (B' j) (B' j) := by
  classical
  have key : ∀ u₁ u₂ : TangentSpace I x, A u₁ u₂ =
      ∑ k : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (g.inner x u₁ (B' j) * g.inner x u₂ (B' k)) • A (B' j) (B' k) := by
    intro u₁ u₂
    conv_lhs => rw [orthoFrame_expand (I := I) g x B' hB' u₁,
      orthoFrame_expand (I := I) g x B' hB' u₂]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_sum, ContinuousLinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_smul, mul_comm]
  have hcoef : ∀ j k : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E),
        g.inner x (B i) (B' j) * g.inner x (B i) (B' k)) =
      (if j = k then (1 : ℝ) else 0) := by
    intro j k
    rw [← hB' j k, g_inner_eq_orthonormal_parseval_sum (I := I) g x (B' j) (B' k) B hB]
    exact Finset.sum_congr rfl fun i _ => by
      rw [g.symm x (B' j) (B i), g.symm x (B i) (B' k)]
  rw [Finset.sum_congr rfl (fun i _ => key (B i) (B i)), Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  have hinner : ∀ j : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E),
        (g.inner x (B i) (B' j) * g.inner x (B i) (B' k)) • A (B' j) (B' k)) =
      (if j = k then (1 : ℝ) else 0) • A (B' j) (B' k) := by
    intro j
    rw [← Finset.sum_smul, hcoef j k]
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  simp

omit [InnerProductSpace ℝ E] [SigmaCompactSpace M] in
theorem deTurckVF_frame_trace (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    (deTurckVF (I := I) g g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ i : Fin (Module.finrank ℝ E), connectionDifference (I := I) g g_bg x (B i) (B i) := by
  rw [deTurckVF_eq_orthoFrame_trace (I := I) g g_bg x]
  exact frameDiag_indep (I := I) g x
    (fun i => smoothOrthoFrame (I := I) g x i x) B
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j) hB
    (connectionDifference (I := I) g g_bg x)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem skewDiag_zero (g : SmoothRiemannianMetric I M) (x : M)
    (B D : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (hskew : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (D i) (B j) = - g.inner x (D j) (B i))
    (A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (hA : ∀ u w : TangentSpace I x, A u w = A w u) :
    ∑ i : Fin (Module.finrank ℝ E), A (D i) (B i) = 0 := by
  classical
  have hexp : ∑ i : Fin (Module.finrank ℝ E), A (D i) (B i)
      = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          g.inner x (D i) (B j) • A (B j) (B i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [orthoFrame_expand (I := I) g x B hB (D i)]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smul, ContinuousLinearMap.smul_apply]
  have hflip : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        g.inner x (D i) (B j) • A (B j) (B i))
      = - ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          g.inner x (D i) (B j) • A (B j) (B i) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          g.inner x (D b) (B a) • A (B a) (B b))
        = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            (- g.inner x (D a) (B b)) • A (B b) (B a) from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [hskew b a, hA (B a) (B b)]]
    simp only [neg_smul, Finset.sum_neg_distrib]
  rw [hexp]
  have h2 : (2 : ℝ) • (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      g.inner x (D i) (B j) • A (B j) (B i)) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hflip]
    exact add_neg_cancel _
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h (by norm_num)
  · exact h

omit [InnerProductSpace ℝ E] [SigmaCompactSpace M] in
theorem frameCorr_vanish (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        connectionDifference (I := I) g g_bg x
          ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
          (smoothOrthoFrame (I := I) g x i x) = 0 :=
  skewDiag_zero (I := I) g x
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)
    (fun i j => by
      rw [smoothOrthoFrame_cov_skew (I := I) g x i j v]
      exact congrArg Neg.neg (g.symm x _ _))
    (connectionDifference (I := I) g g_bg x)
    (fun u w => connectionDifference_symm (I := I) g g_bg x u w)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem cov_sum (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {ι : Type*} (σ : ι → Π b : M, TangentSpace I b)
    (hσ : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (σ i))) (s : Finset ι) (x : M) :
    cov.toFun (fun b : M => ∑ i ∈ s, σ i b) x = ∑ i ∈ s, cov.toFun (σ i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact congrFun (CovariantDerivative.zero cov) x
  · intro a t ha ih
    have hsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => ∑ i ∈ t, σ i b)) :=
      ContMDiff.sum_section (fun i _ => hσ i)
    have hstep : (fun b : M => ∑ i ∈ insert a t, σ i b)
        = σ a + (fun b : M => ∑ i ∈ t, σ i b) := by
      funext b
      rw [Finset.sum_insert ha]
      rfl
    rw [hstep, cov.isCovariantDerivativeOnUniv.add ((hσ a x).mdifferentiableAt (by simp))
      ((hsm x).mdifferentiableAt (by simp)) (Set.mem_univ x), ih, Finset.sum_insert ha]

omit [InnerProductSpace ℝ E] [SigmaCompactSpace M] in
theorem deTurckVF_covDeriv_eq (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    (LeviCivita (I := I) g).toFun
        (fun b : M => (deTurckVF (I := I) g g_bg : Π b : M, TangentSpace I b) b) x v =
      ∑ i : Fin (Module.finrank ℝ E),
        (covDerivConnectionDifference (I := I) g_bg g (smoothExtensionTangent (I := I) x v)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) x
          + (connectionDifference (I := I) g g_bg x
                (connectionDifference (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
                  (smoothOrthoFrame (I := I) g x i x)) v
              - connectionDifference (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
                  (connectionDifference (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x) v)
              - connectionDifference (I := I) g g_bg x
                  (connectionDifference (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x) v)
                  (smoothOrthoFrame (I := I) g x i x))) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hXx : smoothExtensionTangent (I := I) x v x = v :=
    smoothExtensionTangent_eq (I := I) x v
  have hBsm : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) := fun i =>
    smoothOrthoFrame_smooth (I := I) g x i
  have hσsm : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i))) := fun i =>
    diffSec_contMDiff (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g) (hBsm i)
      (by simpa using hBsm i)
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => (deTurckVF (I := I) g g_bg : Π b : M, TangentSpace I b) b)) :=
    (deTurckVF (I := I) g g_bg).contMDiff
  have hSsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
        diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) b)) :=
    ContMDiff.sum_section (fun i _ => hσsm i)
  have hev : ∀ᶠ b in nhds x,
      (deTurckVF (I := I) g g_bg : Π b : M, TangentSpace I b) b =
        ∑ i : Fin (Module.finrank ℝ E),
          diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) b := by
    filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with b hb
    rw [deTurckVF_frame_trace (I := I) g g_bg b
      (fun i => smoothOrthoFrame (I := I) g x i b)
      (fun i j => smoothOrthoFrame_orthonormal (I := I) g x hb i j)]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hcongr := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (σ := fun b : M => (deTurckVF (I := I) g g_bg : Π b : M, TangentSpace I b) b)
    (σ' := fun b : M => ∑ i : Fin (Module.finrank ℝ E),
      diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g)
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) b)
    ((hW x).mdifferentiableAt (by simp)) ((hSsm x).mdifferentiableAt (by simp))
    Filter.univ_mem hev
  rw [hcongr, cov_sum (I := I) (LeviCivita (I := I) g)
    (fun i : Fin (Module.finrank ℝ E) =>
      diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g)
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i))
    hσsm Finset.univ x, ContinuousLinearMap.sum_apply]
  have hper : ∀ i : Fin (Module.finrank ℝ E),
      (LeviCivita (I := I) g).toFun
          (diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)) x v =
        (covDerivConnectionDifference (I := I) g_bg g (smoothExtensionTangent (I := I) x v)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) x
          + (connectionDifference (I := I) g g_bg x
                (connectionDifference (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
                  (smoothOrthoFrame (I := I) g x i x)) v
              - connectionDifference (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
                  (connectionDifference (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x) v)
              - connectionDifference (I := I) g g_bg x
                  (connectionDifference (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x) v)
                  (smoothOrthoFrame (I := I) g x i x)))
        + (connectionDifference (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
              ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
            + connectionDifference (I := I) g g_bg x
                ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
                (smoothOrthoFrame (I := I) g x i x)) := by
    intro i
    have hkey := connectionDifference_outerCovDeriv_eq (I := I) g g_bg
      (X := smoothExtensionTangent (I := I) x v)
      (Y := smoothOrthoFrame (I := I) g x i) (Z := smoothOrthoFrame (I := I) g x i)
      (hBsm i) (hBsm i) x
    rw [hXx] at hkey
    have hcov : covApply (LeviCivita (I := I) g) (smoothExtensionTangent (I := I) x v)
        (smoothOrthoFrame (I := I) g x i) x =
        (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v := by
      rw [covApply_apply, hXx]
    rw [hcov] at hkey
    linear_combination (norm := abel) hkey
  have hcorr2 : ∑ i : Fin (Module.finrank ℝ E),
      connectionDifference (I := I) g g_bg x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
        (smoothOrthoFrame (I := I) g x i x) = 0 :=
    frameCorr_vanish (I := I) g g_bg x v
  have hcorr1 : ∑ i : Fin (Module.finrank ℝ E),
      connectionDifference (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v) = 0 := by
    rw [Finset.sum_congr rfl
      (fun i _ => connectionDifference_symm (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v))]
    exact hcorr2
  have hcorr : ∑ i : Fin (Module.finrank ℝ E),
      (connectionDifference (I := I) g g_bg x (smoothOrthoFrame (I := I) g x i x)
            ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
          + connectionDifference (I := I) g g_bg x
              ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)
              (smoothOrthoFrame (I := I) g x i x)) = 0 := by
    rw [Finset.sum_add_distrib, hcorr1, hcorr2, add_zero]
  rw [Finset.sum_congr rfl (fun i _ => hper i), Finset.sum_add_distrib,
    Finset.sum_add_distrib, hcorr, add_zero]

end DeTurck
end PDE
end DifferentialGeometry

end
