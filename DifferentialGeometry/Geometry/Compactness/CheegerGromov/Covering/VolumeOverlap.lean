import DifferentialGeometry.Geometry.Comparison.Volume.SegmentCount


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.VolumeComparison
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.GoodCovering.Basic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold
open scoped Manifold ContDiff Topology Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers

open DifferentialGeometry.Integral.Measure

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]

section Dim1

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)] in
theorem riemannOp_dim1_zero (h1 : Module.finrank ℝ E = 1)
    (g : SmoothRiemannianMetric I M) (x : M) (u v w : TangentSpace I x) :
    riemannOp (LeviCivita (I := I) g) x u v w = 0 := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hfr : Module.finrank ℝ (TangentSpace I x) = 1 := h1
  have : Nontrivial (TangentSpace I x) :=
    Module.nontrivial_of_finrank_pos (by rw [hfr]; exact one_pos)
  obtain ⟨e, he⟩ := exists_ne (0 : TangentSpace I x)
  have hspan := (finrank_eq_one_iff_of_nonzero' e he).mp hfr
  obtain ⟨a, ha⟩ := hspan u
  obtain ⟨b, hb⟩ := hspan v
  have hee : riemannOp (LeviCivita (I := I) g) x e e w = 0 := by
    have hsw := riemannOp_swap (LeviCivita (I := I) g) x e e w
    have h2 : (2 : ℝ) • riemannOp (LeviCivita (I := I) g) x e e w = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hsw]
      exact add_neg_cancel _
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  rw [← ha, ← hb, map_smul, smul_apply, map_smul,
    smul_apply, smul_apply, hee,
    smul_zero, smul_zero]

omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)] in
theorem ricci_dim1_bddBelow (h1 : Module.finrank ℝ E = 1)
    (g : SmoothRiemannianMetric I M) :
    RicciBoundedBelow (I := I) g 0 := by
  intro x v
  rw [zero_mul]
  have hzero : ricciTensor (I := I) g x v v = 0 := by
    rw [ricciTensor_apply_basisSum]
    refine Finset.sum_eq_zero ?_
    intro i _
    rw [riemannOp_dim1_zero h1 g x ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis x) i) v v,
      map_zero, Finsupp.zero_apply]
  rw [hzero]

end Dim1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def volInputOfBg
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (bg : SeqBoundedGeometry (I := I) X)
    (hd : InjectivityRadiusDecay (I := I) X) (hreal : hd.RealizesDistance)
    (hcpl : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (r0 : Real) (hr0 : 0 < r0) :
    { vc : BallMultiplicityBound (I := I) X // vc.dist = hd.dist } := by
  set q : ℝ := (Module.finrank ℝ E : ℝ) * Real.sqrt (bg.C 0) with hq_def
  have hq : 0 ≤ q := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hC0 : 0 ≤ bg.C 0 := bg.nonneg 0
  refine ⟨{ dist := hd.dist, r0 := r0, r0_pos := hr0,
            multiplicity := fun m => segImult (Module.finrank ℝ E) q r0 m,
            card_le := ?_ }, rfl⟩
  intro m k α _ _ centers r hr hcap hsep z J hJz
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M :=
    IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle (fun x : (X.obj k).M => TangentSpace I x) :=
    (X.obj k).riemBundle
  have : IsContinuousRiemannianBundle E (fun x : (X.obj k).M => TangentSpace I x) :=
    (X.obj k).riemBundle_cont
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  have : IsRiemannianManifold I (X.obj k).M := ⟨fun _ _ => rfl⟩
  let : ConnectedSpace (X.obj k).M := hconn k
  have : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (X.obj k) (hcpl.complete k)
  have hRic : RicciBoundedBelow (I := I) (X.obj k).metric
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)) := by
    by_cases hn1 : Module.finrank ℝ E = 1
    · have h0 : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2 = 0 := by
        rw [hn1]; simp
      rw [h0, neg_zero]
      exact ricci_dim1_bddBelow hn1 (X.obj k).metric
    · have hn2 : 2 ≤ Module.finrank ℝ E := by
        have h1 : 1 ≤ Module.finrank ℝ E :=
          Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
        omega
      have hsrc : RicciBoundedBelow (I := I) (X.obj k).metric
          (-((Module.finrank ℝ E : ℝ) ^ 2 * bg.C 0)) :=
        ricciLower_of_rm (I := I) (X.obj k).metric
          (by simpa [Geometry.Riemannian.VolumeComparison.Rm04GlobalBound]
            using rm04Bound_of_seq (I := I) bg k)
      have hq2 : q ^ 2 = (Module.finrank ℝ E : ℝ) ^ 2 * bg.C 0 := by
        rw [hq_def, mul_pow, Real.sq_sqrt hC0]
      intro x v
      have hinner : 0 ≤ (X.obj k).metric.inner x v v := by
        rcases eq_or_ne v 0 with hv | hv
        · subst hv; simp
        · exact ((X.obj k).metric.pos x v hv).le
      have hkappa : -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) ≤
          -((Module.finrank ℝ E : ℝ) ^ 2 * bg.C 0) := by
        rw [neg_le_neg_iff, hq2]
        have hone : (1 : ℝ) ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
          have : 1 ≤ Module.finrank ℝ E - 1 := by omega
          exact_mod_cast this
        nlinarith [mul_nonneg (sq_nonneg (Module.finrank ℝ E : ℝ)) hC0]
      calc (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2))
              * (X.obj k).metric.inner x v v
          ≤ (-((Module.finrank ℝ E : ℝ) ^ 2 * bg.C 0))
              * (X.obj k).metric.inner x v v :=
            mul_le_mul_of_nonneg_right hkappa hinner
        _ ≤ ricciTensor (I := I) (X.obj k).metric x v v := hsrc x v
  have hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
    intro y w
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (X.obj k).metric y w
  have hbridge : ∀ x y : (X.obj k).M,
      riemannianEDist I x y = ENNReal.ofReal (hd.dist k x y) := by
    intro x y
    rw [← IsRiemannianManifold.out (I := I) x y]
    exact hreal.edist_eq k x y
  have hsep' : ∀ i j : α, i ≠ j →
      ENNReal.ofReal r ≤ riemannianEDist I (centers i) (centers j) := by
    intro i j hij
    rw [hbridge (centers i) (centers j)]
    exact ENNReal.ofReal_le_ofReal (hsep i j hij)
  have hJz' : ∀ j : α, j ∈ J →
      riemannianEDist I (centers j) z ≤ ENNReal.ofReal (m * r) := by
    intro j hj
    rw [hbridge (centers j) z]
    exact ENNReal.ofReal_le_ofReal (hJz j hj)
  exact segBall_card (I := I) (X.obj k).metric hEnorm hq hRic hr hcap
    centers hsep' z J hJz'

def packInputOfBg
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (bg : SeqBoundedGeometry (I := I) X)
    (hd : InjectivityRadiusDecay (I := I) X) (hreal : hd.RealizesDistance)
    (hcpl : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (D : Real) (hD : 0 < D) :
    hd.PackingBound D where
  A := fun r =>
    if hr : 0 ≤ r then
      let vc :=
        (volInputOfBg (I := I) X bg hd hreal hcpl hconn
          (r + 1) (by linarith)).1
      vc.multiplicity (r / hd.lambda D r)
    else
      0
  card_le := by
    classical
    intro k r J hJr hsep
    by_cases hr : 0 ≤ r
    · let s : Real := hd.lambda D r
      have hs : 0 < s := hd.lambda_pos hD r
      have hs_ne : s ≠ 0 := ne_of_gt hs
      have hr0 : 0 < r + 1 := by linarith
      let out :=
        volInputOfBg (I := I) X bg hd hreal hcpl hconn (r + 1) hr0
      let vc : BallMultiplicityBound (I := I) X := out.1
      have hvc : vc.dist = hd.dist := out.2
      have hmul_eq : (r / s) * s = r := div_mul_cancel₀ r hs_ne
      have hcap : (r / s) * s ≤ r + 1 := by
        rw [hmul_eq]
        linarith
      have hcap' : (r / s) * s ≤ vc.r0 := by
        change (r / s) * s ≤ r + 1
        exact hcap
      have hmul := vc.card_le (r / s) k
        (centers := fun i : {x // x ∈ J} => (i : (X.obj k).M))
        (r := s) hs hcap'
        (fun i j hij => by
          rw [hvc]
          exact hsep i i.2 j j.2 (fun h => hij (Subtype.ext h)))
        (X.obj k).basepoint Finset.univ
        (fun j _ => by
          rw [hvc]
          exact (hJr j j.2).trans_eq hmul_eq.symm)
      simpa only [Finset.card_univ, Fintype.card_coe, hr, ↓reduceDIte,
        out, vc, s] using hmul
    · have hJ : J = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hnonneg := hreal.dist_nonneg k x (X.obj k).basepoint
        exact (not_lt_of_ge hnonneg) (lt_of_le_of_lt (hJr x hx) (lt_of_not_ge hr))
      subst J
      simp only [Finset.card_empty, hr, ↓reduceDIte, le_refl]

end HCGCompactness
end DifferentialGeometry
