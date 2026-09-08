import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrameIndex
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariationMinimiser
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Metric.Completeness

set_option autoImplicit false

noncomputable section

open Set Function Manifold Bundle MeasureTheory
open scoped Topology Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem ricci_eq_sum_sectional_curvature_of_orthonormal_perp_frame
    (g : SmoothRiemannianMetric I M) (x : M) (X : TangentSpace I x)
    (hUnit : g.inner x X X = 1)
    (e : Fin (Module.finrank Real E - 1) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0)
    (hPerp : ∀ i, g.inner x (e i) X = 0) :
    (∑ i : Fin (Module.finrank Real E - 1),
        g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) X X) (e i)) =
      ricciTensor (I := I) g x X X := by
  classical
  have hn_pos : 0 < Module.finrank Real E := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn_eq : Module.finrank Real E - 1 + 1 = Module.finrank Real E :=
    Nat.succ_pred_eq_of_pos hn_pos
  let B' : Fin (Module.finrank Real E - 1 + 1) → TangentSpace I x := Fin.cases X e
  let B : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => B' (Fin.cast hn_eq.symm i)
  have hB_zero : B (⟨0, hn_pos⟩ : Fin (Module.finrank Real E)) = X := by
    change B' (Fin.cast hn_eq.symm ⟨0, hn_pos⟩) = X
    have hcast_eq : Fin.cast hn_eq.symm (⟨0, hn_pos⟩ : Fin (Module.finrank Real E)) =
        (0 : Fin (Module.finrank Real E - 1 + 1)) := by
      apply Fin.ext
      rfl
    rw [hcast_eq]
    rfl
  have hsigma_lt : ∀ i : Fin (Module.finrank Real E - 1),
      i.val + 1 < Module.finrank Real E := by
    intro i
    have hi : i.val < Module.finrank Real E - 1 := i.isLt
    omega
  let sigma : Fin (Module.finrank Real E - 1) → Fin (Module.finrank Real E) :=
    fun i => ⟨i.val + 1, hsigma_lt i⟩
  have hB_succ : ∀ i : Fin (Module.finrank Real E - 1), B (sigma i) = e i := by
    intro i
    change B' (Fin.cast hn_eq.symm (sigma i)) = e i
    have hsucc_eq : Fin.cast hn_eq.symm (sigma i) = Fin.succ i := by
      apply Fin.ext
      rfl
    rw [hsucc_eq]
    rfl
  have hB_orth : ∀ i j : Fin (Module.finrank Real E),
      g.inner x (B i) (B j) = if i = j then (1 : Real) else 0 := by
    intro i j
    by_cases hi : i.val = 0
    · have hi_eq : i = ⟨0, hn_pos⟩ := Fin.ext hi
      by_cases hj : j.val = 0
      · have hj_eq : j = ⟨0, hn_pos⟩ := Fin.ext hj
        rw [hi_eq, hj_eq, hB_zero, hUnit]
        rw [if_pos rfl]
      · have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj
        let k : Fin (Module.finrank Real E - 1) :=
          ⟨j.val - 1, by have := j.isLt; omega⟩
        have hj_eq : j = sigma k := by
          apply Fin.ext
          change j.val = (j.val - 1) + 1
          omega
        rw [hi_eq, hj_eq, hB_zero, hB_succ]
        have h_inner : g.inner x X (e k) = 0 := by
          rw [g.symm x X (e k)]
          exact hPerp k
        rw [h_inner]
        rw [if_neg]
        intro h
        have hval := congrArg Fin.val h
        change 0 = k.val + 1 at hval
        omega
    · have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi
      let k : Fin (Module.finrank Real E - 1) :=
        ⟨i.val - 1, by have := i.isLt; omega⟩
      have hi_eq : i = sigma k := by
        apply Fin.ext
        change i.val = (i.val - 1) + 1
        omega
      by_cases hj : j.val = 0
      · have hj_eq : j = ⟨0, hn_pos⟩ := Fin.ext hj
        rw [hi_eq, hj_eq, hB_succ, hB_zero]
        have h_inner : g.inner x (e k) X = 0 := hPerp k
        rw [h_inner]
        rw [if_neg]
        intro h
        have hval := congrArg Fin.val h
        change k.val + 1 = 0 at hval
        omega
      · have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj
        let l : Fin (Module.finrank Real E - 1) :=
          ⟨j.val - 1, by have := j.isLt; omega⟩
        have hj_eq : j = sigma l := by
          apply Fin.ext
          change j.val = (j.val - 1) + 1
          omega
        rw [hi_eq, hj_eq, hB_succ, hB_succ]
        have h_inner : g.inner x (e k) (e l) = if k = l then (1 : Real) else 0 :=
          hON k l
        rw [h_inner]
        by_cases hkl : k = l
        · rw [hkl]
          simp
        · rw [if_neg hkl, if_neg]
          intro hsigma_eq
          apply hkl
          apply Fin.ext
          have hval := congrArg Fin.val hsigma_eq
          change k.val + 1 = l.val + 1 at hval
          omega
  rw [ricciTensor_eq_orthonormal_trace (I := I) g x X X B hB_orth]
  have hsum_split :
      ∑ i : Fin (Module.finrank Real E),
          g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) X X) (B i) =
        g.inner x (riemannOp (LeviCivita (I := I) g) x X X X) X +
          ∑ i : Fin (Module.finrank Real E - 1),
            g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) X X) (e i) := by
    have heq_sum :
        ∑ i : Fin (Module.finrank Real E),
          g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) X X) (B i) =
        ∑ j : Fin (Module.finrank Real E - 1 + 1),
          g.inner x (riemannOp (LeviCivita (I := I) g) x (B (finCongr hn_eq j)) X X)
            (B (finCongr hn_eq j)) :=
      (Equiv.sum_comp (finCongr hn_eq)
        (fun i => g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) X X) (B i))).symm
    rw [heq_sum]
    rw [Fin.sum_univ_succ]
    have h0 : (finCongr hn_eq (0 : Fin (Module.finrank Real E - 1 + 1)) :
              Fin (Module.finrank Real E)) = ⟨0, hn_pos⟩ := by
      apply Fin.ext
      rfl
    rw [h0, hB_zero]
    refine congrArg (fun s : Real =>
        g.inner x (riemannOp (LeviCivita (I := I) g) x X X X) X + s)
      (Finset.sum_congr rfl ?_)
    intro i _
    have heq : finCongr hn_eq i.succ = sigma i := by
      apply Fin.ext
      rfl
    rw [heq, hB_succ]
  rw [hsum_split]
  have hR_self : riemannOp (LeviCivita (I := I) g) x X X X = 0 := by
    have h := riemannOp_swap (LeviCivita (I := I) g) x X X X
    have hsum : riemannOp (LeviCivita (I := I) g) x X X X +
        riemannOp (LeviCivita (I := I) g) x X X X = 0 := by
      rw [eq_neg_iff_add_eq_zero] at h
      exact h
    have h_two : (2 : Real) • riemannOp (LeviCivita (I := I) g) x X X X = 0 := by
      rw [two_smul]
      exact hsum
    rcases smul_eq_zero.mp h_two with h2_zero | hv_zero
    · exact absurd h2_zero (by norm_num)
    · exact hv_zero
  rw [hR_self]
  rw [map_zero]
  change _ = 0 + _
  rw [zero_add]

omit [SigmaCompactSpace M] in
theorem sum_indexIntegrand_eq_weighted_ricci
    (g : SmoothRiemannianMetric I M) (gamma : Real → M)
    (F : Fin (Module.finrank Real E - 1) →
      ∀ t : Real, TangentSpace I (gamma t))
    (t w dw : Real)
    (hunit : g.inner (gamma t)
      (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
      (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) = 1)
    (hON : ∀ i j, g.inner (gamma t) (F i t) (F j t) =
      if i = j then 1 else 0)
    (hperp : ∀ i, g.inner (gamma t) (F i t)
      (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) = 0) :
    (∑ i : Fin (Module.finrank Real E - 1),
      DifferentialGeometry.Analysis.ODE.indexIntegrand
        (perpCurvOp (I := I) g gamma F)
        (fun _s => w • EuclideanSpace.single i (1 : Real))
        (fun _s => dw • EuclideanSpace.single i (1 : Real))
        (fun _s => w • EuclideanSpace.single i (1 : Real))
        (fun _s => dw • EuclideanSpace.single i (1 : Real)) t) =
      (Module.finrank Real E - 1 : Real) * dw ^ 2 -
        w ^ 2 * ricciTensor (I := I) g (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) := by
  classical
  have hcurv (i : Fin (Module.finrank Real E - 1)) :
      inner Real
        (perpCurvOp (I := I) g gamma F t
          (w • EuclideanSpace.single i (1 : Real)))
        (w • EuclideanSpace.single i (1 : Real)) =
      w ^ 2 * g.inner (gamma t)
        ((riemannOp (LeviCivita (I := I) g) (gamma t))
          (F i t)
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)))
        (F i t) := by
    rw [perpCurv_inner (I := I) g gamma F]
    simp
    ring
  have htrace :=
    ricci_eq_sum_sectional_curvature_of_orthonormal_perp_frame
      (I := I) g (gamma t)
      (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) hunit
      (fun i => F i t) hON hperp
  simp only [DifferentialGeometry.Analysis.ODE.indexIntegrand]
  rw [Finset.sum_sub_distrib]
  simp_rw [hcurv]
  rw [← Finset.mul_sum, htrace]
  have hkin (i : Fin (Module.finrank Real E - 1)) :
      inner Real (dw • EuclideanSpace.single i (1 : Real))
        (dw • EuclideanSpace.single i (1 : Real)) = dw ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    simp [norm_smul, sq_abs]
  simp_rw [hkin]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.cast_sub (Nat.pos_of_ne_zero (NeZero.ne _)), Nat.cast_one]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem weighted_ricci_integral_le_with_frame
    [T2Space (TangentBundle I M)]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [CompleteSpace E]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (gamma : Real → M) {L : Real} (hL : 0 < L)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hgeo : IsGeodesicOn (I := I) g gamma (Set.Icc 0 L))
    (hmin : ∀ eta : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 eta (Set.Icc 0 L) →
      eta 0 = gamma 0 → eta L = gamma L →
      arcLength (I := I) g gamma 0 L ≤ arcLength (I := I) g eta 0 L)
    (hunit : ∀ t ∈ Set.Icc (0 : Real) L,
      g.inner (gamma t)
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) = 1)
    (F : Fin (Module.finrank Real E - 1) →
      ∀ t : Real, TangentSpace I (gamma t))
    (hFdiff : ∀ i, ∀ t ∈ Set.Icc (0 : Real) L,
      DifferentiableAt Real (chartRepAt (I := I) gamma (F i) t) t)
    (hFpar : ∀ i, ∀ t ∈ Set.Icc (0 : Real) L,
      covDerivAlong (I := I) g gamma (F i) t = 0)
    (hFON : ∀ t ∈ Set.Icc (0 : Real) L, ∀ i j,
      g.inner (gamma t) (F i t) (F j t) = if i = j then 1 else 0)
    (hFperp : ∀ t ∈ Set.Icc (0 : Real) L, ∀ i,
      g.inner (gamma t) (F i t)
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) = 0)
    (hFsmooth : ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (gamma t) (F i t)))
    (phi : Real → Real) (hphi : ContDiff Real ∞ phi)
    (hphi0 : phi 0 = 0) (hphiL : phi L = 0) :
    (∫ t in (0 : Real)..L, phi t ^ 2 *
      ricciTensor (I := I) g (gamma t)
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))) ≤
      (Module.finrank Real E - 1 : Real) *
        ∫ t in (0 : Real)..L, deriv phi t ^ 2 := by
  classical
  let basis : Fin (Module.finrank Real E - 1) →
      EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    fun i => EuclideanSpace.single i 1
  let y : Fin (Module.finrank Real E - 1) →
      Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    fun i t => phi t • basis i
  let dy : Fin (Module.finrank Real E - 1) →
      Real → EuclideanSpace Real (Fin (Module.finrank Real E - 1)) :=
    fun i t => deriv phi t • basis i
  let V : Fin (Module.finrank Real E - 1) → Real → E :=
    fun i t => perpFrameLift (I := I) F (y i) t
  have hy_smooth (i : Fin (Module.finrank Real E - 1)) :
      ContDiff Real ∞ (y i) :=
    hphi.smul_const (basis i)
  have hdy_smooth (i : Fin (Module.finrank Real E - 1)) :
      ContDiff Real ∞ (dy i) :=
    (contDiff_infty_iff_deriv.mp hphi).2.smul_const (basis i)
  have hy_deriv (i : Fin (Module.finrank Real E - 1)) :
      deriv (y i) = dy i := by
    funext t
    exact ((((contDiff_infty_iff_deriv.mp hphi).1 t).hasDerivAt.smul_const
      (basis i)).deriv)
  have hV_smooth (i : Fin (Module.finrank Real E - 1)) :
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun t => TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _)) (gamma t) (V i t)) :=
    perpLift_smooth (I := I) hgamma F (y i) (hy_smooth i) hFsmooth
  have hform_nonneg (i : Fin (Module.finrank Real E - 1)) :
      0 ≤ DifferentialGeometry.Analysis.ODE.indexForm
        (perpCurvOp (I := I) g gamma F) 0 L
        (y i) (dy i) (y i) (dy i) := by
    have hVperp : ∀ t ∈ Set.Icc (0 : Real) L,
        g.inner (gamma t) (V i t)
          (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) = 0 := by
      intro t ht
      exact perpLift_perp (I := I) g F (y i) t _ (hFperp t ht)
    have hV0 : V i 0 = 0 := by
      apply perpLift_zero
      simp only [y, hphi0, zero_smul]
    have hVL : V i L = 0 := by
      apply perpLift_zero
      simp only [y, hphiL, zero_smul]
    have hnonneg : 0 ≤ indexForm (I := I) g gamma 0 L (V i) (V i) :=
      indexForm_nonneg_of_minimising_geodesic
        (I := I) g hEnorm gamma L (V i) hL hgamma (hV_smooth i)
          hgeo hmin hunit hVperp hV0 hVL
    have heq := perpLift_indexForm (I := I) g gamma F (y i) (y i) 0 L
      (fun t _ => ((hy_smooth i).differentiable (by simp)) t)
      (fun t _ => ((hy_smooth i).differentiable (by simp)) t)
      (fun j t ht => hFdiff j t (by simpa [Set.uIcc_of_le hL.le] using ht))
      (fun j t ht => hFpar j t (by simpa [Set.uIcc_of_le hL.le] using ht))
      (fun t ht => hFON t (by simpa [Set.uIcc_of_le hL.le] using ht))
    change indexForm (I := I) g gamma 0 L (V i) (V i) = _ at heq
    rw [hy_deriv i] at heq
    rw [← heq]
    exact hnonneg
  have hsum_nonneg : 0 ≤
      ∑ i : Fin (Module.finrank Real E - 1),
        DifferentialGeometry.Analysis.ODE.indexForm
          (perpCurvOp (I := I) g gamma F) 0 L
          (y i) (dy i) (y i) (dy i) :=
    Finset.sum_nonneg fun i _ => hform_nonneg i
  have hR_smooth : ContDiff Real ∞ (perpCurvOp (I := I) g gamma F) :=
    perpCurv_smooth (I := I) g gamma hgamma F hFsmooth
  have hint (i : Fin (Module.finrank Real E - 1)) :
      IntervalIntegrable
        (DifferentialGeometry.Analysis.ODE.indexIntegrand
          (perpCurvOp (I := I) g gamma F)
          (y i) (dy i) (y i) (dy i)) volume 0 L :=
    DifferentialGeometry.Analysis.ODE.intInt_indexIntegrand
      hR_smooth.continuous.continuousOn
      (hy_smooth i).continuous.continuousOn
      (hdy_smooth i).continuous.continuousOn
      (hy_smooth i).continuous.continuousOn
      (hdy_smooth i).continuous.continuousOn
  have hsum_eq :
      (∑ i : Fin (Module.finrank Real E - 1),
        DifferentialGeometry.Analysis.ODE.indexForm
          (perpCurvOp (I := I) g gamma F) 0 L
          (y i) (dy i) (y i) (dy i)) =
      ∫ t in (0 : Real)..L,
        ((Module.finrank Real E - 1 : Real) * deriv phi t ^ 2 -
          phi t ^ 2 * ricciTensor (I := I) g (gamma t)
            (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
            (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))) := by
    calc
      (∑ i : Fin (Module.finrank Real E - 1),
          DifferentialGeometry.Analysis.ODE.indexForm
            (perpCurvOp (I := I) g gamma F) 0 L
            (y i) (dy i) (y i) (dy i)) =
          ∑ i : Fin (Module.finrank Real E - 1),
            ∫ t in (0 : Real)..L,
              DifferentialGeometry.Analysis.ODE.indexIntegrand
                (perpCurvOp (I := I) g gamma F)
                (y i) (dy i) (y i) (dy i) t := by rfl
      _ = ∫ t in (0 : Real)..L,
          ∑ i : Fin (Module.finrank Real E - 1),
            DifferentialGeometry.Analysis.ODE.indexIntegrand
              (perpCurvOp (I := I) g gamma F)
              (y i) (dy i) (y i) (dy i) t :=
        (intervalIntegral.integral_finsetSum (fun i _ => hint i)).symm
      _ = ∫ t in (0 : Real)..L,
          ((Module.finrank Real E - 1 : Real) * deriv phi t ^ 2 -
            phi t ^ 2 * ricciTensor (I := I) g (gamma t)
              (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
              (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htIcc : t ∈ Set.Icc (0 : Real) L := by
          simpa [Set.uIcc_of_le hL.le] using ht
        simpa only [y, dy, basis,
          DifferentialGeometry.Analysis.ODE.indexIntegrand] using
            sum_indexIntegrand_eq_weighted_ricci (I := I) g gamma F t
              (phi t) (deriv phi t)
              (hunit t htIcc) (hFON t htIcc) (hFperp t htIcc)
  have henergy_int : IntervalIntegrable
      (fun t : Real => (Module.finrank Real E - 1 : Real) * deriv phi t ^ 2)
      volume 0 L :=
    ((contDiff_infty_iff_deriv.mp hphi).2.continuous.pow 2).intervalIntegrable 0 L
      |>.const_mul _
  have hsum_int : IntervalIntegrable
      (fun t : Real =>
        ∑ i : Fin (Module.finrank Real E - 1),
          DifferentialGeometry.Analysis.ODE.indexIntegrand
            (perpCurvOp (I := I) g gamma F)
            (y i) (dy i) (y i) (dy i) t) volume 0 L := by
    have hs := IntervalIntegrable.sum Finset.univ fun i _ => hint i
    refine hs.congr ?_
    intro t _
    simp
  have hric_int : IntervalIntegrable
      (fun t : Real => phi t ^ 2 * ricciTensor (I := I) g (gamma t)
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))) volume 0 L := by
    refine (henergy_int.sub hsum_int).congr ?_
    intro t ht
    have ht' : t ∈ Set.uIcc (0 : Real) L := Set.uIoc_subset_uIcc ht
    have htIcc : t ∈ Set.Icc (0 : Real) L := by
      simpa [Set.uIcc_of_le hL.le] using ht'
    have hp := sum_indexIntegrand_eq_weighted_ricci (I := I) g gamma F t
      (phi t) (deriv phi t)
      (hunit t htIcc) (hFON t htIcc) (hFperp t htIcc)
    have hp' :
        (∑ i : Fin (Module.finrank Real E - 1),
          DifferentialGeometry.Analysis.ODE.indexIntegrand
            (perpCurvOp (I := I) g gamma F)
            (y i) (dy i) (y i) (dy i) t) =
          (Module.finrank Real E - 1 : Real) * deriv phi t ^ 2 -
            phi t ^ 2 * ricciTensor (I := I) g (gamma t)
              (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
              (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) := by
      simpa only [y, dy, basis,
        DifferentialGeometry.Analysis.ODE.indexIntegrand] using hp
    linarith
  rw [hsum_eq, intervalIntegral.integral_sub henergy_int hric_int,
    intervalIntegral.integral_const_mul] at hsum_nonneg
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem weighted_ricci_integral_le_aux
    [T2Space (TangentBundle I M)]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [CompleteSpace E]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (gamma : Real → M) {L : Real} (hL : 0 < L)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hgeo : IsGeodesicOn (I := I) g gamma (Set.Icc 0 L))
    (hmin : ∀ eta : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 eta (Set.Icc 0 L) →
      eta 0 = gamma 0 → eta L = gamma L →
      arcLength (I := I) g gamma 0 L ≤ arcLength (I := I) g eta 0 L)
    (hunit : ∀ t ∈ Set.Icc (0 : Real) L,
      g.inner (gamma t)
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) = 1)
    (phi : Real → Real) (hphi : ContDiff Real ∞ phi)
    (hphi0 : phi 0 = 0) (hphiL : phi L = 0) :
    (∫ t in (0 : Real)..L, phi t ^ 2 *
      ricciTensor (I := I) g (gamma t)
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))) ≤
      (Module.finrank Real E - 1 : Real) *
        ∫ t in (0 : Real)..L, deriv phi t ^ 2 := by
  obtain ⟨F, hFdiff, hFpar, hFON, hFperp, hFsmooth⟩ :=
    exists_parallel_perp_frame (I := I) g gamma hgamma hL hgeo
      (hunit 0 ⟨le_rfl, hL.le⟩)
  exact weighted_ricci_integral_le_with_frame
    (I := I) g hEnorm gamma hL hgamma hgeo hmin hunit
      (fun i => (F i).toFun) hFdiff hFpar hFON hFperp hFsmooth
        phi hphi hphi0 hphiL

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem weighted_ricci_integral_le_of_minimising_geodesic
    [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (gamma : Real → M) {L : Real} (hL : 0 < L)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hgeo : IsGeodesicOn (I := I) g gamma (Set.Icc 0 L))
    (hmin : ∀ eta : Real → M,
      ContMDiffOn 𝓘(Real, Real) I 1 eta (Set.Icc 0 L) →
      eta 0 = gamma 0 → eta L = gamma L →
      arcLength (I := I) g gamma 0 L ≤ arcLength (I := I) g eta 0 L)
    (hunit : ∀ t ∈ Set.Icc (0 : Real) L,
      g.inner (gamma t)
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real)) = 1)
    (phi : Real → Real) (hphi : ContDiff Real ∞ phi)
    (hphi0 : phi 0 = 0) (hphiL : phi L = 0) :
    (∫ t in (0 : Real)..L, phi t ^ 2 *
      ricciTensor (I := I) g (gamma t)
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))
        (mfderiv 𝓘(Real, Real) I gamma t (1 : Real))) ≤
      (Module.finrank Real E - 1 : Real) *
        ∫ t in (0 : Real)..L, deriv phi t ^ 2 := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := inferInstance
  let : CompleteSpace M := hcomplete.complete
  let hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  exact weighted_ricci_integral_le_aux
    (I := I) g hEnorm gamma hL hgamma hgeo hmin hunit
      phi hphi hphi0 hphiL

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
