import DifferentialGeometry.Geometry.Comparison.Variation.CovariantGronwall
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Curvature.Rm04OperatorBound
import DifferentialGeometry.Geometry.Exponential.EndpointShape
import DifferentialGeometry.Geometry.Exponential.IntrinsicSmooth

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def IntrinsicRm04Bound
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : TangentSpace I p) (R : Real) : Prop :=
  ∀ t ∈ Ico (0 : Real) 1,
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm p u t) 4
      (DifferentialGeometry.Geometry.Curvature.metricRm04At
        (I := I) (M := M) g
        (intrinsicGeodesic (I := I) g hEnorm p u t))) ≤ R

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrJacobi_ode
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u w : TangentSpace I p) {R : Real}
    (hR : 0 ≤ R)
    (hRm : IntrinsicRm04Bound (I := I) g hEnorm p u R) :
    ∀ t ∈ Ico (0 : Real) 1,
      g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
          (covDerivAlong (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u)
            (fun s => covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u)
              (intrinsicJacobi (I := I) g hEnorm p u w) s) t)
          (covDerivAlong (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u)
            (fun s => covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u)
              (intrinsicJacobi (I := I) g hEnorm p u w) s) t)
        ≤ (Real.sqrt
              (Fintype.card
                (Fin (Module.finrank Real E)) : Real) *
              R * g.inner p u u) ^ 2 *
            g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
              (intrinsicJacobi (I := I) g hEnorm p u w t)
              (intrinsicJacobi (I := I) g hEnorm p u w t) := by
  classical
  let γ : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm p u
  let J : ∀ t : Real, TangentSpace I (γ t) :=
    intrinsicJacobi (I := I) g hEnorm p u w
  have hJac : IsJacobiAlong (I := I) g γ J := by
    have hγeq :
        γ = fun t ↦ intrinsicGeodesic (I := I) g hEnorm p u t := rfl
    have hJeq :
        J = fun t ↦ intrinsicJacobi (I := I) g hEnorm p u w t := rfl
    rw [hγeq, hJeq]
    exact intrinsic_jacobi (I := I) g hEnorm p (u : E) (w : E)
  intro t ht
  have hD2 := (isJacobiAlong_iff (I := I) g γ J).mp hJac t
  have htBound : t ∈ Ico (0 : Real) 1 := ht
  · let q : M := γ t
    let V : TangentSpace I q := curveVelocity (I := I) γ t
    let Jt : TangentSpace I q := J t
    let Rv : TangentSpace I q :=
      DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
        q Jt V V
    have hfin :
        Module.finrank Real (TangentSpace I q) ≠ 0 := by
      rw [show Module.finrank Real (TangentSpace I q) = Module.finrank Real E from rfl]
      exact NeZero.out
    let : Nonempty
        (Fin (Module.finrank Real (TangentSpace I q))) :=
      Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hfin)
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis
        (I := I) g q
    have hOp :=
      DifferentialGeometry.Integral.Connection.riemannOp_sq_le
        (I := I) g q basis (by simp) hON Jt V
    have hcardq :
        (Fintype.card (Fin (Module.finrank Real (TangentSpace I q))) : Real) =
          (Fintype.card (Fin (Module.finrank Real E)) : Real) := by
      rfl
    rw [hcardq] at hOp
    have hRmAt :
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g q)) ≤ R := by
      simpa only [q, γ] using hRm t htBound
    have hJnn : 0 ≤ g.inner q Jt Jt := by
      rcases eq_or_ne Jt 0 with hzero | hne
      · simp [hzero]
      · exact (g.pos q Jt hne).le
    have hu_nn : 0 ≤ g.inner p u u := by
      rcases eq_or_ne u 0 with hzero | hne
      · simp [hzero]
      · exact (g.pos p u hne).le
    have hVeq : g.inner q V V = g.inner p u u := by
      convert intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u t using 1
      all_goals rfl
    have hVroot :
        (Real.sqrt (g.inner q V V)) ^ 2 = g.inner p u u := by
      rw [Real.sq_sqrt]
      · exact hVeq
      · rw [hVeq]
        exact hu_nn
    have hJroot :
        (Real.sqrt (g.inner q Jt Jt)) ^ 2 = g.inner q Jt Jt :=
      Real.sq_sqrt hJnn
    let n : Real :=
      Fintype.card (Fin (Module.finrank Real E))
    have hn_nn : 0 ≤ n := by positivity
    have hnroot : (Real.sqrt n) ^ 2 = n :=
      Real.sq_sqrt hn_nn
    let A : Real :=
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g q))
    have hA_nn : 0 ≤ A := Real.sqrt_nonneg _
    have hcore :
        A * Real.sqrt (g.inner q Jt Jt) *
            (Real.sqrt (g.inner q V V)) ^ 2
          ≤ R * Real.sqrt (g.inner q Jt Jt) * g.inner p u u := by
      rw [hVroot]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hRmAt (Real.sqrt_nonneg _)) hu_nn
    have hcore_nn :
        0 ≤ A * Real.sqrt (g.inner q Jt Jt) *
            (Real.sqrt (g.inner q V V)) ^ 2 :=
      mul_nonneg (mul_nonneg hA_nn (Real.sqrt_nonneg _)) (sq_nonneg _)
    have hcoreR_nn :
        0 ≤ R * Real.sqrt (g.inner q Jt Jt) * g.inner p u u :=
      mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg _)) hu_nn
    have hscaled :
        n * (A * Real.sqrt (g.inner q Jt Jt) *
            (Real.sqrt (g.inner q V V)) ^ 2) ^ 2
          ≤ n * (R * Real.sqrt (g.inner q Jt Jt) *
            g.inner p u u) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hcore_nn hcoreR_nn).2 hcore) hn_nn
    have htarget :
        n * (R * Real.sqrt (g.inner q Jt Jt) *
            g.inner p u u) ^ 2 =
          (Real.sqrt n * R * g.inner p u u) ^ 2 *
            g.inner q Jt Jt := by
      calc
        n * (R * Real.sqrt (g.inner q Jt Jt) *
            g.inner p u u) ^ 2 =
            n * R ^ 2 * (Real.sqrt (g.inner q Jt Jt)) ^ 2 *
              (g.inner p u u) ^ 2 := by ring
        _ = n * R ^ 2 * g.inner q Jt Jt *
              (g.inner p u u) ^ 2 := by rw [hJroot]
        _ = (Real.sqrt n) ^ 2 * R ^ 2 *
              (g.inner p u u) ^ 2 * g.inner q Jt Jt := by
          rw [hnroot]
          ring
        _ = (Real.sqrt n * R * g.inner p u u) ^ 2 *
              g.inner q Jt Jt := by ring
    rw [hD2]
    change g.inner q (-Rv) (-Rv) ≤ _
    have hneg : g.inner q (-Rv) (-Rv) = g.inner q Rv Rv := by
      simp
    rw [hneg]
    calc
      g.inner q Rv Rv ≤
          n * (A * Real.sqrt (g.inner q Jt Jt) *
            (Real.sqrt (g.inner q V V)) ^ 2) ^ 2 := by
        simpa only [A, q, V, Jt, Rv] using hOp
      _ ≤ n * (R * Real.sqrt (g.inner q Jt Jt) *
            g.inner p u u) ^ 2 := hscaled
      _ = (Real.sqrt n * R * g.inner p u u) ^ 2 *
            g.inner q Jt Jt := htarget
      _ = (Real.sqrt
              (Fintype.card
                (Fin (Module.finrank Real E)) : Real) *
              R * g.inner p u u) ^ 2 *
            g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
              (intrinsicJacobi (I := I) g hEnorm p u w t)
              (intrinsicJacobi (I := I) g hEnorm p u w t) := rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrJacobi_bounds
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u w : TangentSpace I p) {K b : Real}
    (hK : 0 ≤ K) (hb : 0 < b)
    (hODE : ∀ t ∈ Ico (0 : Real) b,
      g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
          (covDerivAlong (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u)
            (fun s => covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u)
              (intrinsicJacobi (I := I) g hEnorm p u w) s) t)
          (covDerivAlong (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u)
            (fun s => covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u)
              (intrinsicJacobi (I := I) g hEnorm p u w) s) t)
        ≤ K ^ 2 *
          g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
            (intrinsicJacobi (I := I) g hEnorm p u w t)
            (intrinsicJacobi (I := I) g hEnorm p u w t)) :
    (∀ t ∈ Icc (0 : Real) b,
      Real.sqrt
          (g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
            (intrinsicJacobi (I := I) g hEnorm p u w t)
            (intrinsicJacobi (I := I) g hEnorm p u w t)) ≤
        t * Real.sqrt (g.inner p w w) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner p w w))) t) ∧
    (∀ t ∈ Icc (0 : Real) b,
      t * Real.sqrt (g.inner p w w) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner p w w))) t ≤
        Real.sqrt
          (g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
            (intrinsicJacobi (I := I) g hEnorm p u w t)
            (intrinsicJacobi (I := I) g hEnorm p u w t))) := by
  classical
  let γ : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm p u
  let J : ∀ t : Real, TangentSpace I (γ t) :=
    intrinsicJacobi (I := I) g hEnorm p u w
  have hγInf : ContMDiff 𝓘(Real, Real) I ∞ γ := by
    simpa only [γ] using
      intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hγ2 : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) γ :=
    hγInf.of_le ENat.LEInfty.out
  obtain ⟨basis, hON0⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis
      (I := I) g (γ 0)
  obtain ⟨F, _hF0, hFdiff, hFpar, hFON⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_parallel_frame
      (I := I) g γ (N := 2) (by norm_num) hγ2 hb basis hON0
  have hcard : ∀ t : Real,
      Fintype.card
          (Fin (Module.finrank Real (TangentSpace I (γ 0)))) =
        Module.finrank Real (TangentSpace I (γ t)) := by
    intro t
    simp only [Fintype.card_fin]
    rfl
  have hfin :
      Module.finrank Real (TangentSpace I (γ 0)) ≠ 0 := by
    rw [show Module.finrank Real (TangentSpace I (γ 0)) = Module.finrank Real E from rfl]
    exact NeZero.out
  let : Nonempty (Fin (Module.finrank Real (TangentSpace I (γ 0)))) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hfin)
  have hJdiff : ∀ t ∈ Icc (0 : Real) b,
      DifferentiableAt Real (chartRepAt (I := I) γ J t) t := by
    intro t _ht
    exact (intrJacobi_diff (I := I) g hEnorm p u w t).1
  have hDJdiff : ∀ t ∈ Icc (0 : Real) b,
      DifferentiableAt Real
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ J s) t) t := by
    intro t _ht
    exact (intrJacobi_diff (I := I) g hEnorm p u w t).2
  have hJ0 : J 0 = 0 := by
    simpa only [J] using intrinsicJacobi_zero (I := I) g hEnorm p u w
  have hDJ0 : covDerivAlong (I := I) g γ J 0 = w := by
    have hγeq :
        γ = fun t ↦ intrinsicGeodesic (I := I) g hEnorm p u t := rfl
    have hJeq :
        J = fun t ↦ intrinsicJacobi (I := I) g hEnorm p u w t := rfl
    rw [hγeq, hJeq]
    exact intrinsic_jacobi_d0 (I := I) g hEnorm p (u : E) (w : E)
  have hbounds := covGronwall_bounds_at (I := I) g γ
    (K := K) (b := b) (fun _ _ => hγInf.contMDiffAt.of_le (by norm_num))
    hcard F J hK hb.le hFpar hFON hFdiff hJdiff hDJdiff hODE hJ0 hDJ0
  have hγ0 : intrinsicGeodesic (I := I) g hEnorm p u 0 = p :=
    intrinsicGeodesic_zero (I := I) g hEnorm p u
  dsimp only [γ, J] at hbounds
  rw [hγ0] at hbounds
  exact hbounds

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrForce_pair
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u : TangentSpace I p)
    (J : ∀ t : Real,
      TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u t))
    {K eps delta b : Real}
    (hK : 0 ≤ K) (heps : 0 ≤ eps) (hb : 0 < b)
    (hJ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (intrinsicGeodesic (I := I) g hEnorm p u t) (J t) :
            TangentBundle I M)))
    (hDJ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (intrinsicGeodesic (I := I) g hEnorm p u t)
          (covDerivAlong (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u) J t) :
              TangentBundle I M)))
    (hODE : ∀ t ∈ Ico (0 : Real) b,
      Real.sqrt
          (g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
            (covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u)
              (fun s => covDerivAlong (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm p u) J s) t)
            (covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u)
              (fun s => covDerivAlong (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm p u) J s) t)) ≤
        K * Real.sqrt
          (g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
            (J t) (J t)) + eps)
    (hJ0 : Real.sqrt
      (g.inner (intrinsicGeodesic (I := I) g hEnorm p u 0)
        (J 0) (J 0)) ≤ delta)
    (hDJ0 : Real.sqrt
      (g.inner (intrinsicGeodesic (I := I) g hEnorm p u 0)
        (covDerivAlong (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u) J 0)
        (covDerivAlong (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u) J 0)) ≤ delta) :
    (∀ t ∈ Icc (0 : Real) b,
      Real.sqrt
          (g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
            (J t) (J t)) ≤
        gronwallBound delta (max K 1) eps t) ∧
    (∀ t ∈ Icc (0 : Real) b,
      Real.sqrt
          (g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
            (covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u) J t)
            (covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u) J t)) ≤
        gronwallBound delta (max K 1) eps t) := by
  classical
  let γ : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm p u
  have hγInf : ContMDiff 𝓘(Real, Real) I ∞ γ := by
    simpa only [γ] using
      intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hγ2 : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) γ :=
    hγInf.of_le ENat.LEInfty.out
  obtain ⟨basis, hON0⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis
      (I := I) g (γ 0)
  obtain ⟨F, _hF0, hFdiff, hFpar, hFON⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_parallel_frame
      (I := I) g γ (N := 2) (by norm_num) hγ2 hb basis hON0
  have hcard : ∀ t : Real,
      Fintype.card
          (Fin (Module.finrank Real (TangentSpace I (γ 0)))) =
        Module.finrank Real (TangentSpace I (γ t)) := by
    intro t
    simp only [Fintype.card_fin]
    rfl
  have hfin :
      Module.finrank Real (TangentSpace I (γ 0)) ≠ 0 := by
    rw [show Module.finrank Real (TangentSpace I (γ 0)) = Module.finrank Real E from rfl]
    exact NeZero.out
  let : Nonempty (Fin (Module.finrank Real (TangentSpace I (γ 0)))) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hfin)
  have hJdiff : ∀ t ∈ Icc (0 : Real) b,
      DifferentiableAt Real (chartRepAt (I := I) γ J t) t := by
    intro t _ht
    exact chartRep_diff (I := I) γ J (by simpa only [γ] using hJ) t
  have hDJdiff : ∀ t ∈ Icc (0 : Real) b,
      DifferentiableAt Real
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ J s) t) t := by
    intro t _ht
    exact chartRep_diff (I := I) γ
      (fun s => covDerivAlong (I := I) g γ J s)
      (by simpa only [γ] using hDJ) t
  have hbounds := covGronwall_pair_at (I := I) g γ
    (K := K) (eps := eps) (delta := delta) (b := b)
    (fun _ _ => hγInf.contMDiffAt.of_le (by norm_num))
    hcard F J hK heps hb.le hFpar hFON hFdiff hJdiff hDJdiff
    (by simpa only [γ] using hODE)
    (by simpa only [γ] using hJ0)
    (by simpa only [γ] using hDJ0)
  simpa only [γ] using hbounds

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrJacobi_pair
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u w : TangentSpace I p) {K b : Real}
    (hK : 0 ≤ K) (hb : 0 < b)
    (hODE : ∀ t ∈ Ico (0 : Real) b,
      Real.sqrt
          (g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
            (covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u)
              (fun s => covDerivAlong (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm p u)
                (intrinsicJacobi (I := I) g hEnorm p u w) s) t)
            (covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u)
              (fun s => covDerivAlong (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm p u)
                (intrinsicJacobi (I := I) g hEnorm p u w) s) t)) ≤
        K * Real.sqrt
          (g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
            (intrinsicJacobi (I := I) g hEnorm p u w t)
            (intrinsicJacobi (I := I) g hEnorm p u w t))) :
    (∀ t ∈ Icc (0 : Real) b,
      Real.sqrt
          (g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
            (intrinsicJacobi (I := I) g hEnorm p u w t)
            (intrinsicJacobi (I := I) g hEnorm p u w t)) ≤
        gronwallBound (Real.sqrt (g.inner p w w)) (max K 1) 0 t) ∧
    (∀ t ∈ Icc (0 : Real) b,
      Real.sqrt
          (g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
            (covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u)
              (intrinsicJacobi (I := I) g hEnorm p u w) t)
            (covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u)
              (intrinsicJacobi (I := I) g hEnorm p u w) t)) ≤
        gronwallBound (Real.sqrt (g.inner p w w)) (max K 1) 0 t) := by
  classical
  let γ : Real → M :=
    intrinsicGeodesic (I := I) g hEnorm p u
  let J : ∀ t : Real, TangentSpace I (γ t) :=
    intrinsicJacobi (I := I) g hEnorm p u w
  have hγInf : ContMDiff 𝓘(Real, Real) I ∞ γ := by
    simpa only [γ] using
      intrinsicGeodesic_contMDiff (I := I) g hEnorm p u
  have hγ2 : ContMDiff 𝓘(Real, Real) I (2 : ℕ∞) γ :=
    hγInf.of_le ENat.LEInfty.out
  obtain ⟨basis, hON0⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis
      (I := I) g (γ 0)
  obtain ⟨F, _hF0, hFdiff, hFpar, hFON⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_parallel_frame
      (I := I) g γ (N := 2) (by norm_num) hγ2 hb basis hON0
  have hcard : ∀ t : Real,
      Fintype.card
          (Fin (Module.finrank Real (TangentSpace I (γ 0)))) =
        Module.finrank Real (TangentSpace I (γ t)) := by
    intro t
    simp only [Fintype.card_fin]
    rfl
  have hfin :
      Module.finrank Real (TangentSpace I (γ 0)) ≠ 0 := by
    rw [show Module.finrank Real (TangentSpace I (γ 0)) = Module.finrank Real E from rfl]
    exact NeZero.out
  let : Nonempty (Fin (Module.finrank Real (TangentSpace I (γ 0)))) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hfin)
  have hJdiff : ∀ t ∈ Icc (0 : Real) b,
      DifferentiableAt Real (chartRepAt (I := I) γ J t) t := by
    intro t _ht
    exact (intrJacobi_diff (I := I) g hEnorm p u w t).1
  have hDJdiff : ∀ t ∈ Icc (0 : Real) b,
      DifferentiableAt Real
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ J s) t) t := by
    intro t _ht
    exact (intrJacobi_diff (I := I) g hEnorm p u w t).2
  have hJ0 : J 0 = 0 := by
    simpa only [J] using intrinsicJacobi_zero (I := I) g hEnorm p u w
  have hDJ0 : covDerivAlong (I := I) g γ J 0 = w := by
    have hγeq :
        γ = fun t ↦ intrinsicGeodesic (I := I) g hEnorm p u t := rfl
    have hJeq :
        J = fun t ↦ intrinsicJacobi (I := I) g hEnorm p u w t := rfl
    rw [hγeq, hJeq]
    exact intrinsic_jacobi_d0 (I := I) g hEnorm p (u : E) (w : E)
  have hγ0 : γ 0 = p := by
    simpa only [γ] using intrinsicGeodesic_zero (I := I) g hEnorm p u
  have hJ0norm :
      Real.sqrt (g.inner (γ 0) (J 0) (J 0)) ≤
        Real.sqrt (g.inner p w w) := by
    rw [hJ0]
    simp only [map_zero, Real.sqrt_zero]
    exact Real.sqrt_nonneg _
  have hDJ0norm :
      Real.sqrt
          (g.inner (γ 0)
            (covDerivAlong (I := I) g γ J 0)
            (covDerivAlong (I := I) g γ J 0)) ≤
        Real.sqrt (g.inner p w w) := by
    rw [hDJ0, hγ0]
  have hbounds := covGronwall_pair_at (I := I) g γ
    (K := K) (eps := 0) (delta := Real.sqrt (g.inner p w w)) (b := b)
    (fun _ _ => hγInf.contMDiffAt.of_le (by norm_num))
    hcard F J hK (by norm_num) hb.le hFpar hFON hFdiff hJdiff hDJdiff
    (by simpa only [γ, J, add_zero] using hODE) hJ0norm hDJ0norm
  simpa only [γ, J] using hbounds

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
