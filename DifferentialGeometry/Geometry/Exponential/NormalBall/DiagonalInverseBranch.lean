import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.InverseBranch
import DifferentialGeometry.Geometry.Exponential.NormalBall.Homeomorphism
import DifferentialGeometry.Geometry.Exponential.NormalBall.TangentCoordinates
import DifferentialGeometry.Geometry.Exponential.NormalBall.Recenter

noncomputable section
open Set Bundle
open scoped ContDiff Manifold
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open Exponential

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

def diagonalInverseBranch
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {p : M} (c : NormalBallChart (I := I) p)
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (hzero : (0 : E × E) ∈ e.source) (hezero : e 0 = 0)
    (hinv : ContDiffOn ℝ ∞ (e.symm : E × E → E × E) e.target)
    (hdiag : ∀ z ∈ e.source, c.pair (e z) = diagExp (I := I) g hEnorm (c.tangent z)) :
    DiagonalInverseBranch (I := I) g hEnorm p := by
  let A := c.tangentHome
  let P := c.pairHome
  let D := A.symm.trans (e.trans P)
  let u0 : TangentBundle I M := ⟨p, 0⟩
  have hz : (0 : E) ∈ Metric.ball 0 c.radius := Metric.mem_ball_self c.radius_pos
  have hAsource : (0 : E × E) ∈ A.source := by
    rw [tangentHome_source]
    exact hz
  have hAzero : A 0 = u0 := by
    rw [tangentHome_apply c 0 hz]
    exact c.tangent_zero
  have hPsource : (0 : E × E) ∈ P.source := by
    rw [pairHome_source]
    exact ⟨hz, hz⟩
  refine { hom := D, zero_mem := ?_, hom_eq := ?_, inv_contMDiffOn := ?_ }
  · change u0 ∈ A.target ∩ A.symm ⁻¹' (e.trans P).source
    have hAtarget : u0 ∈ A.target := hAzero ▸ A.map_source hAsource
    have hAinv : A.symm u0 = 0 := by rw [← hAzero]; exact A.left_inv hAsource
    refine ⟨hAtarget, ?_⟩
    change A.symm u0 ∈ e.source ∩ e ⁻¹' P.source
    rw [hAinv]
    exact ⟨hzero, by change e 0 ∈ P.source; rw [hezero]; exact hPsource⟩
  · intro u hu
    change u ∈ A.target ∩ A.symm ⁻¹' (e.source ∩ e ⁻¹' P.source) at hu
    have hzA := A.map_target hu.1
    have htan : c.tangent (A.symm u) = u := by
      rw [← c.tangentHome_apply (A.symm u) (by
        simpa only [A, tangentHome_source, mem_preimage] using hzA)]
      exact A.right_inv hu.1
    change c.pair (e (A.symm u)) = diagExp (I := I) g hEnorm u
    rw [hdiag (A.symm u) hu.2.1, htan]
  · let B := e.trans P
    have heInv : ContMDiffOn 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) ∞ e.symm e.target :=
      hinv.contMDiffOn
    have hBInv : ContMDiffOn (I.prod I) 𝓘(ℝ, E × E) ∞ B.symm B.target := by
      change ContMDiffOn (I.prod I) 𝓘(ℝ, E × E) ∞
        ((e.symm : E × E → E × E) ∘ (P.symm : M × M → E × E))
        (P.target ∩ (P.symm : M × M → E × E) ⁻¹' e.target)
      exact heInv.comp' c.pairHome_symm_contMDiffOn
    change ContMDiffOn (I.prod I) I.tangent ∞
      ((A : E × E → TangentBundle I M) ∘ (B.symm : M × M → E × E))
      (B.target ∩ (B.symm : M × M → E × E) ⁻¹' A.source)
    exact c.tangentHome_contMDiffOn.comp' hBInv

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
end

noncomputable section
open Set Bundle
open scoped ContDiff Manifold
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open Exponential

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) (M := M) g}
  {p : M} (c : NormalBallChart (I := I) p)
  (e : OpenPartialHomeomorph (E × E) (E × E))
  (hzero : (0 : E × E) ∈ e.source) (hezero : e 0 = 0)
  (hinv : ContDiffOn ℝ ∞ (e.symm : E × E → E × E) e.target)
  (hdiag : ∀ z ∈ e.source, c.pair (e z) = diagExp (I := I) g hEnorm (c.tangent z))

theorem diagonalInverseBranch_mem_source_iff {y : M} (v : TangentSpace I y)
    (hy : y ∈ c.restrictBall.target) :
    (⟨y, v⟩ : TangentBundle I M) ∈
        (c.diagonalInverseBranch e hzero hezero hinv hdiag).hom.source ↔
      (c.inv y, mfderiv I 𝓘(ℝ, E) c.inv y v) ∈ e.source ∧
      e (c.inv y, mfderiv I 𝓘(ℝ, E) c.inv y v) ∈ c.pairHome.source := by
  change (⟨y, v⟩ : TangentBundle I M) ∈ c.tangentHome.target ∩
    c.tangentHome.symm ⁻¹' (e.source ∩ e ⁻¹' c.pairHome.source) ↔ _
  have hyt : (⟨y, v⟩ : TangentBundle I M) ∈ c.tangentHome.target := by
    rw [tangentHome_target]
    exact hy
  simp only [mem_inter_iff, mem_preimage, hyt, true_and,
    c.tangentHome_symm_apply hy v]
  rfl

theorem diagonalInverseBranch_fiber_ball_subset
    {q r C : ℝ} (hC : 0 < C) (hrq : C * r ≤ q)
    (hsource : Metric.ball (0 : E × E) q ⊆ e.source)
    (hfence : MapsTo e (Metric.ball (0 : E × E) q) c.pairHome.source)
    {y : M} (hy : y ∈ c.restrictBall.target) (hyq : ‖c.inv y‖ < q)
    (hread : ∀ v : TangentSpace I y,
      ‖(tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) (c.inv y) (mfderiv I 𝓘(ℝ, E) c.inv y v))‖ ≤ C * Real.sqrt (g.inner y v v)) :
    ∀ v : TangentSpace I y, Real.sqrt (g.inner y v v) < r →
      (⟨y, v⟩ : TangentBundle I M) ∈
        (c.diagonalInverseBranch e hzero hezero hinv hdiag).hom.source := by
  intro v hv
  apply (c.diagonalInverseBranch_mem_source_iff e hzero hezero hinv hdiag v hy).2
  have hnorm : ‖(tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) (c.inv y) (mfderiv I 𝓘(ℝ, E) c.inv y v))‖ < q :=
    (hread v).trans_lt ((mul_lt_mul_of_pos_left hv hC).trans_le hrq)
  have hpair : (c.inv y, tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) (c.inv y)
      (mfderiv I 𝓘(ℝ, E) c.inv y v)) ∈ Metric.ball (0 : E × E) q := by
    simp only [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff]
    exact ⟨hyq, hnorm⟩
  exact ⟨hsource hpair, hfence hpair⟩

theorem diagonalInverseBranch_fiber_ball_subset_of_metric_lower_bound
    {q : ℝ}
    (hsource : Metric.ball (0 : E × E) q ⊆ e.source)
    (hfence : MapsTo e (Metric.ball (0 : E × E) q) c.pairHome.source)
    {y : M} (hy : y ∈ c.restrictBall.target) (hyq : ‖c.inv y‖ < q)
    (hlower : ∀ w : E, (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ c.metric g (c.inv y) w w) :
    ∀ v : TangentSpace I y, Real.sqrt (g.inner y v v) < q / 2 →
      (⟨y, v⟩ : TangentBundle I M) ∈
        (c.diagonalInverseBranch e hzero hezero hinv hdiag).hom.source := by
  apply c.diagonalInverseBranch_fiber_ball_subset e hzero hezero hinv hdiag
    (by norm_num : (0 : ℝ) < 2) (by linarith : 2 * (q / 2) ≤ q)
    hsource hfence hy hyq
  intro v
  exact c.norm_mfderiv_inv_le_of_metric_lower_bound g hy hlower v

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
end

noncomputable section
open Set Bundle
open scoped ContDiff Manifold
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open Exponential

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable {g : SmoothRiemannianMetric I M}
  {hEnorm : IsMetricNorm (I := I) (M := M) g}
  {p : M} (c : NormalBallChart (I := I) p)
  (e : OpenPartialHomeomorph (E × E) (E × E))
  (hdiag : ∀ z ∈ e.source, c.pair (e z) = diagExp (I := I) g hEnorm (c.tangent z))
  (hfence : ∀ z ∈ e.source,
    z.1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).1 ∈ Metric.ball (0 : E) c.radius ∧ (e z).2 ∈ Metric.ball (0 : E) c.radius)

include hdiag hfence in
theorem diagonal_inverse_fst {z : E × E} (hz : z ∈ e.target) :
    (e.symm z).1 = z.1 := by
  have hsrc := e.map_target hz
  have hd := congrArg Prod.fst (hdiag (e.symm z) hsrc)
  have hf := hfence (e.symm z) hsrc
  have hid : c.hom (e (e.symm z)).1 = c.hom (e.symm z).1 := hd
  have hfst := c.hom.injOn (c.ball_subset hf.2.1) (c.ball_subset hf.1) hid
  simpa only [e.right_inv hz] using hfst.symm

include hdiag hfence in
theorem diagonal_inverse_norm_lt {z : E × E} (hz : z ∈ e.target)
    {q : ℝ} (hmem : e.symm z ∈ Metric.ball (0 : E × E) q) : ‖z.1‖ < q := by
  have hfst := c.diagonal_inverse_fst e hdiag hfence hz
  have hnorm : ‖(e.symm z).1‖ < q := by
    exact lt_of_le_of_lt (norm_fst_le (e.symm z)) (by simpa only [Metric.mem_ball, dist_zero_right] using hmem)
  simpa only [hfst] using hnorm

include hfence in
theorem diagonalInverseBranch_inv_apply
    (hzero : (0 : E × E) ∈ e.source) (hezero : e 0 = 0)
    (hinv : ContDiffOn ℝ ∞ (e.symm : E × E → E × E) e.target)
    {a b : E} (ha : a ∈ Metric.ball (0 : E) c.radius)
    (hb : b ∈ Metric.ball (0 : E) c.radius) (hab : (a, b) ∈ e.target) :
    (c.diagonalInverseBranch e hzero hezero hinv hdiag).inv (c.hom a, c.hom b) =
      (⟨c.hom a, mfderiv (modelWithCornersSelf ℝ E) I c.hom a
        (e.symm (a, b)).2⟩ : TangentBundle I M) := by
  exact c.tangentHome_trans_pairHome_symm_apply ha hb
    (c.diagonal_inverse_fst e hdiag hfence hab)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
end

noncomputable section
open Set Bundle
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open Exponential

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable {g : SmoothRiemannianMetric I M}
  {hEnorm : IsMetricNorm (I := I) (M := M) g} {p : M}

theorem mem_recenter_target_of_inverse_pair_mem
    (c : NormalBallChart (I := I) p) (a : E) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball a r ⊆ Metric.ball (0 : E) c.radius)
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (hdiag : ∀ z ∈ e.source,
      (c.recenter a hr hball).pair (e z) = diagExp (I := I) g hEnorm
        ((c.recenter a hr hball).tangent z))
    (hfence : ∀ z ∈ e.source,
      z.1 ∈ Metric.ball (0 : E) (c.recenter a hr hball).radius ∧
      (e z).1 ∈ Metric.ball (0 : E) (c.recenter a hr hball).radius ∧
      (e z).2 ∈ Metric.ball (0 : E) (c.recenter a hr hball).radius)
    {y : M} (hy : y ∈ c.hom.target) {ξ : E}
    (hpair : ((c.recenter a hr hball).inv y, ξ) ∈ e.target) :
    y ∈ (c.recenter a hr hball).restrictBall.target := by
  have hcoord := (hfence (e.symm ((c.recenter a hr hball).inv y, ξ))
    (e.map_target hpair)).1
  rw [(c.recenter a hr hball).diagonal_inverse_fst e hdiag hfence hpair] at hcoord
  exact (c.recenter_apply_inv_of_mem_target a hr hball hy hcoord rfl).2.2

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
end
