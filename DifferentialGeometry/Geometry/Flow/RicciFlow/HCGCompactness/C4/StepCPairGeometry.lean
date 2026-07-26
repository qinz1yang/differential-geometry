import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringItem3
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ProperBallExp

/-!
# Step C pair geometry

Numerical containment estimates for the stable-intersection branch of two
good-cover centers.  This file keeps the pairwise geometry separate from the
transition-map compactness extraction.
-/

noncomputable section

open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- A stable intersection of the book's `B`-balls sends the physical
`16 * lamInf` source ball into half of the item-3 target ball.  The spare factor
of two is reserved for the framed target-coordinate ball. -/
theorem NetLimitData.sigmaBall_nesting
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) {α β : Nat}
    (hfreq : ∃ᶠ k in atTop, BInter hd D P L.lamInf α β (L.φ k))
    (k : Nat) (hk : BInter hd D P L.lamInf α β (L.φ k))
    {x y : (X.obj (L.φ k)).M}
    (hx : seqCenter hd D P (L.φ k) α = some x)
    (hy : seqCenter hd D P (L.φ k) β = some y) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    Metric.ball x (16 * L.lamInf α) ⊆
      Metric.ball y ((item3RadiusFactor hd D / 2) * L.lamInf β) := by
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  obtain ⟨x', y', hx', hy', hmeet⟩ := hk
  have hxx : x' = x := Option.some.inj (hx'.symm.trans hx)
  have hyy : y' = y := Option.some.inj (hy'.symm.trans hy)
  rw [hxx, hyy] at hmeet
  obtain ⟨w, hwx, hwy⟩ := Set.not_disjoint_iff.mp hmeet
  rw [Metric.mem_ball] at hwx hwy
  have hdxy : dist x y < 5 * L.lamInf α + 5 * L.lamInf β := by
    have htri := dist_triangle x w y
    rw [dist_comm w x] at hwx
    linarith
  have hlamBetaPos : 0 < L.lamInf β := hd.lambda_pos hD (L.rInf β)
  have hAlphaZero : L.lamInf α ≤ hd.lambda D 0 :=
    hd.lambda_antitone hD (L.rInf_mem α).1
  have hBetaZero : L.lamInf β ≤ hd.lambda D 0 :=
    hd.lambda_antitone hD (L.rInf_mem β).1
  have hclose := L.rInf_close hd P hfreq
  have hgap : L.rInf β - L.rInf α ≤ 10 * hd.lambda D 0 := by
    linarith
  have hratio :
      L.lamInf α ≤
        Real.exp (hd.C * (10 * hd.lambda D 0)) * L.lamInf β :=
    hd.lambda_exp_le hD hgap
  set E1 := Real.exp (hd.C * (10 * hd.lambda D 0)) with hE1
  set E2 := Real.exp (hd.C * (20 * hd.lambda D 0)) with hE2
  have hE1ge1 : (1 : Real) ≤ E1 := by
    rw [hE1, show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
    apply Real.exp_le_exp.mpr
    exact mul_nonneg hd.C_nonneg (by linarith [(hd.lambda_pos hD 0).le])
  have hEmul : E1 * E1 = E2 := by
    rw [hE1, hE2, ← Real.exp_add]
    congr 1
    ring
  have hE12 : E1 ≤ E2 := by
    nlinarith
  have hE2ge1 : (1 : Real) ≤ E2 := hE1ge1.trans hE12
  have hAlphaBeta : L.lamInf α ≤ E2 * L.lamInf β := by
    exact hratio.trans (mul_le_mul_of_nonneg_right hE12 hlamBetaPos.le)
  have hBetaBeta : L.lamInf β ≤ E2 * L.lamInf β := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hE2ge1 hlamBetaPos.le
  have hscalePos : 0 < E2 * L.lamInf β :=
    mul_pos (zero_lt_one.trans_le hE2ge1) hlamBetaPos
  intro z hz
  rw [Metric.mem_ball] at hz ⊢
  have htri := dist_triangle z x y
  have hdistZero :
      dist z y < 21 * L.lamInf α + 5 * L.lamInf β := by
    nlinarith
  have hdist : dist z y < 26 * (E2 * L.lamInf β) := by
    have hbound :
        21 * L.lamInf α + 5 * L.lamInf β ≤
          26 * (E2 * L.lamInf β) := by
      nlinarith
    exact hdistZero.trans_le hbound
  calc
    dist z y < 26 * (E2 * L.lamInf β) := hdist
    _ < (205 / 2 : Real) * (E2 * L.lamInf β) := by
      apply mul_lt_mul_of_pos_right
      · norm_num
      · exact hscalePos
    _ = (item3RadiusFactor hd D / 2) * L.lamInf β := by
      rw [item3RadiusFactor, ← hE2]
      ring

/-- For a stable intersecting pair, the source sigma exponential image lies in
the target item-3 exponential image.  The hypotheses are the pointwise outputs
of the H6 origin comparison, the finite item-3 radius tail, and the half-radius
intrinsic tail. -/
theorem NetLimitData.pair_exp_maps
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (α β : Fin (pb.A r))
    (hfreq : ∃ᶠ j in atTop, BInter hd D P L.lamInf (α : Nat) (β : Nat) (L.φ j))
    (k : Nat) (hk : BInter hd D P L.lamInf (α : Nat) (β : Nat) (L.φ k))
    {x y : (X.obj (L.φ k)).M}
    (hx : seqCenter hd D P (L.φ k) (α : Nat) = some x)
    (hy : seqCenter hd D P (L.φ k) (β : Nat) = some y)
    (hrad : Item3RadiusAt (I := I) hd D P L pb r
      (item3RadiusFactor hd D) k)
    (hgp :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      (item3RadiusFactor hd D / 2) * L.lamInf (β : Nat) <
        Geometry.Riemannian.expRadiusGp
          (I := I) (X.obj (L.φ k)).metric y) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    Set.MapsTo
      (Geometry.Riemannian.NormalCoordinates.framedExpDiffeo
        (I := I) (X.obj (L.φ k)).metric x)
      (Metric.ball 0 (8 * L.lamInf (α : Nat)))
      (Geometry.Riemannian.NormalCoordinates.framedExpMap
        (I := I) (X.obj (L.φ k)).metric y ''
          Metric.ball 0 (item3RadiusFactor hd D * L.lamInf (β : Nat))) := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  have hExp :
      (1 : Real) ≤ Real.exp (hd.C * (20 * hd.lambda D 0)) := by
    rw [show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr
      (mul_nonneg hd.C_nonneg (by nlinarith [(hd.lambda_pos hD 0).le]))
  have hfactor : (8 : Real) ≤ item3RadiusFactor hd D := by
    rw [item3RadiusFactor]
    nlinarith
  have hsourceGp :
      8 * L.lamInf (α : Nat) ≤
        Geometry.Riemannian.expRadiusGp
          (I := I) (X.obj (L.φ k)).metric x := by
    calc
      8 * L.lamInf (α : Nat) ≤
          item3RadiusFactor hd D * L.lamInf (α : Nat) :=
        mul_le_mul_of_nonneg_right hfactor
          (hd.lambda_pos hD (L.rInf (α : Nat))).le
      _ ≤ Geometry.Riemannian.expRadiusGp
            (I := I) (X.obj (L.φ k)).metric x := (hrad α x hx).2
  have hsource := exp_sigma_maps (I := I) (X.obj (L.φ k))
    (P (L.φ k)).ms (P (L.φ k)).realizes x hsourceGp
  have hnest := L.sigmaBall_nesting hd hD P hfreq k hk hx hy
  have hApos : 0 < item3RadiusFactor hd D * L.lamInf (β : Nat) :=
    mul_pos (item3Factor_pos hd D) (hd.lambda_pos hD (L.rInf (β : Nat)))
  have hcoord :
      (item3RadiusFactor hd D / 2) * L.lamInf (β : Nat) <
        item3RadiusFactor hd D * L.lamInf (β : Nat) := by
    nlinarith
  have htarget := properBall_to_exp (I := I) (X.obj (L.φ k))
    (P (L.φ k)).ms (P (L.φ k)).realizes
    (c := y) (R := (item3RadiusFactor hd D / 2) * L.lamInf (β : Nat))
    (σ := item3RadiusFactor hd D * L.lamInf (β : Nat)) hgp hcoord
  intro z hz
  have hzGp : ‖z‖ < Geometry.Riemannian.expRadiusGp
      (I := I) (X.obj (L.φ k)).metric x := by
    have hz8 : ‖z‖ < 8 * L.lamInf (α : Nat) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact hz8.trans_le hsourceGp
  have hzSrc : z ∈ (Geometry.Riemannian.NormalCoordinates.framedExpDiffeo
      (I := I) (X.obj (L.φ k)).metric x).source := by
    rw [Geometry.Riemannian.NormalCoordinates.framedExp_source]
    apply Geometry.Riemannian.mem_expMapDiffeo_source_of_norm_lt_radius
      (I := I) (X.obj (L.φ k)).metric x
    apply Geometry.Riemannian.norm_lt_expMapC2Radius_of_sqrt_inner_lt
      (I := I) (X.obj (L.φ k)).metric x
    simpa only [Geometry.Riemannian.NormalCoordinates.normalFrame_sqrt] using hzGp
  rw [Geometry.Riemannian.NormalCoordinates.framedExp_eq_expMap
    (I := I) (X.obj (L.φ k)).metric x hzSrc]
  exact htarget (Metric.ball_subset_closedBall (hnest (hsource hz)))

end HCGCompactness
end DifferentialGeometry
