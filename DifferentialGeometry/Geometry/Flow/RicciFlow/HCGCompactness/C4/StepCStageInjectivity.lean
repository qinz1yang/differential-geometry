import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCSourceBuffer
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageReturn

set_option autoImplicit false

/-!
# Global injectivity of the finite-stage comparison maps

The proof combines the uniform intrinsic source buffer with the independently
constructed reverse-stage approximate return map.  If two source points have
the same forward image, return closeness puts them in one buffered normal
chart.  The coordinate segment between them remains in a slightly larger
source ball, where the order-one stage-map jet estimate gives injectivity.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Filter Topology Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- With the same explicit construction-radius room used by the approximate
return theorem, the actual global comparison maps are eventually injective on
the smaller retained source ball. -/
theorem HasStageJetData.inj_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {s : Real} (hs : 0 ≤ s)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hcomplete : ∀ j, MetricComplete (I := I) (X.obj j))
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack s → Set E)
    (aInf : (alpha : LiveSlot L inp.pack s) →
      Fin (inp.pack.A s) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack s) →
      InterSlot L inp.pack s alpha → E → E)
    (gInf : LiveSlot L inp.pack s →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hs phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    (R0 R1 : Real)
    (hroom : R0 + (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 < R1)
    (hR1s : R1 < s) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      Set.InjOn (stageComparisonMap inp P Lphi s hs hconn k l)
        (Lphi.hatSourceBall inp.decay P R0 k) := by
  classical
  have hstage0 := hstage
  rcases hstage with ⟨hdata, _hmetric, hjets, _hbase⟩
  have hlam0 : 0 < inp.decay.lambda inp.D 0 :=
    inp.decay.lambda_pos inp.hD 0
  have hcoef : 0 <
      (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 := by positivity
  have hR0R1 : R0 < R1 := by linarith
  have hR0s : R0 < s := hR0R1.trans hR1s
  obtain ⟨rho0, hrho0, hbuffer⟩ :=
    hdata.metric_buffer inp P L s hs U C0 C1 aInf Jinf Jbarinf
      hcomplete hconn
  let rho : Real := min rho0 (R1 - R0)
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact lt_min hrho0 (sub_pos.mpr hR0R1)
  have hrho_le : rho ≤ rho0 := min_le_left _ _
  have hrho_room : rho ≤ R1 - R0 := min_le_right _ _
  obtain ⟨Nret, hret⟩ := hstage0.return_tail inp P L hs phi hphi
    hconn U C0 C1 aInf Jinf Jbarinf gInf R0 R1 hroom hR1s
      (rho / 4) (div_pos hrho (by norm_num))
  obtain ⟨Njet, hjet⟩ := hjets R1 hR1s 1 (1 / 2 : Real) (by norm_num)
  refine ⟨max Nret Njet, ?_⟩
  intro k hk l hl
  have hkRet : Nret ≤ k := (le_max_left _ _).trans hk
  have hlRet : Nret ≤ l := (le_max_left _ _).trans hl
  have hkJet : Njet ≤ k := (le_max_right _ _).trans hk
  have hlJet : Njet ≤ l := (le_max_right _ _).trans hl
  dsimp only
  let Lphi := L.subseq hphi
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : T2Space Yl.M := Yl.t2
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
  let F := stageComparisonMap inp P Lphi s hs hconn k l
  let Hret := stageComparisonMap inp P Lphi s hs hconn l k
  intro x hx y hy hFxy
  have hFxy' : F x = F y := by
    simpa only [F] using hFxy
  have hretx := hret k l hkRet hlRet x hx
  have hrety := hret k l hkRet hlRet y hy
  have hxyHalf : dist y x < rho / 2 := by
    calc
      dist y x ≤ dist y (Hret (F y)) + dist (Hret (F y)) x :=
        dist_triangle _ _ _
      _ = dist (Hret (F y)) y + dist (Hret (F x)) x := by
        rw [dist_comm y (Hret (F y)), hFxy']
      _ < rho / 4 + rho / 4 := by
        simpa only [F, Hret] using add_lt_add hrety hretx
      _ = rho / 2 := by ring
  have hxy : dist y x < rho0 :=
    hxyHalf.trans_le (by linarith [hrho, hrho_le])
  have hxLarge : x ∈ Lphi.hatSourceBall inp.decay P s k :=
    cball_subset_of_le hR0s.le hx
  obtain ⟨alpha, z, hzx, hball, hcoord⟩ := hbuffer k x hxLarge
  let ck := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let cl := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric ck
  let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric cl
  have hxBall : x ∈ Metric.ball x rho0 := Metric.mem_ball_self hrho0
  have hyBall : y ∈ Metric.ball x rho0 := by
    simpa only [Metric.mem_ball] using hxy
  obtain ⟨zx, hzxInt, hzxEq⟩ := hball hxBall
  obtain ⟨zy, hzyInt, hzyEq⟩ := hball hyBall
  obtain ⟨_hUopen, _hC0compact, _hC1compact, hC01, hC1U⟩ :=
    hdata.core_on inp P L s hs U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨hconv, _hzero⟩ :=
    hdata.core_shape inp P L s hs U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨hUmetric, hUexp, _hUmap⟩ :=
    hdata.geom_on inp P L s hs U C0 C1 aInf Jinf Jbarinf k alpha
  have hIntU : interior (C0 alpha) ⊆ U alpha :=
    interior_subset.trans (hC01.trans interior_subset |>.trans hC1U)
  have hUtgt : U alpha ⊆ chiK.target := by
    intro w hw
    have hwBall := hUexp hw
    rw [Metric.mem_ball, dist_zero_right] at hwBall
    change w ∈ (NormalCoordinates.framedExpDiffeo
      (I := I) Yk.metric ck).source
    rw [NormalCoordinates.framedExp_source]
    apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Yk.metric ck
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Yk.metric ck
    simpa only [NormalCoordinates.normalFrame_sqrt] using hwBall
  have hchiX : chiK x = zx := by
    rw [← hzxEq]
    exact chiK.right_inv (hUtgt (hIntU hzxInt))
  have hchiY : chiK y = zy := by
    rw [← hzyEq]
    exact chiK.right_inv (hUtgt (hIntU hzyInt))
  have hcoordX0 := hcoord x hxBall
  rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (Lphi.φ k) x x,
      dist_self, mul_zero] at hcoordX0
  have hcoordX0' : dist (chiK x) z ≤ 0 := by
    simpa only [chiK, ck, Yk, Lphi] using hcoordX0
  have hzxCoord : zx = z := by
    apply dist_le_zero.mp
    simpa only [hchiX] using hcoordX0'
  have hcoordY0 := hcoord y hyBall
  rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (Lphi.φ k) y x]
      at hcoordY0
  have hcoordYX : dist zy zx ≤ Real.sqrt 2 * dist y x := by
    rw [hzxCoord]
    simpa only [chiK, ck, Yk, Lphi, hchiY] using hcoordY0
  have hequiv : NormalCoordMetricEquivOn (I := I) Yk ck (U alpha) := by
    intro w hw v
    exact inp.normalBounds.metric_equiv (Lphi.φ k) ck w (hUmetric hw) v
  let G : E → E := fun w ↦ chiL (F (chiK.symm w))
  have hsegInt : segment Real zx zy ⊆ interior (C0 alpha) :=
    hconv.interior.segment_subset hzxInt hzyInt
  have hsegR1 : ∀ w ∈ segment Real zx zy, chiK.symm w ∈
      Lphi.hatSourceBall inp.decay P R1 k := by
    intro w hw
    have hwInt := hsegInt hw
    have hwClosed : w ∈ Metric.closedBall zx (dist zx zy) :=
      segment_subset_closedBall_left zx zy hw
    have hwCoord : dist w zx ≤ dist zx zy := Metric.mem_closedBall.mp hwClosed
    have hsegU : segment Real w zx ⊆ U alpha := by
      intro q hq
      exact hIntU (hconv.interior.segment_subset hwInt hzxInt hq)
    have hsymm := NormalCoordMetricEquivOn.symm_dist_le
      (I := I) Yk (P (Lphi.φ k)) hequiv hUtgt hsegU
    have hlocal : dist (chiK.symm w) x < rho := by
      rw [← hzxEq]
      calc
        dist (chiK.symm w) (chiK.symm zx) ≤
            Real.sqrt 2 * dist w zx := by
          simpa only [chiK] using hsymm
        _ ≤ Real.sqrt 2 * dist zx zy := by gcongr
        _ ≤ Real.sqrt 2 * (Real.sqrt 2 * dist y x) := by
          gcongr
          simpa only [dist_comm] using hcoordYX
        _ = 2 * dist y x := by
          rw [← mul_assoc, Real.mul_self_sqrt (by norm_num : (0 : Real) ≤ 2)]
        _ < rho := by linarith
    rw [NetLimitData.hatSourceBall, Metric.mem_closedBall]
    have hxR0 : dist x Yk.basepoint ≤ R0 := by
      simpa only [NetLimitData.hatSourceBall, Yk] using hx
    have hlt : dist (chiK.symm w) Yk.basepoint < R1 := by
      calc
        dist (chiK.symm w) Yk.basepoint ≤
            dist (chiK.symm w) x + dist x Yk.basepoint := dist_triangle _ _ _
        _ < rho + R0 := add_lt_add_of_lt_of_le hlocal hxR0
        _ ≤ R1 := by linarith
    exact hlt.le
  have hsegDiff : ∀ w ∈ segment Real zx zy, DifferentiableAt Real G w := by
    intro w hw
    have hwInt := hsegInt hw
    have hwR1 := hsegR1 w hw
    have hout := hjet k hkJet l hlJet alpha w
      (interior_subset hwInt) hwInt hwR1
    exact (by simpa only [G, F, chiK, chiL, ck, cl, Yk, Yl, Lphi] using
      hout.2.1.differentiableAt (by simp))
  have hsegBd : ∀ w ∈ segment Real zx zy,
      ‖ContinuousLinearMap.id Real E - fderiv Real G w‖ ≤ (1 / 2 : Real) := by
    intro w hw
    have hwInt := hsegInt hw
    have hwR1 := hsegR1 w hw
    have hout := hjet k hkJet l hlJet alpha w
      (interior_subset hwInt) hwInt hwR1
    have hdiff : DifferentiableAt Real G w := hsegDiff w hw
    have hraw : mapDerivNorm 1 G id w ≤ (1 / 2 : Real) := by
      simpa only [G, F, chiK, chiL, ck, cl, Yk, Yl, Lphi] using
        hout.2.2 1 le_rfl
    exact neumannOfDerivNorm hdiff hraw
  have hGinj : Set.InjOn G (segment Real zx zy) :=
    Coordinates.injOn_of_fderiv_near_id (convex_segment zx zy)
      (by norm_num) hsegDiff hsegBd
  have hGxy : G zx = G zy := by
    dsimp only [G]
    rw [hzxEq, hzyEq, hFxy']
  have hzyeq : zx = zy :=
    hGinj (left_mem_segment Real zx zy) (right_mem_segment Real zx zy) hGxy
  calc
    x = chiK.symm zx := hzxEq.symm
    _ = chiK.symm zy := congrArg chiK.symm hzyeq
    _ = y := hzyEq

end HCGCompactness
end DifferentialGeometry
