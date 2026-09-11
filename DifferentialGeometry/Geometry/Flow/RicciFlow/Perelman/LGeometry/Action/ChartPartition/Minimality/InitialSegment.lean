import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.TwoPieceSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.LocalMinimality

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [T2Space M] in
omit [CompactSpace M] in
theorem lChartAction_initial_pair_le_of_lRegularizedAction_minimizer
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b c d : Real) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (p q : M) (gamma : Real → M)
    (u0 : timeH1 E (b - a)) (u1 : timeH1 E (c - b))
    (u2 : timeH1 E (d - c))
    (hsrc0 : MapsTo gamma (Icc a b) (chartAt H p).source)
    (hsrc1 : MapsTo gamma (Icc b c) (chartAt H p).source)
    (hsrc2 : MapsTo gamma (Icc c d) (chartAt H q).source)
    (hrep0 : EqOn u0.toFun (fun r ↦ extChartAt I p (gamma (a + r)))
      (Icc (0 : Real) (b - a)))
    (hrep1 : EqOn u1.toFun (fun r ↦ extChartAt I p (gamma (b + r)))
      (Icc (0 : Real) (c - b)))
    (hrep2 : EqOn u2.toFun (fun r ↦ extChartAt I q (gamma (c + r)))
      (Icc (0 : Real) (d - c)))
    (hreg : ∀ s ∈ Icc a d, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta d = gamma d →
      lRegularizedAction S T gamma a d ≤ lRegularizedAction S T delta a d)
    (v0 : timeH1 E (b - a)) (v1 : timeH1 E (c - b))
    (hvtar0 : MapsTo v0.toFun (Icc (0 : Real) (b - a))
      (extChartAt I p).target)
    (hvtar1 : MapsTo v1.toFun (Icc (0 : Real) (c - b))
      (extChartAt I p).target)
    (hv0 : (extChartAt I p).symm (v0.toFun 0) = gamma a)
    (hv2 : (extChartAt I p).symm (v1.toFun (c - b)) = gamma c)
    (hvnode : (extChartAt I p).symm (v0.toFun (b - a)) =
      (extChartAt I p).symm (v1.toFun 0)) :
    lChartAction S T a p u0 + lChartAction S T b p u1 ≤
      lChartAction S T a p v0 + lChartAction S T b p v1 := by
  classical
  let th : Fin 3 → Real := ![a, b, c]
  let ph : Fin 2 → M := ![p, p]
  let vh : (i : Fin 2) → timeH1 E (partitionIntervalLength th i) :=
    Fin.cases (by simpa [th, partitionIntervalLength] using v0)
      (Fin.cases (by simpa [th, partitionIntervalLength] using v1) (fun i ↦ Fin.elim0 i))
  have hvh0 : vh (0 : Fin 2) = v0 := by rfl
  have hvh1 : vh (1 : Fin 2) = v1 := by
    change vh ((0 : Fin 1).succ) = v1
    rfl
  have hth : Monotone th := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i
    · simpa [th] using hab
    · simpa [th] using hbc
  have hvhtar : ∀ i, MapsTo (vh i).toFun
      (Icc (0 : Real) (partitionIntervalLength th i)) (extChartAt I (ph i)).target := by
    intro i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) i
    · change MapsTo (vh 0).toFun
        (Icc (0 : Real) (partitionIntervalLength th 0)) (extChartAt I (ph 0)).target
      rw [hvh0]
      simpa [th, ph, partitionIntervalLength] using hvtar0
    · change MapsTo (vh 1).toFun
        (Icc (0 : Real) (partitionIntervalLength th 1)) (extChartAt I (ph 1)).target
      rw [hvh1]
      simpa [th, ph, partitionIntervalLength] using hvtar1
  have hvhnode : (extChartAt I (ph 0)).symm
        ((vh 0).toFun (partitionIntervalLength th 0)) =
      (extChartAt I (ph 1)).symm ((vh 1).toFun 0) := by
    rw [hvh0, hvh1]
    simpa [th, ph, partitionIntervalLength] using hvnode
  have hregHead : ∀ s ∈ Icc (th 0) (th (Fin.last 2)),
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hreg s
    exact ⟨hs.1, hs.2.trans hcd⟩
  obtain ⟨gammaV, _hgammaV, hsrcV, hrepV, hV0, hV2, alpha, _w,
      halpha, halpha0, halpha2, _hsrcA, _hrepA, _hw, _huniform, hact⟩ :=
    exists_contMDiff_one_lRegularizedAction_approximation_of_compatible_chartH1_pair (I := I) S hMet hSc T th hth ph vh hvhtar hvhnode
      hregHead
  have hjoin : gammaV c = gamma c := by
    exact hV2.trans (by
      rw [hvh1]
      simpa [th, ph, partitionIntervalLength] using hv2)
  let delta : Real → M := Set.piecewise (Iic c) gammaV gamma
  have hdelta_head {s : Real} (hs : s ≤ c) : delta s = gammaV s :=
    (Iic c).piecewise_eq_of_mem gammaV gamma hs
  have hdelta_tail {s : Real} (hs : c ≤ s) : delta s = gamma s := by
    rcases hs.eq_or_lt with rfl | hcs
    · exact (hdelta_head le_rfl).trans hjoin
    · exact (Iic c).piecewise_eq_of_notMem gammaV gamma (not_le.mpr hcs)
  let tf : Fin 4 → Real := ![a, b, c, d]
  let pf : Fin 3 → M := ![p, p, q]
  let uf : (i : Fin 3) → timeH1 E (partitionIntervalLength tf i) :=
    Fin.cases (by simpa [tf, partitionIntervalLength] using u0)
      (Fin.cases (by simpa [tf, partitionIntervalLength] using u1)
        (Fin.cases (by simpa [tf, partitionIntervalLength] using u2) (fun i ↦ Fin.elim0 i)))
  let vf : (i : Fin 3) → timeH1 E (partitionIntervalLength tf i) :=
    Fin.cases (by simpa [tf, partitionIntervalLength] using v0)
      (Fin.cases (by simpa [tf, partitionIntervalLength] using v1)
        (Fin.cases (by simpa [tf, partitionIntervalLength] using u2) (fun i ↦ Fin.elim0 i)))
  have huf0 : uf (0 : Fin 3) = u0 := by rfl
  have huf1 : uf (1 : Fin 3) = u1 := by
    change uf ((0 : Fin 2).succ) = u1
    rfl
  have huf2 : uf (2 : Fin 3) = u2 := by
    change uf (((0 : Fin 1).succ).succ) = u2
    rfl
  have hvf0 : vf (0 : Fin 3) = v0 := by rfl
  have hvf1 : vf (1 : Fin 3) = v1 := by
    change vf ((0 : Fin 2).succ) = v1
    rfl
  have hvf2 : vf (2 : Fin 3) = u2 := by
    change vf (((0 : Fin 1).succ).succ) = u2
    rfl
  have htf : Monotone tf := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i
    · simpa [tf] using hab
    · simpa [tf] using hbc
    · simpa [tf] using hcd
  have hsrcBase : ∀ i, MapsTo gamma
      (Icc (tf i.castSucc) (tf i.succ)) (chartAt H (pf i)).source := by
    intro i
    fin_cases i
    · simpa [tf, pf] using hsrc0
    · simpa [tf, pf] using hsrc1
    · simpa [tf, pf] using hsrc2
  have hrepBase : ∀ i, EqOn (uf i).toFun
      (fun r ↦ extChartAt I (pf i) (gamma (tf i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength tf i)) := by
    intro i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_
      (fun k ↦ Fin.cases ?_ (fun l ↦ Fin.elim0 l) k) j) i
    · change EqOn (uf 0).toFun
        (fun r ↦ extChartAt I (pf 0) (gamma (tf 0 + r)))
        (Icc (0 : Real) (partitionIntervalLength tf 0))
      rw [huf0]
      simpa [tf, pf, partitionIntervalLength] using hrep0
    · change EqOn (uf 1).toFun
        (fun r ↦ extChartAt I (pf 1) (gamma (tf 1 + r)))
        (Icc (0 : Real) (partitionIntervalLength tf 1))
      rw [huf1]
      simpa [tf, pf, partitionIntervalLength] using hrep1
    · change EqOn (uf 2).toFun
        (fun r ↦ extChartAt I (pf 2) (gamma (tf 2 + r)))
        (Icc (0 : Real) (partitionIntervalLength tf 2))
      rw [huf2]
      simpa [tf, pf, partitionIntervalLength] using hrep2
  have hsrcDelta : ∀ i, MapsTo delta
      (Icc (tf i.castSucc) (tf i.succ)) (chartAt H (pf i)).source := by
    intro i s hs
    fin_cases i
    · rw [hdelta_head (hs.2.trans hbc)]
      exact hsrcV 0 (by simpa [th, tf] using hs)
    · rw [hdelta_head hs.2]
      exact hsrcV 1 (by simpa [th, tf] using hs)
    · rw [hdelta_tail hs.1]
      exact hsrc2 (by simpa [tf, pf] using hs)
  have hrepDelta : ∀ i, EqOn (vf i).toFun
      (fun r ↦ extChartAt I (pf i) (delta (tf i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength tf i)) := by
    intro i r hr
    fin_cases i
    · change v0.toFun r = extChartAt I p (delta (a + r))
      have hrh : r ∈ Icc (0 : Real) (b - a) := by
        simpa [tf, partitionIntervalLength] using hr
      rw [hdelta_head (by linarith [hrh.2, hbc])]
      have h := hrepV 0 hrh
      rw [hvh0] at h
      simpa [th, ph, partitionIntervalLength] using h
    · change v1.toFun r = extChartAt I p (delta (b + r))
      have hrh : r ∈ Icc (0 : Real) (c - b) := by
        simpa [tf, partitionIntervalLength] using hr
      rw [hdelta_head (by linarith [hrh.2])]
      have h := hrepV 1 hrh
      rw [hvh1] at h
      simpa [th, ph, partitionIntervalLength] using h
    · change u2.toFun r = extChartAt I q (delta (c + r))
      have hrt : r ∈ Icc (0 : Real) (d - c) := by
        simpa [tf, partitionIntervalLength] using hr
      rw [hdelta_tail (by linarith [hrt.1])]
      exact hrep2 hrt
  obtain ⟨beta, _z, hbeta, hbeta0, hbeta3, _hsrcB, _hrepB, _hz, _huniformB,
      hactB⟩ :=
    lAction_c1_dense (I := I) S hMet hSc T a d tf htf rfl rfl pf delta
      vf hsrcDelta hrepDelta hreg
  have hneg : Tendsto (fun n ↦ -lRegularizedAction S T (beta n) a d) atTop
      (nhds (-lRegularizedAction S T delta a d)) :=
    continuousAt_neg.tendsto.comp hactB
  have hdelta0 : delta a = gamma a :=
    (hdelta_head (hab.trans hbc)).trans
      (hV0.trans (by
        rw [hvh0]
        simpa [th, ph, partitionIntervalLength] using hv0))
  have hdelta3 : delta d = gamma d := hdelta_tail hcd
  have hglobal : lRegularizedAction S T gamma a d ≤ lRegularizedAction S T delta a d := by
    have hlim := le_of_tendsto' hneg fun n ↦ neg_le_neg
      (hmin (beta n) (hbeta n) ((hbeta0 n).trans hdelta0)
        ((hbeta3 n).trans hdelta3))
    linarith
  rw [lRegularizedAction_eq_sum_lChartAction S hMet hSc T a d tf htf rfl rfl pf gamma uf
    hsrcBase hrepBase hreg] at hglobal
  rw [lRegularizedAction_eq_sum_lChartAction S hMet hSc T a d tf htf rfl rfl pf delta vf
    hsrcDelta hrepDelta hreg] at hglobal
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at hglobal
  rw [huf0, huf1, huf2, hvf0, hvf1, hvf2] at hglobal
  have hhead := (add_le_add_iff_right
    (lChartAction S T (tf (Fin.castSucc (2 : Fin 3))) (pf 2) u2)).mp hglobal
  have htf0 : tf (Fin.castSucc (0 : Fin 3)) = a := by rfl
  have htf1 : tf (Fin.castSucc (1 : Fin 3)) = b := by rfl
  have hpf0 : pf (0 : Fin 3) = p := by rfl
  have hpf1 : pf (1 : Fin 3) = p := by rfl
  rw [htf0, htf1, hpf0, hpf1] at hhead
  exact hhead

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
