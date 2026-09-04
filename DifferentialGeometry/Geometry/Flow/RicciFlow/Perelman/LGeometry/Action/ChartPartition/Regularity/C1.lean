import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Matching.VelocityAtNodes
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Regularity.PiecewiseC1
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Curve.FiniteManifoldC1Gluing

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Function Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [CompactSpace M] in
private theorem lRegularizedAction_minimizer_contMDiffOn_one_of_chart_partition_aux
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 3) → Real)
    (ht0 : t 0 = a) (htlast : t (Fin.last (m + 2)) = b)
    (p : Fin (m + 2) → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (k : Fin (m + 2)) → timeH1 E (partitionIntervalLength t k))
    (hpos : ∀ k : Fin (m + 2), t k.castSucc < t k.succ)
    (hsrc : ∀ k, MapsTo gamma
      (Icc (t k.castSucc) (t k.succ)) (chartAt H (p k)).source)
    (hrep : ∀ k, EqOn (u k).toFun
      (fun r ↦ extChartAt I (p k) (gamma (t k.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t k)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b) :
    ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma (Icc a b) := by
  classical
  have ht : StrictMono t := by
    rw [Fin.strictMono_iff_lt_succ]
    exact hpos
  have huC1 : ∀ i, ContDiffOn Real 1 (u i).toFun
      (Icc (0 : Real) (partitionIntervalLength t i)) :=
    lRegularizedAction_minimizer_chart_piece_contDiffOn_one (I := I) S hS T a b t ht ht0 htlast p gamma hgamma
      u hsrc hrep hreg hmin
  have hpieceFin (i : Fin (m + 2)) :
      ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
        (Icc (t i.castSucc) (t i.succ)) :=
    curve_c1_local I (p i) gamma (u i) (hsrc i) (hrep i) (huC1 i)
  let tn : Nat → Real := fun k ↦
    if hk : k < m + 3 then t ⟨k, hk⟩ else b
  have htn (k : Nat) (hk : k < m + 3) : tn k = t ⟨k, hk⟩ := by
    simp only [tn, dif_pos hk]
  have htNat : ∀ k, k < m + 2 → tn k < tn (k + 1) := by
    intro k hk
    let i : Fin (m + 2) := ⟨k, hk⟩
    have hi0 : tn k = t i.castSucc := by
      rw [htn k (by omega)]
      congr 1
    have hi1 : tn (k + 1) = t i.succ := by
      rw [htn (k + 1) (by omega)]
      congr 1
    rw [hi0, hi1]
    exact hpos i
  have hpieceNat : ∀ k, k < m + 2 →
      ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
        (Icc (tn k) (tn (k + 1))) := by
    intro k hk
    let i : Fin (m + 2) := ⟨k, hk⟩
    have hi0 : tn k = t i.castSucc := by
      rw [htn k (by omega)]
      congr 1
    have hi1 : tn (k + 1) = t i.succ := by
      rw [htn (k + 1) (by omega)]
      congr 1
    rw [hi0, hi1]
    exact hpieceFin i
  have hnodeNat : ∀ k, 0 < k → k < m + 2 →
      derivWithin ((extChartAt I (gamma (tn k))) ∘ gamma)
          (Icc (tn (k - 1)) (tn k)) (tn k) =
        derivWithin ((extChartAt I (gamma (tn k))) ∘ gamma)
          (Icc (tn k) (tn (k + 1))) (tn k) := by
    intro k hk0 hk
    let q : Fin (m + 1) := ⟨k - 1, by omega⟩
    let i : Fin (m + 2) := q.castSucc
    let j : Fin (m + 2) := q.succ
    have hij : i.succ = j.castSucc := rfl
    have hprev : tn (k - 1) = t i.castSucc := by
      rw [htn (k - 1) (by omega)]
      congr 1
    have hnode : tn k = t j.castSucc := by
      rw [htn k (by omega)]
      congr 1
      apply Fin.ext
      simp only [j, q, Fin.val_castSucc, Fin.val_succ]
      omega
    have hnext : tn (k + 1) = t j.succ := by
      rw [htn (k + 1) (by omega)]
      congr 1
      apply Fin.ext
      simp only [j, q, Fin.val_succ]
      omega
    rw [hprev, hnode, hnext]
    have hpos0 : t i.castSucc < t i.succ := hpos i
    have hpos1 : t j.castSucc < t j.succ := hpos j
    have hgamma0 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
        (Icc (t i.castSucc) (t j.castSucc)) := by
      simpa only [hij] using hpieceFin i
    have hgamma1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
        (Icc (t j.castSucc) (t j.succ)) := hpieceFin j
    have hp0der : derivWithin ((extChartAt I (p i)) ∘ gamma)
          (Icc (t i.castSucc) (t j.castSucc)) (t j.castSucc) =
        derivWithin (u i).toFun
          (Icc (0 : Real) (partitionIntervalLength t i)) (partitionIntervalLength t i) := by
      have hshift := chartDeriv_shift
        (a := t i.castSucc) (b := t i.succ) (r := partitionIntervalLength t i)
        ((extChartAt I (p i)) ∘ gamma) (u i)
        (by
          intro r hr
          change (u i).toFun r = extChartAt I (p i)
            (gamma (t i.castSucc + r))
          exact hrep i (by simpa only [partitionIntervalLength] using hr))
        ⟨by simpa only [partitionIntervalLength] using sub_nonneg.mpr hpos0.le, le_rfl⟩
      simpa only [hij, partitionIntervalLength, add_sub_cancel] using hshift
    have hp1der : derivWithin ((extChartAt I (p j)) ∘ gamma)
          (Icc (t j.castSucc) (t j.succ)) (t j.castSucc) =
        derivWithin (u j).toFun (Icc (0 : Real) (partitionIntervalLength t j)) 0 := by
      have hshift := chartDeriv_shift
        (a := t j.castSucc) (b := t j.succ) (r := 0)
        ((extChartAt I (p j)) ∘ gamma) (u j)
        (by
          intro r hr
          change (u j).toFun r = extChartAt I (p j)
            (gamma (t j.castSucc + r))
          exact hrep j (by simpa only [partitionIntervalLength] using hr))
        ⟨le_rfl, by simpa only [partitionIntervalLength] using sub_nonneg.mpr hpos1.le⟩
      change derivWithin ((extChartAt I (p j)) ∘ gamma)
          (Icc (t j.castSucc) (t j.succ)) (t j.castSucc) =
        derivWithin (u j).toFun
          (Icc (0 : Real) (t j.succ - t j.castSucc)) 0
      convert hshift using 1
      · simp only [add_zero]
      · rfl
    have hp0src : gamma (t j.castSucc) ∈ (chartAt H (p i)).source := by
      apply hsrc i
      rw [← hij]
      exact ⟨hpos0.le, le_rfl⟩
    have hp1src : gamma (t j.castSucc) ∈ (chartAt H (p j)).source :=
      hsrc j ⟨le_rfl, hpos1.le⟩
    have hnodesrc : gamma (t j.castSucc) ∈
        (chartAt H (gamma (t j.castSucc))).source :=
      mem_chart_source H (gamma (t j.castSucc))
    have hp0ext : gamma (t j.castSucc) ∈ (extChartAt I (p i)).source := by
      rw [extChartAt_source]
      exact hp0src
    have hp1ext : gamma (t j.castSucc) ∈ (extChartAt I (p j)).source := by
      rw [extChartAt_source]
      exact hp1src
    have hnodeext : gamma (t j.castSucc) ∈
        (extChartAt I (gamma (t j.castSucc))).source := by
      rw [extChartAt_source]
      exact hnodesrc
    have hchange0 := chartDeriv_change I (p i) (gamma (t j.castSucc)) gamma
      hgamma0 ⟨by rw [← hij]; exact hpos0.le, le_rfl⟩
      (uniqueDiffOn_Icc (by simpa only [hij] using hpos0)
        (t j.castSucc) ⟨by rw [← hij]; exact hpos0.le, le_rfl⟩)
      (by simpa only [hij] using hsrc i) hnodesrc
    have hchange1 := chartDeriv_change I (p j) (gamma (t j.castSucc)) gamma
      hgamma1 ⟨le_rfl, hpos1.le⟩
      (uniqueDiffOn_Icc hpos1 (t j.castSucc) ⟨le_rfl, hpos1.le⟩)
      (hsrc j) hnodesrc
    have hvel : tangentCoordChange I (p i) (p j) (gamma (t j.castSucc))
          (derivWithin (u i).toFun
            (Icc (0 : Real) (partitionIntervalLength t i)) (partitionIntervalLength t i)) =
        derivWithin (u j).toFun (Icc (0 : Real) (partitionIntervalLength t j)) 0 := by
      simpa only [i, j] using
        lRegularizedAction_minimizer_velocity_eq_at_partition_nodes (I := I) S hS T a b t ht0 htlast p gamma hgamma u
          hpos hsrc hrep hreg hmin q
    rw [hchange0, hchange1, hp0der, hp1der, ← hvel]
    exact (tangentCoordChange_comp (I := I) (w := p i) (x := p j)
      (y := gamma (t j.castSucc)) (z := gamma (t j.castSucc))
      ⟨⟨hp0ext, hp1ext⟩, hnodeext⟩).symm
  have hfull := curve_c1_fin (I := I) (gamma := gamma) (t := tn)
    (m := m + 2) (by omega) htNat hpieceNat hnodeNat
  have htn0 : tn 0 = a := by
    rw [htn 0 (by omega)]
    exact ht0
  have htnlast : tn (m + 2) = b := by
    rw [htn (m + 2) (by omega)]
    rw [← htlast]
    congr 1
  simpa only [htn0, htnlast] using hfull

omit [CompactSpace M] in
theorem lRegularizedAction_minimizer_contMDiffOn_one_of_chart_partition
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) {m : Nat} (hm : 0 < m) (t : Fin (m + 1) → Real)
    (ht0 : t 0 = a) (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (k : Fin m) → timeH1 E (partitionIntervalLength t k))
    (hpos : ∀ k : Fin m, t k.castSucc < t k.succ)
    (hsrc : ∀ k, MapsTo gamma
      (Icc (t k.castSucc) (t k.succ)) (chartAt H (p k)).source)
    (hrep : ∀ k, EqOn (u k).toFun
      (fun r ↦ extChartAt I (p k) (gamma (t k.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t k)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b) :
    ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma (Icc a b) := by
  classical
  cases m with
  | zero => omega
  | succ n =>
      cases n with
      | zero =>
          have ht : StrictMono t := by
            rw [Fin.strictMono_iff_lt_succ]
            exact hpos
          have huC1 := lRegularizedAction_minimizer_chart_piece_contDiffOn_one (I := I) S hS T a b t ht ht0
            htlast p gamma hgamma u hsrc hrep hreg hmin (0 : Fin 1)
          have hpiece := curve_c1_local I (p 0) gamma (u 0) (hsrc 0)
            (hrep 0) huC1
          have hleft : t (0 : Fin 1).castSucc = a := by
            rw [show (0 : Fin 1).castSucc = (0 : Fin 2) by ext; rfl]
            exact ht0
          have hright : t (0 : Fin 1).succ = b := by
            rw [show (0 : Fin 1).succ = Fin.last 1 by ext; rfl]
            exact htlast
          simpa only [hleft, hright] using hpiece
      | succ n =>
          exact lRegularizedAction_minimizer_contMDiffOn_one_of_chart_partition_aux (I := I) S hS T a b t ht0 htlast p gamma
            hgamma u hpos hsrc hrep hreg hmin

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
