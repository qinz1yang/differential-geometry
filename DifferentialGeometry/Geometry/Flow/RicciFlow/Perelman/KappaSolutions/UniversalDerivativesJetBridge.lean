import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MixedCurvatureJet
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RiemannFromRicci


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff

universe u uE uH


private def curvEquiv : (m : ℕ) → Fin (4 + m) ≃ Fin (m + 4)
  | 0 => Equiv.refl _
  | (m + 1) => frontExtendEquiv (curvEquiv m)

section TowerBridge

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

private local instance towerBridgeC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

private local instance towerBridgeC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem curv_apply_iterCov (g : SmoothRiemannianMetric I M) :
    ∀ (m : ℕ) (x : M) (v : Fin (m + 4) → TangentSpace I x),
      curvCovDeriv (I := I) (M := M) g m x v =
        (ContinuousMultilinearMap.domDomCongr (curvEquiv m)
          ((iterCov (I := I) g 4
            (DifferentialGeometry.Geometry.Curvature.metricRm04
              (I := I) (M := M) g) m) x)) v := by
  intro m
  induction m with
  | zero =>
      intro x v
      rfl
  | succ m ih =>
      intro x v
      have hfield :
          curvCovDeriv (I := I) (M := M) g m =
            MultilinearSection.domDomCongr
              (𝕜 := ℝ) (F := E) (IB := I) (E := TangentSpace I)
              (∞ : WithTop ℕ∞) (curvEquiv m)
              (iterCov (I := I) g 4
                (DifferentialGeometry.Geometry.Curvature.metricRm04
                  (I := I) (M := M) g) m) := by
        refine DFunLike.ext _ _ (fun y => ?_)
        refine ContinuousMultilinearMap.ext (fun w => ?_)
        exact ih y w
      calc
        curvCovDeriv (I := I) (M := M) g (m + 1) x v =
            curvCovDerivStep (I := I) g m
              (curvCovDeriv (I := I) (M := M) g m) x v :=
          congrArg (fun A => A x v)
            (curvCovDeriv_succ (I := I) (M := M) g m)
        _ = covStep (I := I) g (m + 4)
              (curvCovDeriv (I := I) (M := M) g m) x v :=
          congrArg (fun A => A x v)
            (curvStep_eq_covStep (I := I) (M := M) g m _)
        _ = covStep (I := I) g (m + 4)
              (MultilinearSection.domDomCongr
                (𝕜 := ℝ) (F := E) (IB := I) (E := TangentSpace I)
                (∞ : WithTop ℕ∞) (curvEquiv m)
                (iterCov (I := I) g 4
                  (DifferentialGeometry.Geometry.Curvature.metricRm04
                    (I := I) (M := M) g) m)) x v :=
          congrArg (fun A => covStep (I := I) g (m + 4) A x v) hfield
        _ = (MultilinearSection.domDomCongr
              (𝕜 := ℝ) (F := E) (IB := I) (E := TangentSpace I)
              (∞ : WithTop ℕ∞) (frontExtendEquiv (curvEquiv m))
              (covStep (I := I) g (4 + m)
                (iterCov (I := I) g 4
                  (DifferentialGeometry.Geometry.Curvature.metricRm04
                    (I := I) (M := M) g) m))) x v :=
          congrArg (fun A => A x v)
            (covStep_domDomCongr (I := I) g (curvEquiv m) _)
        _ = (ContinuousMultilinearMap.domDomCongr (curvEquiv (m + 1))
              ((iterCov (I := I) g 4
                (DifferentialGeometry.Geometry.Curvature.metricRm04
                  (I := I) (M := M) g) (m + 1)) x)) v := by
          rfl

end TowerBridge


section RicciEnd

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [BoundarylessManifold I M]


theorem ricciEndAt_metricRicciAt_eq_ricciSharp
    (g : SmoothRiemannianMetric I M) (x : M) (w : TangentSpace I x) :
    ricciEndAt (I := I) g (metricRicciAt (I := I) g x) w = ricciSharp (I := I) g x w := by
  refine SmoothRiemannianMetric.eq_of_inner_eq_gen g (fun z => ?_)
  rw [ricciEnd_inner (I := I) g (metricRicciAt (I := I) g x) w z,
    metricRicciAt_apply_eq_ricciTensor (I := I) g x w z,
    inner_ricciSharp (I := I) g x w z]

end RicciEnd


section Bridge

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

private theorem bridgeThreeSpaceFinrank : Module.finrank ℝ ThreeSpace = 3 := by
  simp [ThreeSpace]

private local instance bridgeThreeSpaceNeZero : NeZero (Module.finrank ℝ ThreeSpace) :=
  ⟨by rw [bridgeThreeSpaceFinrank]; norm_num⟩

private local instance bridgeC1 : IsManifold I3 1 M :=
  IsManifold.of_le (I := I3) (M := M) (n := ∞) (by decide)

private local instance bridgeC2 : IsManifold I3 2 M :=
  IsManifold.of_le (I := I3) (M := M) (n := ∞) (by decide)

omit [SigmaCompactSpace M] in
theorem exists_slotEquiv_mixedCurvatureJet_value
    (S : SolutionOn (I := I3) (M := M) ancientTimeInterval)
    (J : MixedCurvatureJet S) (a : ℕ) (x : M)
    (hdiff : ∀ (q : ℕ) (t : ℝ), t ≤ 0 →
      DifferentiableWithinAt ℝ (fun s : ℝ => mixedCurvatureTensor S a q s x) (Iic 0) t) :
    ∃ e : Fin (4 + a) ≃ Fin (a + 4), ∀ (b : ℕ) (t : ℝ), t ≤ 0 →
      ∀ v : Fin (a + 4) → TangentSpace I3 x,
        J.value a b t x v = mixedCurvatureTensor S a b t x (v ∘ e) := by
  classical
  refine ⟨curvEquiv a, ?_⟩
  intro b
  induction b with
  | zero =>
      intro t _ v
      have hspat : J.value a 0 t x v = curvCovDeriv (I := I3) (M := M) (S.base.metric t) a x v :=
        congrArg (fun A => A x v) (J.spatial a t)
      have hiter := curv_apply_iterCov (I := I3) (M := M) (S.base.metric t) a x v
      have hnabla : nablaKRm04Field (I := I3) S t a =
          iterCov (I := I3) (S.base.metric t) 4 (S.base.rm04 t) a :=
        nablaKRm_eq_iterCov (I := I3) S t a
      rw [hspat, hiter]
      change (iterCov (I := I3) (S.base.metric t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04 (I := I3) (M := M)
          (S.base.metric t)) a x) (v ∘ curvEquiv a) = _
      rw [mixedCurvatureTensor_zero]
      exact congrArg (fun A => A x (v ∘ curvEquiv a)) hnabla.symm
  | succ b ih =>
      intro t ht v
      set e := curvEquiv a with hedef
      set A : ℝ → Tensor0SSpace (4 + a) I3 x :=
        fun s => mixedCurvatureTensor S a b s x with hAdef
      have hcar : ancientTimeInterval.carrier = Iic (0 : ℝ) := ancientTimeInterval_carrier
      have htc : t ∈ ancientTimeInterval.carrier := by
        rw [hcar]; exact mem_Iic.mpr ht
      have hAdiff : DifferentiableWithinAt ℝ A (Iic (0 : ℝ)) t := hdiff b t ht
      have huniq : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) t :=
        uniqueDiffOn_Iic (0 : ℝ) t (mem_Iic.mpr ht)
      have huniqt : UniqueDiffWithinAt ℝ (Iic t) t :=
        uniqueDiffOn_Iic t t (mem_Iic.mpr le_rfl)
      have hJtime := J.time a b t htc x v
      have hmixed : mixedCurvatureTensor S a (b + 1) t x =
          metricTimeDerivWithin (I := I3) S.base.metric ancientTimeInterval.carrier A t := rfl
      have hstep := metricTimeDerivWithin_apply (I := I3) (M := M) S.base.metric
        (J := ancientTimeInterval.carrier) (A := A) (t := t)
        (by rw [hcar]; exact hAdiff) (by rw [hcar]; exact huniq) (v ∘ e)
      have hev : HasDerivWithinAt (fun s : ℝ => A s (v ∘ e))
          (derivWithin A (Iic (0 : ℝ)) t (v ∘ e)) (Iic (0 : ℝ)) t :=
        (tensor0SEvalCLM (I := I3) (v ∘ e)).hasFDerivAt.comp_hasDerivWithinAt t
          hAdiff.hasDerivWithinAt
      have hevt : HasDerivWithinAt (fun s : ℝ => A s (v ∘ e))
          (derivWithin A (Iic (0 : ℝ)) t (v ∘ e)) (Iic t) t :=
        hev.mono (Iic_subset_Iic.mpr ht)
      have hset : ancientTimeInterval.carrier ∩ Iic t = Iic t := by
        rw [hcar]
        exact inter_eq_self_of_subset_right (Iic_subset_Iic.mpr ht)
      have hcongr : derivWithin (fun s : ℝ => J.value a b s x v)
          (ancientTimeInterval.carrier ∩ Iic t) t =
          derivWithin (fun s : ℝ => A s (v ∘ e)) (Iic t) t := by
        rw [hset]
        refine derivWithin_congr (fun s hs => ?_) ?_
        · exact ih s (le_trans (mem_Iic.mp hs) ht) v
        · exact ih t ht v
      have hderiv : derivWithin (fun s : ℝ => J.value a b s x v)
          (ancientTimeInterval.carrier ∩ Iic t) t =
          derivWithin (fun s : ℝ => A s (v ∘ e)) ancientTimeInterval.carrier t := by
        rw [hcongr, hevt.derivWithin huniqt, hcar, hev.derivWithin huniq]
      have hsum : (∑ j : Fin (a + 4), J.value a b t x (Function.update v j
            (ricciEndAt (I := I3) (S.base.metric t)
              (metricRicciAt (I := I3) (S.base.metric t) x) (v j)))) =
          ∑ i : Fin (4 + a), A t (Function.update (v ∘ e) i
            (ricciSharp (I := I3) (S.base.metric t) x ((v ∘ e) i))) := by
        refine (Fintype.sum_equiv e
          (fun i => A t (Function.update (v ∘ e) i
            (ricciSharp (I := I3) (S.base.metric t) x ((v ∘ e) i))))
          (fun j => J.value a b t x (Function.update v j
            (ricciEndAt (I := I3) (S.base.metric t)
              (metricRicciAt (I := I3) (S.base.metric t) x) (v j)))) ?_).symm
        intro i
        have hupd : Function.update v (e i)
              (ricciSharp (I := I3) (S.base.metric t) x ((v ∘ e) i)) ∘ e =
            Function.update (v ∘ e) i
              (ricciSharp (I := I3) (S.base.metric t) x ((v ∘ e) i)) := by
          rw [Function.update_comp_equiv v e (e i) _, Equiv.symm_apply_apply]
        have hend : ricciEndAt (I := I3) (S.base.metric t)
              (metricRicciAt (I := I3) (S.base.metric t) x) (v (e i)) =
            ricciSharp (I := I3) (S.base.metric t) x ((v ∘ e) i) :=
          ricciEndAt_metricRicciAt_eq_ricciSharp (I := I3) (S.base.metric t) x (v (e i))
        rw [ih t ht (Function.update v (e i)
          (ricciEndAt (I := I3) (S.base.metric t)
            (metricRicciAt (I := I3) (S.base.metric t) x) (v (e i)))), hend, hupd]
      rw [hJtime, hmixed, hstep, hderiv, hsum]

omit [SigmaCompactSpace M] in
theorem mixedCurvatureJet_norm_eq
    (S : SolutionOn (I := I3) (M := M) ancientTimeInterval)
    (J : MixedCurvatureJet S) (a : ℕ) (x : M)
    (hdiff : ∀ (q : ℕ) (t : ℝ), t ≤ 0 →
      DifferentiableWithinAt ℝ (fun s : ℝ => mixedCurvatureTensor S a q s x) (Iic 0) t)
    (b : ℕ) {t : ℝ} (ht : t ≤ 0) :
    J.norm a b t x = mixedCurvatureNorm S a b t x := by
  classical
  obtain ⟨e, hrep⟩ := exists_slotEquiv_mixedCurvatureJet_value S J a x hdiff
  have hfiber : J.value a b t x =
      (mixedCurvatureTensor S a b t x).domDomCongr e := by
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    exact hrep b t ht v
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I3) (S.base.metric t) x
  have hinv : MetricInverseInBasis (I := I3) (S.base.metric t) x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I3 x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I3) (S.base.metric t) basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h' i j
  have hnorm : normSq0S (I := I3) (S.base.metric t) x (a + 4) (J.value a b t x) =
      normSq0S (I := I3) (S.base.metric t) x (4 + a) (mixedCurvatureTensor S a b t x) := by
    rw [hfiber]
    exact normSq0S_domDomCongr (I := I3) (S.base.metric t) x basis hinv e
      (mixedCurvatureTensor S a b t x)
  change Real.sqrt (normSq0S (I := I3) (S.base.metric t) x (a + 4) (J.value a b t x)) = _
  rw [hnorm]
  rfl

end Bridge


section Slot

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

private theorem slotThreeSpaceFinrank : Module.finrank ℝ ThreeSpace = 3 := by
  simp [ThreeSpace]

private local instance slotThreeSpaceNeZero : NeZero (Module.finrank ℝ ThreeSpace) :=
  ⟨by rw [slotThreeSpaceFinrank]; norm_num⟩

private local instance slotC1 {D : RealTimeInterval}
    (P : PointedFlowData.{u, 0, 0} (I := I3) D) : IsManifold I3 1 P.M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance slotC2 {D : RealTimeInterval}
    (P : PointedFlowData.{u, 0, 0} (I := I3) D) : IsManifold I3 2 P.M :=
  IsManifold.of_le (n := ∞) (by decide)


theorem ancientKappa_mixedCurvatureTensor_differentiableWithinAt
    {kappa : ℝ} (P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (hP : IsAncientKappaSolution (I := I3) kappa P) (hbase : PointedFlowScalarAtBase P 1)
    (p q : ℕ) {t : ℝ} (ht : t ≤ 0) :
    DifferentiableWithinAt ℝ
      (fun s : ℝ => mixedCurvatureTensor P.S p q s P.basepoint) (Iic 0) t := by
  obtain ⟨_, _, hbound⟩ := exists_normalized_klim_mixed_jet_bound (I := I3)
    slotThreeSpaceFinrank kappa 0 le_rfl p q
  exact (hbound ancientTimeInterval P
    (ancientKappaThree_toKLim P hP slotThreeSpaceFinrank) hbase t ht P.basepoint
    (by simp [riemannianEDistOf_self])).1


theorem ancientKappa_universal_derivatives_jet (a b : ℕ) {C : ℝ}
    (hU : UniversalMixedJetBound.{u} a b C) :
    ∀ kappa : ℝ, 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval,
        IsAncientKappaSolution (I := I3) kappa P → PointedFlowScalarAtBase P 1 →
        ∀ J : MixedCurvatureJet P.S, J.norm a b 0 P.basepoint ≤ C := by
  intro kappa _ P hP hbase J
  have hdiff : ∀ (q : ℕ) (t : ℝ), t ≤ 0 →
      DifferentiableWithinAt ℝ
        (fun s : ℝ => mixedCurvatureTensor P.S a q s P.basepoint) (Iic 0) t :=
    fun q t ht =>
      ancientKappa_mixedCurvatureTensor_differentiableWithinAt P hP hbase a q ht
  have hbridge : J.norm a b 0 P.basepoint =
      mixedCurvatureNorm P.S a b 0 P.basepoint :=
    mixedCurvatureJet_norm_eq P.S J a P.basepoint hdiff b le_rfl
  have hjet := hU kappa P hP 0 le_rfl P.basepoint
  have hscalar : P.S.scalar 0 P.basepoint = 1 := hbase
  rw [hscalar, Real.one_rpow, mul_one] at hjet
  rw [hbridge]
  exact hjet


theorem exists_kappa_universal_derivatives_of_round (a b : ℕ) {C₁ : ℝ}
    (hround : RoundMixedJetBound.{u} a b C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ kappa : ℝ, 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval,
        IsAncientKappaSolution (I := I3) kappa P → PointedFlowScalarAtBase P 1 →
        ∀ J : MixedCurvatureJet P.S, J.norm a b 0 P.basepoint ≤ C := by
  obtain ⟨C, hC, hU⟩ := exists_universal_mixed_jet_bound.{u} a b hround
  exact ⟨C, hC, ancientKappa_universal_derivatives_jet a b hU⟩

end Slot

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
