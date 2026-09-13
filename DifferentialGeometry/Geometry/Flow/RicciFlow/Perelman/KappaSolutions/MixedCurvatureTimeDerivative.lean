import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundFlowMixedJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativesJetBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.MixedJetPolynomials

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology

universe u

private def mixedTimeCurvEquiv : (m : ℕ) → Fin (4 + m) ≃ Fin (m + 4)
  | 0 => Equiv.refl _
  | (m + 1) => frontExtendEquiv (mixedTimeCurvEquiv m)

section Bridge

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

private theorem mixedTimeThreeSpaceFinrank : Module.finrank ℝ ThreeSpace = 3 := by
  simp [ThreeSpace]

private local instance mixedTimeThreeSpaceNeZero : NeZero (Module.finrank ℝ ThreeSpace) :=
  ⟨by rw [mixedTimeThreeSpaceFinrank]; norm_num⟩

omit [SigmaCompactSpace M] in
private theorem mixedTime_curv_apply_iterCov (g : SmoothRiemannianMetric I3 M) :
    ∀ (m : ℕ) (x : M) (v : Fin (m + 4) → TangentSpace I3 x),
      curvCovDeriv (I := I3) (M := M) g m x v =
        (ContinuousMultilinearMap.domDomCongr (mixedTimeCurvEquiv m)
          ((iterCov (I := I3) g 4
            (DifferentialGeometry.Geometry.Curvature.metricRm04
              (I := I3) (M := M) g) m) x)) v := by
  intro m
  induction m with
  | zero =>
      intro x v
      rfl
  | succ m ih =>
      intro x v
      have hfield :
          curvCovDeriv (I := I3) (M := M) g m =
            MultilinearSection.domDomCongr
              (𝕜 := ℝ) (F := ThreeSpace) (IB := I3) (E := TangentSpace I3)
              (∞ : WithTop ℕ∞) (mixedTimeCurvEquiv m)
              (iterCov (I := I3) g 4
                (DifferentialGeometry.Geometry.Curvature.metricRm04
                  (I := I3) (M := M) g) m) := by
        refine DFunLike.ext _ _ (fun y => ?_)
        refine ContinuousMultilinearMap.ext (fun w => ?_)
        exact ih y w
      calc
        curvCovDeriv (I := I3) (M := M) g (m + 1) x v =
            curvCovDerivStep (I := I3) g m
              (curvCovDeriv (I := I3) (M := M) g m) x v :=
          congrArg (fun A => A x v)
            (curvCovDeriv_succ (I := I3) (M := M) g m)
        _ = covStep (I := I3) g (m + 4)
              (curvCovDeriv (I := I3) (M := M) g m) x v :=
          congrArg (fun A => A x v)
            (curvStep_eq_covStep (I := I3) (M := M) g m _)
        _ = covStep (I := I3) g (m + 4)
              (MultilinearSection.domDomCongr
                (𝕜 := ℝ) (F := ThreeSpace) (IB := I3) (E := TangentSpace I3)
                (∞ : WithTop ℕ∞) (mixedTimeCurvEquiv m)
                (iterCov (I := I3) g 4
                  (DifferentialGeometry.Geometry.Curvature.metricRm04
                    (I := I3) (M := M) g) m)) x v :=
          congrArg (fun A => covStep (I := I3) g (m + 4) A x v) hfield
        _ = (MultilinearSection.domDomCongr
              (𝕜 := ℝ) (F := ThreeSpace) (IB := I3) (E := TangentSpace I3)
              (∞ : WithTop ℕ∞) (frontExtendEquiv (mixedTimeCurvEquiv m))
              (covStep (I := I3) g (4 + m)
                (iterCov (I := I3) g 4
                  (DifferentialGeometry.Geometry.Curvature.metricRm04
                    (I := I3) (M := M) g) m))) x v :=
          congrArg (fun A => A x v)
            (covStep_domDomCongr (I := I3) g (mixedTimeCurvEquiv m) _)
        _ = (ContinuousMultilinearMap.domDomCongr (mixedTimeCurvEquiv (m + 1))
              ((iterCov (I := I3) g 4
                (DifferentialGeometry.Geometry.Curvature.metricRm04
                  (I := I3) (M := M) g) (m + 1)) x)) v := by
          rfl

omit [SigmaCompactSpace M] in
theorem exists_slotEquiv_mixedCurvatureJet_value_of_uniqueDiffWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    (J : MixedCurvatureJet S) (a : ℕ) (x : M) {t' t : ℝ}
    (hdiff : ∀ q : ℕ, ∀ s ∈ D.carrier ∩ Set.Ioc t' t, DifferentiableWithinAt ℝ
      (fun u : ℝ => mixedCurvatureTensor S a q u x) D.carrier s)
    (hcar : ∀ s ∈ D.carrier ∩ Set.Ioc t' t, UniqueDiffWithinAt ℝ D.carrier s)
    (hint : ∀ s ∈ D.carrier ∩ Set.Ioc t' t,
      UniqueDiffWithinAt ℝ (D.carrier ∩ Set.Iic s) s) :
    ∃ e : Fin (4 + a) ≃ Fin (a + 4),
      ∀ (b : ℕ) (s : ℝ), s ∈ D.carrier ∩ Set.Ioc t' t →
        ∀ v : Fin (a + 4) → TangentSpace I3 x,
          J.value a b s x v = mixedCurvatureTensor S a b s x (v ∘ e) := by
  classical
  refine ⟨mixedTimeCurvEquiv a, ?_⟩
  intro b
  induction b with
  | zero =>
      intro s _ v
      have hspat : J.value a 0 s x v =
          curvCovDeriv (I := I3) (M := M) (S.base.metric s) a x v :=
        congrArg (fun A => A x v) (J.spatial a s)
      have hiter := mixedTime_curv_apply_iterCov (M := M) (S.base.metric s) a x v
      have hnabla : nablaKRm04Field (I := I3) S s a =
          iterCov (I := I3) (S.base.metric s) 4 (S.base.rm04 s) a :=
        nablaKRm_eq_iterCov (I := I3) S s a
      rw [hspat, hiter]
      change (iterCov (I := I3) (S.base.metric s) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04 (I := I3) (M := M)
          (S.base.metric s)) a x) (v ∘ mixedTimeCurvEquiv a) = _
      rw [mixedCurvatureTensor_zero]
      exact congrArg (fun A => A x (v ∘ mixedTimeCurvEquiv a)) hnabla.symm
  | succ b ih =>
      intro s hs v
      set e := mixedTimeCurvEquiv a with hedef
      set A : ℝ → Tensor0SSpace (4 + a) I3 x :=
        fun s => mixedCurvatureTensor S a b s x with hAdef
      have hsc : s ∈ D.carrier := Set.mem_of_mem_inter_left hs
      have hst : t' < s := (Set.mem_of_mem_inter_right hs).1
      have hAdiff : DifferentiableWithinAt ℝ A D.carrier s := hdiff b s hs
      have hJtime := J.time a b s hsc x v
      have hmixed : mixedCurvatureTensor S a (b + 1) s x =
          metricTimeDerivWithin (I := I3) S.base.metric D.carrier A s := rfl
      have hstep := metricTimeDerivWithin_apply (I := I3) (M := M) S.base.metric
        (J := D.carrier) (A := A) (t := s) hAdiff (hcar s hs) (v ∘ e)
      have hev : HasDerivWithinAt (fun s : ℝ => A s (v ∘ e))
          (derivWithin A D.carrier s (v ∘ e)) D.carrier s :=
        (tensor0SEvalCLM (I := I3) (v ∘ e)).hasFDerivAt.comp_hasDerivWithinAt s
          hAdiff.hasDerivWithinAt
      have hevt : HasDerivWithinAt (fun s : ℝ => A s (v ∘ e))
          (derivWithin A D.carrier s (v ∘ e)) (D.carrier ∩ Set.Iic s) s :=
        hev.mono Set.inter_subset_left
      have hAe : derivWithin (fun s : ℝ => A s (v ∘ e)) D.carrier s =
          derivWithin A D.carrier s (v ∘ e) :=
        hev.derivWithin (hcar s hs)
      have hIH : (fun u : ℝ => J.value a b u x v) =ᶠ[𝓝[D.carrier ∩ Set.Iic s] s]
          (fun u : ℝ => A u (v ∘ e)) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hst),
          self_mem_nhdsWithin] with u hu hmem
        exact ih u ⟨Set.mem_of_mem_inter_left hmem, hu,
          (Set.mem_Iic.mp (Set.mem_of_mem_inter_right hmem)).trans
            (Set.mem_of_mem_inter_right hs).2⟩ v
      have hderiv : derivWithin (fun u : ℝ => J.value a b u x v)
          (D.carrier ∩ Set.Iic s) s =
          derivWithin (fun u : ℝ => A u (v ∘ e)) D.carrier s := by
        rw [(hevt.congr_of_eventuallyEq hIH (ih s hs v)).derivWithin (hint s hs), ← hAe]
      have hsum : (∑ j : Fin (a + 4), J.value a b s x (Function.update v j
            (ricciEndAt (I := I3) (S.base.metric s)
              (metricRicciAt (I := I3) (S.base.metric s) x) (v j)))) =
          ∑ i : Fin (4 + a), A s (Function.update (v ∘ e) i
            (ricciSharp (I := I3) (S.base.metric s) x ((v ∘ e) i))) := by
        refine (Fintype.sum_equiv e
          (fun i => A s (Function.update (v ∘ e) i
            (ricciSharp (I := I3) (S.base.metric s) x ((v ∘ e) i))))
          (fun j => J.value a b s x (Function.update v j
            (ricciEndAt (I := I3) (S.base.metric s)
              (metricRicciAt (I := I3) (S.base.metric s) x) (v j)))) ?_).symm
        intro i
        have hupd : Function.update v (e i)
              (ricciSharp (I := I3) (S.base.metric s) x ((v ∘ e) i)) ∘ e =
            Function.update (v ∘ e) i
              (ricciSharp (I := I3) (S.base.metric s) x ((v ∘ e) i)) := by
          rw [Function.update_comp_equiv v e (e i) _, Equiv.symm_apply_apply]
        have hend : ricciEndAt (I := I3) (S.base.metric s)
              (metricRicciAt (I := I3) (S.base.metric s) x) (v (e i)) =
            ricciSharp (I := I3) (S.base.metric s) x ((v ∘ e) i) :=
          ricciEndAt_metricRicciAt_eq_ricciSharp (I := I3) (S.base.metric s) x (v (e i))
        rw [ih s hs (Function.update v (e i)
          (ricciEndAt (I := I3) (S.base.metric s)
            (metricRicciAt (I := I3) (S.base.metric s) x) (v (e i)))), hend, hupd]
      rw [hJtime, hmixed, hstep, hderiv, hsum]

omit [SigmaCompactSpace M] in
theorem mixedCurvatureJet_norm_eq_mixedCurvatureNorm_of_uniqueDiffWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    (J : MixedCurvatureJet S) (a : ℕ) (x : M) {t' t : ℝ}
    (hdiff : ∀ q : ℕ, ∀ s ∈ D.carrier ∩ Set.Ioc t' t, DifferentiableWithinAt ℝ
      (fun u : ℝ => mixedCurvatureTensor S a q u x) D.carrier s)
    (hcar : ∀ s ∈ D.carrier ∩ Set.Ioc t' t, UniqueDiffWithinAt ℝ D.carrier s)
    (hint : ∀ s ∈ D.carrier ∩ Set.Ioc t' t,
      UniqueDiffWithinAt ℝ (D.carrier ∩ Set.Iic s) s)
    (b : ℕ) (ht : t ∈ D.carrier ∩ Set.Ioc t' t) :
    J.norm a b t x = mixedCurvatureNorm S a b t x := by
  classical
  obtain ⟨e, hrep⟩ :=
    exists_slotEquiv_mixedCurvatureJet_value_of_uniqueDiffWithinAt S J a x hdiff hcar hint
  have hfiber : J.value a b t x = (mixedCurvatureTensor S a b t x).domDomCongr e := by
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    exact hrep b t ht v
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I3) (S.base.metric t) x
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

theorem mixedCurvatureJet_norm_eq_mixedCurvatureNorm_of_regular
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D) (hS : IsSolutionOn S)
    (J : MixedCurvatureJet S) (a b : ℕ) (x : M) {t : ℝ} (ht : t ∈ D.regular) :
    J.norm a b t x = mixedCurvatureNorm S a b t x := by
  obtain ⟨c₁, c₂, _htIcc, hIccnhds, hsub⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (D.regular_isOpen.mem_nhds ht)
  have htIoo : t ∈ Set.Ioo c₁ c₂ := Icc_mem_nhds_iff.mp hIccnhds
  have hrange : ∀ s : ℝ, s ∈ D.carrier ∩ Set.Ioc c₁ t → s ∈ D.regular := by
    intro s hs
    exact hsub ⟨(Set.mem_of_mem_inter_right hs).1.le,
      (Set.mem_of_mem_inter_right hs).2.trans htIoo.2.le⟩
  refine mixedCurvatureJet_norm_eq_mixedCurvatureNorm_of_uniqueDiffWithinAt S J a x
    (t' := c₁) ?_ ?_ ?_ b ⟨D.regular_subset ht, htIoo.1, le_rfl⟩
  · intro q s hs
    obtain ⟨P, hP⟩ :=
      exists_mixed_curvature_jet_polynomials (Module.finrank ℝ (TangentSpace I3 x)) a q
    have hd := (hP S hS s (hrange s hs) x (Module.finBasis ℝ (TangentSpace I3 x))).1
    have hd' : DifferentiableAt ℝ (fun u : ℝ => mixedCurvatureTensor S a q u x) s := by
      simpa only [mixedCurvatureTensor] using hd
    exact hd'.differentiableWithinAt
  · intro s hs
    exact uniqueDiffWithinAt_of_mem_nhds (D.regular_mem_nhds (hrange s hs))
  · intro s hs
    have hst : c₁ < s := (Set.mem_of_mem_inter_right hs).1
    have hU : UniqueDiffWithinAt ℝ (Set.Ioc c₁ s) s :=
      (uniqueDiffOn_Ioc c₁ s).uniqueDiffWithinAt ⟨hst, le_rfl⟩
    refine hU.mono (fun u hu => ⟨?_, hu.2⟩)
    exact D.regular_subset (hsub ⟨hu.1.le,
      hu.2.trans ((Set.mem_of_mem_inter_right hs).2.trans htIoo.2.le)⟩)

omit [SigmaCompactSpace M] in
theorem closedOpen_carrier_inter_Iic_leftEndpoint {T : ℝ} (hT : 0 < T) :
    (RealTimeInterval.closedOpen 0 T hT).carrier ∩ Set.Iic 0 = {0} := by
  ext s
  simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hcar, hle⟩
    exact le_antisymm hle hcar.1
  · rintro rfl
    exact ⟨⟨le_rfl, hT⟩, le_rfl⟩

private theorem not_uniqueDiffWithinAt_singleton_zero :
    ¬ UniqueDiffWithinAt ℝ ({0} : Set ℝ) 0 := by
  intro h
  have hcone : ∀ y ∈ tangentConeAt ℝ ({0} : Set ℝ) 0, y = 0 := by
    intro y hy
    obtain ⟨α, l, hl, c, d, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
    have hzero : ∀ᶠ n in l, d n = 0 := by
      filter_upwards [hds] with n hn
      simpa using hn
    have hlim : Tendsto (fun n => c n • d n) l (𝓝 0) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hzero] with n hn
      simp [hn]
    exact tendsto_nhds_unique hcd hlim
  have hspan : (Submodule.span ℝ (tangentConeAt ℝ ({0} : Set ℝ) 0) : Set ℝ) ⊆ {0} := by
    intro y hy
    exact Submodule.span_induction (p := fun z _ => z = 0)
      (fun z hz => hcone z hz) rfl
      (fun a b _ _ ha hb => by rw [ha, hb, add_zero])
      (fun a b _ hb => by rw [hb, smul_zero]) hy
  have hd : Dense ({0} : Set ℝ) := h.dense_tangentConeAt.mono hspan
  have huniv : (Set.univ : Set ℝ) = {0} := by rw [← hd.closure_eq, closure_singleton]
  have h10 : (1 : ℝ) = 0 := by
    simpa using congrArg (fun s : Set ℝ => (1 : ℝ) ∈ s) huniv
  norm_num at h10

theorem derivWithin_closedOpen_inter_Iic_leftEndpoint (f : ℝ → ℝ) {T : ℝ} (hT : 0 < T) :
    derivWithin f ((RealTimeInterval.closedOpen 0 T hT).carrier ∩ Set.Iic 0) 0 = 0 := by
  rw [closedOpen_carrier_inter_Iic_leftEndpoint hT]
  exact derivWithin_zero_of_not_uniqueDiffWithinAt not_uniqueDiffWithinAt_singleton_zero

theorem derivWithin_id_closedOpen_leftEndpoint (T : ℝ) (hT : 0 < T) :
    derivWithin (fun s : ℝ => s) ((RealTimeInterval.closedOpen 0 T hT).carrier ∩ Set.Iic 0) 0 =
        0 ∧
      derivWithin (fun s : ℝ => s) (RealTimeInterval.closedOpen 0 T hT).carrier 0 = 1 := by
  refine ⟨derivWithin_closedOpen_inter_Iic_leftEndpoint (fun s : ℝ => s) hT, ?_⟩
  exact ((hasDerivAt_id (0 : ℝ)).hasDerivWithinAt).derivWithin
    (uniqueDiffOn_Ico (0 : ℝ) T 0 ⟨le_rfl, hT⟩)

omit [SigmaCompactSpace M] in
theorem closedOpen_carrier_inter_Iic_ssubset {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Set.Ioo 0 T) :
    (RealTimeInterval.closedOpen 0 T hT).carrier ∩ Set.Iic t ⊂
      (RealTimeInterval.closedOpen 0 T hT).carrier := by
  refine ⟨Set.inter_subset_left, fun hsub => ?_⟩
  have hmid : (t + T) / 2 ∈ (RealTimeInterval.closedOpen 0 T hT).carrier :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgt : t < (t + T) / 2 := by linarith [ht.2]
  exact absurd (Set.mem_of_mem_inter_right (hsub hmid)) (not_le.mpr hgt)

theorem derivWithin_abs_Icc_inter_Iic_ne_derivWithin_abs_Icc :
    derivWithin (fun s : ℝ => |s|) (Set.Icc (-1 : ℝ) 1 ∩ Set.Iic 0) 0 ≠
      derivWithin (fun s : ℝ => |s|) (Set.Icc (-1 : ℝ) 1) 0 := by
  have hset : Set.Icc (-1 : ℝ) 1 ∩ Set.Iic 0 = Set.Icc (-1 : ℝ) 0 := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by linarith⟩, h2⟩
  have hleft : derivWithin (fun s : ℝ => |s|) (Set.Icc (-1 : ℝ) 1 ∩ Set.Iic 0) 0 = -1 := by
    rw [hset]
    have hder : HasDerivWithinAt (fun s : ℝ => |s|) (-1) (Set.Icc (-1 : ℝ) 0) 0 :=
      (hasDerivWithinAt_neg (0 : ℝ) (Set.Icc (-1 : ℝ) 0)).congr_of_mem
        (fun s hs => abs_of_nonpos hs.2) ⟨by norm_num, le_rfl⟩
    exact hder.derivWithin
      (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0) 0 ⟨by norm_num, le_rfl⟩)
  have hright : derivWithin (fun s : ℝ => |s|) (Set.Icc (-1 : ℝ) 1) 0 = 0 := by
    have hnot : ¬ DifferentiableWithinAt ℝ (fun s : ℝ => |s|) (Set.Icc (-1 : ℝ) 1) 0 :=
      fun hd => not_differentiableAt_abs_zero
        (hd.differentiableAt (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)))
    rw [derivWithin_zero_of_not_differentiableWithinAt hnot]
  rw [hleft, hright]
  norm_num

theorem not_forall_derivWithin_inter_Iic_eq :
    ¬ (∀ (f : ℝ → ℝ) (s : Set ℝ) (t : ℝ), derivWithin f (s ∩ Set.Iic t) t = derivWithin f s t) :=
  fun h => derivWithin_abs_Icc_inter_Iic_ne_derivWithin_abs_Icc
    (h (fun s : ℝ => |s|) (Set.Icc (-1 : ℝ) 1) 0)

end Bridge

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

open Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology ENNReal

theorem high_curvature_derivatives_of_mixedCurvatureNorm_bound (a b : ℕ)
    (h : ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
        [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
        (_hS : IsSolutionOn S) (_o : TangentOrientationSection M),
        ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ x t, t ∈ Set.Ioo 0 T → Q0 ≤ S.scalar t x →
          ∀ y ∈ riemannianBallOf (I := I3) (S.base.metric t) x
              (eta / Real.sqrt (S.scalar t x)),
            0 < S.scalar t y ∧
              DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureNorm
                  S a b t y ≤
                C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b)) :
    ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
        [T2Space (TangentBundle I3 M)] (T : ℝ) (hT : 0 < T)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
        (_hS : IsSolutionOn S) (_o : TangentOrientationSection M),
        ∃ Q0 : ℝ, 0 < Q0 ∧ ∀ J : MixedCurvatureJet S, ∀ x t,
          t ∈ Set.Ioo 0 T → Q0 ≤ S.scalar t x →
          ∀ y ∈ riemannianBallOf (I := I3) (S.base.metric t) x
              (eta / Real.sqrt (S.scalar t x)),
            0 < S.scalar t y ∧ J.norm a b t y ≤
              C * Real.rpow (S.scalar t y) (1 + (a : ℝ) / 2 + b) := by
  obtain ⟨C, eta, hC, heta, hbound⟩ := h
  refine ⟨C, eta, hC, heta, ?_⟩
  intro M _ _ _ _ _ _ _ T hT S hS o
  obtain ⟨Q0, hQ0, hmain⟩ := hbound M T hT S hS o
  refine ⟨Q0, hQ0, fun J x t ht hQ y hy => ?_⟩
  obtain ⟨hpos, hnorm⟩ := hmain x t ht hQ y hy
  have hbridge : J.norm a b t y =
      DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureNorm
        S a b t y :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.mixedCurvatureJet_norm_eq_mixedCurvatureNorm_of_regular
      S hS J a b y (by simpa only [RealTimeInterval.closedOpen] using ht)
  exact ⟨hpos, by rw [hbridge]; exact hnorm⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
