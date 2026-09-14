import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Compact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Topology.Manifold.SphereOrientation

noncomputable section
open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage

variable {P : OrientedThreeStage.{u}}

theorem chartVector_contMDiffOn (P : OrientedThreeStage.{u}) (p : P.Carrier) (i : Fin 3) :
    ContMDiffOn ThreeModel (ThreeModel.prod 𝓘(ℝ, ThreeSpace)) ∞
      (fun x : P.Carrier => TotalSpace.mk' ThreeSpace x (P.chartVector p x i))
      (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet := by
  have hiff :=
    ((trivializationAt ThreeSpace (TangentSpace ThreeModel) p)).contMDiffOn_section_baseSet_iff
      (IB := ThreeModel) (n := ∞) (s := fun x => P.chartVector p x i)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn ThreeModel 𝓘(ℝ, ThreeSpace) ∞
      (fun _ : P.Carrier => EuclideanSpace.single i (1 : ℝ))
      (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet := contMDiffOn_const
  refine hconst.congr ?_
  intro x hx
  have h := (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).apply_mk_symm hx
    (EuclideanSpace.single i (1 : ℝ))
  rw [chartVector, Trivialization.symmL_apply _ hx]
  exact congrArg Prod.snd h

theorem chartVector_metric_contMDiffOn (P : OrientedThreeStage.{u}) (g : ℝ → P.Metric)
    {K : Set ℝ}
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × P.Carrier => (⟨q.2, (g q.1).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (K ×ˢ (Set.univ : Set P.Carrier)))
    (p : P.Carrier) (i j : Fin 3) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × P.Carrier =>
        (g q.1).inner q.2 (P.chartVector p q.2 i) (P.chartVector p q.2 j))
      (K ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) := by
  have hmetric := hg.mono (fun q hq => ⟨hq.1, Set.mem_univ q.2⟩ :
    K ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet ⊆
      K ×ˢ (Set.univ : Set P.Carrier))
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) (ThreeModel.prod 𝓘(ℝ, ThreeSpace)) ∞
      (fun q : ℝ × P.Carrier => TotalSpace.mk' ThreeSpace q.2 (P.chartVector p q.2 i))
      (K ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) :=
    (P.chartVector_contMDiffOn p i).comp contMDiffOn_snd (fun _ hq => hq.2)
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) (ThreeModel.prod 𝓘(ℝ, ThreeSpace)) ∞
      (fun q : ℝ × P.Carrier => TotalSpace.mk' ThreeSpace q.2 (P.chartVector p q.2 j))
      (K ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) :=
    (P.chartVector_contMDiffOn p j).comp contMDiffOn_snd (fun _ hq => hq.2)
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := ThreeSpace) (F₂ := ThreeSpace)
    (F₃ := ℝ)
    (E₁ := TangentSpace ThreeModel (M := P.Carrier))
    (E₂ := TangentSpace ThreeModel (M := P.Carrier))
    (E₃ := Bundle.Trivial P.Carrier ℝ) (b := fun q : ℝ × P.Carrier => q.2) hmetric hv hw
  intro q hq
  have h := happ q hq
  rw [Bundle.contMDiffWithinAt_totalSpace] at h
  exact h.2

theorem MetricSmoothUpTo.of_contMDiffOn (P : OrientedThreeStage.{u}) (g : ℝ → P.Metric)
    {J K : Set ℝ} (hK : IsOpen K) (hJK : J ⊆ K)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × P.Carrier => (⟨q.2, (g q.1).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (K ×ˢ (Set.univ : Set P.Carrier))) :
    P.MetricSmoothUpTo g J := by
  intro p t ht
  refine ⟨(trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet,
    (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).open_baseSet,
    FiberBundle.mem_baseSet_trivializationAt ThreeSpace (TangentSpace ThreeModel) p, subset_rfl,
    K, hK, hJK ht,
    fun q i j => (g q.1).inner q.2 (P.chartVector p q.2 i) (P.chartVector p q.2 j), ?_, ?_⟩
  · exact fun i j => P.chartVector_metric_contMDiffOn g hg p i j
  · intro s hs x hx i j
    rfl

theorem MetricSmoothUpTo.of_contMDiffOn_Ico (P : OrientedThreeStage.{u}) (g : ℝ → P.Metric)
    {a b d : ℝ} (hab : a < b) (hbd : b < d)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × P.Carrier => (⟨q.2, (g q.1).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (Ico a d ×ˢ (Set.univ : Set P.Carrier))) :
    P.MetricSmoothUpTo g (Icc a b) := by
  classical
  intro p t ht
  have hpiece : ∀ i j : Fin 3, ∃ (U : Set P.Carrier) (A : ℝ × P.Carrier → ℝ),
      IsOpen U ∧ p ∈ U ∧
      U ⊆ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞ (fun q => A q)
        ((Set.univ : Set ℝ) ×ˢ U) ∧
      ∀ s ∈ Icc a b, ∀ x ∈ U,
        A (s, x) = (g s).inner x (P.chartVector p x i) (P.chartVector p x j) := by
    intro i j
    let c : OpenPartialHomeomorph P.Carrier ThreeSpace :=
      { toPartialEquiv := extChartAt ThreeModel p
        open_source := isOpen_extChartAt_source p
        open_target := isOpen_extChartAt_target p
        continuousOn_toFun := continuousOn_extChartAt p
        continuousOn_invFun := continuousOn_extChartAt_symm p }
    have hp : p ∈ c.source := mem_extChartAt_source p
    have hcsymm : ContMDiffOn 𝓘(ℝ, ThreeSpace) ThreeModel ∞ (fun z => c.symm z) c.target :=
      contMDiffOn_extChartAt_symm p
    let hh : ℝ → ThreeSpace → ℝ := fun r z =>
      (g (a + r)).inner (c.symm z) (P.chartVector p (c.symm z) i)
        (P.chartVector p (c.symm z) j)
    have hf : ContDiffOn ℝ ∞ (Function.uncurry hh) (Icc 0 (b - a) ×ˢ c.target) := by
      rw [← contMDiffOn_iff_contDiffOn]
      have hmap : ContMDiffOn (𝓘(ℝ, ℝ × ThreeSpace)) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
          (fun z : ℝ × ThreeSpace => (a + z.1, c.symm z.2)) (Icc 0 (b - a) ×ˢ c.target) :=
        (((contDiff_const (c := a)).add contDiff_fst).contMDiff.contMDiffOn).prodMk
          (hcsymm.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2))
      exact (P.chartVector_metric_contMDiffOn g hg p i j).comp hmap (fun z hz => by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · linarith [hz.1.1]
        · linarith [hz.1.2, hbd]
        · change c.symm z.2 ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet
          rw [TangentBundle.trivializationAt_baseSet,
            ← extChartAt_source (I := ThreeModel) (x := p)]
          exact c.map_target hz.2)
    obtain ⟨fext, V₀, hV₀, hfext, heq⟩ :=
      DifferentialGeometry.Analysis.borel_interval_extend_param hh (b - a) (sub_pos.mpr hab)
        c.target (c p) (by rw [c.open_target.interior_eq]; exact c.map_source hp) hf
    obtain ⟨V, hVV₀, hVopen, hpV⟩ := mem_nhds_iff.mp hV₀
    refine ⟨c.source ∩ c ⁻¹' V, fun q => fext (q.1 - a) (c q.2),
      c.isOpen_inter_preimage hVopen, ⟨hp, hpV⟩, ?_, ?_, ?_⟩
    · intro x hx
      rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := ThreeModel) (x := p)]
      exact hx.1
    · have hfe : ContMDiffOn (𝓘(ℝ, ℝ × ThreeSpace)) 𝓘(ℝ, ℝ) ∞
          (Function.uncurry fext) ((Set.univ : Set ℝ) ×ˢ V) :=
        hfext.contMDiffOn.mono (Set.prod_mono Subset.rfl hVV₀)
      have hct : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ThreeSpace) ∞
          (fun q : ℝ × P.Carrier => c q.2)
          ((Set.univ : Set ℝ) ×ˢ (c.source ∩ c ⁻¹' V)) :=
        (contMDiffOn_extChartAt (I := ThreeModel) (x := p)).comp contMDiff_snd.contMDiffOn
          (fun _ hq => by
            rw [← extChartAt_source (I := ThreeModel) (x := p)]
            exact hq.2.1)
      have hc : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ × ThreeSpace) ∞
          (fun q : ℝ × P.Carrier => (q.1 - a, c q.2))
          ((Set.univ : Set ℝ) ×ˢ (c.source ∩ c ⁻¹' V)) :=
        ((contMDiff_fst.sub contMDiff_const).contMDiffOn).prodMk_space hct
      exact hfe.comp hc (fun q hq => ⟨mem_univ _, hq.2.2⟩)
    · intro s hs x hx
      have hsV : s - a ∈ Icc 0 (b - a) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h1 : fext (s - a) (c x) = (g (a + (s - a))).inner (c.symm (c x))
          (P.chartVector p (c.symm (c x)) i) (P.chartVector p (c.symm (c x)) j) :=
        heq (s - a) hsV (c x) (hVV₀ hx.2)
      change fext (s - a) (c x) =
        (g s).inner x (P.chartVector p x i) (P.chartVector p x j)
      rw [h1, show a + (s - a) = s by ring, c.left_inv hx.1]
  choose U A hUopen hpU hUbase hA hAeq using hpiece
  have hWopen : IsOpen (⋂ i : Fin 3, ⋂ j : Fin 3, U i j) :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hUopen i j
  have hpW : p ∈ ⋂ i : Fin 3, ⋂ j : Fin 3, U i j :=
    mem_iInter.mpr fun i => mem_iInter.mpr fun j => hpU i j
  have hWsub : ∀ i j : Fin 3, (⋂ i : Fin 3, ⋂ j : Fin 3, U i j) ⊆ U i j := by
    intro i j x hx
    exact (mem_iInter.mp (mem_iInter.mp hx i)) j
  refine ⟨⋂ i : Fin 3, ⋂ j : Fin 3, U i j, hWopen, hpW,
    fun x hx => hUbase 0 0 (hWsub 0 0 hx), Set.univ, isOpen_univ, mem_univ t,
    fun q i j => A i j q, ?_, ?_⟩
  · intro i j
    exact (hA i j).mono (Set.prod_mono Subset.rfl (hWsub i j))
  · intro s hs x hx i j
    exact hAeq i j s hs.2 x (hWsub i j hx)

end OrientedThreeStage

namespace OrientedThreeStage.ClosedSlab

variable {P : OrientedThreeStage.{u}}

def ofClosedOpen (P : OrientedThreeStage.{u}) {a b d : ℝ} (had : a < d)
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) (RealTimeInterval.closedOpen a d had))
    (hS : IsSolutionOn (I := ThreeModel) S)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × P.Carrier => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (Ico a d ×ˢ (Set.univ : Set P.Carrier)))
    (hab : a < b) (hbd : b < d) : P.ClosedSlab a b := by
  refine ⟨hab, S.timeRestrict (RealTimeInterval.closed a b hab.le), ?_, ?_⟩
  · exact isSolutionOn_timeRestrict hS
      (fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hbd⟩)
      (fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hbd.le⟩)
  · exact MetricSmoothUpTo.of_contMDiffOn_Ico P S.base.metric hab hbd hg

end OrientedThreeStage.ClosedSlab

namespace OrientedThreeStage.IncomingSlab

def ofClosedOpen (P : OrientedThreeStage.{u}) {a s d : ℝ} (had : a < d)
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) (RealTimeInterval.closedOpen a d had))
    (hS : IsSolutionOn (I := ThreeModel) S)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × P.Carrier => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (Ico a d ×ˢ (Set.univ : Set P.Carrier)))
    (has : a < s) (hsd : s < d) : P.IncomingSlab a s := by
  refine ⟨has, S.timeRestrict (RealTimeInterval.closedOpen a s has), ?_, ?_⟩
  · exact isSolutionOn_timeRestrict hS
      (fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hsd.le⟩)
      (fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hsd.le⟩)
  · exact MetricSmoothUpTo.mono (MetricSmoothUpTo.of_contMDiffOn_Ico P S.base.metric has hsd hg)
      (fun t ht => ⟨ht.1, ht.2.le⟩)

end OrientedThreeStage.IncomingSlab

theorem exists_closedSlab_of_metric (P : OrientedThreeStage.{u}) (g : P.Metric) (a : ℝ) :
    ∃ b : ℝ, a < b ∧ ∃ S : P.ClosedSlab a b, S.flow.base.metric a = g := by
  obtain ⟨d, had, Q, hinit, -, hjoint, -⟩ :=
    exists_completeBoundedCurvatureSolutionOn_from_time_of_compact (I := ThreeModel)
      (M := P.Carrier) g a
  obtain ⟨b, hab, hbd⟩ := exists_between had
  exact ⟨b, hab,
    OrientedThreeStage.ClosedSlab.ofClosedOpen P had Q.solution Q.isSolution hjoint hab hbd,
    hinit⟩

theorem exists_incomingSlab_of_metric (P : OrientedThreeStage.{u}) (g : P.Metric) (a : ℝ) :
    ∃ s : ℝ, a < s ∧ Nonempty (P.IncomingSlab a s) := by
  obtain ⟨d, had, Q, -, -, hjoint, -⟩ :=
    exists_completeBoundedCurvatureSolutionOn_from_time_of_compact (I := ThreeModel)
      (M := P.Carrier) g a
  obtain ⟨s, has, hsd⟩ := exists_between had
  exact ⟨s, has,
    ⟨OrientedThreeStage.IncomingSlab.ofClosedOpen P had Q.solution Q.isSolution hjoint has
      hsd⟩⟩

def threeSphereStage : OrientedThreeStage where
  Carrier := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
  orientation :=
    TangentOrientationSection.ofManifoldOrientation (sphereOrientation 3 (by decide))

theorem nonempty_threeSphereStage : Nonempty threeSphereStage.Carrier := by
  change Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
  refine Set.nonempty_coe_sort.mpr ?_
  exact (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 4))) (r := 1)).mpr
    (by norm_num)

theorem exists_closedSlab_threeSphere (a : ℝ) :
    ∃ b : ℝ, a < b ∧ Nonempty (threeSphereStage.ClosedSlab a b) := by
  obtain ⟨b, hab, S, -⟩ := exists_closedSlab_of_metric threeSphereStage
    (DifferentialGeometry.Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) a
  exact ⟨b, hab, ⟨S⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
