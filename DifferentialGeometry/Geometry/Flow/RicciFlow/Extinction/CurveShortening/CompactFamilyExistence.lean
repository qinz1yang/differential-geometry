import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.FamilyDependence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicUniqueness

section

noncomputable section

open Set Filter
open scoped ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval} {a b : ℝ}

theorem exists_continuous_compact_solution_family_of_localUniformDependence
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (hlocal : curveShorteningLocalUniformDependence (I := I) (M := M) B)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hcontinuous : @Continuous P _ inferInstance (smoothImmersionTopology e) initial) :
    ∃ d : ℝ, a < d ∧ d ≤ b ∧ ∃ solutions : P → CurveMap M,
      @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions ∧
      ∀ p, (solutions p).IsSolutionOn (I := I) B.family.metric (Icc a d) ∧
        ∀ z, solutions p z a = (initial p).map z := by
  classical
  let : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  rcases isEmpty_or_nonempty P with hP | hP
  · let := hP
    refine ⟨b, B.lt, le_rfl, (fun p => isEmptyElim p), ?_, fun p => isEmptyElim p⟩
    let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a b)
    exact continuous_of_discreteTopology
  let := hP
  choose T hTa hTb U hU hmem localSol hcont hsol hinit using
    fun p : P => exists_continuous_solution_family_on_initial_interval B hlocal e (initial p)
  let V : P → Set P := fun p => initial ⁻¹' U p
  have hVo : ∀ p, IsOpen (V p) := fun p => (hU p).preimage hcontinuous
  have hcover : (univ : Set P) ⊆ ⋃ p, V p :=
    fun p _ => mem_iUnion.mpr ⟨p, hmem p⟩
  obtain ⟨cover, hcover⟩ := isCompact_univ.elim_finite_subcover V hVo hcover
  have hcoverne : cover.Nonempty := by
    obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp (hcover (mem_univ (Classical.arbitrary P)))
    exact ⟨i, hi⟩
  let d : ℝ := (cover.image T).min' (hcoverne.image T)
  have had : a < d := by
    exact (Finset.lt_min'_iff _ _).mpr (fun z hz => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact hTa i)
  have hdT (i : P) (hi : i ∈ cover) : d ≤ T i :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hdb : d ≤ b := by
    obtain ⟨i, hi⟩ := hcoverne
    exact (hdT i hi).trans (hTb i).le
  have hselect : ∀ p : P, ∃ i, i ∈ cover ∧ p ∈ V i := by
    intro p
    obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp (hcover (mem_univ p))
    exact ⟨i, hi, hp⟩
  choose choice hchoice hmember using hselect
  let selected : P → CurveMap M := fun p => localSol (choice p) ⟨initial p, hmember p⟩
  have hselected (p : P) : (selected p).IsSolutionOn (I := I) B.family.metric (Icc a d) :=
    (hsol (choice p) ⟨initial p, hmember p⟩).mono_Icc le_rfl (hdT _ (hchoice p)) had
  have hselected_initial (p : P) (z : AddCircle (1 : ℝ)) :
      selected p z a = (initial p).map z := hinit (choice p) ⟨initial p, hmember p⟩ z
  refine ⟨d, had, hdb, selected, ?_, fun p => ⟨hselected p, hselected_initial p⟩⟩
  let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a d)
  apply continuous_iff_continuousAt.mpr
  intro p₀
  let i := choice p₀
  have hi : i ∈ cover := hchoice p₀
  have hp₀ : p₀ ∈ V i := hmember p₀
  let lift : V i → U i := fun p => ⟨initial p, p.2⟩
  have hlift : Continuous lift := (hcontinuous.comp continuous_subtype_val).subtype_mk _
  let localFamily : V i → CurveMap M := fun p => localSol i (lift p)
  have hlocalcont : Continuous localFamily := by
    have hc : @Continuous (V i) (CurveMap M) inferInstance
        (smoothCylinderTopology e (Icc a (T i))) localFamily := by
      let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a (T i))
      exact (hcont i).comp hlift
    exact smoothCylinderTopology_continuous_mono e (Icc_subset_Icc le_rfl (hdT i hi))
      (uniqueDiffOn_Icc had) (uniqueDiffOn_Icc (hTa i)) hc
      (fun p => (hsol i (lift p)).smooth)
  have hagree : ∀ p : V i, ∀ z t, t ∈ Icc a d → localFamily p z t = selected p.1 z t := by
    intro p z t ht
    exact huniq a d d le_rfl had had hdb hdb (localFamily p) (selected p.1)
      ((hsol i (lift p)).mono_Icc le_rfl (hdT i hi) had) (hselected p.1)
      (fun z => (hinit i (lift p) z).trans (hselected_initial p.1 z).symm) z t
      (by simpa only [min_self] using ht)
  have hselected_sub : ContinuousAt (selected ∘ Subtype.val : V i → CurveMap M) ⟨p₀, hp₀⟩ :=
    smoothCylinderTopology_continuousAt_congr e hagree hlocalcont.continuousAt
  exact (hVo i).isOpenEmbedding_subtypeVal.continuousAt_iff.mp hselected_sub

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
end

section

open Set
open scoped ContDiff
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval} {a b : ℝ}

theorem exists_continuous_solution_family_of_compact
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hcontinuous : @Continuous P _ inferInstance (smoothImmersionTopology e) initial) :
    ∃ d : ℝ, a < d ∧ d ≤ b ∧ ∃ solutions : P → CurveMap M,
      @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions ∧
      ∀ p, (solutions p).IsSolutionOn (I := I) B.family.metric (Icc a d) ∧
        ∀ z, solutions p z a = (initial p).map z :=
  exists_continuous_compact_solution_family_of_localUniformDependence B
    (curveShorteningLocalUniformDependence_of_compact B)
    (curveShorteningLocalUniqueness_of_compact B) e initial hcontinuous

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
