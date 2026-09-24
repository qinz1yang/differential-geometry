import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.TimeTranslation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcingContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.HigherForcingFamilies
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ForcingFamilies
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientFamilies
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.Reconstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicReconstruction
import DifferentialGeometry.Analysis.Calculus.TimeJet.FirstJetComposition
import DifferentialGeometry.Analysis.Calculus.TimeJet.MixedJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicGaugeLocalExistence
import DifferentialGeometry.Analysis.ODE.Uniqueness
import DifferentialGeometry.Analysis.Calculus.TimeJet.SpatialDerivatives
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.UniformSpace.CompactConvergence
import DifferentialGeometry.Analysis.ODE.Regularity.ScalarJetContinuity
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Families
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.LinearTimeDependentStability

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [t2M : T2Space M] [compactM : CompactSpace M]
  [nonemptyM : Nonempty M] [hBoundary : I.Boundaryless]
variable {D : RealTimeInterval} {a b : ℝ}

def CurveShorteningUniformLocalDependence
    (B : SmoothMetricWindow (I := I) (M := M) D a b) (d : ℝ) : Prop :=
  ∀ (c₀ : SmoothImmersion (I := I) (M := M)) (N : ℕ)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
    letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    ∃ U : Set (SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ c₀ ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions) ∧
        ∀ p : U, (solutions p).IsSolutionOn B.family.metric (Icc a d) ∧
          ∀ z, solutions p z a = p.1.map z

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem rfs_csf_family_dependence_of_uniformLocalDependence
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (hdep : CurveShorteningUniformLocalDependence (I := I) (M := M) B d)
    (had : a < d) (hdb : d ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc a d))
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    letI := smoothImmersionTopology e
    ∃ U : Set (SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions) ∧
        ∀ p : U, (solutions p).IsSolutionOn B.family.metric (Icc a d) ∧
          ∀ z, solutions p z a = p.1.map z := by
  let _ := hdb
  exact hdep (SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩) N e

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem curveShortening_exists_solution_of_uniformLocalDependence
    (B : SmoothMetricWindow (I := I) (M := M) D a b) {d : ℝ}
    (hdep : CurveShorteningUniformLocalDependence (I := I) (M := M) B d)
    (c₀ : SmoothImmersion (I := I) (M := M)) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    ∃ c : CurveMap M, c.IsSolutionOn B.family.metric (Icc a d) ∧ ∀ z, c z a = c₀.map z := by
  obtain ⟨U, -, hmem, sols, -, hprop⟩ := hdep c₀ N e
  exact ⟨sols ⟨c₀, hmem⟩, (hprop ⟨c₀, hmem⟩).1, (hprop ⟨c₀, hmem⟩).2⟩

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem curveShorteningUniformLocalDependence_of_isEmpty [IsEmpty M]
    (B : SmoothMetricWindow (I := I) (M := M) D a b) (d : ℝ) :
    CurveShorteningUniformLocalDependence (I := I) (M := M) B d :=
  fun c₀ _ _ => (inferInstance : IsEmpty M).elim (c₀.map 0)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem exists_left_time_mem_of_continuous
    {a T τ : ℝ} (haT : a < T) (hτ : 0 < τ)
    {X : Type*} [TopologicalSpace X] {f : Icc a T → X} (hf : Continuous f)
    {U : Set X} (hU : IsOpen U) (hmem : f ⟨T, haT.le, le_rfl⟩ ∈ U) :
    ∃ s : Icc a T, (s : ℝ) < T ∧ T < s + τ ∧ f s ∈ U := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (hf.continuousAt.preimage_mem_nhds (hU.mem_nhds hmem))
  let δ := min (min ε τ) (T - a)
  have hδ : 0 < δ := lt_min (lt_min hε hτ) (sub_pos.mpr haT)
  have hδε : δ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hδτ : δ ≤ τ := (min_le_left _ _).trans (min_le_right _ _)
  have hδa : δ ≤ T - a := min_le_right _ _
  let s : Icc a T := ⟨T - δ / 2, by constructor <;> linarith⟩
  refine ⟨s, by change T - δ / 2 < T; linarith,
    by change T < T - δ / 2 + τ; linarith, ?_⟩
  apply hεsub
  change dist (T - δ / 2) T < ε
  rw [Real.dist_eq]
  have heq : T - δ / 2 - T = -(δ / 2) := by ring
  rw [heq, abs_neg, abs_of_pos (half_pos hδ)]
  linarith

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval} {a b : ℝ}

theorem exists_continuous_solution_family_extension
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (hlocal : curveShorteningLocalUniformDependence (I := I) (M := M) B)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] {T : ℝ} (haT : a < T) (hTb : T < b)
    (f : P → CurveMap M)
    (hf : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a T)) f)
    (hsol : ∀ p, (f p).IsSolutionOn (I := I) B.family.metric (Icc a T)) (p₀ : P) :
    ∃ u : ℝ, T < u ∧ u ≤ b ∧ ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧
      ∃ solutions : V → CurveMap M,
        @Continuous V (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a u)) solutions ∧
        (∀ p, (solutions p).IsSolutionOn (I := I) B.family.metric (Icc a u)) ∧
        (∀ p z t, t ∈ Icc a T → solutions p z t = f p.1 z t) ∧
        ∀ p z, solutions p z a = f p.1 z a := by
  let : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  let timeT : {t : ℝ // t ∈ Ico a b} := ⟨T, haT.le, hTb⟩
  let cT := SmoothImmersion.slice (f p₀) (hsol p₀).smooth (hsol p₀).immersed
    T ⟨haT.le, le_rfl⟩
  obtain ⟨τ, hτ, U, hU, hmem, localSolutions, hcont, hprop⟩ := hlocal timeT cT N e
  let slices : P × Icc a T → SmoothImmersion (I := I) (M := M) := fun q =>
    SmoothImmersion.slice (f q.1) (hsol q.1).smooth (hsol q.1).immersed q.2 q.2.2
  have hslices : Continuous slices :=
    continuous_iff_continuousAt.mpr fun q => continuousAt_slice_smoothImmersion e haT hf
      (fun p => (hsol p).smooth) (fun p => (hsol p).immersed) q
  let ref : Icc a T → {t : ℝ // t ∈ Ico a b} × SmoothImmersion (I := I) (M := M) :=
    fun t => (⟨t, t.2.1, t.2.2.trans_lt hTb⟩, slices (p₀, t))
  have href : Continuous ref := by
    apply Continuous.prodMk
    · exact continuous_subtype_val.subtype_mk _
    · exact hslices.comp (continuous_const.prodMk continuous_id)
  obtain ⟨s, hsT, hTend, hsU⟩ :=
    exists_left_time_mem_of_continuous haT hτ href hU hmem
  let restart : P → {t : ℝ // t ∈ Ico a b} × SmoothImmersion (I := I) (M := M) :=
    fun p => (⟨s, s.2.1, s.2.2.trans_lt hTb⟩, slices (p, s))
  have hrestart : Continuous restart :=
    continuous_const.prodMk (hslices.comp (continuous_id.prodMk continuous_const))
  let V : Set P := restart ⁻¹' U
  have hV : IsOpen V := hU.preimage hrestart
  have hpV : p₀ ∈ V := hsU
  let restartU : V → U := fun p => ⟨restart p.1, p.2⟩
  have hrestartU : Continuous restartU :=
    (hrestart.comp continuous_subtype_val).subtype_mk _
  let raw : V → CurveMap M := fun p => localSolutions (restartU p)
  have hraw : @Continuous V (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc 0 τ)) raw := by
    let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc 0 τ)
    exact hcont.comp hrestartU
  let right : V → CurveMap M := fun p z t => raw p z (t + -(s : ℝ))
  have hright : @Continuous V (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc (s : ℝ) ((s : ℝ) + τ))) right := by
    apply smoothCylinderTopology_continuous_time_translate e (s : ℝ) ((s : ℝ) + τ) (-(s : ℝ))
    have hzero : (s : ℝ) + -(s : ℝ) = 0 := by ring
    have hend : (s : ℝ) + τ + -(s : ℝ) = τ := by ring
    rw [hzero, hend]
    exact hraw
  have hrightsol (p : V) : (right p).IsSolutionOn (I := I) B.family.metric
      (Icc (s : ℝ) ((s : ℝ) + τ)) := by
    have hrawsol := (hprop (restartU p)).2.1
    have hmap : MapsTo (fun t : ℝ => t + -(s : ℝ))
        (Icc (s : ℝ) ((s : ℝ) + τ)) (Icc 0 τ) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hshift := hrawsol.time_translate (-(s : ℝ)) hmap
      (uniqueDiffOn_Icc (by linarith : (s : ℝ) < (s : ℝ) + τ))
    change (right p).IsSolutionOn
      (fun t => B.family.metric ((s : ℝ) + (t + -(s : ℝ)))) _ at hshift
    have hmetric : (fun t => B.family.metric ((s : ℝ) + (t + -(s : ℝ)))) =
        B.family.metric := by
      funext t
      congr 1
      ring
    rw [hmetric] at hshift
    exact hshift
  have hrightinit (p : V) (z : AddCircle (1 : ℝ)) : right p z s = f p.1 z s := by
    change localSolutions (restartU p) z ((s : ℝ) + -(s : ℝ)) = _
    rw [add_neg_cancel]
    exact (hprop (restartU p)).2.2 z
  have hbound : (s : ℝ) + τ ≤ b := (hprop (restartU ⟨p₀, hpV⟩)).1
  have hleftsol (p : V) : (f p.1).IsSolutionOn (I := I) B.family.metric (Icc a T) := hsol p.1
  have hagree (p : V) (z : AddCircle (1 : ℝ)) (t : ℝ) (ht : t ∈ Icc (s : ℝ) T) :
      f p.1 z t = right p z t := by
    have heq := huniq (s : ℝ) T ((s : ℝ) + τ) s.2.1 hsT
      (by linarith) hTb.le hbound (f p.1) (right p)
      ((hsol p.1).mono_Icc s.2.1 le_rfl hsT) (hrightsol p)
      (fun z => (hrightinit p z).symm) z t
    exact heq (by simpa only [min_eq_left hTend.le] using ht)
  have hleft : @Continuous V (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc a T)) (fun p : V => f p.1) := by
    let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a T)
    exact hf.comp continuous_subtype_val
  obtain ⟨hgluecont, hgluesol, hglueleft, hglueinitial⟩ :=
    continuous_solution_family_glue e s.2.1 hsT hTend hleft hright hleftsol hrightsol hagree
  exact ⟨(s : ℝ) + τ, hTend, hbound, V, hV, hpV, _,
    hgluecont, hgluesol, hglueleft, hglueinitial⟩

theorem exists_continuous_solution_family_on_initial_interval
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (hlocal : curveShorteningLocalUniformDependence (I := I) (M := M) B)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (c₀ : SmoothImmersion (I := I) (M := M)) :
    let _ : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    ∃ T : ℝ, a < T ∧ T < b ∧
      ∃ U : Set (SmoothImmersion (I := I) (M := M)), IsOpen U ∧ c₀ ∈ U ∧
        ∃ solutions : U → CurveMap M,
          @Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a T)) solutions ∧
          (∀ p, (solutions p).IsSolutionOn (I := I) B.family.metric (Icc a T)) ∧
          ∀ p z, solutions p z a = p.1.map z := by
  let : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  let start : {t : ℝ // t ∈ Ico a b} := ⟨a, le_rfl, B.lt⟩
  obtain ⟨τ, hτ, U, hU, hmem, localSolutions, hcont, hprop⟩ := hlocal start c₀ N e
  let inclusion : SmoothImmersion (I := I) (M := M) →
      {t : ℝ // t ∈ Ico a b} × SmoothImmersion (I := I) (M := M) := fun p => (start, p)
  have hinclusion : Continuous inclusion := continuous_const.prodMk continuous_id
  let V := inclusion ⁻¹' U
  have hV : IsOpen V := hU.preimage hinclusion
  have hcV : c₀ ∈ V := hmem
  let lift : V → U := fun p => ⟨inclusion p.1, p.2⟩
  have hlift : Continuous lift := (hinclusion.comp continuous_subtype_val).subtype_mk _
  let raw : V → CurveMap M := localSolutions ∘ lift
  have hraw : @Continuous V (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc 0 τ)) raw := by
    let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc 0 τ)
    exact hcont.comp hlift
  let solutions : V → CurveMap M := fun p z t => raw p z (t + -a)
  have hsolutions : @Continuous V (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc a (a + τ))) solutions := by
    apply smoothCylinderTopology_continuous_time_translate e a (a + τ) (-a)
    have hend : a + τ + -a = τ := by ring
    rw [add_neg_cancel, hend]
    exact hraw
  have hsol (p : V) : (solutions p).IsSolutionOn (I := I) B.family.metric (Icc a (a + τ)) := by
    have hmap : MapsTo (fun t : ℝ => t + -a) (Icc a (a + τ)) (Icc 0 τ) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hshift := (hprop (lift p)).2.1.time_translate (-a) hmap
      (uniqueDiffOn_Icc (by linarith : a < a + τ))
    change (solutions p).IsSolutionOn (fun t => B.family.metric (a + (t + -a))) _ at hshift
    have hmetric : (fun t => B.family.metric (a + (t + -a))) = B.family.metric := by
      funext t
      congr 1
      ring
    rw [hmetric] at hshift
    exact hshift
  have hbound : a + τ ≤ b := (hprop (lift ⟨c₀, hcV⟩)).1
  have haT : a < a + τ / 2 := by linarith
  refine ⟨a + τ / 2, haT, by linarith, V, hV, hcV, solutions, ?_, ?_, ?_⟩
  · exact smoothCylinderTopology_continuous_mono e
      (Icc_subset_Icc le_rfl (by linarith : a + τ / 2 ≤ a + τ))
      (uniqueDiffOn_Icc haT) (uniqueDiffOn_Icc (by linarith : a < a + τ)) hsolutions
      (fun p => (hsol p).smooth)
  · intro p
    exact (hsol p).mono_Icc le_rfl (by linarith) haT
  · intro p z
    change localSolutions (lift p) z (a + -a) = p.1.map z
    rw [add_neg_cancel]
    exact (hprop (lift p)).2.2 z

theorem isOpen_setOf_exists_continuous_solution_family
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (hlocal : curveShorteningLocalUniformDependence (I := I) (M := M) B)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (c₀ : SmoothImmersion (I := I) (M := M)) :
    let _ : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    IsOpen {T : ℝ | a < T ∧ T < b ∧
      ∃ U : Set (SmoothImmersion (I := I) (M := M)), IsOpen U ∧ c₀ ∈ U ∧
        ∃ solutions : U → CurveMap M,
          @Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a T)) solutions ∧
          (∀ p, (solutions p).IsSolutionOn (I := I) B.family.metric (Icc a T)) ∧
          ∀ p z, solutions p z a = p.1.map z} := by
  let : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  rw [isOpen_iff_mem_nhds]
  rintro T ⟨haT, hTb, U, hU, hc₀, f, hf, hsol, hinit⟩
  obtain ⟨u, hTu, hub, V, hV, hpV, solutions, hcont, hsolutions, hagree, htrace⟩ :=
    exists_continuous_solution_family_extension B hlocal huniq e haT hTb f hf hsol ⟨c₀, hc₀⟩
  obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.mp hV
  let Z := U ∩ W
  have hZ : IsOpen Z := hU.inter hW
  have hcZ : c₀ ∈ Z := by
    refine ⟨hc₀, ?_⟩
    have hcW : (⟨c₀, hc₀⟩ : U) ∈ Subtype.val ⁻¹' W := by
      rw [hWV]
      exact hpV
    exact hcW
  let inclusion : Z → U := fun p => ⟨p.1, p.2.1⟩
  have hinclusion : Continuous inclusion := continuous_subtype_val.subtype_mk _
  have hmem (p : Z) : inclusion p ∈ V := by
    rw [← hWV]
    exact p.2.2
  let lift : Z → V := fun p => ⟨inclusion p, hmem p⟩
  have hlift : Continuous lift := hinclusion.subtype_mk _
  let extended : Z → CurveMap M := solutions ∘ lift
  have hextended : @Continuous Z (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc a u)) extended := by
    let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a u)
    exact hcont.comp hlift
  have hextsol (p : Z) : (extended p).IsSolutionOn (I := I) B.family.metric (Icc a u) :=
    hsolutions (lift p)
  have hextinit (p : Z) (z : AddCircle (1 : ℝ)) : extended p z a = p.1.map z :=
    (htrace (lift p) z).trans (hinit (inclusion p) z)
  apply mem_of_superset (Ioo_mem_nhds haT hTu)
  intro S hS
  refine ⟨hS.1, hS.2.trans_le hub, Z, hZ, hcZ, extended, ?_, ?_, hextinit⟩
  · exact smoothCylinderTopology_continuous_mono e (Icc_subset_Icc le_rfl hS.2.le)
      (uniqueDiffOn_Icc hS.1) (uniqueDiffOn_Icc (haT.trans hTu)) hextended
      (fun p => (hextsol p).smooth)
  · intro p
    exact (hextsol p).mono_Icc le_rfl hS.2.le hS.1

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end


noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening


variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval} {a b : ℝ}

private theorem exists_family_extension_of_local_family
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] {T τ : ℝ} (haT : a < T) (hTb : T < b)
    (f : P → CurveMap M)
    (hf : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a T)) f)
    (hsol : ∀ p, (f p).IsSolutionOn (I := I) B.family.metric (Icc a T)) (p₀ : P)
    (s : Icc a T) (hsT : (s : ℝ) < T) (hTend : T < s + τ) :
    let _ : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    ∀ (U : Set ({t : ℝ // t ∈ Ico a b} × SmoothImmersion (I := I) (M := M))),
      IsOpen U →
      (⟨s, s.2.1, s.2.2.trans_lt hTb⟩,
        SmoothImmersion.slice (f p₀) (hsol p₀).smooth (hsol p₀).immersed s s.2) ∈ U →
      ∀ localSolutions : U → CurveMap M,
      @Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc 0 τ)) localSolutions →
      (∀ p : U, (p.1.1 : ℝ) + τ ≤ b ∧
        (localSolutions p).IsSolutionOn (fun v => B.family.metric ((p.1.1 : ℝ) + v)) (Icc 0 τ) ∧
        ∀ z, localSolutions p z 0 = p.1.2.map z) →
      (s : ℝ) + τ ≤ b ∧ ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧
        ∃ solutions : V → CurveMap M,
          @Continuous V (CurveMap M) inferInstance
            (smoothCylinderTopology e (Icc a ((s : ℝ) + τ))) solutions ∧
          (∀ p, (solutions p).IsSolutionOn (I := I) B.family.metric (Icc a ((s : ℝ) + τ))) ∧
          (∀ p z t, t ∈ Icc a T → solutions p z t = f p.1 z t) ∧
          ∀ p z, solutions p z a = f p.1 z a := by
  let : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  dsimp only
  intro U hU hsU localSolutions hcont hprop
  let slices : P × Icc a T → SmoothImmersion (I := I) (M := M) := fun q =>
    SmoothImmersion.slice (f q.1) (hsol q.1).smooth (hsol q.1).immersed q.2 q.2.2
  have hslices : Continuous slices :=
    continuous_iff_continuousAt.mpr fun q => continuousAt_slice_smoothImmersion e haT hf
      (fun p => (hsol p).smooth) (fun p => (hsol p).immersed) q
  let restart : P → {t : ℝ // t ∈ Ico a b} × SmoothImmersion (I := I) (M := M) :=
    fun p => (⟨s, s.2.1, s.2.2.trans_lt hTb⟩, slices (p, s))
  have hrestart : Continuous restart :=
    continuous_const.prodMk (hslices.comp (continuous_id.prodMk continuous_const))
  let V : Set P := restart ⁻¹' U
  have hV : IsOpen V := hU.preimage hrestart
  have hpV : p₀ ∈ V := hsU
  let restartU : V → U := fun p => ⟨restart p.1, p.2⟩
  have hrestartU : Continuous restartU :=
    (hrestart.comp continuous_subtype_val).subtype_mk _
  let raw : V → CurveMap M := fun p => localSolutions (restartU p)
  have hraw : @Continuous V (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc 0 τ)) raw := by
    let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc 0 τ)
    exact hcont.comp hrestartU
  let right : V → CurveMap M := fun p z t => raw p z (t + -(s : ℝ))
  have hright : @Continuous V (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc (s : ℝ) ((s : ℝ) + τ))) right := by
    apply smoothCylinderTopology_continuous_time_translate e (s : ℝ) ((s : ℝ) + τ) (-(s : ℝ))
    have hzero : (s : ℝ) + -(s : ℝ) = 0 := by ring
    have hend : (s : ℝ) + τ + -(s : ℝ) = τ := by ring
    rw [hzero, hend]
    exact hraw
  have hrightsol (p : V) : (right p).IsSolutionOn (I := I) B.family.metric
      (Icc (s : ℝ) ((s : ℝ) + τ)) := by
    have hrawsol := (hprop (restartU p)).2.1
    have hmap : MapsTo (fun t : ℝ => t + -(s : ℝ))
        (Icc (s : ℝ) ((s : ℝ) + τ)) (Icc 0 τ) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hshift := hrawsol.time_translate (-(s : ℝ)) hmap
      (uniqueDiffOn_Icc (by linarith : (s : ℝ) < (s : ℝ) + τ))
    change (right p).IsSolutionOn
      (fun t => B.family.metric ((s : ℝ) + (t + -(s : ℝ)))) _ at hshift
    have hmetric : (fun t => B.family.metric ((s : ℝ) + (t + -(s : ℝ)))) =
        B.family.metric := by
      funext t
      congr 1
      ring
    rw [hmetric] at hshift
    exact hshift
  have hrightinit (p : V) (z : AddCircle (1 : ℝ)) : right p z s = f p.1 z s := by
    change localSolutions (restartU p) z ((s : ℝ) + -(s : ℝ)) = _
    rw [add_neg_cancel]
    exact (hprop (restartU p)).2.2 z
  have hbound : (s : ℝ) + τ ≤ b := (hprop (restartU ⟨p₀, hpV⟩)).1
  have hleftsol (p : V) : (f p.1).IsSolutionOn (I := I) B.family.metric (Icc a T) := hsol p.1
  have hagree (p : V) (z : AddCircle (1 : ℝ)) (t : ℝ) (ht : t ∈ Icc (s : ℝ) T) :
      f p.1 z t = right p z t := by
    have heq := huniq (s : ℝ) T ((s : ℝ) + τ) s.2.1 hsT
      (by linarith) hTb.le hbound (f p.1) (right p)
      ((hsol p.1).mono_Icc s.2.1 le_rfl hsT) (hrightsol p)
      (fun z => (hrightinit p z).symm) z t
    exact heq (by simpa only [min_eq_left hTend.le] using ht)
  have hleft : @Continuous V (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc a T)) (fun p : V => f p.1) := by
    let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a T)
    exact hf.comp continuous_subtype_val
  obtain ⟨hgluecont, hgluesol, hglueleft, hglueinitial⟩ :=
    continuous_solution_family_glue e s.2.1 hsT hTend hleft hright hleftsol hrightsol hagree
  exact ⟨hbound, V, hV, hpV, _,
    hgluecont, hgluesol, hglueleft, hglueinitial⟩
theorem exists_continuous_solution_family_of_reference_solution
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (hlocal : curveShorteningLocalUniformDependence (I := I) (M := M) B)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B)
    {d : ℝ} (had : a < d) (hdb : d < b)
    (c : CurveMap M) (hc : c.IsSolutionOn (I := I) B.family.metric (Icc a d))
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    let _ : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    ∃ U : Set (SmoothImmersion (I := I) (M := M)), IsOpen U ∧
      SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ ∈ U ∧
      ∃ solutions : U → CurveMap M,
        @Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions ∧
        (∀ p, (solutions p).IsSolutionOn (I := I) B.family.metric (Icc a d)) ∧
        ∀ p z, solutions p z a = p.1.map z := by
  let : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  let c₀ := SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩
  let F : ℝ → Prop := fun T =>
    ∃ U : Set (SmoothImmersion (I := I) (M := M)), IsOpen U ∧ c₀ ∈ U ∧
      ∃ f : U → CurveMap M,
        @Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a T)) f ∧
        (∀ p, (f p).IsSolutionOn (I := I) B.family.metric (Icc a T)) ∧
        ∀ p z, f p z a = p.1.map z
  have hmono {T u : ℝ} (haT : a < T) (hTu : T ≤ u) (hFu : F u) : F T := by
    obtain ⟨U, hU, hmem, f, hf, hsol, hinit⟩ := hFu
    refine ⟨U, hU, hmem, f, ?_, ?_, hinit⟩
    · exact smoothCylinderTopology_continuous_mono e (Icc_subset_Icc le_rfl hTu)
        (uniqueDiffOn_Icc haT) (uniqueDiffOn_Icc (haT.trans_le hTu)) hf
        (fun p => (hsol p).smooth)
    · intro p
      exact (hsol p).mono_Icc le_rfl hTu haT
  let A : Set ℝ := {T | a < T ∧ T ≤ d ∧ F T}
  obtain ⟨T₀, haT₀, _, hF₀⟩ := exists_continuous_solution_family_on_initial_interval B hlocal e c₀
  have haMin : a < min T₀ d := lt_min haT₀ had
  have hA : A.Nonempty :=
    ⟨min T₀ d, haMin, min_le_right _ _, hmono haMin (min_le_left _ _) hF₀⟩
  have hAbdd : BddAbove A := ⟨d, fun _ hT => hT.2.1⟩
  let S := sSup A
  have hSd : S ≤ d := csSup_le hA (fun _ hT => hT.2.1)
  have haS : a < S := haMin.trans_le (le_csSup hAbdd
    ⟨haMin, min_le_right _ _, hmono haMin (min_le_left _ _) hF₀⟩)
  have hSb : S < b := hSd.trans_lt hdb
  let cS := SmoothImmersion.slice c hc.smooth hc.immersed S ⟨haS.le, hSd⟩
  let timeS : {t : ℝ // t ∈ Ico a b} := ⟨S, haS.le, hSb⟩
  obtain ⟨τ, hτ, U, hU, hmem, localSolutions, hcont, hprop⟩ := hlocal timeS cS N e
  have hconstant : @Continuous Unit (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc a d)) (fun _ => c) := by
    let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a d)
    exact continuous_const
  have hslices : Continuous (fun q : Unit × Icc a d =>
      SmoothImmersion.slice c hc.smooth hc.immersed q.2 q.2.2) :=
    continuous_iff_continuousAt.mpr fun q => continuousAt_slice_smoothImmersion e had hconstant
      (fun _ => hc.smooth) (fun _ => hc.immersed) q
  let ref : Icc a S → {t : ℝ // t ∈ Ico a b} × SmoothImmersion (I := I) (M := M) :=
    fun t => (⟨t, t.2.1, t.2.2.trans_lt hSb⟩,
      SmoothImmersion.slice c hc.smooth hc.immersed t ⟨t.2.1, t.2.2.trans hSd⟩)
  have href : Continuous ref := by
    apply Continuous.prodMk
    · exact continuous_subtype_val.subtype_mk _
    · have hinto : Continuous (fun t : Icc a S =>
          ((), (⟨t, t.2.1, t.2.2.trans hSd⟩ : Icc a d))) :=
        continuous_const.prodMk (continuous_subtype_val.subtype_mk _)
      exact hslices.comp hinto
  obtain ⟨s, hsS, hSend, hsU⟩ :=
    exists_left_time_mem_of_continuous haS hτ href hU hmem
  obtain ⟨T, hTA, hsT⟩ := exists_lt_of_lt_csSup hA hsS
  obtain ⟨haT, hTd, Vf, hVf, hcf, f, hf, hsol, hinit⟩ := hTA
  have hTS : T ≤ S := le_csSup hAbdd (by exact ⟨haT, hTd, Vf, hVf, hcf, f, hf, hsol, hinit⟩)
  let p₀ : Vf := ⟨c₀, hcf⟩
  have hcenter (z : AddCircle (1 : ℝ)) (t : ℝ) (ht : t ∈ Icc a T) :
      f p₀ z t = c z t := by
    apply huniq a T d le_rfl haT had (hTd.trans hdb.le) hdb.le
      (f p₀) c (hsol p₀) hc (fun z => hinit p₀ z) z t
    simpa only [min_eq_left hTd] using ht
  let sT : Icc a T := ⟨s, s.2.1, hsT.le⟩
  have hsTU :
      (⟨sT, sT.2.1, sT.2.2.trans_lt (hTd.trans_lt hdb)⟩,
        SmoothImmersion.slice (f p₀) (hsol p₀).smooth (hsol p₀).immersed sT sT.2) ∈ U := by
    have heq : SmoothImmersion.slice (f p₀) (hsol p₀).smooth (hsol p₀).immersed sT sT.2 =
        SmoothImmersion.slice c hc.smooth hc.immersed s ⟨s.2.1, s.2.2.trans hSd⟩ := by
      apply (SmoothImmersion.mk.injEq _ _ _ _ _ _).mpr
      exact funext fun z => hcenter z s ⟨s.2.1, hsT.le⟩
    rw [heq]
    exact hsU
  have hTend : T < (sT : ℝ) + τ := hTS.trans_lt hSend
  obtain ⟨hub, V, hV, hpV, solutions, hcont', hsolutions, _, htrace⟩ :=
    exists_family_extension_of_local_family B huniq e haT (hTd.trans_lt hdb)
      f hf hsol p₀ sT hsT hTend U hU hsTU localSolutions hcont hprop
  obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.mp hV
  let Z := Vf ∩ W
  have hZ : IsOpen Z := hVf.inter hW
  have hcZ : c₀ ∈ Z := by
    refine ⟨hcf, ?_⟩
    have hcW : (⟨c₀, hcf⟩ : Vf) ∈ Subtype.val ⁻¹' W := by
      rw [hWV]
      exact hpV
    exact hcW
  let inclusion : Z → Vf := fun p => ⟨p.1, p.2.1⟩
  have hinclusion : Continuous inclusion := continuous_subtype_val.subtype_mk _
  have hmember (p : Z) : inclusion p ∈ V := by
    rw [← hWV]
    exact p.2.2
  let lift : Z → V := fun p => ⟨inclusion p, hmember p⟩
  have hlift : Continuous lift := hinclusion.subtype_mk _
  let extended : Z → CurveMap M := solutions ∘ lift
  have hextended : @Continuous Z (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc a ((sT : ℝ) + τ))) extended := by
    let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a ((sT : ℝ) + τ))
    exact hcont'.comp hlift
  have hFend : F ((sT : ℝ) + τ) :=
    ⟨Z, hZ, hcZ, extended, hextended, fun p => hsolutions (lift p),
      fun p z => (htrace (lift p) z).trans (hinit (inclusion p) z)⟩
  have hdend : d ≤ (sT : ℝ) + τ := by
    by_contra hn
    have hmemA : (sT : ℝ) + τ ∈ A := ⟨haT.trans hTend, (not_le.mp hn).le, hFend⟩
    have hle : (sT : ℝ) + τ ≤ S := le_csSup hAbdd hmemA
    exact (not_lt_of_ge hle) hSend
  exact hmono had hdend hFend

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval} {a b : ℝ}

theorem rfs_csf_family_dependence_of_localUniformDependence
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (hlocal : ∀ b' : ℝ, ∀ B' : SmoothMetricWindow (I := I) (M := M) D a b',
      B'.family = B.family →
        curveShorteningLocalUniformDependence (I := I) (M := M) B')
    (huniq : ∀ b' : ℝ, ∀ B' : SmoothMetricWindow (I := I) (M := M) D a b',
      B'.family = B.family →
        curveShorteningLocalUniqueness (I := I) (M := M) B')
    {d : ℝ} (had : a < d) (hdb : d ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn (I := I) B.family.metric (Icc a d))
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    let _ : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    ∃ U : Set (SmoothImmersion (I := I) (M := M)), IsOpen U ∧
      SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ ∈ U ∧
      ∃ solutions : U → CurveMap M,
        @Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions ∧
        ∀ p, (solutions p).IsSolutionOn (I := I) B.family.metric (Icc a d) ∧
          ∀ z, solutions p z a = p.1.map z := by
  let : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  obtain ⟨b', hbb', B', hfamily⟩ := B.exists_right_extension
  have hc' : c.IsSolutionOn (I := I) B'.family.metric (Icc a d) := by
    rw [hfamily]
    exact hc
  obtain ⟨U, hU, hmem, solutions, hcont, hsol, hinit⟩ :=
    exists_continuous_solution_family_of_reference_solution
      B' (hlocal b' B' hfamily) (huniq b' B' hfamily) had (hdb.trans_lt hbb') c hc' e
  refine ⟨U, hU, hmem, solutions, hcont, ?_⟩
  intro p
  refine ⟨?_, hinit p⟩
  rw [← hfamily]
  exact hsol p

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

section

noncomputable section

open Set
open scoped _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem exists_uniform_initial_time_neighborhood
    {C : Type*} [TopologicalSpace C] {a b : ℝ}
    (t₀ : {t : ℝ // t ∈ Ico a b}) (c₀ : C)
    {ρ T₀ : ℝ} (hρ : 0 < ρ) (hT₀ : 0 < T₀)
    {V : Set C} (hV : IsOpen V) (hc₀ : c₀ ∈ V) :
    ∃ T : ℝ, 0 < T ∧ T ≤ T₀ ∧ T ≤ ρ / 4 ∧
      ∃ U : Set ({t : ℝ // t ∈ Ico a b} × C),
        IsOpen U ∧ (t₀, c₀) ∈ U ∧
        ∃ pull : U → Ioo (-ρ / 4) (ρ / 4) × V,
          Continuous pull ∧
          (∀ p : U, (pull p).1.val = p.val.1.val - t₀.val) ∧
          (∀ p : U, (pull p).2.val = p.val.2) ∧
          (∀ p : U, p.val.1.val + T ≤ b) ∧
          ∀ p : U, -ρ ≤ (pull p).1.val ∧ (pull p).1.val + T ≤ ρ := by
  let θ := min (ρ / 4) ((b - t₀.val) / 2)
  have hθ : 0 < θ := lt_min (by linarith) (by linarith [t₀.property.2])
  have hθρ : θ ≤ ρ / 4 := min_le_left _ _
  have hθb : θ ≤ (b - t₀.val) / 2 := min_le_right _ _
  let T := min T₀ θ
  have hT : 0 < T := lt_min hT₀ hθ
  have hTT₀ : T ≤ T₀ := min_le_left _ _
  have hTθ : T ≤ θ := min_le_right _ _
  let shift : ({t : ℝ // t ∈ Ico a b} × C) → ℝ := fun p => p.1.val - t₀.val
  have hshift : Continuous shift := by fun_prop
  let U : Set ({t : ℝ // t ∈ Ico a b} × C) :=
    shift ⁻¹' Ioo (-θ) θ ∩ Prod.snd ⁻¹' V
  have hU : IsOpen U :=
    (isOpen_Ioo.preimage hshift).inter (hV.preimage continuous_snd)
  have hmem : (t₀, c₀) ∈ U := by
    refine ⟨?_, hc₀⟩
    change -θ < t₀.val - t₀.val ∧ t₀.val - t₀.val < θ
    constructor <;> linarith
  let pull : U → Ioo (-ρ / 4) (ρ / 4) × V := fun p =>
    (⟨shift p.val, by
      have hp := p.property.1
      change -θ < shift p.val ∧ shift p.val < θ at hp
      constructor <;> linarith⟩,
      ⟨p.val.2, p.property.2⟩)
  have hpull : Continuous pull := by
    apply Continuous.prodMk
    · exact (hshift.comp continuous_subtype_val).subtype_mk _
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  refine ⟨T, hT, hTT₀, hTθ.trans hθρ, U, hU, hmem, pull, hpull,
    fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro p
    have hp := p.property.1.2
    change p.val.1.val - t₀.val < θ at hp
    linarith
  · intro p
    have hp := p.property.1
    change -θ < p.val.1.val - t₀.val ∧ p.val.1.val - t₀.val < θ at hp
    change -ρ ≤ p.val.1.val - t₀.val ∧ p.val.1.val - t₀.val + T ≤ ρ
    constructor <;> linarith

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

section

open private
  CircleHsPi
  circleHsPiInclusion
  circleHsPiCongr from
DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private
  circleFirstJet
  ambientSobolev
  firstJetCoordinates from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private
  fixedAmbientSobolev
  referenceCircleSolutionFacts from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
open private
  referenceCircleSymmetricCoefficientFacts from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
open private
  referenceCirclePrincipalNormBounds
  ambient_reference_translated_solutions_on_smooth_neighborhood from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
open private vectorTensorHsNormedSpace in
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.exists_uniform_time_shifted_vector

noncomputable section

open Set
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {n : ℕ}

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
attribute [local instance] vectorTensorHsNormedSpace

private theorem ambient_reference_solutions_on_initial_time_neighborhood
    (c₀ : SmoothImmersion (I := I) (M := M))
    (g : ℝ → SmoothRiemannianMetric I M) {D : RealTimeInterval} {a b : ℝ}
    (t₀ : {t : ℝ // t ∈ Ico a b}) (ht : t₀.val ∈ D.regular)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) n)
    {r : EuclideanSpace ℝ (Fin n) → M}
    {O : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ r O)
    (hEO : Set.range e.map ⊆ O) (hleft : ∀ p, r (e.map p) = p) (β : O)
    (hG : MetricFamilySmoothOn D
      (fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr)) :
    let gshift : ℝ → SmoothRiemannianMetric I M := fun s => g (t₀.val + s)
    let _ := smoothImmersionTopology e
    let f₀ : CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) :=
      ambientSobolev c₀ (gshift 0) e.map e.smooth (((1 : ℕ) : ℝ) + 2)
    let J₀ : CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (1 + 1) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n ⊕ Fin n) 1 := circleFirstJet (ι := Fin n)
        (c₀.pullbackMetric (gshift 0))
    let K₀ : CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (1 + 1) := ContinuousLinearMap.piLpMap 2
        (fun _ : Fin n =>
      tensorHsInclusion (g := (c₀.pullbackMetric (gshift 0))) (r := 0) (s := 0)
        (show (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num))
    let P : CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (((1 : ℕ) : ℝ) + 2) →L[ℝ]
      CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n ⊕ Fin n) 1  := J₀.comp K₀
    let J := J₀.comp (circleHsPiCongr (c₀.pullbackMetric (gshift 0)) (Fin n)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion (c₀.pullbackMetric (gshift 0)) (Fin n)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by norm_num)
    let F := curveShorteningChartDiffusionCoefficient
      (fun t => Geometry.Riemannian.retractionMetric (gshift t) e.smooth hr) β ∘
        firstJetCoordinates n
    let G := fun z j => curveShorteningParametricChartReaction
      (fun t => Geometry.Riemannian.retractionMetric (gshift t) e.smooth hr) β
        (firstJetCoordinates n z) j
    let S := firstJetCoordinates n ⁻¹' curveShorteningChartFirstJetDomain (D.timeShift t₀.val)
      (fun t => Geometry.Riemannian.retractionMetric (gshift t) e.smooth hr) β
    (∀ f v, P f + J (K v) = P (f + v)) ∧
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∃ alpha : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) → TensorHs
          (c₀.pullbackMetric (gshift 0)) 0 0 1,
      ∃ reaction : Metric.closedBall f₀ δ → ℝ →
        CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) (((1 : ℕ) : ℝ) + 1) →
          CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) 1,
      referenceCircleSymmetricCoefficientFacts (c₀.pullbackMetric (gshift 0)) f₀ P J F G S δ ρ
        alpha reaction ∧
      referenceCirclePrincipalNormBounds (n := n) (c₀.pullbackMetric (gshift 0)) ρ alpha ∧
      ∃ (T : ℝ) (hT : 0 < T), T ≤ ρ / 4 ∧
        ∃ U : Set ({t : ℝ // t ∈ Ico a b} × SmoothImmersion (I := I) (M := M)),
          IsOpen U ∧ (t₀, c₀) ∈ U ∧
          ∃ f : U → Metric.closedBall f₀ δ,
            (∀ p : U, (f p).val =
              fixedAmbientSobolev e (c₀.pullbackMetric (gshift 0)) p.val.2) ∧
            ∃ (u : U →
                timeH1 (CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) ((1 : ℕ) : ℝ)) T)
              (gforce : U →
                timeL2 (CircleHsPi (c₀.pullbackMetric (gshift 0)) (Fin n) ((1 : ℕ) : ℝ)) T),
              Continuous u ∧ Continuous gforce ∧
              (∀ p : U, p.val.1.val + T ≤ b) ∧
              (∀ p : U, -ρ ≤ p.val.1.val - t₀.val ∧ p.val.1.val - t₀.val + T ≤ ρ) ∧
              ∀ p : U, referenceCircleSolutionFacts (c₀.pullbackMetric (gshift 0))
                (f p).val
                (fun t z => alpha (f p) (p.val.1.val - t₀.val + t) z)
                (fun t z => reaction (f p) (p.val.1.val - t₀.val + t) z)
                ρ hT (u p) (gforce p) := by
  let _ := smoothImmersionTopology e
  intro gshift _ f₀ J₀ K₀ P J K F G S
  have hzero : (0 : ℝ) ∈ (D.timeShift t₀.val).regular := by
    change 0 + t₀.val ∈ D.regular
    simpa only [zero_add] using ht
  have hshift : MetricFamilySmoothOn (D.timeShift t₀.val)
      (fun t => Geometry.Riemannian.retractionMetric (gshift t) e.smooth hr) := by
    simpa only [gshift, add_comm] using hG.timeShift t₀.val
  have hproducer := ambient_reference_translated_solutions_on_smooth_neighborhood
    c₀ gshift hzero e hr hEO hleft β hshift
  obtain ⟨hadd, δ, ρ, hδ, hρ, alpha, reaction, hcoeff, hprincipal,
      V, hVopen, hc₀, hV, T₀, hT₀, _, hfamily⟩ := hproducer
  obtain ⟨T, hT, hTT₀, hTρ, U, hU, hmem, pull, hpull, htime, hinit, hend, hbounds⟩ :=
    exists_uniform_initial_time_neighborhood t₀ c₀ hρ hT₀ hVopen hc₀
  obtain ⟨u₀, force₀, hu₀, hforce₀, hfacts₀⟩ := hfamily hT hTT₀
  let f : U → Metric.closedBall f₀ δ := fun p =>
    ⟨fixedAmbientSobolev e (c₀.pullbackMetric (gshift 0)) (pull p).2.val,
      hV (pull p).2.val (pull p).2.property⟩
  refine ⟨hadd, δ, ρ, hδ, hρ, alpha, reaction, hcoeff, hprincipal,
    T, hT, hTρ, U, hU, hmem, f, ?_,
    u₀ ∘ pull, force₀ ∘ pull, hu₀.comp hpull, hforce₀.comp hpull, hend, ?_, ?_⟩
  · intro p
    exact congrArg (fixedAmbientSobolev e (c₀.pullbackMetric (gshift 0))) (hinit p)
  · intro p
    simpa only [htime p] using hbounds p
  · intro p
    simpa only [f, Function.comp_def, htime p] using hfacts₀ (pull p)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

end

section

open private
  exists_normalized_h2_coefficients from
DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.AddCircleForcingContinuity
open private
  reference_exists_continuousOn_sobolev_forcing_family_timeShift from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.HigherForcingFamilies
open private
  reference_parameterDerivative_forcing_field_lift_timeShift from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ForcingFamilies
open private
  reference_exists_continuousOn_h2_forcing_h3_state_timeShift from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ForcingFamilies
open private
  reference_exists_continuousOn_principalCoefficient_timeShift from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.CoefficientFamilies
open private
  reference_joint_total_sobolev_representatives from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialJets
open private
  referenceCirclePrincipalNormBounds from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
open private
  CircleHsPi
  circleHsPiInclusion
  circleHsPiCongr from
DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private
  circleFirstJet from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private
  referenceCircleSolutionFacts
  fixedAmbientSobolev
  continuous_fixedAmbientSobolev from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
open private
  referenceCircleSymmetricCoefficientFacts
  fixedAmbientSobolevExponent
  continuous_fixedAmbientSobolevExponent
  fixedAmbientSobolevExponent_inclusion_three from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
open private
  parameterDerivativeForcingFieldLift from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity
open private vectorTensorHsNormedSpace in
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tendsto_heatVectorForcingResidualL

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open TensorHeatEquation TensorSpectral TimeSobolev QuasiLinear MaximalRegularity

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
attribute [local instance] vectorTensorHsNormedSpace

private theorem reference_exists_normalized_principal_coefficients_timeShift
    {X : Type*} [TopologicalSpace X] {N : ℕ} {D : Set X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (σ : X → ℝ) (hσ : ContinuousOn σ D)
    (fref : CircleHsPi g (Fin N) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (hf : ContinuousOn (fun x => (f x).val) D)
    (f₄ : X → CircleHsPi g (Fin N) (((2 : ℕ) : ℝ) + 2))
    (diffusion : (Option (Fin N ⊕ Fin N) → ℝ) → ℝ)
    (drift : (Option (Fin N ⊕ Fin N) → ℝ) → Fin N → ℝ)
    {S : Set (Option (Fin N ⊕ Fin N) → ℝ)}
    (hdiffusion : ContDiffOn ℝ ∞ diffusion S)
    (hdrift : ContDiffOn ℝ ∞ drift S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin N) (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin N) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g (Fin N) 1)
    (force : X → timeL2 (CircleHsPi g (Fin N) ((1 : ℕ) : ℝ)) T)
    (hforce : ContinuousOn force D)
    (W₂ : X → ℝ → CircleHsPi g (Fin N) (((1 : ℕ) : ℝ) + 1))
    (hW₂ : ∀ x, ContinuousOn (W₂ x) (Icc 0 T))
    (aRaw : X → timeL2 (TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) T)
    (bRaw : X → timeL2 (CircleHsPi g (Fin N) (((1 : ℕ) : ℝ) + 1)) T)
    (F₂ : X → timeL2 (CircleHsPi g (Fin N) ((2 : ℕ) : ℝ)) T) :
    let K₀ := circleHsPiInclusion g (Fin N)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P₀ := (circleFirstJet (ι := Fin N) g).comp K₀
    let J₀ := (circleFirstJet (ι := Fin N) g).comp (circleHsPiCongr g (Fin N)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let K := circleHsPiInclusion g (Fin N)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let AH := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    let C := tensorHsCongrL g 0 0 (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let Cpi := circleHsPiCongr g (Fin N) (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
    let M₂ := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : ((2 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1)
    referenceCircleSymmetricCoefficientFacts g fref P₀ J₀ diffusion drift S δ ρ alpha reaction →
    referenceCirclePrincipalNormBounds (n := N) g ρ alpha →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ ∧ ∀ t ∈ Icc 0 T, ‖W₂ x t‖ ≤ ρ) →
    (∀ x, W₂ x =ᵐ[timeMeasure T] fun t => K (maximalRegularityDuhamelVectorField hT 0 (force x) t)) →
    (∀ x, (fun t => AH (aRaw x t)) =ᵐ[timeMeasure T]
      (fun t => C (alpha (f x) (σ x + t) (W₂ x t)))) →
    (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin N => AH) (bRaw x t))
      =ᵐ[timeMeasure T] (fun t => Cpi (reaction (f x) (σ x + t) (W₂ x t)))) →
    (∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
        (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i) + F₂ x t i =
        scalarHsMul g 2 (by norm_num) (M₂ (aRaw x t))
          (AddCircle.parameterSecondDerivativeHs g 2
            (f₄ x i + maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i)) + M₂ (bRaw x t i)) →
    ∃ (a₂ : X → timeL2 (TensorHs g 0 0 ((2 : ℕ) : ℝ)) T)
      (b₂ : X → timeL2 (CircleHsPi g (Fin N) ((2 : ℕ) : ℝ)) T)
      (aTop₁ : X → Lp (TensorHs g 0 0 ((1 : ℕ) : ℝ)) ∞ (timeMeasure T)),
      (∀ x, (fun t => tensorHsInclusion (g := g) (r := 0) (s := 0)
        (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ)) (a₂ x t)) =ᵐ[timeMeasure T]
          fun t => alpha (f x) (σ x + t) (W₂ x t)) ∧
      (∀ x, (fun t => ContinuousLinearMap.piLpMap 2 (fun _ : Fin N =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ ((2 : ℕ) : ℝ))) (b₂ x t)) =ᵐ[timeMeasure T]
            fun t => reaction (f x) (σ x + t) (W₂ x t)) ∧
      (∀ x, aTop₁ x =ᵐ[timeMeasure T] fun t => tensorHsCongrL g 0 0
        (Nat.cast_one.symm : (1 : ℝ) = ((1 : ℕ) : ℝ))
          (alpha (f x) (σ x + t) (W₂ x t))) ∧
      ContinuousOn aTop₁ D ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T,
        ‖AddCircle.parameterPrincipalOperatorHsPi (ι := Fin N) g (aTop₁ x t)‖ ≤ (1 / 4 : ℝ)) ∧
      (∀ x, ∀ᵐ t ∂timeMeasure T,
        ‖AddCircle.parameterPrincipalOperatorH0Pi (ι := Fin N) g (aTop₁ x t)‖ ≤ (1 / 4 : ℝ)) ∧
      ∀ x, ∀ᵐ t ∂timeMeasure T, ∀ i,
        tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((2 : ℕ) : ℝ)
          (maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i) + F₂ x t i =
          scalarHsMul g 2 (by norm_num) (a₂ x t)
            (AddCircle.parameterSecondDerivativeHs g 2
              (f₄ x i + maximalRegularityDuhamelVectorField hT 0 (F₂ x) t i)) + b₂ x t i := by
  intro K₀ P₀ J₀ K AH C Cpi M₂ hcoeff hprincipal hgood hW₂pin haRaw hbRaw hPDE₂raw
  obtain ⟨aTop₁, haTopRaw, haTopCont, hCh, hCl⟩ :=
    reference_exists_continuousOn_principalCoefficient_timeShift
      g hT P₀ J₀ σ hσ fref f hf force hforce W₂ hW₂ diffusion drift
      hdiffusion hdrift hS alpha reaction hcoeff hprincipal hgood hW₂pin
  obtain ⟨a₂, b₂, _, _, ha₂, hb₂, hPDE₂⟩ := exists_normalized_h2_coefficients
    (X := X) (ι := Fin N) g T f₄
    (fun x => maximalRegularityDuhamelVectorField hT 0 (F₂ x)) F₂ aRaw bRaw
    (fun x t => alpha (f x) (σ x + t) (W₂ x t))
    (fun x t => reaction (f x) (σ x + t) (W₂ x t)) haRaw hbRaw hPDE₂raw
  exact ⟨a₂, b₂, aTop₁, ha₂, hb₂, haTopRaw, haTopCont, hCh, hCl, hPDE₂⟩

private theorem fluctuation_representatives_of_sobolev_tower
    {X : Type*} [TopologicalSpace X] {N : ℕ} {D : Set X}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) {T : ℝ}
    (u : X → timeH1 (CircleHsPi g (Fin N) ((1 : ℕ) : ℝ)) T)
    (W₂ : X → ℝ → CircleHsPi g (Fin N) (((1 : ℕ) : ℝ) + 1))
    (W₃ : X → ℝ → CircleHsPi g (Fin N) ((3 : ℕ) : ℝ))
    (Ws : ∀ k : ℕ, X → ℝ → CircleHsPi g (Fin N) ((k + 3 : ℕ) : ℝ))
    (hW₂low : ∀ x t, t ∈ Icc 0 T → circleHsPiInclusion g (Fin N)
      (by norm_num : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1) (W₂ x t) = (u x).toFun t)
    (hW₃₂ : ∀ x t, t ∈ Icc 0 T → circleHsPiInclusion g (Fin N)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 ≤ ((3 : ℕ) : ℝ)) (W₃ x t) = W₂ x t)
    (hWs : ∀ k x, ContinuousOn (Ws k x) (Icc 0 T))
    (hWslim : ∀ k x, x ∈ D →
      TendstoUniformlyOn (Ws k) (Ws k x) (𝓝[D] x) (Icc 0 T))
    (hWs₃ : ∀ k x t, t ∈ Icc 0 T → circleHsPiInclusion g (Fin N)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((3 : ℕ) : ℝ) ≤ ((k + 3 : ℕ) : ℝ)) (Ws k x t) = W₃ x t) :
    let E := fun k : ℕ => circleHsPiInclusion g (Fin N)
      (by push_cast; linarith : (k : ℝ) + 3 ≤ ((k + 3 : ℕ) : ℝ))
    let W := fun k x t => E k (Ws k x t)
    let L := circleHsPiInclusion g (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    (∀ k x, x ∈ D → ContinuousOn (W k x) (Icc 0 T)) ∧
    (∀ k x, x ∈ D → TendstoUniformlyOn (W k) (W k x) (𝓝[D] x) (Icc 0 T)) ∧
    ∀ (k : ℕ) x, x ∈ D → ∀ t ∈ Icc 0 T,
      circleHsPiInclusion g (Fin N)
        (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith [hk] :
          (1 : ℝ) ≤ (k : ℝ) + 3) (W k x t) = L ((u x).toFun t) := by
  intro E W L
  refine ⟨fun k x _ => (E k).continuous.comp_continuousOn (hWs k x),
    fun k x hx => (E k).uniformContinuous.comp_tendstoUniformlyOn (hWslim k x hx), ?_⟩
  intro k x hx t ht
  rw [← hW₂low x t ht, ← hW₃₂ x t ht, ← hWs₃ k x t ht]
  apply PiLp.ext
  intro i
  apply TensorHs.ext
  rfl

private theorem reference_exists_fluctuation_sobolev_representatives_timeShift
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {X : Type*} [TopologicalSpace X] {N : ℕ} {D : Set X}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (σ : X → ℝ) (hσ : ContinuousOn σ D)
    (initial : X → SmoothImmersion (I := I) (M := M))
    (hinitial : @ContinuousOn X (SmoothImmersion (I := I) (M := M))
      inferInstance (smoothImmersionTopology e) initial D)
    (fref : CircleHsPi g (Fin N) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (hbase : ∀ x, (f x).val = fixedAmbientSobolev e g (initial x))
    (diffusion : (Option (Fin N ⊕ Fin N) → ℝ) → ℝ)
    (drift : (Option (Fin N ⊕ Fin N) → ℝ) → Fin N → ℝ)
    {S : Set (Option (Fin N ⊕ Fin N) → ℝ)}
    (hdiffusion : ContDiffOn ℝ ∞ diffusion S)
    (hdrift : ContDiffOn ℝ ∞ drift S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin N) (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin N) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g (Fin N) 1)
    (u : X → timeH1 (CircleHsPi g (Fin N) ((1 : ℕ) : ℝ)) T)
    (force : X → timeL2 (CircleHsPi g (Fin N) ((1 : ℕ) : ℝ)) T)
    (hforce : ContinuousOn force D) :
    let K₀ := circleHsPiInclusion g (Fin N)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P₀ := (circleFirstJet (ι := Fin N) g).comp K₀
    let J₀ := (circleFirstJet (ι := Fin N) g).comp (circleHsPiCongr g (Fin N)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let L := circleHsPiInclusion g (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    referenceCircleSymmetricCoefficientFacts g fref P₀ J₀ diffusion drift S δ ρ alpha reaction →
    referenceCirclePrincipalNormBounds (n := N) g ρ alpha →
    (∀ x, referenceCircleSolutionFacts g (f x).val
      (fun t z => alpha (f x) (σ x + t) z)
      (fun t z => reaction (f x) (σ x + t) z) ρ hT (u x) (force x)) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ) →
    (∀ x, parameterDerivativeForcingFieldLift g hT (force x)) ∧
    ∃ W : ∀ k : ℕ, X → ℝ → CircleHsPi g (Fin N) ((k : ℝ) + 3),
      (∀ k x, x ∈ D → ContinuousOn (W k x) (Icc 0 T)) ∧
      (∀ k x, x ∈ D →
        TendstoUniformlyOn (W k) (W k x) (𝓝[D] x) (Icc 0 T)) ∧
      ∀ (k : ℕ) x, x ∈ D → ∀ t ∈ Icc 0 T,
        circleHsPiInclusion g (Fin N)
          (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith [hk] :
            (1 : ℝ) ≤ (k : ℝ) + 3) (W k x t) = L ((u x).toFun t) := by
  classical
  intro K₀ P₀ J₀ L hcoeff hprincipal hfacts htime
  let : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  let initialHs := fun (k : ℕ) x =>
    fixedAmbientSobolevExponent e g (((k + 2 : ℕ) : ℝ) + 2) (initial x)
  have hinitialHs (k : ℕ) : ContinuousOn (initialHs k) D :=
    (continuous_fixedAmbientSobolevExponent e g (((k + 2 : ℕ) : ℝ) + 2)).comp_continuousOn hinitial
  have hbaseHs (k : ℕ) (x : X) : circleHsPiInclusion g (Fin N)
      (by have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith :
        ((1 : ℕ) : ℝ) + 2 ≤ ((k + 2 : ℕ) : ℝ) + 2) (initialHs k x) = (f x).val := by
    exact (fixedAmbientSobolevExponent_inclusion_three e g
      (by have hk := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith)
      (initial x)).trans (hbase x).symm
  obtain ⟨W₂, hW₂, hW₂low, hW₂pin, hW₂bound, _, _,
      aRaw, bRaw, haRaw, hbRaw, F₂, _, _, hPDE₂raw, hF₂, _,
      W₃, hW₃, hW₃pin, hW₃₂, hW₃lim⟩ :=
    reference_exists_continuousOn_h2_forcing_h3_state_timeShift
      g hT σ hσ fref f (initialHs 0) (hinitialHs 0) diffusion drift
      hdiffusion hdrift hS alpha reaction u force hforce hcoeff hprincipal (hbaseHs 0) hfacts htime
  have hlift (x : X) : parameterDerivativeForcingFieldLift g hT (force x) :=
    reference_parameterDerivative_forcing_field_lift_timeShift
      g hT (σ x) fref (f x) (initialHs 0 x) alpha reaction
      (u x) (force x) (W₂ x) (aRaw x) (bRaw x)
      hprincipal (hbaseHs 0 x) (hW₂pin x) (hfacts x)
      ⟨(htime x).1, (htime x).2, hW₂bound x⟩ (haRaw x) (hbRaw x)
  have hf : ContinuousOn (fun x => (f x).val) D :=
    ((continuous_fixedAmbientSobolev e g).comp_continuousOn hinitial).congr
      (fun x _ => hbase x)
  obtain ⟨a₂, b₂, aTop₁, ha₂, hb₂, haTopRaw, haTopCont, hCh, hCl, hPDE₂⟩ :=
    reference_exists_normalized_principal_coefficients_timeShift g hT σ hσ fref f hf
      (initialHs 0) diffusion drift hdiffusion hdrift hS alpha reaction force hforce
      W₂ hW₂ aRaw bRaw F₂ hcoeff hprincipal
      (fun x => ⟨(htime x).1, (htime x).2, hW₂bound x⟩) hW₂pin haRaw hbRaw hPDE₂raw
  have htower := reference_exists_continuousOn_sobolev_forcing_family_timeShift
    g hT σ hσ fref f initialHs hinitialHs diffusion drift hdiffusion hdrift hS
    alpha reaction F₂ hF₂ W₂ W₃ hW₃ hW₃lim a₂ b₂ aTop₁ haTopCont
    hcoeff hbaseHs (fun x => ⟨(htime x).1, (htime x).2, hW₂bound x⟩)
    hW₃₂ hW₃pin ha₂ hb₂ haTopRaw hCh hCl hPDE₂
  choose forces Ws _ hWs _ hWs₃ _ hWslim using htower
  have htransport := fluctuation_representatives_of_sobolev_tower
    g u W₂ W₃ Ws hW₂low hW₃₂ hWs hWslim hWs₃
  exact ⟨hlift, _, htransport⟩

private theorem reference_exists_joint_sobolev_representatives_timeShift
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {X : Type*} [TopologicalSpace X] {N : ℕ} {D : Set X}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {T : ℝ} (hT : 0 < T) (σ : X → ℝ) (hσ : ContinuousOn σ D)
    (initial : X → SmoothImmersion (I := I) (M := M))
    (hinitial : @ContinuousOn X (SmoothImmersion (I := I) (M := M))
      inferInstance (smoothImmersionTopology e) initial D)
    (fref : CircleHsPi g (Fin N) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : X → Metric.closedBall fref δ)
    (hbase : ∀ x, (f x).val = fixedAmbientSobolev e g (initial x))
    (diffusion : (Option (Fin N ⊕ Fin N) → ℝ) → ℝ)
    (drift : (Option (Fin N ⊕ Fin N) → ℝ) → Fin N → ℝ)
    {S : Set (Option (Fin N ⊕ Fin N) → ℝ)}
    (hdiffusion : ContDiffOn ℝ ∞ diffusion S)
    (hdrift : ContDiffOn ℝ ∞ drift S) (hS : IsOpen S)
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin N) (((1 : ℕ) : ℝ) + 1) → TensorHs g 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g (Fin N) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g (Fin N) 1)
    (u : X → timeH1 (CircleHsPi g (Fin N) ((1 : ℕ) : ℝ)) T)
    (force : X → timeL2 (CircleHsPi g (Fin N) ((1 : ℕ) : ℝ)) T)
    (hforce : ContinuousOn force D) :
    let K₀ := circleHsPiInclusion g (Fin N)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let P₀ := (circleFirstJet (ι := Fin N) g).comp K₀
    let J₀ := (circleFirstJet (ι := Fin N) g).comp (circleHsPiCongr g (Fin N)
      (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let B := circleHsPiInclusion g (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let L := circleHsPiInclusion g (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    referenceCircleSymmetricCoefficientFacts g fref P₀ J₀ diffusion drift S δ ρ alpha reaction →
    referenceCirclePrincipalNormBounds (n := N) g ρ alpha →
    (∀ x, referenceCircleSolutionFacts g (f x).val
      (fun t z => alpha (f x) (σ x + t) z)
      (fun t z => reaction (f x) (σ x + t) z) ρ hT (u x) (force x)) →
    (∀ x, -ρ ≤ σ x ∧ σ x + T ≤ ρ) →
    ∀ k : ℕ, ∃ Z : X × ℝ → CircleHsPi g (Fin N) ((k : ℝ) + 2),
      ContinuousOn Z (D ×ˢ Icc 0 T) ∧
      ∀ x ∈ D, ∀ t ∈ Icc 0 T, circleHsPiInclusion g (Fin N)
        (by have := Nat.cast_nonneg (α := ℝ) k; linarith :
          (1 : ℝ) ≤ (k : ℝ) + 2) (Z (x, t)) =
        B (fixedAmbientSobolev e g (initial x)) + L ((u x).toFun t) := by
  intro K₀ P₀ J₀ B L hcoeff hprincipal hfacts htime
  obtain ⟨_, W, hW, hWlim, hWpin⟩ :=
    reference_exists_fluctuation_sobolev_representatives_timeShift
      e g hT σ hσ initial hinitial fref f hbase diffusion drift
      hdiffusion hdrift hS alpha reaction u force hforce hcoeff hprincipal hfacts htime
  exact reference_joint_total_sobolev_representatives
    e g initial hinitial u W hW hWlim hWpin

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

end

section

noncomputable section

open Set Filter
open scoped ContDiff Manifold _root_.Topology
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

open private
  CircleHsPi
  circleHsPiInclusion
  circleHsPiCongr from
DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private
  circleFirstJet
  firstJetCoordinates from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private
  fixedAmbientSobolev
  referenceCircleSolutionFacts from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
open private
  referenceCircleSymmetricCoefficientFacts from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ParameterSolutions
open private
  parameterDerivativeForcingFieldLift from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.SpatialRegularity
open private
  reference_selected_retraction from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.Reconstruction
open private
  reference_selected_ambient_jets from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.Reconstruction
open private
  reference_chart_equation_of_parameterDerivative_lift from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.Reconstruction

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem reference_selected_retraction_and_ambient_jets
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {P : Type*} [TopologicalSpace P] {S : Set P} {N : ℕ} {T : ℝ}
    (hT : 0 < T) {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) (σ : P → ℝ) (hσ : ContinuousOn σ S)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g₀ : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinitial : @ContinuousOn P (SmoothImmersion (I := I) (M := M))
      inferInstance (smoothImmersionTopology e) initial S)
    (fref : CircleHsPi g₀ (Fin N) (((1 : ℕ) : ℝ) + 2))
    {δ ρ : ℝ} (f : P → Metric.closedBall fref δ)
    (hf : ∀ p ∈ S, (f p).val = fixedAmbientSobolev e g₀ (initial p))
    (alpha : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin N) (((1 : ℕ) : ℝ) + 1) → TensorHs g₀ 0 0 1)
    (reaction : Metric.closedBall fref δ → ℝ →
      CircleHsPi g₀ (Fin N) (((1 : ℕ) : ℝ) + 1) → CircleHsPi g₀ (Fin N) 1)
    (hσlo : ∀ p ∈ S, -ρ ≤ σ p) (hσhi : ∀ p ∈ S, σ p + T ≤ ρ)
    (u : P → timeH1 (CircleHsPi g₀ (Fin N) ((1 : ℕ) : ℝ)) T)
    (gforce : P → timeL2 (CircleHsPi g₀ (Fin N) ((1 : ℕ) : ℝ)) T)
    (W : ∀ k : ℕ, P → ℝ → CircleHsPi g₀ (Fin N) ((k : ℝ) + 3))
    (hW : ∀ k p, p ∈ S → ContinuousOn (W k p) (Icc 0 T))
    (hWlim : ∀ k p, p ∈ S →
      TendstoUniformlyOn (W k) (W k p) (𝓝[S] p) (Icc 0 T))
    {r : EuclideanSpace ℝ (Fin N) → M}
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin N))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I ∞ r U)
    (hEU : range e.map ⊆ U) (hleft : ∀ p, r (e.map p) = p) (β : U) :
    let K₂ := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2)
    let Q := (circleFirstJet (ι := Fin N) g₀).comp K₂
    let J := (circleFirstJet (ι := Fin N) g₀).comp
      (circleHsPiCongr g₀ (Fin N)
        (by norm_num : ((1 : ℕ) : ℝ) + 1 = (1 : ℝ) + 1)).toLinearIsometry.toContinuousLinearMap
    let gambient := fun t => Geometry.Riemannian.retractionMetric (g t) e.smooth hr
    referenceCircleSymmetricCoefficientFacts g₀ fref Q J
      (curveShorteningChartDiffusionCoefficient gambient β ∘ firstJetCoordinates N)
      (fun z i => curveShorteningParametricChartReaction gambient β (firstJetCoordinates N z) i)
      (firstJetCoordinates N ⁻¹' curveShorteningChartFirstJetDomain D gambient β)
      δ ρ alpha reaction →
    (∀ p ∈ S, referenceCircleSolutionFacts g₀ (f p).val
      (fun t => alpha (f p) (σ p + t)) (fun t => reaction (f p) (σ p + t))
      ρ hT (u p) (gforce p)) →
    (∀ p ∈ S, parameterDerivativeForcingFieldLift g₀ hT (gforce p)) →
    let B := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    let L := circleHsPiInclusion g₀ (Fin N)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let d : P → CurveMap (EuclideanSpace ℝ (Fin N)) := fun p z t => WithLp.toLp 2
      (scalarH1PiToContinuous g₀
        (B (fixedAmbientSobolev e g₀ (initial p)) + L ((u p).toFun t)) z)
    (∀ (k : ℕ) p, p ∈ S → ∀ t, t ∈ Icc 0 T →
      circleHsPiInclusion g₀ (Fin N)
        (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith [hk] :
          (1 : ℝ) ≤ (k : ℝ) + 3) (W k p t) = L ((u p).toFun t)) →
    let c : P → CurveMap M := fun p z t => r (d p z t)
    (∀ p ∈ S,
      (c p).SmoothOn (I := I) (Icc 0 T) ∧
        (∀ z, c p z 0 = (initial p).map z) ∧
        (∀ z t, t ∈ Icc 0 T → e.map (c p z t) = d p z t) ∧
        (c p).ImmersedOn (I := I) (Icc 0 T) ∧
        ∀ x t, t ∈ Icc 0 T → (c p).velocity (I := I) (Icc 0 T) x t =
          (c p).speed (fun s => g (σ p + s)) x t ^ (-2 : ℤ) •
            (c p).Dx (fun s => g (σ p + s)) (c p).X x t) ∧
      (∀ p ∈ S, ContDiffOn ℝ ∞
        (fun q : ℝ × ℝ => (d p).lift q.2 q.1) (Icc 0 T ×ˢ univ)) ∧
      (∀ k j : ℕ, ContinuousOn
        (fun q : P × ℝ × ℝ => iteratedDerivWithin k
          (fun t => iteratedDeriv j (fun x => (d q.1).lift x t) q.2.2)
          (Icc 0 T) q.2.1) (S ×ˢ Icc 0 T ×ˢ univ)) ∧
      (∀ n : ℕ, ContinuousOn
        (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
          (fun z : ℝ × ℝ => (d q.1).lift z.2 z.1) (Icc 0 T ×ˢ univ) q.2)
        (S ×ˢ Icc 0 T ×ˢ univ)) ∧
      ∀ p ∈ S, ∀ t ∈ Icc 0 T, ∀ x : ℝ,
        (σ p + t, (d p).lift x t, deriv (fun y => (d p).lift y t) x) ∈
          curveShorteningChartFirstJetDomain D gambient β := by
  intro K₂ Q J gambient hcoeff hfacts hlift B L d hWpin c
  have hc := reference_selected_retraction
    hT g hg σ hσ e g₀ initial hinitial fref f hf alpha reaction hσlo hσhi
    u gforce W hW hWlim hr hEU hleft β hcoeff hfacts hlift hWpin
  have hambient := reference_selected_ambient_jets
    hT g hg σ hσ e g₀ initial hinitial fref f hf alpha reaction hσlo hσhi
    u gforce W hW hWlim hr β hcoeff hfacts hlift hWpin
  refine ⟨hc, hambient.1, hambient.2.1, hambient.2.2, ?_⟩
  intro p hp t ht x
  have hgambient : MetricFamilySmoothOn D gambient :=
    metricFamilySmoothOn_retractionMetric g hg e.smooth hr
  have heq := reference_chart_equation_of_parameterDerivative_lift
    gambient hgambient β g₀ hT (σ p) fref (f p) alpha reaction
    (hσlo p hp) (hσhi p hp) (u p) (gforce p) hcoeff (hfacts p hp) (hlift p hp)
  simpa only [hf p hp, d] using ((heq.1 t ht x).1)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.SmoothImmersion

end

end

section

noncomputable section

open Set Manifold
open scoped ContDiff Manifold _root_.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem contDiffOn_and_continuousOn_mixed_gaugeCoefficient_of_retraction_jets
    {P : Type*} [TopologicalSpace P] {S : Set P} {J : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J))
    {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) (σ : P → ℝ) (hσ : ContinuousOn σ S)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U)
    (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p) (β : U)
    (c : P → CurveMap M) (d : P → CurveMap F)
    (hc : ∀ p ∈ S, (c p).SmoothOn (I := I) J)
    (hi : ∀ p ∈ S, (c p).ImmersedOn (I := I) J)
    (hcd : ∀ p ∈ S, ∀ z t, t ∈ J → e (c p z t) = d p z t)
    (hd : ∀ p ∈ S, ContDiffOn ℝ ∞
      (fun q : ℝ × ℝ => (d p).lift q.2 q.1) (J ×ˢ univ))
    (hmixed : ∀ k j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDerivWithin k
        (fun t => iteratedDeriv j (fun x => (d q.1).lift x t) q.2.2) J q.2.1)
      (S ×ˢ J ×ˢ univ))
    (hjet : ∀ p ∈ S, ∀ t ∈ J, ∀ x,
      (σ p + t, (d p).lift x t, deriv (fun y => (d p).lift y t) x) ∈
        curveShorteningChartFirstJetDomain D
          (fun s => retractionMetric (g s) he hr) β) :
    let ξ := fun p t x =>
      -(deriv (fun y => (c p).speed (fun s => g (σ p + s)) y t) x /
        (c p).speed (fun s => g (σ p + s)) x t ^ 2) /
          (c p).speed (fun s => g (σ p + s)) x t
    (∀ p ∈ S, ContDiffOn ℝ ∞ (Function.uncurry (ξ p)) (J ×ˢ univ)) ∧
      ∀ k j : ℕ, ContinuousOn
        (fun q : P × ℝ × ℝ => iteratedDerivWithin k
          (fun t => iteratedDeriv j (ξ q.1 t) q.2.2) J q.2.1)
        (S ×ˢ J ×ˢ univ) := by
  intro ξ
  let gambient := fun s => retractionMetric (g s) he hr
  let Ω := curveShorteningChartFirstJetDomain D gambient β
  let Φ := curveShorteningChartDiffusionCoefficient gambient β
  let G := fun p t x => (d p).lift x t
  let A := fun p t x => Φ (σ p + t, G p t x, deriv (G p t) x)
  have hGa : MetricFamilySmoothOn D gambient :=
    metricFamilySmoothOn_retractionMetric g hg he hr
  have hΩ : IsOpen Ω := isOpen_curveShorteningChartFirstJetDomain hGa β
  have hΦ : ContDiffOn ℝ ∞ Φ Ω := contDiffOn_curveShorteningChartDiffusionCoefficient hGa β
  have hAs (p : P) (hp : p ∈ S) :
      ContDiffOn ℝ ∞ (Function.uncurry (A p)) (J ×ˢ univ) :=
    Analysis.contDiffOn_shifted_firstJet_comp (d := G p) hJ (σ p) (hd p hp) Φ hΦ (hjet p hp)
  have hAf (n : ℕ) : ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
        (Function.uncurry (A q.1)) (J ×ˢ univ) q.2) (S ×ˢ J ×ˢ univ) :=
    Analysis.continuousOn_iteratedFDerivWithin_shifted_firstJet_comp (d := G)
      hJ hacc hσ hd hmixed hΩ Φ hΦ hjet n
  have hAm (k j : ℕ) : ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDerivWithin k
        (fun t => iteratedDeriv j (A q.1 t) q.2.2) J q.2.1) (S ×ˢ J ×ˢ univ) :=
    Analysis.continuousOn_mixed_derivatives_of_iteratedFDerivWithin
      hJ isOpen_univ hAs hAf k j
  refine ⟨?_, continuousOn_mixed_gaugeCoefficient_of_retraction_chartDiffusionCoefficient
    g σ he hr hEU hleft β c d hc hi hcd hAm⟩
  intro p hp
  have hAdx : ContDiffOn ℝ ∞
      (fun q : ℝ × ℝ => deriv (A p q.1) q.2) (J ×ˢ univ) := by
    have h := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).contDiff.comp_contDiffOn
      (Analysis.spatialFDeriv_contDiffOn hJ isOpen_univ (hAs p hp))
    change ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => fderiv ℝ (A p q.1) q.2 1)
      (J ×ˢ univ) at h
    simpa only [fderiv_apply_one_eq_deriv] using h
  apply ((contDiffOn_const (c := (1 / 2 : ℝ))).mul hAdx).congr
  intro q hq
  have h := congrFun (iteratedDeriv_gaugeCoefficient_eq_retraction_chartDiffusionCoefficient
    g (σ p) he hr hEU hleft β (c p) (d p) (hc p hp) (hi p hp)
    hq.1 (fun z => hcd p hp z q.1 hq.1) 0) q.2
  simpa only [Nat.zero_add, iteratedDeriv_zero, iteratedDeriv_one,
    ξ, A, G, Φ, gambient, Function.uncurry_def] using h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

end

section

noncomputable section

open Set Filter
open scoped ContDiff Manifold _root_.Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Analysis

private theorem continuousOn_of_tendstoUniformlyOn_compact_fst
    {P X Y Z : Type*} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [UniformSpace Z] [WeaklyLocallyCompactSpace X] {S : Set P} {J : Set Y}
    {f : P → X × Y → Z}
    (hcont : ∀ p ∈ S, ContinuousOn (f p) (univ ×ˢ J))
    (hlim : ∀ p ∈ S, ∀ K : Set X, IsCompact K →
      TendstoUniformlyOn f (f p) (𝓝[S] p) (K ×ˢ J)) :
    ContinuousOn (fun q : P × X × Y => f q.1 q.2) (S ×ˢ univ ×ˢ J) := by
  rintro ⟨p, x, t⟩ ⟨hp, _, ht⟩
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have hsame : 𝓝[K ×ˢ J] (x, t) = 𝓝[univ ×ˢ J] (x, t) := by
    rw [nhdsWithin_prod_eq, nhdsWithin_prod_eq, nhdsWithin_univ,
      nhdsWithin_eq_nhds.mpr hxK]
  change Tendsto _ (𝓝[S ×ˢ univ ×ˢ J] (p, x, t)) _
  rw [nhdsWithin_prod_eq]
  have hunif : TendstoUniformlyOn (fun q : P × X × Y => f q.1) (f p)
      (𝓝[S] p ×ˢ 𝓝[univ ×ˢ J] (x, t)) (K ×ˢ J) := by
    intro u hu
    exact tendsto_fst.eventually (hlim p hp K hK u hu)
  apply hunif.tendsto_comp
    ((hcont p hp).mono (prod_mono (subset_univ _) Subset.rfl) (x, t)
      ⟨mem_of_mem_nhds hxK, ht⟩)
  rw [hsame]
  exact tendsto_snd

private theorem continuousOn_iteratedDeriv_fst_of_tendstoUniformlyOn
    {P F : Type*} [TopologicalSpace P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set P} {a b : ℝ} (hab : a < b) {γ : P → ℝ → ℝ → F}
    (hγ : ∀ p ∈ S, ContDiffOn ℝ ∞ (Function.uncurry (γ p)) (univ ×ˢ Icc a b))
    (hlim : ∀ p ∈ S, ∀ K : Set ℝ, IsCompact K → ∀ k : ℕ,
      TendstoUniformlyOn
        (fun q (v : ℝ × ℝ) => iteratedFDeriv ℝ k (fun x => γ q x v.2) v.1)
        (fun v : ℝ × ℝ => iteratedFDeriv ℝ k (fun x => γ p x v.2) v.1)
        (𝓝[S] p) (K ×ˢ Icc a b)) (j : ℕ) :
    ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDeriv j (fun x => γ q.1 x q.2.2) q.2.1)
      (S ×ˢ univ ×ˢ Icc a b) := by
  apply continuousOn_of_tendstoUniformlyOn_compact_fst
    (f := fun p (v : ℝ × ℝ) => iteratedDeriv j (fun x => γ p x v.2) v.1)
  · intro p hp
    exact (contDiffOn_iteratedDeriv_fst_of_uniqueDiffOn
      isOpen_univ (uniqueDiffOn_Icc hab) (hγ p hp) j).continuousOn
  · intro p hp K hK
    have hU := (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j) F).symm.isometry
    have hh := hU.uniformContinuous.comp_tendstoUniformlyOn (hlim p hp K hK j)
    simpa only [iteratedDeriv_eq_equiv_comp, Function.comp_def] using hh

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem exists_fixed_normalizing_flows
    {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : P → RealTimeInterval} {g : P → ℝ → SmoothRiemannianMetric I M}
    (hG : ∀ p, MetricFamilySmoothOn (D p) (g p)) {a b : ℝ} (hab : a < b)
    (hJ : ∀ p, Icc a b ⊆ (D p).regular) {c : P → CurveMap M}
    (hc : ∀ p, (c p).SmoothOn (I := I) (Icc a b))
    (hi : ∀ p, (c p).ImmersedOn (I := I) (Icc a b))
    (heq : ∀ p x t, t ∈ Icc a b → (c p).velocity (I := I) (Icc a b) x t =
      (c p).speed (g p) x t ^ (-2 : ℤ) • (c p).Dx (g p) (c p).X x t) :
    ∃ (F : P → ℝ → (AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ)))
      (γ : P → ℝ → ℝ → ℝ),
      (∀ p, CurveMap.IsSolutionOn (I := I)
        (fun z t => c p (F p t z) t) (g p) (Icc a b)) ∧
      (∀ p z, F p a z = z) ∧
      (∀ p, ContDiffOn ℝ ∞ (Function.uncurry (γ p)) (univ ×ˢ Icc a b)) ∧
      (∀ p x t, t ∈ Icc a b →
        (γ p x t : AddCircle (1 : ℝ)) = F p t (x : AddCircle (1 : ℝ))) ∧
      (∀ p x t, t ∈ Icc a b → γ p (x + 1) t = γ p x t + 1) ∧
      (∀ p x, γ p x a = x) ∧
      (∀ p x, IsIntegralCurveOn (γ p x)
        (fun t y => -(deriv (fun z => (c p).speed (g p) z t) y /
          (c p).speed (g p) y t ^ 2) / (c p).speed (g p) y t) (Icc a b)) ∧
      ∀ (l : Filter P) (p : P),
        (∀ k : ℕ, TendstoUniformlyOn
          (fun q (v : ℝ × ℝ) => iteratedDeriv (k + 1)
            (fun x => (c q).speed (g q) x v.2 ^ (-2 : ℤ)) v.1)
          (fun v : ℝ × ℝ => iteratedDeriv (k + 1)
            (fun x => (c p).speed (g p) x v.2 ^ (-2 : ℤ)) v.1)
          l (Icc (0 : ℝ) 1 ×ˢ Icc a b)) →
        ∀ K : Set ℝ, IsCompact K → ∀ k : ℕ, TendstoUniformlyOn
          (fun q (v : ℝ × ℝ) => iteratedFDeriv ℝ k (fun x => γ q x v.2) v.1)
          (fun v : ℝ × ℝ => iteratedFDeriv ℝ k (fun x => γ p x v.2) v.1)
          l (K ×ˢ Icc a b) := by
  classical
  let α : P → ℝ → ℝ → ℝ := fun p x t =>
    deriv (fun y => (c p).speed (g p) y t) x / (c p).speed (g p) x t ^ 2
  let β : P → ℝ → ℝ → ℝ := fun p t x => -(α p x t) / (c p).speed (g p) x t
  have hgeo (p : P) : (c p).IsGeometricSolutionOn (g p) (Icc a b) (α p) :=
    CurveMap.isGeometricSolutionOn_of_parabolicGauge
      (hG p) (uniqueDiffOn_Icc hab) (hJ p) (hc p) (hi p) (heq p)
  have hex (p : P) :
      ∃ (F : ℝ → (AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ)))
        (γ : ℝ → ℝ → ℝ),
        CurveMap.IsSolutionOn (I := I) (fun z t => c p (F t z) t) (g p) (Icc a b) ∧
        (∀ z, F a z = z) ∧
        ContDiffOn ℝ ∞ (Function.uncurry γ) (univ ×ˢ Icc a b) ∧
        (∀ x t, t ∈ Icc a b → (γ x t : AddCircle (1 : ℝ)) =
          F t (x : AddCircle (1 : ℝ))) ∧
        (∀ x t, t ∈ Icc a b → γ (x + 1) t = γ x t + 1) ∧
        (∀ x, γ x a = x) ∧
        ∀ x, IsIntegralCurveOn (γ x) (β p) (Icc a b) := by
    obtain ⟨βcircle, F, _, hβeq, hF0, hFsm, _, hFode, hsol⟩ :=
      (hgeo p).exists_diffeomorph_flow_isSolutionOn (hG p) hab (hJ p)
    obtain ⟨γ, hγsm, hγcoe, hγper, hγ0, hγode⟩ :=
      AddCircle.exists_affine_periodic_integralCurve_lift hab.le hFsm hF0 hFode
    refine ⟨F, γ, hsol, hF0, hγsm, hγcoe, hγper, hγ0, ?_⟩
    intro x t ht
    have h := hγode x t ht
    dsimp only at h
    rw [hβeq t ht] at h
    exact h
  choose F γ hsol hF0 hγsm hγcoe hγper hγ0 hγode using hex
  refine ⟨F, γ, hsol, hF0, hγsm, hγcoe, hγper, hγ0, hγode, ?_⟩
  have hβsmooth (p : P) :
      ContDiffOn ℝ 1 (Function.uncurry (β p)) (Icc a b ×ˢ univ) := by
    have hspeed := CurveMap.Field.smoothOn_speed (g p) (hG p) (hJ p) (c p) (hc p) (hi p)
    have hraw : ContDiffOn ℝ ∞
        (fun q : ℝ × ℝ => -(α p q.1 q.2) / (c p).speed (g p) q.1 q.2)
        (univ ×ˢ Icc a b) :=
      (hgeo p).tangentSmooth.neg.div hspeed
        (fun q hq => ((c p).speed_pos (g p) (hi p) q.1 q.2 hq.2).ne')
    exact (hraw.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun q hq => ⟨hq.2, hq.1⟩)).of_le (by norm_num)
  have hid (p : P) (η : ℝ → ℝ → ℝ)
      (hη0 : ∀ x, η x a = x)
      (hηode : ∀ x, IsIntegralCurveOn (η x) (β p) (Icc a b)) :
      ∀ x t, t ∈ Icc a b → γ p x t = η x t := by
    intro x
    exact DifferentialGeometry.Analysis.ODE.IsIntegralCurveOn.eqOn_of_contDiffOn
      (hγode p x) (hηode x) ordConnected_Icc (hβsmooth p) ⟨le_rfl, hab.le⟩
      ((hγ0 p x).trans (hη0 x).symm)
  intro l p hconv
  obtain ⟨_, _, η, ηInf, _, _, _, _, _, _, _, _, _, _, hη0, hηInf0,
      hηode, hηInfOde, hηconv⟩ :=
    exists_diffeomorph_flow_lift_iteratedFDeriv_tendstoUniformlyOn_of_parabolic_equation
      hG (hG p) hab hJ (hJ p) hc hi (hc p) (hi p) heq (heq p) hconv
  have heta (q : P) (t : ℝ) (ht : t ∈ Icc a b) :
      (fun x => η q x t) = (fun x => γ q x t) :=
    funext (fun x => (hid q (η q) (hη0 q) (hηode q) x t ht).symm)
  have heqInf (t : ℝ) (ht : t ∈ Icc a b) :
      (fun x => ηInf x t) = (fun x => γ p x t) :=
    funext (fun x => (hid p ηInf hηInf0 hηInfOde x t ht).symm)
  intro K hK k
  apply ((hηconv K hK k).congr (Eventually.of_forall fun q v hv => ?_)).congr_right
    (fun v hv => ?_)
  · exact congrArg (fun f : ℝ → ℝ => iteratedFDeriv ℝ k f v.1) (heta q v.2 hv.2)
  · exact congrArg (fun f : ℝ → ℝ => iteratedFDeriv ℝ k f v.1) (heqInf v.2 hv.2)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry.Analysis

private theorem tendstoUniformlyOn_of_continuousOn_prod
    {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X] [UniformSpace Y]
    {K : Set X} (hK : IsCompact K) {f : P → X → Y}
    (hf : ContinuousOn (Function.uncurry f) (univ ×ˢ K)) (p : P) :
    TendstoUniformlyOn f (f p) (𝓝 p) K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : P → C(K, Y) := fun q =>
    ⟨fun x => f q x, hf.comp_continuous
      (continuous_const.prodMk continuous_subtype_val) (fun x => ⟨mem_univ q, x.2⟩)⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hf.comp_continuous (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun q => ⟨mem_univ q.1, q.2.2⟩)
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (ContinuousMap.tendsto_iff_tendstoUniformly.mp (hF.tendsto p))

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem exists_fixed_normalizing_flows_continuousOn_iteratedFDerivWithin
    {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace P]
    {D : P → RealTimeInterval} {g : P → ℝ → SmoothRiemannianMetric I M}
    (hG : ∀ p, MetricFamilySmoothOn (D p) (g p)) {a b : ℝ} (hab : a < b)
    (hJ : ∀ p, Icc a b ⊆ (D p).regular) {c : P → CurveMap M}
    (hc : ∀ p, (c p).SmoothOn (I := I) (Icc a b))
    (hi : ∀ p, (c p).ImmersedOn (I := I) (Icc a b))
    (heq : ∀ p x t, t ∈ Icc a b → (c p).velocity (I := I) (Icc a b) x t =
      (c p).speed (g p) x t ^ (-2 : ℤ) • (c p).Dx (g p) (c p).X x t) :
    let ξ := fun p t x =>
      -(deriv (fun y => (c p).speed (g p) y t) x /
        (c p).speed (g p) x t ^ 2) / (c p).speed (g p) x t
    (∀ p, ContDiffOn ℝ ∞ (Function.uncurry (ξ p)) (Icc a b ×ˢ univ)) →
    (∀ k j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDerivWithin k
        (fun t => iteratedDeriv j (ξ q.1 t) q.2.2) (Icc a b) q.2.1)
      (univ ×ˢ Icc a b ×ˢ univ)) →
    ∃ (F : P → ℝ → (AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ)))
      (γ : P → ℝ → ℝ → ℝ),
      (∀ p, CurveMap.IsSolutionOn (I := I)
        (fun z t => c p (F p t z) t) (g p) (Icc a b)) ∧
      (∀ p z, F p a z = z) ∧
      (∀ p, ContDiffOn ℝ ∞ (Function.uncurry (γ p)) (univ ×ˢ Icc a b)) ∧
      (∀ p x t, t ∈ Icc a b →
        (γ p x t : AddCircle (1 : ℝ)) = F p t (x : AddCircle (1 : ℝ))) ∧
      (∀ p x t, t ∈ Icc a b → γ p (x + 1) t = γ p x t + 1) ∧
      (∀ p x, γ p x a = x) ∧
      (∀ p x, IsIntegralCurveOn (γ p x) (ξ p) (Icc a b)) ∧
      ∀ n : ℕ, ContinuousOn
        (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
          (fun v : ℝ × ℝ => γ q.1 v.2 v.1) (Icc a b ×ˢ univ) q.2)
        (univ ×ˢ Icc a b ×ˢ univ) := by
  intro ξ hξ hξjets
  obtain ⟨F, γ, hsol, hF0, hγsm, hγcoe, hγper, hγ0, hγode, hγconv⟩ :=
    exists_fixed_normalizing_flows hG hab hJ hc hi heq
  have hspeed (k : ℕ) : ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDeriv (k + 1)
        (fun x => (c q.1).speed (g q.1) x q.2.2 ^ (-2 : ℤ)) q.2.1)
      (univ ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc a b) := by
    have hswap : ContinuousOn (fun q : P × ℝ × ℝ => (q.1, q.2.2, q.2.1))
        (univ ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc a b) := by fun_prop
    have hcont := (hξjets 0 k).comp hswap (fun q hq => ⟨hq.1, hq.2.2, mem_univ _⟩)
    simp only [iteratedDerivWithin_zero] at hcont
    apply ((continuousOn_const (c := (2 : ℝ))).mul hcont).congr
    intro q hq
    have hid := CurveMap.iteratedDeriv_neg_deriv_speed_div_sq_div_speed
      (g := g q.1) (hc q.1) (hi q.1) hq.2.2 k q.2.1
    change iteratedDeriv k (ξ q.1 q.2.2) q.2.1 = _ at hid
    change _ = 2 * iteratedDeriv k (ξ q.1 q.2.2) q.2.1
    linarith
  have hspeedconv (p : P) (k : ℕ) : TendstoUniformlyOn
      (fun q (v : ℝ × ℝ) => iteratedDeriv (k + 1)
        (fun x => (c q).speed (g q) x v.2 ^ (-2 : ℤ)) v.1)
      (fun v : ℝ × ℝ => iteratedDeriv (k + 1)
        (fun x => (c p).speed (g p) x v.2 ^ (-2 : ℤ)) v.1)
      (𝓝 p) (Icc (0 : ℝ) 1 ×ˢ Icc a b) :=
    DifferentialGeometry.Analysis.tendstoUniformlyOn_of_continuousOn_prod
      (isCompact_Icc.prod isCompact_Icc) (hspeed k) p
  have hγjets (j : ℕ) : ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDeriv j (fun x => γ q.1 x q.2.2) q.2.1)
      (univ ×ˢ univ ×ˢ Icc a b) := by
    apply DifferentialGeometry.Analysis.continuousOn_iteratedDeriv_fst_of_tendstoUniformlyOn
      hab (fun p _ => hγsm p)
    intro p _ K hK k
    simpa only [nhdsWithin_univ] using hγconv (𝓝 p) p (hspeedconv p) K hK k
  have hγtime (p : P) : ContDiffOn ℝ ∞
      (fun v : ℝ × ℝ => γ p v.2 v.1) (Icc a b ×ˢ univ) :=
    (hγsm p).comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun q hq => ⟨hq.2, hq.1⟩)
  refine ⟨F, γ, hsol, hF0, hγsm, hγcoe, hγper, hγ0, hγode, ?_⟩
  intro n
  apply DifferentialGeometry.Analysis.continuousOn_iteratedFDerivWithin_of_scalar_ode
    (uniqueDiffOn_Icc hab) ?_ isOpen_univ
    (γ := fun p t x => γ p x t) (ξ := ξ)
    (fun p _ => hγtime p) (fun p _ => hξ p) ?_ hξjets ?_ n
  · rw [interior_Icc, closure_Ioo hab.ne]
  · intro j
    have hswap : ContinuousOn (fun q : P × ℝ × ℝ => (q.1, q.2.2, q.2.1))
        (univ ×ˢ Icc a b ×ˢ univ) := by fun_prop
    exact (hγjets j).comp hswap (fun q hq => ⟨hq.1, hq.2.2, hq.2.1⟩)
  · intro p _ t ht x _
    exact hγode p x t ht

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis

private theorem continuousOn_iteratedFDerivWithin_comp_swap
    {P F : Type*} [TopologicalSpace P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set P} {J : Set ℝ} {d : P → ℝ × ℝ → F} {n : ℕ}
    (hJ : UniqueDiffOn ℝ J)
    (hd : ∀ p ∈ S, ContDiffOn ℝ n (d p) (J ×ˢ univ))
    (hjet : ∀ k ≤ n, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ k (d q.1) (J ×ˢ univ) q.2)
      (S ×ˢ J ×ˢ univ)) :
    ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
        (fun z : ℝ × ℝ => d q.1 (z.2, z.1)) (univ ×ˢ J) q.2)
      (S ×ˢ univ ×ˢ J) := by
  have hswap : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (z.2, z.1)) :=
    contDiff_snd.prodMk contDiff_fst
  apply continuousOn_iteratedFDerivWithin_comp (uniqueDiffOn_univ.prod hJ)
    (hJ.prod uniqueDiffOn_univ)
    (fun _ _ => hswap.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top : (n : ℕ∞ω) ≤ ∞))
    hd ?_ hjet
    (fun _ hq => ⟨hq.2.2, mem_univ _⟩)
  intro k hk
  have hs : ContDiffOn ℝ k (fun z : ℝ × ℝ => (z.2, z.1)) (univ ×ˢ J) :=
    hswap.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top : (k : ℕ∞ω) ≤ ∞)
  exact (hs.continuousOn_iteratedFDerivWithin le_rfl (uniqueDiffOn_univ.prod hJ)).comp
    continuousOn_snd (fun _ hq => hq.2)

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem continuous_smoothCylinderTopology_reparametrize_of_ambient_jets
    {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace P]
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hJcompact : IsCompact J)
    (c : P → CurveMap M) (d : P → CurveMap (EuclideanSpace ℝ (Fin N)))
    (F : P → ℝ → AddCircle (1 : ℝ) → AddCircle (1 : ℝ))
    (γ : P → ℝ → ℝ → ℝ)
    (hcd : ∀ p z t, t ∈ J → e.map (c p z t) = d p z t)
    (hγcoe : ∀ p x t, t ∈ J →
      (γ p x t : AddCircle (1 : ℝ)) = F p t (x : AddCircle (1 : ℝ)))
    (hγsmooth : ∀ p, ContDiffOn ℝ ∞ (Function.uncurry (γ p)) (univ ×ˢ J))
    (hγjet : ∀ n : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
        (fun z : ℝ × ℝ => γ q.1 z.2 z.1) (J ×ˢ univ) q.2)
      (univ ×ˢ J ×ˢ univ))
    (hd : ∀ p, ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => (d p).lift z.2 z.1) (J ×ˢ univ))
    (hdjet : ∀ n : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
        (fun z : ℝ × ℝ => (d q.1).lift z.2 z.1) (J ×ˢ univ) q.2)
      (univ ×ˢ J ×ˢ univ)) :
    @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e J)
      (fun p z t => c p (F p t z) t) := by
  let v := fun p (z : ℝ × ℝ) => (d p).lift (γ p z.2 z.1) z.1
  have hγtime (p : P) : ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => γ p z.2 z.1) (J ×ˢ univ) :=
    (hγsmooth p).comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun q hq => ⟨hq.2, hq.1⟩)
  have hv (p : P) : ContDiffOn ℝ ∞ (v p) (J ×ˢ univ) :=
    (hd p).comp (contDiffOn_fst.prodMk (hγtime p))
      (fun _ hq => ⟨hq.1, mem_univ _⟩)
  have hvjet (n : ℕ) : ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n (v q.1) (J ×ˢ univ) q.2)
      (univ ×ˢ J ×ˢ univ) :=
    Analysis.continuousOn_iteratedFDerivWithin_comp_graph hJ uniqueDiffOn_univ
      (fun p _ => (hγtime p).of_le
        (WithTop.coe_le_coe.mpr le_top : (n : ℕ∞ω) ≤ ∞))
      (fun p _ => (hd p).of_le
        (WithTop.coe_le_coe.mpr le_top : (n : ℕ∞ω) ≤ ∞))
      (fun k _ => hγjet k) (fun k _ => hdjet k)
  apply continuous_smoothCylinderTopology_of_continuousOn_jets e hJcompact
  intro n
  have hswap := Analysis.continuousOn_iteratedFDerivWithin_comp_swap hJ
    (fun p _ => (hv p).of_le
      (WithTop.coe_le_coe.mpr le_top : (n : ℕ∞ω) ≤ ∞))
    (fun k (_ : k ≤ n) => hvjet k)
  apply (hswap.mono (by intro q hq; exact ⟨hq.1, mem_univ _, hq.2.2⟩)).congr
  intro q hq
  apply iteratedFDerivWithin_congr (s := univ ×ˢ J) _
    (show q.2 ∈ univ ×ˢ J from ⟨mem_univ _, hq.2.2⟩) n
  intro z hz
  change e.map (c q.1 (F q.1 z.2 (z.1 : AddCircle (1 : ℝ))) z.2) =
    d q.1 (γ q.1 z.1 z.2 : AddCircle (1 : ℝ)) z.2
  rw [hγcoe q.1 z.1 z.2 hz.2]
  exact hcd q.1 _ z.2 hz.2

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

section

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval MetricFamilySmoothOn)
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem exists_continuous_solution_family_of_retraction_jets
    {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [TopologicalSpace P] {N : ℕ} {T : ℝ} (hT : 0 < T)
    {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) (σ : P → ℝ) (hσ : ContinuousOn σ univ)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {r : EuclideanSpace ℝ (Fin N) → M}
    {V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin N))}
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I ∞ r V)
    (hEV : range e.map ⊆ V) (hleft : ∀ p, r (e.map p) = p) (β : V)
    (c : P → CurveMap M) (d : P → CurveMap (EuclideanSpace ℝ (Fin N)))
    (initial : P → AddCircle (1 : ℝ) → M)
    (hinit : ∀ p z, c p z 0 = initial p z)
    (hc : ∀ p, (c p).SmoothOn (I := I) (Icc 0 T))
    (hi : ∀ p, (c p).ImmersedOn (I := I) (Icc 0 T))
    (hcd : ∀ p z t, t ∈ Icc 0 T → e.map (c p z t) = d p z t)
    (heq : ∀ p x t, t ∈ Icc 0 T → (c p).velocity (I := I) (Icc 0 T) x t =
      (c p).speed (fun s => g (σ p + s)) x t ^ (-2 : ℤ) •
        (c p).Dx (fun s => g (σ p + s)) (c p).X x t)
    (hd : ∀ p, ContDiffOn ℝ ∞
      (fun q : ℝ × ℝ => (d p).lift q.2 q.1) (Icc 0 T ×ˢ univ))
    (hmixed : ∀ k j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDerivWithin k
        (fun t => iteratedDeriv j (fun x => (d q.1).lift x t) q.2.2)
          (Icc 0 T) q.2.1) (univ ×ˢ Icc 0 T ×ˢ univ))
    (hdjet : ∀ n : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
        (fun z : ℝ × ℝ => (d q.1).lift z.2 z.1) (Icc 0 T ×ˢ univ) q.2)
      (univ ×ˢ Icc 0 T ×ˢ univ))
    (hjet : ∀ p t, t ∈ Icc 0 T → ∀ x : ℝ,
      (σ p + t, (d p).lift x t, deriv (fun y => (d p).lift y t) x) ∈
        curveShorteningChartFirstJetDomain D
          (fun s => Geometry.Riemannian.retractionMetric (g s) e.smooth hr) β) :
    ∃ solutions : P → CurveMap M,
      @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc 0 T)) solutions ∧
        ∀ p, (solutions p).IsSolutionOn (fun t => g (σ p + t)) (Icc 0 T) ∧
          ∀ z, solutions p z 0 = initial p z := by
  have hacc : Icc (0 : ℝ) T ⊆ closure (interior (Icc (0 : ℝ) T)) := by
    rw [interior_Icc, closure_Ioo hT.ne]
  obtain ⟨hξsmooth, hξjets⟩ :=
    CurveMap.contDiffOn_and_continuousOn_mixed_gaugeCoefficient_of_retraction_jets
      (uniqueDiffOn_Icc hT) hacc g hg σ hσ
      e.smooth hr hEV hleft β c d (fun p _ => hc p) (fun p _ => hi p)
      (fun p _ => hcd p) (fun p _ => hd p) hmixed (fun p _ => hjet p)
  have hgparam (p : P) : MetricFamilySmoothOn (D.timeShift (σ p))
      (fun s => g (σ p + s)) := by
    simpa only [add_comm] using hg.timeShift (σ p)
  have hreg (p : P) : Icc 0 T ⊆ (D.timeShift (σ p)).regular := by
    intro t ht
    change t + σ p ∈ D.regular
    have hh : σ p + t ∈ D.regular := (hjet p t ht 0).1
    simpa only [add_comm] using hh
  obtain ⟨F, γ, hsol, hF0, hγsmooth, hγcoe, _, _, _, hγjet⟩ :=
    exists_fixed_normalizing_flows_continuousOn_iteratedFDerivWithin
      hgparam hT hreg hc hi heq
      (fun p => hξsmooth p (mem_univ _)) hξjets
  refine ⟨fun p z t => c p (F p t z) t, ?_, ?_⟩
  · exact continuous_smoothCylinderTopology_reparametrize_of_ambient_jets e
      (uniqueDiffOn_Icc hT) isCompact_Icc c d (fun p t => F p t) γ hcd hγcoe
      hγsmooth hγjet hd hdjet
  · intro p
    refine ⟨hsol p, ?_⟩
    intro z
    change c p (F p 0 z) 0 = initial p z
    rw [hF0 p z]
    exact hinit p z

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

section

open private
  CircleHsPi
  circleHsPiInclusion from
DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.AddCircleShiftedCoefficients
open private
  ambientSobolev
  geometric_coefficients_contDiffOn
  firstJetCoordinates from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.InitialState
open private
  fixedAmbientSobolev from
DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Sobolev.ReferenceSolutions
open private vectorTensorHsNormedSpace in
  DifferentialGeometry.Analysis.Parabolic.QuasiLinear.tendsto_heatVectorForcingResidualL

noncomputable section

open Set
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩
attribute [local instance] vectorTensorHsNormedSpace

theorem curveShorteningLocalUniformDependence_of_compact
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b) :
    curveShorteningLocalUniformDependence (I := I) (M := M) B := by
  intro t₀ c₀ N e
  let : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  let : Nonempty M := ⟨c₀.map 0⟩
  obtain ⟨r, O, hO, heO, hr, hleft⟩ :=
    Geometry.exists_smooth_neighborhood_retraction
      e.smooth e.isClosedEmbedding.isEmbedding e.injective_mfderiv
  let V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin N)) := ⟨O, hO⟩
  have hrV : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) I ∞ r V := hr
  let β : V := ⟨e.map (c₀.map 0), heO (mem_range_self _)⟩
  have hG := metricFamilySmoothOn_retractionMetric B.family.metric B.smooth e.smooth hrV
  have ht₀ : t₀.val ∈ D.regular := B.regular ⟨t₀.property.1, t₀.property.2.le⟩
  let gshift : ℝ → SmoothRiemannianMetric I M := fun s => B.family.metric (t₀.val + s)
  let g₀ := c₀.pullbackMetric (gshift 0)
  let fref : CircleHsPi g₀ (Fin N) (((1 : ℕ) : ℝ) + 2) :=
    ambientSobolev c₀ (gshift 0) e.map e.smooth (((1 : ℕ) : ℝ) + 2)
  obtain ⟨_, δ, ρ, _, _, alpha, reaction, hcoeff, hprincipal,
      T, hT, _, U, hU, hmem, f, hf, u, force, _, hforce, hend, htime, hfacts⟩ :=
    SmoothImmersion.ambient_reference_solutions_on_initial_time_neighborhood
      c₀ B.family.metric t₀ ht₀ e hrV heO hleft β hG
  let σ : U → ℝ := fun p => p.val.1.val - t₀.val
  let initial : U → SmoothImmersion (I := I) (M := M) := fun p => p.val.2
  have hσ : Continuous σ := by fun_prop
  have hinitial : Continuous initial := continuous_snd.comp continuous_subtype_val
  have hgshift : MetricFamilySmoothOn (D.timeShift t₀.val) gshift := by
    simpa only [gshift, add_comm] using B.smooth.timeShift t₀.val
  have hgambient := metricFamilySmoothOn_retractionMetric gshift hgshift e.smooth hrV
  obtain ⟨hS, hdiffusion, hdrift⟩ := geometric_coefficients_contDiffOn hgambient β
  obtain ⟨hlift, W, hW, hWlim, hWpin⟩ :=
    SmoothImmersion.reference_exists_fluctuation_sobolev_representatives_timeShift
      (D := univ) e g₀ hT σ hσ.continuousOn initial hinitial.continuousOn fref f hf
      (curveShorteningChartDiffusionCoefficient
        (fun t => Geometry.Riemannian.retractionMetric (gshift t) e.smooth hrV) β ∘
        firstJetCoordinates N)
      (fun z i => curveShorteningParametricChartReaction
        (fun t => Geometry.Riemannian.retractionMetric (gshift t) e.smooth hrV) β
        (firstJetCoordinates N z) i)
      hdiffusion hdrift hS alpha reaction u force hforce.continuousOn
      hcoeff hprincipal hfacts htime
  obtain ⟨hc, hd, hmixed, hdjet, hjet⟩ :=
    SmoothImmersion.reference_selected_retraction_and_ambient_jets
      (S := univ) hT gshift hgshift σ hσ.continuousOn e g₀ initial
      hinitial.continuousOn fref f (fun p _ => hf p) alpha reaction
      (fun p _ => (htime p).1) (fun p _ => (htime p).2)
      u force W hW hWlim hrV heO hleft β hcoeff
      (fun p _ => hfacts p) (fun p _ => hlift p) hWpin
  obtain ⟨solutions, hcontinuous, hsol⟩ :=
    exists_continuous_solution_family_of_retraction_jets hT gshift hgshift σ
      hσ.continuousOn e hrV heO hleft β _ _ (fun p => (initial p).map)
      (fun p => (hc p (mem_univ _)).2.1)
      (fun p => (hc p (mem_univ _)).1) (fun p => (hc p (mem_univ _)).2.2.2.1)
      (fun p => (hc p (mem_univ _)).2.2.1)
      (fun p => (hc p (mem_univ _)).2.2.2.2)
      (fun p => hd p (mem_univ _)) hmixed hdjet
      (fun p => hjet p (mem_univ _))
  refine ⟨T, hT, U, hU, hmem, solutions, hcontinuous, ?_⟩
  intro p
  refine ⟨hend p, ?_, (hsol p).2⟩
  have hg : (fun s => gshift (σ p + s)) =
      (fun s => B.family.metric (p.val.1.val + s)) := by
    funext s
    change B.family.metric (t₀.val + (p.val.1.val - t₀.val + s)) = _
    congr 1
    ring
  rw [← hg]
  exact (hsol p).1

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end
