import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.TimeTranslation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing

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
