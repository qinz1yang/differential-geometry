import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ParabolicUniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.FamilyDependence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening


private theorem continuousAt_of_eq_subtype_val {X α : Type*} [TopologicalSpace X]
    [TopologicalSpace α] {s : Set α} (hs : IsOpen s) (sol : s → X) (hcont : Continuous sol)
    {y : α} (hy : y ∈ s) {F : α → X} (hFy : F y = sol ⟨y, hy⟩)
    (hFs : ∀ (x : α) (hx : x ∈ s), F x = sol ⟨x, hx⟩) : ContinuousAt F y := by
  rw [ContinuousAt, Filter.tendsto_def]
  intro W hW
  rw [hFy] at hW
  have h1 : sol ⁻¹' W ∈ 𝓝 (⟨y, hy⟩ : s) := hcont.continuousAt.preimage_mem_nhds hW
  rw [nhds_subtype] at h1
  obtain ⟨Z, hZ, hZsub⟩ := Filter.mem_comap.mp h1
  refine Filter.mem_of_superset (Filter.inter_mem hZ (hs.mem_nhds hy)) ?_
  intro z hz
  simp only [Set.mem_preimage] at hz ⊢
  rw [hFs z hz.2]
  exact hZsub (a := ⟨z, hz.2⟩) hz.1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



variable [SigmaCompactSpace M] [t2M : T2Space M] [compactM : CompactSpace M] [nonemptyM : Nonempty M]
  [hBoundary : I.Boundaryless]
include t2M compactM nonemptyM hBoundary
variable {D : RealTimeInterval} {a b : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] t2M compactM nonemptyM hBoundary
  [SigmaCompactSpace M] in
theorem compact_family_regular_homotopy_at_start
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinit : @Continuous P _ inferInstance (smoothImmersionTopology e) initial)
    (h : immersionContinuityIntoRegularLoops (I := I) (M := M)) :
    ∃ homotopy : C(P × Icc a a, Width.RegularLoop I M),
      ∀ (p : P) (t : Icc a a) z, homotopy (p, t) z = (initial p).map z := by
  obtain ⟨loops, hloops⟩ := smooth_immersion_regular_family e initial hinit h
  exact ⟨loops.comp ⟨Prod.fst, continuous_fst⟩, fun p _ z => hloops p z⟩

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
theorem rfs_csf_continuation (B : RicciBackground (I := I) (M := M) D a b)
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    (K : ℝ) (hK : 0 ≤ K)
    (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K)
    (hclose : curveShorteningTerminalClosure (I := I) (M := M) B)
    (hwin : curveShorteningLocalWindow (I := I) (M := M) B.toSmoothMetricWindow)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B.toSmoothMetricWindow)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    ∃ cT : SmoothImmersion (I := I) (M := M),
      (∀ (N : ℕ) (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N),
        letI := smoothImmersionTopology e
        Tendsto
          (fun t : {t : ℝ // t ∈ Ico a T} => SmoothImmersion.slice c hc.smooth hc.immersed t.1 t.2)
          (Filter.comap Subtype.val (𝓝[<] T)) (𝓝 cT)) ∧
      (∃ closed : CurveMap M, closed.IsSolutionOn B.family.metric (Icc a T) ∧
        (∀ z t, t ∈ Ico a T → closed z t = c z t) ∧ (∀ z, closed z T = cT.map z)) ∧
      (T < b → ∃ τ > 0, T + τ ≤ b ∧ ∃ extended : CurveMap M,
        extended.IsSolutionOn B.family.metric (Icc a (T + τ)) ∧
        (∀ z t, t ∈ Ico a T → extended z t = c z t)) := by
  obtain ⟨closed, hsol, hagr⟩ := hclose T haT hTb c K hK hc hcurv
  refine ⟨SmoothImmersion.slice closed hsol.smooth hsol.immersed T ⟨haT.le, le_rfl⟩, ?_,
    ⟨closed, hsol, hagr, fun z => rfl⟩, ?_⟩
  · intro N' e'
    exact CurveMap.tendsto_slice_of_terminalClosure e' haT hsol hagr hc.smooth hc.immersed
  · intro hTb'
    exact exists_extension_of_localWindow B.toSmoothMetricWindow e haT hTb' hc
      ⟨closed, hsol, hagr⟩ hwin huniq

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
theorem maximal_curvature_unbounded (B : RicciBackground (I := I) (M := M) D a b)
    {T : ℝ} (haT : a < T) (hTb : T < b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    (hmax : ∀ u : ℝ, T < u → u ≤ b →
      ¬∃ extended : CurveMap M, extended.IsSolutionOn B.family.metric (Icc a u) ∧
        ∀ z t, t ∈ Ico a T → extended z t = c z t)
    (hclose : curveShorteningTerminalClosure (I := I) (M := M) B)
    (hwin : curveShorteningLocalWindow (I := I) (M := M) B.toSmoothMetricWindow)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B.toSmoothMetricWindow)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    ∀ K : ℝ, ∃ x t, t ∈ Ico a T ∧ K < c.curvature B.family.metric x t := by
  intro K
  by_contra! hbound
  have hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ max K 0 := by
    intro x t ht
    exact (hbound x t ht).trans (le_max_left K 0)
  obtain ⟨cT, hlimit, hclosed, hextend⟩ :=
    rfs_csf_continuation B haT hTb.le c hc (max K 0) (le_max_right K 0) hcurv hclose hwin huniq e
  obtain ⟨τ, hτ, hτb, extended, hsol, heq⟩ := hextend hTb
  exact hmax (T + τ) (lt_add_of_pos_right T hτ) hτb ⟨extended, hsol, heq⟩

omit [CompleteSpace E] [SigmaCompactSpace M] nonemptyM in
theorem rfs_csf_family_dependence (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d) (hdb : d ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc a d))
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    letI := smoothImmersionTopology e
    ∃ U : Set (SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions) ∧
        ∀ p : U, (solutions p).IsSolutionOn B.family.metric (Icc a d) ∧
          ∀ z, solutions p z a = p.1.map z := by
  exact rfs_csf_family_dependence_of_localUniformDependence B
    (fun _ B' _ => curveShorteningLocalUniformDependence_of_compact B')
    (fun _ B' _ => curveShorteningLocalUniqueness_of_compact B') had hdb c hc e

omit [CompleteSpace E] [SigmaCompactSpace M] nonemptyM in
theorem compact_family_solution_continuous
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d) (hdb : d ≤ b)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinit : @Continuous P _ inferInstance (smoothImmersionTopology e) initial)
    (solutions : P → CurveMap M)
    (hsol : ∀ p, (solutions p).IsSolutionOn B.family.metric (Icc a d))
    (htrace : ∀ p z, solutions p z a = (initial p).map z)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B) :
    @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions :=
  letI instImm : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  letI instCyl : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a d)
  by
    classical
    let φ : P → SmoothImmersion (I := I) (M := M) := fun p =>
      SmoothImmersion.slice (solutions p) (hsol p).smooth (hsol p).immersed a ⟨le_rfl, had.le⟩
    have hφinit : φ = initial := by
      funext p
      exact (SmoothImmersion.mk.injEq _ _ _ _ _ _).mpr (funext fun z => htrace p z)
    have hφcont : Continuous φ := hφinit ▸ hinit
    rw [continuous_iff_continuousAt]
    intro p₀
    obtain ⟨U, hUopen, hmem, sols, hcont, hprop⟩ :=
      rfs_csf_family_dependence B had hdb (solutions p₀) (hsol p₀) e
    have hmem0 : φ p₀ ∈ U := hmem
    let T : SmoothImmersion (I := I) (M := M) → CurveMap M := fun x =>
      if h : x ∈ U then sols ⟨x, h⟩ else sols ⟨φ p₀, hmem0⟩
    let T' : P → CurveMap M := fun p => if h : φ p ∈ U then T (φ p) else solutions p
    have hTat : ContinuousAt T (φ p₀) :=
      continuousAt_of_eq_subtype_val hUopen sols hcont hmem0 (F := T)
        (by simp only [T, dite_eq_left hmem0]) (fun x hx => by simp only [T, dite_eq_left hx])
    have hT'at : ContinuousAt T' p₀ := by
      have hbase : ContinuousAt (fun p : P => T (φ p)) p₀ := hTat.comp hφcont.continuousAt
      have hev : ∀ᶠ p in 𝓝 p₀, T (φ p) = T' p := by
        filter_upwards [hφcont.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hmem0)]
          with p hp
        have hp' : φ p ∈ U := hp
        simp only [T', dite_eq_left hp']
      exact hbase.congr hev
    have hagree : ∀ p z t, t ∈ Icc a d → T' p z t = solutions p z t := by
      intro p z t ht
      by_cases h : φ p ∈ U
      · have hTp : T' p = sols ⟨φ p, h⟩ := by
          simp only [T', T, dite_eq_left h]
        rw [hTp]
        refine local_solution_unique B (le_refl a) had had hdb hdb (sols ⟨φ p, h⟩) (solutions p)
          (hprop ⟨φ p, h⟩).1 (hsol p) (fun z => (hprop ⟨φ p, h⟩).2 z) huniq z t ?_
        simpa only [min_self] using ht
      · simp only [T', dite_eq_right h]
    exact smoothCylinderTopology_continuousAt_congr e hagree hT'at

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem compact_family_regular_homotopy
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P]
    (solutions : P → CurveMap M)
    (hsol : ∀ p, (solutions p).IsSolutionOn B.family.metric (Icc a d))
    (hcont : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a d)) solutions)
    (hreg : immersionContinuityIntoRegularLoops (I := I) (M := M)) :
    ∃ homotopy : C(P × Icc a d, Width.RegularLoop I M),
      ∀ (p : P) (t : Icc a d) z, homotopy (p, t) z = solutions p z t :=
  letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  by
    have hbridge : Continuous (fun q : P × Icc a d => SmoothImmersion.slice (solutions q.1)
        (hsol q.1).smooth (hsol q.1).immersed q.2.1 q.2.2) :=
      continuous_iff_continuousAt.mpr fun q =>
        continuousAt_slice_smoothImmersion e had hcont (fun p => (hsol p).smooth)
          (fun p => (hsol p).immersed) q
    refine ⟨⟨fun q => regularLoopOfImmersion (SmoothImmersion.slice (solutions q.1) (hsol q.1).smooth
      (hsol q.1).immersed q.2.1 q.2.2), ?_⟩, ?_⟩
    · exact (@Continuous.comp (P × Icc a d) (SmoothImmersion (I := I) (M := M))
        (Width.RegularLoop I M) inferInstance (smoothImmersionTopology e)
        (Width.regularLoopTopologicalSpace (I := I) (Q := M))
        (fun q : P × Icc a d => SmoothImmersion.slice (solutions q.1) (hsol q.1).smooth
          (hsol q.1).immersed q.2.1 q.2.2) (regularLoopOfImmersion (I := I) (M := M)) (hreg N e)
        hbridge)
    · intro p t z
      rfl

omit [CompleteSpace E] [SigmaCompactSpace M] nonemptyM in
theorem CurveMap.exists_solution_extension
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (c : CurveMap M) {T : ℝ} (haT : a < T) (hTb : T < b)
    (hc : c.IsSolutionOn B.family.metric (Icc a T)) :
    ∃ u : ℝ, T < u ∧ u ≤ b ∧ ∃ extended : CurveMap M,
      extended.IsSolutionOn B.family.metric (Icc a u) ∧
      ∀ z t, t ∈ Icc a T → extended z t = c z t := by
  let : Nonempty M := ⟨c 0 a⟩
  obtain ⟨N, ⟨e⟩⟩ := Width.smoothLoopEmbedding_exists (I := I) (Q := M)
  have hcont : @Continuous Unit (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc a T)) (fun _ => c) :=
    @continuous_const Unit (CurveMap M) inferInstance
      (smoothCylinderTopology e (Icc a T)) c
  obtain ⟨u, hTu, hub, V, _, hV, solutions, _, hsol, hagree, _⟩ :=
    exists_continuous_solution_family_extension B
      (curveShorteningLocalUniformDependence_of_compact B)
      (curveShorteningLocalUniqueness_of_compact B) e haT hTb
      (fun _ : Unit => c) hcont (fun _ => hc) ()
  exact ⟨u, hTu, hub, solutions ⟨(), hV⟩, hsol ⟨(), hV⟩, hagree ⟨(), hV⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
