import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity

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

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] t2M compactM nonemptyM
  hBoundary [SigmaCompactSpace M] in
theorem smoothCylinderTopology_continuousAt_congr {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] {J : Set ℝ} {f g : P → CurveMap M} {p : P}
    (h : ∀ p z t, t ∈ J → f p z t = g p z t)
    (hf : @ContinuousAt P (CurveMap M) inferInstance (smoothCylinderTopology e J) f p) :
    @ContinuousAt P (CurveMap M) inferInstance (smoothCylinderTopology e J) g p := by
  simp only [ContinuousAt, TopologicalSpace.tendsto_nhds_generateFrom_iff] at hf ⊢
  rintro s ⟨c₀, m, ε, hε, rfl⟩ hgs
  have hiff : ∀ d d' : CurveMap M, (∀ z t, t ∈ J → d z t = d' z t) →
      ((∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
          ‖iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d.lift r.1 r.2)) (univ ×ˢ J) q -
           iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (c₀.lift r.1 r.2))
            (univ ×ˢ J) q‖ ≤ ρ) ↔
       (∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
          ‖iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d'.lift r.1 r.2)) (univ ×ˢ J) q -
           iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (c₀.lift r.1 r.2))
            (univ ×ˢ J) q‖ ≤ ρ)) := by
    intro d d' hdd
    have hkey : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
        iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d.lift r.1 r.2)) (univ ×ˢ J) q =
        iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d'.lift r.1 r.2)) (univ ×ˢ J) q :=
      fun q hq => smoothCylinderJets_eq_of_eqOn e hdd m q ⟨mem_univ _, hq.2⟩
    constructor <;> rintro ⟨ρ, hρ, hb⟩ <;> refine ⟨ρ, hρ, fun q hq => ?_⟩
    · rw [← hkey q hq]; exact hb q hq
    · rw [hkey q hq]; exact hb q hq
  have hfp : f p ∈ {d : CurveMap M | ∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d.lift r.1 r.2)) (univ ×ˢ J) q -
       iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (c₀.lift r.1 r.2))
        (univ ×ˢ J) q‖ ≤ ρ} :=
    (hiff (g p) (f p) (fun z t ht => (h p z t ht).symm)).mp hgs
  have hpre : g ⁻¹' {d : CurveMap M | ∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d.lift r.1 r.2)) (univ ×ˢ J) q -
       iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (c₀.lift r.1 r.2))
        (univ ×ˢ J) q‖ ≤ ρ} =
    f ⁻¹' {d : CurveMap M | ∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (d.lift r.1 r.2)) (univ ×ˢ J) q -
       iteratedFDerivWithin ℝ m (fun r : ℝ × ℝ => e.map (c₀.lift r.1 r.2))
        (univ ×ˢ J) q‖ ≤ ρ} := by
    ext q
    exact hiff (g q) (f q) (fun z t ht => (h q z t ht).symm)
  rw [hpre]
  exact hf _ ⟨c₀, m, ε, hε, rfl⟩ hfp

omit t2M compactM nonemptyM hBoundary [SigmaCompactSpace M] in
theorem compact_family_regular_homotopy_at_start
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinit : @Continuous P _ inferInstance (smoothImmersionTopology e) initial) :
    ∃ homotopy : C(P × Icc a a, Width.RegularLoop I M),
      ∀ (p : P) (t : Icc a a) z, homotopy (p, t) z = (initial p).map z := by
  obtain ⟨loops, hloops⟩ := smooth_immersion_regular_family e initial hinit
  exact ⟨loops.comp ⟨Prod.fst, continuous_fst⟩, fun p _ z => hloops p z⟩

theorem rfs_csf_continuation (B : RicciBackground (I := I) (M := M) D a b)
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    (K : ℝ) (hK : 0 ≤ K)
    (hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ K) :
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
  sorry

theorem maximal_curvature_unbounded (B : RicciBackground (I := I) (M := M) D a b)
    {T : ℝ} (haT : a < T) (hTb : T < b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Ico a T))
    (hmax : ∀ u : ℝ, T < u → u ≤ b →
      ¬∃ extended : CurveMap M, extended.IsSolutionOn B.family.metric (Icc a u) ∧
        ∀ z t, t ∈ Ico a T → extended z t = c z t) :
    ∀ K : ℝ, ∃ x t, t ∈ Ico a T ∧ K < c.curvature B.family.metric x t := by
  intro K
  by_contra! hbound
  have hcurv : ∀ x t, t ∈ Ico a T → c.curvature B.family.metric x t ≤ max K 0 := by
    intro x t ht
    exact (hbound x t ht).trans (le_max_left K 0)
  obtain ⟨cT, hlimit, hclosed, hextend⟩ :=
    rfs_csf_continuation B haT hTb.le c hc (max K 0) (le_max_right K 0) hcurv
  obtain ⟨τ, hτ, hτb, extended, hsol, heq⟩ := hextend hTb
  exact hmax (T + τ) (lt_add_of_pos_right T hτ) hτb ⟨extended, hsol, heq⟩

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
  sorry

theorem compact_family_solution_continuous
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d) (hdb : d ≤ b)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinit : @Continuous P _ inferInstance (smoothImmersionTopology e) initial)
    (solutions : P → CurveMap M)
    (hsol : ∀ p, (solutions p).IsSolutionOn B.family.metric (Icc a d))
    (htrace : ∀ p z, solutions p z a = (initial p).map z) :
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
        (by simp only [T, dif_pos hmem0]) (fun x hx => by simp only [T, dif_pos hx])
    have hT'at : ContinuousAt T' p₀ := by
      have hbase : ContinuousAt (fun p : P => T (φ p)) p₀ := hTat.comp hφcont.continuousAt
      have hev : ∀ᶠ p in 𝓝 p₀, T (φ p) = T' p := by
        filter_upwards [hφcont.continuousAt.preimage_mem_nhds (hUopen.mem_nhds hmem0)]
          with p hp
        have hp' : φ p ∈ U := hp
        simp only [T', dif_pos hp']
      exact hbase.congr hev
    have hagree : ∀ p z t, t ∈ Icc a d → T' p z t = solutions p z t := by
      intro p z t ht
      by_cases h : φ p ∈ U
      · have hTp : T' p = sols ⟨φ p, h⟩ := by
          simp only [T', T, dif_pos h]
        rw [hTp]
        refine local_solution_unique B (le_refl a) had had hdb hdb (sols ⟨φ p, h⟩) (solutions p)
          (hprop ⟨φ p, h⟩).1 (hsol p) (fun z => (hprop ⟨φ p, h⟩).2 z) z t ?_
        simpa only [min_self] using ht
      · simp only [T', dif_neg h]
    exact smoothCylinderTopology_continuousAt_congr e hagree hT'at

theorem compact_family_regular_homotopy
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d) (hdb : d ≤ b)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinit : @Continuous P _ inferInstance (smoothImmersionTopology e) initial)
    (solutions : P → CurveMap M)
    (hsol : ∀ p, (solutions p).IsSolutionOn B.family.metric (Icc a d))
    (htrace : ∀ p z, solutions p z a = (initial p).map z) :
    ∃ homotopy : C(P × Icc a d, Width.RegularLoop I M),
      ∀ (p : P) (t : Icc a d) z, homotopy (p, t) z = solutions p z t := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
