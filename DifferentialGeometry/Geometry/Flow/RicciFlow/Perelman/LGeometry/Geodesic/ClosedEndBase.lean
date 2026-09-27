import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ClosedStartCurve

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set Filter
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.ODE.Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lRegularizedDomain_eq_empty_of_not_mem_regular (S : SolutionOn (I := I) (M := M) D)
    {T : ℝ} (hT : T ∉ D.regular) (x : M) (Z : TangentSpace I x) :
    lRegularizedDomain S T x Z = ∅ := by
  refine eq_empty_of_forall_notMem fun s hs => hT ?_
  obtain ⟨_, J, -, -, h0J, -, halpha⟩ := hs
  simpa using (halpha.2.2 0 h0J).1

theorem lPhaseField_contDiffAt_of_closed_end (S : SolutionOn (I := I) (M := M) D) {a b : ℝ}
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ioc a b ×ˢ (univ : Set M)))
    (x0 : M) {s : ℝ} {z : E × E} (hs : s ^ 2 < b - a)
    (hz : z.1 ∈ interior (extChartAt I x0).target) :
    ContDiffAt ℝ ∞ (Function.uncurry (lPhaseField S b x0)) (s, z) := by
  have hO : IsOpen {p : ℝ × (E × E) |
      p.1 ^ 2 < b - a ∧ p.2.1 ∈ interior (extChartAt I x0).target} :=
    (isOpen_lt (continuous_fst.pow 2) continuous_const).inter
      (isOpen_interior.preimage continuous_snd.fst)
  refine (lPhaseField_contDiffOn_of_jointContMDiffOn S hmetric b x0).contDiffAt
    (mem_of_superset (hO.mem_nhds ⟨hs, hz⟩) ?_)
  rintro p ⟨hp, hpz⟩
  exact ⟨⟨by linarith, by nlinarith [sq_nonneg p.1]⟩, hpz⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedFamily_of_lPhaseField_contDiffAt
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (Z0 : TangentSpace I x) {ρ : ℝ}
    (hρ : 0 < ρ) (hreg : ∀ s : ℝ, s ^ 2 < ρ → T - s ^ 2 ∈ D.regular)
    (hF : ∀ (s : ℝ) (z : E × E), s ^ 2 < ρ → z.1 ∈ interior (extChartAt I x).target →
      ContDiffAt ℝ ∞ (Function.uncurry (lPhaseField S T x)) (s, z)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set E, IsOpen V ∧ Z0 ∈ V ∧ ∃ α : E × ℝ → M,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I ∞ α (V ×ˢ Ioo (-ε) ε) ∧
      ∀ Z ∈ V, IsLRegularizedCurveOn S T (fun s => α (Z, s)) (Ioo (-ε) ε) x Z := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Ω : Set (ℝ × (E × E)) :=
    {p | p.1 ^ 2 < ρ ∧ p.2.1 ∈ interior (extChartAt I x).target}
  have hΩ : IsOpen Ω := (isOpen_lt (continuous_fst.pow 2) continuous_const).inter
    (isOpen_interior.preimage continuous_snd.fst)
  let vf : ℝ × (E × E) → ℝ × (E × E) := fun p => ((1 : ℝ), lPhaseField S T x p.1 p.2)
  have hvf : ContDiffOn ℝ ∞ vf Ω := fun p hp =>
    (contDiffAt_const.prodMk (hF p.1 p.2 hp.1 hp.2)).contDiffWithinAt
  let seed : E → E × E := fun Z => (extChartAt I x x, (2 : ℝ) • Z)
  have hseed : ContDiff ℝ ∞ seed := contDiff_const.prodMk
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : E => (2 : ℝ))).smul contDiff_id)
  have hx : (extChartAt I x x) ∈ interior (extChartAt I x).target := by
    rw [(isOpen_extChartAt_target (I := I) x).interior_eq]
    exact mem_extChartAt_target (I := I) x
  let y0 : ℝ × (E × E) := (0, seed Z0)
  have hy0 : y0 ∈ Ω := by
    refine ⟨?_, hx⟩
    change (0 : ℝ) ^ 2 < ρ
    rw [zero_pow two_ne_zero]
    exact hρ
  obtain ⟨ε, hε, hlocal⟩ := exists_flow_on hΩ hvf isCompact_singleton
    (singleton_subset_iff.mpr hy0)
  obtain ⟨U, hUo, hy0U, Ψ, hΨ0, hΨsm, hΨd, hΨmap⟩ := hlocal y0 (mem_singleton y0)
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have htime : ∀ y ∈ U, ∀ r ∈ Ioo (-ε) ε, (Ψ (y, r)).1 = y.1 + r := by
    intro y hy
    let phi : ℝ → ℝ := fun r => (Ψ (y, r)).1 - y.1
    have hphi : ∀ r ∈ Ioo (-ε) ε, HasDerivAt phi 1 r := by
      intro r hr
      have hfst := hasFDerivAt_fst.comp_hasDerivAt r (hΨd y hy r hr)
      simpa [phi, vf, Function.comp_def] using hfst.sub_const y.1
    have hphi0 : phi 0 = 0 := by simp only [phi, hΨ0 y hy, sub_self]
    intro r hr
    have h := DifferentialGeometry.Analysis.ODE.hasDerivAt_one_eq_self_on_Ioo
      phi hzero hphi hphi0 r hr
    simp only [phi] at h
    linarith
  let V : Set E := {Z | ((0 : ℝ), seed Z) ∈ U}
  have hVo : IsOpen V := hUo.preimage (continuous_const.prodMk hseed.continuous)
  let ph : E × ℝ → E × E := fun p => (Ψ (((0 : ℝ), seed p.1), p.2)).2
  have hph : ContDiffOn ℝ ∞ ph (V ×ˢ Ioo (-ε) ε) := by
    have hin : ContDiff ℝ ∞ (fun p : E × ℝ => ((((0 : ℝ), seed p.1) : ℝ × (E × E)), p.2)) :=
      (contDiff_const.prodMk (hseed.comp contDiff_fst)).prodMk contDiff_snd
    exact (hΨsm.comp hin.contDiffOn fun p hp => ⟨hp.1, hp.2⟩).snd
  have hdata : ∀ Z ∈ V, ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt (fun r => ph (Z, r)) (lPhaseField S T x s (ph (Z, s))) s ∧
        T - s ^ 2 ∈ D.regular ∧ (ph (Z, s)).1 ∈ interior (extChartAt I x).target := by
    intro Z hZ s hs
    have ht : (Ψ (((0 : ℝ), seed Z), s)).1 = s := by
      rw [htime _ hZ s hs, zero_add]
    have hmap := hΨmap (show ((((0 : ℝ), seed Z), s) : (ℝ × (E × E)) × ℝ) ∈ U ×ˢ Ioo (-ε) ε
      from ⟨hZ, hs⟩)
    rw [show Ψ (((0 : ℝ), seed Z), s) = (s, ph (Z, s)) from Prod.ext ht rfl] at hmap
    refine ⟨?_, hreg s hmap.1, hmap.2⟩
    have hsnd := hasFDerivAt_snd.comp_hasDerivAt s (hΨd _ hZ s hs)
    simpa [ph, vf, ht, Function.comp_def] using hsnd
  let α : E × ℝ → M := fun p => (extChartAt I x).symm (ph p).1
  refine ⟨ε, hε, V, hVo, hy0U, α, ?_, ?_⟩
  · have hphMD : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞ (fun p => (ph p).1)
        (V ×ˢ Ioo (-ε) ε) := hph.fst.contMDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hphMD
    refine (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x).comp hphMD ?_
    intro p hp
    exact (interior_subset (hdata p.1 hp.1 p.2 hp.2).2.2 : (ph p).1 ∈ (extChartAt I x).target)
  intro Z hZ
  let z : ℝ → E × E := fun s => ph (Z, s)
  have hgeo : IsLRegularizedGeodesicOn S T (lPhaseCurve (I := I) x z) (Ioo (-ε) ε) :=
    isLRegularizedGeodesicOn_lPhaseCurve S T x isOpen_Ioo fun s hs => hdata Z hZ s hs
  have hz0 : z 0 = seed Z := by
    change (Ψ (((0 : ℝ), seed Z), 0)).2 = seed Z
    rw [hΨ0 _ hZ]
  have hγ0 : lPhaseCurve (I := I) x z 0 = x := by
    change (extChartAt I x).symm (z 0).1 = x
    rw [hz0]
    exact (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  have hq : HasDerivAt (fun r : ℝ => (z r).1) (z 0).2 0 := by
    simpa [lPhaseField, Function.comp_def] using
      hasFDerivAt_fst.comp_hasDerivAt 0 (hdata Z hZ 0 hzero).1
  have hvel0 : lVelocity (I := I) (lPhaseCurve (I := I) x z) 0 = 2 • Z := by
    rw [lPhase_velocity (I := I) x z 0 hq (hdata Z hZ 0 hzero).2.2]
    change trivFromE (I := I) x (lPhaseCurve (I := I) x z 0) (z 0).2 = 2 • Z
    rw [hγ0, hz0]
    change trivFromE (I := I) x x ((2 : ℝ) • Z) = (2 : ℕ) • Z
    rw [trivFromE_self_apply]
    have hcenterSymm (w : E) :
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x).symm w =
          w := by
      apply (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x).injective
      rw [ContinuousLinearEquiv.apply_symm_apply]
      have hmodel : tangentSpaceModelContinuousLinearEquiv (I := I) x
          (show TangentSpace I x from w) = w := rfl
      exact hmodel.symm.trans
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply (I := I) x
          (show TangentSpace I x from w)).symm
    rw [hcenterSymm]
    simp only [two_smul]
    rfl
  exact ⟨hγ0, hvel0, hgeo⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedFamily_of_closed_end (S : SolutionOn (I := I) (M := M) D)
    {a b : ℝ} (hab : a < b)
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ioc a b ×ˢ (univ : Set M)))
    (hreg : Ioc a b ⊆ D.regular) (x : M) (Z0 : TangentSpace I x) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set E, IsOpen V ∧ Z0 ∈ V ∧ ∃ α : E × ℝ → M,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I ∞ α (V ×ˢ Ioo (-ε) ε) ∧
      ∀ Z ∈ V, IsLRegularizedCurveOn S b (fun s => α (Z, s)) (Ioo (-ε) ε) x Z :=
  exists_lRegularizedFamily_of_lPhaseField_contDiffAt S b x Z0 (sub_pos.mpr hab)
    (fun s hs => hreg ⟨by linarith, by nlinarith [sq_nonneg s]⟩)
    (fun _ _ hs hz => lPhaseField_contDiffAt_of_closed_end S hmetric x hs hz)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem zero_mem_lRegularizedDomain_of_closed_end (S : SolutionOn (I := I) (M := M) D)
    {a b : ℝ} (hab : a < b)
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ioc a b ×ˢ (univ : Set M)))
    (hreg : Ioc a b ⊆ D.regular) (x : M) (Z : TangentSpace I x) :
    (0 : ℝ) ∈ lRegularizedDomain S b x Z := by
  obtain ⟨ε, hε, V, -, hZV, α, -, hcurves⟩ :=
    exists_lRegularizedFamily_of_closed_end S hab hmetric hreg x Z
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  exact ⟨fun s => α (Z, s), Ioo (-ε) ε, isOpen_Ioo, isPreconnected_Ioo, hzero, hzero,
    hcurves Z hZV⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
