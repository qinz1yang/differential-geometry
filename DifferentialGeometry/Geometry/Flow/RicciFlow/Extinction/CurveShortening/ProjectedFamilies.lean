import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Ramps

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

section

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  {P T : Type*} [TopologicalSpace P]
  [TopologicalSpace T] [PathConnectedSpace T]

theorem exists_contractible_regular_family_of_pathConnected
    (R : C(T × P, RegularLoop I Q)) (t₀ : T)
    (initial : RegularFamily (I := I) (Q := Q) P)
    (hinit : ∀ p, R (t₀, p) = (initial p).1) :
    ∃ projected : C(T, RegularFamily (I := I) (Q := Q) P),
      (∀ t p, (projected t p).1 = R (t, p)) ∧
      projected t₀ = initial ∧
      ∀ t, FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (projected t)) =
        FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp initial) := by
  have hctr : ∀ t p, IsContractibleLoop (R (t, p)).toContinuousLoop := by
    intro t p
    have hj := (PathConnectedSpace.joined t₀ t).map
      (regularLoopInclusion.continuous.comp
        (R.continuous.comp (continuous_id.prodMk (continuous_const (y := p)))))
    have hhom := (DifferentialGeometry.Topology.homotopic_iff_joined _ _).mpr hj
    obtain ⟨q, hq⟩ := (initial p).2
    refine ⟨q, hhom.symm.trans ?_⟩
    change ContinuousMap.Homotopic (R (t₀, p)).toContinuousLoop (constantLoops q)
    rw [hinit]
    exact hq
  let lifted : C(T × P, ContractibleRegularLoop (I := I) (Q := Q)) :=
    ⟨fun q => ⟨R q, hctr q.1 q.2⟩, R.continuous.subtype_mk _⟩
  let projected : C(T, RegularFamily (I := I) (Q := Q) P) := lifted.curry
  have hat : projected t₀ = initial := by
    apply ContinuousMap.ext
    intro p
    exact Subtype.ext (hinit p)
  refine ⟨projected, fun _ _ => rfl, hat, fun t => ?_⟩
  apply (FreeHomotopyClass.mk_eq_mk_iff _ _).mpr
  let path : Path t t₀ := PathConnectedSpace.somePath t t₀
  have hh : ContinuousMap.Homotopic (projected t) initial := by
    refine ⟨⟨⟨fun q => lifted (path q.1, q.2),
      lifted.continuous.comp ((path.continuous.comp continuous_fst).prodMk continuous_snd)⟩,
      ?_, ?_⟩⟩
    · intro p
      simp only [path.source]
      rfl
    · intro p
      simp only [path.target]
      exact Subtype.ext (hinit p)
  exact (ContinuousMap.Homotopic.refl contractibleRegularLoopInclusion).comp hh

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

end

section

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem continuous_embedded_spatial_jets_of_smoothCylinder
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {a b : ℝ} (hab : a < b) {P : Type*} [TopologicalSpace P]
    {c : P → CurveMap M}
    (hc : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a b)) c)
    (hs : ∀ p, (c p).SmoothOn (I := I) (Icc a b)) (m : ℕ) :
    Continuous (fun q : (P × Icc a b) × ℝ =>
      iteratedDeriv m (fun x => e.map ((c q.1.1).lift x q.1.2.1)) q.2) := by
  let J : P × Icc a b → C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin N)) := fun q =>
    ⟨fun x => iteratedDeriv m (fun y => e.map ((c q.1).lift y q.2.1)) x,
      (((e.smooth.comp (contMDiffOn_univ.mp
        ((c q.1).space_slice_contMDiffOn (Icc a b) (hs q.1)
          q.2.1 q.2.2))).contDiff.continuous_iteratedDeriv
            m (by exact_mod_cast le_top)).comp continuous_subtype_val)⟩
  have hJ : Continuous J := by
    refine continuous_iff_continuousAt.mpr fun q => Metric.tendsto_nhds.mpr ?_
    intro ε hε
    obtain ⟨O, hO, hclose⟩ := exists_nhds_slice_jet_close e hab hc hs m q hε
    filter_upwards [hO] with q' hq'
    apply (ContinuousMap.dist_lt_iff hε).mpr
    intro x
    exact (show dist (J q' x) (J q x) < ε from by
      rw [dist_eq_norm]
      exact hclose q' hq' x.1 x.2)
  have hlocal : Continuous (fun q : (P × Icc a b) × Icc (0 : ℝ) 1 => J q.1 q.2) :=
    continuous_eval.comp ((hJ.comp continuous_fst).prodMk continuous_snd)
  apply DifferentialGeometry.Topology.continuous_of_continuousOn_Icc_of_add_one
  · rw [continuousOn_iff_continuous_domRestrict]
    let ι : (univ ×ˢ Icc (0 : ℝ) 1 : Set ((P × Icc a b) × ℝ)) →
        (P × Icc a b) × Icc (0 : ℝ) 1 := fun q =>
      (q.1.1, ⟨q.1.2, q.2.2⟩)
    have hι : Continuous ι :=
      continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
    exact hlocal.comp hι
  · intro q x
    exact DifferentialGeometry.Topology.periodic_iteratedDeriv
      (f := fun y => e.map ((c q.1).lift y q.2.1))
      (fun y => congrArg e.map ((c q.1).lift_add_period q.2.1 y)) m x

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

section

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def regularSlice (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (t : J) : Width.RegularLoop I M where
  toContinuousLoop := ⟨fun z => c z t, by
    exact (isQuotientMap_quotient_mk' (s := QuotientAddGroup.leftRel
      (AddSubgroup.zmultiples (1 : ℝ)))).continuous_iff.mpr
        (c.smooth_slice hc t.2).continuous⟩
  contMDiff_lift := (c.smooth_slice hc t.2).of_le (by simp)

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] [Nonempty M]

theorem exists_regular_family_of_smoothCylinder
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {a b : ℝ} (hab : a < b) {P : Type*} [TopologicalSpace P]
    (c : P → CurveMap M)
    (hc : @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a b)) c)
    (hs : ∀ p, (c p).SmoothOn (I := I) (Icc a b)) :
    ∃ F : C(P × Icc a b, Width.RegularLoop I M),
      (∀ p t z, F (p, t) z = c p z t) ∧
      (∀ p t, ContMDiff 𝓘(ℝ, ℝ) I ∞ (Width.loopLift (F (p, t)).toContinuousLoop)) ∧
      ∀ m : ℕ, Continuous (fun q : (P × Icc a b) × ℝ =>
        iteratedDeriv m (e.map ∘ Width.loopLift (F q.1).toContinuousLoop) q.2) := by
  let F : P × Icc a b → Width.RegularLoop I M := fun q => regularSlice (c q.1) (hs q.1) q.2
  have hF : Continuous F := by
    apply (Width.continuous_regularLoop_iff e F).mpr
    constructor
    · have hj : Continuous (fun q : (P × Icc a b) × ℝ =>
          e.map ((c q.1.1).lift q.2 q.1.2.1)) := by
        simpa only [iteratedDeriv_zero] using
          continuous_embedded_spatial_jets_of_smoothCylinder e hab hc hs 0
      have hq := (_root_.IsOpenQuotientMap.id (X := P × Icc a b)).prodMap
        (QuotientAddGroup.isOpenQuotientMap_mk
          (N := AddSubgroup.zmultiples (1 : ℝ)))
      exact hq.isQuotientMap.continuous_iff.mpr hj
    · simpa only [iteratedDeriv_one, F, regularSlice, CurveMap.lift, ContinuousMap.coe_mk] using
        continuous_embedded_spatial_jets_of_smoothCylinder e hab hc hs 1
  refine ⟨⟨F, hF⟩, fun _ _ _ => rfl, ?_, ?_⟩
  · intro p t
    exact (c p).smooth_slice (hs p) t.2
  · intro m
    exact continuous_embedded_spatial_jets_of_smoothCylinder e hab hc hs m

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

section

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem contDiffOn_productEmbeddedCoordinates
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {c : ProductCurve M} {J : Set ℝ} (hc : c.SmoothOn (I := I) J) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => productEmbeddedCoordinates e c q.1 q.2)
      (univ ×ˢ J) := by
  have hcir : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ =>
      Complex.exp ((2 * Real.pi * c.y q.1 q.2 : ℝ) * Complex.I)) (univ ×ˢ J) := by
    have hy : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ =>
        (2 * Real.pi * c.y q.1 q.2 : ℝ) * Complex.I) (univ ×ˢ J) :=
      (Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((contDiffOn_const (c := 2 * Real.pi)).mul hc.2)).mul contDiffOn_const
    exact Complex.contDiff_exp.comp_contDiffOn hy
  have hpair := (contDiffOn_liftMap e hc.1).prodMk hcir
  apply hpair.congr
  intro q _
  apply Prod.ext
  · rfl
  · dsimp only [productEmbeddedCoordinates]
    rw [← c.lift_eq, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
      Circle.coe_exp]
    simp

private theorem projection_jet_norm_sub_le
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) {c d : ProductCurve M}
    (hc : c.SmoothOn (I := I) J) (hd : d.SmoothOn (I := I) J)
    (m : ℕ) (q : ℝ × ℝ) (hq : q ∈ univ ×ˢ J) :
    ‖iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (c.projection.lift q.1 q.2))
        (univ ×ˢ J) q -
      iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (d.projection.lift q.1 q.2))
        (univ ×ˢ J) q‖ ≤
    ‖iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e c q.1 q.2)
        (univ ×ˢ J) q -
      iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e d q.1 q.2)
        (univ ×ˢ J) q‖ := by
  let π := ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin N)) ℂ
  have heq (u : ProductCurve M) (hu : u.SmoothOn (I := I) J) :
      iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (u.projection.lift q.1 q.2))
        (univ ×ˢ J) q =
      π.compContinuousMultilinearMap
        (iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => productEmbeddedCoordinates e u q.1 q.2)
          (univ ×ˢ J) q) :=
    π.iteratedFDerivWithin_comp_left (contDiffOn_productEmbeddedCoordinates e hu q hq)
      (uniqueDiffOn_univ.prod hJ) hq (by exact_mod_cast le_top)
  rw [heq c hc, heq d hd]
  have hsub (L₁ L₂ : (ℝ × ℝ) [×m]→L[ℝ] (EuclideanSpace ℝ (Fin N) × ℂ)) :
      π.compContinuousMultilinearMap L₁ - π.compContinuousMultilinearMap L₂ =
        π.compContinuousMultilinearMap (L₁ - L₂) := by
    ext v
    simp
  rw [hsub]
  exact (π.norm_compContinuousMultilinearMap_le _).trans
    ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_fst_le ..) (norm_nonneg _)).trans_eq
      (one_mul _))

theorem continuous_projection_of_smoothProductCylinder
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) {P : Type*} [TopologicalSpace P]
    {c : P → ProductCurve M}
    (hc : @Continuous P (ProductCurve M) inferInstance (smoothProductCylinderTopology e J) c)
    (hs : ∀ p, (c p).SmoothOn (I := I) J) :
    @Continuous P (CurveMap M) inferInstance (smoothCylinderTopology e J)
      (fun p => (c p).projection) := by
  let : TopologicalSpace (ProductCurve M) := smoothProductCylinderTopology e J
  let : TopologicalSpace (CurveMap M) := smoothCylinderTopology e J
  apply continuous_iff_continuousAt.mpr
  intro p
  have hcat := hc.continuousAt (x := p)
  simp only [ContinuousAt,
    TopologicalSpace.tendsto_nhds_generateFrom_iff] at hcat
  simp only [ContinuousAt,
    TopologicalSpace.tendsto_nhds_generateFrom_iff]
  rintro s ⟨d, m, ε, hε, rfl⟩ ⟨ρ₀, hρ₀, hb₀⟩
  have hgap : 0 < ε - ρ₀ := sub_pos.mpr hρ₀
  have hW := hcat _ ⟨c p, m, ε - ρ₀, hgap, rfl⟩
    ⟨0, hgap, fun q _ => by simp⟩
  filter_upwards [hW] with p' hp'
  obtain ⟨ρ, hρ, hb⟩ := hp'
  refine ⟨ρ + ρ₀, by linarith, fun q hq => ?_⟩
  have hproj := projection_jet_norm_sub_le e hJ (hs p') (hs p) m q
    ⟨mem_univ _, hq.2⟩
  have htriangle := norm_add_le
    (iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map ((c p').projection.lift q.1 q.2))
        (univ ×ˢ J) q -
      iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map ((c p).projection.lift q.1 q.2))
        (univ ×ˢ J) q)
    (iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map ((c p).projection.lift q.1 q.2))
        (univ ×ˢ J) q -
      iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (d.lift q.1 q.2))
        (univ ×ˢ J) q)
  rw [sub_add_sub_cancel] at htriangle
  exact htriangle.trans (add_le_add (hproj.trans (hb q hq)) (hb₀ q hq))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

section

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [Nonempty M]

theorem exists_projected_regular_family
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {a b : ℝ} (hab : a < b) {P : Type*} [TopologicalSpace P]
    (c : P → ProductCurve M)
    (hc : @Continuous P (ProductCurve M) inferInstance
      (smoothProductCylinderTopology e (Icc a b)) c)
    (hs : ∀ p, (c p).SmoothOn (I := I) (Icc a b))
    (initial : Width.RegularFamily (I := I) (Q := M) P)
    (hinit : ∀ p z, (c p).projection z a = (initial p).1 z) :
    ∃ projected : C(Icc a b, Width.RegularFamily (I := I) (Q := M) P),
      (∀ t p z, (projected t p).1 z = (c p).projection z t) ∧
      projected ⟨a, le_rfl, hab.le⟩ = initial ∧
      (∀ t, Width.HasContinuousSmoothLoopJets e (projected t)) ∧
      ∀ t, FreeHomotopyClass.mk (Width.contractibleRegularLoopInclusion.comp (projected t)) =
        FreeHomotopyClass.mk (Width.contractibleRegularLoopInclusion.comp initial) := by
  have hproj := continuous_projection_of_smoothProductCylinder e (uniqueDiffOn_Icc hab) hc hs
  obtain ⟨F, hF, hsF, hjF⟩ := exists_regular_family_of_smoothCylinder e hab
    (fun p => (c p).projection) hproj (fun p => (hs p).1)
  let R : C(Icc a b × P, Width.RegularLoop I M) :=
    ⟨fun q => F (q.2, q.1), F.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
  let _ : PathConnectedSpace (Icc a b) :=
    isPathConnected_iff_pathConnectedSpace.mp ((convex_Icc a b).isPathConnected
      ⟨a, le_rfl, hab.le⟩)
  have hat : ∀ p, R (⟨a, le_rfl, hab.le⟩, p) = (initial p).1 := by
    intro p
    apply Width.RegularLoop.toContinuousLoop_injective
    apply ContinuousMap.ext
    intro z
    exact (hF p ⟨a, le_rfl, hab.le⟩ z).trans (hinit p z)
  obtain ⟨projected, hp, hp₀, hclass⟩ :=
    Width.exists_contractible_regular_family_of_pathConnected R ⟨a, le_rfl, hab.le⟩ initial hat
  refine ⟨projected, ?_, hp₀, ?_, hclass⟩
  · intro t p z
    rw [hp]
    exact hF p t z
  · intro t
    constructor
    · intro p
      rw [hp]
      exact hsF p t
    · intro m
      have h := (hjF m).comp
        ((continuous_fst.prodMk (continuous_const (y := t))).prodMk continuous_snd)
      exact h.congr fun q => by rw [hp]; rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
