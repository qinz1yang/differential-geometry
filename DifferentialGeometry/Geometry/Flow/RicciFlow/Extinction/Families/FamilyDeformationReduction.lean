import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlowReduction

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

abbrev RampInitialData (B : RicciBackground (I := I) (M := Q) D a b) (lambda : ℝ) : Type _ :=
  {c : ProductCurve Q // c.SmoothOn (I := I) {a} ∧ c.IsRampOn B.family.metric lambda {a}}

def RampFamilyWindowExtension (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (lambda omega : ℝ) : Prop :=
  letI : TopologicalSpace (ProductCurve Q) := smoothProductInitialTopology e a
  0 < omega ∧
    (∀ x : RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda,
      ∃ U : Set (RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda),
        IsOpen U ∧ x ∈ U ∧
          ∃ sols : U → ProductCurve Q,
            @Continuous U (ProductCurve Q) inferInstance
              (smoothProductCylinderTopology e (Icc a (min b (a + omega)))) sols ∧
            (∀ p : U,
              (sols p).IsSolutionOn B.family.metric lambda (Icc a (min b (a + omega)))) ∧
            (∀ p : U,
              (sols p).IsRampOn B.family.metric lambda (Icc a (min b (a + omega)))) ∧
            ∀ p : U, ∀ z, (sols p).map z a = (p.1.1).map z a) ∧
    (∀ (T : ℝ), a ≤ T → T < b →
      ∀ x : RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda,
      ∀ U : Set (RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda),
        IsOpen U → x ∈ U → ∀ sols : U → ProductCurve Q,
        @Continuous U (ProductCurve Q) inferInstance
          (smoothProductCylinderTopology e (Icc a T)) sols →
        (∀ p : U, (sols p).IsSolutionOn B.family.metric lambda (Icc a T)) →
        (∀ p : U, ∀ z, (sols p).map z a = (p.1.1).map z a) →
        ∃ V : Set (RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda),
          IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
            ∃ sols' : V → ProductCurve Q,
              @Continuous V (ProductCurve Q) inferInstance
                (smoothProductCylinderTopology e (Icc a (min b (T + omega)))) sols' ∧
              (∀ p : V,
                (sols' p).IsSolutionOn B.family.metric lambda (Icc a (min b (T + omega)))) ∧
              (∀ p : V,
                (sols' p).IsRampOn B.family.metric lambda (Icc a (min b (T + omega)))) ∧
              ∀ p : V, ∀ z, (sols' p).map z a = (p.1.1).map z a)

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rampFamilyWindowExtension_of_forall_not_isRampOn
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (lambda omega : ℝ) (homega : 0 < omega)
    (h : ∀ c : ProductCurve Q, ¬ (c.SmoothOn (I := I) {a} ∧
      c.IsRampOn B.family.metric lambda {a})) :
    RampFamilyWindowExtension (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda omega := by
  refine ⟨homega, ?_, ?_⟩
  · rintro ⟨c, hs, hr⟩
    exact absurd ⟨hs, hr⟩ (h c)
  · intro T hTa hTb x U hU hx sols hcont hsol hinit
    exact absurd ⟨x.2.1, x.2.2⟩ (h x.1)

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rampFamilyWindowExtension_zero
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (omega : ℝ) (homega : 0 < omega) :
    RampFamilyWindowExtension (I := I) (Q := Q) (D := D) (a := a) (b := b) B e 0 omega :=
  rampFamilyWindowExtension_of_forall_not_isRampOn (I := I) (Q := Q) (D := D) (a := a) (b := b)
    B e 0 omega homega fun c hc => ProductCurve.not_isRampOn_zero c B.family.metric hc.2

private theorem min_add_window_min {w x d : ℝ} (hw : 0 ≤ w) :
    min d (min d x + w) = min d (x + w) := by
  rcases le_total x d with h | h
  · rw [min_eq_right h]
  · rw [min_eq_left h]
    rcases le_total (x + w) d with h2 | h2
    · rw [min_eq_left (le_add_of_nonneg_right hw), min_eq_right h2]
      linarith
    · rw [min_eq_left (le_add_of_nonneg_right hw), min_eq_left h2]

private theorem continuousAt_of_eq_subtype_val {X α : Type*} [tX : TopologicalSpace X]
    [tα : TopologicalSpace α] {s : Set α} (hs : IsOpen s) (sol : s → X)
    (hcont : Continuous sol)
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

theorem rampFamilyInput_of_windowExtension
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (lambda omega : ℝ)
    (K : RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (H : RampFamilyWindowExtension (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda omega) :
    RampFamilyInput (I := I) (M := Q) (D := D) (a := a) (b := b) (N := d) B lambda e :=
  letI instInit : TopologicalSpace (ProductCurve Q) := smoothProductInitialTopology e a
  ⟨fun c₀ hs₀ hr₀ => by
    classical
    obtain ⟨homega, hseed, hext⟩ := H
    have key : ∀ n : ℕ, ∃ (T : ℝ)
        (U : Set (RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda))
        (sols : U → ProductCurve Q),
        IsOpen U ∧ (⟨c₀, hs₀, hr₀⟩ :
            RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda) ∈ U ∧
        @Continuous U (ProductCurve Q) inferInstance
          (smoothProductCylinderTopology e (Icc a T)) sols ∧
        (∀ p : U, (sols p).IsSolutionOn B.family.metric lambda (Icc a T)) ∧
        (∀ p : U, (sols p).IsRampOn B.family.metric lambda (Icc a T)) ∧
        (∀ p : U, ∀ z, (sols p).map z a = (p.1.1).map z a) ∧
        T = min b (a + (n : ℝ) * omega + omega) := by
      intro n
      induction n with
      | zero =>
        obtain ⟨U, hU, hxU, sols, hcont, hsol, hramp, hinit⟩ := hseed ⟨c₀, hs₀, hr₀⟩
        refine ⟨min b (a + omega), U, sols, hU, hxU, ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [Nat.cast_zero, zero_mul, zero_add] using hcont
        · intro p
          simpa only [Nat.cast_zero, zero_mul, zero_add] using hsol p
        · intro p
          simpa only [Nat.cast_zero, zero_mul, zero_add] using hramp p
        · intro p z
          simpa only [Nat.cast_zero, zero_mul, zero_add] using hinit p z
        · congr 1
          ring
      | succ n ih =>
        obtain ⟨T, U, sols, hU, hxU, hcont, hsol, hramp, hinit, hTeq⟩ := ih
        have hTle : T ≤ b := by rw [hTeq]; exact min_le_left _ _
        have hTa : a ≤ T := by
          rw [hTeq]
          refine le_min B.lt.le ?_
          have hnn : (0 : ℝ) ≤ (n : ℝ) * omega := mul_nonneg (Nat.cast_nonneg n) homega.le
          linarith
        by_cases hTd : T < b
        · obtain ⟨V, hV, hxV, -, sols', hcont', hsol', hramp', hinit'⟩ :=
            hext T hTa hTd ⟨c₀, hs₀, hr₀⟩ U hU hxU sols hcont hsol hinit
          have hstep : min b (T + omega) = min b (a + ((n : ℝ) + 1) * omega + omega) := by
            have hrw : a + ((n : ℝ) + 1) * omega + omega =
                a + (n : ℝ) * omega + omega + omega := by ring
            rw [hrw, hTeq]
            exact min_add_window_min homega.le
          have hgoal : min b (a + ((n : ℝ) + 1) * omega + omega) =
              min b (a + ((n + 1 : ℕ) : ℝ) * omega + omega) := by
            congr 1
            push_cast
            ring
          refine ⟨min b (T + omega), V, sols', hV, hxV, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [hstep] using hcont'
          · intro p
            simpa only [hstep] using hsol' p
          · intro p
            simpa only [hstep] using hramp' p
          · intro p z
            simpa only [hstep] using hinit' p z
          · rw [hstep, hgoal]
        · have hTd' : b ≤ T := not_lt.mp hTd
          have hTeqd : T = b := le_antisymm hTle hTd'
          have hbase : b ≤ a + (n : ℝ) * omega + omega := by
            rw [← hTeqd, hTeq]
            exact min_le_right _ _
          have hge : b ≤ a + ((n + 1 : ℕ) : ℝ) * omega + omega := by
            have hrw : a + ((n + 1 : ℕ) : ℝ) * omega + omega =
                a + (n : ℝ) * omega + omega + omega := by push_cast; ring
            rw [hrw]
            linarith [hbase, homega]
          refine ⟨T, U, sols, hU, hxU, hcont, hsol, hramp, hinit, ?_⟩
          rw [hTeqd, min_eq_left hge]
    obtain ⟨T, U, sols, hU, hxU, hcont, hsol, hramp, hinit, hTeq⟩ :=
      key (Nat.ceil ((b - a) / omega))
    have hceil : (b - a) / omega ≤ ((Nat.ceil ((b - a) / omega) : ℕ) : ℝ) := Nat.le_ceil _
    have hmul : b - a ≤ ((Nat.ceil ((b - a) / omega) : ℕ) : ℝ) * omega :=
      (div_le_iff₀ homega).mp hceil
    have hTb : T = b := by
      rw [hTeq, min_eq_left]
      linarith [hmul, homega]
    rw [hTb] at hcont hsol hramp
    let sol : (c : ProductCurve Q) → c.SmoothOn (I := I) {a} →
        c.IsRampOn B.family.metric lambda {a} → ProductCurve Q := fun c hs hr =>
      if h : (⟨c, hs, hr⟩ :
          RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda) ∈ U
        then sols ⟨_, h⟩ else Classical.choose (K.exists_solution c hs hr)
    refine ⟨sol, ?_, ?_⟩
    · refine continuousAt_of_eq_subtype_val (tX := smoothProductCylinderTopology e (Icc a b))
        hU sols hcont hxU ?_ ?_
      · simp only [sol, dif_pos hxU]
      · intro x hx
        simp only [sol, dif_pos hx]
    · intro c hs hr
      by_cases h : (⟨c, hs, hr⟩ :
          RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda) ∈ U
      · simp only [sol, dif_pos h]
        exact ⟨hsol ⟨_, h⟩, hramp ⟨_, h⟩, hinit ⟨_, h⟩⟩
      · simp only [sol, dif_neg h]
        exact ⟨(K.exists_solution c hs hr).choose_spec.1,
          (K.exists_solution c hs hr).choose_spec.2.1,
          (K.exists_solution c hs hr).choose_spec.2.2.1⟩
    ⟩

theorem rfs_csf_ramp_family_of_windowExtension
    (B : RicciBackground (I := I) (M := Q) D a b) (lambda omega : ℝ)
    (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    {P : Type*} [TopologicalSpace P] [CompactSpace P] (initial : P → ProductCurve Q)
    (hcontinuous : @Continuous P (ProductCurve Q) inferInstance
      (smoothProductInitialTopology e a) initial)
    (hsmooth : ∀ p, (initial p).SmoothOn (I := I) {a})
    (hramp : ∀ p, (initial p).IsRampOn B.family.metric lambda {a})
    (K : RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (H : RampFamilyWindowExtension (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda omega) :
    ∃ solutions : P → ProductCurve Q,
      (@Continuous P (ProductCurve Q) inferInstance
        (smoothProductCylinderTopology e (Icc a b)) solutions) ∧
      ∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
        (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
        ∀ z, (solutions p).map z a = (initial p).map z a :=
  rfs_csf_ramp_family B lambda hlambda hlambda_one e initial hcontinuous hsmooth hramp K
    (rampFamilyInput_of_windowExtension (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B e lambda omega K H)

theorem rfs_rampFamilyFlowSolutions_of_windowExtension
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hsmooth : HasContinuousSmoothLoopJets e prepared)
    (lambda omega : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    (hinit : @Continuous (Sphere 2) (ProductCurve Q) inferInstance
      (smoothProductInitialTopology e a) (fun p => initialRamp ((prepared p).1)))
    (K : RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (H : RampFamilyWindowExtension (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda omega) :
    RampFamilyFlowSolutions (I := I) (Q := Q) (D := D) (a := a) (b := b) B e prepared lambda :=
  rfs_rampFamilyFlowSolutions_of_ramp_frontiers B e prepared hsmooth lambda hlambda hlambda_one
    hinit K (rampFamilyInput_of_windowExtension (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B e lambda omega K H)

theorem rfs_preparedFamilyFlowData_of_windowExtension
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (L₀ Theta₀ omega : ℝ)
    (hinitial : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        ∀ p, (initialRamp (prepared p).1).SmoothOn (I := I) {0} ∧
          (initialRamp (prepared p).1).length (fun _ => B.family.metric a) lambda 0 ≤ L₀ ∧
          (initialRamp (prepared p).1).totalCurvature (fun _ => B.family.metric a) lambda 0 ≤
            Theta₀)
    (hrampcont : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        @Continuous (Sphere 2) (ProductCurve Q) inferInstance
          (smoothProductInitialTopology e a) (fun p => initialRamp ((prepared p).1)))
    (hexists : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (hwindow : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        RampFamilyWindowExtension (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda omega)
    (hprojected : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        RampFamilyProjectedDeformation (I := I) (Q := Q) (D := D) (a := a) (b := b) B e prepared
          lambda) :
    PreparedFamilyFlowData (I := I) (Q := Q) (D := D) (a := a) (b := b) B e L₀ Theta₀ :=
  rfs_preparedFamilyFlowData_of_frontier B e L₀ Theta₀ hinitial
    (fun lambda hlambda hlambda_one prepared hsmooth =>
      rfs_rampFamilyFlowSolutions_of_windowExtension B e prepared hsmooth lambda omega hlambda
        hlambda_one (hrampcont lambda hlambda hlambda_one prepared hsmooth)
        (hexists lambda hlambda hlambda_one prepared hsmooth)
        (hwindow lambda hlambda hlambda_one prepared hsmooth))
    hprojected

theorem rfs_family_deformation_of_windowExtension
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (epsilon ell : ℝ) (hepsilon : 0 < epsilon) (hell : 0 < ell)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀)
    (hAinit : 0 ≤ Ainit)
    (hprepared : PreparedFamilyApproximation B e Γ L₀ Theta₀ Ainit)
    (omega : ℝ)
    (hinitial : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        ∀ p, (initialRamp (prepared p).1).SmoothOn (I := I) {0} ∧
          (initialRamp (prepared p).1).length (fun _ => B.family.metric a) lambda 0 ≤ L₀ ∧
          (initialRamp (prepared p).1).totalCurvature (fun _ => B.family.metric a) lambda 0 ≤
            Theta₀)
    (hrampcont : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        @Continuous (Sphere 2) (ProductCurve Q) inferInstance
          (smoothProductInitialTopology e a) (fun p => initialRamp ((prepared p).1)))
    (hexists : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (hwindow : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        RampFamilyWindowExtension (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda omega)
    (hprojected : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        RampFamilyProjectedDeformation (I := I) (Q := Q) (D := D) (a := a) (b := b) B e prepared
          lambda)
    (halt : RampAlternativeData (I := I) (Q := Q) (D := D) (a := a) (b := b) B ell epsilon) :
    ∃ lambda : ℝ, 0 < lambda ∧ lambda ≤ 1 ∧
      ∃ solutions : Sphere 2 → ProductCurve Q,
        ∃ deformed : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
          @Continuous (Sphere 2) (ProductCurve Q) inferInstance
            (smoothProductCylinderTopology e (Icc a b)) solutions ∧
          (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
            (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧ (solutions p).degree = 1) ∧
          (∀ t : Icc a b, ∀ p z,
            ((deformed t) p).1 z = (solutions p).projection z t) ∧
          (∀ t : Icc a b, HasContinuousSmoothLoopJets e (deformed t) ∧
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (deformed t)) =
              FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp Γ)) ∧
          (∀ p, |regularLeastArea (B.family.metric a) ((deformed ⟨a, le_rfl, B.lt.le⟩) p) -
            regularLeastArea (B.family.metric a) (Γ p)| < epsilon) ∧
          ∀ p,
            loopLength (B.family.metric b)
              (((deformed ⟨b, B.lt.le, le_rfl⟩) p).1.toContinuousLoop) < ell ∨
            regularLeastArea (B.family.metric b) ((deformed ⟨b, B.lt.le, le_rfl⟩) p) ≤
              affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon := by
  let _ := hdim
  let _ := hell
  exact rfs_family_deformation_of_input B e Γ epsilon ell hepsilon
    ⟨L₀, Theta₀, Ainit, hL₀, hTheta₀, hAinit, hprepared,
      rfs_preparedFamilyFlowData_of_windowExtension B e L₀ Theta₀ omega hinitial hrampcont
        hexists hwindow hprojected, halt⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
