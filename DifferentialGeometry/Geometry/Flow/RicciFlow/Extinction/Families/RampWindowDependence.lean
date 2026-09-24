import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FamilyDeformationReduction

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

def RampWindowLocalDependence (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (lambda : ℝ) : Prop :=
  letI : TopologicalSpace (ProductCurve Q) := smoothProductInitialTopology e a
  ∀ s : ℝ, a < s → s ≤ b →
    ∀ x : RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda,
      ∀ U : Set (RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda),
        IsOpen U → x ∈ U →
          ∀ sols : RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda →
              ProductCurve Q,
            (∀ p, (sols p).IsSolutionOn B.family.metric lambda (Icc a s)) →
            (∀ p, ∀ z, ProductCurve.map (sols p) z a = ProductCurve.map (p.1) z a) →
            ∃ V : Set (RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda),
              IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
                ∃ solsV : V → ProductCurve Q,
                  @Continuous V (ProductCurve Q) inferInstance
                    (smoothProductCylinderTopology e (Icc a s)) solsV ∧
                  ∀ p : V, solsV p = sols p.1

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rampWindowLocalDependence_of_forall_not_isRampOn
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (lambda : ℝ)
    (h : ∀ c : ProductCurve Q, ¬ (c.SmoothOn (I := I) {a} ∧
      c.IsRampOn B.family.metric lambda {a})) :
    RampWindowLocalDependence (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda := by
  intro s hs hsb x U hU hxU
  exact absurd ⟨x.2.1, x.2.2⟩ (h x.1)

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rampWindowLocalDependence_zero
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) :
    RampWindowLocalDependence (I := I) (Q := Q) (D := D) (a := a) (b := b) B e 0 :=
  rampWindowLocalDependence_of_forall_not_isRampOn (I := I) (Q := Q) (D := D) (a := a) (b := b)
    B e 0 fun c hc => ProductCurve.not_isRampOn_zero c B.family.metric hc.2

theorem rampFamilyWindowExtension_of_existence_and_localDependence
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (lambda omega : ℝ)
    (K : RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (Dloc : RampWindowLocalDependence (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda)
    (homega : 0 < omega) :
    RampFamilyWindowExtension (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda omega := by
  let instInit : TopologicalSpace (ProductCurve Q) := smoothProductInitialTopology e a
  let solK : RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda →
      ProductCurve Q := fun p => Classical.choose (K.exists_solution p.1 p.2.1 p.2.2)
  have key : ∀ s : ℝ, a < s → s ≤ b →
      (∀ p, (solK p).IsSolutionOn B.family.metric lambda (Icc a s)) ∧
        (∀ p, (solK p).IsRampOn B.family.metric lambda (Icc a s)) ∧
        (∀ p, ∀ z, ProductCurve.map (solK p) z a = ProductCurve.map (p.1) z a) := by
    intro s has hsb
    refine ⟨fun p => (Classical.choose_spec (K.exists_solution p.1 p.2.1 p.2.2)).1.mono_Icc
        le_rfl hsb has,
      fun p => (Classical.choose_spec (K.exists_solution p.1 p.2.1 p.2.2)).2.1.mono
        (Icc_subset_Icc le_rfl hsb),
      fun p z => (Classical.choose_spec (K.exists_solution p.1 p.2.1 p.2.2)).2.2.1 z⟩
  have hseed : ∀ x : RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda,
      ∃ U : Set (RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda),
        IsOpen U ∧ x ∈ U ∧
          ∃ sols : U → ProductCurve Q,
            @Continuous U (ProductCurve Q) inferInstance
              (smoothProductCylinderTopology e (Icc a (min b (a + omega)))) sols ∧
            (∀ p : U, (sols p).IsSolutionOn B.family.metric lambda
              (Icc a (min b (a + omega)))) ∧
            (∀ p : U, (sols p).IsRampOn B.family.metric lambda
              (Icc a (min b (a + omega)))) ∧
            ∀ p : U, ∀ z, ProductCurve.map (sols p) z a =
              ProductCurve.map (p.1.1) z a := by
    intro x
    have hlt : a < min b (a + omega) := lt_min B.lt (by linarith)
    have hle : min b (a + omega) ≤ b := min_le_left _ _
    obtain ⟨V, hV, hxV, -, solsV, hcontV, heqV⟩ :=
      Dloc (min b (a + omega)) hlt hle x univ isOpen_univ (mem_univ x) solK
        (key _ hlt hle).1 (key _ hlt hle).2.2
    refine ⟨V, hV, hxV, solsV, hcontV, ?_, ?_, ?_⟩
    · intro p
      rw [heqV p]
      exact (key _ hlt hle).1 p.1
    · intro p
      rw [heqV p]
      exact (key _ hlt hle).2.1 p.1
    · intro p z
      rw [heqV p]
      exact (key _ hlt hle).2.2 p.1 z
  have hext : ∀ (T : ℝ), a ≤ T → T < b →
      ∀ x : RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda,
      ∀ U : Set (RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda),
        IsOpen U → x ∈ U → ∀ sols : U → ProductCurve Q,
        @Continuous U (ProductCurve Q) inferInstance
          (smoothProductCylinderTopology e (Icc a T)) sols →
        (∀ p : U, (sols p).IsSolutionOn B.family.metric lambda (Icc a T)) →
        (∀ p : U, ∀ z, ProductCurve.map (sols p) z a = ProductCurve.map (p.1.1) z a) →
        ∃ V : Set (RampInitialData (I := I) (Q := Q) (D := D) (a := a) (b := b) B lambda),
          IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
            ∃ sols' : V → ProductCurve Q,
              @Continuous V (ProductCurve Q) inferInstance
                (smoothProductCylinderTopology e (Icc a (min b (T + omega)))) sols' ∧
              (∀ p : V, (sols' p).IsSolutionOn B.family.metric lambda
                (Icc a (min b (T + omega)))) ∧
              (∀ p : V, (sols' p).IsRampOn B.family.metric lambda
                (Icc a (min b (T + omega)))) ∧
              ∀ p : V, ∀ z, ProductCurve.map (sols' p) z a =
                ProductCurve.map (p.1.1) z a := by
    intro T hTa hTb x U hU hxU sols hcont hsol hinit
    have hlt : a < min b (T + omega) := lt_min B.lt (by linarith)
    have hle : min b (T + omega) ≤ b := min_le_left _ _
    obtain ⟨V, hV, hxV, hVU, solsV, hcontV, heqV⟩ :=
      Dloc (min b (T + omega)) hlt hle x U hU hxU solK
        (key _ hlt hle).1 (key _ hlt hle).2.2
    refine ⟨V, hV, hxV, hVU, solsV, hcontV, ?_, ?_, ?_⟩
    · intro p
      rw [heqV p]
      exact (key _ hlt hle).1 p.1
    · intro p
      rw [heqV p]
      exact (key _ hlt hle).2.1 p.1
    · intro p z
      rw [heqV p]
      exact (key _ hlt hle).2.2 p.1 z
  exact ⟨homega, hseed, hext⟩

theorem rampFamilyWindowExtension_of_uniformExtension_and_localDependence
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (lambda omega : ℝ)
    (H : RampUniformExtension (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (U : RampLocalUniqueness (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (Dloc : RampWindowLocalDependence (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda)
    (homega : 0 < omega) :
    RampFamilyWindowExtension (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda omega :=
  rampFamilyWindowExtension_of_existence_and_localDependence B e lambda omega
    (RampExistenceInput.of_uniformExtension_and_localUniqueness (I := I) (M := Q) (D := D)
      (a := a) (b := b) B lambda H U) Dloc homega

theorem rampFamilyInput_of_uniformExtension_and_localDependence
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (lambda omega : ℝ)
    (H : RampUniformExtension (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (U : RampLocalUniqueness (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (Dloc : RampWindowLocalDependence (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda)
    (homega : 0 < omega) :
    RampFamilyInput (I := I) (M := Q) (D := D) (a := a) (b := b) (N := d) B lambda e :=
  rampFamilyInput_of_windowExtension (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda omega
    (RampExistenceInput.of_uniformExtension_and_localUniqueness (I := I) (M := Q) (D := D)
      (a := a) (b := b) B lambda H U)
    (rampFamilyWindowExtension_of_uniformExtension_and_localDependence B e lambda omega H U Dloc
      homega)

theorem rfs_preparedFamilyFlowData_of_uniformExtension_localUniqueness_localDependence
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (L₀ Theta₀ omega : ℝ)
    (homega : 0 < omega)
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
    (huniform : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      RampUniformExtension (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (hlocalUnique : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      RampLocalUniqueness (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (hdependence : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        RampWindowLocalDependence (I := I) (Q := Q) (D := D) (a := a) (b := b) B e lambda)
    (hprojected : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        RampFamilyProjectedDeformation (I := I) (Q := Q) (D := D) (a := a) (b := b) B e prepared
          lambda) :
    PreparedFamilyFlowData (I := I) (Q := Q) (D := D) (a := a) (b := b) B e L₀ Theta₀ :=
  rfs_preparedFamilyFlowData_of_windowExtension B e L₀ Theta₀ omega hinitial hrampcont
    (fun lambda hlambda hlambda_one _ _ =>
      RampExistenceInput.of_uniformExtension_and_localUniqueness (I := I) (M := Q) (D := D)
        (a := a) (b := b) B lambda (huniform lambda hlambda hlambda_one)
        (hlocalUnique lambda hlambda hlambda_one))
    (fun lambda hlambda hlambda_one prepared hsmooth =>
      rampFamilyWindowExtension_of_uniformExtension_and_localDependence B e lambda omega
        (huniform lambda hlambda hlambda_one) (hlocalUnique lambda hlambda hlambda_one)
        (hdependence lambda hlambda hlambda_one prepared hsmooth) homega)
    hprojected

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
