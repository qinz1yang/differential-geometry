import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlowReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlowDeformationFrontierAudit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.PreparedFamilyFrontier



universe uK

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
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

include hT2 hCompact hConnected hBoundary

omit [SigmaCompactSpace Q] in
theorem rfs_ramp_uniform_bounds_of_ramp_producers
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (hcurv : curveShorteningTotalCurvatureBound (I := I) (M := Q) B)
    (hslope : curveShorteningLeastAreaSlope (I := I) (M := Q) B) :
    let delta := b - a
    let Lbar := Real.exp (B.B₀ * delta) * L₀
    let Thetabar := (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * delta)
    let Abar := Real.exp (2 * B.B₀ * delta) * (Ainit + delta * Thetabar)
    let Cup := Real.exp (2 * B.B₀ * delta) * (2 * B.B₀ * Abar + Thetabar)
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      ∀ γ : ℝ → ContinuousFreeLoop Q,
        (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
        ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ t ∈ Icc a b,
          c.length B.family.metric lambda t ≤ Lbar ∧
          c.totalCurvature B.family.metric lambda t ≤ Thetabar ∧
          0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
          loopFamilyLeastArea B.family.metric γ t ≤ Abar) ∧
        (∫ t in a..b, c.energy B.family.metric lambda t) ≤ Lbar ∧
        ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
            Cup * (t - s) :=
  rfs_ramp_uniform_bounds_of_input B L₀ Theta₀ Ainit hL₀ hTheta₀ hAinit
    (rampUniformBoundsInput_of_extinction_frontiers B Ainit hAinit hev hcurv hslope)

omit [SigmaCompactSpace Q] in
theorem rfs_uniform_ramp_alternative_of_ramp_producers
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (ell epsilon : ℝ) (hell : 0 < ell) (hepsilon : 0 < epsilon)
    (hev : RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (hcurv : curveShorteningTotalCurvatureBound (I := I) (M := Q) B)
    (hslope : curveShorteningLeastAreaSlope (I := I) (M := Q) B)
    (hwindow : ∀ eta : ℝ, 0 < eta → eta < 1 → ∀ threshold : ℝ, 1 ≤ threshold →
      ∀ epsilon : ℝ, 0 < epsilon → ∃ d : ℝ, 0 < d ∧ d < epsilon ∧
        RampWindowInput (I := I) (Q := Q) (D := D) (a := a) (b := b) B
          L₀ Theta₀ Ainit ell eta threshold d) :
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        ∀ γ : ℝ → ContinuousFreeLoop Q,
          (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
          (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
          c.length B.family.metric lambda a ≤ L₀ →
          c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
          loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
          loopLength (B.family.metric b) (γ b) < ell ∨
            loopFamilyLeastArea B.family.metric γ b ≤
              affineComparison B.family a b (loopFamilyLeastArea B.family.metric γ a) + epsilon :=
  rfs_uniform_ramp_alternative_of_input B hdim L₀ Theta₀ Ainit hL₀ hTheta₀ hAinit
    ell epsilon hell hepsilon
    ⟨rfs_rampProductBounds_of_length_evolution B hev hcurv,
      rampAreaBounds_of_projection_frontiers B hslope hcurv Ainit hAinit, hwindow⟩

omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
structure FlatPolygonRampBoundsInput (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    (N : ℕ) (γ : RegularLoop I Q) where
  segment_short : ∀ i : ℤ, IsShortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
    (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)))
  polygon_contMDiff : ContMDiff 𝓘(ℝ, ℝ) I ∞
    (fun t : ℝ => flatPolygon g P N γ (t : Surgery.Topology.Circle))
  polygon_length_le : loopLength g (flatPolygonLoop g P N γ polygon_contMDiff).toContinuousLoop ≤
    loopLength g γ.toContinuousLoop
  ramp_length : ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
    (initialRamp (flatPolygonLoop g P N γ polygon_contMDiff)).length (fun _ => g) lambda 0 ≤
      loopLength g γ.toContinuousLoop + 1
  ramp_curvature : ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
    (initialRamp (flatPolygonLoop g P N γ polygon_contMDiff)).totalCurvature
      (fun _ => g) lambda 0 ≤ (N : ℝ) * Real.pi

omit [CompleteSpace E] [SigmaCompactSpace Q] hCompact hConnected in
theorem rfs_flat_polygon_bounds_of_frontier (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (radius : ℝ) (hradius : 0 < radius)
    (hchain : ∀ (N : ℕ), 2 ≤ N → ∀ γ : RegularLoop I Q,
      (∀ i : Fin N, riemannianEDistOf g (polygonVertex γ N i.val)
        (polygonVertex γ N (i.val + 1)) < ENNReal.ofReal radius) →
      FlatPolygonRampBoundsInput (I := I) g P N γ)
    (hjets : ∀ (K : Type uK) [TopologicalSpace K] (N : ℕ), 2 ≤ N →
      ∀ v : K → Surgery.Topology.Circle → Q,
        (∀ i : Fin N, Continuous (fun k => polygonVertex (v k) N i.val)) →
        (∀ k (i : Fin N), riemannianEDistOf g (polygonVertex (v k) N i.val)
          (polygonVertex (v k) N (i.val + 1)) < ENNReal.ofReal radius) →
        ∀ m : ℕ, Continuous (fun p : K × ℝ =>
          iteratedDeriv m (fun x : ℝ =>
            e.map (flatPolygon g P N (v p.1) (x : Surgery.Topology.Circle))) p.2)) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ (N : ℕ), 2 ≤ N → ∀ γ : RegularLoop I Q,
        (∀ i : Fin N, riemannianEDistOf g (polygonVertex γ N i.val)
          (polygonVertex γ N (i.val + 1)) < ENNReal.ofReal radius) →
        ∃ c : RegularLoop I Q,
          (∀ z, c z = flatPolygon g P N γ z) ∧
          ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift c.toContinuousLoop) ∧
          (∀ (i : ℤ) (m : ℕ), 0 < m →
            iteratedDeriv m (e.map ∘ loopLift c.toContinuousLoop) ((i : ℝ) / N) = 0) ∧
          loopLength g c.toContinuousLoop =
            ∑ i : Fin N, (riemannianEDistOf g (polygonVertex γ N i.val)
              (polygonVertex γ N (i.val + 1))).toReal ∧
          loopLength g c.toContinuousLoop ≤ loopLength g γ.toContinuousLoop ∧
          ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
            (initialRamp c).SmoothOn (I := I) univ ∧
            (initialRamp c).IsRampOn (fun _ => g) lambda univ ∧
            (initialRamp c).length (fun _ => g) lambda 0 ≤ loopLength g γ.toContinuousLoop + 1 ∧
            (initialRamp c).totalCurvature (fun _ => g) lambda 0 ≤ (N : ℝ) * Real.pi) ∧
      (∀ (K : Type uK) [TopologicalSpace K] (N : ℕ), 2 ≤ N →
        ∀ v : K → Surgery.Topology.Circle → Q,
          (∀ i : Fin N, Continuous (fun k => polygonVertex (v k) N i.val)) →
          (∀ k (i : Fin N), riemannianEDistOf g (polygonVertex (v k) N i.val)
            (polygonVertex (v k) N (i.val + 1)) < ENNReal.ofReal radius) →
          ∀ m : ℕ, Continuous (fun p : K × ℝ =>
            iteratedDeriv m (fun x : ℝ =>
              e.map (flatPolygon g P N (v p.1) (x : Surgery.Topology.Circle))) p.2)) := by
  refine ⟨radius, hradius, ?_, hjets⟩
  intro N hN γ hedges
  obtain ⟨hseg, hcd, hlen_le, hramp_len, hramp_curv⟩ := hchain N hN γ hedges
  refine ⟨flatPolygonLoop g P N γ hcd, ?_, ?_, ?_, ?_, hlen_le, ?_⟩
  · intro z
    rfl
  · exact hcd
  · intro i m hm
    set F : ℝ → EuclideanSpace ℝ (Fin d) :=
      fun x : ℝ => e.map (flatPolygon g P N γ (x : Surgery.Topology.Circle)) with hF
    change iteratedDeriv m F ((i : ℝ) / N) = 0
    have hNpos : 0 < N := by omega
    set q : ℤ := i / N with hq
    set r : ℤ := i % N with hr
    have hdec : i = N * q + r := by
      rw [hq, hr]
      exact (Int.mul_ediv_add_emod i N).symm
    have hiR : (i : ℝ) = (N : ℝ) * (q : ℝ) + (r : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) hdec
      push_cast at h
      linarith
    have hdiv : (i : ℝ) / N = (q : ℝ) + (r : ℝ) / N := by
      rw [hiR]
      field_simp
    have hper : (fun y : ℝ => F (y + (q : ℝ))) = F := by
      funext y
      rw [hF]
      change e.map (flatPolygon g P N γ ((y + (q : ℝ) : ℝ) : Surgery.Topology.Circle)) =
        e.map (flatPolygon g P N γ (y : Surgery.Topology.Circle))
      rw [flatPolygon_add_int g P N γ q y]
    have hshift : iteratedDeriv m F ((r : ℝ) / N) =
        iteratedDeriv m F ((r : ℝ) / N + (q : ℝ)) := by
      have hcomp := congrArg (iteratedDeriv m) hper
      have h := congrArg (fun G : ℝ → EuclideanSpace ℝ (Fin d) => G ((r : ℝ) / N)) hcomp
      rw [iteratedDeriv_comp_add_const] at h
      simpa using h.symm
    have hzero : iteratedDeriv m F ((r : ℝ) / N) = 0 :=
      iteratedDeriv_map_flatPolygon_eq_zero g P e hNpos γ (fun j _ _ => hseg j)
        (Int.emod_nonneg i (by omega)) (Int.emod_lt_of_pos i (by exact_mod_cast hNpos)) hm
    rw [hdiv]
    rw [add_comm ((q : ℝ)) ((r : ℝ) / N)]
    rw [← hshift]
    exact hzero
  · exact flatPolygon_loopLength_eq_sum g P (by omega : 0 < N) γ
      (flatPolygonLoop g P N γ hcd) (fun z => rfl) (fun i _ _ => hseg i)
  · intro lambda hlambda hlambda_one
    refine ⟨?_, ?_, hramp_len lambda hlambda hlambda_one, hramp_curv lambda hlambda hlambda_one⟩
    · exact initialRamp_smoothOn (I := I) hcd
    · exact initialRamp_isRampOn (I := I) g hlambda (flatPolygonLoop g P N γ hcd)
theorem rfs_prepared_family_flow_of_ramp_producers (B : RicciBackground (I := I) (M := Q) D a b)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hsmooth : HasContinuousSmoothLoopJets e prepared)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    (hinit : @Continuous (Sphere 2) (ProductCurve Q) inferInstance
      (smoothProductInitialTopology e a) (fun p => initialRamp ((prepared p).1)))
    (hexists : RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (hfamily : RampFamilyInput (I := I) (M := Q) (D := D) (a := a) (b := b) (N := d) B lambda e)
    (hprojected : RampFamilyProjectedDeformation (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B e prepared lambda) :
    ∃ solutions : Sphere 2 → ProductCurve Q,
      ∃ projected : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
        @Continuous (Sphere 2) (ProductCurve Q) inferInstance
          (smoothProductCylinderTopology e (Icc a b)) solutions ∧
        (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
          (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
          (solutions p).degree = 1 ∧
          ∀ z, (solutions p).map z a = ((prepared p).1 z, z)) ∧
        (∀ t : Icc a b, ∀ p z,
          ((projected t) p).1 z = (solutions p).projection z t) ∧
        projected ⟨a, le_rfl, B.lt.le⟩ = prepared ∧
        (∀ t : Icc a b, HasContinuousSmoothLoopJets e (projected t)) ∧
        ∀ t : Icc a b,
          FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (projected t)) =
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp prepared) :=
  rfs_prepared_family_flow_of_frontier B e prepared hsmooth lambda hlambda hlambda_one
    (rfs_rampFamilyFlowSolutions_of_ramp_frontiers B e prepared hsmooth lambda hlambda hlambda_one
      hinit hexists hfamily)
    hprojected

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
def PreparedFamilyInitialLengthCurvatureFront (B : RicciBackground (I := I) (M := Q) D a b)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (L₀ Theta₀ : ℝ) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
    ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
      HasContinuousSmoothLoopJets e prepared →
      ∀ p, (initialRamp (prepared p).1).length (fun _ => B.family.metric a) lambda 0 ≤ L₀ ∧
        (initialRamp (prepared p).1).totalCurvature (fun _ => B.family.metric a) lambda 0 ≤
          Theta₀

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem preparedFamilyInitialBoundsFront_of_length_curvatureFront
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (L₀ Theta₀ : ℝ)
    (h : PreparedFamilyInitialLengthCurvatureFront (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B e L₀ Theta₀) :
    PreparedFamilyInitialBoundsFront (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B e L₀ Theta₀ := by
  intro lambda hlambda hlambda_one prepared hsmooth p
  obtain ⟨h1, h2⟩ := initialRamp_smoothOn (I := I) (Q := Q)
    (γ := ((prepared p).1).toContinuousLoop) (hsmooth.1 p)
  exact ⟨⟨h1.mono (Set.prod_mono Subset.rfl (Set.subset_univ _)),
      h2.mono (Set.prod_mono Subset.rfl (Set.subset_univ _))⟩,
    (h lambda hlambda hlambda_one prepared hsmooth p).1,
    (h lambda hlambda hlambda_one prepared hsmooth p).2⟩

theorem rfs_family_deformation_of_ramp_producers (B : RicciBackground (I := I) (M := Q) D a b)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (epsilon ell : ℝ) (hepsilon : 0 < epsilon)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (hcontinuous : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        @Continuous (Sphere 2) (ProductCurve Q) inferInstance
          (smoothProductInitialTopology e a) (fun p => initialRamp ((prepared p).1)))
    (hexists : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (hfamily : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      RampFamilyInput (I := I) (M := Q) (D := D) (a := a) (b := b) (N := d) B lambda e)
    (hbounds : PreparedFamilyInitialLengthCurvatureFront (I := I) (Q := Q) (D := D) (a := a)
      (b := b) B e L₀ Theta₀)
    (hprojected : RampFamilyProjectedDeformationFrontier (I := I) (Q := Q) (D := D) (a := a)
      (b := b) B e)
    (hprepared : PreparedFamilyApproximation (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B e Γ L₀ Theta₀ Ainit)
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
              affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon :=
  rfs_family_deformation_of_projected_frontier B e Γ epsilon ell hepsilon L₀ Theta₀ Ainit hL₀
    hTheta₀ hAinit hcontinuous hexists hfamily
    (preparedFamilyInitialBoundsFront_of_length_curvatureFront B e L₀ Theta₀ hbounds)
    hprojected hprepared halt

omit [CompleteSpace E] in
noncomputable def shortSegmentRadius (g : SmoothRiemannianMetric I Q) : ℝ :=
  Classical.choose (shortSegment_neighborhood (I := I) (Q := Q) g)

omit [CompleteSpace E] [SigmaCompactSpace Q] in
theorem isShortSegment_of_lt_shortSegmentRadius (g : SmoothRiemannianMetric I Q) {p q : Q}
    (h : riemannianEDistOf g p q < ENNReal.ofReal (shortSegmentRadius (I := I) (Q := Q) g)) :
    IsShortSegment g p q (shortSegment g p q) :=
  (Classical.choose_spec (shortSegment_neighborhood (I := I) (Q := Q) g)).2.1 p q h |>.1

omit [CompleteSpace E] [SigmaCompactSpace Q] in
theorem isShortSegment_shortSegment_self (g : SmoothRiemannianMetric I Q) (p : Q) :
    IsShortSegment g p p (shortSegment g p p) :=
  (Classical.choose_spec (shortSegment_neighborhood (I := I) (Q := Q) g)).2.1 p p (by
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr
      (Classical.choose_spec (shortSegment_neighborhood (I := I) (Q := Q) g)).1) |>.1

structure PreparedFamilyShortEdgeFrontier (g : SmoothRiemannianMetric I Q) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (eta : ℝ) where
  profile : FlatteningProfile
  bound : ℕ
  bound_two : 2 ≤ bound
  vertex_close : ∀ (p : Sphere 2) (i : ℤ),
    riemannianEDistOf g (polygonVertex (Γ p).1.toContinuousLoop bound i)
      (polygonVertex (Γ p).1.toContinuousLoop bound (i + 1)) <
      ENNReal.ofReal (shortSegmentRadius (I := I) (Q := Q) g)
  polygon_contMDiff : ∀ p : Sphere 2, ContMDiff 𝓘(ℝ, ℝ) I ∞
    (fun t : ℝ => flatPolygon g profile bound ((Γ p).1) (t : Surgery.Topology.Circle))
  polygon_jets_continuous : ∀ m : ℕ, Continuous (fun q : Sphere 2 × ℝ => iteratedDeriv m
    (fun t : ℝ => e.map (flatPolygon g profile bound ((Γ q.1).1)
      (t : Surgery.Topology.Circle))) q.2)
  polygon_homotopic : ∀ p : Sphere 2, ContinuousMap.Homotopic
    (flatPolygonLoop g profile bound ((Γ p).1) (polygon_contMDiff p)).toContinuousLoop
    (Γ p).1.toContinuousLoop
  polygon_area_error : ∀ p : Sphere 2,
    |regularLeastArea g (flatPolygonPreparationFamily g profile bound Γ polygon_contMDiff
        polygon_homotopic p) - regularLeastArea g (Γ p)| < eta
  polygon_ramp_length : ∀ (p : Sphere 2) (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
    (initialRamp (flatPolygon g profile bound ((Γ p).1))).length (fun _ => g) lambda 0 ≤
      loopLength g (Γ p).1.toContinuousLoop + 1
  polygon_ramp_curvature : ∀ (p : Sphere 2) (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
    (initialRamp (flatPolygon g profile bound ((Γ p).1))).totalCurvature (fun _ => g) lambda 0 ≤
      (bound : ℝ) * Real.pi
  family_homotopic : ContinuousMap.Homotopic
    (flatPolygonPreparedFamily g profile bound Γ polygon_contMDiff polygon_homotopic e
      polygon_jets_continuous) Γ

omit [CompleteSpace E] in
def preparedFamilyFrontierOfShortEdgeFrontier (g : SmoothRiemannianMetric I Q) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (eta : ℝ)
    (f : PreparedFamilyShortEdgeFrontier (I := I) (Q := Q) g e Γ eta) :
    PreparedFamilyFrontier (I := I) (Q := Q) g e Γ eta :=
  { profile := f.profile
    bound := f.bound
    bound_two := f.bound_two
    segment_short := fun p i =>
      isShortSegment_of_lt_shortSegmentRadius (I := I) (Q := Q) g (f.vertex_close p i)
    polygon_contMDiff := f.polygon_contMDiff
    polygon_jets_continuous := f.polygon_jets_continuous
    polygon_homotopic := f.polygon_homotopic
    polygon_area_error := f.polygon_area_error
    polygon_ramp_length := f.polygon_ramp_length
    polygon_ramp_curvature := f.polygon_ramp_curvature
    family_homotopic := f.family_homotopic }

omit [CompleteSpace E] [SigmaCompactSpace Q] in
theorem rfs_prepared_family_of_shortEdgeFrontier (g : SmoothRiemannianMetric I Q) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (eta : ℝ) (heta : 0 < eta)
    (f : PreparedFamilyShortEdgeFrontier (I := I) (Q := Q) g e Γ eta) :
    ∃ P : FlatteningProfile, ∃ N : ℕ, 2 ≤ N ∧
      ∃ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        (∀ p z, (prepared p).1 z = flatPolygon g P N (Γ p).1 z) ∧
        HasContinuousSmoothLoopJets e prepared ∧
        ContinuousMap.Homotopic prepared Γ ∧
        (∀ p, |regularLeastArea g (prepared p) - regularLeastArea g (Γ p)| < eta) ∧
        let L₀ := 1 + sSup (Set.range (fun p => loopLength g (Γ p).1.toContinuousLoop))
        let Theta₀ := (N : ℝ) * Real.pi
        let Ainit := familyMaximum g Γ + eta
        0 ≤ L₀ ∧ 0 ≤ Theta₀ ∧ 0 ≤ Ainit ∧
          ∀ p (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
            (initialRamp (prepared p).1).SmoothOn (I := I) univ ∧
            (initialRamp (prepared p).1).IsRampOn (fun _ => g) lambda univ ∧
            (initialRamp (prepared p).1).length (fun _ => g) lambda 0 ≤ L₀ ∧
            (initialRamp (prepared p).1).totalCurvature (fun _ => g) lambda 0 ≤ Theta₀ ∧
            regularLeastArea g (prepared p) ≤ Ainit :=
  rfs_prepared_family_of_preparedFamilyFrontier g e Γ eta heta
    (preparedFamilyFrontierOfShortEdgeFrontier g e Γ eta f)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
