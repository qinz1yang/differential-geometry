import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlatPolygonRampCurvature

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]

omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
theorem continuous_flatPolygon_of_contMDiff (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) (N : ℕ) (γ : Surgery.Topology.Circle → Q)
    (hcd : ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => flatPolygon g P N γ (t : Surgery.Topology.Circle))) :
    Continuous (flatPolygon g P N γ) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  change Continuous (fun t : ℝ => flatPolygon g P N γ (t : Surgery.Topology.Circle))
  exact hcd.continuous

omit [CompleteSpace E] hT2 in
def flatPolygonLoop (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) (N : ℕ)
    (γ : Surgery.Topology.Circle → Q)
    (hcd : ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => flatPolygon g P N γ (t : Surgery.Topology.Circle))) :
    RegularLoop I Q where
  toContinuousLoop := ⟨flatPolygon g P N γ, continuous_flatPolygon_of_contMDiff g P N γ hcd⟩
  contMDiff_lift := hcd.of_le (by simp)

omit [CompleteSpace E] hT2 in
theorem continuous_flatPolygonLoopFamily (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) (N : ℕ) (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hcd : ∀ p : Sphere 2, ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => flatPolygon g P N ((Γ p).1) (t : Surgery.Topology.Circle)))
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (hjets : ∀ m : ℕ, Continuous (fun q : Sphere 2 × ℝ => iteratedDeriv m
      (fun t : ℝ => e.map (flatPolygon g P N ((Γ q.1).1) (t : Surgery.Topology.Circle))) q.2)) :
    Continuous (fun p : Sphere 2 => flatPolygonLoop g P N ((Γ p).1) (hcd p)) := by
  refine (continuous_regularLoop_iff (I := I) (Q := Q) e
    (fun p : Sphere 2 => flatPolygonLoop g P N ((Γ p).1) (hcd p))).mpr ⟨?_, ?_⟩
  · have hval := hjets 0
    simp only [iteratedDeriv_zero] at hval
    change Continuous (fun q : Sphere 2 × ℝ =>
      e.map (flatPolygon g P N ((Γ q.1).1) (q.2 : Surgery.Topology.Circle))) at hval
    have hq := (_root_.IsOpenQuotientMap.id (X := Sphere 2)).prodMap
      (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ)))
    refine hq.isQuotientMap.continuous_iff.mpr ?_
    exact hval
  · simpa only [flatPolygonLoop, ContinuousMap.coe_mk, iteratedDeriv_one] using hjets 1

omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
theorem flatPolygonContractibleLoop (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    (N : ℕ) (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hcd : ∀ p : Sphere 2, ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => flatPolygon g P N ((Γ p).1) (t : Surgery.Topology.Circle)))
    (hhom : ∀ p : Sphere 2, ContinuousMap.Homotopic
      (flatPolygonLoop g P N ((Γ p).1) (hcd p)).toContinuousLoop
      (Γ p).1.toContinuousLoop) (p : Sphere 2) :
    IsContractibleLoop (flatPolygonLoop g P N ((Γ p).1) (hcd p)).toContinuousLoop := by
  obtain ⟨q, hq⟩ := (Γ p).2
  exact ⟨q, (hhom p).trans hq⟩

def flatPolygonPreparationFamily (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile)
    (N : ℕ) (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hcd : ∀ p : Sphere 2, ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => flatPolygon g P N ((Γ p).1) (t : Surgery.Topology.Circle)))
    (hhom : ∀ p : Sphere 2, ContinuousMap.Homotopic
      (flatPolygonLoop g P N ((Γ p).1) (hcd p)).toContinuousLoop
      (Γ p).1.toContinuousLoop) :
    Sphere 2 → ContractibleRegularLoop (I := I) (Q := Q) :=
  fun p => ⟨flatPolygonLoop g P N ((Γ p).1) (hcd p),
    flatPolygonContractibleLoop g P N Γ hcd hhom p⟩

omit [CompleteSpace E] hT2 in
theorem continuous_flatPolygonPreparationFamily (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) (N : ℕ) (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hcd : ∀ p : Sphere 2, ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => flatPolygon g P N ((Γ p).1) (t : Surgery.Topology.Circle)))
    (hhom : ∀ p : Sphere 2, ContinuousMap.Homotopic
      (flatPolygonLoop g P N ((Γ p).1) (hcd p)).toContinuousLoop
      (Γ p).1.toContinuousLoop)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (hjets : ∀ m : ℕ, Continuous (fun q : Sphere 2 × ℝ => iteratedDeriv m
      (fun t : ℝ => e.map (flatPolygon g P N ((Γ q.1).1) (t : Surgery.Topology.Circle))) q.2)) :
    Continuous (flatPolygonPreparationFamily g P N Γ hcd hhom) :=
  (continuous_flatPolygonLoopFamily g P N Γ hcd e hjets).subtype_mk
    (fun p => flatPolygonContractibleLoop g P N Γ hcd hhom p)

def flatPolygonPreparedFamily (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) (N : ℕ)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hcd : ∀ p : Sphere 2, ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => flatPolygon g P N ((Γ p).1) (t : Surgery.Topology.Circle)))
    (hhom : ∀ p : Sphere 2, ContinuousMap.Homotopic
      (flatPolygonLoop g P N ((Γ p).1) (hcd p)).toContinuousLoop
      (Γ p).1.toContinuousLoop)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (hjets : ∀ m : ℕ, Continuous (fun q : Sphere 2 × ℝ => iteratedDeriv m
      (fun t : ℝ => e.map (flatPolygon g P N ((Γ q.1).1) (t : Surgery.Topology.Circle))) q.2)) :
    RegularFamily (I := I) (Q := Q) (Sphere 2) :=
  ⟨flatPolygonPreparationFamily g P N Γ hcd hhom,
    continuous_flatPolygonPreparationFamily g P N Γ hcd hhom e hjets⟩

structure PreparedFamilyFrontier (g : SmoothRiemannianMetric I Q) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (eta : ℝ) where
  profile : FlatteningProfile
  bound : ℕ
  bound_two : 2 ≤ bound
  segment_short : ∀ (p : Sphere 2) (i : ℤ),
    IsShortSegment g (polygonVertex (Γ p).1.toContinuousLoop bound i)
      (polygonVertex (Γ p).1.toContinuousLoop bound (i + 1))
      (shortSegment g (polygonVertex (Γ p).1.toContinuousLoop bound i)
        (polygonVertex (Γ p).1.toContinuousLoop bound (i + 1)))
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
theorem rfs_prepared_family_of_preparedFamilyFrontier
    (g : SmoothRiemannianMetric I Q) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (eta : ℝ) (heta : 0 < eta)
    (frontier : PreparedFamilyFrontier (I := I) (Q := Q) g e Γ eta) :
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
            regularLeastArea g (prepared p) ≤ Ainit := by
  refine ⟨frontier.profile, frontier.bound, frontier.bound_two, ?_⟩
  refine ⟨flatPolygonPreparedFamily g frontier.profile frontier.bound Γ
    frontier.polygon_contMDiff frontier.polygon_homotopic e frontier.polygon_jets_continuous,
    ?_, ?_, ?_, ?_⟩
  · intro p z
    rfl
  · exact ⟨frontier.polygon_contMDiff, frontier.polygon_jets_continuous⟩
  · exact frontier.family_homotopic
  · refine ⟨frontier.polygon_area_error, ?_, ?_, ?_, ?_⟩
    · obtain ⟨L, _, hL⟩ := regularFamily_uniform_bounds g Γ
      have hbdd : BddAbove (Set.range fun p : Sphere 2 =>
          loopLength g (Γ p).1.toContinuousLoop) :=
        ⟨(L : ℝ), by rintro _ ⟨p, rfl⟩; exact hL p⟩
      obtain ⟨k, _⟩ := familyMaximum_attained g Γ
      have hnonneg : (0 : ℝ) ≤
          sSup (Set.range fun p : Sphere 2 => loopLength g (Γ p).1.toContinuousLoop) :=
        (loopLength_nonneg g (Γ k).1.toContinuousLoop).trans (le_csSup hbdd ⟨k, rfl⟩)
      linarith
    · exact mul_nonneg (Nat.cast_nonneg frontier.bound) Real.pi_pos.le
    · exact add_nonneg (familyMaximum_nonneg g Γ) heta.le
    · intro p lambda hlambda hlambda_one
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact initialRamp_smoothOn (I := I) (Q := Q) (frontier.polygon_contMDiff p)
      · exact initialRamp_isRampOn (I := I) g hlambda
          (flatPolygon g frontier.profile frontier.bound (Γ p).1)
      · obtain ⟨L, _, hL⟩ := regularFamily_uniform_bounds g Γ
        have hbdd : BddAbove (Set.range fun p : Sphere 2 =>
            loopLength g (Γ p).1.toContinuousLoop) :=
          ⟨(L : ℝ), by rintro _ ⟨p, rfl⟩; exact hL p⟩
        change (initialRamp (flatPolygon g frontier.profile frontier.bound
            (Γ p).1)).length (fun _ => g) lambda 0 ≤
          1 + sSup (Set.range fun p : Sphere 2 => loopLength g (Γ p).1.toContinuousLoop)
        have hle := frontier.polygon_ramp_length p lambda hlambda hlambda_one
        have hsup := le_csSup hbdd (Set.mem_range_self p)
        linarith
      · exact frontier.polygon_ramp_curvature p lambda hlambda hlambda_one
      · change regularLeastArea g (flatPolygonPreparationFamily g frontier.profile
          frontier.bound Γ frontier.polygon_contMDiff frontier.polygon_homotopic p) ≤
          familyMaximum g Γ + eta
        have hle := regularLeastArea_le_familyMaximum g Γ p
        have hlt := (abs_lt.mp (frontier.polygon_area_error p)).2
        linarith

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
