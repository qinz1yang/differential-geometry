import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlatPolygonBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlatPolygonArea
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlatPolygonHomotopy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.PreparedFamilyFrontier

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [T2Space Q] [CompactSpace Q] [ConnectedSpace Q] [I.Boundaryless]

theorem rfs_prepared_family (g : SmoothRiemannianMetric I Q) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (eta : ℝ) (heta : 0 < eta) :
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
  let P : FlatteningProfile := Classical.choice flatteningProfile_exists
  obtain ⟨radius, hradius, hbound, hjets⟩ := rfs_flat_polygon_bounds g P e
  obtain ⟨rho, hrho, hshort, _, _⟩ := shortSegment_neighborhood g
  obtain ⟨N₀, hN₀, hedges⟩ := exists_uniform_short_polygon_edges g Γ
    (lt_min hradius hrho)
  obtain ⟨N₁, _, harea⟩ := exists_uniform_flatPolygon_area_error g P Γ heta
  obtain ⟨N₂, _, hhom⟩ := exists_uniform_flatPolygon_family_homotopy g P e Γ
  obtain ⟨N₃, _, hloop⟩ := exists_uniform_flatPolygon_loop_homotopy g P e Γ
  let N := max N₀ (max N₁ (max N₂ N₃))
  have h0 : N₀ ≤ N := le_max_left _ _
  have h1 : N₁ ≤ N := (le_max_left N₁ _).trans (le_max_right N₀ _)
  have h2 : N₂ ≤ N := (le_max_left N₂ N₃).trans
    ((le_max_right N₁ _).trans (le_max_right N₀ _))
  have h3 : N₃ ≤ N := (le_max_right N₂ N₃).trans
    ((le_max_right N₁ _).trans (le_max_right N₀ _))
  have hN : 2 ≤ N := hN₀.trans h0
  have hedge : ∀ p (i : Fin N), riemannianEDistOf g (polygonVertex (Γ p).1 N i.val)
      (polygonVertex (Γ p).1 N (i.val + 1)) < ENNReal.ofReal radius := by
    intro p i
    exact (hedges N h0 p i.val).trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hseg : ∀ p (i : ℤ), IsShortSegment g (polygonVertex (Γ p).1 N i)
      (polygonVertex (Γ p).1 N (i + 1))
      (shortSegment g (polygonVertex (Γ p).1 N i) (polygonVertex (Γ p).1 N (i + 1))) := by
    intro p i
    exact (hshort _ _ ((hedges N h0 p i).trans_le
      (ENNReal.ofReal_le_ofReal (min_le_right _ _)))).1
  have hcd : ∀ p, ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => flatPolygon g P N (Γ p).1 (t : Surgery.Topology.Circle)) := by
    intro p
    obtain ⟨c, hc, hcs, _⟩ := hbound N hN (Γ p).1 (hedge p)
    have hl : loopLift c.toContinuousLoop =
        fun t : ℝ => flatPolygon g P N (Γ p).1 (t : Surgery.Topology.Circle) :=
      funext fun t => hc _
    rwa [hl] at hcs
  have hvertices : ∀ i : Fin N, Continuous (fun p => polygonVertex (Γ p).1 N i.val) := by
    intro i
    exact (continuous_eval_const _).comp
      (regularLoopInclusion.continuous.comp (continuous_subtype_val.comp Γ.continuous))
  have hjet := hjets (Sphere 2) N hN (fun p => (Γ p).1) hvertices hedge
  have hloop' : ∀ p, ContinuousMap.Homotopic
      (flatPolygonLoop g P N (Γ p).1 (hcd p)).toContinuousLoop
      (Γ p).1.toContinuousLoop :=
    fun p => hloop N h3 p (flatPolygonLoop g P N (Γ p).1 (hcd p)) (fun _ => rfl)
  apply rfs_prepared_family_of_preparedFamilyFrontier g e Γ eta heta
  refine {
    profile := P
    bound := N
    bound_two := hN
    segment_short := hseg
    polygon_contMDiff := hcd
    polygon_jets_continuous := hjet
    polygon_homotopic := hloop'
    polygon_area_error := fun p => harea N h1 p
      (flatPolygonPreparationFamily g P N Γ hcd hloop' p) (fun _ => rfl)
    polygon_ramp_length := ?_
    polygon_ramp_curvature := ?_
    family_homotopic := hhom N h2 (flatPolygonPreparedFamily g P N Γ hcd hloop' e hjet)
      (fun _ _ => rfl) }
  · intro p lambda hlambda hlambda1
    obtain ⟨c, hc, _, _, _, _, hramps⟩ := hbound N hN (Γ p).1 (hedge p)
    have heq : (c : Surgery.Topology.Circle → Q) = flatPolygon g P N (Γ p).1 := funext hc
    have h := (hramps lambda hlambda hlambda1).2.2.1
    rwa [heq] at h
  · intro p lambda hlambda hlambda1
    obtain ⟨c, hc, _, _, _, _, hramps⟩ := hbound N hN (Γ p).1 (hedge p)
    have heq : (c : Surgery.Topology.Circle → Q) = flatPolygon g P N (Γ p).1 := funext hc
    have h := (hramps lambda hlambda hlambda1).2.2.2
    rwa [heq] at h

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
