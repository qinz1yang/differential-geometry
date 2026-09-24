import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlatPolygonRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlatPolygonRampCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlatPolygonLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.PreparedFamilyFrontier

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [T2Space Q] [CompactSpace Q] [ConnectedSpace Q] [I.Boundaryless]

theorem rfs_flat_polygon_bounds (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d) :
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
      (∀ (K : Type*) [TopologicalSpace K] (N : ℕ), 2 ≤ N →
        ∀ v : K → Surgery.Topology.Circle → Q,
          (∀ i : Fin N, Continuous (fun k => polygonVertex (v k) N i.val)) →
          (∀ k (i : Fin N), riemannianEDistOf g (polygonVertex (v k) N i.val)
            (polygonVertex (v k) N (i.val + 1)) < ENNReal.ofReal radius) →
          ∀ m : ℕ, Continuous (fun p : K × ℝ =>
            iteratedDeriv m (fun x : ℝ =>
              e.map (flatPolygon g P N (v p.1) (x : Surgery.Topology.Circle))) p.2)) := by
  obtain ⟨radius, hradius, hsegment, hsmooth, _hdiag⟩ := shortSegment_neighborhood g
  refine ⟨radius, hradius, ?_, ?_⟩
  · intro N hN γ hedges
    have hNpos : 0 < N := by omega
    have hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
        (polygonVertex γ N (i + 1))
        (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))) := by
      intro i hi hiN
      let ii : Fin N := ⟨i.toNat, by omega⟩
      have hiCast : (ii.val : ℤ) = i := Int.toNat_of_nonneg hi
      exact (hsegment _ _ (by simpa only [hiCast] using hedges ii)).1
    have hcd := contMDiff_flatPolygon g P e hNpos γ hseg
    let c : RegularLoop I Q := flatPolygonLoop g P N γ hcd
    have hc : ∀ z, c z = flatPolygon g P N γ z := fun _ => rfl
    refine ⟨c, hc, hcd, ?_, flatPolygon_loopLength_eq_sum g P hNpos γ c hc hseg,
      flatPolygon_loopLength_le g P hNpos γ c hc hseg, ?_⟩
    · intro i m hm
      set F : ℝ → EuclideanSpace ℝ (Fin d) :=
        fun x : ℝ => e.map (flatPolygon g P N γ (x : Surgery.Topology.Circle)) with hF
      change iteratedDeriv m F ((i : ℝ) / N) = 0
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
        iteratedDeriv_map_flatPolygon_eq_zero g P e hNpos γ hseg
          (Int.emod_nonneg i (by omega)) (Int.emod_lt_of_pos i (by exact_mod_cast hNpos)) hm
      rw [hdiv, add_comm ((q : ℝ)) ((r : ℝ) / N), ← hshift]
      exact hzero
    · intro lambda hlambda hlambda_one
      refine ⟨initialRamp_smoothOn hcd, initialRamp_isRampOn g hlambda c, ?_, ?_⟩
      · have hlen := initialRamp_flatPolygon_length_le g P hNpos γ c hc hseg lambda 0
        rw [abs_of_pos hlambda] at hlen
        exact hlen.trans (add_le_add_right hlambda_one _)
      · change (initialRamp (flatPolygon g P N γ)).totalCurvature (fun _ => g) lambda 0 ≤ _
        exact initialRamp_flatPolygon_totalCurvature_le g P hNpos γ hseg hlambda 0
  · intro K _ N hN v hv hedges m
    exact continuous_flatPolygon_jets_of_radius g P e
      (fun p q h => (hsegment p q h).1) hsmooth (by omega) v hv hedges m

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
