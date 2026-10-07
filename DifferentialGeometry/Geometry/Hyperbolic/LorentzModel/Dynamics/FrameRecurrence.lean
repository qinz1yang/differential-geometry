/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Ergodic.HomogeneousSpace
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.HorosphericalGenerators
import Mathlib.Dynamics.Ergodic.Conservative

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.RecurrentFrames

open DifferentialGeometry.HomogeneousSpaceMeasure DifferentialGeometry.HomogeneousSpaceDynamics GeodesicFlow LorentzGenerators

variable {m : ℕ}

theorem iterate_right_diagonal (hm : 1 ≤ m) (Γ : Subgroup (IsometryGroup m))
    (t : ℝ) (k : ℕ) (q : FrameQuotient Γ) :
    (right Γ (GeodesicFlow.diagonal t))^[k] q =
      right Γ (GeodesicFlow.diagonal ((k : ℝ) * t)) q := by
  induction k with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_mul,
      diagonal_zero hm, right_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ← right_mul, ← diagonal_add hm]
    congr 2
    push_cast
    ring

theorem quasiMeasurePreserving_projection (Γ : Subgroup (IsometryGroup m))
    (ν : Measure (FrameQuotient Γ))
    (hn : ∀ U : Set (FrameQuotient Γ), MeasurableSet U →
      (ν U = 0 ↔ volume (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ ⁻¹' U) = 0)) :
    Measure.QuasiMeasurePreserving (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ) volume ν := by
  refine ⟨DifferentialGeometry.HomogeneousSpaceMeasure.measurable_projection Γ,
    Measure.AbsolutelyContinuous.mk fun U hU hzero => ?_⟩
  rw [Measure.map_apply (DifferentialGeometry.HomogeneousSpaceMeasure.measurable_projection Γ) hU]
  exact (hn U hU).mp hzero

theorem exists_compact_return_sequence (hm : 1 ≤ m)
    (Γ : Subgroup (IsometryGroup m)) (disc : IsDiscrete (SetLike.coe Γ))
    (ν : Measure (FrameQuotient Γ)) [IsFiniteMeasure ν]
    (hr : ∀ g : IsometryGroup m, MeasurePreserving (right Γ g) ν ν)
    (hn : ∀ U : Set (FrameQuotient Γ), MeasurableSet U →
      (ν U = 0 ↔ volume (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ ⁻¹' U) = 0))
    (P : IsometryGroup m → Prop)
    (hP : ∀ᵐ g ∂(volume : Measure (IsometryGroup m)), P g) :
    ∃ (g s : IsometryGroup m) (k : ℕ → ℕ) (γ : ℕ → Γ),
      P g ∧ StrictMono k ∧
        Tendsto (fun j => (γ j : IsometryGroup m) * g * GeodesicFlow.diagonal (-(k j : ℝ)))
          atTop (𝓝 s) := by
  let : T3Space (IsometryGroup m) := DifferentialGeometry.ProjectiveOrthogonalGroup.Center.t3Space_PO (by omega)
  let : T2Space (FrameQuotient Γ) := DifferentialGeometry.ProjectiveOrthogonalGroup.Center.t2Space_orbitQuotient (by omega) Γ disc
  let := po_quotient_borel (by omega) Γ disc
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : IsometryGroup m)
  have hKpos : (volume : Measure (IsometryGroup m)) K ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds volume hKn).ne'
  have hQ : MeasurableSet (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ '' K) :=
    (hK.image (continuous_projection Γ)).measurableSet
  have hrec := (hr (GeodesicFlow.diagonal (-1))).conservative.ae_mem_imp_frequently_image_mem
    hQ.nullMeasurableSet
  have hrec' := (quasiMeasurePreserving_projection Γ ν hn).ae hrec
  have hex : ∃ᵐ g ∂(volume : Measure (IsometryGroup m)), g ∈ K ∧ P g ∧
      (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ g ∈ DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ '' K →
        ∃ᶠ k in atTop, (right Γ (GeodesicFlow.diagonal (-1)))^[k]
          (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ g) ∈ DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ '' K) :=
    (frequently_ae_mem_iff.mpr hKpos).and_eventually (hP.and hrec')
  obtain ⟨g, hgK, hgP, hgR⟩ := hex.exists
  have hfreq := hgR (mem_image_of_mem (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ) hgK)
  simp only [iterate_right_diagonal hm, mul_neg_one, right_projection] at hfreq
  obtain ⟨k, hk, hreturns⟩ := extraction_of_frequently_atTop hfreq
  have hreps (j : ℕ) : ∃ γ : Γ,
      (γ : IsometryGroup m) * g * GeodesicFlow.diagonal (-(k j : ℝ)) ∈ K := by
    obtain ⟨z, hz, he⟩ := hreturns j
    obtain ⟨γ, hγ⟩ := Quotient.exact he
    refine ⟨γ, ?_⟩
    change (γ : IsometryGroup m) * (g * GeodesicFlow.diagonal (-(k j : ℝ))) = z at hγ
    rwa [mul_assoc, hγ]
  choose γ hγ using hreps
  obtain ⟨s, _, r, hrmono, hlim⟩ := hK.tendsto_subseq hγ
  exact ⟨g, s, k ∘ r, γ ∘ r, hgP, hk.comp hrmono, hlim⟩

end DifferentialGeometry.RecurrentFrames
