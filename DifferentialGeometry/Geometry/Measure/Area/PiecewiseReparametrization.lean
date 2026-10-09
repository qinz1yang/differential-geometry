/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Measure.Area.LocalReparametrization
import DifferentialGeometry.Geometry.Measure.Area.Decomposition

set_option autoImplicit false
noncomputable section

open Manifold Set Filter MeasureTheory DifferentialGeometry
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- Finite bi-Lipschitz rearrangements preserve area in the same metric. The
source and image cells cover the same finite-volume region up to null sets.
Integrability of the new density follows from its actual open-cell formulas;
no global regularity of the piecewise map is assumed here. -/
theorem riemannianArea_piecewise_reparametrization
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {ι : Type*} [Finite ι] {P : Set ℂ}
    [IsFiniteMeasure (volume.restrict P)]
    {U V : ℂ → M} {C : ℝ≥0}
    (hU : ∀ x y, riemannianEDistOf g (U x) (U y) ≤
      (C : ℝ≥0∞) * edist x y)
    (s : ι → Set ℂ) (φ : ι → ℂ → ℂ) (K L : ι → ℝ≥0)
    (hs : ∀ i, IsOpen (s i))
    (hsP : ∀ i, s i ⊆ P)
    (hφP : ∀ i, φ i '' s i ⊆ P)
    (hφmeas : ∀ i, MeasurableSet (φ i '' s i))
    (hsdisj : Pairwise (fun i j => AEDisjoint volume (s i) (s j)))
    (hφdisj : Pairwise (fun i j =>
      AEDisjoint volume (φ i '' s i) (φ j '' s j)))
    (hscover : (⋃ i, s i) =ᵐ[volume] P)
    (hφcover : (⋃ i, φ i '' s i) =ᵐ[volume] P)
    (hφLip : ∀ i, LipschitzOnWith (K i) (φ i) (s i))
    (hφlower : ∀ i, ∀ x ∈ s i, ∀ y ∈ s i,
      edist x y ≤ (L i : ℝ≥0∞) * edist (φ i x) (φ i y))
    (hV : ∀ i, EqOn V (U ∘ φ i) (s i)) :
    IntegrableOn (riemannianAreaDensity g V) P ∧
      riemannianArea g V P = riemannianArea g U P := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hiU : IntegrableOn (riemannianAreaDensity g U) P :=
    integrableOn_riemannianAreaDensity_of_lipschitz g hU P
  have hiVcell (i : ι) : IntegrableOn (riemannianAreaDensity g V) (s i) := by
    obtain ⟨Φ, hΦ, heΦ⟩ := (hφLip i).extend_finite_dimension
    obtain ⟨KΦ, hKΦ⟩ : ∃ KΦ : ℝ≥0, LipschitzWith KΦ Φ := ⟨_, hΦ⟩
    have hUΦ : ∀ x y, riemannianEDistOf g ((U ∘ Φ) x) ((U ∘ Φ) y) ≤
        ((C * KΦ : ℝ≥0) : ℝ≥0∞) * edist x y := by
      intro x y
      calc
        _ ≤ (C : ℝ≥0∞) * edist (Φ x) (Φ y) := hU _ _
        _ ≤ (C : ℝ≥0∞) * ((KΦ : ℝ≥0∞) * edist x y) := by
          gcongr
          exact hKΦ x y
        _ = _ := by rw [ENNReal.coe_mul, mul_assoc]
    have hi := (integrableOn_riemannianAreaDensity_of_lipschitz g hUΦ P).mono_set
      (hsP i)
    apply hi.congr
    filter_upwards [ae_restrict_mem (hs i).measurableSet] with z hz
    apply (riemannianAreaDensity_congr g _).symm
    apply EqOn.eventuallyEq_of_mem (s := s i) _ ((hs i).mem_nhds hz)
    intro w hw
    exact (hV i hw).trans (congrArg U (heΦ hw))
  have hiVunion : IntegrableOn (riemannianAreaDensity g V) (⋃ i, s i) := by
    have hfinite (t : Finset ι) :
        IntegrableOn (riemannianAreaDensity g V) (⋃ i ∈ t, s i) := by
      induction t using Finset.induction_on with
      | empty => simp
      | @insert i t hit ht => simpa using (hiVcell i).union ht
    simpa using hfinite Finset.univ
  have hiV : IntegrableOn (riemannianAreaDensity g V) P := by
    change Integrable (riemannianAreaDensity g V) (volume.restrict P)
    rw [← Measure.restrict_congr_set hscover]
    exact hiVunion
  refine ⟨hiV, ?_⟩
  calc
    riemannianArea g V P = riemannianArea g V (⋃ i, s i) :=
      setIntegral_congr_set hscover.symm
    _ = ∑ i, riemannianArea g V (s i) :=
      riemannianArea_finite_decomposition g V s
        (fun i => (hs i).measurableSet) hsdisj hiVunion
    _ = ∑ i, riemannianArea g U (φ i '' s i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (riemannianArea_congr_on_open g (hs i) (hV i)).trans
        (riemannianArea_precomp_on g hU (hs i) (hφLip i) (hφlower i))
    _ = riemannianArea g U (⋃ i, φ i '' s i) := by
      symm
      apply riemannianArea_finite_decomposition g U
        (fun i => φ i '' s i) hφmeas hφdisj
      exact hiU.mono_set (iUnion_subset hφP)
    _ = riemannianArea g U P := setIntegral_congr_set hφcover

end DifferentialGeometry.Geometry
