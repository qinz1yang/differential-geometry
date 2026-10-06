/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ProfileConfinement
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction
import DifferentialGeometry.Geometry.Metric.Conformal.PositiveDomain
import DifferentialGeometry.Geometry.Operator.Restriction
import DifferentialGeometry.Geometry.HarmonicMap.CompactTargetCriticalValues
import Mathlib.Topology.Order.Compact

noncomputable section

open Bundle Filter Manifold Set Metric TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Metric.BarrierProfile
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

/-- An alternate Morrey disk spanning the literal inner trace has a uniform negative
profile margin below the original outer level. The full inverse image of its
range under the original disk is compact and interior. Both disks and the metric
are unchanged; no boundary phase inverse or rank hypothesis is used. -/
theorem profile_alternate_negative_margin_and_compact_original_preimage
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hbase : ∀ x : M, 0 < ρ x → ρ x < a →
      ∀ v : TangentSpace 𝓘(ℝ, E) x, 0 ≤ hessFun g ρ x v v)
    (hcontact : ∀ x : M, ρ x = 0 → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      v ≠ 0 → 0 < hessFun g ρ x v v) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : M → ℝ := fun x => cutoff a (ρ x)
    let hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth a).contMDiff.comp hρ
    let hU : ∀ x : M, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric g hδ U hU
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := E) γU → IsMorreyDisk G γU q →
      (∀ θ : loopCircle, ρ (γU θ : M) = 0) →
      ∀ r : ℝ, 0 < r → r < 1 →
      IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r)) →
      ∀ aOrig : C(closedDisk, U),
      IsMorreyDisk G (diskTrace (affineSubdisk q 0 r)) aOrig →
      ∃ c : ℝ, c < 0 ∧ (∀ z : closedDisk, ρ (aOrig z : M) ≤ c) ∧
        Disjoint (Set.range aOrig) (Set.range γU) ∧
        IsCompact ((Subtype.val : closedDisk → ℂ) '' (q ⁻¹' Set.range aOrig)) ∧
        ((Subtype.val : closedDisk → ℂ) '' (q ⁻¹' Set.range aOrig)) ⊆
          ball (0 : ℂ) 1 := by
  intro U δ hδ hU G γU q hγ hq hγzero r hr hr1 hloop aOrig haOrig
  let ρU : U → ℝ := fun x => ρ (x : M)
  have hρU : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρU :=
    hρ.comp contMDiff_subtype_val
  have hρUa : ∀ x : U, ρU x < a := fun x => x.property
  have hbaseU (x : U) (hx : 0 < ρU x) (v : TangentSpace 𝓘(ℝ, E) x) :
      0 ≤ hessFun (g.restrictOpen U) ρU x v v := by
    rw [hessFun_restrictOpen_of_contMDiff g U ρ hρ]
    exact hbase (x : M) hx x.property
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x v)
  have hcontactU (x : U) (hx : ρU x = 0) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ≠ 0) : 0 < hessFun (g.restrictOpen U) ρU x v v := by
    rw [hessFun_restrictOpen_of_contMDiff g U ρ hρ]
    simpa only [mfderiv_subtype_val_apply] using hcontact (x : M) hx v hv
  have hqProfile : IsMorreyDisk
      (profileMetric (g.restrictOpen U) a ha ρU hρU hρUa) γU q := hq
  obtain ⟨_, hqStrict, _⟩ :=
    IsMorreyDisk.profile_confinement (g.restrictOpen U) a ha ρU hρU hρUa
      hbaseU hcontactU hqProfile hγ (fun θ => (hγzero θ).le)
  have hΓnegative (θ : loopCircle) :
      ρU (diskTrace (affineSubdisk q 0 r) θ) < 0 := by
    have hθnorm : ‖(diskBoundary θ : ℂ)‖ = 1 := Circle.norm_coe _
    have hnorm : ‖(0 : ℂ) + r • (diskBoundary θ : ℂ)‖ < 1 := by
      simpa only [zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        hθnorm, mul_one] using hr1
    let z : closedDisk := ⟨(0 : ℂ) + r • (diskBoundary θ : ℂ), by
      simpa only [mem_closedBall, dist_zero_right] using hnorm.le⟩
    have hvalue : diskTrace (affineSubdisk q 0 r) θ = q z :=
      diskExtension_coe q z
    rw [hvalue]
    exact hqStrict z hnorm
  have haProfile : IsMorreyDisk
      (profileMetric (g.restrictOpen U) a ha ρU hρU hρUa)
      (diskTrace (affineSubdisk q 0 r)) aOrig := haOrig
  obtain ⟨_, haStrict, _⟩ :=
    IsMorreyDisk.profile_confinement (g.restrictOpen U) a ha ρU hρU hρUa
      hbaseU hcontactU haProfile hloop (fun θ => (hΓnegative θ).le)
  have hnegative (z : closedDisk) : ρ (aOrig z : M) < 0 := by
    by_cases hz : ‖(z : ℂ)‖ < 1
    · exact haStrict z hz
    · have hzle : ‖(z : ℂ)‖ ≤ 1 := by
        simpa only [mem_closedBall, dist_zero_right] using z.property
      have hzeq : ‖(z : ℂ)‖ = 1 := le_antisymm hzle (le_of_not_gt hz)
      obtain ⟨θ, hθ⟩ := exists_diskBoundary_eq_of_norm_eq_one hzeq
      have hzθ : diskBoundary θ = z := Subtype.ext hθ
      obtain ⟨σ, _, htrace⟩ := haOrig.trace
      have hvalue : aOrig (diskBoundary θ) =
          diskTrace (affineSubdisk q 0 r) (σ θ) :=
        congrArg (fun η : freeLoop U => η θ) htrace
      rw [← hzθ, hvalue]
      exact hΓnegative (σ θ)
  have haway : Disjoint (Set.range aOrig) (Set.range γU) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨z, rfl⟩ ⟨θ, hθ⟩
    have hz := hnegative z
    rw [← hθ, hγzero θ] at hz
    exact (lt_irrefl (0 : ℝ)) hz
  have hpre := hq.compact_preimage_and_finite_critical_values_away_trace hγ
    (isCompact_range aOrig.continuous) haway
  have hf : Continuous (fun z : closedDisk => ρ (aOrig z : M)) :=
    hρ.continuous.comp (continuous_subtype_val.comp aOrig.continuous)
  obtain ⟨zmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set closedDisk).Nonempty) hf.continuousOn
  exact ⟨ρ (aOrig zmax : M), hnegative zmax,
    fun z => hmax (Set.mem_univ z), haway, hpre.1, hpre.2.1⟩

end DifferentialGeometry.Geometry
