import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.HalfSpace

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- A compactly supported stress field need only be continuous at the seam.
Its interior divergence is supplied by an actual continuous extension `D`.
The boundary flux identity is proved by truncating at positive heights and
passing to the seam; no derivative regularity at the seam is assumed. -/
theorem integral_divergence_eq_neg_boundary_of_continuous_extension
    (β : ℝ × ℝ → ℝ × ℝ) (D : ℝ × ℝ → ℝ)
    (hβ : ContinuousOn β (univ ×ˢ Ici 0))
    (hβdiff : ContDiffOn ℝ 1 β (univ ×ˢ Ioi 0))
    (hβcs : HasCompactSupport β)
    (hDcont : ContinuousOn D (univ ×ˢ Ici 0))
    (hD : ∀ p : ℝ × ℝ, 0 < p.2 →
      D p = LinearMap.trace ℝ (ℝ × ℝ) (fderiv ℝ β p).toLinearMap) :
    (∫ p in univ ×ˢ Ioi (0 : ℝ), D p) = -∫ s : ℝ, (β (s, 0)).2 := by
  classical
  let H : Set (ℝ × ℝ) := univ ×ˢ Ioi 0
  let K : Set (ℝ × ℝ) := tsupport β
  have hHm : MeasurableSet H := MeasurableSet.prod (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)) measurableSet_Ioi
  have hKm : MeasurableSet K := (isClosed_tsupport β).measurableSet
  have hzero (p : ℝ × ℝ) (hp : p ∈ H) (hpK : p ∉ K) : D p = 0 := by
    rw [hD p hp.2, fderiv_of_notMem_tsupport ℝ hpK]
    simp
  have hIK : IntegrableOn D (K ∩ (univ ×ˢ Ici (0 : ℝ))) :=
    (hDcont.mono inter_subset_right).integrableOn_compact
      (hβcs.inter_right (isClosed_univ.prod isClosed_Ici))
  have hIKind : IntegrableOn (K.indicator D) H := by
    apply (integrableOn_indicator_iff hKm).mpr
    apply hIK.mono_set
    intro p hp
    refine ⟨hp.1, hp.2.1, ?_⟩
    change 0 ≤ p.2
    exact (show 0 < p.2 from hp.2.2).le
  have hI : IntegrableOn D H := hIKind.congr_fun (by
    intro p hp
    by_cases hpK : p ∈ K
    · exact indicator_of_mem hpK D
    · rw [indicator_of_notMem hpK, hzero p hp hpK]) hHm
  have hshift (a : ℝ) (ha : 0 < a) :
      (∫ p in univ ×ˢ Ioi a, D p) = -∫ s : ℝ, (β (s, a)).2 := by
    have hdiffa : ContDiffOn ℝ 1 β (univ ×ˢ Ici a) :=
      hβdiff.mono (fun p hp => ⟨hp.1, ha.trans_le hp.2⟩)
    have hflux := DifferentialGeometry.Analysis.integral_trace_fderivWithin_half_space_of_hasCompactSupport
      (mu := (volume : Measure ℝ)) hdiffa hβcs
    have hflux' :
        (∫ p in univ ×ˢ Ioi a, LinearMap.trace ℝ (ℝ × ℝ)
          (fderivWithin ℝ β (univ ×ˢ Ici a) p).toLinearMap) =
          -∫ s : ℝ, (β (s, a)).2 := by
      rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict, Measure.restrict_univ]
      exact hflux
    refine (integral_congr_ae ?_).trans hflux'
    filter_upwards [ae_restrict_mem (MeasurableSet.prod (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)) measurableSet_Ioi)] with p hp
    have hnhds : univ ×ˢ Ici a ∈ 𝓝 p :=
      mem_of_superset ((isOpen_univ.prod isOpen_Ioi).mem_nhds hp)
        (prod_mono Subset.rfl Ioi_subset_Ici_self)
    rw [fderivWithin_of_mem_nhds hnhds]
    exact hD p (ha.trans hp.2)
  have hbound : ContinuousOn (fun a : ℝ => ∫ s : ℝ, (β (s, a)).2) (Ici 0) := by
    apply continuousOn_integral_of_compact_support (k := Prod.fst '' K)
      (hβcs.image continuous_fst)
    · exact (hβ.comp (continuous_snd.prodMk continuous_fst).continuousOn
        (fun p hp => ⟨mem_univ _, hp.1⟩)).snd
    · intro a s ha hs
      have hp : (s, a) ∉ tsupport β := fun hp => hs ⟨(s, a), hp, rfl⟩
      rw [image_eq_zero_of_notMem_tsupport hp]
      rfl
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  let S : ℕ → Set (ℝ × ℝ) := fun n => univ ×ˢ Ioi (ε n)
  have hSm (n : ℕ) : MeasurableSet (S n) :=
    MeasurableSet.prod (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)) measurableSet_Ioi
  have hSmono : Monotone S := by
    intro i j hij p hp
    refine ⟨mem_univ _, ?_⟩
    change ε j < p.2
    have hi : ε i < p.2 := hp.2
    apply lt_of_le_of_lt ?_ hi
    apply one_div_le_one_div_of_le (by positivity)
    have hc : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
    linarith
  have hSunion : (⋃ n, S n) = H := by
    ext p
    simp only [mem_iUnion, S, H, mem_prod, mem_univ, true_and, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      exact (hε n).trans hn
    · exact fun hp => exists_nat_one_div_lt hp
  have hleft : Tendsto (fun n => ∫ p in S n, D p) atTop
      (𝓝 (∫ p in H, D p)) := by
    have h := tendsto_setIntegral_of_monotone hSm hSmono
      (show IntegrableOn D (⋃ n, S n) from hSunion.symm ▸ hI)
    simpa only [hSunion] using h
  have hεlim : Tendsto ε atTop (𝓝[Ici (0 : ℝ)] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => (hε n).le)⟩
  have hright : Tendsto (fun n => -∫ s : ℝ, (β (s, ε n)).2) atTop
      (𝓝 (-∫ s : ℝ, (β (s, 0)).2)) :=
    ((hbound 0 self_mem_Ici).tendsto.comp hεlim).neg
  exact tendsto_nhds_unique hleft
    (hright.congr' (Eventually.of_forall (fun n => (hshift (ε n) (hε n)).symm)))

end DifferentialGeometry.Analysis
