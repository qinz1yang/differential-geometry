import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.LocalChartDistance
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_mem_riemannianEDistOf_eq_of_ball_diff_subset (g : SmoothRiemannianMetric I M)
    {S V W : Set M} (hV : IsOpen V) (hW : IsOpen W) (hVW : Disjoint V W) {x : M} {a b c : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (hS : ∀ z ∈ S, riemannianEDistOf g x z ≤ ENNReal.ofReal b)
    (hcover : riemannianBallOf g x c \ S ⊆ V ∪ W) {q : M} (hq : q ∈ V)
    (ha : ENNReal.ofReal a ≤ riemannianEDistOf g x q)
    (hc : riemannianEDistOf g x q < ENNReal.ofReal c) :
    ∃ q' ∈ V, riemannianEDistOf g x q' = ENNReal.ofReal a := by
  have ha0 : 0 < a := hb.trans_lt hba
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_edistOf_lt g hc
  have hmaps : MapsTo γ (Icc 0 1) (riemannianBallOf g x c) :=
    mapsTo_of_riemannianEDistOf_add_pathELength_lt g x _ (ENNReal.ofReal c) subset_rfl γ hγ
      (by rw [hγ0, riemannianEDistOf_self, zero_add]; exact hlen)
  let φ : ℝ → ℝ≥0∞ := fun s => riemannianEDistOf g x (γ s)
  have hφ : ContinuousOn φ (Icc 0 1) :=
    (Riemannian.continuous_riemannianEDist g x).comp_continuousOn hγ.continuousOn
  let T : Set ℝ := Icc 0 1 ∩ φ ⁻¹' Iic (ENNReal.ofReal a)
  have hTc : IsClosed T := hφ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hT0 : (0 : ℝ) ∈ T :=
    ⟨⟨le_rfl, zero_le_one⟩, by
      change riemannianEDistOf g x (γ 0) ≤ _
      rw [hγ0, riemannianEDistOf_self]
      exact bot_le⟩
  have hTb : BddAbove T := ⟨1, fun s hs => hs.1.2⟩
  set s₀ := sSup T with hs₀
  have hs₀T : s₀ ∈ T := hTc.csSup_mem ⟨0, hT0⟩ hTb
  have hs₀I : s₀ ∈ Icc (0 : ℝ) 1 := hs₀T.1
  have hgt : ∀ s ∈ Ioc s₀ 1, ENNReal.ofReal a < φ s := by
    intro s hs
    by_contra hle
    exact absurd (le_csSup hTb ⟨⟨hs₀I.1.trans hs.1.le, hs.2⟩, not_lt.mp hle⟩)
      (not_le.mpr hs.1)
  have hφs₀ : φ s₀ = ENNReal.ofReal a := by
    refine le_antisymm hs₀T.2 ?_
    rcases hs₀I.2.eq_or_lt with h1 | h1
    · change ENNReal.ofReal a ≤ riemannianEDistOf g x (γ s₀)
      rw [h1, hγ1]
      exact ha
    · have htend : Tendsto φ (𝓝[>] s₀) (𝓝 (φ s₀)) :=
        ((hφ s₀ hs₀I).mono_of_mem_nhdsWithin
          (mem_nhdsWithin.mpr ⟨Iio 1, isOpen_Iio, h1, fun s hs =>
            ⟨hs₀I.1.trans hs.2.le, hs.1.le⟩⟩)).tendsto
      refine ge_of_tendsto htend ?_
      filter_upwards [Ioo_mem_nhdsGT h1] with s hs
      exact (hgt s ⟨hs.1, hs.2.le⟩).le
  have hge : ∀ s ∈ Icc s₀ 1, ENNReal.ofReal a ≤ φ s := by
    intro s hs
    rcases hs.1.eq_or_lt with h | h
    · rw [← h, hφs₀]
    · exact (hgt s ⟨h, hs.2⟩).le
  have hpre : IsPreconnected (γ '' Icc s₀ 1) :=
    isPreconnected_Icc.image γ (hγ.continuousOn.mono (Icc_subset_Icc hs₀I.1 le_rfl))
  have hZ : γ '' Icc s₀ 1 ⊆ V ∪ W := by
    rintro _ ⟨s, hs, rfl⟩
    refine hcover ⟨hmaps ⟨hs₀I.1.trans hs.1, hs.2⟩, fun hsS => ?_⟩
    have h3 : ENNReal.ofReal b < ENNReal.ofReal a := (ENNReal.ofReal_lt_ofReal_iff ha0).mpr hba
    exact absurd ((hge s hs).trans (hS _ hsS)) (not_le.mpr h3)
  have hqZ : q ∈ γ '' Icc s₀ 1 := ⟨1, ⟨hs₀I.2, le_rfl⟩, hγ1⟩
  rcases hpre.subset_or_subset hV hW hVW hZ with hZV | hZW
  · exact ⟨γ s₀, hZV ⟨s₀, ⟨le_rfl, hs₀I.2⟩, rfl⟩, hφs₀⟩
  · exact absurd (hZW hqZ) (disjoint_left.mp hVW hq)

end DifferentialGeometry.Geometry.Metric

end
