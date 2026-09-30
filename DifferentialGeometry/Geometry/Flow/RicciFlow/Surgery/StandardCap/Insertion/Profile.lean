import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {A D ε : ℝ} {hA : 0 < A} {m : ℕ}

theorem CanonicalStaticInsertionWitness.profileTip_neg
    (w : CanonicalStaticInsertionWitness d A hA D m ε) :
    w.data.profileTip < 0 := by
  have htip := w.properties.profileTip_location.2
  linarith [transitionEnd_pos]

theorem CanonicalStaticInsertionWitness.profile_derivWithin_mem_Icc
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    {z : ℝ} (hz : z ∈ Icc w.data.profileTip 0) :
    derivWithin w.data.profile (Icc w.data.profileTip 0) z ∈ Icc (0 : ℝ) 1 := by
  rw [(w.properties.profile_smooth.differentiable (by simp) z).derivWithin
    (uniqueDiffOn_Icc w.profileTip_neg z hz)]
  exact w.properties.profile_speed z

theorem CanonicalStaticInsertionWitness.profile_tip_germ
    (w : CanonicalStaticInsertionWitness d A hA D m ε) :
    ∃ e : ℝ, 0 < e ∧
      ∀ z ∈ Icc w.data.profileTip (min 0 (w.data.profileTip + e)),
        w.data.profile z = z - w.data.profileTip := by
  obtain ⟨e, he, h⟩ := w.properties.profile_linear
  exact ⟨e, he, fun z hz => h z (hz.2.trans (min_le_right _ _))⟩

theorem CanonicalStaticInsertionWitness.profile_collar_eq_standardCapRadiusOfZ
    (w : CanonicalStaticInsertionWitness d A hA D m ε)
    {z : ℝ} (hz : z ∈ Icc (-2 * A) 0) :
    w.data.profile z = standardCapRadiusOfZ z := by
  rw [standardCapRadiusOfZ_eq_conformalRadius]
  exact w.properties.profile_collar z hz

theorem CanonicalStaticInsertionWitness.profile_properties
    (w : CanonicalStaticInsertionWitness d A hA D m ε) :
    ContinuousOn w.data.profile (Icc w.data.profileTip 0) ∧
      MonotoneOn w.data.profile (Icc w.data.profileTip 0) ∧
      MapsTo w.data.profile (Icc w.data.profileTip 0) (Icc 0 standardCapL) ∧
      ContDiffOn ℝ ∞ w.data.profile (Ioc w.data.profileTip 0) ∧
      w.data.profile w.data.profileTip = 0 ∧
      w.data.profile 0 = standardCapL ∧
      (∀ z ∈ Ioc w.data.profileTip 0,
        0 ≤ derivWithin w.data.profile (Icc w.data.profileTip 0) z ∧
          derivWithin w.data.profile (Icc w.data.profileTip 0) z ≤ 1) ∧
      (∃ e : ℝ, 0 < e ∧
        ∀ z ∈ Icc w.data.profileTip (min 0 (w.data.profileTip + e)),
          w.data.profile z = z - w.data.profileTip) ∧
      (∀ z ∈ Icc (-2 * A) 0, w.data.profile z = standardCapRadiusOfZ z) := by
  refine ⟨w.properties.profile_smooth.continuous.continuousOn,
    w.properties.profile_monotone.monotoneOn _, w.properties.profile_mapsTo,
    w.properties.profile_smooth.contDiffOn, w.properties.profile_tip,
    w.properties.profile_zero, ?_, w.profile_tip_germ,
    fun z hz => w.profile_collar_eq_standardCapRadiusOfZ hz⟩
  intro z hz
  exact w.profile_derivWithin_mem_Icc ⟨hz.1.le, hz.2⟩

end DifferentialGeometry.PDE.RicciFlow.StandardCap
