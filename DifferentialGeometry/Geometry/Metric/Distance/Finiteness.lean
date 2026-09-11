import DifferentialGeometry.Geometry.Metric.Distance.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic

open Set Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

theorem Manifold.riemannianEDist_lt_top
    [PreconnectedSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (p q : M) : riemannianEDist I p q < (⊤ : ℝ≥0∞) := by
  set S : Set M := {z : M | riemannianEDist I p z ≠ ⊤} with hS
  have hpS : p ∈ S := by
    simp only [hS, Set.mem_ofPred_eq, riemannianEDist_self]; exact ENNReal.zero_ne_top
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z₀ hz₀
    have hfin : riemannianEDist I p z₀ ≠ ⊤ := hz₀
    have hloc : ∀ᶠ z in nhds z₀, riemannianEDist I z₀ z < (1 : ℝ≥0∞) :=
      eventually_riemannianEDist_lt I z₀ one_pos
    filter_upwards [hloc] with z hz
    simp only [hS, Set.mem_ofPred_eq]
    have htri : riemannianEDist I p z ≤
        riemannianEDist I p z₀ + riemannianEDist I z₀ z := riemannianEDist_triangle
    have hlt : riemannianEDist I p z < ⊤ :=
      lt_of_le_of_lt htri
        (ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hfin,
          lt_of_lt_of_le hz (by norm_num)⟩)
    exact hlt.ne
  have hScompl_open : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro z₀ hz₀
    have hinf : riemannianEDist I p z₀ = ⊤ := by
      simpa only [hS, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using hz₀
    have hloc : ∀ᶠ z in nhds z₀, riemannianEDist I z₀ z < (1 : ℝ≥0∞) :=
      eventually_riemannianEDist_lt I z₀ one_pos
    filter_upwards [hloc] with z hz
    simp only [hS, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
    by_contra hpz
    have hpz' : riemannianEDist I p z ≠ ⊤ := hpz
    have htri : riemannianEDist I p z₀ ≤
        riemannianEDist I p z + riemannianEDist I z z₀ := riemannianEDist_triangle
    have hzz0 : riemannianEDist I z z₀ < ⊤ := by
      rw [riemannianEDist_comm]; exact lt_of_lt_of_le hz (by norm_num)
    have hfin' : riemannianEDist I p z₀ < ⊤ :=
      lt_of_le_of_lt htri
        (ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hpz', hzz0⟩)
    exact hfin'.ne hinf
  have hSclopen : IsClopen S := ⟨⟨hScompl_open⟩, hSopen⟩
  have hSuniv : S = Set.univ := by
    rcases isClopen_iff.mp hSclopen with hempty | huniv
    · exact absurd (hempty ▸ hpS) (by simp)
    · exact huniv
  exact lt_top_iff_ne_top.mpr (hSuniv ▸ Set.mem_univ q : q ∈ S)

end

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianEDistOf_ne_top [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (x y : M) :
    riemannianEDistOf (I := I) g x y ≠ (⊤ : ℝ≥0∞) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  exact (Manifold.riemannianEDist_lt_top (I := I) x y).ne

end DifferentialGeometry
