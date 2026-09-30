import DifferentialGeometry.Topology.Manifold.GeneralPosition.ChartDiskComplement
import DifferentialGeometry.Topology.Morse.RoundedSublevel.RoundedDouble

namespace DifferentialGeometry.Topology

open Set Metric _root_.Topology
open scoped Manifold ContDiff ContinuousMap

universe u

structure SmoothSpherePuncture (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] where
  e : Disk n → M
  g : M → ℝ
  chartDisk : isChartDisk e
  smooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g
  regular_zero : ∀ x, g x = 0 → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 n) g x
  base_eq_compl : RoundedDouble.base g = (e '' diskInterior n)ᶜ
  zero_eq_boundary : g ⁻¹' {0} = e '' diskSphere n
  positive_eq_range : g ⁻¹' Ici 0 = range e
  negative_nonempty : (g ⁻¹' Iio 0).Nonempty
  simplyConnected_base : SimplyConnectedSpace (RoundedDouble.base g)
  acyclic_base : SingularPair.acyclic SingularPair.integerCoefficients.{u} (TopCat.of (RoundedDouble.base g))
  levelHomeomorph : (g ⁻¹' {0}) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n)) 1

theorem exists_smoothSpherePuncture {n : ℕ} (hn : 3 ≤ n) {M : Type u}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hSphere : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty (SmoothSpherePuncture n M) := by
  have : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    simplyConnectedSpace_sphere (by omega)
  have : Nonempty M := nonempty_of_homotopyEquiv hSphere
  obtain ⟨e₀, e, f, he₀, he, -, hf, hf₀, hf₁, -, hfi, -, hfz, hreg⟩ :=
    exists_chartDisks_and_strip (M := M) (by omega : 1 ≤ n)
  let g : M → ℝ := fun x => f x - 1 / 2
  have hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g := hf.sub contMDiff_const
  have hbase : RoundedDouble.base g = (e '' diskInterior n)ᶜ := by
    rw [← hfi]
    ext x
    simp only [RoundedDouble.base, mem_ofPred_eq, mem_compl_iff, mem_preimage, mem_Ioi,
      not_lt, g]
    constructor <;> intro h <;> linarith
  have hzero : g ⁻¹' {0} = e '' diskSphere n := by
    rw [← hfz]
    ext x
    simp only [mem_preimage, mem_singleton_iff, g]
    constructor <;> intro h <;> linarith
  obtain ⟨hsc, hac⟩ := simplyConnected_acyclic_compl_chartDisk_of_homotopy_sphere hn hSphere he
  obtain ⟨φ⟩ := he.nonempty_homeomorph_image_diskSphere
  refine ⟨{
    e := e
    g := g
    chartDisk := he
    smooth := hg
    regular_zero := ?_
    base_eq_compl := hbase
    zero_eq_boundary := hzero
    positive_eq_range := ?_
    negative_nonempty := ?_
    simplyConnected_base := ?_
    acyclic_base := ?_
    levelHomeomorph := (Homeomorph.setCongr hzero).trans φ }⟩
  · intro x hx hcrit
    apply hreg x (Or.inr (by dsimp [g] at hx; linarith))
    rw [RoundedDouble.isCriticalPointAt_iff_mvfderiv_eq_zero] at hcrit ⊢
    dsimp [g] at hcrit
    rw [mvfderiv_fun_sub (hf.mdifferentiable (by simp) x) mdifferentiableAt_const,
      mvfderiv_const, sub_zero] at hcrit
    exact hcrit
  · rw [← hf₁]
    ext x
    simp only [mem_preimage, mem_Ici, g]
    constructor <;> intro h <;> linarith
  · let z : Disk n := ⟨0, by simp⟩
    have hz : f (e₀ z) ≤ -1 / 2 := by
      have hmem : e₀ z ∈ f ⁻¹' Iic (-1 / 2) := hf₀ ▸ mem_range_self z
      exact hmem
    refine ⟨e₀ z, ?_⟩
    change f (e₀ z) - 1 / 2 < 0
    linarith
  · rwa [hbase]
  · rwa [hbase]

end DifferentialGeometry.Topology
