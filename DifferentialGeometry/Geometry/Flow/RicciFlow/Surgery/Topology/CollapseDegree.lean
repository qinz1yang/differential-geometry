import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Comparison
import DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion
import DifferentialGeometry.Topology.Homology.SquareBoundaryDegree

noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

universe u

namespace DifferentialGeometry.Topology

theorem eq_one_of_exists_linearMap_eq_one_of_eq_zsmul_of_pos
    {M : Type u} [AddCommGroup M] [Module ℤ M] {x y : M} {k : ℤ}
    (h : ∃ φ : M →ₗ[ℤ] ℤ, φ x = 1) (hxy : x = k • y) (hk : 0 < k) : k = 1 := by
  rcases Int.isUnit_iff.mp (isUnit_of_exists_linearMap_eq_one x h hxy) with h1 | h1
  · exact h1
  · omega

theorem not_exists_linearMap_eq_one_zero {M : Type u} [AddCommGroup M] [Module ℤ M] :
    ¬ ∃ φ : M →ₗ[ℤ] ℤ, φ (0 : M) = 1 := by
  rintro ⟨φ, hφ⟩
  rw [map_zero] at hφ
  exact zero_ne_one hφ

theorem exists_eq_zsmul_not_isUnit :
    ∃ (k : ℤ) (x y : ℤ), x = k • y ∧ ¬ IsUnit k :=
  ⟨0, 0, 0, by simp, by rw [Int.isUnit_iff]; norm_num⟩

theorem exists_eq_zsmul_of_exists_linearMap_eq_one_not_eq_one :
    ∃ (k : ℤ) (x y : ℤ), x = k • y ∧ (∃ φ : ℤ →ₗ[ℤ] ℤ, φ x = 1) ∧ k ≠ 1 :=
  ⟨-1, 1, -1, by norm_num, ⟨LinearMap.id, rfl⟩, by norm_num⟩

theorem exists_linearMap_eq_one_integralLiftedSphereGenerator :
    ∃ φ : integralSingularHomology 3 (liftedHomotopySphere.{u} 2) →ₗ[ℤ] ℤ,
      φ (integralLiftedSphereGenerator.{u} 2) = 1 :=
  (isSphereHomologyGenerator_iff_exists_functional 2
    (integralLiftedSphereGenerator.{u} 2)).mp (integralLiftedSphereGenerator_isGenerator 2)

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}
  {c : ConnectedComponents (H.stage i.succ).Carrier}

namespace GeometricCutoffRecord

namespace ComparisonSupport

variable (K : G.ComparisonSupport c)

def LocalTerminalDistanceControl
    (f : C((G.Parent c).Carrier, (G.Child c).Carrier)) : Prop :=
  ∀ x ∈ K.support.region, ∃ U ∈ 𝓝 x,
    (∀ y ∈ U, y.1 ∈ (H.event i).incoming.terminalRegularRegion) ∧
    (∀ y ∈ U, ∀ z ∈ U,
      ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
      ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
        riemannianEDistOf (H.event i).outputMetric (f y).1 (f z).1 ≤
          riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩)

theorem rfs_whole_parent_map_localTerminalLengthControl_of_localTerminalDistanceControl
    (hlip : K.LocalTerminalDistanceControl K.canonicalWholeParentMap) :
    K.LocalTerminalLengthControl K.canonicalWholeParentMap := by
  intro x hx
  obtain ⟨U, hU, hterm, hdist⟩ := hlip x hx
  refine ⟨U, hU, hterm, hdist, ?_⟩
  intro γ hparent a b hab hγ hγU hlen
  unfold riemannianCurveLength
  refine iSup_le fun p => ?_
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (le_iSup (fun q : ℕ ×
    {u : ℕ → ℝ // Monotone u ∧ ∀ j, u j ∈ Icc a b} =>
      ∑ j ∈ Finset.range q.1, riemannianEDistOf (H.event i).terminal.metric
        (γ (q.2.1 (j + 1))) (γ (q.2.1 j))) p)
  exact hdist _ (hγU _ (p.2.2.2 (k + 1))) _ (hγU _ (p.2.2.2 k))
    (γ (p.2.1 (k + 1))).2 (γ (p.2.1 k)).2

theorem rfs_collapse_degree_of_localTerminalDistanceControl_and_class_generator
    (a : IntegralHomology (G.Parent c).Carrier 3) (b : IntegralHomology (G.Child c).Carrier 3)
    {k : ℤ} (hlip : K.LocalTerminalDistanceControl K.canonicalWholeParentMap)
    (hmap : integralHomologyMap 3 K.canonicalWholeParentMap a = k • b)
    (hgen : ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (integralHomologyMap 3 K.canonicalWholeParentMap a) = 1)
    (hk : 0 < k) :
    K.LocalTerminalLengthControl K.canonicalWholeParentMap ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.canonicalWholeParentMap y = K.canonicalWholeParentMap x) ∧
    (∀ x : G.transition.ChildCore c,
      K.canonicalWholeParentMap (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 K.canonicalWholeParentMap a = b ∧
    Function.Surjective K.canonicalWholeParentMap := by
  have hclass : integralHomologyMap 3 K.canonicalWholeParentMap a = b := by
    have hone : k = 1 :=
      DifferentialGeometry.Topology.eq_one_of_exists_linearMap_eq_one_of_eq_zsmul_of_pos
        hgen hmap hk
    rw [hmap, hone, one_smul]
  exact ⟨K.rfs_whole_parent_map_localTerminalLengthControl_of_localTerminalDistanceControl hlip,
    fun _ hx => K.rfs_whole_parent_map_locallyConstant_of_notMem hx,
    fun x => K.rfs_whole_parent_map_childCore x, hclass,
    K.rfs_whole_parent_map_surjective_of_cover K.rfs_collapse_cover⟩

end ComparisonSupport

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
