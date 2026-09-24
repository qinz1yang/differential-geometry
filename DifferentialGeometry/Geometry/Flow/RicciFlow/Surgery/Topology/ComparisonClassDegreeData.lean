import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildComparisonAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Comparison

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

universe u

namespace DifferentialGeometry.Topology

theorem eq_of_pos_zsmul_and_linearMap_eq_one {A : Type*} [AddCommGroup A] [Module ℤ A]
    {x y : A}
    (h : ∃ (k : ℤ) (φ : A →ₗ[ℤ] ℤ), x = k • y ∧ 0 < k ∧ φ x = 1) :
    x = y ∧ ∃ φ : A →ₗ[ℤ] ℤ, φ y = 1 := by
  obtain ⟨k, φ, hxy, hk, hφ⟩ := h
  have hmul : k * φ y = 1 := by
    have h2 : φ x = k * φ y := by
      rw [hxy, map_zsmul]
      rw [zsmul_eq_mul (φ y) k]
      simp only [Int.cast_id]
    rw [h2] at hφ
    exact hφ
  have hm : 1 ≤ φ y := by
    by_contra hcon
    have hle : φ y ≤ 0 := by omega
    nlinarith [hmul, hk]
  have hk1 : k = 1 := by nlinarith [hmul, hk, hm]
  have hxy' : x = y := by rw [hxy, hk1, one_zsmul]
  exact ⟨hxy', φ, by rw [← hxy']; exact hφ⟩

theorem exists_pos_zsmul_and_linearMap_eq_one_of_eq {A : Type*} [AddCommGroup A] [Module ℤ A]
    {x y : A} (hxy : x = y) (h : ∃ φ : A →ₗ[ℤ] ℤ, φ y = 1) :
    ∃ (k : ℤ) (φ : A →ₗ[ℤ] ℤ), x = k • y ∧ 0 < k ∧ φ x = 1 := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨1, φ, by rw [hxy, one_zsmul], one_pos, by rw [hxy, hφ]⟩

theorem exists_pos_zsmul_and_linearMap_eq_one_iff {A : Type*} [AddCommGroup A] [Module ℤ A]
    (x y : A) :
    (∃ (k : ℤ) (φ : A →ₗ[ℤ] ℤ), x = k • y ∧ 0 < k ∧ φ x = 1) ↔
      x = y ∧ ∃ φ : A →ₗ[ℤ] ℤ, φ y = 1 :=
  ⟨eq_of_pos_zsmul_and_linearMap_eq_one,
    fun h => exists_pos_zsmul_and_linearMap_eq_one_of_eq h.1 h.2⟩

theorem exists_not_exists_linearMap_eq_one :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (y : A),
      ¬ ∃ φ : A →ₗ[ℤ] ℤ, φ y = 1 :=
  ⟨ℤ, inferInstance, inferInstance, 0, by
    rintro ⟨φ, hφ⟩
    exact absurd ((map_zero φ).symm.trans hφ) zero_ne_one⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  {G : GeometricCutoffRecord H i parameters}

namespace GeometricCutoffRecord.ComparisonSupport

def CollapseDegreeLipschitzInput {c : ConnectedComponents (H.stage i.succ).Carrier}
    (K : G.ComparisonSupport c) : Prop :=
  ∀ (y z : (G.Parent c).Carrier),
    ∀ hy : y.1 ∈ (H.event i).incoming.terminalRegularRegion,
    ∀ hz : z.1 ∈ (H.event i).incoming.terminalRegularRegion,
    riemannianEDistOf (H.event i).outputMetric (K.rfs_whole_parent_map y).1
      (K.rfs_whole_parent_map z).1 ≤
    riemannianEDistOf (H.event i).terminal.metric ⟨y.1, hy⟩ ⟨z.1, hz⟩

def CollapseDegreeClassInput {c : ConnectedComponents (H.stage i.succ).Carrier}
    (K : G.ComparisonSupport c) : Prop :=
  integralHomologyMap 3 K.rfs_whole_parent_map (fundamentalClass (G.Parent c).orientation) =
    fundamentalClass (G.Child c).orientation

def ClassDegreeData {c : ConnectedComponents (H.stage i.succ).Carrier}
    (K : G.ComparisonSupport c) : Prop :=
  CollapseDegreeClassInput K ∧
    ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (fundamentalClass (G.Child c).orientation) = 1

theorem classDegreeData_iff_multiplierForm {c : ConnectedComponents (H.stage i.succ).Carrier}
    (K : G.ComparisonSupport c) :
    ClassDegreeData K ↔
      ∃ (k : ℤ) (φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ),
        integralHomologyMap 3 K.rfs_whole_parent_map
            (fundamentalClass (G.Parent c).orientation) =
          k • fundamentalClass (G.Child c).orientation ∧
        0 < k ∧
        φ (integralHomologyMap 3 K.rfs_whole_parent_map
          (fundamentalClass (G.Parent c).orientation)) = 1 := by
  constructor
  · rintro ⟨hclass, φ, hφ⟩
    have hc : integralHomologyMap 3 K.rfs_whole_parent_map
        (fundamentalClass (G.Parent c).orientation) =
        fundamentalClass (G.Child c).orientation := hclass
    exact ⟨1, φ, by rw [hc, one_zsmul], one_pos, by rw [hc, hφ]⟩
  · rintro ⟨k, φ, hmul, hk, hφ⟩
    obtain ⟨hxy, φ', hφ'⟩ :=
      DifferentialGeometry.Topology.eq_of_pos_zsmul_and_linearMap_eq_one
        (A := IntegralHomology (G.Child c).Carrier 3) ⟨k, φ, hmul, hk, hφ⟩
    exact ⟨hxy, φ', hφ'⟩

theorem rfs_collapse_degree_of_namedInputs {c : ConnectedComponents (H.stage i.succ).Carrier}
    (K : G.ComparisonSupport c)
    (hlip : CollapseDegreeLipschitzInput K) (hclass : CollapseDegreeClassInput K) :
    K.LocalTerminalLengthControl K.rfs_whole_parent_map ∧
    (∀ x ∉ K.support.region, ∃ U ∈ 𝓝 x, ∀ y ∈ U,
      K.rfs_whole_parent_map y = K.rfs_whole_parent_map x) ∧
    (∀ x : G.transition.ChildCore c,
      K.rfs_whole_parent_map (G.transition.childCoreIntoParent c x) =
        G.transition.childCoreInclusion c x) ∧
    integralHomologyMap 3 K.rfs_whole_parent_map
      (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation ∧
    Function.Surjective K.rfs_whole_parent_map :=
  K.rfs_collapse_degree_of_lipschitz_and_degree hlip hclass

end GeometricCutoffRecord.ComparisonSupport

namespace GeometricCutoffRecord

theorem nonempty_childComparisonInputs_of_classDegreeData
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hcollapse : G.LocalTerminalEDistComparison Kc)
    (t : ℝ) (ht : t ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (scale : ℝ → ℝ) (hscale : ∀ s ∈ Ioo t (H.time i.succ), 1 ≤ scale s)
    (htend : Filter.Tendsto scale (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hconv : G.LocalTerminalParentEDistComparison Kc t scale)
    (hclass : ∀ c, ComparisonSupport.CollapseDegreeClassInput (Kc c))
    (hgen : ∀ c, ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (fundamentalClass (G.Child c).orientation) = 1) :
    Nonempty (G.ChildComparisonInputs
      (fun c => fundamentalClass (G.Parent c).orientation)
      (fun c => fundamentalClass (G.Child c).orientation)) :=
  ⟨{ Kc := Kc
     collapse := hcollapse
     convergenceTime := t
     convergenceTime_mem := ht
     scale := scale
     scale_one := hscale
     scale_tendsto := htend
     convergence := hconv
     multiplier := fun _ => 1
     map_eq := fun c => by
       have hc : integralHomologyMap 3 (Kc c).rfs_whole_parent_map
           (fundamentalClass (G.Parent c).orientation) =
           fundamentalClass (G.Child c).orientation := hclass c
       rw [hc, one_zsmul]
     generator := fun c => by
       refine ⟨(hgen c).choose, ?_⟩
       have hc : integralHomologyMap 3 (Kc c).rfs_whole_parent_map
           (fundamentalClass (G.Parent c).orientation) =
           fundamentalClass (G.Child c).orientation := hclass c
       rw [hc]
       exact (hgen c).choose_spec
     positive := fun _ => one_pos }⟩

theorem rfs_child_comparison_of_classDegreeData
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hcollapse : G.LocalTerminalEDistComparison Kc)
    (t : ℝ) (ht : t ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (scale : ℝ → ℝ) (hscale : ∀ s ∈ Ioo t (H.time i.succ), 1 ≤ scale s)
    (htend : Filter.Tendsto scale (𝓝[<] (H.time i.succ)) (𝓝 1))
    (hconv : G.LocalTerminalParentEDistComparison Kc t scale)
    (hclass : ∀ c, ComparisonSupport.CollapseDegreeClassInput (Kc c))
    (hgen : ∀ c, ∃ φ : IntegralHomology (G.Child c).Carrier 3 →ₗ[ℤ] ℤ,
      φ (fundamentalClass (G.Child c).orientation) = 1) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      C((G.Parent c).Carrier, (G.Child c).Carrier),
    (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
    (∀ c, integralHomologyMap 3 (f c) (fundamentalClass (G.Parent c).orientation) =
      fundamentalClass (G.Child c).orientation) ∧
    ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
      (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
      ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
        riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
          (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y :=
  G.rfs_child_comparison_of_nonempty_data
    (nonempty_childComparisonInputs_of_classDegreeData Kc hcollapse t ht scale hscale htend
      hconv hclass hgen)

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
