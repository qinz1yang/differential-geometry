import DifferentialGeometry.Topology.Homology.Support
import DifferentialGeometry.Topology.Homology.MayerVietoris.OpenRelative
import DifferentialGeometry.Topology.Homology.Local.ChartTransport
import DifferentialGeometry.Topology.Homology.Local.PointRestriction
import DifferentialGeometry.Topology.Homology.Local.Injectivity
import DifferentialGeometry.Topology.Homology.Spheres.SphereHomology

open CategoryTheory Limits
open scoped ContinuousMap

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

lemma relπ_eq_zero_of_mem_range_inclMap {X : TopCat.{u}} {K B : Set X} (hKB : K ⊆ B) {n : ℕ}
    {c : singularHomology R X n} (hc : c ∈ Set.range (inclMap R X K n)) : relπ R X B n c = 0 := by
  obtain ⟨a, rfl⟩ := hc
  have h0 : inclMap R X B n ≫ relπ R X B n = 0 :=
    (pair X B).homologyMap_hom_homologyπ R n
  change relπ R X B n (inclMap R X K n a) = 0
  rw [inclMap_eq_singularHomologyMap, ← inclOfLE_incl hKB, singularHomologyMap_comp, ModuleCat.comp_apply, ← inclMap_eq_singularHomologyMap,
    ← ModuleCat.comp_apply, h0]
  rfl

lemma relπ_comp_relativeHomologyMap_id {X : TopCat.{u}} {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    relπ R X A n ≫ relativeHomologyMap R (𝟙 X) (id_mapsTo h) n = relπ R X B n := by
  rw [relπ_natural, singularHomologyMap_id, Category.id_comp]

theorem eq_zero_of_relπ_eq_zero_of_isOpen {X : TopCat.{u}} {P Q : Set X} (hP : IsOpen P)
    (hQ : IsOpen Q) (hPQ : P ∩ Q = ∅) {n : ℕ} (h : IsZero (relativeHomology R X (P ∪ Q) (n + 1)))
    (c : singularHomology R X n) (hcP : relπ R X P n c = 0) (hcQ : relπ R X Q n c = 0) : c = 0 := by
  have hmono : Mono (relπ R X (P ∩ Q) n) := by
    rw [hPQ]
    have := isIso_relπ_empty R X n
    infer_instance
  have ha : relπ R X (P ∩ Q) n c = 0 := by
    refine relMV_injective R hP hQ n h _ ?_ ?_
    · rw [← ModuleCat.comp_apply, relπ_comp_relativeHomologyMap_id R Set.inter_subset_left n, hcP]
    · rw [← ModuleCat.comp_apply, relπ_comp_relativeHomologyMap_id R Set.inter_subset_right n, hcQ]
  exact ((ModuleCat.mono_iff_injective (relπ R X (P ∩ Q) n)).1 hmono)
    (ha.trans (map_zero _).symm)

lemma exists_notMem_of_not_compactSpace {M : Type*} [TopologicalSpace M] (hM : ¬ CompactSpace M)
    {K : Set M} (hK : IsCompact K) : ∃ y, y ∉ K := by
  by_contra h
  refine hM (isCompact_univ_iff.1 ?_)
  have hKu : K = Set.univ := Set.eq_univ_of_forall fun y => by_contra fun hy => h ⟨y, hy⟩
  exact hKu ▸ hK

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem isZero_singularHomology_of_not_compactSpace (hn : 1 ≤ n) [ConnectedSpace M] (hM : ¬ CompactSpace M) :
    IsZero (singularHomology R (TopCat.of M) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  suffices h : ∀ c : singularHomology R (TopCat.of M) n, c = 0 from ⟨fun a b => (h a).trans (h b).symm⟩
  intro c
  have := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨K, hK, hc⟩ := exists_isCompact_mem_range_inclMap R (TopCat.of M) n c
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  set U : Set M := interior K' with hUdef
  set V : Set M := (closure U)ᶜ with hVdef
  have hU : IsOpen U := isOpen_interior
  have hV : IsOpen V := isClosed_closure.isOpen_compl
  have hclU : closure U ⊆ K' := closure_minimal interior_subset hK'.isClosed
  have hclU_compact : IsCompact (closure U) := hK'.of_isClosed_subset isClosed_closure hclU
  have hUV : U ∩ V = ∅ :=
    Set.disjoint_iff_inter_eq_empty.1 (disjoint_compl_right.mono_left subset_closure)
  have hA : IsCompact (U ∪ V)ᶜ := by
    refine hK'.of_isClosed_subset (hU.union hV).isClosed_compl fun x hx => ?_
    exact hclU (by_contra fun hx' => hx (Or.inr hx'))
  have hzero : IsZero (relativeHomology R (TopCat.of M) (U ∪ V) (n + 1)) := by
    have := (localGood.of_isCompact R hn hA).1 (n + 1) (by omega)
    rwa [compl_compl] at this
  have hcU : relπ R (TopCat.of M) U n c = 0 := relπ_eq_zero_of_mem_range_inclMap R hKK' hc
  obtain ⟨y, hy⟩ := exists_notMem_of_not_compactSpace hM hK
  have hpt : ∀ x, ptRes R (TopCat.of M) n c x = 0 :=
    ptRes_eq_zero_of_exists R hn c ⟨y, ptRes_eq_zero_of_notMem R hc hy⟩
  have hcV : relπ R (TopCat.of M) V n c = 0 :=
    relπ_compl_eq_zero_of_forall_ptRes R hn hclU_compact c fun x _ => hpt x
  exact eq_zero_of_relπ_eq_zero_of_isOpen R hU hV hUV hzero c hcU hcV

end charted

theorem not_isZero_integerCoefficients : ¬ IsZero (integerCoefficients.{u}) := by
  intro h
  have := h.eq_zero_of_src (𝟙 integerCoefficients)
  have h1 := congrArg (fun f : integerCoefficients ⟶ integerCoefficients => (f : integerCoefficients → integerCoefficients) ⟨1⟩) this
  have h2 := congrArg ULift.down h1
  simp at h2

theorem pathConnectedSpace_of_homotopyEquiv_target {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace Y] (e : X ≃ₕ Y) : PathConnectedSpace X := by
  obtain ⟨H⟩ := e.left_inv
  refine ⟨⟨e.invFun (Classical.arbitrary Y)⟩, fun x y => ?_⟩
  have hx : Joined (e.invFun (e.toFun x)) x := ⟨H.evalAt x⟩
  have hy : Joined (e.invFun (e.toFun y)) y := ⟨H.evalAt y⟩
  have hxy : Joined (e.invFun (e.toFun x)) (e.invFun (e.toFun y)) :=
    (PathConnectedSpace.joined (e.toFun x) (e.toFun y)).map e.invFun.continuous
  exact hx.symm.trans (hxy.trans hy)

theorem compactSpace_of_homotopyEquiv_sphere_of_one_le {n : ℕ} (hn : 1 ≤ n) {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : CompactSpace M := by
  have : PathConnectedSpace (unitSphere n) := Sphere.pathConnectedSpace_of_one_le hn
  have : PathConnectedSpace M := pathConnectedSpace_of_homotopyEquiv_target e
  have : ConnectedSpace M := inferInstance
  by_contra hM
  exact not_isZero_integerCoefficients ((isZero_singularHomology_of_not_compactSpace integerCoefficients hn hM).of_iso
    (Sphere.singularHomologyTopIsoOfHomotopyEquivSphere integerCoefficients e (by omega)).symm)

end DifferentialGeometry.Topology.SingularPair

end
