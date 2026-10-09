import DifferentialGeometry.Topology.Manifold.ChartPatch.CoordinateConvergence
import DifferentialGeometry.Topology.UniformConvergence.Chart
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.CheegerGromovCompactness

private theorem exists_open_neighborhoods_of_compact_union
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [RegularSpace X]
    {C D V T₀ : Set X} (hC : IsCompact C) (hD : IsCompact D)
    (hV : IsOpen V) (hT₀ : IsOpen T₀) (hCV : C ⊆ V) (hDT₀ : D ⊆ T₀) :
    ∃ A T W : Set X, IsOpen A ∧ IsOpen T ∧ IsOpen W ∧
      IsCompact (closure A) ∧ IsCompact (closure T) ∧ IsCompact (closure W) ∧
      C ⊆ A ∧ D ⊆ T ∧ C ∪ D ⊆ W ∧
      closure A ⊆ V ∧ closure T ⊆ T₀ ∧ closure W ⊆ A ∪ T := by
  obtain ⟨A, hA, hCA, hAV, hAc⟩ :=
    exists_open_between_and_isCompact_closure hC hV hCV
  obtain ⟨T, hT, hDT, hTT₀, hTc⟩ :=
    exists_open_between_and_isCompact_closure hD hT₀ hDT₀
  obtain ⟨W, hW, hCDW, hWAT, hWc⟩ :=
    exists_open_between_and_isCompact_closure (hC.union hD) (hA.union hT)
      (union_subset_union hCA hDT)
  exact ⟨A, T, W, hA, hT, hW, hAc, hTc, hWc, hCA, hDT, hCDW, hAV, hTT₀, hWAT⟩

private theorem chart_map_coordinate_convergence
    {E X α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [TopologicalSpace X] [ChartedSpace E X]
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    {p : ℕ} {V : Set X} (hV : IsOpen V)
    (σ : α → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E X p)
    (d : α → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) p)
    (a₀ : α) (hVtarget : V ⊆ (σ a₀).target)
    (hsource : ∀ i, (σ a₀).source ⊆ (d a₀ i).source)
    (htrans : ∀ a (L : Set E), IsCompact L →
      L ⊆ ((σ a₀).trans (σ a).symm).source →
      MapCPConvergenceOn L p (fun i x => (d a i).symm (d a₀ i x))
        ((σ a₀).trans (σ a).symm) ∧
      ∀ᶠ i in atTop, L ⊆ ((d a₀ i).trans (d a i).symm).source) :
    (∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) p (d a₀ i ∘ (σ a₀).symm) V) ∧
      ∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source ∩ σ a ⁻¹' V →
        (∀ᶠ i in atTop,
          MapsTo (fun x => d a₀ i ((σ a₀).symm (σ a x))) L (d a i).target) ∧
        MapCPConvergenceOn L p
          (fun i x => (d a i).symm (d a₀ i ((σ a₀).symm (σ a x)))) id := by
  have hFc : ∀ i,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) p (d a₀ i ∘ (σ a₀).symm) V := by
    intro i
    exact (d a₀ i).contMDiffOn_toFun.comp
      ((σ a₀).contMDiffOn_invFun.mono hVtarget)
      (fun _ hx => hsource i ((σ a₀).toPartialEquiv.map_target (hVtarget hx)))
  refine ⟨hFc, ?_⟩
  intro a L hL hLV
  let U : Set E := (σ a).source ∩ σ a ⁻¹' (V ∩ (σ a₀).target)
  have hU : IsOpen U :=
    (σ a).toOpenPartialHomeomorph.isOpen_inter_preimage (hV.inter (σ a₀).open_target)
  have hLU : L ⊆ U := fun _ hx => ⟨(hLV hx).1, (hLV hx).2, hVtarget (hLV hx).2⟩
  have hcoord (i : ℕ) :
      EqOn (fun x => (d a₀ i).symm (d a₀ i ((σ a₀).symm (σ a x))))
        ((σ a).trans (σ a₀).symm) U := by
    intro x hx
    exact (d a₀ i).toPartialEquiv.left_inv
      (hsource i ((σ a₀).toPartialEquiv.map_target hx.2.2))
  apply mapCPConvergenceOn_chart_inverse_comp_of_partialDiffeomorph_transitions
    (E := E) (X := X) (Y := Y) (p := p) (W := V) (K := L)
    hV hL (σ a) (σ a₀) hLU (d a₀) (d a)
    (fun i => d a₀ i ∘ (σ a₀).symm) hFc
  · intro S _ hSU
    apply Eventually.of_forall
    intro i x hx
    exact (d a₀ i).toPartialEquiv.map_source
      (hsource i ((σ a₀).toPartialEquiv.map_target (hSU hx).2.2))
  · intro S hS hSU
    exact (mapCInfConvergence_const ((σ a).trans (σ a₀).symm) S hS hSU p).congr_eventually
      hU hSU (Eventually.of_forall hcoord) (Set.eqOn_refl _ _)
  · intro S hS hSU
    exact (htrans a S hS hSU).1
  · intro S hS hSU
    exact (htrans a S hS hSU).2

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Topology.Manifold

open DifferentialGeometry.CheegerGromovCompactness

private theorem eventually_mapsTo_inverse_coordinates_of_compact_chart_convergence
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)]
    (ψ : OpenPartialHomeomorph E X) (e : ∀ i, OpenPartialHomeomorph E (Y i))
    (f : ∀ i, X → Y i) {V C : Set X} {p : ℕ}
    (hC : IsCompact C) (hCV : C ⊆ V) (hCψ : C ⊆ ψ.target)
    {D : Set E} (hD : IsOpen D) (hψD : ψ.source ⊆ D)
    (hold : ∀ L : Set E, IsCompact L → L ⊆ ψ.source ∩ ψ ⁻¹' V →
      (∀ᶠ i in atTop, MapsTo (f i ∘ ψ) L (e i).target) ∧
      MapCPConvergenceOn L p (fun i x => (e i).symm (f i (ψ x))) id) :
    ∀ᶠ i in atTop, ∀ x ∈ C, f i x ∈ (e i).target ∧ (e i).symm (f i x) ∈ D := by
  have hL : IsCompact (ψ.symm '' C) :=
    hC.image_of_continuousOn (ψ.symm.continuousOn.mono hCψ)
  have hLV : ψ.symm '' C ⊆ ψ.source ∩ ψ ⁻¹' V := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨ψ.map_target (hCψ hx), ?_⟩
    simpa only [mem_preimage, ψ.right_inv (hCψ hx)] using hCV hx
  have hi := hold (ψ.symm '' C) hL hLV
  exact ψ.eventually_mapsTo_inverse_coordinates_of_tendstoUniformlyOn e f hC hCψ
    hD (hLV.trans inter_subset_left |>.trans hψD)
    (tendstoUniformlyOn_of_cPConvergence (hi.2.mono_order (Nat.zero_le p))) hi.1

theorem exists_contMDiffOn_with_chart_convergence_on_finite_union
    {E X α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [ChartedSpace E X] [T2Space X]
    {p : ℕ} [IsManifold 𝓘(ℝ, E) p X]
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    (σ : α → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E X p)
    (d : α → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) p)
    (D : α → Set E) (hDopen : ∀ a, IsOpen (D a))
    (hDconvex : ∀ a, Convex ℝ (D a)) (hσD : ∀ a, (σ a).source ⊆ D a)
    (hDd : ∀ a i, D a ⊆ (d a i).source)
    (htrans : ∀ a b (L : Set E), IsCompact L →
      L ⊆ ((σ a).trans (σ b).symm).source →
      MapCPConvergenceOn L p (fun i x ↦ (d b i).symm (d a i x))
        ((σ a).trans (σ b).symm) ∧
      ∀ᶠ i in atTop, L ⊆ ((d a i).trans (d b i).symm).source)
    (a₀ : α) (x₀ : X) (hx₀ : x₀ ∈ (σ a₀).target)
    (S : Finset α) (C : α → Set X)
    (hC : ∀ a ∈ S, IsCompact (C a)) (hCσ : ∀ a ∈ S, C a ⊆ (σ a).target) :
    ∃ W : Set X, ∃ F : ∀ i, X → Y i,
      IsOpen W ∧ IsCompact (closure W) ∧
      ((⋃ a ∈ S, C a) ∪ {x₀}) ⊆ W ∧
      closure W ⊆ (σ a₀).target ∪ ⋃ a ∈ S, (σ a).target ∧
      (∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) p (F i) W) ∧
      (∀ᶠ i in atTop, F i =ᶠ[𝓝 x₀] d a₀ i ∘ (σ a₀).symm) ∧
      ∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source ∩ σ a ⁻¹' W →
        (∀ᶠ i in atTop, MapsTo (F i ∘ σ a) L (d a i).target) ∧
        MapCPConvergenceOn L p (fun i x ↦ (d a i).symm (F i (σ a x))) id := by
  classical
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
  revert hC hCσ
  induction S using Finset.induction_on with
  | empty =>
      intro _ _
      obtain ⟨W, hW, hxW, hWσ, hWc⟩ :=
        exists_open_between_and_isCompact_closure isCompact_singleton (σ a₀).open_target
          (singleton_subset_iff.mpr hx₀)
      have hinit := chart_map_coordinate_convergence hW σ d a₀
        (subset_closure.trans hWσ) (fun i ↦ (hσD a₀).trans (hDd a₀ i))
        (htrans a₀)
      refine ⟨W, (fun i ↦ d a₀ i ∘ (σ a₀).symm), hW, hWc, ?_, ?_, hinit.1,
        Eventually.of_forall (fun _ ↦ Filter.EventuallyEq.rfl), hinit.2⟩
      · simpa using hxW
      · simpa using hWσ
  | @insert a S _ ih =>
      intro hC hCσ
      obtain ⟨V, f, hV, hVc, hCV, hVσ, hf, hfgerm, hold⟩ :=
        ih (fun b hb ↦ hC b (Finset.mem_insert_of_mem hb))
          (fun b hb ↦ hCσ b (Finset.mem_insert_of_mem hb))
      let K : Set X := (⋃ b ∈ S, C b) ∪ {x₀}
      have hK : IsCompact K :=
        (S.isCompact_biUnion fun b hb ↦ hC b (Finset.mem_insert_of_mem hb)).union
          isCompact_singleton
      obtain ⟨A, T, W, hA, hT, hW, hAc, hTc, hWc, hKA, hCT, hKW, hAV, hTσ, hWAT⟩ :=
        exists_open_neighborhoods_of_compact_union hK (hC a (Finset.mem_insert_self a S))
          hV (σ a).open_target hCV (hCσ a (Finset.mem_insert_self a S))
      have hAV' : A ⊆ V := subset_closure.trans hAV
      have hTσ' : T ⊆ (σ a).target := subset_closure.trans hTσ
      have hpointK : x₀ ∈ K := Or.inr rfl
      have hpointA : ({x₀} : Set X) ⊆ A := singleton_subset_iff.mpr (hKA hpointK)
      have hpointW : ({x₀} : Set X) ⊆ W :=
        singleton_subset_iff.mpr (hKW (Or.inl hpointK))
      have hcoord := eventually_mapsTo_inverse_coordinates_of_compact_chart_convergence
        (σ a).toOpenPartialHomeomorph (fun i ↦ (d a i).toOpenPartialHomeomorph) f
        (hAc.inter_right isClosed_closure) (fun _ hx ↦ hAV hx.1)
        (fun _ hx ↦ hTσ hx.2) (hDopen a) (hσD a) (hold a)
      have hfD : ∀ᶠ i in atTop, ∀ x ∈ W ∩ T ∩ A,
          f i x ∈ (d a i).target ∧ (d a i).symm (f i x) ∈ D a := by
        filter_upwards [hcoord] with i hi x hx
        exact hi x ⟨subset_closure hx.2, subset_closure hx.1.2⟩
      obtain ⟨_, g, _, _, _, _, _, _, hg, hpatch, hall⟩ :=
        exists_fixed_cutoff_chart_patch_preserving_chart_convergence
          hA hW hT hWc hWAT isCompact_singleton hpointA hpointW σ d a hTσ' f
          (Eventually.of_forall fun i ↦ (hf i).mono hAV') (hDconvex a) (hDd a)
          (fun _ hx ↦ hσD a ((σ a).toPartialEquiv.map_target (hTσ' hx.2))) hfD
          (fun b L hL hLA ↦ hold b L hL (fun _ hx ↦ ⟨(hLA hx).1, hAV' (hLA hx).2⟩))
          (fun b L hL hLσ ↦ htrans a b L hL hLσ)
      refine ⟨W, g, hW, hWc, ?_, ?_, hg, ?_, hall⟩
      · intro x hx
        rcases hx with hx | hx
        · rcases mem_iUnion₂.mp hx with ⟨b, hb, hxb⟩
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact hKW (Or.inr hxb)
          · exact hKW (Or.inl (Or.inl (mem_iUnion₂.mpr ⟨b, hb, hxb⟩)))
        · exact hKW (Or.inl (Or.inr hx))
      · intro x hx
        rcases hWAT hx with hxA | hxT
        · rcases hVσ (subset_closure (hAV' hxA)) with hx₀ | hxS
          · exact Or.inl hx₀
          · rcases mem_iUnion₂.mp hxS with ⟨b, hb, hxb⟩
            exact Or.inr (mem_iUnion₂.mpr ⟨b, Finset.mem_insert_of_mem hb, hxb⟩)
        · exact Or.inr (mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a S, hTσ' hxT⟩)
      · filter_upwards [hpatch, hfgerm] with i hi hfi
        exact (hi.2.1 x₀ rfl).trans hfi

end DifferentialGeometry.Topology.Manifold
