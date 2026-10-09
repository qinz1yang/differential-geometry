import DifferentialGeometry.Topology.Manifold.SubmersionFiber

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Manifold Topology
namespace DifferentialGeometry.Topology.Manifold

section

variable {X A B : Type*} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]

private def subsetSliceChart (s : Set X) (x₀ : s) (e : OpenPartialHomeomorph X (A × B))
    (a : A) (hs : ∀ x ∈ e.source, x ∈ s ↔ (e x).1 = a) :
    OpenPartialHomeomorph s B := by
  classical
  have hinv : ∀ z, (a, z) ∈ e.target → e.symm (a, z) ∈ s := by
    intro z hz
    exact (hs _ (e.map_target hz)).mpr (congrArg Prod.fst (e.right_inv hz))
  let inv : B → s := fun z ↦ if hz : (a, z) ∈ e.target then ⟨e.symm (a, z), hinv z hz⟩ else x₀
  have hp : ∀ x : s, x.1 ∈ e.source → (a, (e x.1).2) = e x.1 := by
    intro x hx
    exact Prod.ext ((hs _ hx).mp x.2).symm rfl
  refine
    { toFun := fun x ↦ (e x.1).2
      invFun := inv
      source := Subtype.val ⁻¹' e.source
      target := (fun z ↦ (a, z)) ⁻¹' e.target
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_ }
  · intro x hx
    change (a, (e x.1).2) ∈ e.target
    rw [hp x hx]
    exact e.map_source hx
  · intro z hz
    change (a, z) ∈ e.target at hz
    change (inv z).1 ∈ e.source
    simpa only [inv, dite_eq_left hz] using e.map_target hz
  · intro x hx
    have hz : (a, (e x.1).2) ∈ e.target := by rw [hp x hx]; exact e.map_source hx
    apply Subtype.ext
    simp only [inv, dite_eq_left hz]
    rw [hp x hx]
    exact e.left_inv hx
  · intro z hz
    change (a, z) ∈ e.target at hz
    simp only [inv, dite_eq_left hz]
    exact congrArg Prod.snd (e.right_inv hz)
  · exact continuous_snd.comp_continuousOn
      (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx ↦ hx))
  · rw [continuousOn_iff_continuous_domRestrict]
    apply Continuous.subtype_mk
    have hc : Continuous (fun z : (fun z ↦ (a, z)) ⁻¹' e.target ↦ e.symm (a, z.1)) := by
      apply continuousOn_univ.mp
      exact e.symm.continuousOn.comp
        (continuous_const.prodMk continuous_subtype_val).continuousOn (fun z _ ↦ z.2)
    apply hc.congr
    intro z
    have hz : (a, z.1) ∈ e.target := z.2
    have hv : inv z.1 = ⟨e.symm (a, z.1), hinv z.1 hz⟩ := dite_eq_left hz
    exact (congrArg Subtype.val hv).symm

end

variable {H A K : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

private def subsetSlice (s : Set H) (e : s → OpenPartialHomeomorph H (A × K))
    (a : s → A) (hs : ∀ x : s, ∀ y ∈ (e x).source, y ∈ s ↔ (e x y).1 = a x)
    (x : s) : OpenPartialHomeomorph s K :=
  subsetSliceChart s x (e x) (a x) (hs x)

omit [NormedSpace ℝ H] [NormedSpace ℝ A] [NormedSpace ℝ K] in
private theorem subsetSlice_symm_apply
    (s : Set H) (e : s → OpenPartialHomeomorph H (A × K))
    (a : s → A) (hs : ∀ x : s, ∀ y ∈ (e x).source, y ∈ s ↔ (e x y).1 = a x)
    (x : s) {z : K} (hz : z ∈ (subsetSlice s e a hs x).target) :
    ((subsetSlice s e a hs x).symm z : H) = (e x).symm (a x,z) := by
  classical
  change ((if hz : (a x,z) ∈ (e x).target then
    ⟨(e x).symm (a x,z), _⟩ else x) : s).1 = _
  have ht : (a x,z) ∈ (e x).target := hz
  rw [dite_eq_left ht]

private theorem subsetSlice_symm_contDiffOn
    (s : Set H) (e : s → OpenPartialHomeomorph H (A × K))
    (a : s → A) (hs : ∀ x : s, ∀ y ∈ (e x).source, y ∈ s ↔ (e x y).1 = a x)
    (hei : ∀ x : s, ContDiffOn ℝ ∞ (e x).symm (e x).target) (x : s) :
    ContDiffOn ℝ ∞ (Subtype.val ∘ (subsetSlice s e a hs x).symm)
      (subsetSlice s e a hs x).target := by
  have hc : ContDiffOn ℝ ∞ (fun z : K => (e x).symm (a x,z))
      (subsetSlice s e a hs x).target :=
    (hei x).comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun z hz => hz)
  exact hc.congr (fun z hz => subsetSlice_symm_apply s e a hs x hz)

@[reducible]
def localSliceChartedSpace
    (s : Set H) (e : s → OpenPartialHomeomorph H (A × K))
    (a : s → A) (hx : ∀ x : s, (x : H) ∈ (e x).source)
    (hs : ∀ x : s, ∀ y ∈ (e x).source, y ∈ s ↔ (e x y).1 = a x) :
    ChartedSpace K s where
  atlas := Set.range (subsetSlice s e a hs)
  chartAt := subsetSlice s e a hs
  mem_chart_source := hx
  chart_mem_atlas := fun x => ⟨x,rfl⟩

theorem localSliceIsManifold
    (s : Set H) (e : s → OpenPartialHomeomorph H (A × K))
    (a : s → A) (hx : ∀ x : s, (x : H) ∈ (e x).source)
    (hs : ∀ x : s, ∀ y ∈ (e x).source, y ∈ s ↔ (e x y).1 = a x)
    (he : ∀ x : s, ContDiffOn ℝ ∞ (e x) (e x).source)
    (hei : ∀ x : s, ContDiffOn ℝ ∞ (e x).symm (e x).target) :
    let _ := localSliceChartedSpace s e a hx hs
    IsManifold 𝓘(ℝ,K) ∞ s := by
  dsimp only
  let _ := localSliceChartedSpace s e a hx hs
  refine { toHasGroupoid := ?_ }
  apply hasGroupoid_of_pregroupoid (contDiffPregroupoid ∞ 𝓘(ℝ,K))
  rintro c c' ⟨x,rfl⟩ ⟨y,rfl⟩
  change ContDiffOn ℝ ∞ (𝓘(ℝ,K) ∘ _ ∘ (𝓘(ℝ,K)).symm) _
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
  exact ((he y).comp
    ((subsetSlice_symm_contDiffOn s e a hs hei x).mono Set.inter_subset_left)
    (fun z hz => hz.2)).snd

theorem contMDiff_localSliceInclusion
    (s : Set H) (e : s → OpenPartialHomeomorph H (A × K))
    (a : s → A) (hx : ∀ x : s, (x : H) ∈ (e x).source)
    (hs : ∀ x : s, ∀ y ∈ (e x).source, y ∈ s ↔ (e x y).1 = a x)
    (hei : ∀ x : s, ContDiffOn ℝ ∞ (e x).symm (e x).target) :
    let _ := localSliceChartedSpace s e a hx hs
    ContMDiff 𝓘(ℝ,K) 𝓘(ℝ,H) ∞ (Subtype.val : s → H) := by
  dsimp only
  let _ := localSliceChartedSpace s e a hx hs
  intro x
  rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ]
  change ContMDiffAt 𝓘(ℝ,K) 𝓘(ℝ,H) ∞
    (Subtype.val ∘ (subsetSlice s e a hs x).symm) ((subsetSlice s e a hs x) x)
  exact (subsetSlice_symm_contDiffOn s e a hs hei x).contMDiffOn.contMDiffAt
    ((subsetSlice s e a hs x).open_target.mem_nhds
      ((subsetSlice s e a hs x).map_source (mem_chart_source K x)))

theorem mfderiv_localSliceInclusion_injective
    (s : Set H) (e : s → OpenPartialHomeomorph H (A × K))
    (a : s → A) (hx : ∀ x : s, (x : H) ∈ (e x).source)
    (hs : ∀ x : s, ∀ y ∈ (e x).source, y ∈ s ↔ (e x y).1 = a x)
    (he : ∀ x : s, ContDiffOn ℝ ∞ (e x) (e x).source)
    (hei : ∀ x : s, ContDiffOn ℝ ∞ (e x).symm (e x).target) (x : s) :
    let _ := localSliceChartedSpace s e a hx hs
    Function.Injective (mfderiv 𝓘(ℝ,K) 𝓘(ℝ,H) (Subtype.val : s → H) x) := by
  dsimp only
  let _ := localSliceChartedSpace s e a hx hs
  let _ : IsManifold 𝓘(ℝ,K) ∞ s := localSliceIsManifold s e a hx hs he hei
  let c := chartAt K x
  have hcd : c.MDifferentiable 𝓘(ℝ,K) 𝓘(ℝ,K) :=
    ⟨(contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp)⟩
  have hci := hcd.mfderiv_injective (mem_chart_source K x)
  let g : H → K := fun y => (e x y).2
  have hgd : MDifferentiableAt 𝓘(ℝ,H) 𝓘(ℝ,K) g (x : H) :=
    ((he x).snd.contMDiffOn.contMDiffAt ((e x).open_source.mem_nhds (hx x))).mdifferentiableAt
      (by simp)
  have hid := ((contMDiff_localSliceInclusion s e a hx hs hei) x).mdifferentiableAt (by simp)
  have hd : mfderiv 𝓘(ℝ,K) 𝓘(ℝ,K) c x =
      (mfderiv 𝓘(ℝ,H) 𝓘(ℝ,K) g (x : H)).comp
        (mfderiv 𝓘(ℝ,K) 𝓘(ℝ,H) (Subtype.val : s → H) x) :=
    mfderiv_comp x hgd hid
  intro u v huv
  apply hci
  rw [hd]
  exact congrArg (mfderiv 𝓘(ℝ,H) 𝓘(ℝ,K) g (x : H)) huv

end DifferentialGeometry.Topology.Manifold
