import DifferentialGeometry.Topology.Manifold.Submersion

set_option autoImplicit false
noncomputable section
open scoped ContDiff Manifold Topology

namespace Poincare.Topology.Manifold

variable {X A B : Type*} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]

private def sliceChart (s : Set X) (x₀ : s) (e : OpenPartialHomeomorph X (A × B))
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
    simpa only [inv, dif_pos hz] using e.map_target hz
  · intro x hx
    have hz : (a, (e x.1).2) ∈ e.target := by rw [hp x hx]; exact e.map_source hx
    apply Subtype.ext
    simp only [inv, dif_pos hz]
    rw [hp x hx]
    exact e.left_inv hx
  · intro z hz
    change (a, z) ∈ e.target at hz
    simp only [inv, dif_pos hz]
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
    have hv : inv z.1 = ⟨e.symm (a, z.1), hinv z.1 hz⟩ := dif_pos hz
    exact (congrArg Subtype.val hv).symm

variable {E F K H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} [I.Boundaryless]
  {f : M → N} {x : M}

private def projectionChart (h : Manifold.IsSubmersionAtOfComplement K I J ∞ f x) :
    OpenPartialHomeomorph M (F × K) :=
  (h.domChart.trans I.toHomeomorph.toOpenPartialHomeomorph).trans
    h.equiv.toHomeomorph.toOpenPartialHomeomorph

private theorem projectionChart_source (h : Manifold.IsSubmersionAtOfComplement K I J ∞ f x) :
    (projectionChart h).source = h.domChart.source := by
  simp [projectionChart]

private theorem projectionChart_apply_fst
    (h : Manifold.IsSubmersionAtOfComplement K I J ∞ f x)
    {z : M} (hz : z ∈ (projectionChart h).source) :
    (projectionChart h z).1 = (h.codChart.extend J) (f z) := by
  have hzφ : z ∈ (h.domChart.extend I).source := by
    simpa only [OpenPartialHomeomorph.extend_source, projectionChart_source] using hz
  have he := h.writtenInCharts ((h.domChart.extend I).map_source hzφ)
  dsimp only [Function.comp_def] at he
  rw [(h.domChart.extend I).left_inv hzφ] at he
  exact he.symm

private theorem projectionChart_contMDiffOn
    (h : Manifold.IsSubmersionAtOfComplement K I J ∞ f x) :
    ContMDiffOn I 𝓘(ℝ, F × K) ∞ (projectionChart h) (projectionChart h).source := by
  rw [projectionChart_source]
  exact h.equiv.contDiff.contMDiff.comp_contMDiffOn
    (h.domChart.contMDiffOn_extend h.domChart_mem_maximalAtlas)

private theorem projectionChart_symm_contMDiffOn
    (h : Manifold.IsSubmersionAtOfComplement K I J ∞ f x) :
    ContMDiffOn 𝓘(ℝ, F × K) I ∞ (projectionChart h).symm (projectionChart h).target := by
  have hi : ContMDiff 𝓘(ℝ, E) I ∞ I.symm := by
    rw [← contMDiffOn_univ]
    simpa only [I.range_eq_univ] using (I.contMDiffOn_symm (n := ∞))
  exact (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
    (hi.comp h.equiv.symm.contDiff.contMDiff).contMDiffOn (fun z hz ↦ hz.2.2)

private theorem projectionChart_fiber_iff
    (h : Manifold.IsSubmersionAtOfComplement K I J ∞ f x)
    {z : M} (hz : z ∈ (projectionChart h).source) :
    f z = f x ↔ (projectionChart h z).1 = (h.codChart.extend J) (f x) := by
  rw [projectionChart_apply_fst h hz]
  constructor
  · intro he
    rw [he]
  · intro he
    apply (h.codChart.extend J).injOn _ _ he
    · rw [OpenPartialHomeomorph.extend_source]
      exact h.source_subset_preimage_source (by simpa only [projectionChart_source] using hz)
    · simpa only [OpenPartialHomeomorph.extend_source] using h.mem_codChart_source

private def fiberChart (y : N) (x₀ : {z : M // f z = y})
    (h : Manifold.IsSubmersionAtOfComplement K I J ∞ f x₀.1) :
    OpenPartialHomeomorph {z : M // f z = y} K :=
  sliceChart {z : M | f z = y} x₀ (projectionChart h) ((h.codChart.extend J) y)
    (fun z hz ↦ by
      change f z = y ↔ _
      simpa only [x₀.2] using projectionChart_fiber_iff h hz)

private theorem fiberChart_symm_apply (y : N) (x₀ : {z : M // f z = y})
    (h : Manifold.IsSubmersionAtOfComplement K I J ∞ f x₀.1)
    {z : K} (hz : z ∈ (fiberChart y x₀ h).target) :
    ((fiberChart y x₀ h).symm z).1 =
      (projectionChart h).symm ((h.codChart.extend J) y, z) := by
  classical
  change ((if hz : ((h.codChart.extend J) y, z) ∈ (projectionChart h).target then
      ⟨(projectionChart h).symm ((h.codChart.extend J) y, z), _⟩ else x₀) :
        {z : M // f z = y}).1 = _
  have ht : ((h.codChart.extend J) y, z) ∈ (projectionChart h).target := hz
  rw [dif_pos ht]

private theorem fiberChart_symm_contMDiffOn (y : N) (x₀ : {z : M // f z = y})
    (h : Manifold.IsSubmersionAtOfComplement K I J ∞ f x₀.1) :
    ContMDiffOn 𝓘(ℝ, K) I ∞ (Subtype.val ∘ (fiberChart y x₀ h).symm)
      (fiberChart y x₀ h).target := by
  have hi : ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, F × K) ∞
      (fun z : K ↦ ((h.codChart.extend J) y, z)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  have hc := (projectionChart_symm_contMDiffOn h).comp
    hi.contMDiffOn (fun z hz ↦ hz)
  exact hc.congr (fun z hz ↦ fiberChart_symm_apply y x₀ h hz)

private theorem fiberChart_transition_contDiffOn (y : N)
    (x₁ x₂ : {z : M // f z = y})
    (h₁ : Manifold.IsSubmersionAtOfComplement K I J ∞ f x₁.1)
    (h₂ : Manifold.IsSubmersionAtOfComplement K I J ∞ f x₂.1) :
    ContDiffOn ℝ ∞ ((fiberChart y x₁ h₁).symm.trans (fiberChart y x₂ h₂))
      ((fiberChart y x₁ h₁).symm.trans (fiberChart y x₂ h₂)).source := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact (ContinuousLinearMap.snd ℝ F K).contMDiff.comp_contMDiffOn
    ((projectionChart_contMDiffOn h₂).comp
      ((fiberChart_symm_contMDiffOn y x₁ h₁).mono Set.inter_subset_left)
      (fun z hz ↦ hz.2))

@[reducible]
def submersionFiberChartedSpace (f : M → N) (y : N)
    (h : ∀ x, f x = y → Manifold.IsSubmersionAtOfComplement K I J ∞ f x) :
    ChartedSpace K {x : M // f x = y} where
  atlas := Set.range (fun x : {x : M // f x = y} ↦ fiberChart y x (h x.1 x.2))
  chartAt := fun x ↦ fiberChart y x (h x.1 x.2)
  mem_chart_source := by
    intro x
    change x.1 ∈ (projectionChart (h x.1 x.2)).source
    rw [projectionChart_source]
    exact (h x.1 x.2).mem_domChart_source
  chart_mem_atlas := fun x ↦ ⟨x, rfl⟩

theorem submersionFiberIsManifold (f : M → N) (y : N)
    (h : ∀ x, f x = y → Manifold.IsSubmersionAtOfComplement K I J ∞ f x) :
    let _ := submersionFiberChartedSpace f y h
    IsManifold 𝓘(ℝ, K) ∞ {x : M // f x = y} := by
  let _ := submersionFiberChartedSpace f y h
  refine { toHasGroupoid := ?_ }
  apply hasGroupoid_of_pregroupoid (contDiffPregroupoid ∞ 𝓘(ℝ, K))
  rintro e e' ⟨x₁, rfl⟩ ⟨x₂, rfl⟩
  change ContDiffOn ℝ ∞ (𝓘(ℝ, K) ∘ _ ∘ (𝓘(ℝ, K)).symm) _
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
    using fiberChart_transition_contDiffOn y x₁ x₂ (h x₁.1 x₁.2) (h x₂.1 x₂.2)

theorem contMDiff_submersionFiberInclusion (f : M → N) (y : N)
    (h : ∀ x, f x = y → Manifold.IsSubmersionAtOfComplement K I J ∞ f x) :
    let _ := submersionFiberChartedSpace f y h
    ContMDiff 𝓘(ℝ, K) I ∞ (Subtype.val : {x : M // f x = y} → M) := by
  dsimp only
  let _ := submersionFiberChartedSpace f y h
  intro x
  rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ]
  change ContMDiffAt 𝓘(ℝ, K) I ∞ (Subtype.val ∘ (fiberChart y x (h x.1 x.2)).symm)
    (fiberChart y x (h x.1 x.2) x)
  exact (fiberChart_symm_contMDiffOn y x (h x.1 x.2)).contMDiffAt
    ((fiberChart y x (h x.1 x.2)).open_target.mem_nhds
      ((fiberChart y x (h x.1 x.2)).map_source (mem_chart_source K x)))

theorem contMDiff_submersionFiberCorestrict
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [TopologicalSpace HP] [TopologicalSpace P] [ChartedSpace HP P]
    {IP : ModelWithCorners ℝ EP HP}
    (f : M → N) (y : N)
    (h : ∀ x, f x = y → Manifold.IsSubmersionAtOfComplement K I J ∞ f x)
    (g : P → M) (hg : ContMDiff IP I ∞ g) (hgy : ∀ z, f (g z) = y) :
    let _ := submersionFiberChartedSpace f y h
    ContMDiff IP 𝓘(ℝ, K) ∞ (fun z ↦ (⟨g z, hgy z⟩ : {x : M // f x = y})) := by
  dsimp only
  let _ := submersionFiberChartedSpace f y h
  intro z
  rw [contMDiffAt_iff_target]
  constructor
  · exact (hg.continuous.subtype_mk hgy).continuousAt
  · change ContMDiffAt IP 𝓘(ℝ, K) ∞
      (fun w ↦ (projectionChart (h (g z) (hgy z)) (g w)).2) z
    have hz : g z ∈ (projectionChart (h (g z) (hgy z))).source := by
      rw [projectionChart_source]
      exact (h (g z) (hgy z)).mem_domChart_source
    exact (ContinuousLinearMap.snd ℝ F K).contMDiff.contMDiffAt.comp z
      (((projectionChart_contMDiffOn (h (g z) (hgy z))).contMDiffAt
        ((projectionChart (h (g z) (hgy z))).open_source.mem_nhds hz)).comp z (hg z))

theorem contMDiff_submersionFiber_iff
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [TopologicalSpace HP] [TopologicalSpace P] [ChartedSpace HP P]
    {IP : ModelWithCorners ℝ EP HP}
    (f : M → N) (y : N)
    (h : ∀ x, f x = y → Manifold.IsSubmersionAtOfComplement K I J ∞ f x)
    (g : P → {x : M // f x = y}) :
    let _ := submersionFiberChartedSpace f y h
    ContMDiff IP 𝓘(ℝ, K) ∞ g ↔ ContMDiff IP I ∞ (Subtype.val ∘ g) := by
  dsimp only
  let _ := submersionFiberChartedSpace f y h
  constructor
  · exact (contMDiff_submersionFiberInclusion f y h).comp
  · intro hg
    exact contMDiff_submersionFiberCorestrict f y h (Subtype.val ∘ g) hg (fun z ↦ (g z).2)

theorem mfderiv_submersionFiberInclusion_injective (f : M → N) (y : N)
    (h : ∀ x, f x = y → Manifold.IsSubmersionAtOfComplement K I J ∞ f x)
    (x : {x : M // f x = y}) :
    let _ := submersionFiberChartedSpace f y h
    Function.Injective (mfderiv 𝓘(ℝ, K) I
      (Subtype.val : {x : M // f x = y} → M) x) := by
  dsimp only
  let _ := submersionFiberChartedSpace f y h
  let _ : IsManifold 𝓘(ℝ, K) ∞ {x : M // f x = y} := submersionFiberIsManifold f y h
  let c := chartAt K x
  have hcd : c.MDifferentiable 𝓘(ℝ, K) 𝓘(ℝ, K) :=
    ⟨(contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp)⟩
  have hci := hcd.mfderiv_injective (mem_chart_source K x)
  let g : M → K := fun z ↦ (projectionChart (h x.1 x.2) z).2
  have hx : x.1 ∈ (projectionChart (h x.1 x.2)).source := by
    rw [projectionChart_source]
    exact (h x.1 x.2).mem_domChart_source
  have hgd : MDifferentiableAt I 𝓘(ℝ, K) g x.1 :=
    ((ContinuousLinearMap.snd ℝ F K).contMDiff.contMDiffAt.comp x.1
      ((projectionChart_contMDiffOn (h x.1 x.2)).contMDiffAt
        ((projectionChart (h x.1 x.2)).open_source.mem_nhds hx))).mdifferentiableAt (by simp)
  have hid := ((contMDiff_submersionFiberInclusion f y h) x).mdifferentiableAt (by simp)
  have hd : mfderiv 𝓘(ℝ, K) 𝓘(ℝ, K) c x =
      (mfderiv I 𝓘(ℝ, K) g x.1).comp
        (mfderiv 𝓘(ℝ, K) I (Subtype.val : {x : M // f x = y} → M) x) :=
    mfderiv_comp x hgd hid
  intro u v huv
  apply hci
  rw [hd]
  exact congrArg (mfderiv I 𝓘(ℝ, K) g x.1) huv

section FiniteDimensional

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]

@[reducible]
def regularFiberChartedSpace (f : M → N) (y : N) (hf : ContMDiff I J ∞ f)
    (hreg : ∀ x, f x = y → Function.Surjective (mfderiv I J f x)) :
    ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ)
      {x : M // f x = y} :=
  submersionFiberChartedSpace f y
    (fun x hx ↦ isSubmersionAtOfComplement_of_surjective_mfderiv f hf x (hreg x hx))

theorem regularFiberIsManifold (f : M → N) (y : N) (hf : ContMDiff I J ∞ f)
    (hreg : ∀ x, f x = y → Function.Surjective (mfderiv I J f x)) :
    let _ := regularFiberChartedSpace f y hf hreg
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) ∞
      {x : M // f x = y} :=
  submersionFiberIsManifold f y _

theorem contMDiff_regularFiberInclusion (f : M → N) (y : N) (hf : ContMDiff I J ∞ f)
    (hreg : ∀ x, f x = y → Function.Surjective (mfderiv I J f x)) :
    let _ := regularFiberChartedSpace f y hf hreg
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I ∞
      (Subtype.val : {x : M // f x = y} → M) :=
  contMDiff_submersionFiberInclusion f y _

theorem contMDiff_regularFiber_iff
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [TopologicalSpace HP] [TopologicalSpace P] [ChartedSpace HP P]
    {IP : ModelWithCorners ℝ EP HP}
    (f : M → N) (y : N) (hf : ContMDiff I J ∞ f)
    (hreg : ∀ x, f x = y → Function.Surjective (mfderiv I J f x))
    (g : P → {x : M // f x = y}) :
    let _ := regularFiberChartedSpace f y hf hreg
    ContMDiff IP 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) ∞ g ↔
      ContMDiff IP I ∞ (Subtype.val ∘ g) :=
  contMDiff_submersionFiber_iff f y _ g

theorem mfderiv_regularFiberInclusion_injective
    (f : M → N) (y : N) (hf : ContMDiff I J ∞ f)
    (hreg : ∀ x, f x = y → Function.Surjective (mfderiv I J f x))
    (x : {x : M // f x = y}) :
    let _ := regularFiberChartedSpace f y hf hreg
    Function.Injective (mfderiv
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) I
      (Subtype.val : {x : M // f x = y} → M) x) :=
  mfderiv_submersionFiberInclusion_injective f y _ x

end FiniteDimensional

end Poincare.Topology.Manifold
