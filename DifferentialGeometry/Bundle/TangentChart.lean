import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

def chartFiberCoord (α : M) (p : TangentBundle I M) : E :=
  (trivializationAt E (TangentSpace I) α p).2

@[simp] lemma chartFiberCoord_def (α : M) (p : TangentBundle I M) :
    chartFiberCoord (I := I) α p =
      (trivializationAt E (TangentSpace I) α p).2 := rfl

lemma chartFiberCoord_self_zero (α : M) :
    chartFiberCoord (I := I) α
      (⟨α, (0 : E)⟩ : TangentBundle I M) = 0 := by
  classical
  have hα : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' α
  have hzero := (trivializationAt E (TangentSpace I) α).zeroSection ℝ (x := α) hα
  have hzero' : (trivializationAt E (TangentSpace I) α)
      (⟨α, (0 : TangentSpace I α)⟩ : TangentBundle I M) = (α, 0) := hzero
  change (trivializationAt E (TangentSpace I) α
      (⟨α, (0 : TangentSpace I α)⟩ : TangentBundle I M)).2 = 0
  rw [hzero']

end DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open DifferentialGeometry.Geometry.Riemannian.Geodesic

theorem extChartAt_tangent_apply_snd
    (q : TangentBundle I M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H q.proj).source) :
    (extChartAt I.tangent q p).2 =
      (trivializationAt E (TangentSpace I) q.proj).continuousLinearMapAt ℝ p.proj p.snd := by
  classical
  have hp_base : p.proj ∈ (trivializationAt E (TangentSpace I) q.proj).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hp
  have hcoe :=
    (trivializationAt E (TangentSpace I) q.proj).coe_linearMapAt_of_mem
      (R := ℝ) hp_base
  have hcoe_at :
      (trivializationAt E (TangentSpace I) q.proj).linearMapAt ℝ p.proj p.snd =
      (trivializationAt E (TangentSpace I) q.proj p).2 := by
    have h := congrFun hcoe p.snd
    exact h
  have hext : extChartAt I.tangent q p =
      ((extChartAt I q.proj) (trivializationAt E (TangentSpace I) q.proj p).1,
        (trivializationAt E (TangentSpace I) q.proj p).2) := by
    rw [FiberBundle.extChartAt]
    rfl
  rw [hext]
  change (trivializationAt E (TangentSpace I) q.proj p).2 = _
  rw [← hcoe_at]
  rfl

theorem extChartAt_tangent_apply_fst
    (q : TangentBundle I M) {p : TangentBundle I M}
    :
    (extChartAt I.tangent q p).1 = extChartAt I q.proj p.proj := by
  classical
  have hext : extChartAt I.tangent q p =
      ((extChartAt I q.proj) (trivializationAt E (TangentSpace I) q.proj p).1,
        (trivializationAt E (TangentSpace I) q.proj p).2) := by
    rw [FiberBundle.extChartAt]
    rfl
  rw [hext]
  have hp1 : (trivializationAt E (TangentSpace I) q.proj p).1 = p.proj :=
    TangentBundle.trivializationAt_fst _ _
  rw [hp1]

theorem extChartAt_tangent_zero_apply
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p =
      (extChartAt I α p.proj,
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ p.proj p.snd) := by
  classical
  apply Prod.ext
  · have h := extChartAt_tangent_apply_fst (I := I)
      (q := (⟨α, (0 : E)⟩ : TangentBundle I M)) (p := p)
    exact h
  · have h := extChartAt_tangent_apply_snd (I := I)
      (q := (⟨α, (0 : E)⟩ : TangentBundle I M)) (p := p) (by exact hp)
    exact h

theorem extChartAt_tangent_zero_apply_chartFiber
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p =
      (extChartAt I α p.proj, chartFiberCoord (I := I) α p) := by
  rw [extChartAt_tangent_zero_apply (I := I) α hp]
  apply Prod.ext
  · rfl
  · rw [Trivialization.continuousLinearMapAt_apply,
      (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem]
    · rfl
    · rw [TangentBundle.trivializationAt_baseSet]
      exact hp

theorem extChartAt_tangent_eq_at_proj
    (q : TangentBundle I M) :
    extChartAt I.tangent q =
      extChartAt I.tangent (⟨q.proj, (0 : E)⟩ : TangentBundle I M) := by
  classical
  rw [FiberBundle.extChartAt, FiberBundle.extChartAt]

end DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.Geometry.Riemannian.Exponential

lemma chartFiberCoord_eq_tangentCoordChange
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    chartFiberCoord (I := I) α p =
      tangentCoordChange I p.proj α p.proj (p.snd : E) := by
  classical
  unfold chartFiberCoord
  have hp_E_base : p.proj ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hp
  have hcoeE :=
    (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem
      (R := ℝ) hp_E_base
  have hh : (trivializationAt E (TangentSpace I) α).linearMapAt ℝ p.proj p.snd =
      (trivializationAt E (TangentSpace I) α p).snd := by
    have := congrFun hcoeE p.snd
    exact this
  have hcore :
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ p.proj =
        (tangentBundleCore I M).coordChange (achart H p.proj) (achart H α) p.proj :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ)
      (b₀ := α) (b := p.proj) hp
  have happ :
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ p.proj :
        E → E) p.snd =
        tangentCoordChange I p.proj α p.proj p.snd := by
    rw [hcore]; rfl
  change (trivializationAt E (TangentSpace I) α p).snd = _
  rw [← hh]
  change ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ p.proj :
    E → E) p.snd = _
  rw [happ]

lemma fst_continuousLinearMapAt_secondaryTriv
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (w : E × E) :
    ((trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ p w).1 =
      tangentCoordChange I p.proj α p.proj w.1 := by
  classical
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M) with he_def
  have hp_TM : p ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff]; exact hp
  have hcore2 :
      e.continuousLinearMapAt ℝ p =
        (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
          (achart (ModelProd H E) p)
          (achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)) p :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (𝕜 := ℝ) (b₀ := (⟨α, (0 : E)⟩ : TangentBundle I M)) (b := p) hp_TM
  have hcc :
      e.continuousLinearMapAt ℝ p =
        tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p :=
    hcore2
  have hp_source_p : p ∈ (extChartAt I.tangent p).source :=
    mem_extChartAt_source (I := I.tangent) p
  have hp_source_α0 : p ∈ (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]; exact hp_TM
  have hFTM :
      HasFDerivWithinAt
        ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) ∘
          (extChartAt I.tangent p).symm)
        (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p)
        (range I.tangent)
        ((extChartAt I.tangent p) p) :=
    hasFDerivWithinAt_tangentCoordChange (I := I.tangent) (M := TangentBundle I M)
      (x := p) (y := (⟨α, (0 : E)⟩ : TangentBundle I M)) (z := p)
      ⟨hp_source_p, hp_source_α0⟩
  set FTM : E × E → E × E :=
    (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) ∘
      (extChartAt I.tangent p).symm with hFTM_def
  set basepoint : E × E := (extChartAt I.tangent p) p with hbase_def
  have hFTM_fst :
      HasFDerivWithinAt (fun z : E × E => (FTM z).1)
        ((ContinuousLinearMap.fst ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p))
        (range I.tangent) basepoint :=
    hFTM.fst
  set FM : E → E :=
    (extChartAt I α) ∘ (extChartAt I p.proj).symm with hFM_def
  have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hproj_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  set U : Set (TangentBundle I M) :=
    (extChartAt I.tangent p).source ∩
      (Bundle.TotalSpace.proj ⁻¹' (chartAt H α).source) with hU_def
  have hU_open : IsOpen U :=
    ((isOpen_extChartAt_source (I := I.tangent) p).inter (hα_open.preimage hproj_cont))
  have hU_mem : p ∈ U := by
    refine ⟨?_, ?_⟩
    · exact mem_extChartAt_source (I := I.tangent) p
    · simpa using hp
  have hU_nhds : U ∈ 𝓝 p := hU_open.mem_nhds hU_mem
  have hVnhds :
      (extChartAt I.tangent p) '' U ∈
        𝓝[range I.tangent] basepoint := by
    rw [hbase_def, ← map_extChartAt_nhds (I := I.tangent) p]
    exact Filter.image_mem_map hU_nhds
  have hfst_FTM_eq_FM :
      (fun z : E × E => (FTM z).1) =ᶠ[𝓝[range I.tangent] basepoint]
        (fun z : E × E => FM z.1) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨(extChartAt I.tangent p) '' U, hVnhds, ?_⟩
    rintro z ⟨q, hqU, hqEq⟩
    have hq_source : q ∈ (extChartAt I.tangent p).source := hqU.1
    have hsymm : (extChartAt I.tangent p).symm z = q := by
      rw [← hqEq]; exact (extChartAt I.tangent p).left_inv hq_source
    change ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))
        ((extChartAt I.tangent p).symm z)).1 = FM z.1
    rw [hsymm]
    rw [extChartAt_tangent_apply_fst (I := I)
      (q := (⟨α, (0 : E)⟩ : TangentBundle I M)) (p := q)]
    have hz1 : z.1 = extChartAt I p.proj q.proj := by
      rw [← hqEq]
      have hq_proj_source_p : q.proj ∈ (chartAt H p.proj).source := by
        have := hq_source
        rw [extChartAt_source] at this
        rw [TangentBundle.mem_chart_source_iff] at this
        exact this
      exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := q)
    rw [hz1]
    change extChartAt I α q.proj =
      (extChartAt I α) ((extChartAt I p.proj).symm
        (extChartAt I p.proj q.proj))
    have hq_proj_source : q.proj ∈ (extChartAt I p.proj).source := by
      rw [extChartAt_source]
      have := hq_source
      rw [extChartAt_source] at this
      rw [TangentBundle.mem_chart_source_iff] at this
      exact this
    rw [(extChartAt I p.proj).left_inv hq_proj_source]
  have hfst_basepoint :
      (fun z : E × E => (FTM z).1) basepoint = (fun z : E × E => FM z.1) basepoint := by
    have hsymmp : (extChartAt I.tangent p).symm basepoint = p := by
      rw [hbase_def]
      exact (extChartAt I.tangent p).left_inv
        (mem_extChartAt_source (I := I.tangent) p)
    change ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))
        ((extChartAt I.tangent p).symm basepoint)).1 = FM basepoint.1
    rw [hsymmp]
    rw [extChartAt_tangent_apply_fst (I := I)
      (q := (⟨α, (0 : E)⟩ : TangentBundle I M)) (p := p)]
    have hbase_fst : basepoint.1 = extChartAt I p.proj p.proj := by
      rw [hbase_def]
      exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := p)
    rw [hbase_fst]
    change extChartAt I α p.proj =
      (extChartAt I α) ((extChartAt I p.proj).symm
        (extChartAt I p.proj p.proj))
    rw [(extChartAt I p.proj).left_inv (mem_extChartAt_source (I := I) p.proj)]
  have hFM_fst_FT :
      HasFDerivWithinAt (fun z : E × E => FM z.1)
        ((ContinuousLinearMap.fst ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p))
        (range I.tangent) basepoint :=
    hFTM_fst.congr_of_eventuallyEq hfst_FTM_eq_FM hfst_basepoint
  have hp_E_source : p.proj ∈ (extChartAt I p.proj).source :=
    mem_extChartAt_source (I := I) p.proj
  have hp_E_source_α : p.proj ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hp
  have hFM_hasD :
      HasFDerivWithinAt FM (tangentCoordChange I p.proj α p.proj)
        (range I) (extChartAt I p.proj p.proj) :=
    hasFDerivWithinAt_tangentCoordChange (I := I) (M := M)
      (x := p.proj) (y := α) (z := p.proj) ⟨hp_E_source, hp_E_source_α⟩
  have hfst_hasD :
      HasFDerivWithinAt (Prod.fst : E × E → E) (ContinuousLinearMap.fst ℝ E E)
        (range I.tangent) basepoint :=
    hasFDerivWithinAt_fst
  have hmaps : MapsTo (Prod.fst : E × E → E) (range I.tangent) (range I) := by
    intro x hx
    have hxr : x ∈ (range I) ×ˢ (range (𝓘(ℝ, E) : ModelWithCorners ℝ E E)) := by
      have : range (I.tangent : ModelWithCorners ℝ (E × E) (ModelProd H E)) =
          range I ×ˢ range (𝓘(ℝ, E) : ModelWithCorners ℝ E E) :=
        ModelWithCorners.range_prod
      rw [← this]; exact hx
    exact hxr.1
  have hFM_comp_fst :
      HasFDerivWithinAt (FM ∘ (Prod.fst : E × E → E))
        ((tangentCoordChange I p.proj α p.proj).comp
          (ContinuousLinearMap.fst ℝ E E))
        (range I.tangent) basepoint := by
    have hbase_fst : basepoint.1 = extChartAt I p.proj p.proj := by
      rw [hbase_def]
      exact extChartAt_tangent_apply_fst (I := I) (q := p) (p := p)
    have hFM_at_basepoint :
        HasFDerivWithinAt FM (tangentCoordChange I p.proj α p.proj) (range I) basepoint.1 := by
      rw [hbase_fst]; exact hFM_hasD
    exact HasFDerivWithinAt.comp basepoint
      (g := FM) (f := (Prod.fst : E × E → E))
      (g' := tangentCoordChange I p.proj α p.proj)
      (f' := ContinuousLinearMap.fst ℝ E E)
      (s := range I.tangent) (t := range I)
      hFM_at_basepoint hfst_hasD hmaps
  have huniqueMD : UniqueDiffWithinAt ℝ (range I.tangent) basepoint :=
    ModelWithCorners.uniqueDiffWithinAt_image I.tangent
  have heq_clm :
      (ContinuousLinearMap.fst ℝ E E).comp
        (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p) =
      (tangentCoordChange I p.proj α p.proj).comp
        (ContinuousLinearMap.fst ℝ E E) := by
    have h1 :
        HasFDerivWithinAt (FM ∘ (Prod.fst : E × E → E))
          ((ContinuousLinearMap.fst ℝ E E).comp
            (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p))
          (range I.tangent) basepoint := hFM_fst_FT
    exact huniqueMD.eq h1 hFM_comp_fst
  have hgoal :
      ((e.continuousLinearMapAt ℝ p) w).1 =
        tangentCoordChange I p.proj α p.proj w.1 := by
    rw [hcc]
    have := congrArg (· w) heq_clm
    have heq_app :
        ((ContinuousLinearMap.fst ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p) :
            E × E →L[ℝ] E) w =
        ((tangentCoordChange I p.proj α p.proj).comp
          (ContinuousLinearMap.fst ℝ E E) :
            E × E →L[ℝ] E) w := by
      rw [heq_clm]
    change ((ContinuousLinearMap.fst ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p) :
            E × E →L[ℝ] E) w = _
    rw [heq_app]
    rfl
  exact hgoal

lemma extChartAt_tangent_apply_snd_tangentCoordChange
    (q : TangentBundle I M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H q.proj).source) :
    (extChartAt I.tangent q p).2 =
      tangentCoordChange I p.proj q.proj p.proj (p.snd : E) := by
  classical
  have hsnd := extChartAt_tangent_apply_snd (I := I) (q := q) (p := p) hp
  have hp_base : p.proj ∈ (trivializationAt E (TangentSpace I) q.proj).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hp
  have hcoe :=
    (trivializationAt E (TangentSpace I) q.proj).coe_linearMapAt_of_mem (R := ℝ) hp_base
  have hCLM_eq_fiber :
      (trivializationAt E (TangentSpace I) q.proj).continuousLinearMapAt ℝ p.proj p.snd =
        chartFiberCoord (I := I) q.proj p := by
    change (trivializationAt E (TangentSpace I) q.proj).linearMapAt ℝ p.proj p.snd = _
    have := congrFun hcoe p.snd
    rw [this]
    rfl
  rw [hsnd, hCLM_eq_fiber]
  exact chartFiberCoord_eq_tangentCoordChange (I := I) (α := q.proj) (p := p) hp

def secondaryTrivFiberComponentMap (α : M) (p : TangentBundle I M) (z : E × E) : E :=
  tangentCoordChange I p.proj α ((extChartAt I p.proj).symm z.1) z.2

lemma snd_continuousLinearMapAt_secondaryTriv
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (w : E × E) :
    ((trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ p w).2 =
      (fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent)
        ((extChartAt I.tangent p) p)) w := by
  classical
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M) with he_def
  have hp_TM : p ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff]; exact hp
  have hcc :
      e.continuousLinearMapAt ℝ p =
        tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (𝕜 := ℝ) (b₀ := (⟨α, (0 : E)⟩ : TangentBundle I M)) (b := p) hp_TM
  have hp_source_p : p ∈ (extChartAt I.tangent p).source :=
    mem_extChartAt_source (I := I.tangent) p
  have hp_source_α0 : p ∈ (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]; exact hp_TM
  set Ψ : E × E → E × E :=
    (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) ∘
      (extChartAt I.tangent p).symm with hΨ_def
  set basepoint : E × E := (extChartAt I.tangent p) p with hbase_def
  have hΨ :
      HasFDerivWithinAt Ψ
        (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p)
        (range I.tangent) basepoint :=
    hasFDerivWithinAt_tangentCoordChange (I := I.tangent) (M := TangentBundle I M)
      (x := p) (y := (⟨α, (0 : E)⟩ : TangentBundle I M)) (z := p)
      ⟨hp_source_p, hp_source_α0⟩
  have hΨ_snd :
      HasFDerivWithinAt (fun z : E × E => (Ψ z).2)
        ((ContinuousLinearMap.snd ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p))
        (range I.tangent) basepoint :=
    hΨ.snd
  have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hproj_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  set U : Set (TangentBundle I M) :=
    (extChartAt I.tangent p).source ∩
      (Bundle.TotalSpace.proj ⁻¹' (chartAt H α).source) with hU_def
  have hU_open : IsOpen U :=
    ((isOpen_extChartAt_source (I := I.tangent) p).inter (hα_open.preimage hproj_cont))
  have hU_mem : p ∈ U := by
    refine ⟨mem_extChartAt_source (I := I.tangent) p, ?_⟩
    simpa using hp
  have hU_nhds : U ∈ 𝓝 p := hU_open.mem_nhds hU_mem
  have hVnhds :
      (extChartAt I.tangent p) '' U ∈ 𝓝[range I.tangent] basepoint := by
    rw [hbase_def, ← map_extChartAt_nhds (I := I.tangent) p]
    exact Filter.image_mem_map hU_nhds
  have hpoint : ∀ {q : TangentBundle I M}, q ∈ U →
      ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) q).2 =
        secondaryTrivFiberComponentMap (I := I) α p ((extChartAt I.tangent p) q) := by
    intro q hqU
    have hq_source : q ∈ (extChartAt I.tangent p).source := hqU.1
    have hq_proj_source_α : q.proj ∈ (chartAt H α).source := hqU.2
    have hq_proj_source_p : q.proj ∈ (chartAt H p.proj).source := by
      have := hq_source
      rw [extChartAt_source] at this
      rw [TangentBundle.mem_chart_source_iff] at this
      exact this
    have hLHS :
        ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) q).2 =
          tangentCoordChange I q.proj α q.proj (q.snd : E) :=
      extChartAt_tangent_apply_snd_tangentCoordChange (I := I)
        (q := (⟨α, (0 : E)⟩ : TangentBundle I M)) (p := q) hq_proj_source_α
    have hz1 : ((extChartAt I.tangent p) q).1 = extChartAt I p.proj q.proj :=
      extChartAt_tangent_apply_fst (I := I) (q := p) (p := q)
    have hz2 : ((extChartAt I.tangent p) q).2 =
        tangentCoordChange I q.proj p.proj q.proj (q.snd : E) :=
      extChartAt_tangent_apply_snd_tangentCoordChange (I := I) (q := p) (p := q) hq_proj_source_p
    have hq_proj_ext_source : q.proj ∈ (extChartAt I p.proj).source := by
      rw [extChartAt_source]; exact hq_proj_source_p
    have hsymm_z1 :
        (extChartAt I p.proj).symm (((extChartAt I.tangent p) q).1) = q.proj := by
      rw [hz1]; exact (extChartAt I p.proj).left_inv hq_proj_ext_source
    have hq_proj_ext_source_α : q.proj ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hq_proj_source_α
    unfold secondaryTrivFiberComponentMap
    rw [hsymm_z1, hz2]
    have hq_proj_ext_source_self : q.proj ∈ (extChartAt I q.proj).source :=
      mem_extChartAt_source (I := I) q.proj
    rw [tangentCoordChange_comp (I := I) (w := q.proj) (x := p.proj) (y := α)
      (z := q.proj) (v := (q.snd : E))
      ⟨⟨hq_proj_ext_source_self, hq_proj_ext_source⟩, hq_proj_ext_source_α⟩]
    exact hLHS.symm
  have hsnd_Ψ_eq :
      (secondaryTrivFiberComponentMap (I := I) α p) =ᶠ[𝓝[range I.tangent] basepoint]
        (fun z : E × E => (Ψ z).2) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨(extChartAt I.tangent p) '' U, hVnhds, ?_⟩
    rintro z ⟨q, hqU, hqEq⟩
    have hq_source : q ∈ (extChartAt I.tangent p).source := hqU.1
    have hsymm : (extChartAt I.tangent p).symm z = q := by
      rw [← hqEq]; exact (extChartAt I.tangent p).left_inv hq_source
    change secondaryTrivFiberComponentMap (I := I) α p z =
      ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))
        ((extChartAt I.tangent p).symm z)).2
    rw [hsymm, ← hqEq]
    exact (hpoint hqU).symm
  have hsnd_basepoint :
      (secondaryTrivFiberComponentMap (I := I) α p) basepoint =
        (fun z : E × E => (Ψ z).2) basepoint := by
    have hsymmp : (extChartAt I.tangent p).symm basepoint = p := by
      rw [hbase_def]
      exact (extChartAt I.tangent p).left_inv
        (mem_extChartAt_source (I := I.tangent) p)
    change secondaryTrivFiberComponentMap (I := I) α p basepoint =
      ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))
        ((extChartAt I.tangent p).symm basepoint)).2
    rw [hsymmp, hbase_def]
    exact (hpoint hU_mem).symm
  have hform_hasD :
      HasFDerivWithinAt (secondaryTrivFiberComponentMap (I := I) α p)
        ((ContinuousLinearMap.snd ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p))
        (range I.tangent) basepoint :=
    hΨ_snd.congr_of_eventuallyEq hsnd_Ψ_eq hsnd_basepoint
  have hfderivWithin_eq :
      fderivWithin ℝ (secondaryTrivFiberComponentMap (I := I) α p) (range I.tangent) basepoint =
        (ContinuousLinearMap.snd ℝ E E).comp
          (tangentCoordChange I.tangent p (⟨α, (0 : E)⟩ : TangentBundle I M) p) :=
    hform_hasD.fderivWithin (ModelWithCorners.uniqueDiffWithinAt_image I.tangent)
  rw [hcc]
  rw [hfderivWithin_eq]
  rfl

end DifferentialGeometry.Geometry.Riemannian.Geodesic

end
