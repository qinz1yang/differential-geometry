import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeLocalMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

set_option autoImplicit false
noncomputable section
open Bundle Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold J ∞ N]

def partialRadialChart (e : PartialDiffeomorph 𝓘(ℝ, V) J V N ∞) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × V) (𝓘(ℝ, ℝ).prod J) (ℝ × V) (ℝ × N) ∞ where
  toPartialEquiv := (PartialEquiv.refl ℝ).prod e.toPartialEquiv
  open_source := isOpen_univ.prod e.open_source
  open_target := isOpen_univ.prod e.open_target
  contMDiffOn_toFun := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (contMDiff_id : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ id).contMDiffOn.prodMap
      e.contMDiffOn
  contMDiffOn_invFun := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (contMDiff_id : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ id).contMDiffOn.prodMap
      e.symm.contMDiffOn

omit [IsManifold J ∞ N] in
@[simp] theorem partialRadialChart_apply
    (e : PartialDiffeomorph 𝓘(ℝ, V) J V N ∞) (z : ℝ × V) :
    partialRadialChart e z = (z.1, e z.2) := rfl

omit [IsManifold J ∞ N] in
theorem partialRadialChart_mfderiv
    (e : PartialDiffeomorph 𝓘(ℝ, V) J V N ∞) {z : ℝ × V}
    (hz : z ∈ (partialRadialChart e).source) (v : ℝ × V) :
    mfderiv 𝓘(ℝ, ℝ × V) (𝓘(ℝ, ℝ).prod J) (partialRadialChart e) z v =
      (v.1, mfderiv 𝓘(ℝ, V) J e z.2 v.2) := by
  have he := e.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hz.2
  change mfderiv 𝓘(ℝ, ℝ × V) (𝓘(ℝ, ℝ).prod J) (Prod.map id e) z v = _
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  rw [mfderiv_prodMap mdifferentiableAt_id he, mfderiv_id]
  rfl

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold I2 ∞ S]

def angularModelChart (s : S) :
    PartialDiffeomorph I2 I2 S (EuclideanSpace ℝ (Fin 2)) ∞ where
  toPartialEquiv := (chartAt (EuclideanSpace ℝ (Fin 2)) s).toPartialEquiv
  open_source := (chartAt (EuclideanSpace ℝ (Fin 2)) s).open_source
  open_target := (chartAt (EuclideanSpace ℝ (Fin 2)) s).open_target
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {U : Set M}

attribute [local instance] ConeChart.topology ConeChart.charted ConeChart.smooth
  ConeChart.t2 ConeChart.sigmaCompact


def ConeChart.coordinates (C : ConeChart g U) (s : C.surface) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) I3
      (ℝ × EuclideanSpace ℝ (Fin 2)) M ∞ :=
  (partialRadialChart (angularModelChart s).symm).trans C.map

omit [T2Space M] [SigmaCompactSpace M] in
theorem ConeChart.coordinates_mem_source (C : ConeChart g U)
    {z : ℝ × C.surface} (hz : z ∈ C.map.source) :
    (z.1, chartAt (EuclideanSpace ℝ (Fin 2)) z.2 z.2) ∈
      (C.coordinates z.2).source := by
  have hs := mem_chart_source (EuclideanSpace ℝ (Fin 2)) z.2
  refine ⟨⟨Set.mem_univ _, (chartAt (EuclideanSpace ℝ (Fin 2)) z.2).map_source hs⟩, ?_⟩
  change (z.1, (chartAt (EuclideanSpace ℝ (Fin 2)) z.2).symm
    (chartAt (EuclideanSpace ℝ (Fin 2)) z.2 z.2)) ∈ C.map.source
  rwa [(chartAt (EuclideanSpace ℝ (Fin 2)) z.2).left_inv hs]

omit [T2Space M] [SigmaCompactSpace M] in
theorem ConeChart.coordinates_apply_center (C : ConeChart g U) (z : ℝ × C.surface) :
    C.coordinates z.2 (z.1, chartAt (EuclideanSpace ℝ (Fin 2)) z.2 z.2) = C.map z := by
  change C.map (z.1, (chartAt (EuclideanSpace ℝ (Fin 2)) z.2).symm
    (chartAt (EuclideanSpace ℝ (Fin 2)) z.2 z.2)) = C.map z
  rw [(chartAt (EuclideanSpace ℝ (Fin 2)) z.2).left_inv
    (mem_chart_source (EuclideanSpace ℝ (Fin 2)) z.2)]

omit [T2Space M] [SigmaCompactSpace M] in
theorem ConeChart.coordinates_mfderiv_radial (C : ConeChart g U) (s : C.surface)
    {y : ℝ × EuclideanSpace ℝ (Fin 2)} (hy : y ∈ (C.coordinates s).source) :
    mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) I3 (C.coordinates s) y (1, 0) =
      mfderiv (𝓘(ℝ, ℝ).prod I2) I3 C.map
        (y.1, (angularModelChart s).symm y.2) (1, 0) := by
  let e := partialRadialChart (angularModelChart s).symm
  have he := e.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hy.1
  have hC : MDifferentiableAt (𝓘(ℝ, ℝ).prod I2) I3 C.map (e y) :=
    C.map.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hy.2
  change mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) I3 (C.map ∘ e) y (1, 0) = _
  erw [mfderiv_comp y hC he, ContinuousLinearMap.comp_apply,
    partialRadialChart_mfderiv (angularModelChart s).symm hy.1]
  have hzero : mfderiv I2 I2 (angularModelChart s).symm y.2
      (0 : EuclideanSpace ℝ (Fin 2)) = 0 := map_zero _
  erw [hzero]
  rfl

omit [T2Space M] [SigmaCompactSpace M] in
theorem ConeChart.coordinates_metric (C : ConeChart g U) (s : C.surface)
    {y : ℝ × EuclideanSpace ℝ (Fin 2)} (hy : y ∈ (C.coordinates s).source)
    (v w : ℝ × EuclideanSpace ℝ (Fin 2)) :
    g.inner (C.coordinates s y)
      (mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) I3 (C.coordinates s) y v)
      (mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) I3 (C.coordinates s) y w) =
        v.1 * w.1 + y.1 ^ 2 *
          C.metric.inner ((angularModelChart s).symm y.2)
            (mfderiv I2 I2 (angularModelChart s).symm y.2 v.2)
            (mfderiv I2 I2 (angularModelChart s).symm y.2 w.2) := by
  let e := partialRadialChart (angularModelChart s).symm
  have he := e.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hy.1
  have hC : MDifferentiableAt (𝓘(ℝ, ℝ).prod I2) I3 C.map (e y) :=
    C.map.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hy.2
  have hd (a : ℝ × EuclideanSpace ℝ (Fin 2)) :
      mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) I3 (C.coordinates s) y a =
        mfderiv (𝓘(ℝ, ℝ).prod I2) I3 C.map (e y)
          (a.1, mfderiv I2 I2 (angularModelChart s).symm y.2 a.2) := by
    change mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) I3 (C.map ∘ e) y a = _
    erw [mfderiv_comp y hC he, ContinuousLinearMap.comp_apply,
      partialRadialChart_mfderiv (angularModelChart s).symm hy.1]
    rfl
  rw [hd, hd]
  exact C.radial_metric (e y) hy.2 _ _

theorem ConeChart.radial_curvature_zero (C : ConeChart g U)
    {z : ℝ × C.surface} (hz : z ∈ C.map.source)
    (u v w : TangentSpace I3 (C.map z)) :
    metricRm04StandardAt g (C.map z) u v
      (mfderiv (𝓘(ℝ, ℝ).prod I2) I3 C.map z (1, 0)) w = 0 := by
  let A := EuclideanSpace ℝ (Fin 2)
  let P := ℝ × A
  let y0 : P := (z.1, chartAt A z.2 z.2)
  let Φ := C.coordinates z.2
  have hy0 : y0 ∈ Φ.source := C.coordinates_mem_source hz
  have ha0 : y0.2 ∈ (angularModelChart z.2).symm.source := hy0.1.2
  obtain ⟨ga, Va, hva, _hva, hga⟩ := exists_partialDiffeomorph_modelMetric
    C.metric (angularModelChart z.2).symm ha0
  obtain ⟨gp, Vp, hvp, hVp, hgp⟩ := exists_partialDiffeomorph_modelMetric g Φ hy0
  let h : A → A →L[ℝ] A →L[ℝ] ℝ := fun a => tangentBilinearFormToModel a (ga.inner a)
  have hnear : (fun y => tangentBilinearFormToModel y (gp.inner y)) =ᶠ[𝓝 y0]
      coneForm h := by
    filter_upwards [Vp.isOpen.mem_nhds hvp,
      continuous_snd.continuousAt.preimage_mem_nhds (Va.isOpen.mem_nhds hva)] with y hyp hya
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    change gp.inner y a b = a.1 * b.1 + y.1 ^ 2 * ga.inner y.2 a.2 b.2
    rw [hgp y hyp a b, C.coordinates_metric z.2 (hVp hyp), hga y.2 hya a.2 b.2]
  have hh : ∀ᶠ y : P in 𝓝 y0, DifferentiableAt ℝ h y.2 :=
    Filter.Eventually.of_forall fun _ => (modelMetric_form_contDiff ga).differentiable
      (by simp) _
  have hr : y0.1 ≠ 0 := ne_of_gt (C.positive_radius z hz)
  let eD := (Φ.isLocalDiffeomorphAt 𝓘(ℝ, P) I3 ∞ hy0).mfderivToContinuousLinearEquiv
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hd (a : TangentSpace I3 (C.map z)) :
      mfderiv 𝓘(ℝ, P) I3 Φ y0 (eD.symm a) = a := by
    rw [← (Φ.isLocalDiffeomorphAt 𝓘(ℝ, P) I3 ∞ hy0).mfderivToContinuousLinearEquiv_coe
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)]
    exact eD.apply_symm_apply a
  have hzero := metricRm04_coneRadial_eq_zero gp hnear hh hr
    (eD.symm u) (eD.symm v) (eD.symm w)
  have htrans := metricRm04_partialDiffeomorph_of_inner_eq g Φ gp Vp hVp hgp
    ⟨y0, hvp⟩ (eD.symm u) (eD.symm v) (1, 0) (eD.symm w)
  have hzero' : metricRm04StandardAt gp y0 (eD.symm u) (eD.symm v) (1, 0) (eD.symm w) = 0 :=
    hzero
  rw [htrans] at hzero'
  rw [hd, hd, hd, C.coordinates_mfderiv_radial z.2 hy0] at hzero'
  have hangular : (y0.1, (angularModelChart z.2).symm y0.2) = z := by
    change (z.1, (chartAt A z.2).symm (chartAt A z.2 z.2)) = z
    rw [(chartAt A z.2).left_inv (mem_chart_source A z.2)]
  change metricRm04StandardAt g (C.map (y0.1, (angularModelChart z.2).symm y0.2)) u v
    (mfderiv (𝓘(ℝ, ℝ).prod I2) I3 C.map
      (y0.1, (angularModelChart z.2).symm y0.2) (1, 0)) w = 0 at hzero'
  rw [hangular] at hzero'
  exact hzero'

omit [SigmaCompactSpace M] in
theorem ConeChart.exists_concurrentField (C : ConeChart g U) {p : M} (hp : p ∈ U) :
    ∃ W : Opens M, p ∈ W ∧ (W : Set M) ⊆ U ∧
      ∃ Z : ContMDiffSection I3 ThreeSpace ∞ (TangentSpace I3 : W → Type _),
        ∀ y : W, ∀ v : TangentSpace I3 y,
          metricCov (g.restrictOpen W) Z y v = v := by
  have ht : p ∈ C.map.target := C.target_eq.symm ▸ hp
  let z := C.map.symm p
  have hz : z ∈ C.map.source := C.map.map_target' ht
  have hzp : C.map z = p := C.map.right_inv' ht
  let A := EuclideanSpace ℝ (Fin 2)
  let P := ℝ × A
  let y0 : P := (z.1, chartAt A z.2 z.2)
  let Φ := C.coordinates z.2
  have hy0 : y0 ∈ Φ.source := C.coordinates_mem_source hz
  obtain ⟨ga, Va, hva, _hVa, hga⟩ := exists_partialDiffeomorph_modelMetric
    C.metric (angularModelChart z.2).symm hy0.1.2
  obtain ⟨gp, Vp, hvp, hVp, hgp⟩ := exists_partialDiffeomorph_modelMetric g Φ hy0
  let h : A → A →L[ℝ] A →L[ℝ] ℝ := fun a => tangentBilinearFormToModel a (ga.inner a)
  have hnear : (fun y => tangentBilinearFormToModel y (gp.inner y)) =ᶠ[𝓝 y0]
      coneForm h := by
    filter_upwards [Vp.isOpen.mem_nhds hvp,
      continuous_snd.continuousAt.preimage_mem_nhds (Va.isOpen.mem_nhds hva)] with y hyp hya
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    change gp.inner y a b = a.1 * b.1 + y.1 ^ 2 * ga.inner y.2 a.2 b.2
    rw [hgp y hyp a b, C.coordinates_metric z.2 (hVp hyp), hga y.2 hya a.2 b.2]
  let ZE : ContMDiffSection 𝓘(ℝ, P) P ∞ (TangentSpace 𝓘(ℝ, P) : P → Type _) :=
    ⟨coneEulerField, coneEulerField_contMDiff⟩
  have hr : y0.1 ≠ 0 := ne_of_gt (C.positive_radius z hz)
  have hrnear : ∀ᶠ y : P in 𝓝 y0, y.1 ≠ 0 :=
    continuous_fst.continuousAt.eventually_ne hr
  have hconcurrent : ∀ᶠ y in 𝓝 y0, ∀ v : P, metricCov gp ZE y v = v := by
    filter_upwards [eventually_eventually_nhds.mpr hnear, hrnear] with y hy hry
    intro v
    exact leviCivita_coneEuler_of_coneForm gp hy
      ((modelMetric_form_contDiff ga).differentiable (by simp) y.2) hry v
  obtain ⟨K, hKsub, hKopen, hy0K⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (Vp.isOpen.mem_nhds hvp) hconcurrent)
  let V : Opens P := ⟨K, hKopen⟩
  have hV : (V : Set P) ⊆ Φ.source := fun y hy => hVp (hKsub hy).1
  obtain ⟨W, hW, Z, hZ⟩ := exists_concurrentField_partialDiffeomorph g Φ gp V hV
    (fun y hy => hgp y (hKsub hy).1) ZE (fun y hy => (hKsub hy).2)
  refine ⟨W, ?_, ?_, Z, hZ⟩
  · change p ∈ (W : Set M)
    rw [hW]
    exact ⟨y0, hy0K, (C.coordinates_apply_center z).trans hzp⟩
  · intro y hy
    rw [hW] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [← C.target_eq]
    exact C.map.map_source' (hV ha).2

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
