import DifferentialGeometry.Geometry.Metric.ConeChart.Defs
import DifferentialGeometry.Geometry.Metric.ConeChart.Curvature
import DifferentialGeometry.Geometry.Metric.Euclidean.Construction
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.LocalExtension
import DifferentialGeometry.Geometry.Connection.LeviCivita.ConcurrentField
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open Bundle Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.ConeChart

open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

section AuxiliaryCharts

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

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

@[simp] theorem partialRadialChart_apply
    (e : PartialDiffeomorph 𝓘(ℝ, V) J V N ∞) (z : ℝ × V) :
    partialRadialChart e z = (z.1, e z.2) := rfl

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

variable {n : ℕ} {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) S] [IsManifold (𝓡 n) ∞ S]

def angularModelChart (s : S) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) S (EuclideanSpace ℝ (Fin n)) ∞ where
  toPartialEquiv := (chartAt (EuclideanSpace ℝ (Fin n)) s).toPartialEquiv
  open_source := (chartAt (EuclideanSpace ℝ (Fin n)) s).open_source
  open_target := (chartAt (EuclideanSpace ℝ (Fin n)) s).open_target
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

end AuxiliaryCharts

universe u uE uH v

variable {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : SmoothRiemannianMetric I M} {U : Set M}

attribute [local instance] topology charted smooth t2 sigmaCompact

def coordinates (C : ConeChart.{u, uE, uH, v} n g U) (s : C.surface) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) I
      (ℝ × EuclideanSpace ℝ (Fin n)) M ∞ :=
  (partialRadialChart (angularModelChart s).symm).trans C.map

theorem coordinates_mem_source (C : ConeChart.{u, uE, uH, v} n g U)
    {z : ℝ × C.surface} (hz : z ∈ C.map.source) :
    (z.1, chartAt (EuclideanSpace ℝ (Fin n)) z.2 z.2) ∈
      (coordinates C z.2).source := by
  have hs := mem_chart_source (EuclideanSpace ℝ (Fin n)) z.2
  refine ⟨⟨Set.mem_univ _, (chartAt (EuclideanSpace ℝ (Fin n)) z.2).map_source hs⟩, ?_⟩
  change (z.1, (chartAt (EuclideanSpace ℝ (Fin n)) z.2).symm
    (chartAt (EuclideanSpace ℝ (Fin n)) z.2 z.2)) ∈ C.map.source
  rwa [(chartAt (EuclideanSpace ℝ (Fin n)) z.2).left_inv hs]

theorem coordinates_apply_center (C : ConeChart.{u, uE, uH, v} n g U) (z : ℝ × C.surface) :
    coordinates C z.2 (z.1, chartAt (EuclideanSpace ℝ (Fin n)) z.2 z.2) = C.map z := by
  change C.map (z.1, (chartAt (EuclideanSpace ℝ (Fin n)) z.2).symm
    (chartAt (EuclideanSpace ℝ (Fin n)) z.2 z.2)) = C.map z
  rw [(chartAt (EuclideanSpace ℝ (Fin n)) z.2).left_inv
    (mem_chart_source (EuclideanSpace ℝ (Fin n)) z.2)]

theorem coordinates_mfderiv_radial (C : ConeChart.{u, uE, uH, v} n g U) (s : C.surface)
    {y : ℝ × EuclideanSpace ℝ (Fin n)} (hy : y ∈ (coordinates C s).source) :
    mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) I (coordinates C s) y (1, 0) =
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) I C.map
        (y.1, (angularModelChart s).symm y.2) (1, 0) := by
  let e := partialRadialChart (angularModelChart (n := n) s).symm
  have he := e.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hy.1
  have hC : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) I C.map (e y) :=
    C.map.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hy.2
  change mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) I (C.map ∘ e) y (1, 0) = _
  erw [mfderiv_comp y hC he, ContinuousLinearMap.comp_apply,
    partialRadialChart_mfderiv (angularModelChart s).symm hy.1]
  have hzero : mfderiv (𝓡 n) (𝓡 n) (angularModelChart s).symm y.2
      (0 : EuclideanSpace ℝ (Fin n)) = 0 := map_zero _
  erw [hzero]
  rfl

theorem coordinates_metric (C : ConeChart.{u, uE, uH, v} n g U) (s : C.surface)
    {y : ℝ × EuclideanSpace ℝ (Fin n)} (hy : y ∈ (coordinates C s).source)
    (v w : ℝ × EuclideanSpace ℝ (Fin n)) :
    g.inner (coordinates C s y)
      (mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) I (coordinates C s) y v)
      (mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) I (coordinates C s) y w) =
        v.1 * w.1 + y.1 ^ 2 *
          C.metric.inner ((angularModelChart s).symm y.2)
            (mfderiv (𝓡 n) (𝓡 n) (angularModelChart s).symm y.2 v.2)
            (mfderiv (𝓡 n) (𝓡 n) (angularModelChart s).symm y.2 w.2) := by
  let e := partialRadialChart (angularModelChart (n := n) s).symm
  have he := e.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hy.1
  have hC : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) I C.map (e y) :=
    C.map.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0) hy.2
  have hd (a : ℝ × EuclideanSpace ℝ (Fin n)) :
      mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) I (coordinates C s) y a =
        mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) I C.map (e y)
          (a.1, mfderiv (𝓡 n) (𝓡 n) (angularModelChart s).symm y.2 a.2) := by
    change mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) I (C.map ∘ e) y a = _
    erw [mfderiv_comp y hC he, ContinuousLinearMap.comp_apply,
      partialRadialChart_mfderiv (angularModelChart s).symm hy.1]
    rfl
  rw [hd, hd]
  exact C.radial_metric (e y) hy.2 _ _

variable [FiniteDimensional ℝ E] [T2Space M]

theorem radial_curvature_zero (C : ConeChart.{u, uE, uH, v} n g U)
    {z : ℝ × C.surface} (hz : z ∈ C.map.source)
    (u v w : TangentSpace I (C.map z)) :
    metricRm04StandardAt g (C.map z) u v
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) I C.map z (1, 0)) w = 0 := by
  let A := EuclideanSpace ℝ (Fin n)
  let P := ℝ × A
  let y0 : P := (z.1, chartAt A z.2 z.2)
  let Φ := coordinates C z.2
  have hy0 : y0 ∈ Φ.source := coordinates_mem_source C hz
  have ha0 : y0.2 ∈ (angularModelChart z.2).symm.source := hy0.1.2
  obtain ⟨ga, Va, hva, _hva, hga⟩ := exists_model_metric_eq_pullback_on_nhds
    C.metric (angularModelChart z.2).symm ha0
  obtain ⟨gp, Vp, hvp, hVp, hgp⟩ := exists_model_metric_eq_pullback_on_nhds g Φ hy0
  let h : A → A →L[ℝ] A →L[ℝ] ℝ :=
    fun a => (show A →L[ℝ] A →L[ℝ] ℝ from by exact ga.inner a)
  have hnear : (fun y => tangentBilinearFormToModel y (gp.inner y)) =ᶠ[𝓝 y0]
      coneForm h := by
    filter_upwards [Vp.isOpen.mem_nhds hvp,
      continuous_snd.continuousAt.preimage_mem_nhds (Va.isOpen.mem_nhds hva)] with y hyp hya
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    change gp.inner y a b = a.1 * b.1 + y.1 ^ 2 * ga.inner y.2 a.2 b.2
    rw [hgp y hyp a b, coordinates_metric C z.2 (hVp hyp), hga y.2 hya a.2 b.2]
  have hh : ∀ᶠ y : P in 𝓝 y0, DifferentiableAt ℝ h y.2 :=
    Filter.Eventually.of_forall fun _ => (contDiff_metric_inner ga).differentiable
      (by simp) _
  have hr : y0.1 ≠ 0 := ne_of_gt (C.positive_radius z hz)
  let eD := (Φ.isLocalDiffeomorphAt 𝓘(ℝ, P) I ∞ hy0).mfderivToContinuousLinearEquiv
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hd (a : TangentSpace I (C.map z)) :
      mfderiv 𝓘(ℝ, P) I Φ y0 (eD.symm a) = a := by
    rw [← (Φ.isLocalDiffeomorphAt 𝓘(ℝ, P) I ∞ hy0).mfderivToContinuousLinearEquiv_coe
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)]
    exact eD.apply_symm_apply a
  have hzero := metricRm04_coneRadial_eq_zero gp hnear hh hr
    (eD.symm u) (eD.symm v) (eD.symm w)
  have htrans := metricRm04StandardAt_eq_of_partialDiffeomorph_restriction Φ Vp hVp gp g
    (fun x v w => hgp x x.2 v w) ⟨y0, hvp⟩ (eD.symm u) (eD.symm v) (1, 0) (eD.symm w)
  have hzero' : metricRm04StandardAt gp y0 (eD.symm u) (eD.symm v) (1, 0) (eD.symm w) = 0 :=
    hzero
  rw [htrans] at hzero'
  rw [hd, hd, hd, coordinates_mfderiv_radial C z.2 hy0] at hzero'
  have hangular : (y0.1, (angularModelChart z.2).symm y0.2) = z := by
    change (z.1, (chartAt A z.2).symm (chartAt A z.2 z.2)) = z
    rw [(chartAt A z.2).left_inv (mem_chart_source A z.2)]
  change metricRm04StandardAt g (C.map (y0.1, (angularModelChart z.2).symm y0.2)) u v
    (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) I C.map
      (y0.1, (angularModelChart z.2).symm y0.2) (1, 0)) w = 0 at hzero'
  rw [hangular] at hzero'
  exact hzero'

theorem exists_concurrent_field (C : ConeChart.{u, uE, uH, v} n g U) {p : M} (hp : p ∈ U) :
    ∃ W : Opens M, p ∈ W ∧ (W : Set M) ⊆ U ∧
      ∃ Z : ContMDiffSection I E ∞ (TangentSpace I : W → Type _),
        ∀ y : W, ∀ v : TangentSpace I y,
          metricCov (g.restrictOpen W) Z y v = v := by
  have ht : p ∈ C.map.target := C.target_eq.symm ▸ hp
  let z := C.map.symm p
  have hz : z ∈ C.map.source := C.map.map_target' ht
  have hzp : C.map z = p := C.map.right_inv' ht
  let A := EuclideanSpace ℝ (Fin n)
  let P := ℝ × A
  let y0 : P := (z.1, chartAt A z.2 z.2)
  let Φ := coordinates C z.2
  have hy0 : y0 ∈ Φ.source := coordinates_mem_source C hz
  obtain ⟨ga, Va, hva, _hVa, hga⟩ := exists_model_metric_eq_pullback_on_nhds
    C.metric (angularModelChart z.2).symm hy0.1.2
  obtain ⟨gp, Vp, hvp, hVp, hgp⟩ := exists_model_metric_eq_pullback_on_nhds g Φ hy0
  let h : A → A →L[ℝ] A →L[ℝ] ℝ :=
    fun a => (show A →L[ℝ] A →L[ℝ] ℝ from by exact ga.inner a)
  have hnear : (fun y => tangentBilinearFormToModel y (gp.inner y)) =ᶠ[𝓝 y0]
      coneForm h := by
    filter_upwards [Vp.isOpen.mem_nhds hvp,
      continuous_snd.continuousAt.preimage_mem_nhds (Va.isOpen.mem_nhds hva)] with y hyp hya
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    change gp.inner y a b = a.1 * b.1 + y.1 ^ 2 * ga.inner y.2 a.2 b.2
    rw [hgp y hyp a b, coordinates_metric C z.2 (hVp hyp), hga y.2 hya a.2 b.2]
  let ZE : ContMDiffSection 𝓘(ℝ, P) P ∞ (TangentSpace 𝓘(ℝ, P) : P → Type _) :=
    ⟨coneEulerField, coneEulerField_contMDiff⟩
  have hr : y0.1 ≠ 0 := ne_of_gt (C.positive_radius z hz)
  have hrnear : ∀ᶠ y : P in 𝓝 y0, y.1 ≠ 0 :=
    continuous_fst.continuousAt.eventually_ne hr
  have hconcurrent : ∀ᶠ y in 𝓝 y0, ∀ v : P, metricCov gp ZE y v = v := by
    filter_upwards [eventually_eventually_nhds.mpr hnear, hrnear] with y hy hry
    intro v
    exact leviCivita_coneEuler_of_coneForm gp hy
      ((contDiff_metric_inner ga).differentiable (by simp) y.2) hry v
  obtain ⟨K, hKsub, hKopen, hy0K⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (Vp.isOpen.mem_nhds hvp) hconcurrent)
  let V : Opens P := ⟨K, hKopen⟩
  have hV : (V : Set P) ⊆ Φ.source := fun y hy => hVp (hKsub hy).1
  obtain ⟨W, hW, Z, hZ⟩ := exists_concurrent_field_of_partialDiffeomorph g Φ gp V hV
    (fun y hy => hgp y (hKsub hy).1) ZE (fun y hy => (hKsub hy).2)
  refine ⟨W, ?_, ?_, Z, hZ⟩
  · change p ∈ (W : Set M)
    rw [hW]
    exact ⟨y0, hy0K, (coordinates_apply_center C z).trans hzp⟩
  · intro y hy
    rw [hW] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [← C.target_eq]
    exact C.map.map_source' (hV ha).2

end DifferentialGeometry.Geometry.Riemannian.ConeChart
