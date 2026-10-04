import DifferentialGeometry.Geometry.Thurston.SphericalProductIsometry
import DifferentialGeometry.Geometry.Thurston.ModelAtlas
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Subbundle
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PartialDiffeomorph
import DifferentialGeometry.Geometry.Connection.Product
import DifferentialGeometry.Geometry.Curvature.RicciSharpSmooth
import DifferentialGeometry.Bundle.SmoothSubbundle.Kernel
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

/-!
# The line field of an `S² × ℝ` structure is parallel

Chapter 7, packet P8b. On the model, the vertical field `verticalField = (0, ∂ₜ)` is parallel
(`leviCivita_verticalField`) and spans the kernel of the Ricci endomorphism. A chart of a model
atlas is a local isometry, so the Ricci kernel of a metric with a model atlas is the image of the
vertical line (`ker_ricciSharp_eq_span_chartVertical`): it has rank one and is a smooth subbundle
`ricciLine`. Parallel transport commutes with the charts
(`mfderiv_covDerivAlong_partialDiffeomorph`), so the pushed vertical field is parallel along
every curve (`chartVertical_parallel_along`) and the Ricci kernel is a parallel family
(`isParallelSubmoduleFamily_ricciLine`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology

namespace GC.Geometry.SphericalProduct

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "CI" => SpatialNeckCylinderModel
local notation "gS" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance parallelLineSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

def lineUnitField : ContMDiffSection 𝓘(ℝ, ℝ) ℝ ∞ (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _) where
  toFun t := (1 : ℝ)
  contMDiff_toFun := by
    intro t
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simp only [trivializationAt_model_space_apply]
    exact contMDiffAt_const

def verticalField :
    ContMDiffSection CI (E2 × ℝ) ∞ (TangentSpace CI : SpatialNeckCylinder → Type _) :=
  VectorField.productVectorField 0 lineUnitField

theorem verticalField_apply (p : SpatialNeckCylinder) :
    (verticalField p : E2 × ℝ) = (0, 1) := rfl

theorem leviCivita_lineUnitField (t : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) t) :
    (LeviCivita (DifferentialGeometry.euclideanMetric (E := ℝ))) lineUnitField t v = 0 := by
  let g := DifferentialGeometry.euclideanMetric (E := ℝ)
  have hY : MDiffAt (T% (lineUnitField : (t : ℝ) → TangentSpace 𝓘(ℝ, ℝ) t)) t :=
    lineUnitField.mdifferentiableAt
  have hmetric := (LeviCivita_isMetricCompatible (I := 𝓘(ℝ, ℝ)) g).apply hY hY v
  have hconst : (fun b : ℝ => g.inner b (lineUnitField b) (lineUnitField b)) =
      fun b => (1 : ℝ) := by
    funext b
    change inner ℝ (1 : ℝ) (1 : ℝ) = 1
    simp
  rw [hconst, mfderiv_const] at hmetric
  set c : ℝ := (LeviCivita g) lineUnitField t v
  change (0 : ℝ) = inner ℝ c (1 : ℝ) + inner ℝ (1 : ℝ) c at hmetric
  simp only [RCLike.inner_apply, conj_trivial] at hmetric
  change c = 0
  linarith

theorem leviCivita_verticalField (p : SpatialNeckCylinder) (v : TangentSpace CI p) :
    (LeviCivita sphericalProductModelMetric) verticalField p v = 0 := by
  have h := leviCivita_productVectorField_apply gS (DifferentialGeometry.euclideanMetric (E := ℝ))
    0 lineUnitField p v
  rw [sphericalProductModelMetric_eq_prod, LeviCivita_eq_leviCivitaConnectionOfMetric]
  change leviCivitaConnectionOfMetric ((gS).prod (DifferentialGeometry.euclideanMetric (E := ℝ)))
    (VectorField.productVectorField 0 lineUnitField) p v = 0
  rw [h]
  refine Prod.ext ?_ ?_
  · change leviCivitaConnectionOfMetric gS ((0 : ContMDiffSection (𝓡 2) E2 ∞
      (TangentSpace (𝓡 2) : SpatialNeckSphere → Type _)) : _) p.1 v.1 = 0
    rw [ContMDiffSection.coe_zero, ← LeviCivita_eq_leviCivitaConnectionOfMetric,
      CovariantDerivative.zero]
    rfl
  · exact leviCivita_lineUnitField p.2 v.2

section CurveSection

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartRepAt_section_differentiableAt (γ : ℝ → M) {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (s : ∀ y : M, TangentSpace I y)
    (hs : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% s) (γ t)) :
    DifferentiableAt ℝ (chartRepAt (I := I) γ (fun r => s (γ r)) t) t := by
  classical
  let α : M := γ t
  let f : E → E := chartESectionRepr (I := I) α (fun x => s x) ∘ (extChartAt I α).symm
  let u : ℝ → E := DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) α γ
  have hgood : α ∈ chartLeviCivitaGoodSet (I := I) α :=
    self_mem_chartLeviCivitaGoodSet (I := I) α
  have hf : DifferentiableAt ℝ f (extChartAt I α (γ t)) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hgood hs
  have hu : DifferentiableAt ℝ u t := by
    have hchart : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => extChartAt I α (γ r)) t :=
      (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (γ t))).comp t hγ
    exact mdifferentiableAt_iff_differentiableAt.mp hchart
  have hsrc : γ ⁻¹' (extChartAt I α).source ∈ 𝓝 t := by
    apply hγ.continuousAt.preimage_mem_nhds
    apply (isOpen_extChartAt_source (I := I) α).mem_nhds
    exact mem_extChartAt_source (I := I) α
  have heq : (f ∘ u) =ᶠ[𝓝 t] chartRepAt (I := I) γ (fun r => s (γ r)) t := by
    filter_upwards [hsrc] with r hr
    simp only [Function.comp_apply, f, u,
      DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve, chartRepAt_apply]
    rw [(extChartAt I α).left_inv hr]
    rfl
  exact (hf.comp t hu).congr_of_eventuallyEq heq.symm

end CurveSection

section Chart

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  (g : SmoothRiemannianMetric I N) (e : PartialDiffeomorph CI I SpatialNeckCylinder N ∞)
  (he : ∀ y ∈ e.source, ∀ v w : TangentSpace CI y,
    g.inner (e y) (mfderiv CI I e y v) (mfderiv CI I e y w) =
      sphericalProductModelMetric.inner y v w)

include he in
theorem ricciTensor_chart {y : SpatialNeckCylinder} (hy : y ∈ e.source)
    (a b : TangentSpace CI y) :
    ricciTensor g (e y) (mfderiv CI I e y a) (mfderiv CI I e y b) = (gS).inner y.1 a.1 b.1 := by
  let O : TopologicalSpace.Opens SpatialNeckCylinder := ⟨e.source, e.open_source⟩
  let Phi : O → N := fun z => e z
  have hPhi : IsLocalDiffeomorph CI I ∞ Phi :=
    isLocalDiffeomorph_restrict_open O (fun z => ⟨e, z.2, Set.eqOn_refl _ _⟩)
  have hd : ∀ z : O, mfderiv CI I Phi z = mfderiv CI I e z := fun z =>
    DifferentialGeometry.mfderiv_restrict_open _ O z
  have hpull : localPullMetric g Phi hPhi = sphericalProductModelMetric.restrictOpen O := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner, hd]
    exact he z z.2 v w
  have h1 := ricciTensor_localPull g Phi hPhi ⟨y, hy⟩ a b
  have h2 := CheegerGromovCompactness.ricciTensor_restrictOpen sphericalProductModelMetric O
    ⟨y, hy⟩ a b
  have h3 : ∀ c : TangentSpace CI y,
      mfderiv CI CI (Subtype.val : O → SpatialNeckCylinder) ⟨y, hy⟩ c = c := fun c =>
    DifferentialGeometry.mfderiv_subtype_val_apply O ⟨y, hy⟩ c
  rw [hpull] at h1
  calc ricciTensor g (e y) (mfderiv CI I e y a) (mfderiv CI I e y b)
      = ricciTensor g (Phi ⟨y, hy⟩) (mfderiv CI I Phi ⟨y, hy⟩ a)
          (mfderiv CI I Phi ⟨y, hy⟩ b) := by rw [hd]; rfl
    _ = ricciTensor sphericalProductModelMetric y
          (mfderiv CI CI (Subtype.val : O → SpatialNeckCylinder) ⟨y, hy⟩ a)
          (mfderiv CI CI (Subtype.val : O → SpatialNeckCylinder) ⟨y, hy⟩ b) := h1.symm.trans h2
    _ = ricciTensor sphericalProductModelMetric y a b := by rw [h3, h3]
    _ = (gS).inner y.1 a.1 b.1 := ricciTensor_sphericalProductModelMetric y a b

include he in
theorem ker_ricciSharp_chart {y : SpatialNeckCylinder} (hy : y ∈ e.source) :
    (ricciSharp g (e y)).ker = ℝ ∙ (mfderiv CI I e y (verticalField y)) := by
  have hloc : IsLocalDiffeomorphAt CI I ∞ e y := ⟨e, hy, Set.eqOn_refl _ _⟩
  let D := hloc.mfderivToContinuousLinearEquiv (by simp)
  have hD : ∀ a, D a = mfderiv CI I e y a := fun a => rfl
  have hvert : ricciSharp g (e y) (D (verticalField y)) = 0 := by
    set u := ricciSharp g (e y) (D (verticalField y))
    have hu : g.inner (e y) u u = 0 := by
      rw [inner_ricciSharp]
      have hw : u = D (D.symm u) := (D.apply_symm_apply u).symm
      conv_lhs => rw [hw]
      rw [hD, hD, ricciTensor_chart g e he hy]
      change (gS).inner y.1 (0 : E2) _ = 0
      have h0 := map_zero ((gS).inner y.1)
      exact congrArg (fun L : TangentSpace (𝓡 2) y.1 →L[ℝ] ℝ => L _) h0
    by_contra hne
    exact (g.pos (e y) u hne).ne' hu
  ext v
  rw [Submodule.mem_span_singleton]
  change ricciSharp g (e y) v = 0 ↔ _
  constructor
  · intro hv
    let a := D.symm v
    have hva : v = D a := (D.apply_symm_apply v).symm
    have hR : ricciTensor g (e y) v v = 0 := by
      rw [← inner_ricciSharp]
      rw [hv, map_zero]
      rfl
    rw [hva, hD, ricciTensor_chart g e he hy] at hR
    have ha1 : a.1 = 0 := by
      by_contra hne
      exact ((gS).pos y.1 a.1 hne).ne' hR
    refine ⟨a.2, ?_⟩
    rw [hva, ← hD, ← map_smul]
    congr 1
    refine Prod.ext ?_ ?_
    · change a.2 • (0 : E2) = a.1
      rw [smul_zero, ha1]
    · change a.2 * 1 = a.2
      ring
  · rintro ⟨c, rfl⟩
    rw [map_smul, ← hD, hvert, smul_zero]

include he in
theorem finrank_ker_ricciSharp_chart {y : SpatialNeckCylinder} (hy : y ∈ e.source) :
    Module.finrank ℝ (ricciSharp g (e y)).ker = 1 := by
  rw [ker_ricciSharp_chart g e he hy]
  apply finrank_span_singleton
  have hloc : IsLocalDiffeomorphAt CI I ∞ e y := ⟨e, hy, Set.eqOn_refl _ _⟩
  let D := hloc.mfderivToContinuousLinearEquiv (by simp)
  intro h0
  have h1 : D (verticalField y) = D 0 := by
    rw [map_zero]
    exact h0
  have h2 := congrArg Prod.snd (D.injective h1)
  change (1 : ℝ) = 0 at h2
  exact one_ne_zero h2

def chartVertical (p : N) : TangentSpace I p :=
  mfderiv CI I e (e.symm p) (verticalField (e.symm p))

include he in
theorem ker_ricciSharp_eq_span_chartVertical {p : N} (hp : p ∈ e.target) :
    (ricciSharp g p).ker = ℝ ∙ chartVertical e p := by
  have h := ker_ricciSharp_chart g e he (e.map_target hp)
  have hp' : (e : SpatialNeckCylinder → N) ((e.symm : N → SpatialNeckCylinder) p) = p :=
    e.right_inv hp
  change (ricciSharp g (e (e.symm p))).ker =
    ℝ ∙ (chartVertical e p : TangentSpace I (e (e.symm p))) at h
  rw [hp'] at h
  exact h

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] [T2Space N] in
theorem chartVertical_ne_zero {p : N} (hp : p ∈ e.target) : chartVertical e p ≠ 0 := by
  have hy : e.symm p ∈ e.source := e.map_target hp
  have hloc : IsLocalDiffeomorphAt CI I ∞ e (e.symm p) := ⟨e, hy, Set.eqOn_refl _ _⟩
  let D := hloc.mfderivToContinuousLinearEquiv (by simp)
  intro h0
  have h1 : D (verticalField (e.symm p)) = D 0 := by
    rw [map_zero]
    exact h0
  have h2 := congrArg Prod.snd (D.injective h1)
  change (1 : ℝ) = 0 at h2
  exact one_ne_zero h2

end Chart

section Line

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  (g : SmoothRiemannianMetric I N)
  (hA : GC.Geometry.ModelAtlas g sphericalProductModelMetric)

include hA in
theorem finrank_ker_ricciSharp_of_modelAtlas (x : N) :
    Module.finrank ℝ (ricciSharp g x).ker = 1 := by
  obtain ⟨e, hx, he⟩ := hA x
  rw [ker_ricciSharp_eq_span_chartVertical g e he hx]
  exact finrank_span_singleton (chartVertical_ne_zero e hx)

def ricciLine : ContMDiffVectorSubbundle (I := I) (F := E)
    (V := (TangentSpace I : N → Type _)) (n := (∞ : WithTop ℕ∞)) :=
  ContMDiffVectorSubbundle.kernel (fun x => ricciSharp g x) (ricciSharp_contMDiff g) 1
    (finrank_ker_ricciSharp_of_modelAtlas g hA)

section Parallel

attribute [local instance] DifferentialGeometry.seminormedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedSpaceTangentSpace

theorem chartVertical_parallel_along [NeZero (Module.finrank ℝ E)]
    {e : PartialDiffeomorph CI I SpatialNeckCylinder N ∞}
    (he : ∀ y ∈ e.source, ∀ v w : TangentSpace CI y,
      g.inner (e y) (mfderiv CI I e y v) (mfderiv CI I e y w) =
        sphericalProductModelMetric.inner y v w)
    (δ : ℝ → N) (hδ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) δ) {z : ℝ} (hz : δ z ∈ e.target) :
    DifferentiableAt ℝ (chartRepAt (I := I) δ (fun s => chartVertical e (δ s)) z) z ∧
      covDerivAlong (I := I) g δ (fun s => chartVertical e (δ s)) z = 0 := by
  let c : ℝ → SpatialNeckCylinder := fun s => e.symm (δ s)
  have hcz : c z ∈ e.source := e.map_target hz
  have hsymm : ContMDiffAt I CI ∞ e.symm (δ z) :=
    e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds hz)
  have hc1 : ContMDiffAt 𝓘(ℝ, ℝ) CI 1 c z :=
    (hsymm.of_le (by norm_num)).comp z ((hδ z).of_le (by norm_num))
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) CI c z := hc1.mdifferentiableAt (by norm_num)
  let Vc : ∀ s, TangentSpace CI (c s) := fun s => verticalField (c s)
  have hVc : DifferentiableAt ℝ (chartRepAt (I := CI) c Vc z) z :=
    chartRepAt_section_differentiableAt c hc (fun y => verticalField y)
      verticalField.mdifferentiableAt
  have hev : ∀ᶠ s in 𝓝 z, δ s ∈ e.target :=
    (hδ.continuous.continuousAt).preimage_mem_nhds (e.open_target.mem_nhds hz)
  have hcurve : (fun s => e (c s)) =ᶠ[𝓝 z] δ := by
    filter_upwards [hev] with s hs
    exact e.right_inv hs
  have hfield : ∀ᶠ s in 𝓝 z, (mfderiv CI I e (c s) (Vc s) : E) =
      (chartVertical e (δ s) : E) := Eventually.of_forall fun s => rfl
  refine ⟨?_, ?_⟩
  · have hpush :=
      Riemannian.CovariantDerivativeAlong.differentiableAt_chartRepAt_partialDiffeomorph_comp
        e c Vc hcz hc hVc
    exact ((Riemannian.chartRep_congr_curve (I := I) _ _ hcurve
      hfield).differentiableAt_iff).mp hpush
  · have hnat := Riemannian.CovariantDerivativeAlong.mfderiv_covDerivAlong_partialDiffeomorph
      sphericalProductModelMetric g e he c Vc hcz hc hVc
    have hmodel : covDerivAlong (I := CI) sphericalProductModelMetric c Vc z = 0 := by
      rw [covDerivAlong_eq_leviCivita_of_eventuallyEq sphericalProductModelMetric c z hc1
        verticalField.mdifferentiableAt (Eventually.of_forall fun s => rfl)]
      exact leviCivita_verticalField _ _
    rw [hmodel, map_zero] at hnat
    have hcongr := Riemannian.covDerivAlong_congr_curve (I := I) g
      (fun s => mfderiv CI I e (c s) (Vc s)) (fun s => chartVertical e (δ s)) hcurve hfield
    rw [← hnat] at hcongr
    exact hcongr.symm

include hA in
theorem isParallelSubmoduleFamily_ricciLine [NeZero (Module.finrank ℝ E)] :
    IsParallelSubmoduleFamily g (ricciLine g hA).fiber := by
  let S := ricciLine g hA
  have hSfib : ∀ x : N, S.fiber x = (ricciSharp g x).ker := fun x => rfl
  intro γ hγ a b hab
  let δ : ℝ → N := fun r => γ (r + a)
  have hδ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) δ :=
    hγ.comp (contMDiff_id.add contMDiff_const)
  let L : ℝ := b - a
  have hL : 0 < L := sub_pos.mpr hab
  have hpreserves (v : TangentSpace I (δ 0)) (hv : v ∈ S.fiber (δ 0)) :
      Riemannian.Variation.parallelTransportLinearEquivOnIcc (I := I) g δ hδ hL v ∈
        S.fiber (δ L) := by
    let V : ∀ r, TangentSpace I (δ r) :=
      Riemannian.Variation.parallelTransportSectionOnIcc (I := I) g δ hδ hL v
    have hVdiff : ∀ r ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) δ V r) r := fun r hr =>
      Riemannian.Variation.parallelTransportSectionOnIcc_differentiableAt
        (I := I) g δ hδ hL v hr
    have hVpar : ∀ r ∈ Set.Icc (0 : ℝ) L, covDerivAlong (I := I) g δ V r = 0 := fun r hr =>
      Riemannian.Variation.parallelTransportSectionOnIcc_covDerivAlong (I := I) g δ hδ hL v hr
    let P : Set.Icc (0 : ℝ) L → Prop := fun r => V r ∈ S.fiber (δ r)
    let : PreconnectedSpace (Set.Icc (0 : ℝ) L) :=
      Subtype.preconnectedSpace isPreconnected_Icc
    have hlocal : ∀ r : Set.Icc (0 : ℝ) L,
        ∀ᶠ q in 𝓝 r, (P r ↔ P q) ∧ (P q ↔ P r) := by
      intro r
      obtain ⟨e, hre, he⟩ := hA (δ r)
      have hpre : δ ⁻¹' e.target ∈ 𝓝 (r : ℝ) :=
        (e.open_target.preimage hδ.continuous).mem_nhds hre
      obtain ⟨l, u, hrlu, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hpre
      have hnhd : ((fun q : Set.Icc (0 : ℝ) L => (q : ℝ)) ⁻¹' Set.Ioo l u) ∈ 𝓝 r :=
        (isOpen_Ioo.preimage continuous_subtype_val).mem_nhds hrlu
      filter_upwards [hnhd] with q hq
      have hsegment : ∀ z ∈ Set.Icc (min (r : ℝ) (q : ℝ)) (max (r : ℝ) (q : ℝ)),
          δ z ∈ e.target := by
        intro z hz
        apply hlu
        exact ⟨(lt_min hrlu.1 hq.1).trans_le hz.1, hz.2.trans_lt (max_lt hrlu.2 hq.2)⟩
      have himp : ∀ (r₀ r₁ : Set.Icc (0 : ℝ) L),
          (∀ z ∈ Set.Icc (min (r₀ : ℝ) (r₁ : ℝ)) (max (r₀ : ℝ) (r₁ : ℝ)),
            δ z ∈ e.target) → P r₀ → P r₁ := by
        intro r₀ r₁ hseg hr₀
        have hr₀U : δ r₀ ∈ e.target := hseg r₀ ⟨min_le_left _ _, le_max_left _ _⟩
        have hr₁U : δ r₁ ∈ e.target := hseg r₁ ⟨min_le_right _ _, le_max_right _ _⟩
        have hspan : S.fiber (δ r₀) = ℝ ∙ chartVertical e (δ r₀) :=
          (hSfib _).trans (ker_ricciSharp_eq_span_chartVertical g e he hr₀U)
        change V r₀ ∈ S.fiber (δ r₀) at hr₀
        rw [hspan, Submodule.mem_span_singleton] at hr₀
        obtain ⟨c, hc⟩ := hr₀
        let W : ∀ z, TangentSpace I (δ z) := fun z => c • chartVertical e (δ z)
        have hWdiff : ∀ z ∈ Set.Icc (min (r₀ : ℝ) (r₁ : ℝ)) (max (r₀ : ℝ) (r₁ : ℝ)),
            DifferentiableAt ℝ (chartRepAt (I := I) δ W z) z := by
          intro z hz
          rw [show chartRepAt (I := I) δ W z =
            fun y => c • chartRepAt (I := I) δ (fun x => chartVertical e (δ x)) z y by
              simpa [W] using chartRepAt_smul (I := I) δ c (fun x => chartVertical e (δ x)) z]
          exact ((chartVertical_parallel_along g he δ hδ (hseg z hz)).1).const_smul c
        have hWpar : ∀ z ∈ Set.Icc (min (r₀ : ℝ) (r₁ : ℝ)) (max (r₀ : ℝ) (r₁ : ℝ)),
            covDerivAlong (I := I) g δ W z = 0 := by
          intro z hz
          rw [show W = fun y => c • chartVertical e (δ y) from rfl,
            covDerivAlong_smul (I := I) g δ c (fun y => chartVertical e (δ y)) z,
            (chartVertical_parallel_along g he δ hδ (hseg z hz)).2, smul_zero]
        have hseg_global : Set.Icc (min (r₀ : ℝ) (r₁ : ℝ)) (max (r₀ : ℝ) (r₁ : ℝ)) ⊆
            Set.Icc (0 : ℝ) L := by
          intro z hz
          exact ⟨(le_min r₀.2.1 r₁.2.1).trans hz.1, hz.2.trans (max_le r₀.2.2 r₁.2.2)⟩
        have hagree : V r₀ = W r₀ := hc.symm
        have hEq := Riemannian.Variation.parallel_transport_unique_of_eq_at_point
          (I := I) g δ le_rfl hδ V W
            (fun z hz => hVdiff z (hseg_global hz)) hWdiff
            (fun z hz => hVpar z (hseg_global hz)) hWpar
            (t₀ := (r₀ : ℝ)) ⟨min_le_left _ _, le_max_left _ _⟩ hagree
            (r₁ : ℝ) ⟨min_le_right _ _, le_max_right _ _⟩
        change V r₁ ∈ S.fiber (δ r₁)
        rw [hEq, hSfib, ker_ricciSharp_eq_span_chartVertical g e he hr₁U]
        exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
      have hrq : P r → P q := himp r q hsegment
      have hsegment' : ∀ z ∈ Set.Icc (min (q : ℝ) (r : ℝ)) (max (q : ℝ) (r : ℝ)),
          δ z ∈ e.target := by
        simpa [min_comm, max_comm] using hsegment
      have hqr : P q → P r := himp q r hsegment'
      exact ⟨⟨hrq, hqr⟩, ⟨hqr, hrq⟩⟩
    have hPall : ∀ r q : Set.Icc (0 : ℝ) L, P r ↔ P q := by
      intro r q
      exact PreconnectedSpace.induction₂' (fun x y => P x ↔ P y) hlocal
        ⟨fun x y z => Iff.trans⟩ r q
    have hPzero : P ⟨0, le_rfl, le_of_lt hL⟩ := by
      change V 0 ∈ S.fiber (δ 0)
      change Riemannian.Variation.parallelTransportSectionOnIcc (I := I) g δ hδ hL v 0 ∈
        S.fiber (δ 0)
      rw [Riemannian.Variation.parallelTransportSectionOnIcc_initial (I := I) g δ hδ hL]
      exact hv
    have hPL : P ⟨L, le_of_lt hL, le_rfl⟩ :=
      (hPall ⟨0, le_rfl, le_of_lt hL⟩ ⟨L, le_of_lt hL, le_rfl⟩).mp hPzero
    change V L ∈ S.fiber (δ L) at hPL
    simpa [V, Riemannian.Variation.parallelTransportLinearEquivOnIcc_apply] using hPL
  have hshiftMap :
      Submodule.map (Riemannian.Variation.parallelTransportLinearEquivOnIcc
        (I := I) g δ hδ hL).toLinearMap (S.fiber (δ 0)) = S.fiber (δ L) := by
    apply Submodule.eq_of_le_of_finrank_le
    · rintro w ⟨v, hv, rfl⟩
      exact hpreserves v hv
    · rw [← (Submodule.equivMapOfInjective
        (Riemannian.Variation.parallelTransportLinearEquivOnIcc (I := I) g δ hδ hL).toLinearMap
        (Riemannian.Variation.parallelTransportLinearEquivOnIcc (I := I) g δ hδ hL).injective
        (S.fiber (δ 0))).finrank_eq,
        S.finrank_fiber, S.finrank_fiber]
  dsimp only [δ, L] at hshiftMap
  rw [show (0 : ℝ) + a = a by ring, show (b - a) + a = b by ring] at hshiftMap
  unfold Riemannian.Variation.parallelTransportLinearEquivBetween
  exact hshiftMap

end Parallel

end Line

end GC.Geometry.SphericalProduct
