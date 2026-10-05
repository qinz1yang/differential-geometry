import DifferentialGeometry.Geometry.Exponential.Flat.EuclideanTorusQuotient
import DifferentialGeometry.Geometry.Thurston.Descent
import DifferentialGeometry.Geometry.Metric.DistancePullback

/-!
# The actual flat metric on the lattice torus

The original flat metric pulls back along the same finite torus covering. Genuine inverse
sheets pull back its Euclidean model charts. Every finite deck map preserves this metric,
and therefore its induced Riemannian distance, without a rectangular lattice assumption.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Geometry GC.GraphManifold.FlatTorus
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FlatSurface

private theorem modelAtlas_localPull
    {E F V H K L X Y Z : Type*}
    [instNE : NormedAddCommGroup E] [instSE : NormedSpace ℝ E] [instFE : FiniteDimensional ℝ E]
    [instNF : NormedAddCommGroup F] [instSF : NormedSpace ℝ F]
    [instNV : NormedAddCommGroup V] [instSV : NormedSpace ℝ V]
    [instTH : TopologicalSpace H] [instTK : TopologicalSpace K] [instTL : TopologicalSpace L]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
    {A : ModelWithCorners ℝ V L}
    [instTX : TopologicalSpace X]
    [instCX : ChartedSpace H X]
    [instMX : IsManifold I ∞ X]
    [instT2X : T2Space X]
    [instTY : TopologicalSpace Y] [instCY : ChartedSpace K Y] [instMY : IsManifold J ∞ Y]
    [instTZ : TopologicalSpace Z] [instCZ : ChartedSpace L Z] [instMZ : IsManifold A ∞ Z]
    (g : SmoothRiemannianMetric J Y) (h : SmoothRiemannianMetric A Z)
    (hg : ModelAtlas g h) (f : X → Y) (hf : IsLocalDiffeomorph I J ∞ f) :
    ModelAtlas (localPullMetric g f hf) h := by
  intro x
  obtain ⟨Φ, hxΦ, hΦ⟩ := hf x
  obtain ⟨e, hx, he⟩ := hg (f x)
  let d := e.trans Φ.symm
  refine ⟨d, ?_, ?_⟩
  · change x ∈ Φ.source ∩ Φ ⁻¹' e.target
    exact ⟨hxΦ, by change Φ x ∈ e.target; rw [← hΦ hxΦ]; exact hx⟩
  · intro y hy v w
    have hdy : d y ∈ Φ.source := Φ.symm.map_source hy.2
    have hfd : f (d y) = e y := by
      rw [hΦ hdy]
      exact Φ.right_inv hy.2
    have hloc : f ∘ d =ᶠ[𝓝 y] e := by
      filter_upwards [d.open_source.mem_nhds hy] with z hz
      change f (d z) = e z
      rw [hΦ (show d z ∈ Φ.source from Φ.symm.map_source hz.2)]
      exact Φ.right_inv hz.2
    have hd := d.mdifferentiableAt (by decide) hy
    have hder (u : TangentSpace A y) :
        mfderiv I J f (d y) (mfderiv A I d y u) = mfderiv A J e y u := by
      rw [← mfderiv_comp_apply y (hf.contMDiff.mdifferentiableAt (by decide)) hd]
      have hh := hloc.mfderiv_eq (I := A) (I' := J)
      simp only [Function.comp_apply] at hh
      exact congrArg (fun D => D u) hh
    rw [localPullMetric_inner, hder, hder, hfd]
    exact he y hy.1 v w

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => ((AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) × AddCircle (1 : ℝ))

variable (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3)) (b : Module.Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)

variable (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : GeometricStructure (𝓡 3) P.Carrier)
    (f : T3 → P.Carrier) (hl : IsLocalDiffeomorph addTripleModel (𝓡 3) ∞ f)

def torusFlatMetric : SmoothRiemannianMetric addTripleModel T3 :=
  localPullMetric g.metric f hl

theorem torusFlatMetric_atlas (hg : g.model = .euclidean) :
    ModelAtlas (torusFlatMetric P g f hl) euclideanModelMetric :=
  modelAtlas_localPull g.metric euclideanModelMetric
    (by have ha := g.atlas; rw [hg] at ha; exact ha) f hl

def torusFlatDeckDiffeomorph (γ : G ⧸ affineTranslationKernel G) :
    T3 ≃ₘ⟮addTripleModel, addTripleModel⟯ T3 where
  toEquiv := (finiteTorusDeckHom G b hb γ).toEquiv
  contMDiff_toFun := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective γ
    exact affineTorusHom_contMDiff G b hb a
  contMDiff_invFun := by
    have he : (finiteTorusDeckHom G b hb γ).symm = finiteTorusDeckHom G b hb γ⁻¹ :=
      (map_inv (finiteTorusDeckHom G b hb) γ).symm
    change ContMDiff addTripleModel addTripleModel ∞
      (fun z => (finiteTorusDeckHom G b hb γ).symm z)
    simp only [he]
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective γ⁻¹
    rw [← ha]
    exact affineTorusHom_contMDiff G b hb a

theorem torusFlatMetric_invariant
    (hdeck : ∀ γ : G ⧸ affineTranslationKernel G, ∀ z,
      f (finiteTorusDeckHom G b hb γ z) = f z) (γ : G ⧸ affineTranslationKernel G) :
    Diffeomorph.pullbackMetric (torusFlatMetric P g f hl)
      (torusFlatDeckDiffeomorph G b hb γ) = torusFlatMetric P g f hl := by
  apply pullbackMetric_localPullMetric_of_comp_eq
  exact funext (hdeck γ)

theorem torusFlatMetric_distance
    (hdeck : ∀ γ : G ⧸ affineTranslationKernel G, ∀ z,
      f (finiteTorusDeckHom G b hb γ z) = f z) (γ : G ⧸ affineTranslationKernel G) (x y : T3) :
    riemannianEDistOf
      (torusFlatMetric P g f hl)
      (finiteTorusDeckHom G b hb γ x) (finiteTorusDeckHom G b hb γ y) =
    riemannianEDistOf
      (torusFlatMetric P g f hl) x y := by
  have hd := DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross
    (torusFlatMetric P g f hl) (torusFlatDeckDiffeomorph G b hb γ) x y
  have hm : Diffeomorph.pullbackMetricCross (torusFlatMetric P g f hl)
      (torusFlatDeckDiffeomorph G b hb γ) = torusFlatMetric P g f hl := by
    rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    exact torusFlatMetric_invariant G b hb P g f hl hdeck γ
  rw [hm] at hd
  exact hd.symm

theorem exists_flatMetric_on_sameTorus
    (hg : g.model = .euclidean)
    (hf : Finite (G ⧸ affineTranslationKernel G))
    (hfree : ∀ a : G, a ≠ 1 → ∀ x : E3, (a : E3 ≃ᵃⁱ[ℝ] E3) x ≠ x) :
    letI _instCharts := finiteTorusDeckCharts G b hb hf hfree
    ∀ e : P.Carrier ≃ₘ⟮𝓡 3, addTripleModel⟯ finiteTorusDeckQuotient G b hb,
      let π : T3 → P.Carrier :=
        e.symm ∘ (fun z => (Quotient.mk'' z : finiteTorusDeckQuotient G b hb))
      ∃ k : SmoothRiemannianMetric addTripleModel T3,
        (∀ z : T3, ∀ v w : TangentSpace addTripleModel z,
          k.inner z v w = g.metric.inner (π z)
            (mfderiv addTripleModel (𝓡 3) π z v) (mfderiv addTripleModel (𝓡 3) π z w)) ∧
        ModelAtlas k euclideanModelMetric ∧
        (∀ γ : G ⧸ affineTranslationKernel G,
          Diffeomorph.pullbackMetric k (torusFlatDeckDiffeomorph G b hb γ) = k) ∧
        ∀ γ : G ⧸ affineTranslationKernel G, ∀ x y : T3,
          riemannianEDistOf k (finiteTorusDeckHom G b hb γ x)
            (finiteTorusDeckHom G b hb γ y) = riemannianEDistOf k x y := by
  let instCharts := finiteTorusDeckCharts G b hb hf hfree
  intro e
  let π : T3 → P.Carrier :=
    e.symm ∘ (fun z => (Quotient.mk'' z : finiteTorusDeckQuotient G b hb))
  have hπ : IsLocalDiffeomorph addTripleModel (𝓡 3) ∞ π := by
    intro z
    exact (finiteTorusDeck_quotient_localDiffeomorph G b hb hf hfree z).comp
      (𝓡 3) P.Carrier (e.symm.isLocalDiffeomorph _)
  have hdeck (γ : G ⧸ affineTranslationKernel G) (z : T3) :
      π (finiteTorusDeckHom G b hb γ z) = π z := by
    let instAction := finiteTorusDeckAction G b hb
    exact congrArg e.symm (MulAction.orbitRel.Quotient.quotient_smul_eq (g := γ) (a := z))
  exact ⟨torusFlatMetric P g π hπ,
    fun z v w => localPullMetric_inner g.metric π hπ z v w,
    torusFlatMetric_atlas P g π hπ hg,
    torusFlatMetric_invariant G b hb P g π hπ hdeck,
    torusFlatMetric_distance G b hb P g π hπ hdeck⟩

end DifferentialGeometry.Geometry.FlatSurface
