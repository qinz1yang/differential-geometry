import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryPreimage
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryBandUpperDistance
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspTorusDiameter
import DifferentialGeometry.Geometry.Collapse.Inhabitants.SmallBoundaryGeometry
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspBoundaryInst
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicScale

/-!
# CH12 C4: assembling `NearlyCuspidalBoundary` from cusp collars

* `CuspEmbedding.ofSlice_C4`: a cusp collar whose `boundary_preimage` field is *derived*
  (invariance of domain, `boundary_preimage_C4`) from `X ⊆ ∂W`.
* `NearlyCuspidalBoundary.ofCollars_C4`: `n > 0` disjoint collars covering `∂W`, with torus
  diameters `≤ D`, give a `NearlyCuspidalBoundary W g K (max δ (√(1+δ) D))`.
* `deepTorus_edist_C4`: the torus of the cusp at depth `S` (`deepCusp_CPA H S`) has diameter
  `≤ e^{-S/2} D₀`.
* Inhabitants: the actual double cusp.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Geometry.Collapse GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- A cusp collar, with `boundary_preimage` derived from `X ⊆ ∂W`. -/
def CuspEmbedding.ofSlice_C4 {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (cusp : HyperbolicCusp) (toFun : CuspHalfSpace → W.Carrier)
    (contMDiffOn : ContMDiffOn halfCollarModel W.model (K + 1) toFun cuspDomain)
    (isEmbedding : _root_.Topology.IsEmbedding (fun p : cuspDomain => toFun p))
    (immersion : ∀ p ∈ cuspDomain, Function.Injective (mfderiv halfCollarModel W.model toFun p))
    (boundary_image : Set.range (fun t : Torus => toFun (t, halfZero)) = X)
    (hX : X ⊆ W.model.boundary W.Carrier)
    (metric_error : cuspMetricErrorBound g K δ cusp toFun) :
    CuspEmbedding W g K δ X where
  cusp := cusp
  toFun := toFun
  contMDiffOn := contMDiffOn
  isEmbedding := isEmbedding
  immersion := immersion
  boundary_image := boundary_image
  boundary_preimage := fun {_} hp => boundary_preimage_C4
    (contMDiffOn.continuousOn.mono le_rfl)
    (fun x hx y hy hxy => congrArg Subtype.val (isEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy))
    (fun t => hX (boundary_image ▸ ⟨t, rfl⟩)) hp
  metric_error := metric_error

/-- **Assembler.** `n > 0` pairwise disjoint cusp collars covering `∂W` whose reference tori have
diameter `≤ D` form a nearly cuspidal boundary of size `max δ (√(1+δ) D)`. -/
def NearlyCuspidalBoundary.ofCollars_C4 {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (n : ℕ) (hn : 0 < n) (X : Fin n → Set W.Carrier)
    (e : ∀ i, CuspEmbedding W g K δ (X i))
    (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hcover : ⋃ i, X i = W.model.boundary W.Carrier)
    (D : ℝ) (hD : 0 ≤ D) (hbound : ∀ i (x y : Torus),
      riemannianEDistOf (e i).cusp.torusMetric x y ≤ ENNReal.ofReal D) :
    NearlyCuspidalBoundary W g K (max δ (Real.sqrt (1 + δ) * D)) where
  count := n
  count_pos := hn
  component := X
  connected := fun i => by
    rw [← (e i).boundary_image]
    exact isConnected_range (by
      have hc : Continuous (fun t : Torus => ((t, halfZero) : CuspHalfSpace)) :=
        continuous_id.prodMk continuous_const
      exact ((e i).contMDiffOn.continuousOn.comp_continuous hc
        (fun t => by change (0 : ℝ) < 100; norm_num)))
  closed := fun i => by
    rw [← (e i).boundary_image]
    have hc : Continuous (fun t : Torus => ((t, halfZero) : CuspHalfSpace)) :=
      continuous_id.prodMk continuous_const
    exact (isCompact_range ((e i).contMDiffOn.continuousOn.comp_continuous hc
      (fun t => by change (0 : ℝ) < 100; norm_num))).isClosed
  disjoint := hdisj
  covers := hcover
  diameter := fun i x hx y hy => by
    rw [← (e i).boundary_image] at hx hy
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨t', rfl⟩ := hy
    have hp (v : Torus) : ((v, halfZero) : CuspHalfSpace) ∈ cuspDomain := by
      change (0 : ℝ) < 100; norm_num
    have hu := (e i).riemannianEDistOf_le_flat (hp t) (hp t')
    refine hu.trans (ENNReal.ofReal_le_ofReal ?_)
    have hδ : 0 ≤ δ := (e i).delta_nonneg
    have hreal := ENNReal.toReal_mono (by simp) (hbound i t t')
    have h0 : ((halfZero : EuclideanHalfSpace 1).val 0 - (halfZero : EuclideanHalfSpace 1).val 0) = 0 :=
      sub_self _
    have hd0 : 0 ≤ (riemannianEDistOf (e i).cusp.torusMetric t t').toReal := ENNReal.toReal_nonneg
    have hdD : (riemannianEDistOf (e i).cusp.torusMetric t t').toReal ≤ D := by
      have := ENNReal.toReal_mono (by simp) (hbound i t t')
      rwa [ENNReal.toReal_ofReal hD] at this
    refine le_trans ?_ (le_max_right _ _)
    change Real.sqrt (1 + δ) * Real.sqrt (((halfZero : EuclideanHalfSpace 1).val 0 -
      (halfZero : EuclideanHalfSpace 1).val 0) ^ 2 +
      (riemannianEDistOf (e i).cusp.torusMetric t t').toReal ^ 2) ≤ _
    rw [h0, zero_pow (by norm_num), zero_add, Real.sqrt_sq hd0]
    exact mul_le_mul_of_nonneg_left hdD (Real.sqrt_nonneg _)
  collar := fun i => (e i).weaken (le_max_left _ _)

/-- **Depth scaling of the torus diameter.** The reference torus of the depth-`S` cusp has
diameter `≤ e^{-S/2} D₀`. -/
theorem deepTorus_edist_C4 (H : HyperbolicCusp) (S D₀ : ℝ)
    (h : ∀ x y : Torus, riemannianEDistOf H.torusMetric x y ≤ ENNReal.ofReal D₀) (x y : Torus) :
    riemannianEDistOf (GC.LongTime.CuspP1.deepCusp_CPA H S).torusMetric x y ≤
      ENNReal.ofReal (Real.exp (-S / 2) * D₀) := by
  change riemannianEDistOf (scaleMetric (Real.exp (-S)) (Real.exp_pos _) H.torusMetric) x y ≤ _
  rw [edistOf_scale, ← Real.exp_half, ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_le_mul' le_rfl (h x y)

section Inhabitant

/-- Inhabitant of `ofSlice_C4`: the actual double cusp collars, with `boundary_preimage`
re-derived by invariance of domain rather than by the concrete computation. -/
def doubleCuspEmbeddingOfSlice_C4 (a : ℝ) (ha : 0 < a) (K : ℕ) (i : Fin 2) :
    CuspEmbedding annulusCircleCarrier.{u} (doubleCuspMetric.{u} a ha) K 0
      (doubleCuspBoundary.{u} i) :=
  CuspEmbedding.ofSlice_C4 (doubleCuspEmbedding.{u} a ha K i).cusp
    (doubleCuspEmbedding.{u} a ha K i).toFun (doubleCuspEmbedding.{u} a ha K i).contMDiffOn
    (doubleCuspEmbedding.{u} a ha K i).isEmbedding (doubleCuspEmbedding.{u} a ha K i).immersion
    (doubleCuspEmbedding.{u} a ha K i).boundary_image
    (fun _ hx => doubleCuspBoundary_cover.{u} ▸ mem_iUnion.mpr ⟨i, hx⟩)
    (doubleCuspEmbedding.{u} a ha K i).metric_error

/-- Inhabitant of `ofCollars_C4`: a two-component nearly cuspidal boundary. -/
def doubleCuspNCB_C4 (a : ℝ) (ha : 0 < a) (K : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ x y : Torus, riemannianEDistOf standardCuspTorusMetric x y ≤ ENNReal.ofReal D) :
    NearlyCuspidalBoundary annulusCircleCarrier.{u} (doubleCuspMetric.{u} a ha) K
      (max 0 (Real.sqrt (1 + 0) * (a * D))) :=
  NearlyCuspidalBoundary.ofCollars_C4 2 (by norm_num) doubleCuspBoundary.{u}
    (fun i => doubleCuspEmbeddingOfSlice_C4.{u} a ha K i) doubleCuspBoundary_disjoint
    doubleCuspBoundary_cover.{u} (a * D) (mul_nonneg ha.le hD) (fun i x y => by
      change riemannianEDistOf (doubleCuspEmbedding.{u} a ha K i).cusp.torusMetric x y ≤ _
      rw [doubleCuspEmbedding_torusMetric, edistOf_scale, Real.sqrt_sq ha.le,
        ENNReal.ofReal_mul ha.le]
      exact mul_le_mul' le_rfl (hbound x y))

theorem doubleCuspNCB_C4_count (a : ℝ) (ha : 0 < a) (K : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ x y : Torus, riemannianEDistOf standardCuspTorusMetric x y ≤ ENNReal.ofReal D) :
    (doubleCuspNCB_C4.{u} a ha K D hD hbound).count = 2 := rfl

/-- Unconditional non-trivial inhabitant of the thin boundary alternative. -/
theorem exists_doubleCuspNCB_C4 (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (a : ℝ) (ha : 0 < a) (B : NearlyCuspidalBoundary annulusCircleCarrier.{u}
        (doubleCuspMetric.{u} a ha) K δ), B.count = 2 := by
  obtain ⟨D, hD, hb⟩ := exists_standardCuspTorus_diameter_INST
  obtain ⟨a, ha, -, haD⟩ := exists_doubleCuspScale_INST hD hδ
  refine ⟨a, ha, (doubleCuspNCB_C4.{u} a ha K D hD.le hb).weaken ?_, rfl⟩
  rw [add_zero, Real.sqrt_one, one_mul]
  exact max_le hδ.le haD

end Inhabitant

end GC.LongTime.Ch12
