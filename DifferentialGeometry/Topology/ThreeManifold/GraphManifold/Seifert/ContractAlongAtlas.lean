import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ContractAlong

/-!
# Half-space atlases pulled back through local ambient charts

A half-space topological cover whose coordinates factor through a common ambient map
inherits smooth transitions from the ambient coordinate diffeomorphisms. The ambient map
may identify points in different patches; global injectivity is not required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Seifert
open scoped Manifold ContDiff Topology

namespace GC.Seifert.TorusPresentation

variable {E H M X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace X] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) {n : ℕ} [NeZero n]
  (c : ι → OpenPartialHomeomorph X (EuclideanHalfSpace n))
  (hcover : ∀ x : X, ∃ i, x ∈ (c i).source)

@[reducible]
def alongPullbackChartedSpace : ChartedSpace (EuclideanHalfSpace n) X where
  atlas := Set.range c
  chartAt x := c (hcover x).choose
  mem_chart_source x := (hcover x).choose_spec
  chart_mem_atlas x := Set.mem_range_self ((hcover x).choose)

theorem alongPullback_isManifold
    (a : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      M (EuclideanSpace ℝ (Fin n)) ∞)
    (f : X → M)
    (hsource : ∀ i x, x ∈ (c i).source → f x ∈ (a i).source)
    (hforward : ∀ i x, x ∈ (c i).source → (c i x).val = a i (f x))
    (htarget : ∀ i y, y ∈ (c i).target → y.val ∈ (a i).target)
    (hback : ∀ i y, y ∈ (c i).target → f ((c i).symm y) = (a i).symm y.val) :
    letI := alongPullbackChartedSpace c hcover
    IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ X := by
  let := alongPullbackChartedSpace c hcover
  apply isManifold_of_contDiffOn (modelWithCornersEuclideanHalfSpace n) ∞ X
  rintro e g ⟨i, rfl⟩ ⟨j, rfl⟩
  let ih := modelWithCornersEuclideanHalfSpace n
  have hmem (z : EuclideanSpace ℝ (Fin n))
      (hz : z ∈ ih.symm ⁻¹' ((c i).symm.trans (c j)).source ∩ Set.range ih) :
      z ∈ ((a i).symm.trans (a j)).source := by
    have hv : (ih.symm z).val = z := ih.right_inv hz.2
    refine ⟨?_, ?_⟩
    · change z ∈ (a i).target
      simpa only [hv] using htarget i (ih.symm z) hz.1.1
    · have hs := hsource j ((c i).symm (ih.symm z)) hz.1.2
      rw [hback i (ih.symm z) hz.1.1, hv] at hs
      exact hs
  have heq (z : EuclideanSpace ℝ (Fin n))
      (hz : z ∈ ih.symm ⁻¹' ((c i).symm.trans (c j)).source ∩ Set.range ih) :
      ih (((c i).symm.trans (c j)) (ih.symm z)) =
        ((a i).symm.trans (a j)) z := by
    have hv : (ih.symm z).val = z := ih.right_inv hz.2
    change (c j ((c i).symm (ih.symm z))).val = a j ((a i).symm z)
    rw [hforward j ((c i).symm (ih.symm z)) hz.1.2,
      hback i (ih.symm z) hz.1.1, hv]
  have hs := ((a i).symm.trans (a j)).contMDiffOn_toFun.contDiffOn
  exact (hs.mono hmem).congr heq

theorem alongPullback_contMDiff
    (a : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      M (EuclideanSpace ℝ (Fin n)) ∞)
    (f : X → M)
    (hsource : ∀ i x, x ∈ (c i).source → f x ∈ (a i).source)
    (hforward : ∀ i x, x ∈ (c i).source → (c i x).val = a i (f x))
    (htarget : ∀ i y, y ∈ (c i).target → y.val ∈ (a i).target)
    (hback : ∀ i y, y ∈ (c i).target → f ((c i).symm y) = (a i).symm y.val) :
    letI := alongPullbackChartedSpace c hcover
    ContMDiff (modelWithCornersEuclideanHalfSpace n) I ∞ f := by
  let := alongPullbackChartedSpace c hcover
  let := alongPullback_isManifold I c hcover a f hsource hforward htarget hback
  intro x
  let i := (hcover x).choose
  have hx : x ∈ (c i).source := (hcover x).choose_spec
  have hext : extChartAt (modelWithCornersEuclideanHalfSpace n) x x = a i (f x) :=
    hforward i x hx
  have hinv := (a i).contMDiffOn_invFun.contMDiffAt
    ((a i).open_target.mem_nhds ((a i).map_source (hsource i x hx)))
  rw [← hext] at hinv
  have hcomp := hinv.comp x
    (contMDiffAt_extChartAt (I := modelWithCornersEuclideanHalfSpace n) (n := ∞) (x := x))
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(c i).open_source.mem_nhds hx] with y hy
  change f y = (a i).symm (c i y).val
  rw [hforward i y hy]
  exact ((a i).left_inv (hsource i y hy)).symm

theorem alongPullback_mfderiv_bijective
    (a : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      M (EuclideanSpace ℝ (Fin n)) ∞)
    (f : X → M)
    (hsource : ∀ i x, x ∈ (c i).source → f x ∈ (a i).source)
    (hforward : ∀ i x, x ∈ (c i).source → (c i x).val = a i (f x))
    (htarget : ∀ i y, y ∈ (c i).target → y.val ∈ (a i).target)
    (hback : ∀ i y, y ∈ (c i).target → f ((c i).symm y) = (a i).symm y.val)
    (x : X) :
    letI := alongPullbackChartedSpace c hcover
    Function.Bijective (mfderiv (modelWithCornersEuclideanHalfSpace n) I f x) := by
  let := alongPullbackChartedSpace c hcover
  let := alongPullback_isManifold I c hcover a f hsource hforward htarget hback
  let ih := modelWithCornersEuclideanHalfSpace n
  let ie := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let i := (hcover x).choose
  have hx : x ∈ (c i).source := (hcover x).choose_spec
  have ha : MDifferentiableAt I ie (a i) (f x) :=
    ((a i).contMDiffOn.contMDiffAt
      ((a i).open_source.mem_nhds (hsource i x hx))).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt ih I f x :=
    (alongPullback_contMDiff I c hcover a f hsource hforward htarget hback).mdifferentiableAt
      (by simp)
  have heq : ((a i) ∘ f) =ᶠ[𝓝 x] extChartAt ih x := by
    filter_upwards [(c i).open_source.mem_nhds hx] with y hy
    exact (hforward i y hy).symm
  have hcomp : (mfderiv I ie (a i) (f x)).comp (mfderiv ih I f x) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← mfderiv_comp x ha hf, heq.mfderiv_eq, mfderiv_extChartAt_self]
    rfl
  have hloc := (a i).isLocalDiffeomorphAt I ie ∞ (hsource i x hx)
  have hbij : Function.Bijective (mfderiv I ie (a i) (f x)) := by
    rw [← hloc.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (hloc.mfderivToContinuousLinearEquiv (by simp)).bijective
  constructor
  · intro v w hvw
    have hv := congrArg (fun L => L v) hcomp
    have hw := congrArg (fun L => L w) hcomp
    change mfderiv I ie (a i) (f x) (mfderiv ih I f x v) = v at hv
    change mfderiv I ie (a i) (f x) (mfderiv ih I f x w) = w at hw
    rw [hvw] at hv
    exact hv.symm.trans hw
  · intro v
    refine ⟨mfderiv I ie (a i) (f x) v, hbij.injective ?_⟩
    exact congrArg (fun L => L (mfderiv I ie (a i) (f x) v)) hcomp

theorem alongPullback_isBoundaryPoint_iff (x : X) :
    letI := alongPullbackChartedSpace c hcover
    (modelWithCornersEuclideanHalfSpace n).IsBoundaryPoint x ↔
      (c (hcover x).choose x).val 0 = 0 := by
  let := alongPullbackChartedSpace c hcover
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace]
  exact eq_comm

theorem alongPullback_target_of_forward
    (a : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      M (EuclideanSpace ℝ (Fin n)) ∞)
    (f : X → M)
    (hsource : ∀ i x, x ∈ (c i).source → f x ∈ (a i).source)
    (hforward : ∀ i x, x ∈ (c i).source → (c i x).val = a i (f x))
    (i : ι) (y : EuclideanHalfSpace n) (hy : y ∈ (c i).target) :
    y.val ∈ (a i).target := by
  have hx := (c i).map_target hy
  have he := hforward i ((c i).symm y) hx
  rw [(c i).right_inv hy] at he
  exact he ▸ (a i).map_source (hsource i ((c i).symm y) hx)

theorem alongPullback_back_of_forward
    (a : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      M (EuclideanSpace ℝ (Fin n)) ∞)
    (f : X → M)
    (hsource : ∀ i x, x ∈ (c i).source → f x ∈ (a i).source)
    (hforward : ∀ i x, x ∈ (c i).source → (c i x).val = a i (f x))
    (i : ι) (y : EuclideanHalfSpace n) (hy : y ∈ (c i).target) :
    f ((c i).symm y) = (a i).symm y.val := by
  have hx := (c i).map_target hy
  have he := hforward i ((c i).symm y) hx
  rw [(c i).right_inv hy] at he
  exact ((congrArg (a i).symm he).trans
    ((a i).left_inv (hsource i ((c i).symm y) hx))).symm

private theorem alongFinrank_signedCollar :
    Module.finrank ℝ ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ) = 2 + 1 := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]

private theorem alongMfderiv_snd_ne_zero (p : Torus × ℝ) :
    mfderiv signedCollarModel 𝓘(ℝ, ℝ) (Prod.snd : Torus × ℝ → ℝ)
      p ≠ 0 := by
  rw [mfderiv_snd]
  intro h
  have he := congrArg (fun L => L ((0 : EuclideanSpace ℝ (Fin 1) ×
    EuclideanSpace ℝ (Fin 1)), (1 : ℝ))) h
  change (1 : ℝ) = 0 at he
  exact one_ne_zero he

universe u

theorem exists_along_seam_chart {W : CompactCarrier.{u}}
    (T : GC.Seifert.TorusPresentation W) (k : Fin T.pairing.count) {x : W.Carrier}
    (hx : x ∈ (T.seam k).target) (positive : Bool) :
    ∃ φ : PartialDiffeomorph W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      W.Carrier (EuclideanSpace ℝ (Fin 3)) ∞,
      x ∈ φ.source ∧ φ.source ⊆ (T.seam k).target ∧
        ∀ y ∈ φ.source, φ y 0 =
          if positive then ((T.seam k).symm y).2 else -((T.seam k).symm y).2 := by
  have hchart (f : Torus × ℝ → ℝ)
      (hf : ContMDiff signedCollarModel 𝓘(ℝ, ℝ) ∞ f)
      (hreg : ∀ p, mfderiv signedCollarModel 𝓘(ℝ, ℝ) f p ≠ 0) :
      ∃ φ : PartialDiffeomorph W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        W.Carrier (EuclideanSpace ℝ (Fin 3)) ∞,
        x ∈ φ.source ∧ φ.source ⊆ (T.seam k).target ∧
          ∀ y ∈ φ.source, φ y 0 = -f ((T.seam k).symm y) := by
    obtain ⟨ψ, hψ, hψf⟩ := SmoothBoundaryAtlas.exists_partialDiffeomorph_coord_eq_sub
      signedCollarModel alongFinrank_signedCollar hf
      (hreg ((T.seam k).symm x)) 0
    refine ⟨(T.seam k).symm.trans ψ, ⟨hx, hψ⟩, fun y hy => hy.1, fun y hy => ?_⟩
    have hh := hψf ((T.seam k).symm y) hy.2
    rw [zero_sub] at hh
    exact hh
  cases positive
  · simpa using hchart Prod.snd contMDiff_snd alongMfderiv_snd_ne_zero
  · have hreg (p : Torus × ℝ) :
        mfderiv signedCollarModel 𝓘(ℝ, ℝ) (-Prod.snd) p ≠ 0 := by
      rw [mfderiv_neg]
      exact neg_ne_zero.mpr (alongMfderiv_snd_ne_zero p)
    simpa using hchart (-Prod.snd) contMDiff_snd.neg hreg

def alongSeamHalfRange {W : CompactCarrier.{u}} (T : GC.Seifert.TorusPresentation W)
    (k : Fin T.pairing.count) (positive : Bool) : Set W.Carrier :=
  {y | y ∈ (T.seam k).target ∧
    0 ≤ if positive then ((T.seam k).symm y).2 else -((T.seam k).symm y).2}

def alongSeamHalfAtlas {W : CompactCarrier.{u}} (T : GC.Seifert.TorusPresentation W)
    (k : Fin T.pairing.count) (positive : Bool) :
    SmoothBoundaryAtlas W.model 3 (T.alongSeamHalfRange k positive) where
  ambientChart x := (T.exists_along_seam_chart k x.property.1 positive).choose
  mem_source x := (T.exists_along_seam_chart k x.property.1 positive).choose_spec.1
  mem_iff x y hy := by
    have hchart := (T.exists_along_seam_chart k x.property.1 positive).choose_spec
    rw [hchart.2.2 y hy]
    exact and_iff_right (hchart.2.1 hy)

theorem alongSeamHalfAtlas_isBoundaryPoint_iff {W : CompactCarrier.{u}}
    (T : GC.Seifert.TorusPresentation W) (k : Fin T.pairing.count) (positive : Bool)
    (x : T.alongSeamHalfRange k positive) :
    letI := (T.alongSeamHalfAtlas k positive).toChartedSpace
    (modelWithCornersEuclideanHalfSpace 3).IsBoundaryPoint x ↔
      ((T.seam k).symm x.val).2 = 0 := by
  rw [(T.alongSeamHalfAtlas k positive).isBoundaryPoint_iff]
  have hchart := (T.exists_along_seam_chart k x.property.1 positive).choose_spec
  change (T.exists_along_seam_chart k x.property.1 positive).choose x.val 0 = 0 ↔ _
  rw [hchart.2.2 x.val hchart.1]
  cases positive <;> simp

private theorem alongContinuous_halfSpaceOneLift : Continuous Manifold.halfSpaceOneLift := by
  have hs : Continuous (fun t : ℝ =>
      (⟨max 0 t, le_max_left 0 t⟩ : Set.Ici (0 : ℝ))) :=
    (continuous_const.max continuous_id).subtype_mk (fun t => le_max_left 0 t)
  exact (Manifold.halfSpaceOneHomeomorph.symm.continuous.comp hs).congr
    (fun t => (Manifold.halfSpaceOneLift_eq t).symm)

private theorem alongNeg_mem_signedCollarSource {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) : (p.1, -(p.2.val 0)) ∈ signedCollarSource := by
  have h1 : p.2.val 0 < 1 := hp
  have h0 : 0 ≤ p.2.val 0 := p.2.2
  exact ⟨by simp only; linarith, by simp only; linarith⟩

private theorem alongContMDiff_halfCollar_neg :
    ContMDiff halfCollarModel signedCollarModel ∞
      (fun q : Torus × EuclideanHalfSpace 1 => (q.1, -q.2.val 0)) :=
  contMDiff_fst.prodMk (Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd).neg

private theorem alongHalfSpaceOneLift_coord (h : EuclideanHalfSpace 1) :
    Manifold.halfSpaceOneLift (h.val 0) = h := by
  apply Subtype.ext
  ext i
  rw [Subsingleton.elim i 0]
  change max (h.val 0) 0 = h.val 0
  exact max_eq_left h.2

def alongLeftAmbientHomeomorph {W : CompactCarrier.{u}}
    (T : GC.Seifert.TorusPresentation W) (k : Fin T.pairing.count) :
    halfCollarSource ≃ₜ T.alongSeamHalfRange k false where
  toFun p := ⟨T.seam k (p.val.1, -(p.val.2.val 0)), by
    have hs := T.mem_seam_source k (alongNeg_mem_signedCollarSource p.property)
    refine ⟨(T.seam k).map_source hs, ?_⟩
    change 0 ≤ -((T.seam k).symm (T.seam k (p.val.1, -(p.val.2.val 0)))).2
    have he := congrArg (fun z : Torus × ℝ => 0 ≤ -z.2) ((T.seam k).left_inv hs)
    exact he.mpr (neg_nonneg.mpr (neg_nonpos.mpr p.val.2.property))⟩
  invFun y := ⟨T.leftCrossInv k y.val, T.leftCrossInv_mem k y.property.1⟩
  left_inv p := by
    apply Subtype.ext
    have hs := T.mem_seam_source k (alongNeg_mem_signedCollarSource p.property)
    change T.leftCrossInv k (T.seam k (p.val.1, -(p.val.2.val 0))) = p.val
    have he := congrArg (fun z : Torus × ℝ => (z.1, Manifold.halfSpaceOneLift (-z.2)))
      ((T.seam k).left_inv hs)
    exact he.trans (by simp only [neg_neg, alongHalfSpaceOneLift_coord])
  right_inv y := by
    apply Subtype.ext
    change T.seam k ((T.leftCrossInv k y.val).1,
      -((T.leftCrossInv k y.val).2.val 0)) = y.val
    have hn : 0 ≤ -((T.seam k).symm y.val).2 := y.property.2
    rw [leftCrossInv]
    change T.seam k (((T.seam k).symm y.val).1,
      -(max (-((T.seam k).symm y.val).2) 0)) = y.val
    rw [max_eq_left hn, neg_neg]
    exact (T.seam k).right_inv y.property.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc := (T.seam k).contMDiffOn.continuousOn.comp
      alongContMDiff_halfCollar_neg.continuous.continuousOn
      (fun p hp => T.mem_seam_source k (alongNeg_mem_signedCollarSource hp))
    exact hc.domRestrict
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hs : Continuous (fun y : T.alongSeamHalfRange k false =>
        (T.seam k).symm y.val) :=
      (T.seam k).contMDiffOn_invFun.continuousOn.comp_continuous
        continuous_subtype_val (fun y => y.property.1)
    exact (continuous_fst.comp hs).prodMk
      (alongContinuous_halfSpaceOneLift.comp (continuous_snd.comp hs).neg)

private theorem alongPos_mem_signedCollarSource (t : Torus) {a : ℝ}
    (h0 : 0 ≤ a) (h1 : a < 1) : (t, a) ∈ signedCollarSource :=
  ⟨lt_of_lt_of_le (by norm_num) h0, h1⟩

def alongRightAmbientHomeomorph {W : CompactCarrier.{u}}
    (T : GC.Seifert.TorusPresentation W) (k : Fin T.pairing.count) :
    halfCollarSource ≃ₜ T.alongSeamHalfRange k true where
  toFun p := ⟨T.seam k ((T.pairing.matching k).symm p.val.1, p.val.2.val 0), by
    have hs := T.mem_seam_source k
      (alongPos_mem_signedCollarSource ((T.pairing.matching k).symm p.val.1)
        p.val.2.property p.property)
    refine ⟨(T.seam k).map_source hs, ?_⟩
    change 0 ≤ ((T.seam k).symm
      (T.seam k ((T.pairing.matching k).symm p.val.1, p.val.2.val 0))).2
    have he := congrArg (fun z : Torus × ℝ => 0 ≤ z.2) ((T.seam k).left_inv hs)
    exact he.mpr p.val.2.property⟩
  invFun y := ⟨T.rightCrossInv k y.val, T.rightCrossInv_mem k y.property.1⟩
  left_inv p := by
    apply Subtype.ext
    have hs := T.mem_seam_source k
      (alongPos_mem_signedCollarSource ((T.pairing.matching k).symm p.val.1)
        p.val.2.property p.property)
    change T.rightCrossInv k
      (T.seam k ((T.pairing.matching k).symm p.val.1, p.val.2.val 0)) = p.val
    have he := congrArg (fun z : Torus × ℝ =>
      (T.pairing.matching k z.1, Manifold.halfSpaceOneLift z.2)) ((T.seam k).left_inv hs)
    exact he.trans (by simp only [Diffeomorph.apply_symm_apply, alongHalfSpaceOneLift_coord])
  right_inv y := by
    apply Subtype.ext
    change T.seam k ((T.pairing.matching k).symm ((T.rightCrossInv k y.val).1),
      (T.rightCrossInv k y.val).2.val 0) = y.val
    have hn : 0 ≤ ((T.seam k).symm y.val).2 := y.property.2
    rw [rightCrossInv, Diffeomorph.symm_apply_apply]
    change T.seam k (((T.seam k).symm y.val).1,
      max ((T.seam k).symm y.val).2 0) = y.val
    rw [max_eq_left hn]
    exact (T.seam k).right_inv y.property.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun p : Torus × EuclideanHalfSpace 1 =>
        ((T.pairing.matching k).symm p.1, p.2.val 0)) :=
      ((T.pairing.matching k).symm.contMDiff.continuous.comp continuous_fst).prodMk
        ((EuclideanSpace.proj 0).continuous.comp
          (continuous_subtype_val.comp continuous_snd))
    exact ((T.seam k).contMDiffOn.continuousOn.comp hc.continuousOn
      (fun p hp => T.mem_seam_source k
        (alongPos_mem_signedCollarSource ((T.pairing.matching k).symm p.1)
          p.2.property hp))).domRestrict
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hs : Continuous (fun y : T.alongSeamHalfRange k true => (T.seam k).symm y.val) :=
      (T.seam k).contMDiffOn_invFun.continuousOn.comp_continuous
        continuous_subtype_val (fun y => y.property.1)
    exact ((T.pairing.matching k).contMDiff.continuous.comp (continuous_fst.comp hs)).prodMk
      (alongContinuous_halfSpaceOneLift.comp (continuous_snd.comp hs))

theorem exists_along_positive_chart {W : CompactCarrier.{u}} {x : W.Carrier}
    (hx : W.model.IsInteriorPoint x) {U : Set W.Carrier} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ φ : PartialDiffeomorph W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      W.Carrier (EuclideanSpace ℝ (Fin 3)) ∞,
      x ∈ φ.source ∧ φ.source ⊆ U ∧ ∀ y ∈ φ.source, 0 < φ y 0 := by
  let d := DifferentialGeometry.Manifold.interiorChart W.model ∞ x
  let A := SmoothBoundaryAtlas.affineDiffeomorph
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3)))
    ((1 - d x 0) • EuclideanSpace.single 0 1)
  let ψ := d.trans A.toPartialDiffeomorph
  have hψx : ψ x 0 = 1 := by
    change (d x + (1 - d x 0) • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 3)) 0 = 1
    simp
  have hxd : x ∈ d.source := ⟨mem_chart_source _ x, (W.model.isInteriorPoint_iff).mp hx⟩
  have hxψ : x ∈ ψ.source := ⟨hxd, Set.mem_univ x⟩
  let V := (ψ.source ∩ ψ ⁻¹' {v : EuclideanSpace ℝ (Fin 3) | 0 < v 0}) ∩ U
  have hV : IsOpen V :=
    (ψ.contMDiffOn.continuousOn.isOpen_inter_preimage ψ.open_source
      (isOpen_lt continuous_const ((EuclideanSpace.proj 0).continuous))).inter hU
  let φ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict ψ V hV
  exact ⟨φ, ⟨hxψ, ⟨hxψ, by simp [hψx]⟩, hxU⟩,
    fun y hy => hy.2.2, fun y hy => hy.2.1.2⟩

def alongInteriorAtlas {W : CompactCarrier.{u}} (T : GC.Seifert.TorusPresentation W)
    (S : Finset (Fin T.components.count)) (K : Finset (Fin T.pairing.count))
    (hext : ∀ i, T.externalPiece i ∉ S) :
    SmoothBoundaryAtlas W.model 3 (T.alongInteriorRange S K) where
  ambientChart x := (exists_along_positive_chart
    (T.isInteriorPoint_of_mem_range S hext x.property.1.1)
    (T.isOpen_alongInteriorRange S K) x.property).choose
  mem_source x := (exists_along_positive_chart
    (T.isInteriorPoint_of_mem_range S hext x.property.1.1)
    (T.isOpen_alongInteriorRange S K) x.property).choose_spec.1
  mem_iff x y hy := by
    have hc := (exists_along_positive_chart
      (T.isInteriorPoint_of_mem_range S hext x.property.1.1)
      (T.isOpen_alongInteriorRange S K) x.property).choose_spec
    exact iff_of_true (hc.2.1 hy) (hc.2.2 y hy).le

theorem alongInteriorAtlas_isInteriorPoint {W : CompactCarrier.{u}}
    (T : GC.Seifert.TorusPresentation W)
    (S : Finset (Fin T.components.count)) (K : Finset (Fin T.pairing.count))
    (hext : ∀ i, T.externalPiece i ∉ S) (x : T.alongInteriorRange S K) :
    letI := (T.alongInteriorAtlas S K hext).toChartedSpace
    (modelWithCornersEuclideanHalfSpace 3).IsInteriorPoint x := by
  let := (T.alongInteriorAtlas S K hext).toChartedSpace
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint,
    (T.alongInteriorAtlas S K hext).isBoundaryPoint_iff]
  have hc := (exists_along_positive_chart
    (T.isInteriorPoint_of_mem_range S hext x.property.1.1)
    (T.isOpen_alongInteriorRange S K) x.property).choose_spec
  exact (hc.2.2 x.val hc.1).ne'

section LiftedCharts

variable {E H M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace X] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {n : ℕ} [NeZero n]
  (U : TopologicalSpace.Opens X) (L : Set M) (h : U ≃ₜ L)
  (C : SmoothBoundaryAtlas I n L) (q : U)

def alongLiftedChart : _root_.OpenPartialHomeomorph X (EuclideanHalfSpace n) :=
  (h.transOpenPartialHomeomorph (C.chart (h q))).lift_openEmbedding
    U.isOpen.isOpenEmbedding_subtypeVal

theorem alongLiftedChart_mem : (q : X) ∈ (alongLiftedChart U L h C q).source := by
  refine ⟨q, ?_, rfl⟩
  exact C.mem_source (h q)

variable (f : X → M) (hf : ∀ z : U, (h z).val = f z.val)

include hf in
theorem alongLiftedChart_source (x : X) (hx : x ∈ (alongLiftedChart U L h C q).source) :
    f x ∈ (C.ambientChart (h q)).source := by
  obtain ⟨z, hz, rfl⟩ := hx
  change (h z).val ∈ (C.ambientChart (h q)).source at hz
  rwa [hf z] at hz

include hf in
theorem alongLiftedChart_forward (x : X) (hx : x ∈ (alongLiftedChart U L h C q).source) :
    (alongLiftedChart U L h C q x).val = C.ambientChart (h q) (f x) := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [alongLiftedChart, _root_.OpenPartialHomeomorph.lift_openEmbedding_apply]
  change ((C.chart (h q)) (h z)).val = C.ambientChart (h q) (f z.val)
  have hh : ((C.chart (h q)) (h z)).val = C.ambientChart (h q) (h z).val :=
    OpenPartialHomeomorph.restrictSubtypes_apply
      (C.ambientChart (h q)).toOpenPartialHomeomorph L
      {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} (h q) (0 : EuclideanHalfSpace n)
      (C.mem_iff (h q)) (h z) hz
  exact hh.trans (congrArg (C.ambientChart (h q)) (hf z))

theorem alongLiftedChart_target (y : EuclideanHalfSpace n)
    (hy : y ∈ (alongLiftedChart U L h C q).target) :
    y.val ∈ (C.ambientChart (h q)).target := hy

include hf in
theorem alongLiftedChart_back (y : EuclideanHalfSpace n)
    (hy : y ∈ (alongLiftedChart U L h C q).target) :
    f ((alongLiftedChart U L h C q).symm y) = (C.ambientChart (h q)).symm y.val := by
  change f (h.symm ((C.chart (h q)).symm y)).val = _
  rw [← hf, h.apply_symm_apply]
  exact OpenPartialHomeomorph.restrictSubtypes_symm_apply
    (C.ambientChart (h q)).toOpenPartialHomeomorph L
    {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} (h q) (0 : EuclideanHalfSpace n)
    (C.mem_iff (h q)) y hy

end LiftedCharts

section MapsCriterion

variable {E H M Q ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace Q] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) {n : ℕ} [NeZero n]
  (c : ι → _root_.OpenPartialHomeomorph Q (EuclideanHalfSpace n))
  (hcover : ∀ x : Q, ∃ i, x ∈ (c i).source)
  (a : ι → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    M (EuclideanSpace ℝ (Fin n)) ∞)
  (f : Q → M)
  (hsource : ∀ i x, x ∈ (c i).source → f x ∈ (a i).source)
  (hforward : ∀ i x, x ∈ (c i).source → (c i x).val = a i (f x))
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N]

include hsource hforward in
theorem alongPullback_contMDiffWithinAt_of_comp (g : N → Q) (U : Set N) (x : N)
    (hcont : ContinuousWithinAt g U x)
    (hsmooth : ContMDiffWithinAt J I ∞ (f ∘ g) U x) :
    letI := alongPullbackChartedSpace c hcover
    ContMDiffWithinAt J (modelWithCornersEuclideanHalfSpace n) ∞ g U x := by
  let := alongPullbackChartedSpace c hcover
  let i := (hcover (g x)).choose
  have hm : g x ∈ (c i).source := (hcover (g x)).choose_spec
  rw [contMDiffWithinAt_iff_target]
  refine ⟨hcont, ?_⟩
  have ha : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (a i) (f (g x)) :=
    (a i).contMDiffOn_toFun.contMDiffAt ((a i).open_source.mem_nhds (hsource i (g x) hm))
  have hs := ha.comp_contMDiffWithinAt x hsmooth
  apply hs.congr_of_eventuallyEq
  · filter_upwards [hcont ((c i).open_source.mem_nhds hm)] with y hy
    change (c i (g y)).val = a i (f (g y))
    exact hforward i (g y) hy
  · change (c i (g x)).val = a i (f (g x))
    exact hforward i (g x) hm

include hsource hforward in
theorem alongPullback_contMDiffOn_of_comp (g : N → Q) (U : Set N)
    (hcont : ContinuousOn g U) (hsmooth : ContMDiffOn J I ∞ (f ∘ g) U) :
    letI := alongPullbackChartedSpace c hcover
    ContMDiffOn J (modelWithCornersEuclideanHalfSpace n) ∞ g U := by
  let := alongPullbackChartedSpace c hcover
  intro x hx
  exact alongPullback_contMDiffWithinAt_of_comp I c hcover a f hsource hforward g U x
    (hcont x hx) (hsmooth x hx)

end MapsCriterion

end GC.Seifert.TorusPresentation
