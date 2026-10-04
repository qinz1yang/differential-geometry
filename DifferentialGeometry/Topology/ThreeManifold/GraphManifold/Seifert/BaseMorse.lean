import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabUniqueness
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Topology.Manifold.ConnectedInterior
import DifferentialGeometry.Topology.Manifold.MFDeriv.Interior
import DifferentialGeometry.Topology.Manifold.BoundaryExtrema
import DifferentialGeometry.Topology.Morse.RegularLevel.Components
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Morse data on the base of a circle fibration

Lane MD1 of the P1 Morse-decomposition plan (`20261003-survey-p1-morse-decomposition.md`, §3).
A `BaseMorseData B` on a compact surface `B` is a smooth function `f ≥ 0` whose zero set is the
boundary of `B`, whose critical points form a finite set `crit` of nondegenerate critical points,
together with finitely many regular levels `level 0 < ⋯ < level m` such that every critical
point lies alone in the open slab between two consecutive levels, every extremum lies in a thin
slab whose component is the image of a closed Euclidean disc under a chart (`thin`), and a smooth
vector field `field` with `df (field) = 1` within `2 κ` of every level.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

structure BaseMorseData (B : CompactSurface.{u}) where
  f : B.Carrier → ℝ
  smooth : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f
  nonneg : ∀ x, 0 ≤ f x
  eq_zero_iff : ∀ x, f x = 0 ↔ (SurfaceModel.model B.kind).IsBoundaryPoint x
  crit : Finset B.Carrier
  mem_crit : ∀ x, x ∈ crit ↔ IsCriticalPointAt (SurfaceModel.model B.kind) f x
  nondegenerate : ∀ p ∈ crit, IsNondegenerateCriticalPointAt (SurfaceModel.model B.kind) f p
  m : ℕ
  level : Fin (m + 1) → ℝ
  level_strictMono : StrictMono level
  κ : ℝ
  κ_pos : 0 < κ
  two_κ_lt_level : 2 * κ < level 0
  lt_level_last : ∀ x, f x < level (Fin.last m)
  slab : ∀ p ∈ crit, ∃ i : Fin m, f p ∈ Ioo (level i.castSucc) (level i.succ) ∧
    ∀ q ∈ crit, f q ∈ Icc (level i.castSucc) (level i.succ) → q = p
  thin : ∀ p ∈ crit, sigNeg (chartHessianAt
      (fun y => f ((extChartAt (SurfaceModel.model B.kind) p).symm y))
      (extChartAt (SurfaceModel.model B.kind) p p)) ≠ 1 →
    ∀ i : Fin m, f p ∈ Ioo (level i.castSucc) (level i.succ) →
      ∃ (R : ℝ) (χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (SurfaceModel.model B.kind) (EuclideanSpace ℝ (Fin 2)) B.Carrier ∞),
        χ 0 = p ∧ closedBall 0 R ⊆ χ.source ∧
        χ '' closedBall 0 R = connectedComponentIn (f ⁻¹' Icc (level i.castSucc) (level i.succ)) p
  field : (x : B.Carrier) → TangentSpace (SurfaceModel.model B.kind) x
  field_smooth : ContMDiff (SurfaceModel.model B.kind) (SurfaceModel.model B.kind).tangent ∞
    fun x => (⟨x, field x⟩ : TangentBundle (SurfaceModel.model B.kind) B.Carrier)
  field_unit : ∀ (i : Fin (m + 1)) x, |f x - level i| < 2 * κ →
    mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f x (field x) = 1

section Superlevel

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem mfderiv_interiorChart_symm_ne_zero {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} (hx : I.IsInteriorPoint x)
    (hreg : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ)
      (fun z => f ((DifferentialGeometry.Manifold.interiorChart I ∞ x).symm z))
      (DifferentialGeometry.Manifold.interiorChart I ∞ x x) ≠ 0 := by
  set c := DifferentialGeometry.Manifold.interiorChart I ∞ x
  have hxc : x ∈ c.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  have hcx : c.symm (c x) = x := c.left_inv hxc
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I ∞ c.symm (c x) :=
    c.symm.isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I ∞ (c.map_source hxc)
  have hd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I c.symm (c x) :=
    hloc.mdifferentiableAt (by simp)
  have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (c.symm (c x)) := hf.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp (c x) hfd hd
  intro h
  apply hreg
  have h' : (mfderiv I 𝓘(ℝ, ℝ) f (c.symm (c x))).comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I c.symm (c x)) = 0 := hcomp.symm.trans h
  have hz : mfderiv I 𝓘(ℝ, ℝ) f (c.symm (c x)) = 0 := by
    ext v
    obtain ⟨w, hw⟩ := (hloc.mfderivToContinuousLinearEquiv (by simp)).surjective v
    have hw2 : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I c.symm (c x) w = v := hw
    have hw' := congrArg (fun L => L w) h'
    rw [← hw2]
    simpa using hw'
  rwa [hcx] at hz

private theorem exists_superlevelChart_of_eq {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) {x : M} (hx : I.IsInteriorPoint x) (hreg : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) M (EuclideanSpace ℝ (Fin 2)) ∞,
      x ∈ φ.source ∧ ∀ y ∈ φ.source, φ y 0 = f y - a := by
  set c := DifferentialGeometry.Manifold.interiorChart I ∞ x
  have hxc : x ∈ c.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  have hg : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞ (fun z => f (c.symm z))
      c.target := hf.comp_contMDiffOn c.symm.contMDiffOn
  have hcoord : ∃ Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 2))
      (ℝ × EuclideanSpace ℝ (Fin 1)) ∞,
      c x ∈ Φ.source ∧ ∀ z ∈ Φ.source, (Φ z).1 = f (c.symm z) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    obtain ⟨Φ, hΦx, -, hΦ⟩ :=
      DifferentialGeometry.Manifold.RegularLevel.exists_product_coordinates_of_contMDiffOn
        (m := 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) finrank_euclideanSpace_fin c.open_target hg
        (c.map_source hxc) (mfderiv_interiorChart_symm_ne_zero hf hx hreg)
    exact ⟨Φ, hΦx, hΦ⟩
  obtain ⟨Φ, hΦx, hΦ⟩ := hcoord
  let D := SmoothBoundaryAtlas.affineDiffeomorph (SmoothBoundaryAtlas.firstCoordinateEquiv 1)
    ((-a) • EuclideanSpace.single 0 1)
  refine ⟨(c.trans Φ).trans D.toPartialDiffeomorph, ⟨⟨hxc, hΦx⟩, mem_univ _⟩, fun y hy => ?_⟩
  change (SmoothBoundaryAtlas.firstCoordinateEquiv 1 (Φ (c y)) + (-a) • EuclideanSpace.single 0 1 :
    EuclideanSpace ℝ (Fin 2)) 0 = f y - a
  rw [PiLp.add_apply, SmoothBoundaryAtlas.firstCoordinateEquiv_apply_zero, hΦ (c y) hy.1.2,
    show f (c.symm.toPartialEquiv (c.toPartialEquiv y)) = f y from congrArg f (c.left_inv hy.1.1)]
  simp [sub_eq_add_neg]

private theorem exists_superlevelChart_of_lt {f : M → ℝ} (hf : Continuous f) {a : ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hax : a < f x) :
    ∃ φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) M (EuclideanSpace ℝ (Fin 2)) ∞,
      x ∈ φ.source ∧ ∀ y ∈ φ.source, a < f y ∧ 0 < φ y 0 := by
  set c := DifferentialGeometry.Manifold.interiorChart I ∞ x
  have hxc : x ∈ c.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  let e : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  let T := SmoothBoundaryAtlas.affineDiffeomorph
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))) (e - c x)
  let ψ := c.trans T.toPartialDiffeomorph
  have hψ (y : M) : ψ y = c y + (e - c x) := rfl
  let U : Set M := (ψ.source ∩ ψ ⁻¹' ball e 1) ∩ {y | a < f y}
  have hU : IsOpen U :=
    (ψ.contMDiffOn.continuousOn.isOpen_inter_preimage ψ.open_source isOpen_ball).inter
      (isOpen_lt continuous_const hf)
  have hψx : ψ x = e := by rw [hψ]; abel
  refine ⟨DifferentialGeometry.Topology.PartialDiffeomorph.restrict ψ U hU,
    ⟨⟨hxc, mem_univ _⟩, ⟨⟨hxc, mem_univ _⟩, by rw [mem_preimage, hψx]; exact mem_ball_self one_pos⟩,
      hax⟩, fun y hy => ⟨hy.2.2, ?_⟩⟩
  have hb : ψ y ∈ ball e 1 := hy.2.1.2
  rw [mem_ball, dist_eq_norm] at hb
  have h0 := (PiLp.norm_apply_le (ψ y - e) 0).trans_lt hb
  have he0 : e 0 = 1 := by simp [e]
  change 0 < ψ y 0
  rw [PiLp.sub_apply, he0, Real.norm_eq_abs] at h0
  linarith [neg_abs_le (ψ y 0 - 1)]

omit [IsManifold I ∞ M] in
private theorem exists_chart_ne_zero
    (φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) M (EuclideanSpace ℝ (Fin 2)) ∞)
    {x : M} (hx : x ∈ φ.source) :
    ∃ ψ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) M (EuclideanSpace ℝ (Fin 2)) ∞,
      x ∈ ψ.source ∧ ψ x ≠ 0 ∧ ∀ y ∈ ψ.source, y ∈ φ.source ∧ ψ y 0 = φ y 0 := by
  by_cases h : φ x = 0
  · let T := SmoothBoundaryAtlas.affineDiffeomorph
      (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)))
      (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2))
    refine ⟨φ.trans T.toPartialDiffeomorph, ⟨hx, mem_univ _⟩, ?_, fun y hy => ⟨hy.1, ?_⟩⟩
    · change φ x + EuclideanSpace.single 1 1 ≠ 0
      rw [h, zero_add]
      simp
    · change (φ y + EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2)) 0 = φ y 0
      simp
  · exact ⟨φ, hx, h, fun y hy => ⟨hy, rfl⟩⟩

private theorem exists_superlevelChart {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hint : ∀ x, a ≤ f x → I.IsInteriorPoint x)
    (hreg : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) (x : {x | a ≤ f x}) :
    ∃ φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) M (EuclideanSpace ℝ (Fin 2)) ∞,
      x.val ∈ φ.source ∧ (∀ y ∈ φ.source, y ∈ {x | a ≤ f x} ↔ 0 ≤ φ y 0) ∧
      (∀ y ∈ φ.source, φ y 0 = 0 ↔ f y = a) ∧ φ x.val ≠ 0 := by
  rcases eq_or_lt_of_le (show a ≤ f x from x.2) with hxa | hxa
  · obtain ⟨φ, hφx, hφ⟩ := exists_superlevelChart_of_eq hf a (hint x x.2) (hreg x hxa.symm)
    obtain ⟨ψ, hψx, hψ0, hψ⟩ := exists_chart_ne_zero φ hφx
    refine ⟨ψ, hψx, fun y hy => ?_, fun y hy => ?_, hψ0⟩
    · rw [(hψ y hy).2, hφ y (hψ y hy).1, sub_nonneg]
      rfl
    · rw [(hψ y hy).2, hφ y (hψ y hy).1, sub_eq_zero]
  · obtain ⟨φ, hφx, hφ⟩ := exists_superlevelChart_of_lt hf.continuous (hint x x.2) hxa
    refine ⟨φ, hφx, fun y hy => iff_of_true (hφ y hy).1.le (hφ y hy).2.le,
      fun y hy => iff_of_false (hφ y hy).2.ne' (hφ y hy).1.ne', fun h => ?_⟩
    have h0 := (hφ x hφx).2
    rw [h] at h0
    simp at h0

def superlevelAtlas {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hint : ∀ x, a ≤ f x → I.IsInteriorPoint x)
    (hreg : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    SmoothBoundaryAtlas I 2 {x | a ≤ f x} where
  ambientChart x := Classical.choose (exists_superlevelChart hf hint hreg x)
  mem_source x := (Classical.choose_spec (exists_superlevelChart hf hint hreg x)).1
  mem_iff x := (Classical.choose_spec (exists_superlevelChart hf hint hreg x)).2.1

theorem superlevelAtlas_isBoundaryPoint_iff {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hint : ∀ x, a ≤ f x → I.IsInteriorPoint x)
    (hreg : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) (x : {x | a ≤ f x}) :
    letI := (superlevelAtlas hf hint hreg).toChartedSpace
    (𝓡∂ 2).IsBoundaryPoint x ↔ f x = a := by
  rw [(superlevelAtlas hf hint hreg).isBoundaryPoint_iff]
  exact (Classical.choose_spec (exists_superlevelChart hf hint hreg x)).2.2.1 x.val
    (Classical.choose_spec (exists_superlevelChart hf hint hreg x)).1

private def interiorModelInverse (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) H) :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I (EuclideanSpace ℝ (Fin 2)) H ∞ where
  toFun := I.symm
  invFun := I
  source := interior (range I)
  target := I ⁻¹' interior (range I)
  map_source' v hv := by
    change I (I.symm v) ∈ interior (range I)
    rwa [I.right_inv (interior_subset hv)]
  map_target' _ hy := hy
  left_inv' _ hv := I.right_inv (interior_subset hv)
  right_inv' y _ := I.left_inv y
  open_source := isOpen_interior
  open_target := isOpen_interior.preimage I.continuous
  contMDiffOn_toFun := (I.contMDiffOn_symm (n := ∞)).mono interior_subset
  contMDiffOn_invFun := I.contMDiff.contMDiffOn

private theorem exists_mem_interior_range_ne_zero
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) H) :
    ∃ w ∈ interior (range I), w ≠ 0 := by
  obtain ⟨p, hp⟩ := I.nonempty_interior
  by_cases hp0 : p = 0
  · have h1 : ∀ᶠ y in 𝓝[≠] p, y ∈ interior (range I) :=
      nhdsWithin_le_nhds (isOpen_interior.mem_nhds hp)
    have h2 : ∀ᶠ y in 𝓝[≠] p, y ≠ p := self_mem_nhdsWithin
    obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
    exact ⟨y, hy1, hp0 ▸ hy2⟩
  · exact ⟨p, hp, hp0⟩

theorem isSmoothEmbedding_superlevelAtlas_val {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hint : ∀ x, a ≤ f x → I.IsInteriorPoint x)
    (hreg : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    letI := (superlevelAtlas hf hint hreg).toChartedSpace
    Manifold.IsSmoothEmbedding (𝓡∂ 2) I ∞ (Subtype.val : {x | a ≤ f x} → M) := by
  set C := superlevelAtlas hf hint hreg
  let _ := C.toChartedSpace
  let _ := C.isManifold
  refine ⟨Manifold.IsImmersionOfComplement.isImmersion (F := PUnit.{1}) ?_,
    _root_.Topology.IsEmbedding.subtypeVal⟩
  intro x
  let A := C.ambientChart x
  have hAx : A x.val ≠ 0 := (Classical.choose_spec (exists_superlevelChart hf hint hreg x)).2.2.2
  obtain ⟨w, hw, hw0⟩ := exists_mem_interior_range_ne_zero I
  obtain ⟨L, hL⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq (R := ℝ) hAx hw0
  let b := (A.trans L.toDiffeomorph.toPartialDiffeomorph).trans (interiorModelInverse I)
  have hbx : x.val ∈ b.source :=
    ⟨⟨C.mem_source x, mem_univ _⟩, show L (A x.val) ∈ interior (range I) by rw [hL]; exact hw⟩
  have hbmax : b.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas I ∞ M :=
    b.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      b.contMDiffOn_toFun b.contMDiffOn_invFun
  let s : Set {x | a ≤ f x} := Subtype.val ⁻¹' b.source
  have hs : IsOpen s := b.open_source.preimage continuous_subtype_val
  let d := (C.chart x).restr s
  have hdsource : d.source = (C.chart x).source ∩ s := by
    rw [OpenPartialHomeomorph.restr_source, hs.interior_eq]
  have hdmax : d ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ {x | a ≤ f x} :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ 2)) (IsManifold.chart_mem_maximalAtlas x) hs
  have hformula (y : {x | a ≤ f x}) (hy : y ∈ (C.chart x).source) (hyb : y.val ∈ b.source) :
      b.toOpenPartialHomeomorph.extend I y.val = L ((C.chart x).extend (𝓡∂ 2) y) := by
    change I (I.symm (L (A y.val))) = L ((C.chart x y).val)
    rw [I.right_inv (interior_subset (show L (A y.val) ∈ interior (range I) from hyb.2))]
    exact congrArg L (OpenPartialHomeomorph.restrictSubtypes_apply
      (C.ambientChart x).toOpenPartialHomeomorph {x | a ≤ f x}
      {v : EuclideanSpace ℝ (Fin 2) | 0 ≤ v 0} x (0 : EuclideanHalfSpace 2)
      (C.mem_iff x) y hy).symm
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    ((ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 2)) PUnit.{1}).trans L)
    d b.toOpenPartialHomeomorph (by rw [hdsource]; exact ⟨C.mem_source x, hbx⟩) hbx hdmax hbmax
    (fun y hy => by rw [hdsource] at hy; exact hy.2) ?_
  intro u hu
  let y := (d.extend (𝓡∂ 2)).symm u
  have hy : y ∈ d.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (d.extend (𝓡∂ 2)).map_target hu
  rw [hdsource] at hy
  change b.toOpenPartialHomeomorph.extend I y.val = L u
  rw [hformula y hy.1 hy.2]
  exact congrArg L ((d.extend (𝓡∂ 2)).right_inv hu)

private theorem isOpen_superlevelComponents {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {g : X → ℝ} (hg : Continuous g) (hgpos : ∀ y, 0 < g y) (p : X) :
    IsClopen {q | ∃ t, 0 < t ∧ q ∈ connectedComponentIn {z | t ≤ g z} p} := by
  set W := {q | ∃ t, 0 < t ∧ q ∈ connectedComponentIn {z | t ≤ g z} p}
  have hN (q : X) : IsOpen (connectedComponentIn {z | g q / 2 < g z} q) ∧
      q ∈ connectedComponentIn {z | g q / 2 < g z} q := by
    refine ⟨(isOpen_lt continuous_const hg).connectedComponentIn, mem_connectedComponentIn ?_⟩
    change g q / 2 < g q
    linarith [hgpos q]
  have hstep (q z : X) (hz : z ∈ connectedComponentIn {z | g q / 2 < g z} q) (t : ℝ)
      (ht : 0 < t) (hzt : z ∈ connectedComponentIn {z | t ≤ g z} p) :
      ∃ s, 0 < s ∧ q ∈ connectedComponentIn {z | s ≤ g z} p ∧
        connectedComponentIn {z | g q / 2 < g z} q ⊆ connectedComponentIn {z | s ≤ g z} p := by
    set s := min t (g q / 2)
    have hs : 0 < s := lt_min ht (half_pos (hgpos q))
    have hsub : connectedComponentIn {z | g q / 2 < g z} q ⊆ {z | s ≤ g z} := fun y hy =>
      show s ≤ g y from (min_le_right _ _).trans
        (show y ∈ {z | g q / 2 < g z} from connectedComponentIn_subset _ _ hy).le
    have hzs : z ∈ connectedComponentIn {z | s ≤ g z} p :=
      connectedComponentIn_mono p (fun y (hy : t ≤ g y) => show s ≤ g y from
        (min_le_left _ _).trans hy) hzt
    have hNs : connectedComponentIn {z | g q / 2 < g z} q ⊆ connectedComponentIn {z | s ≤ g z} z :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn hz hsub
    rw [← connectedComponentIn_eq hzs] at hNs
    exact ⟨s, hs, hNs (hN q).2, hNs⟩
  refine ⟨isOpen_compl_iff.mp ?_, ?_⟩
  · refine isOpen_iff_forall_mem_open.mpr fun q hq => ⟨_, ?_, (hN q).1, (hN q).2⟩
    rintro z hz ⟨t, ht, hzt⟩
    obtain ⟨s, hs, hqs, -⟩ := hstep q z hz t ht hzt
    exact hq ⟨s, hs, hqs⟩
  · refine isOpen_iff_forall_mem_open.mpr fun q hq => ⟨_, ?_, (hN q).1, (hN q).2⟩
    obtain ⟨t, ht, hqt⟩ := hq
    obtain ⟨s, hs, -, hsub⟩ := hstep q q (hN q).2 t ht hqt
    exact fun z hz => ⟨s, hs, hsub hz⟩

theorem isPreconnected_superlevel [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a : ℝ} (ha : 0 < a)
    (hpos : ∀ x, I.IsInteriorPoint x → 0 < f x) (hint : ∀ x, 0 < f x → I.IsInteriorPoint x)
    (hreg : ∀ x, 0 < f x → f x ≤ a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    IsPreconnected {x | a ≤ f x} := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞ (by simp) (M := M)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) U :=
    DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  have _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ U :=
    DifferentialGeometry.Manifold.interiorIsManifold I ∞
  have : LocallyConnectedSpace U := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) U
  have : LocallyCompactSpace U := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 2)) U
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp
    (DifferentialGeometry.Topology.Manifold.isPreconnected_manifold_interior (I := I))
  let g : U → ℝ := fun y => f y
  have hgold : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := hf.comp contMDiff_subtype_val
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞ g :=
    hf.comp (DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val I ∞ (by simp))
  have hgpos (y : U) : 0 < g y := hpos y y.2
  have hgreg (y : U) (hy : g y ≤ a) : ¬ IsCriticalPointAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) g y := by
    intro hcrit
    have ho : (show EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ from
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) g y) =
        (show EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) g y) :=
      DifferentialGeometry.Manifold.mfderiv_interiorAtlas I hgold y
    have hu := DifferentialGeometry.Manifold.mfderiv_openRestriction I hf y y.2
    exact hreg y (hgpos y) hy (hu.symm.trans (ho.symm.trans hcrit))
  have himage : {x : M | a ≤ f x} = Subtype.val '' {y : U | a ≤ g y} := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hint x (ha.trans_le hx)⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [himage]
  refine IsPreconnected.image ?_ _ continuous_subtype_val.continuousOn
  rcases eq_empty_or_nonempty {y : U | a ≤ g y} with he | ⟨p, hp⟩
  · rw [he]
    exact isPreconnected_empty
  have hW := (isOpen_superlevelComponents hg.continuous hgpos p).eq_univ
    ⟨p, a, ha, mem_connectedComponentIn hp⟩
  have hsub : {y : U | a ≤ g y} ⊆ connectedComponentIn {y : U | a ≤ g y} p := by
    intro q hq
    obtain ⟨t, ht, hqt⟩ : ∃ t, 0 < t ∧ q ∈ connectedComponentIn {z | t ≤ g z} p := by
      have h := hW ▸ mem_univ q
      exact h
    set r := min t a
    have hr : 0 < r := lt_min ht ha
    have hqr : q ∈ connectedComponentIn {z | r ≤ g z} p :=
      connectedComponentIn_mono p (fun y (hy : t ≤ g y) => show r ≤ g y from
        (min_le_left _ _).trans hy) hqt
    have hcompact : IsCompact (g ⁻¹' Icc r a) := by
      refine Subtype.isCompact_iff.mpr ?_
      have heq : Subtype.val '' (g ⁻¹' Icc r a) = f ⁻¹' Icc r a := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hint x (hr.trans_le hx.1)⟩, hx, rfl⟩
      rw [heq]
      exact (isClosed_Icc.preimage hf.continuous).isCompact
    have h := connectedComponentIn_superlevel_inter_eq_of_no_critical_values hg (min_le_right t a)
      hcompact (fun y hy => hgreg y hy.2) hp
    rw [← h]
    exact ⟨hqr, hq⟩
  rw [subset_antisymm hsub (connectedComponentIn_subset _ _)]
  exact isPreconnected_connectedComponentIn

end Superlevel

namespace BaseMorseData

variable {B : CompactSurface.{u}} (D : BaseMorseData B)

theorem level_zero_pos : 0 < D.level 0 := by
  linarith [D.κ_pos, D.two_κ_lt_level]

theorem isInteriorPoint_of_pos {x : B.Carrier} (hx : 0 < D.f x) :
    (SurfaceModel.model B.kind).IsInteriorPoint x :=
  ((SurfaceModel.model B.kind).isInteriorPoint_iff_not_isBoundaryPoint x).mpr
    fun hb => hx.ne' ((D.eq_zero_iff x).mpr hb)

theorem pos_of_isInteriorPoint {x : B.Carrier}
    (hx : (SurfaceModel.model B.kind).IsInteriorPoint x) : 0 < D.f x :=
  lt_of_le_of_ne (D.nonneg x) fun h =>
    ((SurfaceModel.model B.kind).isInteriorPoint_iff_not_isBoundaryPoint x).mp hx
      ((D.eq_zero_iff x).mp h.symm)

theorem level_zero_lt_of_mem_crit {p : B.Carrier} (hp : p ∈ D.crit) : D.level 0 < D.f p := by
  obtain ⟨i, hi, -⟩ := D.slab p hp
  exact (D.level_strictMono.monotone (Fin.zero_le _)).trans_lt hi.1

theorem mfderiv_ne_zero_of_le {x : B.Carrier} (hx : D.f x ≤ D.level 0) :
    mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f x ≠ 0 := fun h =>
  (D.level_zero_lt_of_mem_crit ((D.mem_crit x).mpr h)).not_ge hx

theorem exists_level_zero_lt : ∃ x, D.level 0 < D.f x := by
  obtain ⟨y, hy⟩ := (DifferentialGeometry.Topology.Manifold.dense_manifold_interior
    (I := SurfaceModel.model B.kind) (M := B.Carrier)).nonempty
  obtain ⟨p, -, hp⟩ := isCompact_univ.exists_isMaxOn univ_nonempty D.smooth.continuous.continuousOn
  have hyp : 0 < D.f p := (D.pos_of_isInteriorPoint hy).trans_le (hp (mem_univ y))
  have hcrit : mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) D.f p = 0 := by
    by_contra h
    exact hyp.ne' ((D.eq_zero_iff p).mpr
      (DifferentialGeometry.Topology.Manifold.isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero
        (hp.isLocalMax Filter.univ_mem) h))
  exact ⟨p, D.level_zero_lt_of_mem_crit ((D.mem_crit p).mpr hcrit)⟩

def coreAtlas : SmoothBoundaryAtlas (SurfaceModel.model B.kind) 2 {x | D.level 0 ≤ D.f x} :=
  superlevelAtlas D.smooth (fun _ hx => D.isInteriorPoint_of_pos (D.level_zero_pos.trans_le hx))
    (fun _ hx => D.mfderiv_ne_zero_of_le hx.le)

theorem isConnected_core : IsConnected {x | D.level 0 ≤ D.f x} := by
  obtain ⟨x, hx⟩ := D.exists_level_zero_lt
  refine ⟨⟨x, hx.le⟩, isPreconnected_superlevel D.smooth D.level_zero_pos
    (fun _ hy => D.pos_of_isInteriorPoint hy) (fun _ hy => D.isInteriorPoint_of_pos hy)
    (fun _ _ hy => D.mfderiv_ne_zero_of_le hy)⟩

def core : CompactSurface.{u} where
  kind := .withBoundary
  Carrier := {x : B.Carrier // D.level 0 ≤ D.f x}
  topology := inferInstance
  hausdorff := inferInstance
  secondCountable := TopologicalSpace.Subtype.secondCountableTopology _
  charts := D.coreAtlas.toChartedSpace
  smooth := D.coreAtlas.isManifold
  compact := isCompact_iff_compactSpace.mp
    (isClosed_le continuous_const D.smooth.continuous).isCompact
  connected := isConnected_iff_connectedSpace.mp D.isConnected_core

instance instChartedSpaceCore : ChartedSpace (EuclideanHalfSpace 2) D.core.Carrier :=
  D.core.charts

instance instIsManifoldCore : IsManifold (𝓡∂ 2) ∞ D.core.Carrier :=
  D.core.smooth

instance instChartedSpaceCoreSubtype :
    ChartedSpace (EuclideanHalfSpace 2) {x : B.Carrier // D.level 0 ≤ D.f x} :=
  D.coreAtlas.toChartedSpace

instance instIsManifoldCoreSubtype :
    IsManifold (𝓡∂ 2) ∞ {x : B.Carrier // D.level 0 ≤ D.f x} :=
  D.coreAtlas.isManifold

theorem core_isBoundaryPoint_iff (x : D.core.Carrier) :
    (𝓡∂ 2).IsBoundaryPoint x ↔ D.f x.val = D.level 0 :=
  superlevelAtlas_isBoundaryPoint_iff D.smooth _ _ x

theorem isSmoothEmbedding_core_val (D : BaseMorseData B) :
    Manifold.IsSmoothEmbedding (𝓡∂ 2) (SurfaceModel.model B.kind) ∞
      (Subtype.val : D.core.Carrier → B.Carrier) :=
  isSmoothEmbedding_superlevelAtlas_val D.smooth _ _

end BaseMorseData

end GC.Seifert
