import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.InnerCollarProduct
import DifferentialGeometry.Topology.Manifold.RegularLevel.BoundarySublevelProductOCX
import DifferentialGeometry.Topology.Embedding.CrossModelInstancesOCX
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Ehresmann.Interval

/-!
# The closed inner collar as a smoothly EMBEDDED torus product (lane O-CROSS, G2)

`CuspEmbedding.exists_sublevel_diffeomorph_torus_Icc` (E6 on a cusp carrier) gives the sublevel
`{F ≤ r}` an abstract manifold structure and a product diffeomorphism. The rows (`CuspCores.piece`,
D74-16 / E4c) need the product as a smooth embedding INTO `W`:

* `CuspEmbedding.exists_sublevel_embedding_torus_Icc_OCX`: a smooth embedding
  `Φ : T² × [a, r] → W` (`IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞`) onto `{F ≤ r}`
  with `F ∘ Φ = pr₂` and `T² × {a}` onto `X`; from the concrete-structure E6 kernel
  (`exists_boundarySublevel_embedding_of_boundary_param_OCX`), the sublevel inclusion
  (`boundarySublevel_isSmoothEmbedding_val_OCX`) and the model change
  `halfCollarLinearEquiv_OCX`.
* `CuspEmbedding.exists_sublevel_embedding_torus_unitIcc_OCX`: the same on `T² × [0, 1]`
  (affine reparametrisation of the interval), `F (Φ (t, s)) = (r - a) s + a`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **E6 on a cusp carrier, embedded form.** Same hypotheses as
`CuspEmbedding.exists_sublevel_diffeomorph_torus_Icc`; the product is a smooth embedding into `W`
onto `{F ≤ r}`, carrying the second coordinate to `F` and `T² × {a}` onto `X`. -/
theorem CuspEmbedding.exists_sublevel_embedding_torus_Icc_OCX {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {F : W.Carrier → ℝ} {a r : ℝ} (har : a < r)
    (hF : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F)
    (hreg : ∀ x, F x ≤ r → mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0) (hr : ∃ x, F x = r)
    (hXa : ∀ x ∈ X, F x = a) (hbd : ∀ x, W.model.IsBoundaryPoint x → F x ≤ r → x ∈ X) :
    haveI : Fact (a < r) := ⟨har⟩
    ∃ Φ : Torus × Icc a r → W.Carrier,
      IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ Φ ∧ range Φ = {x | F x ≤ r} ∧
        (∀ p, F (Φ p) = p.2.1) ∧ ∀ p, Φ p ∈ X ↔ p.2.1 = a := by
  obtain ⟨hj, hjinj, hjd, hjbd⟩ := e.boundary_param
  have hmem : ∀ x, x ∈ range (fun t : Torus => e.toFun (t, halfZero)) ↔ x ∈ X :=
    fun x => Set.ext_iff.mp e.boundary_image x
  have hja : ∀ t : Torus, F (e.toFun (t, halfZero)) = a := fun t =>
    hXa _ ((hmem _).mp (mem_range_self t))
  have hjrange : ∀ x, W.model.IsBoundaryPoint x → F x ≤ r →
      x ∈ range (fun t : Torus => e.toFun (t, halfZero)) := fun x hx hxr =>
    (hmem x).mpr (hbd x hx hxr)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) = 1 + 1 := by
    rw [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
  cases W with
  | mk k M orientation =>
    cases k with
    | closed =>
      obtain ⟨t₀⟩ := (inferInstance : Nonempty Torus)
      have hh := ModelWithCorners.Boundaryless.boundary_eq_empty (I := 𝓡 3) (M := M)
      have hb : e.toFun (t₀, halfZero) ∈ (𝓡 3).boundary M := hjbd t₀
      rw [hh] at hb
      exact hb.elim
    | withBoundary =>
      obtain ⟨Φ, hΦ, hrange, hΦF, hΦX⟩ :=
        exists_boundarySublevel_embedding_of_boundary_param_OCX (m := 1) (J := torusModel)
          (T := Torus) hdim halfCollarLinearEquiv_OCX (fun _ => halfCollarLinearEquiv_OCX_range)
          har hF hreg hr (k := K + 1) (by omega) hj hjinj hjd hjbd hja hjrange
      exact ⟨Φ, hΦ, hrange, hΦF, fun p => (hmem _).symm.trans (hΦX p)⟩

/-- **E6 on a cusp carrier, embedded form on `T² × [0, 1]`**: `F (Φ (t, s)) = (r - a) s + a`,
`T² × {0}` onto `X`, range `{F ≤ r}`. -/
theorem CuspEmbedding.exists_sublevel_embedding_torus_unitIcc_OCX {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {F : W.Carrier → ℝ} {a r : ℝ} (har : a < r)
    (hF : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F)
    (hreg : ∀ x, F x ≤ r → mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0) (hr : ∃ x, F x = r)
    (hXa : ∀ x ∈ X, F x = a) (hbd : ∀ x, W.model.IsBoundaryPoint x → F x ≤ r → x ∈ X) :
    ∃ Φ : Torus × Icc (0 : ℝ) 1 → W.Carrier,
      IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ Φ ∧ range Φ = {x | F x ≤ r} ∧
        (∀ p, F (Φ p) = (r - a) * (p.2 : ℝ) + a) ∧ ∀ p, Φ p ∈ X ↔ (p.2 : ℝ) = 0 := by
  have : Fact (a < r) := ⟨har⟩
  obtain ⟨Φ, hΦ, hrange, hΦF, hΦX⟩ :=
    e.exists_sublevel_embedding_torus_Icc_OCX har hF hreg hr hXa hbd
  let R : Diffeomorph (torusModel.prod (𝓡∂ 1)) (torusModel.prod (𝓡∂ 1))
      (Torus × Icc (0 : ℝ) 1) (Torus × Icc a r) ∞ :=
    (Diffeomorph.refl torusModel Torus ∞).prodCongr
      (DifferentialGeometry.Topology.Ehresmann.affineIntervalDiffeomorph a r)
  have hR : ∀ p, ((R p).2 : ℝ) = (r - a) * (p.2 : ℝ) + a := fun p =>
    DifferentialGeometry.Topology.Ehresmann.affineIntervalDiffeomorph_apply a r p.2
  refine ⟨Φ ∘ R, hΦ.comp_diffeomorph R, ?_, fun p => ?_, fun p => ?_⟩
  · have hRs : range R = univ := R.toEquiv.surjective.range_eq
    rw [range_comp, hRs, image_univ]
    exact hrange
  · change F (Φ (R p)) = _
    rw [hΦF, hR]
  · change Φ (R p) ∈ X ↔ _
    rw [hΦX, hR]
    constructor
    · intro h
      have h1 : (r - a) * (p.2 : ℝ) = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · exact h2
    · intro h
      rw [h]
      ring

/-- **E6 on a cusp carrier, full concrete form**: the statement of
`CuspEmbedding.exists_sublevel_diffeomorph_torus_Icc` (sublevel structure, product `D`) with, in
addition, `val ∘ D` a smooth embedding into `W`. -/
theorem CuspEmbedding.exists_sublevel_diffeomorph_torus_Icc_embedding_OCX
    {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {F : W.Carrier → ℝ} {a r : ℝ} (har : a < r)
    (hF : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F)
    (hreg : ∀ x, F x ≤ r → mfderiv W.model 𝓘(ℝ, ℝ) F x ≠ 0) (hr : ∃ x, F x = r)
    (hXa : ∀ x ∈ X, F x = a) (hbd : ∀ x, W.model.IsBoundaryPoint x → F x ≤ r → x ∈ X) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) {x : W.Carrier // F x ≤ r},
      letI := cs
      IsManifold (𝓡∂ 3) ∞ {x : W.Carrier // F x ≤ r} ∧
      ContMDiff (𝓡∂ 3) W.model ∞ (fun x : {x : W.Carrier // F x ≤ r} => x.1) ∧
      (∀ y : {x : W.Carrier // F x ≤ r}, (𝓡∂ 3).IsBoundaryPoint y ↔ (y.1 ∈ X ∨ F y.1 = r)) ∧
      haveI : Fact (a < r) := ⟨har⟩
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc a r)
          {x : W.Carrier // F x ≤ r} ∞,
        (∀ p, F (D p).1 = p.2.1) ∧ (∀ p, (D p).1 ∈ X ↔ p.2.1 = a) ∧
        IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (fun p => (D p).1) := by
  obtain ⟨hj, hjinj, hjd, hjbd⟩ := e.boundary_param
  have hmem : ∀ x, x ∈ range (fun t : Torus => e.toFun (t, halfZero)) ↔ x ∈ X :=
    fun x => Set.ext_iff.mp e.boundary_image x
  have hja : ∀ t : Torus, F (e.toFun (t, halfZero)) = a := fun t =>
    hXa _ ((hmem _).mp (mem_range_self t))
  have hjrange : ∀ x, W.model.IsBoundaryPoint x → F x ≤ r →
      x ∈ range (fun t : Torus => e.toFun (t, halfZero)) := fun x hx hxr =>
    (hmem x).mpr (hbd x hx hxr)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) = 1 + 1 := by
    rw [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
  cases W with
  | mk k M orientation =>
    cases k with
    | closed =>
      obtain ⟨t₀⟩ := (inferInstance : Nonempty Torus)
      have hh := ModelWithCorners.Boundaryless.boundary_eq_empty (I := 𝓡 3) (M := M)
      have hb : e.toFun (t₀, halfZero) ∈ (𝓡 3).boundary M := hjbd t₀
      rw [hh] at hb
      exact hb.elim
    | withBoundary =>
      obtain ⟨cs, hm, hval, hiff, D, hDF, hDX, hemb⟩ :=
        exists_boundarySublevel_product_embedding_full_OCX (m := 1) (J := torusModel)
          (T := Torus) hdim halfCollarLinearEquiv_OCX (fun _ => halfCollarLinearEquiv_OCX_range)
          har hF hreg hr (k := K + 1) (by omega) hj hjinj hjd hjbd hja hjrange
      exact ⟨cs, hm, hval, fun y => (hiff y).trans (or_congr_left (hmem y.1)), D, hDF,
        fun p => (hmem _).symm.trans (hDX p), hemb⟩

end DifferentialGeometry.Geometry.Collapse
