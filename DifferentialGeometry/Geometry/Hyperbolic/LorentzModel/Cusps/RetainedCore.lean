import DifferentialGeometry.Topology.ThreeManifold.Geometrization.BoundaryAtlas
import DifferentialGeometry.Topology.Manifold.FiniteCollarBoundaryAtlas
import DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import DifferentialGeometry.Topology.Diffeomorph.Product
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.SignedCylinder

noncomputable section

open Set GC.Endpoint
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

private theorem exists_smoothBoundaryAtlas_of_torus_collars
    {M ι : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [Finite ι]
    (P : ι → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) M ∞)
    (hzero : ∀ i q, (q, (0 : ℝ)) ∈ (P i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun q : Torus => P i (q, 0))) (range (fun q : Torus => P j (q, 0)))))
    {K : Set M} (hregular : closure (interior K) = K)
    (hfrontier : frontier K ⊆ ⋃ i, range (fun q : Torus => P i (q, 0))) :
    ∃ C : SmoothBoundaryAtlas (𝓡 3) 3 K,
      ∀ x : K, C.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier K := by
  let L : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 2) :=
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 1))).prodCongr
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))).trans (normalFirstEquiv 1)
  let e := torusModel.toHomeomorph.trans L.toHomeomorph
  have hc : ∀ y, (𝓡 2) (e y) = L (torusModel y) := fun _ => rfl
  let CT := DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := Torus) e
  let DT : let _ := CT; Diffeomorph (𝓡 2) torusModel Torus Torus ∞ := by
    let _ := CT
    refine ⟨Equiv.refl Torus, ?_, ?_⟩
    · exact (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
        torusModel (𝓡 2) e L hc (𝓡 2) (f := id)).mp contMDiff_id
    · exact (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
        torusModel (𝓡 2) e L hc torusModel (f := id)).mpr contMDiff_id
  let _ := CT
  let _ : IsManifold (𝓡 2) ∞ Torus :=
    DifferentialGeometry.Manifold.isManifold_transHomeomorph
      torusModel (𝓡 2) e L hc
  let Q (i : ι) : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) (Torus × ℝ) M ∞ :=
    (DT.prodCongrCross (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)).toPartialDiffeomorph.trans (P i)
  apply exists_smoothBoundaryAtlas_of_finite_disjoint_collars Q
  · intro i q
    exact ⟨mem_univ _, hzero i q⟩
  · exact hdisjoint
  · exact hregular
  · exact hfrontier

end DifferentialGeometry.Topology

noncomputable section

open Set GC.Endpoint
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

private theorem exists_halfCollar_of_signedChart
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {K : Set M} (A : SmoothBoundaryAtlas (𝓡 3) 3 K)
    (φ : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) M ∞)
    (hsource : φ.source = {z | z.2 < 1})
    (hside : ∀ z ∈ φ.source, φ z ∈ K ↔ 0 ≤ z.2) :
    let _ := A.toChartedSpace
    ∃ ψ : PartialDiffeomorph halfCollarModel (𝓡∂ 3)
        (Torus × EuclideanHalfSpace 1) K ∞,
      ψ.source = halfCollarSource ∧ ψ.target = Subtype.val ⁻¹' φ.target ∧
      (∀ p ∈ halfCollarSource, (ψ p).val = φ (p.1, p.2.val 0)) ∧
      ∀ y ∈ ψ.target,
        ((ψ.symm y).1, (ψ.symm y).2.val 0) = φ.symm y.val := by
  classical
  let _ := A.toChartedSpace
  have hs (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
      (p.1, p.2.val 0) ∈ φ.source := by
    rw [hsource]
    exact hp
  have h0 : (((1, 1) : Torus), (0 : ℝ)) ∈ φ.source := by
    rw [hsource]
    change (0 : ℝ) < 1
    exact zero_lt_one
  let x₀ : K := ⟨φ (((1, 1) : Torus), (0 : ℝ)), (hside _ h0).mpr le_rfl⟩
  let f : Torus × EuclideanHalfSpace 1 → K := fun p =>
    if hp : φ (p.1, p.2.val 0) ∈ K then ⟨φ (p.1, p.2.val 0), hp⟩ else x₀
  let g : K → Torus × EuclideanHalfSpace 1 := fun y =>
    ((φ.symm y.val).1, Manifold.halfSpaceOneLift (φ.symm y.val).2)
  have hf (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
      (f p).val = φ (p.1, p.2.val 0) := by
    dsimp only [f]
    rw [dite_eq_left ((hside _ (hs p hp)).mpr p.2.property)]
  have ht (y : K) (hy : y.val ∈ φ.target) : 0 ≤ (φ.symm y.val).2 :=
    (hside _ (φ.map_target hy)).mp (by rw [φ.right_inv hy]; exact y.property)
  have hg (y : K) (hy : y.val ∈ φ.target) :
      ((g y).1, (g y).2.val 0) = φ.symm y.val := by
    apply Prod.ext
    · rfl
    · change max (φ.symm y.val).2 0 = (φ.symm y.val).2
      exact max_eq_left (ht y hy)
  have hgs (y : K) (hy : y.val ∈ φ.target) : g y ∈ halfCollarSource := by
    change (g y).2.val 0 < 1
    rw [show (g y).2.val 0 = (φ.symm y.val).2 from congrArg Prod.snd (hg y hy)]
    have hh := φ.map_target hy
    rw [hsource] at hh
    exact hh
  have hlift (t : EuclideanHalfSpace 1) : Manifold.halfSpaceOneLift (t.val 0) = t := by
    apply Subtype.ext
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change max (t.val 0) 0 = t.val 0
    exact max_eq_left t.property
  let ψ : PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) K ∞ :=
    { toFun := f
      invFun := g
      source := halfCollarSource
      target := Subtype.val ⁻¹' φ.target
      map_source' := fun p hp => by
        change (f p).val ∈ φ.target
        rw [hf p hp]
        exact φ.map_source (hs p hp)
      map_target' := hgs
      left_inv' := fun p hp => by
        dsimp only [g]
        rw [hf p hp]
        have hi := congrArg (fun z : Torus × ℝ => (z.1, Manifold.halfSpaceOneLift z.2))
          (φ.left_inv (hs p hp))
        exact hi.trans (Prod.ext rfl (hlift p.2))
      right_inv' := fun y hy => by
        apply Subtype.ext
        rw [hf (g y) (hgs y hy), hg y hy]
        exact φ.right_inv hy
      open_source := isOpen_lt
        ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
        continuous_const
      open_target := φ.open_target.preimage continuous_subtype_val
      contMDiffOn_toFun := by
        apply (A.contMDiffOn_iff_subtype_val f halfCollarSource).mpr
        have hc : ContMDiff halfCollarModel signedCollarModel ∞
            (fun p : Torus × EuclideanHalfSpace 1 => (p.1, p.2.val 0)) :=
          contMDiff_fst.prodMk (Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)
        exact (φ.contMDiffOn_toFun.comp hc.contMDiffOn hs).congr hf
      contMDiffOn_invFun := by
        have hc : ContMDiffOn (𝓡∂ 3) signedCollarModel ∞
            (φ.symm ∘ Subtype.val) (Subtype.val ⁻¹' φ.target) :=
          φ.contMDiffOn_invFun.comp A.contMDiff_subtype_val.contMDiffOn (fun _ hy => hy)
        have hc₁ : ContMDiffOn (𝓡∂ 3) torusModel ∞
            (fun y : K => (φ.symm y.val).1) (Subtype.val ⁻¹' φ.target) :=
          fun y hy => (hc y hy).fst
        have hc₂ : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ) ∞
            (fun y : K => (φ.symm y.val).2) (Subtype.val ⁻¹' φ.target) :=
          fun y hy => (hc y hy).snd
        exact hc₁.prodMk (Manifold.contMDiffOn_halfSpaceOneLift.comp hc₂ ht) }
  exact ⟨ψ, rfl, rfl, hf, hg⟩

end DifferentialGeometry.Topology

noncomputable section

open Set GC.Endpoint
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

private theorem exists_halfCollar_of_retained_side
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {K : Set M} (A : SmoothBoundaryAtlas (𝓡 3) 3 K)
    (P : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) M ∞)
    (R : ℝ) (hR : 0 < R)
    (hsource : P.source = {z | 0 < R + z.2})
    (hside : ∀ z ∈ P.source, P z ∈ K ↔ z.2 ≤ 0) :
    let _ := A.toChartedSpace
    ∃ ψ : PartialDiffeomorph halfCollarModel (𝓡∂ 3)
        (Torus × EuclideanHalfSpace 1) K ∞,
      ψ.source = halfCollarSource ∧
      (∀ p ∈ halfCollarSource, (ψ p).val = P (p.1, -(R / 2) * p.2.val 0)) ∧
      ∀ y ∈ ψ.target, y.val ∈ P.target := by
  let _ := A.toChartedSpace
  have hhalf : R / 2 ≠ 0 := ne_of_gt (half_pos hR)
  let T : Diffeomorph signedCollarModel signedCollarModel (Torus × ℝ) (Torus × ℝ) ∞ :=
    { toFun := fun z => (z.1, -(R / 2) * z.2)
      invFun := fun z => (z.1, -(z.2 / (R / 2)))
      left_inv := fun z => Prod.ext rfl (by field_simp [hhalf])
      right_inv := fun z => Prod.ext rfl (by field_simp [hhalf])
      contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_const.mul contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk ((contMDiff_snd.div_const _).neg) }
  let Q := T.toPartialDiffeomorph.trans P
  let φ := PartialDiffeomorph.restrict Q {z | z.2 < 1}
    (isOpen_lt continuous_snd continuous_const)
  have hφ : φ.source = {z | z.2 < 1} := by
    ext z
    change ((True ∧ (z.1, -(R / 2) * z.2) ∈ P.source) ∧ z.2 < 1) ↔ z.2 < 1
    rw [hsource]
    change ((True ∧ 0 < R + -(R / 2) * z.2) ∧ z.2 < 1) ↔ z.2 < 1
    constructor
    · exact fun h => h.2
    · intro hz
      refine ⟨⟨trivial, ?_⟩, hz⟩
      nlinarith
  have heq (z : Torus × ℝ) : φ z = P (z.1, -(R / 2) * z.2) := rfl
  have hsideφ (z : Torus × ℝ) (hz : z ∈ φ.source) : φ z ∈ K ↔ 0 ≤ z.2 := by
    have hp : (z.1, -(R / 2) * z.2) ∈ P.source := hz.1.2
    rw [heq, hside _ hp]
    constructor <;> intro h <;> nlinarith
  obtain ⟨ψ, hψs, hψt, hψ, _⟩ := exists_halfCollar_of_signedChart A φ hφ hsideφ
  refine ⟨ψ, hψs, ?_, ?_⟩
  · intro p hp
    exact (hψ p hp).trans (heq _)
  · intro y hy
    rw [hψt] at hy
    exact hy.1.1

end DifferentialGeometry.Topology

noncomputable section

open Set GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

private theorem exists_boundaryTori_of_retained_torus_charts
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M]
    (O : ManifoldOrientation (𝓡 3) M 3)
    {K : Set M} (hK : IsCompact K) (hregular : closure (interior K) = K)
    {n : ℕ}
    (P : Fin n → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) M ∞)
    (R : Fin n → ℝ) (hR : ∀ i, 0 < R i)
    (hsource : ∀ i, (P i).source = {z | 0 < R i + z.2})
    (hside : ∀ i, ∀ z ∈ (P i).source, P i z ∈ K ↔ z.2 ≤ 0)
    (hdisjoint : Pairwise (fun i j => Disjoint (P i).target (P j).target))
    (hfrontier : frontier K = ⋃ i, range (fun q : Torus => P i (q, 0))) :
    ∃ A : SmoothBoundaryAtlas (𝓡 3) 3 K,
      (∀ x : K, A.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier K) ∧
      let C := CompactCarrier.ofBoundaryAtlas A O hK
      let _ := C.charts
      ∃ T : BoundaryTori C n,
        C.model.boundary C.Carrier = T.image ∧
        (∀ i q, (T.torusMap i q).val = P i (q, 0)) ∧
        ∀ i p, p ∈ halfCollarSource →
          (T.collar i p).val = P i (p.1, -(R i / 2) * p.2.val 0) := by
  classical
  have hzero (i : Fin n) (q : Torus) : (q, (0 : ℝ)) ∈ (P i).source := by
    rw [hsource]
    simpa only [mem_ofPred_eq, add_zero] using hR i
  have hd : Pairwise (fun i j => Disjoint
      (range (fun q : Torus => P i (q, 0))) (range (fun q : Torus => P j (q, 0)))) := by
    intro i j hij
    apply (hdisjoint hij).mono
    · rintro y ⟨q, rfl⟩
      exact (P i).map_source (hzero i q)
    · rintro y ⟨q, rfl⟩
      exact (P j).map_source (hzero j q)
  obtain ⟨A, hA⟩ := exists_smoothBoundaryAtlas_of_torus_collars
    P hzero hd hregular hfrontier.subset
  let _ := A.toChartedSpace
  choose ψ hψs hψ hψt using fun i =>
    exists_halfCollar_of_retained_side A (P i) (R i) (hR i) (hsource i) (hside i)
  have hz (i : Fin n) (q : Torus) : (ψ i (q, halfZero)).val = P i (q, 0) := by
    have h := hψ i (q, halfZero) (by change (0 : ℝ) < 1; exact zero_lt_one)
    change (ψ i (q, halfZero)).val = P i (q, -(R i / 2) * 0) at h
    simpa only [mul_zero] using h
  have hψdisjoint : Pairwise (fun i j => Disjoint (ψ i).target (ψ j).target) := by
    intro i j hij
    rw [disjoint_left]
    intro y hyi hyj
    exact disjoint_left.mp (hdisjoint hij) (hψt i y hyi) (hψt j y hyj)
  let C := CompactCarrier.ofBoundaryAtlas A O hK
  let _ := C.charts
  let T : BoundaryTori C n :=
    { collar := ψ
      source_eq := hψs
      boundary_zero := fun i q => by
        apply (A.isBoundaryPoint_iff_mem_frontier hA _).mpr
        rw [hz, hfrontier]
        exact mem_iUnion.mpr ⟨i, mem_range_self q⟩
      disjoint := hψdisjoint }
  refine ⟨A, hA, T, ?_, hz, hψ⟩
  ext x
  constructor
  · intro hx
    have hxf := (A.isBoundaryPoint_iff_mem_frontier hA x).mp hx
    rw [hfrontier] at hxf
    obtain ⟨i, q, hq⟩ := mem_iUnion.mp hxf
    exact mem_iUnion.mpr ⟨i, q, Subtype.ext ((hz i q).trans hq)⟩
  · intro hx
    obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hx
    exact T.boundary_zero i q

end DifferentialGeometry.Topology

noncomputable section

open Set GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) : MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

variable {Γ : Subgroup (PO (2 + 1) 1)} [DiscreteTopology Γ]
  [IsCancelSMul Γ (HUpper (2 + 1))] {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 2) Γ r)

local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper (2 + 1))
local notation "πΓ" => Quotient.mk (MulAction.orbitRel Γ (HUpper (2 + 1)))
local notation "S" ξ =>
  (Quotient.mk (MulAction.orbitRel
    (endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton (Subtype.val ξ))) (HUpper (2 + 1)))) ''
      Busemann.horosphere (Subtype.val ξ) (D.level ξ)

private local instance (ξ : D.centers) :
    IsCancelSMul (endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton ξ.val)) (HUpper (2 + 1)) :=
  EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 2)
    (show endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton ξ.val) ≤ Γ from inf_le_left)

private local instance (ξ : D.centers) : ChartedSpace (Fin 2 → ℝ) (S ξ) :=
  D.horosphereQuotientChartedSpace hΓ ξ

theorem exists_boundaryTori_cylindricalCore_image
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M]
    (O : ManifoldOrientation (𝓡 3) M 3) (e : QΓ ≃ₜ M)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ πΓ))
    (F : ∀ ξ : D.centers, Diffeomorph torusModel 𝓘(ℝ, Fin 2 → ℝ) Torus (S ξ) ∞)
    {n : ℕ} (σ : Fin n ≃ D.centers) (R : D.centers → ℝ) (hR : ∀ ξ, 0 < R ξ) :
    let K := e '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R
    ∃ (hK : IsCompact K) (A : Topology.SmoothBoundaryAtlas (𝓡 3) 3 K),
      (∀ x : K, A.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier K) ∧
      let C := CompactCarrier.ofBoundaryAtlas A O hK
      let _ := C.charts
      ∃ T : BoundaryTori C n,
        C.model.boundary C.Carrier = T.image ∧
        (∀ i q, (T.torusMap i q).val =
          e (D.horoballCylinderMap hΓ (σ i) (F (σ i) q, ⟨R (σ i), (hR (σ i)).le⟩))) ∧
        ∀ i q (t : Ico (0 : ℝ) 1),
          (T.collar i (q, halfPoint t.val t.property.1)).val =
            e (D.horoballCylinderMap hΓ (σ i)
              (F (σ i) q, ⟨R (σ i) - (R (σ i) / 2) * t.val,
                by
                  change 0 ≤ R (σ i) - (R (σ i) / 2) * t.val
                  have hh := mul_lt_of_lt_one_right (half_pos (hR (σ i))) t.property.2
                  linarith [hR (σ i)]⟩)) := by
  classical
  let _ : Finite D.centers := D.finite_centers
  let _ : ∀ ξ : D.centers, CompactSpace (S ξ) := fun ξ =>
    isCompact_iff_compactSpace.mp (D.isCompact_quotient_horosphere_of_compact_core hΓ ξ)
  let K := e '' Topology.cylindricalCore (fun ξ => D.horoballCylinderMap hΓ ξ) R
  have hK : IsCompact K := by
    apply IsCompact.image _ e.continuous
    apply Topology.isCompact_cylindricalCore (C := fun ξ => S ξ)
      (fun ξ => D.horoballCylinderMap hΓ ξ) (D.horoballCylinderMap_isClosedEmbedding hΓ)
      (D.isOpen_image_horoballCylinderMap_pos hΓ) ?_ R (fun ξ => (hR ξ).le)
    rw [D.cylindricalCore_zero hΓ]
    exact D.isCompact_quotient
  have hregular : closure (interior K) = K := by
    change closure (interior (e '' _)) = e '' _
    rw [← e.image_interior, ← e.image_closure, D.closure_interior_cylindricalCore hΓ R hR]
  choose P hsource htarget hzero hforward hinverse using fun ξ =>
    D.exists_partialDiffeomorph_horoballCylinderMap_at_depth ξ e he (F ξ) (R ξ) (hR ξ)
  have hzero_eq (ξ : D.centers) (q : Torus) :
      P ξ (q, 0) = e (D.horoballCylinderMap hΓ ξ (F ξ q, ⟨R ξ, (hR ξ).le⟩)) := by
    simpa only [add_zero] using hforward ξ (q, 0) (by simpa only [add_zero] using hR ξ)
  have hside (ξ : D.centers) (z : Torus × ℝ) (hz : z ∈ (P ξ).source) :
      P ξ z ∈ K ↔ z.2 ≤ 0 := by
    have hz' : 0 < R ξ + z.2 := by
      rw [hsource] at hz
      exact hz
    rw [hforward ξ z hz']
    change e (D.horoballCylinderMap hΓ ξ _) ∈ e '' _ ↔ _
    rw [e.injective.mem_set_image, Topology.mem_cylindricalCore_image_iff
      (fun η => D.horoballCylinderMap hΓ η)
      (fun η => (D.horoballCylinderMap_isClosedEmbedding hΓ η).injective)
      (D.pairwise_disjoint_range_horoballCylinderMap hΓ)]
    change R ξ + z.2 ≤ R ξ ↔ z.2 ≤ 0
    exact add_le_iff_nonpos_right (R ξ)
  have htarget_mem (ξ : D.centers) {y : M} (hy : y ∈ (P ξ).target) :
      y ∈ e '' range (D.horoballCylinderMap hΓ ξ) := by
    have hs := (P ξ).map_target hy
    have hz : 0 < R ξ + ((P ξ).symm y).2 := by
      rw [hsource] at hs
      exact hs
    refine ⟨D.horoballCylinderMap hΓ ξ (F ξ ((P ξ).symm y).1, ⟨_, hz.le⟩),
      mem_range_self _, ?_⟩
    exact (hforward ξ ((P ξ).symm y) hz).symm.trans ((P ξ).right_inv hy)
  have hdisjoint : Pairwise (fun ξ η : D.centers => Disjoint (P ξ).target (P η).target) := by
    intro ξ η hξη
    rw [disjoint_left]
    intro y hyξ hyη
    obtain ⟨x, hx, hxy⟩ := htarget_mem ξ hyξ
    obtain ⟨z, hz, hzy⟩ := htarget_mem η hyη
    have hzx : z = x := e.injective (hzy.trans hxy.symm)
    exact disjoint_left.mp (D.pairwise_disjoint_range_horoballCylinderMap hΓ hξη)
      hx (hzx ▸ hz)
  have hfrontier : frontier K = ⋃ i, range (fun q : Torus => P (σ i) (q, 0)) := by
    change frontier (e '' _) = _
    rw [← e.image_frontier, D.frontier_cylindricalCore hΓ R (fun ξ => (hR ξ).le)]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨ξ, p, hp, rfl⟩ := mem_iUnion.mp hx
      obtain ⟨i, rfl⟩ := σ.surjective ξ
      refine mem_iUnion.mpr ⟨i, (F (σ i)).symm p.1, ?_⟩
      change P (σ i) ((F (σ i)).symm p.1, 0) = e (D.horoballCylinderMap hΓ (σ i) p)
      rw [hzero_eq]
      apply congrArg e
      apply congrArg (D.horoballCylinderMap hΓ (σ i))
      exact Prod.ext ((F (σ i)).apply_symm_apply p.1) (Subtype.ext hp.symm)
    · rintro hy
      obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hy
      change P (σ i) (q, 0) ∈ e '' _
      rw [hzero_eq]
      exact ⟨_, mem_iUnion.mpr ⟨σ i, (F (σ i) q, ⟨R (σ i), (hR (σ i)).le⟩), rfl, rfl⟩, rfl⟩
  obtain ⟨A, hA, T, hT, hz, hc⟩ :=
    Topology.exists_boundaryTori_of_retained_torus_charts O hK hregular
      (fun i => P (σ i)) (fun i => R (σ i)) (fun i => hR (σ i))
      (fun i => hsource (σ i)) (fun i => hside (σ i))
      (fun i j hij => hdisjoint (σ.injective.ne hij)) hfrontier
  refine ⟨hK, A, hA, T, hT, ?_, ?_⟩
  · intro i q
    exact (hz i q).trans (hzero_eq (σ i) q)
  · intro i q t
    have ht : (q, halfPoint t.val t.property.1) ∈ halfCollarSource := t.property.2
    rw [hc i _ ht]
    have hp : 0 < R (σ i) + -(R (σ i) / 2) * t.val := by
      have hh := mul_lt_of_lt_one_right (half_pos (hR (σ i))) t.property.2
      linarith [hR (σ i)]
    change P (σ i) (q, -(R (σ i) / 2) * t.val) = _
    rw [hforward (σ i) _ hp]
    apply congrArg e
    apply congrArg (D.horoballCylinderMap hΓ (σ i))
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change R (σ i) + -(R (σ i) / 2) * t.val = R (σ i) - (R (σ i) / 2) * t.val
      ring

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
