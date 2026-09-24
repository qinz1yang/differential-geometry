import DifferentialGeometry.Topology.ThreeManifold.CapAnnulus
import DifferentialGeometry.Topology.ThreeManifold.CoreCapOppositeSides
import DifferentialGeometry.Topology.Attachment.Union

set_option autoImplicit false
noncomputable section

open Set Metric Manifold Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Sphere" => Metric.sphere (0 : E3) 1
local notation "Annulus" => Sphere × Icc (1 / 4 : ℝ) 1
private local instance cellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
private local instance cellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

def capAnnuliBoundaryInclusion : (Σ _b : T.Boundary, Sphere) → (Σ _b : T.Boundary, Annulus) :=
  fun q => ⟨q.1, q.2, ⟨1, by norm_num⟩⟩

def capAnnuliMap (q : Σ _b : T.Boundary, Annulus) : N.Carrier := C.capAnnulusMap q.1 q.2

def capAnnuliAttachingMap (q : Σ _b : T.Boundary, Sphere) : range C.coreInclusion :=
  ⟨C.coreInclusion (T.coreBoundarySphere q.1 (C.attaching q.1 q.2)), ⟨_, rfl⟩⟩

theorem capAnnuliAttachingMap_val (q : Σ _b : T.Boundary, Sphere) :
    (C.capAnnuliAttachingMap q).val = C.capAnnuliMap (capAnnuliBoundaryInclusion q) :=
  (C.capAnnulusMap_outer q.1 q.2).symm

theorem capAnnuliMap_continuous : Continuous C.capAnnuliMap :=
  continuous_sigma fun b => (C.capAnnulusMap b).continuous

theorem capAnnuliMap_injective : Injective C.capAnnuliMap := by
  rintro ⟨b, p⟩ ⟨b', q⟩ h
  have hbb : b = b' := by
    by_contra hne
    have hp : C.capAnnulusMap b p ∈ range (C.cap b) := by
      have h := mem_range_self p (f := C.capAnnulusMap b)
      rw [C.range_capAnnulusMap b] at h
      exact ⟨h.choose, h.choose_spec.2⟩
    have hq : C.capAnnulusMap b' q ∈ range (C.cap b') := by
      have h := mem_range_self q (f := C.capAnnulusMap b')
      rw [C.range_capAnnulusMap b'] at h
      exact ⟨h.choose, h.choose_spec.2⟩
    have heq : C.capAnnulusMap b p = C.capAnnulusMap b' q := h
    exact Set.disjoint_left.mp (C.cap_disjoint hne) hp (heq.symm ▸ hq)
  subst b'
  have hpq : p = q := C.capAnnulusMap_injective b h
  subst q
  rfl

theorem range_capAnnuliMap : range C.capAnnuliMap = ⋃ b, range (C.capAnnulusMap b) := by
  ext y
  simp only [mem_range, mem_iUnion]
  exact ⟨fun ⟨⟨b, q⟩, h⟩ => ⟨b, q, h⟩, fun ⟨b, q, h⟩ => ⟨⟨b, q⟩, h⟩⟩

private theorem capAnnulusMap_mem_core_iff (b : T.Boundary) (q : Annulus) :
    C.capAnnulusMap b q ∈ range C.coreInclusion ↔ q.2.val = 1 := by
  constructor
  · intro h
    let x : ClosedCell 3 := ⟨q.2.val • q.1.val, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [q.2.property.1]),
        norm_eq_of_mem_sphere, mul_one]
      exact q.2.property.2⟩
    have hx : C.cap b x ∈ range C.coreInclusion := h
    obtain ⟨z, hz⟩ := C.eq_sphereToClosedCell_of_cap_mem_coreImage b hx
    have hn := congrArg (fun w : ClosedCell 3 => ‖w.val‖) hz
    change ‖z.val‖ = ‖q.2.val • q.1.val‖ at hn
    rw [norm_eq_of_mem_sphere, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [q.2.property.1]), norm_eq_of_mem_sphere, mul_one] at hn
    exact hn.symm
  · intro h
    have ht : q.2 = (⟨1, by norm_num⟩ : Icc (1 / 4 : ℝ) 1) := Subtype.ext h
    have hq : q = (q.1, ⟨1, by norm_num⟩) := Prod.ext rfl ht
    rw [hq, C.capAnnulusMap_outer]
    exact mem_range_self _

private theorem capAnnuliMap_mem_core_boundary (q : Σ _b : T.Boundary, Annulus)
    (hq : C.capAnnuliMap q ∈ range C.coreInclusion) : q ∈ range (capAnnuliBoundaryInclusion (T := T)) := by
  have ht := (C.capAnnulusMap_mem_core_iff q.1 q.2).mp hq
  refine ⟨⟨q.1, q.2.1⟩, ?_⟩
  cases q with
  | mk b p =>
    have he : (p.1, (⟨1, by norm_num⟩ : Icc (1 / 4 : ℝ) 1)) = p :=
      Prod.ext rfl (Subtype.ext ht.symm)
    exact congrArg (fun r : Annulus => (⟨b, r⟩ : Σ _b : T.Boundary, Annulus)) he

private theorem isClosed_coreImage : IsClosed (range C.coreInclusion) := by
  have hi : IsCompact (range C.coreInclusion) := by
    let _ : CompactSpace T.core := isCompact_iff_compactSpace.mp C.core_compact
    exact isCompact_range C.coreInclusion.continuous
  exact hi.isClosed

abbrev PuncturedCapping :=
  AdjunctionSpace (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap

def capAnnuliHomeomorph : C.PuncturedCapping ≃ₜ
    (range C.coreInclusion ∪ ⋃ b, range (C.capAnnulusMap b) : Set N.Carrier) :=
  (adjunctionHomeomorphUnionImage (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
    C.capAnnuliMap C.capAnnuliAttachingMap_val C.capAnnuliMap_injective C.capAnnuliMap_continuous
    C.capAnnuliMap_mem_core_boundary C.isClosed_coreImage).trans
      (Homeomorph.setCongr (by rw [C.range_capAnnuliMap]))

@[simp] theorem capAnnuliHomeomorph_core (x : range C.coreInclusion) :
    (C.capAnnuliHomeomorph (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
      C.capAnnuliAttachingMap x)).val = x.val := rfl

@[simp] theorem capAnnuliHomeomorph_annulus (b : T.Boundary) (q : Annulus) :
    (C.capAnnuliHomeomorph (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
      C.capAnnuliAttachingMap ⟨b, q⟩)).val = C.capAnnulusMap b q := rfl

theorem capBallChart_image_ball (b : T.Boundary) :
    (C.capBallChart b).chart '' Metric.ball (0 : E3) 1 =
      C.cap b '' {x : ClosedCell 3 | ‖x.val‖ < 1 / 4} := by
  let r : ℝ := if b.2 then 1 / 4 else -(1 / 4)
  have habs : |r| = 1 / 4 := by dsimp only [r]; cases b.2 <;> norm_num
  have hnorm (x : E3) : ‖r • x‖ = (1 / 4 : ℝ) * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, habs]
  have hr : r ≠ 0 := by intro h; rw [h, abs_zero] at habs; norm_num at habs
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hsmall : ‖r • x‖ < 1 / 4 := by
      rw [hnorm]
      have h := mem_ball_zero_iff.mp hx
      linarith
    refine ⟨⟨r • x, by linarith⟩, hsmall, ?_⟩
    exact (C.capBallChart_apply b x (by change ‖r • x‖ < 1; linarith)).symm
  · rintro ⟨x, hx, rfl⟩
    change ‖x.val‖ < 1 / 4 at hx
    let v : E3 := r⁻¹ • x.val
    have hv : r • v = x.val := by simp [v, smul_smul, hr]
    have hvnorm : ‖v‖ < 1 := by
      have h := hnorm v
      rw [hv] at h
      change ‖x.val‖ < 1 / 4 at hx
      linarith
    refine ⟨v, mem_ball_zero_iff.mpr hvnorm, ?_⟩
    rw [C.capBallChart_apply b v (by change ‖r • v‖ < 1; rw [hv]; linarith)]
    apply congrArg (C.cap b)
    exact Subtype.ext hv

theorem core_union_capAnnuli_eq_compl_capBallChart :
    range C.coreInclusion ∪ ⋃ b, range (C.capAnnulusMap b) =
      (⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ := by
  simp_rw [C.capBallChart_image_ball]
  ext y
  constructor
  · intro hy hsmall
    obtain ⟨b, x, hx, hxy⟩ := Set.mem_iUnion.mp hsmall
    rcases hy with hcore | hann
    · have hcore' : C.cap b x ∈ range C.coreInclusion := hxy.symm ▸ hcore
      obtain ⟨z, hz⟩ := C.eq_sphereToClosedCell_of_cap_mem_coreImage b hcore'
      have hn := congrArg (fun w : ClosedCell 3 => ‖w.val‖) hz
      change ‖z.val‖ = ‖x.val‖ at hn
      rw [norm_eq_of_mem_sphere] at hn
      change ‖x.val‖ < 1 / 4 at hx
      linarith
    · obtain ⟨b', hb'⟩ := mem_iUnion.mp hann
      rw [C.range_capAnnulusMap] at hb'
      obtain ⟨x', hx', hx'y⟩ := hb'
      by_cases hbb : b = b'
      · subst b'
        have heq := (C.cap_embedding b).isEmbedding.injective (hxy.trans hx'y.symm)
        rw [heq] at hx
        exact not_lt_of_ge (show 1 / 4 ≤ ‖x'.val‖ from hx') (show ‖x'.val‖ < 1 / 4 from hx)
      · exact Set.disjoint_left.mp (C.cap_disjoint hbb) ⟨x, hxy⟩ ⟨x', hx'y⟩
  · intro hy
    have hex : y ∈ range C.coreInclusion ∪ ⋃ b, range (C.cap b) := by rw [C.exhaustive]; trivial
    rcases hex with h | h
    · exact Or.inl h
    · obtain ⟨b, x, hx⟩ := mem_iUnion.mp h
      refine Or.inr (mem_iUnion.mpr ⟨b, ?_⟩)
      rw [C.range_capAnnulusMap]
      refine ⟨x, ?_, hx⟩
      change 1 / 4 ≤ ‖x.val‖
      apply le_of_not_gt
      intro hsmall
      exact hy (mem_iUnion.mpr ⟨b, x, hsmall, hx⟩)

def puncturedCappingHomeomorph : C.PuncturedCapping ≃ₜ
    ((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier) :=
  C.capAnnuliHomeomorph.trans (Homeomorph.setCongr C.core_union_capAnnuli_eq_compl_capBallChart)

@[simp] theorem puncturedCappingHomeomorph_core (x : range C.coreInclusion) :
    (C.puncturedCappingHomeomorph (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
      C.capAnnuliAttachingMap x)).val = x.val := rfl

@[simp] theorem puncturedCappingHomeomorph_annulus (b : T.Boundary) (q : Annulus) :
    (C.puncturedCappingHomeomorph (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
      C.capAnnuliAttachingMap ⟨b, q⟩)).val = C.capAnnulusMap b q := rfl

end DifferentialGeometry.Topology.SphericalCapping
