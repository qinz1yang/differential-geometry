import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CoreDecomposition
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabClassification
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Interior
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
# The incidence lemma for orientable bases

Lane MD3. Let `D` be Morse data on an orientable base `B` and `K` the slab component of a saddle.
If both levels of `K` were connected, lane MD2's classification
`oneSaddleSlab_connectedLower_cases` would make `K` diffeomorphic, level-preservingly, either to
the slab of `negPantsHeight` (whose upper level is the two hole circles:
`not_isPreconnected_upper_of_negPants`) or to the Möbius slab of `mobiusHeight`; in the second
case the inverse diffeomorphism, read in `B` through `opensVal`, is a local diffeomorphism from
`MobiusBand` at every point of the critical level, which no oriented surface admits
(`false_of_mobius_slab`, via `SurfaceOrientation.not_mobius_localDiffeomorph`). Hence
`h11_of_orientable`, and `exists_planarDecomposition_core_of_shrink_orientable` is
`exists_planarDecomposition_core_of_shrink` without its incidence hypothesis.
-/

set_option autoImplicit false

noncomputable section
open Set Function TopologicalSpace Topology Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.CoreDecomposition

variable {B : CompactSurface.{u}}

section OpensVal

variable (N' : Opens (Ambient B))

def opensValPartialDiffeomorph (z₀ : N') :
    PartialDiffeomorph 𝓘(ℝ, E2) (SurfaceModel.model B.kind) N' B.Carrier ∞ where
  toFun := opensVal N'
  invFun := opensInv N' z₀
  source := univ
  target := opensRange N'
  map_source' := by intro z hz; exact ⟨z, rfl⟩
  map_target' := by intro y hy; exact mem_univ (opensInv N' z₀ y)
  left_inv' := by intro z hz; exact opensInv_opensVal N' z₀ z
  right_inv' := by intro y hy; exact opensVal_opensInv N' z₀ (y := y) hy
  open_source := isOpen_univ
  open_target := isOpen_opensRange N'
  contMDiffOn_toFun := (contMDiff_opensVal N').contMDiffOn
  contMDiffOn_invFun := contMDiffOn_opensInv N' z₀

theorem isLocalDiffeomorphAt_opensVal (z : N') :
    IsLocalDiffeomorphAt 𝓘(ℝ, E2) (SurfaceModel.model B.kind) ∞ (opensVal N') z :=
  (opensValPartialDiffeomorph N' z).isLocalDiffeomorphAt _ _ _ (mem_univ z)

end OpensVal

theorem finrank_real_prod_real : Module.finrank ℝ (ℝ × ℝ) = 2 := by
  rw [Module.finrank_prod, Module.finrank_self]

abbrev mobiusSlabAtlas : SmoothBoundaryAtlas 𝓘(ℝ, ℝ × ℝ) 2 (slabSet mobiusHeight 0 2) :=
  slabAtlas finrank_real_prod_real contMDiff_mobiusHeight zero_lt_two
    mobiusHeight_regular_endpoints

abbrev negPantsSlabAtlas : SmoothBoundaryAtlas 𝓘(ℝ, ℂ) 2 (slabSet negPantsHeight (-1) 0) :=
  slabAtlas Complex.finrank_real_complex contMDiff_negPantsHeight (by norm_num)
    negPantsHeight_regular_endpoints

section Mobius

variable {f : B.Carrier → ℝ} {a b : ℝ}
  (hf : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) ∞ f) (hab : a < b)
  (hreg : ∀ y, f y = a ∨ f y = b → mfderiv (SurfaceModel.model B.kind) 𝓘(ℝ, ℝ) f y ≠ 0)
  (x₀ : Ambient B)

theorem mem_interior_slabSet_of_mem_Ioo {N : Type*} [TopologicalSpace N] {g : N → ℝ}
    (hg : Continuous g) {c d : ℝ} (hcd : c ≤ d) {z : N} (hz : g z ∈ Ioo c d) :
    z ∈ interior (slabSet g c d) := by
  refine interior_mono ?_ ((isOpen_Ioo.preimage hg).mem_nhds hz |> mem_interior_iff_mem_nhds.mpr)
  intro w hw
  exact (mem_slabSet_iff hcd w).mpr (Ioo_subset_Icc_self hw)

theorem false_of_mobius_slab
    (o : ManifoldOrientation (SurfaceModel.model B.kind) B.Carrier 2)
    (e : letI := (pieceAtlas hf hab hreg x₀).toChartedSpace
      letI := mobiusSlabAtlas.toChartedSpace
      slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯
        slabSet mobiusHeight 0 2)
    (he : ∀ x : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b,
      (pieceFun f (componentOpens hf hab hreg x₀) x = a ↔ mobiusHeight (e x) = 0) ∧
      (pieceFun f (componentOpens hf hab hreg x₀) x = b ↔ mobiusHeight (e x) = 2)) :
    False := by
  let := (pieceAtlas hf hab hreg x₀).toChartedSpace
  have := (pieceAtlas hf hab hreg x₀).isManifold
  let := mobiusSlabAtlas.toChartedSpace
  have := mobiusSlabAtlas.isManifold
  let N' := componentOpens hf hab hreg x₀
  let g : slabSet mobiusHeight 0 2 → B.Carrier := fun w => opensVal N' (e.symm w).val
  open Classical in
  let q : MobiusBand → B.Carrier := fun y =>
    if hy : y ∈ slabSet mobiusHeight 0 2 then g ⟨y, hy⟩ else ambientVal x₀
  have hq : ∀ y, mobiusHeight y = 1 →
      IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) (SurfaceModel.model B.kind) ∞ q y := by
    intro y hy1
    have hyI : mobiusHeight y ∈ Ioo (0 : ℝ) 2 := by rw [hy1]; norm_num
    have hyint : y ∈ interior (slabSet mobiusHeight 0 2) :=
      mem_interior_slabSet_of_mem_Ioo contMDiff_mobiusHeight.continuous zero_le_two hyI
    have hyS : y ∈ slabSet mobiusHeight 0 2 := interior_subset hyint
    let PD := mobiusSlabAtlas.interiorPartialDiffeomorph ⟨y, hyS⟩
    have hPDsymm : ∀ y' (hy' : y' ∈ interior (slabSet mobiusHeight 0 2)),
        PD.symm y' = ⟨y', interior_subset hy'⟩ := by
      intro y' hy'
      apply Subtype.ext
      exact PD.right_inv hy'
    have hPD : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) (𝓡∂ 2) ∞ PD.symm y :=
      PD.symm.isLocalDiffeomorphAt _ _ _ hyint
    set w : slabSet mobiusHeight 0 2 := ⟨y, hyS⟩
    have hw : PD.symm y = w := hPDsymm y hyint
    have hwI : pieceFun f N' (e.symm w).val ∈ Ioo a b := by
      have hmem := (mem_slabSet_iff hab.le _).mp (e.symm w).2
      have hea := (he (e.symm w)).1
      have heb := (he (e.symm w)).2
      rw [e.apply_symm_apply] at hea heb
      have hw1 : mobiusHeight w = 1 := hy1
      refine ⟨lt_of_le_of_ne hmem.1 fun h => ?_, lt_of_le_of_ne hmem.2 fun h => ?_⟩
      · have := hea.mp h.symm
        rw [hw1] at this
        norm_num at this
      · have := heb.mp h
        rw [hw1] at this
        norm_num at this
    have hint : (e.symm w).val ∈ interior (slabSet (pieceFun f N') a b) :=
      mem_interior_slabSet_of_mem_Ioo (contMDiff_pieceFun hf N').continuous hab.le hwI
    have hg : IsLocalDiffeomorphAt (𝓡∂ 2) (SurfaceModel.model B.kind) ∞ g w := by
      have h1 : IsLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ e.symm w := e.symm.isLocalDiffeomorph w
      have h2 := (pieceAtlas hf hab hreg x₀).isLocalDiffeomorphAt_subtype_val hint
      have h3 := isLocalDiffeomorphAt_opensVal N' (e.symm w).val
      exact (h1.comp _ _ h2).comp _ _ h3
    have hcomp := hPD.comp (SurfaceModel.model B.kind) B.Carrier (hw ▸ hg)
    refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ hcomp
    filter_upwards [isOpen_interior.mem_nhds hyint] with y' hy'
    change q y' = g (PD.symm y')
    rw [hPDsymm y' hy']
    simp only [q, dite_eq_left (interior_subset hy')]
  let o' : DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SurfaceOrientation
      (SurfaceModel.model B.kind) B.Carrier := ⟨o.orientation, o.locally_constant⟩
  exact SurfaceOrientation.not_mobius_localDiffeomorph o' q hq

theorem not_isPreconnected_upper_of_negPants
    (e : letI := (pieceAtlas hf hab hreg x₀).toChartedSpace
      letI := negPantsSlabAtlas.toChartedSpace
      slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯
        slabSet negPantsHeight (-1) 0)
    (he : ∀ x : slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b,
      (pieceFun f (componentOpens hf hab hreg x₀) x = a ↔ negPantsHeight (e x) = -1) ∧
      (pieceFun f (componentOpens hf hab hreg x₀) x = b ↔ negPantsHeight (e x) = 0)) :
    ¬ IsPreconnected (pieceFun f (componentOpens hf hab hreg x₀) ⁻¹' {b}) := by
  let := (pieceAtlas hf hab hreg x₀).toChartedSpace
  let := negPantsSlabAtlas.toChartedSpace
  intro hpre
  let S := slabSet (pieceFun f (componentOpens hf hab hreg x₀)) a b
  let T : Set S := Subtype.val ⁻¹' (pieceFun f (componentOpens hf hab hreg x₀) ⁻¹' {b})
  have hT : IsPreconnected T := by
    have himg : Subtype.val '' T = pieceFun f (componentOpens hf hab hreg x₀) ⁻¹' {b} := by
      refine image_preimage_eq_of_subset fun z hz => ⟨⟨z, ?_⟩, rfl⟩
      exact (mem_slabSet_iff hab.le z).mpr ⟨by rw [hz]; exact hab.le, by rw [hz]⟩
    rw [← himg] at hpre
    exact Topology.IsInducing.subtypeVal.isPreconnected_image.mp hpre
  have himg : Subtype.val '' (e '' T) = negPantsHeight ⁻¹' {0} := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact (he x).2.mp hx
    · intro hy
      have hyS : y ∈ slabSet negPantsHeight (-1) 0 :=
        (mem_slabSet_iff (by norm_num) y).mpr ⟨by rw [hy]; norm_num, by rw [hy]⟩
      refine ⟨⟨y, hyS⟩, ⟨e.symm ⟨y, hyS⟩, ?_, e.apply_symm_apply _⟩, rfl⟩
      have h := (he (e.symm ⟨y, hyS⟩)).2
      rw [e.apply_symm_apply] at h
      exact h.mpr hy
  have hpre' : IsPreconnected (negPantsHeight ⁻¹' {0}) := by
    rw [← himg]
    exact (hT.image _ e.continuous.continuousOn).image _ continuous_subtype_val.continuousOn
  exact not_isPreconnected_negPantsHeight_zero hpre'

end Mobius

section Orientable

variable (D : BaseMorseData B)

theorem h11_of_orientable (o : ManifoldOrientation (SurfaceModel.model B.kind) B.Carrier 2) :
    ∀ (i : Fin D.m) (p : B.Carrier), p ∈ D.crit →
      sigNeg (chartHessianAt
        (fun y => D.f ((extChartAt (SurfaceModel.model B.kind) p).symm y))
        (extChartAt (SurfaceModel.model B.kind) p p)) = 1 →
      D.f p ∈ Ioo (D.level i.castSucc) (D.level i.succ) →
      ¬ IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        p ∩ D.f ⁻¹' {D.level i.castSucc}) ∨
      ¬ IsPreconnected (connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        p ∩ D.f ⁻¹' {D.level i.succ}) := by
  intro i p hp hidx hpi
  by_contra hcon
  push Not at hcon
  obtain ⟨hlow, hup⟩ := hcon
  have hab := level_castSucc_lt_succ D i
  have hreg := slab_regular D i
  have hint := slab_interior D i
  let x₀ : Ambient B := toAmbient ⟨p, hint p hpi.1.le⟩
  have hx₀p : ambientVal x₀ = p := rfl
  have hpK : p ∈ connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
      (ambientVal x₀) := mem_connectedComponentIn (Ioo_subset_Icc_self hpi)
  have hlow' := (isPreconnected_pieceLevel_iff D i x₀ (Or.inl rfl)).mpr
    (by rw [hx₀p]; exact hlow)
  have hup' := (isPreconnected_pieceLevel_iff D i x₀ (Or.inr rfl)).mpr
    (by rw [hx₀p]; exact hup)
  obtain ⟨p', hp', hpi', hnd', huniq'⟩ := saddle_data D i hp hpK
  have hidx' : sigNeg (chartHessianAt
      (fun y => pieceFun D.f (slabOpens D i x₀) ((extChartAt 𝓘(ℝ, E2) p').symm y))
      (extChartAt 𝓘(ℝ, E2) p' p')) = 1 := by
    rw [chartHessianAt_piece_eq, hp']
    exact hidx
  have hx₀S : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ) :=
    (mem_slabSet_iff hab.le x₀).mpr (Ioo_subset_Icc_self hpi)
  have hcpt : IsCompact (pieceFun D.f (slabOpens D i x₀) ⁻¹'
      Icc (D.level i.castSucc) (D.level i.succ)) := by
    rw [← slabSet_eq hab.le]
    exact isCompact_pieceSlab D.smooth hab hreg hint x₀
  have hconn : IsConnected (pieceFun D.f (slabOpens D i x₀) ⁻¹'
      Icc (D.level i.castSucc) (D.level i.succ)) := by
    rw [← slabSet_eq hab.le]
    exact isConnected_pieceSlab D.smooth hab hreg hx₀S
  rcases oneSaddleSlab_connectedLower_cases 𝓘(ℝ, E2) finrank_euclideanSpace_fin
      (contMDiff_pieceFun D.smooth _) hab (pieceFun_regular D.smooth hreg _) hpi' hnd' hidx'
      huniq' hcpt hconn hlow' with ⟨e, he⟩ | ⟨e, he⟩
  · exact not_isPreconnected_upper_of_negPants D.smooth hab hreg x₀ e he hup'
  · exact false_of_mobius_slab D.smooth hab hreg x₀ o e he

theorem exists_planarDecomposition_core_of_shrink_orientable
    (o : ManifoldOrientation (SurfaceModel.model B.kind) B.Carrier 2) :
    ∃ D' : BaseMorseData B, D'.f = D.f ∧ D'.crit = D.crit ∧ D'.m = D.m ∧ D'.κ ≤ D.κ ∧
      (∀ i : Fin (D'.m + 1), ∃ j : Fin (D.m + 1), D'.level i = D.level j) ∧
      ∃ P : PlanarDecomposition D'.core,
        ∀ j l, (∀ c b, P.cutSide c b ≠ ⟨j, l⟩) →
          ∃ (x₀ : B.Carrier) (hx₀ : D'.f x₀ = D'.level 0)
            (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle), ∀ t s (hs : 0 ≤ s), s < 1 →
              (P.inclusion j ((P.piece j).collar l (t, halfPoint s hs))).val =
                Classical.choose (D'.exists_levelBicollar 0 hx₀) (σ t, s) :=
  exists_planarDecomposition_core_of_shrink D (h11_of_orientable D o)

end Orientable

end GC.Seifert.CoreDecomposition
