import DifferentialGeometry.Geometry.Boundary.Manifold.CollaredQuotientSeamOpen

open Set Function Topology
open scoped Manifold ContDiff

noncomputable section
set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type u} [TopologicalSpace X] [ChartedSpace H X]
variable {ι : Type v} [Finite ι]

namespace CollaredGluing

variable {G : CollaredGluing I X ι}

private theorem eq_of_rel_of_not_isBoundaryPoint (G : CollaredGluing I X ι) [IsManifold I 1 X]
    {x y : X} (hy : ¬ I.IsBoundaryPoint y) (h : (G.toBoundaryGluing).rel x y) : x = y := by
  rcases h with rfl | ⟨i, hx, hy'⟩
  · rfl
  · exact (hy (hy' ▸ G.block_subset_boundary i
      ((G.toBoundaryGluing).flip_mem_block hx))).elim

theorem quotientMk_preimage_seamChartOpen_image (G : CollaredGluing I X ι) [IsManifold I 1 X]
    (i : ι) (V : Set (↥(G.left i).carrier × ↥(Ioo (-(G.ε i)) (G.ε i)))) :
    Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) ⁻¹' (G.seamChartOpen i '' V)
      = (G.collarLeftOpen i '' (G.seamLeftParam i ⁻¹' V))
        ∪ (G.collarRightOpen i '' (G.seamRightParam i ⁻¹' V)) := by
  ext x
  constructor
  · rintro ⟨p, hpV, hpx⟩
    rcases lt_trichotomy (p.2 : ℝ) 0 with ht | ht | ht
    · have hx_eq : Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x
          = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (G.collarLeft i (p.1,
            ⟨-(p.2 : ℝ), neg_nonneg.mpr (le_of_lt ht), by linarith [p.2.2.1]⟩)) := by
        rw [← hpx, G.seamChartOpen_apply_of_nonpos i p (le_of_lt ht)]
      have hrel := (Quotient.eq'' (s₁ := G.toBoundaryGluing.setoid)).mp hx_eq
      have hnb : ¬ I.IsBoundaryPoint (G.collarLeft i (p.1, ⟨-(p.2 : ℝ),
          neg_nonneg.mpr (le_of_lt ht), by linarith [p.2.2.1]⟩)) :=
        G.collarLeft_inward i p.1 _ (by linarith)
      have heq : x = G.collarLeft i (p.1, ⟨-(p.2 : ℝ), neg_nonneg.mpr (le_of_lt ht),
          by linarith [p.2.2.1]⟩) :=
        eq_of_rel_of_not_isBoundaryPoint G hnb hrel
      refine Or.inl ⟨(p.1, ⟨-(p.2 : ℝ), neg_nonneg.mpr (le_of_lt ht),
        by linarith [p.2.2.1]⟩), ?_, heq.symm⟩
      have hq : G.seamLeftParam i (p.1, ⟨-(p.2 : ℝ), neg_nonneg.mpr (le_of_lt ht),
          by linarith [p.2.2.1]⟩) = p := by
        refine Prod.ext rfl (Subtype.ext ?_)
        change -(-(p.2 : ℝ)) = (p.2 : ℝ)
        ring
      simpa only [Set.mem_preimage, hq] using hpV
    · have hp_eq : p = (p.1, (⟨0, neg_lt_zero.mpr (G.ε_pos i), G.ε_pos i⟩ :
          ↥(Ioo (-(G.ε i)) (G.ε i)))) := Prod.ext rfl (Subtype.ext ht)
      have hpV' : (p.1, (⟨0, neg_lt_zero.mpr (G.ε_pos i), G.ε_pos i⟩ :
          ↥(Ioo (-(G.ε i)) (G.ε i)))) ∈ V := hp_eq ▸ hpV
      have hfp : G.seamChartOpen i p
          = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (G.attaching i p.1 : X) := by
        conv_lhs => rw [hp_eq]
        rw [G.seamChartOpen_zero i p.1]
        exact (Quotient.sound' (G.toBoundaryGluing.rel_of_attaching i p.1)).symm
      have hx_eq : Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x
          = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (G.attaching i p.1 : X) :=
        hpx.symm.trans hfp
      have hrel' : (G.toBoundaryGluing).rel (G.attaching i p.1 : X) x :=
        (Quotient.eq'' (s₁ := G.toBoundaryGluing.setoid)).mp hx_eq.symm
      rcases G.rel_iff_of_mem_block (Or.inr (G.attaching i p.1).2) hrel' with hxy | hxy
      · refine Or.inr ⟨(G.attaching i p.1, ⟨0, le_rfl, G.ε_pos i⟩), ?_, ?_⟩
        · simpa only [Set.mem_preimage, seamRightParam_attaching] using hpV'
        · rw [hxy, collarRightOpen_zero]
      · refine Or.inl ⟨(p.1, ⟨0, le_rfl, G.ε_pos i⟩), ?_, ?_⟩
        · simpa only [Set.mem_preimage, seamLeftParam_zero] using hpV'
        · exact (G.collarLeftOpen_zero i p.1).trans
            (((G.toBoundaryGluing).flip_attaching i p.1).symm.trans hxy.symm)
    · have hx_eq : Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) x
          = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (G.collarRight i (G.attaching i p.1,
            ⟨(p.2 : ℝ), le_of_lt ht, le_of_lt p.2.2.2⟩)) := by
        rw [← hpx, G.seamChartOpen_apply_of_nonneg i p (le_of_lt ht)]
      have hrel := (Quotient.eq'' (s₁ := G.toBoundaryGluing.setoid)).mp hx_eq
      have hnb : ¬ I.IsBoundaryPoint (G.collarRight i (G.attaching i p.1,
          ⟨(p.2 : ℝ), le_of_lt ht, le_of_lt p.2.2.2⟩)) :=
        G.collarRight_inward i (G.attaching i p.1) _ (by linarith)
      have heq : x = G.collarRight i (G.attaching i p.1,
          ⟨(p.2 : ℝ), le_of_lt ht, le_of_lt p.2.2.2⟩) :=
        eq_of_rel_of_not_isBoundaryPoint G hnb hrel
      refine Or.inr ⟨(G.attaching i p.1, ⟨(p.2 : ℝ), le_of_lt ht,
        p.2.2.2⟩), ?_, ?_⟩
      · have hq : G.seamRightParam i (G.attaching i p.1, ⟨(p.2 : ℝ), le_of_lt ht,
            p.2.2.2⟩) = p := by
          rw [seamRightParam_attaching]
        simpa only [Set.mem_preimage, hq] using hpV
      · exact heq.symm
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact ⟨G.seamLeftParam i q, hq, G.seamChartOpen_seamLeftParam i q⟩
    · exact ⟨G.seamRightParam i q, hq, G.seamChartOpen_seamRightParam i q⟩

abbrev seamStrip (G : CollaredGluing I X ι) (i : ι) :
    TopologicalSpace.Opens (↥(G.left i).carrier × ℝ) :=
  ⟨univ ×ˢ Ioo (-(G.ε i)) (G.ε i), isOpen_univ.prod isOpen_Ioo⟩

private instance seamStripNonempty (G : CollaredGluing I X ι) (i : ι) :
    Nonempty ↥(G.seamStrip i) :=
  let z : ↥(G.left i).carrier :=
    ⟨(BoundaryComponent.carrier_nonempty (G.left i)).choose,
      (BoundaryComponent.carrier_nonempty (G.left i)).choose_spec⟩
  ⟨⟨(z, 0), ⟨mem_univ _, ⟨neg_lt_zero.mpr (G.ε_pos i), G.ε_pos i⟩⟩⟩⟩

def seamParamHomeomorph (G : CollaredGluing I X ι) (i : ι) :
    ↥(G.seamStrip i) ≃ₜ (↥(G.left i).carrier × ↥(Ioo (-(G.ε i)) (G.ε i))) where
  toFun p := (p.1.1, ⟨p.1.2, p.2.2⟩)
  invFun p := ⟨(p.1, (p.2 : ℝ)), ⟨mem_univ _, p.2.2⟩⟩
  left_inv p := Subtype.ext (Prod.ext rfl rfl)
  right_inv p := Prod.ext rfl (Subtype.ext rfl)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem isOpenEmbedding_seamParamChart (G : CollaredGluing I X ι) [IsManifold I 1 X]
    (h : G.CollarOpenEmbedding) (i : ι) :
    IsOpenEmbedding (fun p : ↥(G.seamStrip i) =>
      G.seamChartOpen i (G.seamParamHomeomorph i p)) :=
  (G.isOpenEmbedding_seamChartOpen h i).comp (G.seamParamHomeomorph i).isOpenEmbedding

noncomputable def seamPiece (G : CollaredGluing I X ι) [IsManifold I 1 X]
    (h : G.CollarOpenEmbedding) (i : ι) :
    OpenPartialHomeomorph ↥(G.seamStrip i) (Quotient G.toBoundaryGluing.setoid) := by
  classical
  exact (G.isOpenEmbedding_seamParamChart h i).toOpenPartialHomeomorph
    (fun p => G.seamChartOpen i (G.seamParamHomeomorph i p))

theorem seamPiece_source (G : CollaredGluing I X ι) [IsManifold I 1 X]
    (h : G.CollarOpenEmbedding) (i : ι) : (G.seamPiece h i).source = univ :=
  IsOpenEmbedding.toOpenPartialHomeomorph_source _ _

theorem seamPiece_apply (G : CollaredGluing I X ι) [IsManifold I 1 X]
    (h : G.CollarOpenEmbedding) (i : ι) (p : ↥(G.seamStrip i)) :
    G.seamPiece h i p = G.seamChartOpen i (G.seamParamHomeomorph i p) :=
  congrFun (IsOpenEmbedding.toOpenPartialHomeomorph_apply _ _) p

theorem seamPiece_target (G : CollaredGluing I X ι) [IsManifold I 1 X]
    (h : G.CollarOpenEmbedding) (i : ι) :
    (G.seamPiece h i).target = range (G.seamChartOpen i) := by
  rw [seamPiece, IsOpenEmbedding.toOpenPartialHomeomorph_target]
  change range ((G.seamChartOpen i) ∘ (G.seamParamHomeomorph i)) = range (G.seamChartOpen i)
  rw [Set.range_comp, (G.seamParamHomeomorph i).surjective.range_eq, Set.image_univ]

theorem seamPiece_target_eq (G : CollaredGluing I X ι) [IsManifold I 1 X]
    (h : G.CollarOpenEmbedding) (i : ι) :
    (G.seamPiece h i).target = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) ''
      (range (G.collarLeftOpen i) ∪ range (G.collarRightOpen i)) := by
  rw [G.seamPiece_target h i, G.range_seamChartOpen i]

theorem seamPiece_symm_collarLeft (G : CollaredGluing I X ι) [IsManifold I 1 X]
    (h : G.CollarOpenEmbedding) (i : ι)
    (q : ↥(G.left i).carrier × ↥(Ico (0 : ℝ) (G.ε i))) :
    (G.seamPiece h i).symm (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid)
        (G.collarLeftOpen i q))
      = ⟨(q.1, -(q.2 : ℝ)), ⟨mem_univ _, ⟨by linarith [q.2.2.2],
          by linarith [q.2.2.1, G.ε_pos i]⟩⟩⟩ := by
  set p : ↥(G.seamStrip i) :=
    ⟨(q.1, -(q.2 : ℝ)), ⟨mem_univ _, ⟨by linarith [q.2.2.2],
      by linarith [q.2.2.1, G.ε_pos i]⟩⟩⟩ with hp
  have hparam : G.seamParamHomeomorph i p = G.seamLeftParam i q := by
    refine Prod.ext rfl (Subtype.ext rfl)
  have hpiece : G.seamPiece h i p = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid)
      (G.collarLeftOpen i q) := by
    rw [G.seamPiece_apply h i p, hparam, G.seamChartOpen_seamLeftParam i q]
  rw [← hpiece]
  exact OpenPartialHomeomorph.left_inv _ (Set.mem_univ p)

theorem seamPiece_symm_collarRight (G : CollaredGluing I X ι) [IsManifold I 1 X]
    (h : G.CollarOpenEmbedding) (i : ι)
    (q : ↥(G.right i).carrier × ↥(Ico (0 : ℝ) (G.ε i))) :
    (G.seamPiece h i).symm (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid)
        (G.collarRightOpen i q))
      = ⟨((G.attaching i).symm q.1, (q.2 : ℝ)), ⟨mem_univ _, ⟨by linarith [q.2.2.1, G.ε_pos i],
          by linarith [q.2.2.2]⟩⟩⟩ := by
  set p : ↥(G.seamStrip i) :=
    ⟨((G.attaching i).symm q.1, (q.2 : ℝ)), ⟨mem_univ _, ⟨by linarith [q.2.2.1, G.ε_pos i],
      by linarith [q.2.2.2]⟩⟩⟩ with hp
  have hparam : G.seamParamHomeomorph i p = G.seamRightParam i q := by
    refine Prod.ext ?_ (Subtype.ext rfl)
    change (G.attaching i).symm q.1 = (G.attaching i).symm q.1
    rfl
  have hpiece : G.seamPiece h i p = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid)
      (G.collarRightOpen i q) := by
    rw [G.seamPiece_apply h i p, hparam, G.seamChartOpen_seamRightParam i q]
  rw [← hpiece]
  exact OpenPartialHomeomorph.left_inv _ (Set.mem_univ p)

theorem boundaryManifold_prod_isInteriorPoint
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ X] (p : BoundaryManifold I X × ℝ) :
    (hI.boundaryI.prod 𝓘(ℝ, ℝ)).IsInteriorPoint p :=
  BoundarylessManifold.isInteriorPoint

end CollaredGluing

section UnitInterval

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem unitIntervalCollaredGluing_seamPiece_target_nonempty :
    (unitIntervalCollaredGluing.seamPiece unitIntervalCollaredGluing_collarOpenEmbedding 0).target.Nonempty := by
  obtain ⟨q, hq⟩ := unitIntervalCollaredGluing_range_seamChartOpen_nonempty
  exact ⟨q, by rwa [unitIntervalCollaredGluing.seamPiece_target
    unitIntervalCollaredGluing_collarOpenEmbedding 0]⟩

end UnitInterval

end DifferentialGeometry.Geometry.Boundary
