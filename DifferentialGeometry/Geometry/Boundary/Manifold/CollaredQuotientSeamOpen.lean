import DifferentialGeometry.Geometry.Boundary.Manifold.CollaredQuotientSeamRegion

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

def seamChartOpen [IsManifold I 1 X] (G : CollaredGluing I X ι) (i : ι) :
    C(↥(G.left i).carrier × ↥(Ioo (-(G.ε i)) (G.ε i)), Quotient G.toBoundaryGluing.setoid) where
  toFun p := G.seamChart i (p.1, ⟨(p.2 : ℝ), le_of_lt p.2.2.1, le_of_lt p.2.2.2⟩)
  continuous_toFun := (G.seamChart i).continuous.comp (by fun_prop)

theorem seamChartOpen_apply [IsManifold I 1 X] (G : CollaredGluing I X ι) (i : ι)
    (p : ↥(G.left i).carrier × ↥(Ioo (-(G.ε i)) (G.ε i))) :
    G.seamChartOpen i p
      = G.seamChart i (p.1, ⟨(p.2 : ℝ), le_of_lt p.2.2.1, le_of_lt p.2.2.2⟩) := rfl

theorem seamChartOpen_apply_of_nonneg [IsManifold I 1 X] (G : CollaredGluing I X ι) (i : ι)
    (p : ↥(G.left i).carrier × ↥(Ioo (-(G.ε i)) (G.ε i))) (hp : 0 ≤ (p.2 : ℝ)) :
    G.seamChartOpen i p = Quotient.mk'' (G.collarRight i (G.attaching i p.1,
      ⟨(p.2 : ℝ), hp, le_of_lt p.2.2.2⟩)) := by
  rw [seamChartOpen_apply]
  exact G.seamChart_apply_of_nonneg i _ hp

theorem seamChartOpen_apply_of_nonpos [IsManifold I 1 X] (G : CollaredGluing I X ι) (i : ι)
    (p : ↥(G.left i).carrier × ↥(Ioo (-(G.ε i)) (G.ε i))) (hp : (p.2 : ℝ) ≤ 0) :
    G.seamChartOpen i p = Quotient.mk'' (G.collarLeft i (p.1,
      ⟨-(p.2 : ℝ), neg_nonneg.mpr hp, by linarith [p.2.2.1]⟩)) := by
  rw [seamChartOpen_apply]
  exact G.seamChart_apply_of_nonpos i _ hp

theorem seamChartOpen_zero (G : CollaredGluing I X ι) [IsManifold I 1 X] (i : ι)
    (z : ↥(G.left i).carrier) :
    G.seamChartOpen i (z, ⟨0, neg_lt_zero.mpr (G.ε_pos i), G.ε_pos i⟩)
      = Quotient.mk'' (z : X) := by
  rw [seamChartOpen_apply]
  exact G.seamChart_zero i z

def seamLeftParam (G : CollaredGluing I X ι) (i : ι) :
    ↥(G.left i).carrier × ↥(Ico (0 : ℝ) (G.ε i)) →
      ↥(G.left i).carrier × ↥(Ioo (-(G.ε i)) (G.ε i)) :=
  fun q => (q.1, ⟨-(q.2 : ℝ), by linarith [q.2.2.2], by linarith [q.2.2.1, G.ε_pos i]⟩)

def seamRightParam (G : CollaredGluing I X ι) (i : ι) :
    ↥(G.right i).carrier × ↥(Ico (0 : ℝ) (G.ε i)) →
      ↥(G.left i).carrier × ↥(Ioo (-(G.ε i)) (G.ε i)) :=
  fun q => ((G.attaching i).symm q.1, ⟨(q.2 : ℝ), by linarith [q.2.2.1, G.ε_pos i],
    by linarith [q.2.2.2]⟩)

theorem continuous_seamLeftParam (G : CollaredGluing I X ι) (i : ι) :
    Continuous (G.seamLeftParam i) := by
  change Continuous (fun q : ↥(G.left i).carrier × ↥(Ico (0 : ℝ) (G.ε i)) =>
      ((q.1, ⟨-(q.2 : ℝ), by linarith [q.2.2.2], by linarith [q.2.2.1, G.ε_pos i]⟩) :
        ↥(G.left i).carrier × ↥(Ioo (-(G.ε i)) (G.ε i))))
  fun_prop

theorem continuous_seamRightParam (G : CollaredGluing I X ι) (i : ι) :
    Continuous (G.seamRightParam i) := by
  change Continuous (fun q : ↥(G.right i).carrier × ↥(Ico (0 : ℝ) (G.ε i)) =>
      (((G.attaching i).symm q.1, ⟨(q.2 : ℝ), by linarith [q.2.2.1, G.ε_pos i],
        by linarith [q.2.2.2]⟩) :
        ↥(G.left i).carrier × ↥(Ioo (-(G.ε i)) (G.ε i))))
  fun_prop

theorem seamLeftParam_zero (G : CollaredGluing I X ι) (i : ι) (z : ↥(G.left i).carrier) :
    G.seamLeftParam i (z, ⟨0, le_rfl, G.ε_pos i⟩)
      = (z, ⟨0, neg_lt_zero.mpr (G.ε_pos i), G.ε_pos i⟩) := by
  refine Prod.ext rfl (Subtype.ext ?_)
  change -(0 : ℝ) = 0
  simp

theorem seamRightParam_zero (G : CollaredGluing I X ι) (i : ι) (w : ↥(G.right i).carrier) :
    G.seamRightParam i (w, ⟨0, le_rfl, G.ε_pos i⟩)
      = ((G.attaching i).symm w, ⟨0, neg_lt_zero.mpr (G.ε_pos i), G.ε_pos i⟩) := by
  refine Prod.ext rfl (Subtype.ext rfl)

theorem seamRightParam_attaching (G : CollaredGluing I X ι) (i : ι)
    (z : ↥(G.left i).carrier) (s : ↥(Ico (0 : ℝ) (G.ε i))) :
    G.seamRightParam i (G.attaching i z, s)
      = (z, ⟨(s : ℝ), by linarith [s.2.1, G.ε_pos i], by linarith [s.2.2]⟩) := by
  refine Prod.ext ?_ (Subtype.ext rfl)
  change (G.attaching i).symm (G.attaching i z) = z
  simp

theorem collarLeftOpen_zero (G : CollaredGluing I X ι) (i : ι) (z : ↥(G.left i).carrier) :
    G.collarLeftOpen i (z, ⟨0, le_rfl, G.ε_pos i⟩) = (z : X) := by
  have h : G.collarLeftOpen i (z, ⟨0, le_rfl, G.ε_pos i⟩)
      = G.collarLeft i (z, ⟨0, le_rfl, (G.ε_pos i).le⟩) := rfl
  rw [h, G.collarLeft_zero]

theorem collarRightOpen_zero (G : CollaredGluing I X ι) (i : ι) (w : ↥(G.right i).carrier) :
    G.collarRightOpen i (w, ⟨0, le_rfl, G.ε_pos i⟩) = (w : X) := by
  have h : G.collarRightOpen i (w, ⟨0, le_rfl, G.ε_pos i⟩)
      = G.collarRight i (w, ⟨0, le_rfl, (G.ε_pos i).le⟩) := rfl
  rw [h, G.collarRight_zero]

theorem seamChartOpen_seamLeftParam (G : CollaredGluing I X ι) [IsManifold I 1 X] (i : ι)
    (q : ↥(G.left i).carrier × ↥(Ico (0 : ℝ) (G.ε i))) :
    G.seamChartOpen i (G.seamLeftParam i q) = Quotient.mk'' (G.collarLeftOpen i q) := by
  have hnonpos : ((G.seamLeftParam i q).2 : ℝ) ≤ 0 := by
    change -(q.2 : ℝ) ≤ 0
    linarith [q.2.2.1]
  rw [G.seamChartOpen_apply_of_nonpos i (G.seamLeftParam i q) hnonpos]
  refine congrArg (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid)) ?_
  refine Eq.trans ?_ (Eq.symm (show G.collarLeft i (q.1,
      ⟨(q.2 : ℝ), q.2.2.1, le_of_lt q.2.2.2⟩) = G.collarLeftOpen i q from rfl))
  refine congrArg (G.collarLeft i) (Prod.ext rfl (Subtype.ext ?_))
  change -(-(q.2 : ℝ)) = (q.2 : ℝ)
  ring

theorem seamChartOpen_seamRightParam (G : CollaredGluing I X ι) [IsManifold I 1 X] (i : ι)
    (q : ↥(G.right i).carrier × ↥(Ico (0 : ℝ) (G.ε i))) :
    G.seamChartOpen i (G.seamRightParam i q) = Quotient.mk'' (G.collarRightOpen i q) := by
  have hnonneg : 0 ≤ ((G.seamRightParam i q).2 : ℝ) := by
    change 0 ≤ (q.2 : ℝ)
    exact q.2.2.1
  rw [G.seamChartOpen_apply_of_nonneg i (G.seamRightParam i q) hnonneg]
  refine congrArg (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid)) ?_
  refine Eq.trans ?_ (Eq.symm (show G.collarRight i (q.1,
      ⟨(q.2 : ℝ), q.2.2.1, le_of_lt q.2.2.2⟩) = G.collarRightOpen i q from rfl))
  refine congrArg (G.collarRight i) (Prod.ext ?_ (Subtype.ext rfl))
  change (G.attaching i) ((G.attaching i).symm q.1) = q.1
  simp

theorem range_seamChartOpen (G : CollaredGluing I X ι) [IsManifold I 1 X] (i : ι) :
    range (G.seamChartOpen i) = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) ''
        (range (G.collarLeftOpen i) ∪ range (G.collarRightOpen i)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨p, rfl⟩
    rcases lt_or_ge (p.2 : ℝ) 0 with ht | ht
    · refine ⟨G.collarLeftOpen i (p.1, ⟨-(p.2 : ℝ), neg_nonneg.mpr (le_of_lt ht),
          by linarith [p.2.2.1]⟩), Or.inl ⟨_, rfl⟩, ?_⟩
      rw [G.seamChartOpen_apply_of_nonpos i p (le_of_lt ht)]
      congr 1
    · refine ⟨G.collarRightOpen i (G.attaching i p.1, ⟨(p.2 : ℝ), ht, p.2.2.2⟩),
        Or.inr ⟨_, rfl⟩, ?_⟩
      rw [G.seamChartOpen_apply_of_nonneg i p ht]
      congr 1
  · rintro _ ⟨x, hx | hx, rfl⟩
    · obtain ⟨q, rfl⟩ := hx
      rcases lt_or_eq_of_le q.2.2.1 with hs | hs
      · refine ⟨(q.1, ⟨-(q.2 : ℝ), by linarith [q.2.2.2], by linarith [q.2.2.1, G.ε_pos i]⟩), ?_⟩
        rw [G.seamChartOpen_apply_of_nonpos i (q.1, ⟨-(q.2 : ℝ), by linarith [q.2.2.2],
          by linarith [q.2.2.1, G.ε_pos i]⟩) (by change -(q.2 : ℝ) ≤ 0; linarith [q.2.2.1])]
        congr 1
        rw [show G.collarLeftOpen i q = G.collarLeft i (q.1,
          ⟨(q.2 : ℝ), q.2.2.1, le_of_lt q.2.2.2⟩) from rfl]
        congr 1
        refine Prod.ext rfl (Subtype.ext ?_)
        change -(-(q.2 : ℝ)) = (q.2 : ℝ)
        ring
      · have hL : G.collarLeftOpen i q = (q.1 : X) := by
          rw [show q = (q.1, ⟨0, le_rfl, G.ε_pos i⟩) from Prod.ext rfl (Subtype.ext hs.symm),
            G.collarLeftOpen_zero i q.1]
        refine ⟨(q.1, ⟨0, neg_lt_zero.mpr (G.ε_pos i), G.ε_pos i⟩), ?_⟩
        rw [G.seamChartOpen_zero i q.1, hL]
    · obtain ⟨q, rfl⟩ := hx
      rcases lt_or_eq_of_le q.2.2.1 with hs | hs
      · refine ⟨((G.attaching i).symm q.1, ⟨(q.2 : ℝ), by linarith [q.2.2.1, G.ε_pos i],
          q.2.2.2⟩), ?_⟩
        rw [G.seamChartOpen_apply_of_nonneg i ((G.attaching i).symm q.1, ⟨(q.2 : ℝ),
          by linarith [q.2.2.1, G.ε_pos i], q.2.2.2⟩) (by change 0 ≤ (q.2 : ℝ); exact q.2.2.1)]
        congr 1
        rw [show G.collarRightOpen i q = G.collarRight i (q.1,
          ⟨(q.2 : ℝ), q.2.2.1, le_of_lt q.2.2.2⟩) from rfl]
        congr 1
        refine Prod.ext ?_ (Subtype.ext rfl)
        change (G.attaching i) ((G.attaching i).symm q.1) = q.1
        simp
      · have hR : G.collarRightOpen i q = (q.1 : X) := by
          rw [show q = (q.1, ⟨0, le_rfl, G.ε_pos i⟩) from Prod.ext rfl (Subtype.ext hs.symm),
            G.collarRightOpen_zero i q.1]
        refine ⟨((G.attaching i).symm q.1, ⟨0, neg_lt_zero.mpr (G.ε_pos i), G.ε_pos i⟩), ?_⟩
        rw [G.seamChartOpen_zero i ((G.attaching i).symm q.1), hR]
        have hstep : Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid)
            (((G.attaching i) ((G.attaching i).symm q.1)) : X)
            = Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) (((G.attaching i).symm q.1) : X) :=
          Quotient.sound' (G.toBoundaryGluing.rel_of_attaching i ((G.attaching i).symm q.1))
        simp only [Homeomorph.apply_symm_apply] at hstep
        exact hstep.symm

private theorem eq_of_rel_of_not_isBoundaryPoint (G : CollaredGluing I X ι) [IsManifold I 1 X]
    {x y : X} (hy : ¬ I.IsBoundaryPoint y) (h : (G.toBoundaryGluing).rel x y) : x = y := by
  rcases h with rfl | ⟨i, hx, hy'⟩
  · rfl
  · exact (hy (hy' ▸ G.block_subset_boundary i ((G.toBoundaryGluing).flip_mem_block hx))).elim

theorem isOpenEmbedding_seamChartOpen (G : CollaredGluing I X ι) [IsManifold I 1 X]
    (h : G.CollarOpenEmbedding) (i : ι) : IsOpenEmbedding (G.seamChartOpen i) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap (G.seamChartOpen i).continuous ?_ ?_
  · intro p q hpq
    have hpq' : G.seamChart i (p.1, ⟨(p.2 : ℝ), le_of_lt p.2.2.1, le_of_lt p.2.2.2⟩)
        = G.seamChart i (q.1, ⟨(q.2 : ℝ), le_of_lt q.2.2.1, le_of_lt q.2.2.2⟩) := hpq
    obtain ⟨h1, h2⟩ := Prod.mk.inj (G.seamChart_injective i hpq')
    have h2' := congrArg (fun t : ↥(Icc (-(G.ε i)) (G.ε i)) => (t : ℝ)) h2
    exact Prod.ext h1 (Subtype.ext (by simpa using h2'))
  · intro V hV
    have hL : IsOpen (G.collarLeftOpen i '' (G.seamLeftParam i ⁻¹' V)) :=
      (h.1 i).isOpenMap _ (hV.preimage (G.continuous_seamLeftParam i))
    have hR : IsOpen (G.collarRightOpen i '' (G.seamRightParam i ⁻¹' V)) :=
      (h.2 i).isOpenMap _ (hV.preimage (G.continuous_seamRightParam i))
    have hpre : Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) ⁻¹' (G.seamChartOpen i '' V)
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
          have heq := eq_of_rel_of_not_isBoundaryPoint G hnb hrel
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
          have heq := eq_of_rel_of_not_isBoundaryPoint G hnb hrel
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
    have hfin : IsOpen (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid) ⁻¹'
        (G.seamChartOpen i '' V)) := by
      rw [hpre]
      exact hL.union hR
    have hqu : IsQuotientMap (Quotient.mk'' (s₁ := G.toBoundaryGluing.setoid)) :=
      isQuotientMap_quotient_mk' (s := G.toBoundaryGluing.setoid)
    exact hqu.isCoinducing.isOpen_preimage.mp hfin

end CollaredGluing

section UnitInterval

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem unitIntervalCollaredGluing_isOpenEmbedding_seamChartOpen :
    IsOpenEmbedding (unitIntervalCollaredGluing.seamChartOpen 0) :=
  CollaredGluing.isOpenEmbedding_seamChartOpen unitIntervalCollaredGluing
    unitIntervalCollaredGluing_collarOpenEmbedding 0

theorem unitIntervalCollaredGluing_range_seamChartOpen_nonempty :
    (range (unitIntervalCollaredGluing.seamChartOpen 0)).Nonempty := by
  obtain ⟨z, hz⟩ := BoundaryComponent.carrier_nonempty (unitIntervalCollaredGluing.left 0)
  refine ⟨_, ⟨(⟨z, hz⟩, ⟨0, ?_, ?_⟩), rfl⟩⟩
  · rw [show unitIntervalCollaredGluing.ε 0 = (1 : ℝ) / 4 from rfl]
    norm_num
  · rw [show unitIntervalCollaredGluing.ε 0 = (1 : ℝ) / 4 from rfl]
    norm_num

end UnitInterval

end DifferentialGeometry.Geometry.Boundary
