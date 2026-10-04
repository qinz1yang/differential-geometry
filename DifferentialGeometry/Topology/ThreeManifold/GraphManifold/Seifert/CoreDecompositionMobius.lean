import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.OneSidedSlab
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CoreDecompositionOrientable

/-!
# Decomposition of the core with one-sided pieces

Lane MD3, T5.
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

section Split

variable (D : BaseMorseData B)

structure SplitData (i : Fin D.m) (x₀ : Ambient B) where
  e : letI := (shiftAtlas (pieceAtlas D.smooth (level_castSucc_lt_succ D i) (slab_regular D i)
        x₀)).toChartedSpace
      letI := GC.Seifert.mobiusSlabAtlas.toChartedSpace
      slabSet (pieceFun D.f (slabOpens D i x₀)) (D.level i.castSucc) (D.level i.succ) ≃ₘ⟮𝓡∂ 2,
        𝓡∂ 2⟯ slabSet mobiusHeight 0 2
  he : ∀ x : slabSet (pieceFun D.f (slabOpens D i x₀)) (D.level i.castSucc) (D.level i.succ),
    (pieceFun D.f (slabOpens D i x₀) x = D.level i.castSucc ↔ mobiusHeight (e x) = 0) ∧
      (pieceFun D.f (slabOpens D i x₀) x = D.level i.succ ↔ mobiusHeight (e x) = 2)

theorem nonempty_slabPiece_or_split (i : Fin D.m) (x₀ : Ambient B) (hx₀ : x₀ ∈ slabS D i) :
    Nonempty (SlabPiece D i hx₀) ∨ Nonempty (SplitData D i x₀) := by
  have hab := level_castSucc_lt_succ D i
  have hreg := slab_regular D i
  have hint := slab_interior D i
  by_cases hcrit : ∃ p ∈ D.crit, p ∈ connectedComponentIn
      (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀)
  · obtain ⟨p, hp, hpK⟩ := hcrit
    by_cases hidx : sigNeg (chartHessianAt
        (fun y => D.f ((extChartAt (SurfaceModel.model B.kind) p).symm y))
        (extChartAt (SurfaceModel.model B.kind) p p)) = 1
    · by_cases hdis : ¬ IsPreconnected (pieceFun D.f (slabOpens D i x₀) ⁻¹' {D.level i.castSucc}) ∨
          ¬ IsPreconnected (pieceFun D.f (slabOpens D i x₀) ⁻¹' {D.level i.succ})
      · exact Or.inl (nonempty_slabPiece_of_saddle D i hx₀ hp hidx hpK hdis)
      · right
        have hlow : IsPreconnected (pieceFun D.f (slabOpens D i x₀) ⁻¹' {D.level i.castSucc}) := by
          by_contra h
          exact hdis (Or.inl h)
        have hup : IsPreconnected (pieceFun D.f (slabOpens D i x₀) ⁻¹' {D.level i.succ}) := by
          by_contra h
          exact hdis (Or.inr h)
        obtain ⟨p', hp', hpi', hnd', huniq'⟩ := saddle_data D i hp hpK
        have hidx' : sigNeg (chartHessianAt
            (fun y => pieceFun D.f (slabOpens D i x₀) ((extChartAt 𝓘(ℝ, E2) p').symm y))
            (extChartAt 𝓘(ℝ, E2) p' p')) = 1 := by
          rw [chartHessianAt_piece_eq, hp']
          exact hidx
        have hcpt : IsCompact (pieceFun D.f (slabOpens D i x₀) ⁻¹'
            Icc (D.level i.castSucc) (D.level i.succ)) := by
          rw [← slabSet_eq hab.le]
          exact isCompact_pieceSlab D.smooth hab hreg hint x₀
        have hconn : IsConnected (pieceFun D.f (slabOpens D i x₀) ⁻¹'
            Icc (D.level i.castSucc) (D.level i.succ)) := by
          rw [← slabSet_eq hab.le]
          exact isConnected_pieceSlab D.smooth hab hreg hx₀
        rcases oneSaddleSlab_connectedLower_cases 𝓘(ℝ, E2) finrank_euclideanSpace_fin
            (contMDiff_pieceFun D.smooth _) hab (pieceFun_regular D.smooth hreg _) hpi' hnd' hidx'
            huniq' hcpt hconn hlow with ⟨e, he⟩ | ⟨e, he⟩
        · exact absurd hup (not_isPreconnected_upper_of_negPants D.smooth hab hreg x₀ e he)
        · let Cp := pieceAtlas D.smooth hab hreg x₀
          let Cs := shiftAtlas Cp
          let Dsh := Cp.diffeomorphOfAmbient Cs (Diffeomorph.refl 𝓘(ℝ, E2) (slabOpens D i x₀) ∞)
            (fun z => Iff.rfl)
          let DshInv := @Diffeomorph.symm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cp.toChartedSpace _ _
            Cs.toChartedSpace _ Dsh
          exact ⟨⟨@Diffeomorph.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Cs.toChartedSpace _ _ Cp.toChartedSpace _ _
            GC.Seifert.mobiusSlabAtlas.toChartedSpace _ DshInv e, he⟩⟩
    · exact Or.inl (nonempty_slabPiece_of_extremum D i hx₀ hp hidx hpK)
  · refine Or.inl (nonempty_slabPiece_of_regular D i hx₀ fun y hy hz =>
      hcrit ⟨ambientVal y, ?_, ?_⟩)
    · exact (D.mem_crit _).mpr hz
    · rw [← ambientVal_image_slabComponent]
      exact mem_image_of_mem _ hy

end Split

section Circles

variable (D : BaseMorseData B)

structure LevelCircles (i : Fin D.m) (x₀ : Ambient B) where
  k : ℕ
  lev : Fin k → Bool
  γ : Fin k → Circle →
    slabSet (pieceFun D.f (slabOpens D i x₀)) (D.level i.castSucc) (D.level i.succ)
  continuous_γ : ∀ l, Continuous (γ l)
  level : ∀ l t, D.f (opensVal _ (γ l t).val) =
    if lev l then D.level i.succ else D.level i.castSucc
  disjoint : ∀ l l', l ≠ l' → ∀ t t', γ l t ≠ γ l' t'
  cover : ∀ w : slabSet (pieceFun D.f (slabOpens D i x₀)) (D.level i.castSucc) (D.level i.succ),
    D.f (opensVal _ w.val) = D.level i.castSucc ∨ D.f (opensVal _ w.val) = D.level i.succ →
      ∃ l t, γ l t = w

namespace LevelCircles

variable {D} {i : Fin D.m} {x₀ : Ambient B} (lc : LevelCircles D i x₀)

def gam (l : Fin lc.k) (t : Circle) : B.Carrier := opensVal _ (lc.γ l t).val

theorem continuous_gam (l : Fin lc.k) : Continuous (lc.gam l) :=
  (isOpenEmbedding_opensVal _).continuous.comp (continuous_subtype_val.comp (lc.continuous_γ l))

theorem disjoint_range_gam {l l' : Fin lc.k} (hll : l ≠ l') :
    Disjoint (range (lc.gam l)) (range (lc.gam l')) := by
  rw [Set.disjoint_left]
  rintro z ⟨t, rfl⟩ ⟨t', ht'⟩
  have h1 : lc.γ l' t' = lc.γ l t :=
    Subtype.val_injective ((isOpenEmbedding_opensVal _).injective ht')
  exact lc.disjoint l l' hll t t' h1.symm

theorem exists_gam_of_level
    (w : slabSet (pieceFun D.f (slabOpens D i x₀)) (D.level i.castSucc) (D.level i.succ))
    (hw : D.f (opensVal _ w.val) = D.level i.castSucc ∨ D.f (opensVal _ w.val) = D.level i.succ) :
    ∃ l t, lc.gam l t = opensVal _ w.val := by
  obtain ⟨l, t, h⟩ := lc.cover w hw
  exact ⟨l, t, by rw [gam, h]⟩

theorem range_gam (l : Fin lc.k) :
    range (lc.gam l) = connectedComponentIn
      (D.f ⁻¹' {if lc.lev l then D.level i.succ else D.level i.castSucc}) (lc.gam l 1) := by
  set L := if lc.lev l then D.level i.succ else D.level i.castSucc
  have hab := level_castSucc_lt_succ D i
  have hLab : L = D.level i.castSucc ∨ L = D.level i.succ := by
    by_cases h : lc.lev l <;> simp [L, h]
  have hpre : IsPreconnected (range (lc.gam l)) := isPreconnected_range (lc.continuous_gam l)
  apply Subset.antisymm
  · refine hpre.subset_connectedComponentIn (mem_range_self 1) ?_
    rintro z ⟨t, rfl⟩
    exact lc.level l t
  · set C := connectedComponentIn (D.f ⁻¹' {L}) (lc.gam l 1)
    have hC : IsPreconnected C := isPreconnected_connectedComponentIn
    have hCX : C ⊆ opensVal _ '' slabSet (pieceFun D.f (slabOpens D i x₀))
        (D.level i.castSucc) (D.level i.succ) := by
      rw [opensVal_image_pieceSlab D.smooth hab (slab_regular D i) (slab_interior D i) x₀]
      have hγX : lc.gam l 1 ∈ connectedComponentIn
          (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀) := by
        rw [← opensVal_image_pieceSlab D.smooth hab (slab_regular D i) (slab_interior D i) x₀]
        exact mem_image_of_mem _ (lc.γ l 1).2
      rw [connectedComponentIn_eq hγX]
      refine hC.subset_connectedComponentIn (mem_connectedComponentIn ?_) ?_
      · change D.f (lc.gam l 1) = L
        exact lc.level l 1
      · intro z hz
        have hzL' : z ∈ D.f ⁻¹' {L} := connectedComponentIn_subset (D.f ⁻¹' {L}) _ hz
        have hzL : D.f z = L := hzL'
        rcases hLab with h | h <;> rw [h] at hzL <;> rw [mem_preimage, hzL] <;>
          exact ⟨by linarith, by linarith⟩
    have hcover : C ⊆ range (lc.gam l) ∪
        ⋃ l' ∈ ({l}ᶜ : Set (Fin lc.k)), range (lc.gam l') := by
      intro z hz
      obtain ⟨w, hwX, hw⟩ := hCX hz
      have hzL' : z ∈ D.f ⁻¹' {L} := connectedComponentIn_subset (D.f ⁻¹' {L}) _ hz
      have hzL : D.f z = L := hzL'
      obtain ⟨l', t', hl't'⟩ := lc.exists_gam_of_level ⟨w, hwX⟩
        (by change D.f (opensVal _ w) = _ ∨ D.f (opensVal _ w) = _; rw [hw, hzL]; exact hLab)
      by_cases hl' : l' = l
      · subst hl'
        exact Or.inl ⟨t', hl't'.trans hw⟩
      · exact Or.inr (mem_biUnion hl' ⟨t', hl't'.trans hw⟩)
    have hclosed (l' : Fin lc.k) : IsClosed (range (lc.gam l')) :=
      (isCompact_range (lc.continuous_gam l')).isClosed
    have hdisj : C ∩ (range (lc.gam l) ∩
        ⋃ l' ∈ ({l}ᶜ : Set (Fin lc.k)), range (lc.gam l')) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun z hz => ?_
      obtain ⟨-, hzA, hzV⟩ := hz
      obtain ⟨l', hl', hz'⟩ := mem_iUnion₂.mp hzV
      exact Set.disjoint_left.mp (lc.disjoint_range_gam (Ne.symm hl')) hzA hz'
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hC _ _ (hclosed l)
      ((Set.toFinite _).isClosed_biUnion (by intro l' hl'; exact hclosed l')) hcover hdisj
      with h | h
    · exact h
    · exfalso
      have h1 : lc.gam l 1 ∈ C := mem_connectedComponentIn (lc.level l 1)
      obtain ⟨l', hl', hz'⟩ := mem_iUnion₂.mp (h h1)
      exact Set.disjoint_left.mp (lc.disjoint_range_gam (Ne.symm hl')) (mem_range_self 1) hz'

end LevelCircles

def SlabPiece.levelCircles {i : Fin D.m} {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp : SlabPiece D i hx₀) : LevelCircles D i x₀ where
  k := sp.k
  lev := sp.lev
  γ l t := sp.e (sp.P.collar l (t, halfZero))
  continuous_γ l := by
    have hcol : Continuous fun t : Circle => sp.P.collar l (t, halfZero) := by
      refine (sp.P.collar l).contMDiffOn.continuousOn.comp_continuous
        (continuous_id.prodMk continuous_const) fun t => ?_
      rw [sp.P.source_eq l]
      exact halfZero_mem_circleCollarSource t
    exact sp.e.continuous.comp hcol
  level l t := sp.hlev l t
  disjoint l l' hll t t' h := by
    have hd := Set.disjoint_left.mp (disjoint_range_pieceGamma D i sp hll) (mem_range_self t)
    exact hd ⟨t', by rw [pieceGamma, pieceGamma, h]⟩
  cover w hw := by
    obtain ⟨l, t, h⟩ := exists_pieceGamma_of_level D i sp w hw
    exact ⟨l, t, Subtype.ext ((isOpenEmbedding_opensVal _).injective h)⟩

theorem SlabPiece.levelCircles_gam {i : Fin D.m} {x₀ : Ambient B}
    {hx₀ : x₀ ∈ slabSet (ambientFun D.f) (D.level i.castSucc) (D.level i.succ)}
    (sp : SlabPiece D i hx₀) (l : Fin sp.k) (t : Circle) :
    sp.levelCircles.gam l t = pieceGamma D i sp l t := rfl

end Circles

section KCircles

def kRadius (l : Fin 2) : ℝ := if l.val = 1 then Real.sqrt 3 else 1

theorem kRadius_pos (l : Fin 2) : 0 < kRadius l := by
  unfold kRadius
  split_ifs
  · exact Real.sqrt_pos.mpr (by norm_num)
  · norm_num

theorem kRadius_sq (l : Fin 2) : kRadius l ^ 2 = if l.val = 1 then 3 else 1 := by
  unfold kRadius
  split_ifs
  · exact Real.sq_sqrt (by norm_num)
  · norm_num

theorem mobiusHeight_kCircle (l : Fin 2) (t : Circle) :
    mobiusHeight (mobiusBlowUp ((kRadius l : ℂ) * (t : ℂ))) = if l.val = 1 then 2 else 0 := by
  rw [mobiusHeight_blowUp, ospU_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (kRadius_pos l).le, Circle.norm_coe, mul_one, kRadius_sq]
  split_ifs <;> norm_num

def kCircle (l : Fin 2) (t : Circle) : slabSet mobiusHeight 0 2 :=
  ⟨mobiusBlowUp ((kRadius l : ℂ) * (t : ℂ)), by
    rw [mem_mobiusSlab_iff, mobiusHeight_kCircle]
    split_ifs <;> norm_num⟩

theorem norm_mobiusPole : ‖mobiusPole‖ = Real.sqrt 2 := by
  rw [mobiusPole, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2),
    Complex.norm_I, mul_one]

theorem exists_kCircle {y : slabSet mobiusHeight 0 2} (l : Fin 2)
    (hy : mobiusHeight y.val = if l.val = 1 then 2 else 0) : ∃ t, kCircle l t = y := by
  have hn : ‖mobiusBlowDown y.val‖ = kRadius l := by
    have h := mobiusHeight_eq_norm_blowDown y.val
    rw [hy] at h
    have hsq : ‖mobiusBlowDown y.val‖ ^ 2 = kRadius l ^ 2 := by
      rw [kRadius_sq]
      split_ifs at h ⊢ <;> linarith
    exact (pow_left_inj₀ (norm_nonneg _) (kRadius_pos l).le two_ne_zero).mp hsq
  have hne : mobiusBlowDown y.val ≠ mobiusPole := by
    intro h
    rw [h, norm_mobiusPole] at hn
    unfold kRadius at hn
    split_ifs at hn with h1
    · have := congrArg (· ^ 2) hn
      simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] at this
      norm_num at this
    · have := congrArg (· ^ 2) hn
      simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] at this
      norm_num at this
  refine ⟨unitOf (mobiusBlowDown y.val), Subtype.ext ?_⟩
  change mobiusBlowUp ((kRadius l : ℂ) * (unitOf (mobiusBlowDown y.val) : ℂ)) = y.val
  have h1 : ((kRadius l : ℝ) : ℂ) * (unitOf (mobiusBlowDown y.val) : ℂ) = mobiusBlowDown y.val := by
    rw [← hn, ← Complex.real_smul, norm_smul_unitOf]
  rw [h1]
  exact mobiusBlowUp_blowDown hne

theorem continuous_kCircle (l : Fin 2) : Continuous (kCircle l) := by
  have hc : Continuous fun t : Circle => mobiusBlowUp ((kRadius l : ℂ) * (t : ℂ)) := by
    have h := contMDiffOn_mobiusBlowUp.continuousOn.comp_continuous
      (continuous_const.mul contMDiff_circle_coe.continuous) fun t => by
        change (kRadius l : ℂ) * (t : ℂ) ≠ mobiusPole
        intro h
        have hn := congrArg norm h
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (kRadius_pos l).le,
          Circle.norm_coe, mul_one, norm_mobiusPole] at hn
        unfold kRadius at hn
        split_ifs at hn
        · have := congrArg (· ^ 2) hn
          simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
            Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] at this
          norm_num at this
        · have := congrArg (· ^ 2) hn
          simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] at this
          norm_num at this
    exact h
  exact Continuous.subtype_mk hc _

end KCircles

section SplitCircles

variable (D : BaseMorseData B)

def SplitData.levelCircles {i : Fin D.m} {x₀ : Ambient B} (sd : SplitData D i x₀) :
    LevelCircles D i x₀ :=
  letI := (shiftAtlas (pieceAtlas D.smooth (level_castSucc_lt_succ D i) (slab_regular D i)
    x₀)).toChartedSpace
  letI := GC.Seifert.mobiusSlabAtlas.toChartedSpace
  { k := 2
    lev := fun l => decide (l.val = 1)
    γ := fun l t => sd.e.symm (kCircle l t)
    continuous_γ := fun l => sd.e.symm.continuous.comp (continuous_kCircle l)
    level := fun l t => by
      have h := sd.he (sd.e.symm (kCircle l t))
      rw [sd.e.apply_symm_apply] at h
      have hk : mobiusHeight (kCircle l t).val = if l.val = 1 then 2 else 0 :=
        mobiusHeight_kCircle l t
      by_cases hl : l.val = 1
      · simp only [hl, decide_true, ↓reduceIte] at hk ⊢
        exact h.2.mpr hk
      · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte] at hk ⊢
        exact h.1.mpr hk
    disjoint := fun l l' hll t t' heq => by
      have h1 := congrArg sd.e heq
      rw [sd.e.apply_symm_apply, sd.e.apply_symm_apply] at h1
      have h2 : mobiusHeight (mobiusBlowUp ((kRadius l : ℂ) * (t : ℂ))) =
          mobiusHeight (mobiusBlowUp ((kRadius l' : ℂ) * (t' : ℂ))) :=
        congrArg (fun y : slabSet mobiusHeight 0 2 => mobiusHeight y.val) h1
      rw [mobiusHeight_kCircle, mobiusHeight_kCircle] at h2
      apply hll
      fin_cases l <;> fin_cases l' <;> simp_all
    cover := fun w hw => by
      have hab := level_castSucc_lt_succ D i
      rcases hw with h | h
      · have h0 : mobiusHeight (sd.e w).val = 0 := (sd.he w).1.mp h
        obtain ⟨t, ht⟩ := exists_kCircle (y := sd.e w) 0 (by simpa using h0)
        exact ⟨0, t, by rw [ht, sd.e.symm_apply_apply]⟩
      · have h2 : mobiusHeight (sd.e w).val = 2 := (sd.he w).2.mp h
        obtain ⟨t, ht⟩ := exists_kCircle (y := sd.e w) 1 (by simpa using h2)
        exact ⟨1, t, by rw [ht, sd.e.symm_apply_apply]⟩ }

end SplitCircles

section PreComp

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]
  [IsManifold (𝓡∂ 2) ∞ X] [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
  [IsManifold (𝓡∂ 2) ∞ Y]
  {F E' H' Z : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace Z]
  [ChartedSpace H' Z]

omit [IsManifold (𝓡∂ 2) ∞ Y] in
theorem isImmersionAt_comp_of_localInverse (φ : X → Y) (hφ : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ φ)
    (hinj : Injective φ) (x : X) {U : Set Y} (hU : IsOpen U) (hxU : φ x ∈ U) {ψ : Y → X}
    (hψ : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ ψ U) (hφψ : ∀ y ∈ U, φ (ψ y) = y) (g : Y → Z)
    (hg : Manifold.IsImmersionAtOfComplement F (𝓡∂ 2) J ∞ g (φ x)) :
    Manifold.IsImmersionAtOfComplement F (𝓡∂ 2) J ∞ (g ∘ φ) x := by
  let R := localInverseHomeomorph φ hφ.continuous hinj hU hψ.continuousOn hφψ
  let A := hg.domChart
  have hA := hg.domChart_mem_maximalAtlas
  let φA := R.trans A
  have hφA : φA ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ X := by
    refine DifferentialGeometry.OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn φA ?_ ?_
    · exact contMDiffOn_trans_partialHomeomorph (e := R) (e' := A) hφ.contMDiffOn
        (contMDiffOn_of_mem_maximalAtlas hA)
    · exact contMDiffOn_trans_symm_partialHomeomorph (e := R) (e' := A) hψ
        (contMDiffOn_symm_of_mem_maximalAtlas hA)
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts hg.equiv φA hg.codChart
    ⟨hxU, hg.mem_domChart_source⟩ hg.mem_codChart_source hφA hg.codChart_mem_maximalAtlas
    (fun y hy => hg.source_subset_preimage_source hy.2) ?_
  intro u hu
  rw [OpenPartialHomeomorph.extend_target] at hu
  obtain ⟨hut, hrange⟩ := hu
  have hAt : (𝓡∂ 2).symm u ∈ A.target := hut.1
  have hU' : A.symm ((𝓡∂ 2).symm u) ∈ U := hut.2
  have hmem : u ∈ (A.extend (𝓡∂ 2)).target := by
    rw [OpenPartialHomeomorph.extend_target]
    exact ⟨hAt, hrange⟩
  have h := hg.writtenInCharts hmem
  change (hg.codChart.extend J) (g (φ (ψ (A.symm ((𝓡∂ 2).symm u))))) = _
  rw [hφψ _ hU']
  exact h

end PreComp

section CompMaps

variable (D : BaseMorseData B)

abbrev compSet (i : Fin D.m) (x₀ : Ambient B) : Set (slabOpens D i x₀) :=
  slabSet (pieceFun D.f (slabOpens D i x₀)) (D.level i.castSucc) (D.level i.succ)

def pieceToCorePD (i : Fin D.m) (x₀ : Ambient B) (z₀ : compSet D i x₀) :
    letI := (shiftAtlas (pieceAtlas D.smooth (level_castSucc_lt_succ D i) (slab_regular D i)
      x₀)).toChartedSpace
    PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) (compSet D i x₀) D.core.Carrier ∞ :=
  letI := (shiftAtlas (pieceAtlas D.smooth (level_castSucc_lt_succ D i) (slab_regular D i)
    x₀)).toChartedSpace
  { toFun := pieceToCore D (level_castSucc_lt_succ D i) (slab_regular D i) x₀
      (D.level_strictMono.monotone (Fin.zero_le _))
    invFun := coreToPiece D (level_castSucc_lt_succ D i) (slab_regular D i) x₀ z₀
    source := pieceToCore D (level_castSucc_lt_succ D i) (slab_regular D i) x₀
      (D.level_strictMono.monotone (Fin.zero_le _)) ⁻¹'
        coreLocalSet D (level_castSucc_lt_succ D i) (slab_regular D i) x₀
    target := coreLocalSet D (level_castSucc_lt_succ D i) (slab_regular D i) x₀
    map_source' := fun y hy => hy
    map_target' := fun y hy => by
      change pieceToCore D (level_castSucc_lt_succ D i) (slab_regular D i) x₀
        (D.level_strictMono.monotone (Fin.zero_le _))
        (coreToPiece D (level_castSucc_lt_succ D i) (slab_regular D i) x₀ z₀ y) ∈
          coreLocalSet D (level_castSucc_lt_succ D i) (slab_regular D i) x₀
      rw [pieceToCore_coreToPiece D _ _ x₀ _ z₀ hy]
      exact hy
    left_inv' := fun y hy => injective_pieceToCore D _ _ x₀ _
      (pieceToCore_coreToPiece D _ _ x₀ _ z₀ hy)
    right_inv' := fun y hy => pieceToCore_coreToPiece D _ _ x₀ _ z₀ hy
    open_source := (isOpen_coreLocalSet D _ _ x₀).preimage
      (contMDiff_pieceToCore_shift D _ _ x₀ _).continuous
    open_target := isOpen_coreLocalSet D _ _ x₀
    contMDiffOn_toFun := (contMDiff_pieceToCore_shift D _ _ x₀ _).contMDiffOn
    contMDiffOn_invFun := contMDiffOn_coreToPiece_shift D _ _ x₀ z₀ }

theorem isOpen_val_image_core {T : Set D.core.Carrier} (hT : IsOpen T)
    (hpos : ∀ y ∈ T, D.level 0 < D.f y.val) : IsOpen (Subtype.val '' T) := by
  obtain ⟨V, hV, hVT⟩ := isOpen_induced_iff.mp hT
  have he : Subtype.val '' T = V ∩ {z | D.level 0 < D.f z} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, hpos y hy⟩
      rw [← hVT] at hy
      exact hy
    · rintro ⟨hzV, hz⟩
      refine ⟨⟨z, hz.le⟩, ?_, rfl⟩
      rw [← hVT]
      exact hzV
  rw [he]
  exact hV.inter (isOpen_lt continuous_const D.smooth.continuous)

open Classical in
def coreLift (y₀ : D.core.Carrier) (z : B.Carrier) : D.core.Carrier :=
  if h : D.level 0 ≤ D.f z then ⟨z, h⟩ else y₀

theorem coreLift_val (y₀ : D.core.Carrier) {z : B.Carrier} (h : D.level 0 ≤ D.f z) :
    (coreLift D y₀ z).val = z := by
  simp [coreLift, h]

theorem contMDiffOn_coreLift (y₀ : D.core.Carrier) :
    ContMDiffOn (SurfaceModel.model B.kind) (𝓡∂ 2) ∞ (coreLift D y₀) {z | D.level 0 < D.f z} := by
  refine (D.coreAtlas.contMDiffOn_iff_subtype_val _ _).mpr ?_
  exact contMDiffOn_id.congr fun z hz => coreLift_val D y₀ (le_of_lt hz)

def coreToBPD {M E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace M]
    [ChartedSpace H'' M] (c : PartialDiffeomorph I'' (𝓡∂ 2) M D.core.Carrier ∞)
    (hpos : ∀ y ∈ c.target, D.level 0 < D.f y.val) (y₀ : D.core.Carrier) :
    PartialDiffeomorph I'' (SurfaceModel.model B.kind) M B.Carrier ∞ :=
  have hlift : ∀ y : D.core.Carrier, coreLift D y₀ y.val = y := fun y =>
    Subtype.ext (coreLift_val D y₀ y.2)
  have himg : ∀ z ∈ {z : B.Carrier | ∃ y : D.core.Carrier, y ∈ c.target ∧ y.val = z},
      coreLift D y₀ z ∈ c.target := by
    rintro z ⟨y, hy, rfl⟩
    rw [hlift]
    exact hy
  have hval : ∀ z ∈ {z : B.Carrier | ∃ y : D.core.Carrier, y ∈ c.target ∧ y.val = z},
      (coreLift D y₀ z).val = z := by
    rintro z ⟨y, hy, rfl⟩
    rw [hlift]
  { toFun := fun q => (c q).val
    invFun := fun z => c.symm (coreLift D y₀ z)
    source := c.source
    target := {z : B.Carrier | ∃ y : D.core.Carrier, y ∈ c.target ∧ y.val = z}
    map_source' := fun q hq => ⟨c q, c.map_source hq, rfl⟩
    map_target' := fun z hz => c.map_target (himg z hz)
    left_inv' := fun q hq => by
      rw [hlift]
      exact c.left_inv hq
    right_inv' := fun z hz => by
      have hr : c (c.symm (coreLift D y₀ z)) = coreLift D y₀ z := c.right_inv (himg z hz)
      change (c (c.symm (coreLift D y₀ z))).val = z
      rw [hr, hval z hz]
    open_source := c.open_source
    open_target := isOpen_val_image_core D c.open_target hpos
    contMDiffOn_toFun := (coreVal_contMDiff D).comp_contMDiffOn c.contMDiffOn
    contMDiffOn_invFun := by
      refine c.symm.contMDiffOn.comp ((contMDiffOn_coreLift D y₀).mono ?_) fun z hz => himg z hz
      rintro z ⟨y, hy, rfl⟩
      exact hpos y hy }

theorem coreToBPD_apply {M E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace M]
    [ChartedSpace H'' M] (c : PartialDiffeomorph I'' (𝓡∂ 2) M D.core.Carrier ∞)
    (hpos : ∀ y ∈ c.target, D.level 0 < D.f y.val) (y₀ : D.core.Carrier) (q : M) :
    coreToBPD D c hpos y₀ q = (c q).val := rfl

theorem coreToBPD_source {M E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace M]
    [ChartedSpace H'' M] (c : PartialDiffeomorph I'' (𝓡∂ 2) M D.core.Carrier ∞)
    (hpos : ∀ y ∈ c.target, D.level 0 < D.f y.val) (y₀ : D.core.Carrier) :
    (coreToBPD D c hpos y₀).source = c.source := rfl

end CompMaps

section HalfHyps

variable (D : BaseMorseData B)

theorem halfCollar_hyps (i : Fin D.m) (x₀ : Ambient B)
    {c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind) (Circle × ℝ)
      B.Carrier ∞} (hcs : c.source = {p | -1 < p.2 ∧ p.2 < 1}) {κ'' : ℝ} (hκ'' : 0 < κ'')
    {L : ℝ} (hcf : ∀ t s, -1 < s → s < 1 → D.f (c (t, s)) = L + κ'' * s) {ε : ℝ}
    (hLε : (L = D.level i.castSucc ∧ ε = 1) ∨ (L = D.level i.succ ∧ ε = -1))
    (hgap : κ'' < D.level i.succ - D.level i.castSucc)
    (hzero : ∀ t, c (t, 0) ∈ connectedComponentIn
      (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀)) :
    (∀ t s, 0 ≤ s → s < 1 → ∃ y : compSet D i x₀, opensVal _ y.val = c (t, ε * s)) ∧
      ∀ y : compSet D i x₀, opensVal _ y.val ∈ c.target →
        0 ≤ ε * (c.symm (opensVal _ y.val)).2 := by
  have hab := level_castSucc_lt_succ D i
  have hε : ε = 1 ∨ ε = -1 := by
    rcases hLε with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  refine ⟨fun t s h0 h1 => ?_, fun y hy => ?_⟩
  · have hmem := half_mem_component hcs hcf hε (a := D.level i.castSucc) (b := D.level i.succ)
      (fun s' hs0 hs1 => by
        rcases hLε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> constructor <;> nlinarith) hzero t h0 h1
    rw [← opensVal_image_pieceSlab D.smooth hab (slab_regular D i) (slab_interior D i) x₀] at hmem
    obtain ⟨w, hw, hw'⟩ := hmem
    exact ⟨⟨w, hw⟩, hw'⟩
  · exact side_of_mem_target hcs hκ'' hcf (a := D.level i.castSucc) (b := D.level i.succ)
      (by rcases hLε with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩) hy ((mem_slabSet_iff hab.le _).mp y.2)

end HalfHyps

section PostComp

variable {EX HX X EY H Y Z : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X]
  [ChartedSpace HX X] [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace H]
  {I : ModelWithCorners ℝ EY H} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def localDiffeoHomeomorph (G : Y → Z) {U : Set Y} (hU : IsOpen U) {V : Set Z} (hV : IsOpen V)
    (hGc : ContinuousOn G U) (hGU : MapsTo G U V) (ψ : Z → Y) (hψc : ContinuousOn ψ V)
    (hψV : MapsTo ψ V U) (hψG : ∀ y ∈ U, ψ (G y) = y) (hGψ : ∀ z ∈ V, G (ψ z) = z) :
    OpenPartialHomeomorph Z Y where
  toFun := ψ
  invFun := G
  source := V
  target := U
  map_source' := hψV
  map_target' := hGU
  left_inv' := hGψ
  right_inv' := hψG
  open_source := hV
  open_target := hU
  continuousOn_toFun := hψc
  continuousOn_invFun := hGc

omit [IsManifold I ∞ Y] in
theorem isImmersionAt_localDiffeo_comp (f : X → Y) (x : X)
    (hf : Manifold.IsImmersionAtOfComplement F IX I ∞ f x) (hfc : ContinuousAt f x)
    (G : Y → Z) {U : Set Y} (hU : IsOpen U) (hfxU : f x ∈ U) {V : Set Z} (hV : IsOpen V)
    (hGs : ContMDiffOn I I ∞ G U) (hGU : MapsTo G U V) (ψ : Z → Y)
    (hψs : ContMDiffOn I I ∞ ψ V) (hψV : MapsTo ψ V U) (hψG : ∀ y ∈ U, ψ (G y) = y)
    (hGψ : ∀ z ∈ V, G (ψ z) = z) :
    Manifold.IsImmersionAtOfComplement F IX I ∞ (G ∘ f) x := by
  let L := localDiffeoHomeomorph G hU hV hGs.continuousOn hGU ψ hψs.continuousOn hψV hψG hGψ
  let Bc := hf.codChart
  have hB := hf.codChart_mem_maximalAtlas
  let Bc' := L.trans Bc
  have hB' : Bc' ∈ IsManifold.maximalAtlas I ∞ Z := by
    refine DifferentialGeometry.OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn Bc' ?_ ?_
    · exact contMDiffOn_trans_partialHomeomorph (e := L) (e' := Bc) hψs
        (contMDiffOn_of_mem_maximalAtlas hB)
    · exact contMDiffOn_trans_symm_partialHomeomorph (e := L) (e' := Bc) hGs
        (contMDiffOn_symm_of_mem_maximalAtlas hB)
  let A := hf.domChart
  have hA := hf.domChart_mem_maximalAtlas
  have hfU : f ⁻¹' U ∈ 𝓝 x := hfc.preimage_mem_nhds (hU.mem_nhds hfxU)
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp hfU
  let A' := A.restr O
  have hA'src : A'.source = A.source ∩ O := by
    rw [OpenPartialHomeomorph.restr_source, hO.interior_eq]
  have hA' : A' ∈ IsManifold.maximalAtlas IX ∞ X :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ IX) hA hO
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts hf.equiv A' Bc'
    (by rw [hA'src]; exact ⟨hf.mem_domChart_source, hxO⟩) ?_ hA' hB' ?_ ?_
  · refine ⟨hGU hfxU, ?_⟩
    change ψ (G (f x)) ∈ Bc.source
    rw [hψG _ hfxU]
    exact hf.mem_codChart_source
  · intro y hy
    rw [hA'src] at hy
    refine ⟨hGU (hOsub hy.2), ?_⟩
    change ψ (G (f y)) ∈ Bc.source
    rw [hψG _ (hOsub hy.2)]
    exact hf.source_subset_preimage_source hy.1
  · intro u hu
    have hu' : u ∈ (A.extend IX).target := by
      rw [OpenPartialHomeomorph.extend_target] at hu ⊢
      exact ⟨hu.1.1, hu.2⟩
    have hy : (A'.extend IX).symm u ∈ A'.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using (A'.extend IX).map_target hu
    rw [hA'src] at hy
    have he : (A'.extend IX).symm u = (A.extend IX).symm u := rfl
    have h := hf.writtenInCharts hu'
    change (Bc.extend I) (ψ (G (f ((A'.extend IX).symm u)))) = _
    rw [hψG _ (hOsub hy.2), he]
    exact h

end PostComp

section EmbComp

variable {Y Z : Type*} [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]
  [IsManifold (𝓡∂ 2) ∞ Y] [TopologicalSpace Z] [ChartedSpace (EuclideanHalfSpace 2) Z]
  [IsManifold (𝓡∂ 2) ∞ Z]

omit [IsManifold (𝓡∂ 2) ∞ Y] in
theorem isSmoothEmbedding_comp_of_localDiffeo {S' : CompactSurface.{u}}
    (hS : S'.kind = .withBoundary) (ι₀ : S'.Carrier → Y)
    (hι₀ : Manifold.IsSmoothEmbedding (SurfaceModel.model S'.kind) (𝓡∂ 2) ∞ ι₀)
    (G : Y → Z) (hG : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 2) ∞ G)
    {U : Set Y} (hU : IsOpen U) {V : Set Z} (hV : IsOpen V)
    (hGs : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ G U) (hGU : MapsTo G U V) (ψG : Z → Y)
    (hψGs : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ ψG V) (hψV : MapsTo ψG V U)
    (hψG : ∀ y ∈ U, ψG (G y) = y) (hGψ : ∀ z ∈ V, G (ψG z) = z)
    {W : Set Y} (hW : IsOpen W) (ψ : Y → S'.Carrier)
    (hψ : ContMDiffOn (𝓡∂ 2) (SurfaceModel.model S'.kind) ∞ ψ W)
    (hψι : ∀ y ∈ W, ι₀ (ψ y) = y) (hcov : ∀ x, ι₀ x ∈ U ∨ ι₀ x ∈ W) :
    Manifold.IsSmoothEmbedding (SurfaceModel.model S'.kind) (𝓡∂ 2) ∞ (G ∘ ι₀) := by
  obtain ⟨⟨kind, Carrier, top, charts, smooth, t2, cpt, sc⟩, conn⟩ := S'
  subst hS
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_isImmersionAt fun x => ?_,
    hG.isEmbedding.comp hι₀.isEmbedding⟩
  have hsm : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ ι₀ := hι₀.isImmersion.contMDiff
  rcases hcov x with hx | hx
  · have hf := (hι₀.isImmersion.isImmersionAt x).isImmersionAtOfComplement_complement
    exact (isImmersionAt_localDiffeo_comp ι₀ x hf hsm.continuous.continuousAt G hU hx hV hGs hGU
      ψG hψGs hψV hψG hGψ).isImmersionAt
  · have hg := (hG.isImmersion.isImmersionAt (ι₀ x)).isImmersionAtOfComplement_complement
    exact (isImmersionAt_comp_of_localInverse ι₀ hsm hι₀.isEmbedding.injective x hW hx hψ hψι G
      hg).isImmersionAt

end EmbComp

section SplitPieces

variable (D : BaseMorseData B)

def lvlEps (l : Fin 2) : ℝ := if l.val = 1 then -1 else 1

def lvlOf (b : Bool) : Fin 2 := if b then 1 else 0

theorem exists_split_pieces (i : Fin D.m) {x₀ : Ambient B} (sd : SplitData D i x₀)
    (c : Fin 2 → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
      (Circle × ℝ) B.Carrier ∞)
    (hcs : ∀ l, (c l).source = {p | -1 < p.2 ∧ p.2 < 1})
    (κl : Fin 2 → ℝ) (hκl : ∀ l, 0 < κl l) (hκD : ∀ l, κl l ≤ D.κ)
    (hcf : ∀ l t s, -1 < s → s < 1 → D.f (c l (t, s)) =
      (if l.val = 1 then D.level i.succ else D.level i.castSucc) + κl l * s)
    (hgap : ∀ l, κl l < D.level i.succ - D.level i.castSucc)
    (hzero : ∀ l t, ∃ t', sd.levelCircles.gam l t' = c l (t, 0))
    (hcov : ∀ l t, ∃ t', c l (t', 0) = sd.levelCircles.gam l t)
    (hη : ∀ y : compSet D i x₀, 1 / 4 ≤ mobiusHeight (sd.e y).val →
      mobiusHeight (sd.e y).val ≤ 7 / 4 →
        D.level i.castSucc + D.κ < pieceFun D.f (slabOpens D i x₀) y.val ∧
          pieceFun D.f (slabOpens D i x₀) y.val < D.level i.succ - D.κ) :
    ∃ (ιM : mobiusBase.{u}.surface.Carrier → D.core.Carrier) (Q : PlanarBase.{u} 3)
      (ιQ : Q.surface.Carrier → D.core.Carrier)
      (cc : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) (Circle × ℝ) D.core.Carrier ∞)
      (jc : Fin 3) (jl : Fin 2 → Fin 3),
      Manifold.IsSmoothEmbedding (SurfaceModel.model mobiusBase.{u}.surface.kind)
        (SurfaceModel.model D.core.kind) ∞ ιM ∧
      Manifold.IsSmoothEmbedding (SurfaceModel.model Q.surface.kind)
        (SurfaceModel.model D.core.kind) ∞ ιQ ∧
      cc.source = {p | -1 < p.2 ∧ p.2 < 1} ∧
      (∀ y ∈ cc.target, D.level i.castSucc + D.κ < D.f y.val ∧
        D.f y.val < D.level i.succ - D.κ) ∧
      (∀ y ∈ cc.target, y.val ∈ connectedComponentIn
        (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀)) ∧
      (∀ t s (hs : 0 ≤ s), s < 1 → ιM (mobiusBase.{u}.collar (t, halfPoint s hs)) = cc (t, s)) ∧
      (∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
        ιQ (Q.collar jc (t, halfPoint s hs)) = cc (σ t, -s)) ∧
      (∀ l, jl l ≠ jc) ∧ Injective jl ∧ (∀ j, j = jc ∨ ∃ l, jl l = j) ∧
      (∀ l, ∃ σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle, ∀ t s (hs : 0 ≤ s), s < 1 →
        (ιQ (Q.collar (jl l) (t, halfPoint s hs))).val = c l (σ t, lvlEps l * s)) ∧
      (∀ x, (ιM x).val ∈ connectedComponentIn
        (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀)) ∧
      (∀ x, (ιQ x).val ∈ connectedComponentIn
        (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀)) ∧
      (∀ y ∈ connectedComponentIn (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ))
        (ambientVal x₀), (∃ x, (ιM x).val = y) ∨ ∃ x, (ιQ x).val = y) ∧
      (∀ x, D.level i.castSucc + D.κ < D.f (ιM x).val ∧ D.f (ιM x).val < D.level i.succ - D.κ) ∧
      (∀ x, D.f (ιQ x).val = D.level i.castSucc ∨ D.f (ιQ x).val = D.level i.succ →
        ∃ l t, x = Q.collar (jl l) (t, halfZero)) ∧
      (∀ x x', ιM x = ιQ x' → ∃ t, ιM x = cc (t, 0)) := by
  have hab := level_castSucc_lt_succ D i
  have hreg := slab_regular D i
  have hint := slab_interior D i
  have ha : D.level 0 ≤ D.level i.castSucc := D.level_strictMono.monotone (Fin.zero_le _)
  let Cp := pieceAtlas D.smooth hab hreg x₀
  let Cs := shiftAtlas Cp
  let := GC.Seifert.mobiusSlabAtlas.toChartedSpace
  have := GC.Seifert.mobiusSlabAtlas.isManifold
  let := Cs.toChartedSpace
  have := Cs.isManifold
  let lc := sd.levelCircles
  have hε : ∀ l, lvlEps l = 1 ∨ lvlEps l = -1 := fun l => by
    unfold lvlEps; split_ifs <;> simp
  have hLε : ∀ l, ((if l.val = 1 then D.level i.succ else D.level i.castSucc) =
      D.level i.castSucc ∧ lvlEps l = 1) ∨
      ((if l.val = 1 then D.level i.succ else D.level i.castSucc) = D.level i.succ ∧
        lvlEps l = -1) := fun l => by
    unfold lvlEps
    by_cases hl : l.val = 1 <;> simp [hl]
  have hgamK : ∀ l t, lc.gam l t ∈ connectedComponentIn
      (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀) := fun l t => by
    rw [← opensVal_image_pieceSlab D.smooth hab hreg hint x₀]
    exact mem_image_of_mem _ (lc.γ l t).2
  have hzeroK : ∀ l t, c l (t, 0) ∈ connectedComponentIn
      (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀) := fun l t => by
    obtain ⟨t', ht'⟩ := hzero l t
    rw [← ht']
    exact hgamK l t'
  have hhyp := fun l => halfCollar_hyps D i x₀ (hcs l) (hκl l) (hcf l) (hLε l) (hgap l) (hzeroK l)
  let hc : Fin 2 → PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (compSet D i x₀) ∞ := fun l =>
    halfCollar D.smooth hab hreg x₀ (c l) (Diffeomorph.refl (𝓡 1) Circle ∞) (lvlEps l) (hcs l)
      (hε l) (hhyp l).1 (hhyp l).2
  have hcval : ∀ l q, opensVal _ (hc l q).val = c l (q.1, lvlEps l * collarClamp q) := fun l q =>
    opensVal_halfCollarFun D.smooth hab hreg x₀ (c l) (Diffeomorph.refl (𝓡 1) Circle ∞)
      (lvlEps l) (hhyp l).1 q
  have hcsrc : ∀ l, (hc l).source = circleCollarSource := fun l => rfl
  have hctgt : ∀ l y, y ∈ (hc l).target ↔ opensVal _ y.val ∈ (c l).target := fun l y => Iff.rfl
  have hc0 : ∀ l t, opensVal _ (hc l (t, halfZero)).val = c l (t, 0) := fun l t => by
    rw [hcval, collarClamp_of_mem (halfZero_mem_circleCollarSource t)]
    change c l (t, lvlEps l * 0) = c l (t, 0)
    rw [mul_zero]
  have hlvl : ∀ b : Bool, (lvlOf b).val = 1 ↔ b = true := fun b => by
    cases b <;> simp [lvlOf]
  let col : Bool → PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (slabSet mobiusHeight 0 2) ∞ := fun b => (hc (lvlOf b)).trans sd.e.toPartialDiffeomorph
  have hcolapp : ∀ b q, col b q = sd.e (hc (lvlOf b) q) := fun b q => rfl
  have hsrcC : ∀ b, (col b).source = circleCollarSource := fun b =>
    Set.ext fun q => ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩
  have hfL : ∀ (l : Fin 2) (y : compSet D i x₀), pieceFun D.f (slabOpens D i x₀) y.val =
      (if l.val = 1 then D.level i.succ else D.level i.castSucc) →
        mobiusHeight (sd.e y).val = if l.val = 1 then 2 else 0 := by
    intro l y hy
    by_cases hl : l.val = 1
    · simp only [hl, ↓reduceIte] at hy ⊢
      exact (sd.he y).2.mp hy
    · simp only [hl, ↓reduceIte] at hy ⊢
      exact (sd.he y).1.mp hy
  have hlevC : ∀ b t, mobiusHeight (col b (t, halfZero)) = if b then 2 else 0 := by
    intro b t
    rw [hcolapp]
    have h1 := hfL (lvlOf b) (hc (lvlOf b) (t, halfZero)) (by
      change D.f (opensVal _ (hc (lvlOf b) (t, halfZero)).val) = _
      rw [hc0, hcf _ t 0 (by norm_num) (by norm_num), mul_zero, add_zero])
    rw [h1]
    cases b <;> simp [lvlOf]
  have htgtC : ∀ b, ∀ x ∈ (col b).target,
      mobiusHeight x < 1 / 4 ∨ 2 - 1 / 4 < mobiusHeight x := by
    intro b x hx
    have hx' : sd.e.symm x ∈ (hc (lvlOf b)).target := hx.2
    rw [hctgt] at hx'
    have habs := abs_sub_lt_of_mem_target (hcs _) (hκl _) (hcf _) hx'
    have hκ := hκD (lvlOf b)
    have hxe : sd.e (sd.e.symm x) = x := sd.e.apply_symm_apply x
    by_contra hcon
    push Not at hcon
    have hb := hη (sd.e.symm x) (by rw [hxe]; exact hcon.1) (by rw [hxe]; linarith [hcon.2])
    have hb1 : D.level i.castSucc + D.κ < D.f (opensVal _ (sd.e.symm x).val) := hb.1
    have hb2 : D.f (opensVal _ (sd.e.symm x).val) < D.level i.succ - D.κ := hb.2
    rw [abs_lt] at habs
    cases b <;> simp [lvlOf] at habs hκ <;> linarith [habs.1, habs.2]
  have hcovC : ∀ b (x : slabSet mobiusHeight 0 2), mobiusHeight x = (if b then 2 else 0) →
      ∃ t, col b (t, halfZero) = x := by
    intro b x hx
    have hxe : sd.e (sd.e.symm x) = x := sd.e.apply_symm_apply x
    have hy : D.f (opensVal _ (sd.e.symm x).val) =
        if (lvlOf b).val = 1 then D.level i.succ else D.level i.castSucc := by
      cases b
      · have h : pieceFun D.f (slabOpens D i x₀) (sd.e.symm x).val = D.level i.castSucc :=
          (sd.he (sd.e.symm x)).1.mpr (by rw [hxe]; simpa using hx)
        simp only [lvlOf, Bool.false_eq_true, ↓reduceIte, Fin.isValue, Fin.val_zero,
          zero_ne_one]
        exact h
      · have h : pieceFun D.f (slabOpens D i x₀) (sd.e.symm x).val = D.level i.succ :=
          (sd.he (sd.e.symm x)).2.mpr (by rw [hxe]; simpa using hx)
        simp only [lvlOf, ↓reduceIte, Fin.isValue, Fin.val_one]
        exact h
    obtain ⟨l', t₁, ht₁⟩ := lc.cover (sd.e.symm x) (by
      rw [hy]; split_ifs <;> simp)
    have hl' : l' = lvlOf b := by
      have h1 := lc.level l' t₁
      rw [ht₁, hy] at h1
      have hne := hab.ne
      revert h1
      cases b <;> fin_cases l' <;>
        simp only [lvlOf, Bool.false_eq_true, ↓reduceIte, Fin.isValue, Fin.coe_ofNat_eq_mod,
          Nat.zero_mod, Nat.mod_succ, zero_ne_one, one_ne_zero, SplitData.levelCircles,
          Fin.zero_eta, Fin.mk_one, decide_false, decide_true, imp_self, imp_false, lc] <;>
        intro h1 <;> first | exact hne h1 | exact hne h1.symm
    subst hl'
    obtain ⟨t', ht'⟩ := hcov (lvlOf b) t₁
    have hy' : hc (lvlOf b) (t', halfZero) = sd.e.symm x := by
      apply Subtype.ext
      apply (isOpenEmbedding_opensVal _).injective
      rw [hc0, ht']
      change opensVal _ (lc.γ (lvlOf b) t₁).val = _
      rw [ht₁]
    exact ⟨t', by rw [hcolapp, hy', hxe]⟩
  obtain ⟨ιM₀, Q, ιQ₀, cK, jc, lv, hkind, hembM, hembQ, hcKs, hband, hKcov, hov, hMcol,
    ⟨σc, hσc⟩, hQlev, hlvinj, hbdry, W, hW, hWlev, ψ, hψ, hψι⟩ :=
    GC.Seifert.mobiusSlab_split_quarter.{u} col hsrcC hlevC htgtC hcovC
  let z₀ : compSet D i x₀ := sd.e.symm (kCircle 0 1)
  let G : slabSet mobiusHeight 0 2 → D.core.Carrier := fun y =>
    pieceToCore D hab hreg x₀ ha (sd.e.symm y)
  have hG : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 2) ∞ G :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
      (pieceToCore D hab hreg x₀ ha) (isSmoothEmbedding_pieceToCore D hab hreg x₀ ha) sd.e.symm
  let U : Set (slabSet mobiusHeight 0 2) := {y | 0 < mobiusHeight y.val ∧ mobiusHeight y.val < 2}
  have hcontH : Continuous fun y : slabSet mobiusHeight 0 2 => mobiusHeight y.val :=
    contMDiff_mobiusHeight.continuous.comp continuous_subtype_val
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const hcontH).inter (isOpen_lt hcontH continuous_const)
  let intS : Set (compSet D i x₀) := {w | D.level i.castSucc < pieceFun D.f _ w.val ∧
    pieceFun D.f _ w.val < D.level i.succ}
  have hcontF : Continuous fun w : compSet D i x₀ => pieceFun D.f (slabOpens D i x₀) w.val :=
    (contMDiff_pieceFun D.smooth _).continuous.comp continuous_subtype_val
  have hintS : IsOpen intS := (isOpen_lt continuous_const hcontF).inter
    (isOpen_lt hcontF continuous_const)
  let V : Set D.core.Carrier := coreLocalSet D hab hreg x₀ ∩
    {z | coreToPiece D hab hreg x₀ z₀ z ∈ intS}
  have hVo : IsOpen V :=
    (contMDiffOn_coreToPiece_shift D hab hreg x₀ z₀).continuousOn.isOpen_inter_preimage
    (isOpen_coreLocalSet D hab hreg x₀) hintS
  let ψG : D.core.Carrier → slabSet mobiusHeight 0 2 := fun z =>
    sd.e (coreToPiece D hab hreg x₀ z₀ z)
  have hlevS : ∀ w : compSet D i x₀,
      (pieceFun D.f (slabOpens D i x₀) w.val = D.level i.castSucc ↔ mobiusHeight (sd.e w).val = 0) ∧
      (pieceFun D.f (slabOpens D i x₀) w.val = D.level i.succ ↔ mobiusHeight (sd.e w).val = 2) :=
    fun w => sd.he w
  have hintIff : ∀ w : compSet D i x₀, w ∈ intS ↔ sd.e w ∈ U := by
    intro w
    have hwS := (mem_slabSet_iff hab.le w.val).mp w.2
    have hK := (mem_mobiusSlab_iff (sd.e w).val).mp (sd.e w).2
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨lt_of_le_of_ne hK.1 fun h => ?_, lt_of_le_of_ne hK.2 fun h => ?_⟩
      · have := (hlevS w).1.mpr h.symm
        linarith
      · have := (hlevS w).2.mpr h
        linarith
    · rintro ⟨h1, h2⟩
      refine ⟨lt_of_le_of_ne hwS.1 fun h => ?_, lt_of_le_of_ne hwS.2 fun h => ?_⟩
      · have := (hlevS w).1.mp h.symm
        linarith
      · have := (hlevS w).2.mp h
        linarith
  have hctp : ∀ w : compSet D i x₀, pieceToCore D hab hreg x₀ ha w ∈ coreLocalSet D hab hreg x₀ →
      coreToPiece D hab hreg x₀ z₀ (pieceToCore D hab hreg x₀ ha w) = w := fun w hw =>
    injective_pieceToCore D hab hreg x₀ ha (pieceToCore_coreToPiece D hab hreg x₀ ha z₀ hw)
  have hlocS : ∀ w ∈ intS, pieceToCore D hab hreg x₀ ha w ∈ coreLocalSet D hab hreg x₀ :=
    fun w hw => ⟨⟨w.val, rfl⟩, hw.2, Or.inl hw.1⟩
  have hGU : MapsTo G U V := by
    intro y hy
    have hw : sd.e.symm y ∈ intS := (hintIff _).mpr (by rw [sd.e.apply_symm_apply]; exact hy)
    refine ⟨hlocS _ hw, ?_⟩
    change coreToPiece D hab hreg x₀ z₀ (pieceToCore D hab hreg x₀ ha (sd.e.symm y)) ∈ intS
    rw [hctp _ (hlocS _ hw)]
    exact hw
  have hψV : MapsTo ψG V U := fun z hz => (hintIff _).mp hz.2
  have hψG : ∀ y ∈ U, ψG (G y) = y := by
    intro y hy
    have hw : sd.e.symm y ∈ intS := (hintIff _).mpr (by rw [sd.e.apply_symm_apply]; exact hy)
    change sd.e (coreToPiece D hab hreg x₀ z₀ (pieceToCore D hab hreg x₀ ha (sd.e.symm y))) = y
    rw [hctp _ (hlocS _ hw), sd.e.apply_symm_apply]
  have hGψ : ∀ z ∈ V, G (ψG z) = z := by
    intro z hz
    change pieceToCore D hab hreg x₀ ha (sd.e.symm (sd.e (coreToPiece D hab hreg x₀ z₀ z))) = z
    rw [sd.e.symm_apply_apply]
    exact pieceToCore_coreToPiece D hab hreg x₀ ha z₀ hz.1
  have hGsm : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ G :=
    (contMDiff_pieceToCore_shift D hab hreg x₀ ha).comp sd.e.symm.contMDiff
  have hψGs : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ ψG V :=
    sd.e.contMDiff.comp_contMDiffOn
      ((contMDiffOn_coreToPiece_shift D hab hreg x₀ z₀).mono inter_subset_left)
  have hMU : ∀ x, ιM₀ x ∈ U := fun x => by
    have h := hband (ιM₀ x) (Or.inr ⟨x, rfl⟩)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hMemb : Manifold.IsSmoothEmbedding (SurfaceModel.model mobiusBase.{u}.surface.kind)
      (𝓡∂ 2) ∞ (G ∘ ιM₀) :=
    isSmoothEmbedding_comp_of_localDiffeo (S' := mobiusBase.{u}.surface) rfl ιM₀ hembM G hG hUo
      hVo hGsm.contMDiffOn hGU ψG hψGs hψV hψG hGψ (W := ∅) isOpen_empty
      (Function.const _ (mobiusBase.{u}.collar (1, halfZero))) contMDiffOn_empty
      (fun y hy => absurd hy (notMem_empty y)) (fun x => Or.inl (hMU x))
  have hQcov : ∀ x, ιQ₀ x ∈ U ∨ ιQ₀ x ∈ W := by
    intro x
    by_cases h : 0 < mobiusHeight (ιQ₀ x).val ∧ mobiusHeight (ιQ₀ x).val < 2
    · exact Or.inl h
    · right
      apply hWlev
      have hK := (mem_mobiusSlab_iff (ιQ₀ x).val).mp (ιQ₀ x).2
      by_cases h0 : mobiusHeight (ιQ₀ x).val = 0
      · exact Or.inl h0
      · right
        by_contra h2
        exact h ⟨lt_of_le_of_ne hK.1 (Ne.symm h0), lt_of_le_of_ne hK.2 h2⟩
  have hQemb : Manifold.IsSmoothEmbedding (SurfaceModel.model Q.surface.kind)
      (𝓡∂ 2) ∞ (G ∘ ιQ₀) :=
    isSmoothEmbedding_comp_of_localDiffeo (S' := Q.surface) hkind ιQ₀ hembQ G hG hUo
      hVo hGsm.contMDiffOn hGU ψG hψGs hψV hψG hGψ hW ψ hψ hψι hQcov
  have hGval : ∀ y, (G y).val = opensVal _ (sd.e.symm y).val := fun y => rfl
  have hGK : ∀ y, (G y).val ∈ connectedComponentIn
      (D.f ⁻¹' Icc (D.level i.castSucc) (D.level i.succ)) (ambientVal x₀) := fun y => by
    rw [hGval, ← opensVal_image_pieceSlab D.smooth hab hreg hint x₀]
    exact mem_image_of_mem _ (sd.e.symm y).2
  have hGf : ∀ y : slabSet mobiusHeight 0 2, 1 / 4 ≤ mobiusHeight y.val →
      mobiusHeight y.val ≤ 2 - 1 / 4 →
        D.level i.castSucc + D.κ < D.f (G y).val ∧ D.f (G y).val < D.level i.succ - D.κ := by
    intro y h1 h2
    have hy : sd.e (sd.e.symm y) = y := sd.e.apply_symm_apply y
    exact hη (sd.e.symm y) (by rw [hy]; exact h1) (by rw [hy]; linarith)
  let cc : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) (Circle × ℝ) D.core.Carrier ∞ :=
    (cK.trans sd.e.symm.toPartialDiffeomorph).trans (pieceToCorePD D i x₀ z₀)
  have hccapp : ∀ p, cc p = G (cK p) := fun p => rfl
  have hccs : cc.source = {p | -1 < p.2 ∧ p.2 < 1} := by
    ext p
    constructor
    · intro hp
      rw [← hcKs]
      exact hp.1.1
    · intro hp
      have hpK : p ∈ cK.source := by rw [hcKs]; exact hp
      have hb := hband (cK p) (Or.inl (cK.map_source hpK))
      have hw : sd.e.symm (cK p) ∈ intS := (hintIff _).mpr (by
        rw [sd.e.apply_symm_apply]
        exact ⟨by linarith [hb.1], by linarith [hb.2]⟩)
      exact ⟨⟨hpK, mem_univ _⟩, hlocS _ hw⟩
  have hccT : ∀ y ∈ cc.target, ∃ p, p ∈ cc.source ∧ cc p = y := fun y hy =>
    ⟨cc.toPartialEquiv.symm y, cc.toPartialEquiv.map_target hy, cc.toPartialEquiv.right_inv hy⟩
  have hthree := (by decide : ∀ j : Fin 3, ∃ j₁ j₂ : Fin 3, j₁ ≠ j ∧ j₂ ≠ j ∧ j₁ ≠ j₂) jc
  have hex : ∀ b, ∃ j, j ≠ jc ∧ lv j = b := by
    intro b
    by_contra hne
    push Not at hne
    obtain ⟨j₁, j₂, h1, h2, h12⟩ := hthree
    have key : ∀ a₁ a₂ b' : Bool, a₁ ≠ b' → a₂ ≠ b' → a₁ = a₂ := by decide
    exact h12 (hlvinj j₁ j₂ h1 h2 (key _ _ b (hne j₁ h1) (hne j₂ h2)))
  let jl : Fin 2 → Fin 3 := fun l => Classical.choose (hex (decide (l.val = 1)))
  have hjl : ∀ l, jl l ≠ jc ∧ lv (jl l) = decide (l.val = 1) := fun l =>
    Classical.choose_spec (hex (decide (l.val = 1)))
  have hlvlOf : ∀ l : Fin 2, lvlOf (decide (l.val = 1)) = l := by decide
  have hdec : ∀ b : Bool, decide ((lvlOf b).val = 1) = b := by decide
  have hjlOf : ∀ j, j ≠ jc → jl (lvlOf (lv j)) = j := fun j hj =>
    hlvinj _ _ (hjl _).1 hj (by rw [(hjl _).2, hdec])
  refine ⟨G ∘ ιM₀, Q, G ∘ ιQ₀, cc, jc, jl, hMemb, hQemb, hccs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := hccT y hy
    have hb := hband (cK p) (Or.inl (cK.map_source hp.1.1))
    exact hGf _ hb.1 hb.2
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := hccT y hy
    exact hGK _
  · intro t s hs hs1
    change G (ιM₀ _) = G (cK (t, s))
    rw [hMcol t s hs hs1]
  · refine ⟨σc, fun t s hs hs1 => ?_⟩
    change G (ιQ₀ _) = G (cK _)
    rw [hσc t s hs hs1]
  · exact fun l => (hjl l).1
  · intro l l' h
    have h1 := (hjl l).2
    rw [h, (hjl l').2] at h1
    rw [← hlvlOf l, ← hlvlOf l', h1]
  · intro j
    by_cases hj : j = jc
    · exact Or.inl hj
    · exact Or.inr ⟨lvlOf (lv j), hjlOf j hj⟩
  · intro l
    obtain ⟨σ, hσ⟩ := hQlev (jl l) (hjl l).1
    refine ⟨σ, fun t s hs hs1 => ?_⟩
    have hlv : lvlOf (lv (jl l)) = l := by rw [(hjl l).2, hlvlOf]
    change (G (ιQ₀ (Q.collar (jl l) (t, halfPoint s hs)))).val = _
    rw [hσ t s hs hs1, hcolapp, hGval, sd.e.symm_apply_apply, hcval]
    have hcl : collarClamp (σ t, halfPoint s hs) = s := by
      rw [collarClamp_of_mem (show (σ t, halfPoint s hs) ∈ circleCollarSource from hs1)]
      rfl
    rw [hcl, hlv]
  · exact fun x => hGK _
  · exact fun x => hGK _
  · intro y hy
    rw [← opensVal_image_pieceSlab D.smooth hab hreg hint x₀] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hk : sd.e (⟨w, hw⟩ : compSet D i x₀) ∈ range ιM₀ ∪ range ιQ₀ := by
      rw [hKcov]
      exact mem_univ _
    have hGe : (G (sd.e (⟨w, hw⟩ : compSet D i x₀))).val = opensVal _ w := by
      rw [hGval, sd.e.symm_apply_apply]
    rcases hk with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact Or.inl ⟨x, by change (G (ιM₀ x)).val = _; rw [hx, hGe]⟩
    · exact Or.inr ⟨x, by change (G (ιQ₀ x)).val = _; rw [hx, hGe]⟩
  · intro x
    have hb := hband (ιM₀ x) (Or.inr ⟨x, rfl⟩)
    exact hGf _ hb.1 hb.2
  · intro x hx
    have hxv : D.f (G (ιQ₀ x)).val =
        pieceFun D.f (slabOpens D i x₀) (sd.e.symm (ιQ₀ x)).val := rfl
    have hy : sd.e (sd.e.symm (ιQ₀ x)) = ιQ₀ x := sd.e.apply_symm_apply _
    have hh : mobiusHeight (ιQ₀ x).val = 0 ∨ mobiusHeight (ιQ₀ x).val = 2 := by
      rcases hx with h | h
      · left
        rw [← hy]
        exact (sd.he _).1.mp (by rw [← hxv]; exact h)
      · right
        rw [← hy]
        exact (sd.he _).2.mp (by rw [← hxv]; exact h)
    obtain ⟨j, t, hj, hxj⟩ := hbdry x hh
    exact ⟨lvlOf (lv j), t, by rw [hjlOf j hj]; exact hxj⟩
  · intro x x' hxx
    have hinj : ιM₀ x = ιQ₀ x' :=
      sd.e.symm.injective (injective_pieceToCore D hab hreg x₀ ha hxx)
    obtain ⟨t, ht⟩ := hov x x' hinj
    exact ⟨t, by change G (ιM₀ x) = G (cK (t, 0)); rw [ht]⟩

end SplitPieces

end GC.Seifert.CoreDecomposition
