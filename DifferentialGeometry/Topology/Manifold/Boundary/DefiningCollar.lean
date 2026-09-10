import DifferentialGeometry.Topology.Manifold.Boundary.DefiningFunction
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Height
import DifferentialGeometry.Topology.Compactness.Nonvanishing
import DifferentialGeometry.Topology.Manifold.Interval.ShorterStrip
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Restriction

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff Topology
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace Poincare.Manifold.Boundary

theorem exists_definingFunction_sublevel_collar
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [CompactSpace M] :
    ∃ r : C(M, ℝ), ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ r ∧
      (∀ x, 0 ≤ r x) ∧ (∀ x, r x = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint x) ∧
      ∃ (a : ℝ) (ha : 0 < a),
        let _ : Fact ((0 : ℝ) < a) := ⟨ha⟩
        ∃ c : C(BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) a, M),
          IsClosedEmbedding c ∧
          ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
            (𝓡∂ (n + 1)) ∞ c ∧
          (∀ p, c (p, ⟨0, ⟨le_rfl, ha.le⟩⟩) = p.val) ∧
          (∀ q, r (c q) = q.2.val) ∧ range c = {x | r x ≤ a} ∧
          let U : Opens (BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) a) :=
            ⟨{q | q.2.val < a}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
          ∃ Y : Opens M, (Y : Set M) = {x | r x < a} ∧
            ∃ d : Diffeomorph ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
              (𝓡∂ (n + 1)) U Y ∞, ∀ q : U, (d q).val = c q.val := by
  let I := 𝓡∂ (n + 1)
  let B := BoundaryManifold I M
  let J := HasSmoothBoundary.boundaryModel I
  have hK : IsCompact (I.boundary M) := (I.isClosed_boundary (n := ∞) (by simp)).isCompact
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hK
  obtain ⟨r, W, hr, hrn, hrzero, _, hBW, V, hV, _, hunit, hpos⟩ :=
    exists_global_boundary_definingFunction hK
  obtain ⟨ε, hε, δ, hδ, hδε, Y, hBY, _, e, he0, heh⟩ :=
    BoundaryCollar.exists_unit_height_boundary_collar hK hV hpos W hBW
      (hr.mdifferentiable (by simp)) (fun p => (hrzero p.val).mpr p.property) hunit
  let _ : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  obtain ⟨η, hη, hηr⟩ := Poincare.Topology.exists_pos_lt_norm_of_isCompact
    Y.isOpen.isClosed_compl.isCompact hr.continuous.continuousOn
    (fun x hx hz => hx (hBY ((hrzero x).mp hz)))
  let a := min (δ / 2) (η / 2)
  have ha : 0 < a := lt_min (half_pos hδ) (half_pos hη)
  have haδ : a < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have haη : a < η := (min_le_right _ _).trans_lt (half_lt_self hη)
  let _ : Fact ((0 : ℝ) < a) := ⟨ha⟩
  let S : Opens (B × Icc (0 : ℝ) ε) :=
    ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
  let j : B × Icc (0 : ℝ) a → S := fun q =>
    ⟨(q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans (haδ.le.trans hδε.le)⟩),
      q.2.property.2.trans_lt haδ⟩
  have hj : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) ∞ j := by
    apply (ContMDiff.subtypeVal_comp_iff S j).mp
    apply contMDiff_fst.prodMk
    apply (contMDiff_iff_comp_subtypeVal_Icc (n := ∞)).mpr
    exact ⟨by fun_prop, (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := a)).comp contMDiff_snd⟩
  let c : C(B × Icc (0 : ℝ) a, M) :=
    ⟨fun q => (e (j q)).val, continuous_subtype_val.comp (e.continuous.comp hj.continuous)⟩
  have hcs : ContMDiff (J.prod (𝓡∂ 1)) I ∞ c :=
    contMDiff_subtype_val.comp (e.contMDiff.comp hj)
  have hcinj : Injective c := by
    intro q p hqp
    have hh := congrArg Subtype.val (e.injective (Subtype.ext hqp))
    have hbase : q.1 = p.1 := congrArg (fun z : B × Icc (0 : ℝ) ε => z.1) hh
    have ht : q.2.val = p.2.val := congrArg (fun z : B × Icc (0 : ℝ) ε => z.2.val) hh
    exact Prod.ext hbase (Subtype.ext ht)
  refine ⟨⟨r, hr.continuous⟩, hr, hrn, hrzero, a, ha, c,
    c.continuous.isClosedEmbedding hcinj, hcs, ?_, ?_, ?_, ?_⟩
  · intro p
    exact he0 p
  · intro q
    exact heh (j q)
  · ext x
    constructor
    · rintro ⟨q, rfl⟩
      change r (e (j q)).val ≤ a
      rw [heh]
      exact q.2.property.2
    · intro hx
      change r x ≤ a at hx
      have hxY : x ∈ Y := by
        by_contra h
        have hh := hηr x h
        rw [Real.norm_eq_abs, abs_of_nonneg (hrn x)] at hh
        linarith
      let q := e.symm ⟨x, hxY⟩
      have hqe : (e q).val = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hxY⟩)
      have hqt : q.val.2.val = r x := (heh q).symm.trans (congrArg r hqe)
      let p : B × Icc (0 : ℝ) a := (q.val.1, ⟨q.val.2.val, q.val.2.property.1, hqt ▸ hx⟩)
      exact ⟨p, hqe⟩
  · let Uε : Opens (B × Icc (0 : ℝ) ε) :=
      ⟨{q | q.2.val < a}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
    have hUεS : Uε ≤ S := fun q hq => hq.trans haδ
    obtain ⟨Y', _, _, d, hd, _⟩ := Poincare.Manifold.Diffeomorph.exists_restrict_opens e Uε hUεS
    have hY'eq : (Y' : Set M) = {x | r x < a} := by
      ext x
      constructor
      · intro hx
        let q := d.symm ⟨x, hx⟩
        have hxq : (d q).val = x := congrArg Subtype.val (d.apply_symm_apply ⟨x, hx⟩)
        have hh : r (d q).val = q.val.2.val := (congrArg r (hd q)).trans (heh _)
        change r x < a
        rw [← hxq, hh]
        exact q.property
      · intro hx
        change r x < a at hx
        have hxY : x ∈ Y := by
          by_contra h
          have hh := hηr x h
          rw [Real.norm_eq_abs, abs_of_nonneg (hrn x)] at hh
          linarith
        let q := e.symm ⟨x, hxY⟩
        have hqe : (e q).val = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hxY⟩)
        have hqt : q.val.2.val = r x := (heh q).symm.trans (congrArg r hqe)
        let q' : Uε := ⟨q.val, by change q.val.2.val < a; rw [hqt]; exact hx⟩
        exact ((hd q').trans hqe) ▸ (d q').property
    let D := (Interval.shorterStripDiffeomorph J (haδ.le.trans hδε.le)).trans d
    refine ⟨Y', hY'eq, D, ?_⟩
    intro q
    exact hd _

end Poincare.Manifold.Boundary
