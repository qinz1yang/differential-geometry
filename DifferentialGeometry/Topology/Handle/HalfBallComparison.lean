import DifferentialGeometry.Topology.Handle.HalfBallAmbientRounding
import DifferentialGeometry.Topology.Handle.RoundedHalfBallComparison
import DifferentialGeometry.Topology.Manifold.AmbientCornerRoundingComparison

open Set Metric
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable (m : ℕ)

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨by simp⟩

theorem exists_diffeomorph_halfBall_comparison
    (c : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))) (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞)
    (D : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))))
    (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {A : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))} {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 2)
    (hc : c.toOpenPartialHomeomorph.IsImage
      {z | ‖z‖ ^ 2 ≤ 1 ∧ 0 ≤ (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1) z).2} A)
    (hK : (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)).symm ''
      (closedBall 0 1 ×ˢ {(0 : ℝ)}) ⊆ c.source)
    (hstrip : (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) ×ˢ
      closedBall (0 : ℝ × ℝ) ε ⊆
      ((c.symm.toOpenPartialHomeomorph.trans
        (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)).toHomeomorph.toOpenPartialHomeomorph).trans
          (OpenPartialHomeomorph.halfBallCorner 1 v)).target)
    (hD : D '' closedBall 0 1 =
      ((c.symm.toOpenPartialHomeomorph.trans
        (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)).toHomeomorph.toOpenPartialHomeomorph).trans
          (OpenPartialHomeomorph.halfBallCorner 1 v)).smoothAbsQuadrantSet A ε) :
    ∃ F : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        (EuclideanSpace ℝ (Fin ((m + 1) + 1))),
      F '' {z | ‖z‖ ^ 2 ≤ 1 ∧ 0 ≤ (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1) z).2} = A ∧
      ∃ U, IsOpen U ∧
        (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)).symm ''
          (closedBall 0 1 ×ˢ {(0 : ℝ)}) ⊆ U ∧ U ⊆ c.source ∧ EqOn F c U := by
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let M := EuclideanSpace ℝ (Fin ((m + 1) + 1))
  let ep := PartialDiffeomorph.halfBallCorner (n := m) 1 v
  let e := L.toDiffeomorph.toPartialDiffeomorph.trans ep
  let f := c.symm.trans e
  let H : Set M := {z | ‖z‖ ^ 2 ≤ 1 ∧ 0 ≤ (L z).2}
  let Hp : Set (E × ℝ) := {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2}
  let K := L.symm '' (closedBall (0 : E) 1 ×ˢ {(0 : ℝ)})
  let Z := (univ : Set (sphere (0 : E) 1)) ×ˢ {(0 : ℝ × ℝ)}
  have hf : f.toOpenPartialHomeomorph =
      (c.symm.toOpenPartialHomeomorph.trans L.toHomeomorph.toOpenPartialHomeomorph).trans
        (OpenPartialHomeomorph.halfBallCorner 1 v) := by
    exact (OpenPartialHomeomorph.trans_assoc _ _ _).symm
  have hstripf : (univ : Set (sphere (0 : E) 1)) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆ f.target := by
    rw [show f.target = f.toOpenPartialHomeomorph.target from rfl, hf]
    exact hstrip
  have htri : {p : sphere (0 : E) 1 × (ℝ × ℝ) |
      0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆ f.target := by
    intro p hp
    apply hstripf
    refine ⟨mem_univ _, ?_⟩
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp.1, abs_of_nonneg hp.2.1]
    constructor <;> linarith [hp.1, hp.2.1, hp.2.2]
  have hraw₀ : ∀ p ∈ e.target, e.symm p ∈ H ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 := by
    intro p hp
    have h := OpenPartialHomeomorph.halfBallCorner_symm_mem_halfBall 1 v hp.1
    change (‖L.symm (ep.symm p)‖ ^ 2 ≤ 1 ∧ 0 ≤ (L (L.symm (ep.symm p))).2) ↔ _
    rw [L.apply_symm_apply, EuclideanSpace.norm_sq_equivProdLast_symm]
    change (‖(ep.symm p).1‖ ^ 2 + (ep.symm p).2 ^ 2 ≤ 1 ^ 2 ∧ 0 ≤ (ep.symm p).2) ↔ _ at h
    simpa only [Real.norm_eq_abs, sq_abs, one_pow] using h
  have hraw₁ : ∀ p ∈ f.target, f.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 := by
    intro p hp
    exact (hc hp.2).trans (hraw₀ p hp.1)
  have hL : L.symm.toHomeomorph.toOpenPartialHomeomorph.IsImage Hp H := by
    intro p hp
    change (‖L.symm p‖ ^ 2 ≤ 1 ∧ 0 ≤ (L (L.symm p)).2) ↔ _
    rw [L.apply_symm_apply, EuclideanSpace.norm_sq_equivProdLast_symm]
    simp only [Real.norm_eq_abs, sq_abs]
    rfl
  have hmodel : e.toOpenPartialHomeomorph.smoothAbsQuadrantSet H ε =
      {z | DifferentialGeometry.Topology.Handle.roundedHalfBallFunction (m + 1) ε 0 z ≤ 0} := by
    have hh := hL.smoothAbsQuadrantSet (OpenPartialHomeomorph.halfBallCorner 1 v) ε
    ext z
    have hz := hh (x := L z) (mem_univ _)
    change L.symm (L z) ∈ e.toOpenPartialHomeomorph.smoothAbsQuadrantSet H ε ↔
      L z ∈ (OpenPartialHomeomorph.halfBallCorner 1 v).smoothAbsQuadrantSet Hp ε at hz
    have hprod := OpenPartialHomeomorph.smoothAbsQuadrantSet_halfBallCorner 1 v hε
      (by simpa using hsmall.trans (by norm_num : (1 : ℝ) / 2 < 1))
    simp only [one_pow] at hprod
    change (OpenPartialHomeomorph.halfBallCorner 1 v).smoothAbsQuadrantSet Hp ε = _ at hprod
    rw [L.symm_apply_apply, hprod] at hz
    change z ∈ e.toOpenPartialHomeomorph.smoothAbsQuadrantSet H ε ↔ _
    rw [hz]
    change Real.smoothMax ε (‖(L z).1‖ ^ 2 + (L z).2 ^ 2 - 1) (-(L z).2) ≤ 0 ↔
      Real.smoothMax ε (‖z‖ ^ 2 - 1) (-(L z).2 - 0) ≤ 0
    rw [EuclideanSpace.norm_sq_equivProdLast (m + 1) z]
    simp only [Real.norm_eq_abs, sq_abs, sub_zero]
    rfl
  obtain ⟨R₀, R₁, h₀, _, _, hCs₀, hfix₀, _, hq₀, _, _,
    _, _, _, _, _, _, hq₁, _, _, _, _, _, _, hcompare⟩ :=
    c.exists_diffeomorph_smoothAbs_corner_comparison e hε hstripf
  have hR₀ : R₀ '' H =
      {z | DifferentialGeometry.Topology.Handle.roundedHalfBallFunction (m + 1) ε 0 z ≤ 0} :=
    (hq₀ H hraw₀).trans hmodel
  have hR₁ : R₁ '' A = f.toOpenPartialHomeomorph.smoothAbsQuadrantSet A ε := hq₁ A hraw₁
  have hcround := hc.smoothAbsQuadrantSet e.toOpenPartialHomeomorph ε
  rw [hmodel] at hcround
  change c.toOpenPartialHomeomorph.IsImage
    {z | DifferentialGeometry.Topology.Handle.roundedHalfBallFunction (m + 1) ε 0 z ≤ 0}
    (f.toOpenPartialHomeomorph.smoothAbsQuadrantSet A ε) at hcround
  rw [hf] at hcround
  obtain ⟨Q, hQ, V, hV, hKV, hVc, hQV⟩ :=
    c.exists_diffeomorph_roundedHalfBall_comparison m D v hε hsmall hD hcround hK
      (by
        have htri' := htri
        change {p : sphere (0 : E) 1 × (ℝ × ℝ) |
          0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆ f.toOpenPartialHomeomorph.target at htri'
        rw [hf] at htri'
        exact htri')
  have hmark (x : E) (hx : x ∈ closedBall 0 1) :
      R₀ (L.symm (x, 0)) = L.symm (DifferentialGeometry.Topology.Handle.halfBallRounding 1 ε (x, 0)) := by
    by_cases hx0 : x = 0
    · subst x
      rw [DifferentialGeometry.Topology.Handle.halfBallRounding_zero_fst]
      apply hfix₀
      intro hh
      have hs := hCs₀ hh
      change True ∧ (L (L.symm (0, 0))).1 ≠ 0 at hs
      exact hs.2 (congrArg Prod.fst (L.apply_symm_apply (0, 0)))
    · have hxs : L.symm (x, 0) ∈ e.source := by
        change True ∧ (L (L.symm (x, 0))).1 ≠ 0
        simpa only [L.apply_symm_apply, true_and] using hx0
      rw [h₀ _ hxs]
      change L.symm (ep.symm ((ep (L (L.symm (x, 0)))).1,
        Homeomorph.smoothAbsCorner hε (ep (L (L.symm (x, 0)))).2)) = _
      rw [L.apply_symm_apply]
      apply congrArg L.symm
      exact (DifferentialGeometry.Topology.Handle.halfBallRounding_eq_smoothAbsCorner 1 v hε
        (by have hn := mem_closedBall_zero_iff.mp hx
            change ‖x‖ ^ 2 + 0 ^ 2 ≤ 1 ^ 2 ∧ 0 ≤ (0 : ℝ)
            exact ⟨by nlinarith [norm_nonneg x], le_rfl⟩) (Or.inr rfl) hx0).symm
  have hRKV : R₀ '' K ⊆ V := by
    rintro z ⟨_, ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩, rfl⟩
    have ht0 : t = 0 := ht
    subst t
    rw [hmark x hx]
    exact hKV ⟨x, hx, rfl⟩
  have hZK : e.symm '' Z ⊆ K := by
    rintro z ⟨⟨θ, w⟩, ⟨_, hw⟩, rfl⟩
    have hw0 : w = 0 := hw
    subst w
    refine ⟨(θ.val, 0), ⟨sphere_subset_closedBall θ.property, rfl⟩, ?_⟩
    change L.symm (θ.val, 0) = L.symm (Real.sqrt (1 ^ 2 - 0 - 0 ^ 2) • θ.val, 0)
    norm_num
  have hQAB : Q '' (R₀ '' H) = R₁ '' A := by
    rw [hR₀, hR₁, hf]
    exact hQ
  obtain ⟨F, _, hFA, hU, _, hFc⟩ := hcompare Q V hV
    ((image_mono hZK).trans hRKV) (hQV.mono inter_subset_left) H A hQAB
  exact ⟨F, hFA, c.source ∩ R₀ ⁻¹' V, hU,
    fun x hx => ⟨hK hx, hRKV ⟨x, hx, rfl⟩⟩, inter_subset_left, hFc⟩

end PartialDiffeomorph
