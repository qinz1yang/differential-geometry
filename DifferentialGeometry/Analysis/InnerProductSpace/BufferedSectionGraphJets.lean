import DifferentialGeometry.Analysis.InnerProductSpace.OrthogonalErrorCoordinates
import DifferentialGeometry.Analysis.Calculus.Inverse.AllOrderContractionGraphJets
import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionZeroEquivalence
import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphSheetExclusion


set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace DifferentialGeometry.Analysis
universe u

theorem exists_uniform_buffered_section_graph_jets
    (C : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (L : Submodule ℝ H) [CompleteSpace L]
        (b r : ℝ) (o : H) (η : H → H) (Q : H → Submodule ℝ H)
        [∀ z, (Q z).HasOrthogonalProjection] (δ : ℝ),
        1 ≤ b → 0 < r → 0 < δ → δ ≤ δ₀ →
        ContDiffOn ℝ ∞ η (ball o (8 * b * r)) →
        (∀ z ∈ ball o (8 * b * r), η z ∈ Q z) →
        (∀ z ∈ ball o (8 * b * r),
          ‖(Q z).starProjection - Lᗮ.starProjection‖ < 1) →
        (∀ m j, j ≤ m → ∀ z ∈ ball o (8 * b * r),
          ‖iteratedFDeriv ℝ j (fun y => η y - Lᗮ.starProjection (y - o)) z‖ ≤
            C m * δ * r * (r⁻¹) ^ j) →
        ∃ g : L → Lᗮ, ContDiffOn ℝ ∞ g (ball 0 (4 * b * r)) ∧
          (∀ t ∈ ball (0 : L) (4 * b * r), ‖g t‖ ≤ r / 4 ∧
            η (o + orthogonalCoordinateSum L (t, g t)) = 0) ∧
          (∀ t ∈ ball (0 : L) (4 * b * r), ∀ n ∈ closedBall (0 : Lᗮ) r,
            η (o + orthogonalCoordinateSum L (t, n)) = 0 ↔ n = g t) ∧
          (∀ m t, t ∈ ball (0 : L) (4 * b * r) → ∀ j, j ≤ m →
            ‖iteratedFDeriv ℝ j g t‖ ≤ F m * δ * r * (r⁻¹) ^ j) ∧
          {z : H | η z = 0} ∩ ball o (3 * b * r) =
            {z : H | ∃ t ∈ ball (0 : L) (4 * b * r),
              z = o + orthogonalCoordinateSum L (t, g t)} ∩ ball o (3 * b * r) := by
  let J : ℕ → ℝ := fun m => 2 ^ m * C m
  have hJ : ∀ m, 0 ≤ J m := fun m => mul_nonneg (by positivity) (hC m)
  obtain ⟨F, hF, hconstruct⟩ := exists_uniform_allOrder_scaled_contraction_graph_jets.{u,u} J hJ
  let δ₀ : ℝ := min 1 (min (1 / (4 * (C 0 + 1))) (1 / (2 * (C 1 + 1))))
  have hδ₀ : 0 < δ₀ := by
    have h0 := hC 0
    have h1 := hC 1
    dsimp [δ₀]
    positivity
  refine ⟨δ₀, hδ₀, F, hF, ?_⟩
  intro H _ _ _ L _ b r o η Q _ δ hb hr hδ hδsmall hη hmem hgap hamb
  have hδ1 : δ ≤ 1 := (le_min_iff.mp hδsmall).1
  have hbnds := le_min_iff.mp (le_min_iff.mp hδsmall).2
  have hvaluebudget : C 0 * δ ≤ 1 / 4 := by
    have h0 := hC 0
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (C 0 + 1))).mp hbnds.1
    nlinarith
  have hderivbudget : C 1 * δ ≤ 1 / 2 := by
    have h1 := hC 1
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (C 1 + 1))).mp hbnds.2
    nlinarith
  let c : L × Lᗮ → H := fun p => o + orthogonalCoordinateSum L p
  let U : Set L := ball 0 (4 * b * r)
  let V : Set (L × Lᗮ) := c ⁻¹' ball o (8 * b * r)
  let e : L × Lᗮ → Lᗮ := orthogonalSectionError L η o
  have hc : ContDiff ℝ ∞ c := contDiff_const.add (orthogonalCoordinateSum L).contDiff
  have hV : IsOpen V := isOpen_ball.preimage hc.continuous
  have hcylinder : U ×ˢ closedBall (0 : Lᗮ) r ⊆ V := by
    intro p hp
    have ht : ‖p.1‖ < 4 * b * r := by simpa only [U, mem_ball, dist_zero_right] using hp.1
    have hn : ‖p.2‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hp.2
    change dist (o + ((p.1 : H) + (p.2 : H))) o < 8 * b * r
    rw [dist_eq_norm]
    have heq : o + ((p.1 : H) + (p.2 : H)) - o = (p.1 : H) + (p.2 : H) := by abel
    rw [heq]
    have hs := norm_add_le (p.1 : H) (p.2 : H)
    change ‖(p.1 : H) + (p.2 : H)‖ ≤ ‖p.1‖ + ‖p.2‖ at hs
    have hbr : r ≤ b * r := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb hr.le
    nlinarith
  have he : ContDiffOn ℝ ∞ e V :=
    (Lᗮ.orthogonalProjectionOnto.contDiff.comp_contDiffOn
      (hη.comp hc.contDiffOn (fun _ hp => hp))).sub contDiffOn_snd
  have hηat (p : L × Lᗮ) (hp : p ∈ V) : ContDiffAt ℝ ∞ η (c p) :=
    hη.contDiffAt (isOpen_ball.mem_nhds hp)
  have hevalue (p : L × Lᗮ) (hp : p ∈ V) : ‖e p‖ ≤ C 0 * δ * r := by
    have hh := norm_iteratedFDeriv_orthogonalSectionError_le L η o p 0
      ((hηat p hp).of_le (by simp))
    simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at hh
    have hraw := hamb 0 0 le_rfl (c p) hp
    simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one] at hraw
    exact hh.trans hraw
  have hsmall : ∀ t ∈ U, ∀ n ∈ closedBall (0 : Lᗮ) r, ‖e (t,n)‖ ≤ r / 4 := by
    intro t ht n hn
    apply (hevalue (t,n) (hcylinder ⟨ht,hn⟩)).trans
    nlinarith [mul_le_mul_of_nonneg_right hvaluebudget hr.le]
  have hnormal : ∀ t ∈ U, ∀ n ∈ closedBall (0 : Lᗮ) r,
      ‖fderiv ℝ (fun z => e (t,z)) n‖ ≤ 1 / 2 := by
    intro t ht n hn
    have hp : (t,n) ∈ V := hcylinder ⟨ht,hn⟩
    apply (norm_fderiv_normal_orthogonalSectionError_le L η o t n
      ((hηat (t,n) hp).differentiableAt (by simp))).trans
    have hh := hamb 1 1 le_rfl (c (t,n)) hp
    rw [norm_iteratedFDeriv_one, pow_one, mul_assoc, mul_inv_cancel₀ hr.ne', mul_one] at hh
    exact hh.trans hderivbudget
  have herr : ∀ m, ∀ p ∈ V, ∀ j, j ≤ m →
      ‖iteratedFDeriv ℝ j e p‖ ≤ J m * δ * r * (r⁻¹) ^ j := by
    intro m p hp j hj
    have hh := norm_iteratedFDeriv_orthogonalSectionError_le L η o p j
      ((hηat p hp).of_le (by simp))
    calc
      _ ≤ 2 ^ j * (C m * δ * r * (r⁻¹) ^ j) :=
        hh.trans (mul_le_mul_of_nonneg_left (hamb m j hj (c p) hp) (by positivity))
      _ ≤ 2 ^ m * (C m * δ * r * (r⁻¹) ^ j) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj)
          (mul_nonneg (mul_nonneg (mul_nonneg (hC m) hδ.le) hr.le) (by positivity))
      _ = _ := by dsimp only [J]; ring
  obtain ⟨g, hg, hvalue, huniq, hjets⟩ := hconstruct Lᗮ L U V isOpen_ball hV r δ hr
    hδ.le hδ1 hcylinder e he hsmall hnormal herr
  have hzero (p : L × Lᗮ) (hp : p ∈ V) : p.2 + e p = 0 ↔ η (c p) = 0 := by
    have heq : p.2 + e p = Lᗮ.orthogonalProjectionOnto (η (c p)) := by
      change p.2 + (Lᗮ.orthogonalProjectionOnto (η (c p)) - p.2) = _
      abel
    rw [heq]
    exact Submodule.orthogonalProjectionOnto_eq_zero_iff_of_mem_of_norm_sub_lt_one
      Lᗮ (Q (c p)) (hgap (c p) hp) (hmem (c p) hp)
  have hgraph : ∀ t ∈ U, ‖g t‖ ≤ r / 4 ∧ η (c (t,g t)) = 0 := by
    intro t ht
    have hgn : g t ∈ closedBall (0 : Lᗮ) r := by
      rw [mem_closedBall, dist_zero_right]
      exact (hvalue t ht).1.trans (by linarith)
    exact ⟨(hvalue t ht).1, (hzero (t,g t) (hcylinder ⟨ht,hgn⟩)).mp (hvalue t ht).2⟩
  have hunique : ∀ t ∈ U, ∀ n ∈ closedBall (0 : Lᗮ) r,
      η (c (t,n)) = 0 ↔ n = g t := by
    intro t ht n hn
    exact (hzero (t,n) (hcylinder ⟨ht,hn⟩)).symm.trans (huniq t ht n hn)
  refine ⟨g, hg, hgraph, hunique, hjets, ?_⟩
  apply zeroSet_inter_ball_eq_normalGraph_of_error_le L o η g r b hr hb
    (fun t ht => (hgraph t ht).2) (fun t ht n hn hzero => (hunique t ht n hn).mp hzero)
  intro z hz
  have hzbig : z ∈ ball o (8 * b * r) := by
    have hzdist : dist z o < 3 * b * r := hz
    change dist z o < 8 * b * r
    have hbr : 0 < b * r := mul_pos (zero_lt_one.trans_le hb) hr
    nlinarith
  have hh := hamb 0 0 le_rfl z hzbig
  simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one] at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hvaluebudget hr.le])

end DifferentialGeometry.Analysis
