import DifferentialGeometry.Geometry.Metric.CloudDisplacementJets
import DifferentialGeometry.Topology.Manifold.NormalSectionSubmersion
import DifferentialGeometry.Analysis.InnerProductSpace.OrthogonalErrorCoordinates
import DifferentialGeometry.Analysis.Calculus.Inverse.AllOrderContractionGraphJets

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Topology Manifold
namespace GC.MetricGeometry
universe u

theorem exists_uniform_cloud_normal_graph_jets (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ →
        (∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x)) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        let ℓ : ℝ := 1 / (100 * (C + 1))
        let α : ℝ := ℓ / 4
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (ℓ * r i)) ∧
          ((⋃ x ∈ S, ball x (ℓ * r x)) ⊆ ⋃ i ∈ I, ball i (5 * ℓ * r i)) ∧
          let w : H → H → ℝ := fun i y =>
            ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)
          let Q : H → Submodule ℝ H := fun y =>
            ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          let η : H → H := fun y => (Q y).starProjection
            (y - ∑ i ∈ hI.toFinset, w i y • i)
          ContDiffOn ℝ ∞ η (⋃ i ∈ I, ball i (6 * ℓ * r i)) ∧
          (∀ x₀ ∈ I, ∀ v ∈ ball x₀ (5*ℓ*r x₀),
            (∀ z ∈ ball v (ℓ*r x₀), Manifold.IsSubmersionAt
              𝓘(ℝ,H) 𝓘(ℝ,(P x₀)ᗮ) ∞
                (fun y => (P x₀)ᗮ.orthogonalProjectionOnto (η y)) z) ∧
            {z : H | z ∈ ball v (ℓ*r x₀) ∧ (P x₀)ᗮ.orthogonalProjectionOnto (η z)=0} =
            {z : H | z ∈ ball v (ℓ*r x₀) ∧ η z=0}) ∧
          ∀ i ∈ I, ∃ g : P i → (P i)ᗮ,
            ContDiffOn ℝ ∞ g (ball 0 (α * r i)) ∧
            (∀ t ∈ ball 0 (α * r i), ‖g t‖ ≤ α * r i / 4 ∧
              η (i + orthogonalCoordinateSum (P i) (t, g t)) = 0) ∧
            (∀ t ∈ ball 0 (α * r i), ∀ n ∈ closedBall 0 (α * r i),
              η (i + orthogonalCoordinateSum (P i) (t,n)) = 0 ↔ n = g t) ∧
            ∀ m, ∀ t ∈ ball 0 (α * r i), ∀ j, j ≤ m →
              ‖iteratedFDeriv ℝ j g t‖ ≤ F m * δ * r i * ((r i)⁻¹)^j := by
  classical
  obtain ⟨B, E, hprod⟩ := exists_uniform_cloud_displacement_jets.{u} k C hC
  let ℓ : ℝ := 1 / (100 * (C + 1))
  let α : ℝ := ℓ / 4
  let A : ℝ := 2 * (C + 1)
  let K : ℝ := 24 * (A + 1)
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by
    dsimp [α, ℓ]
    have hd : 0 < 100 * (C + 1) := by positivity
    have hh : (1 : ℝ) / (100 * (C + 1)) ≤ 1 :=
      (div_le_iff₀ hd).mpr (by nlinarith)
    linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let J : ℕ → ℝ := fun m => 2^m * (E m : ℝ) / α
  have hJ : ∀ m, 0 ≤ J m := by intro m; dsimp [J]; positivity
  obtain ⟨G, hG, hconstruct⟩ := exists_uniform_allOrder_scaled_contraction_graph_jets.{u,u} J hJ
  let F : ℕ → ℝ := fun m => G m * α * (α⁻¹)^m
  have hF : ∀ m, 0 ≤ F m := by
    intro m
    exact mul_nonneg (mul_nonneg (hG m) hα.le) (pow_nonneg (inv_nonneg.mpr hα.le) m)
  let δ₀ : ℝ := min (ℓ / (2*A)) (min 1
    (min (α / (4*((E 0 : ℝ)+1)))
      (min (1 / (2*((E 1 : ℝ)+1))) (1 / (2*(K+1))))))
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  refine ⟨δ₀, hδ₀, F, hF, ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall hscale hcloud
  have hb := (le_min_iff.mp hδsmall)
  have hb1 := le_min_iff.mp hb.2
  have hb2 := le_min_iff.mp hb1.2
  have hb3 := le_min_iff.mp hb2.2
  have hvaluebudget : (E 0 : ℝ)*δ ≤ α/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*((E 0 : ℝ)+1))).mp hb2.1
    nlinarith
  have hderivbudget : (E 1 : ℝ)*δ ≤ 1/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*((E 1 : ℝ)+1))).mp hb3.1
    nlinarith
  have hgap : K*δ < 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(K+1))).mp hb3.2
    nlinarith
  obtain ⟨I,hI,hIS,hdisj,hcover,_hw,_hQ,_hrank,hη,hlocal⟩ :=
    hprod H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hb.1 hscale hcloud
  refine ⟨I,hI,hIS,hdisj,hcover,hη,?_⟩
  dsimp only
  let w : H → H → ℝ := fun i y =>
    ballCutoff i (10*ℓ*r i) (2*(10*ℓ*r i)) y /
      (∑ a ∈ hI.toFinset, ballCutoff a (10*ℓ*r a) (2*(10*ℓ*r a)) y)
  let Q : H → Submodule ℝ H := fun y =>
    ⨆ μ ∈ ball (1 : ℝ) (1/2), Module.End.eigenspace
      (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
  let η : H → H := fun y => (Q y).starProjection (y-∑ i ∈ hI.toFinset,w i y • i)
  constructor
  · intro x₀ hx₀ v hv
    have hr₀ : 0 < r x₀ := hrmin.trans_le (hlower x₀ (hIS hx₀))
    have hUΩ : ball v (ℓ*r x₀) ⊆ ⋃ i ∈ I, ball i (6*ℓ*r i) := by
      intro z hz
      apply mem_iUnion₂.mpr ⟨x₀,hx₀,?_⟩
      have ht := dist_triangle z v x₀
      have hv' : dist v x₀ < 5*ℓ*r x₀ := hv
      have hz' : dist z v < ℓ*r x₀ := hz
      change dist z x₀ < 6*ℓ*r x₀
      linarith
    have hηU : ContDiffOn ℝ ∞ η (ball v (ℓ*r x₀)) := hη.mono hUΩ
    have herror (z : H) (hz : z ∈ ball v (ℓ*r x₀)) :
        ‖fderiv ℝ (fun y => η y-(P x₀)ᗮ.starProjection (y-x₀)) z‖ < 1 := by
      have hb := ((hlocal x₀ hx₀ v hv).2.2 1 1 le_rfl z hz).2
      rw [pow_one,mul_assoc,mul_inv_cancel₀ hr₀.ne',mul_one,
        norm_iteratedFDeriv_one] at hb
      exact (hb.trans hderivbudget).trans_lt (by norm_num)
    refine ⟨Submodule.isSubmersionAt_orthogonalProjectionOnto_of_affine_error
      (P x₀)ᗮ η x₀ isOpen_ball hηU herror,?_⟩
    apply Submodule.orthogonalProjectionOnto_projected_displacement_zeroSet
    intro z hz
    exact (((hlocal x₀ hx₀ v hv).2.1 z hz).2).trans_lt hgap
  · intro i hi
    have hr : 0 < r i := hrmin.trans_le (hlower i (hIS hi))
    have hii : i ∈ ball i (5*ℓ*r i) := by rw [mem_ball,dist_self]; positivity
    obtain ⟨hQi,hri,hji⟩ := hlocal i hi i hii
    let L := P i
    let ρ : ℝ := α*r i
    let c : L × Lᗮ → H := fun p => i + orthogonalCoordinateSum L p
    let U : Set L := ball 0 ρ
    let W : Set (L × Lᗮ) := c ⁻¹' ball i (ℓ*r i)
    let e : L × Lᗮ → Lᗮ := orthogonalSectionError L η i
    have hρ : 0 < ρ := mul_pos hα hr
    have hc : ContDiff ℝ ∞ c := contDiff_const.add (orthogonalCoordinateSum L).contDiff
    have hW : IsOpen W := isOpen_ball.preimage hc.continuous
    have hcylinder : U ×ˢ closedBall (0 : Lᗮ) ρ ⊆ W := by
      intro p hp
      have ht : ‖p.1‖ < ρ := by simpa only [U, mem_ball, dist_zero_right] using hp.1
      have hn : ‖p.2‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hp.2
      change dist (i + ((p.1 : H)+(p.2 : H))) i < ℓ*r i
      rw [dist_eq_norm]
      have heq : i + ((p.1 : H)+(p.2 : H)) - i = (p.1 : H)+(p.2 : H) := by abel
      rw [heq]
      have hsum := norm_add_le (p.1 : H) (p.2 : H)
      change ‖(p.1 : H)+(p.2 : H)‖ ≤ ‖p.1‖+‖p.2‖ at hsum
      calc
        _ ≤ ‖p.1‖ + ‖p.2‖ := hsum
        _ < ρ + ρ := add_lt_add_of_lt_of_le ht hn
        _ < ℓ*r i := by dsimp [ρ, α]; nlinarith [mul_pos hℓ hr]
    have hηi : ContDiffOn ℝ ∞ η (ball i (ℓ*r i)) := by
      apply hη.mono
      intro y hy
      refine mem_iUnion₂.mpr ⟨i,hi,?_⟩
      have hd : dist y i < ℓ*r i := hy
      change dist y i < 6*ℓ*r i
      nlinarith [mul_pos hℓ hr]
    have he : ContDiffOn ℝ ∞ e W := by
      exact (Lᗮ.orthogonalProjectionOnto.contDiff.comp_contDiffOn
        (hηi.comp hc.contDiffOn (fun _ hp => hp))).sub contDiffOn_snd
    have hηat (p : L × Lᗮ) (hp : p ∈ W) : ContDiffAt ℝ ∞ η (c p) :=
      hηi.contDiffAt (isOpen_ball.mem_nhds hp)
    have hamb (m j : ℕ) (hj : j ≤ m) (p : L × Lᗮ) (hp : p ∈ W) :
        ‖iteratedFDeriv ℝ j (fun y => η y-Lᗮ.starProjection (y-i)) (c p)‖ ≤
          (E m : ℝ)*δ*r i*((r i)⁻¹)^j := (hji m j hj (c p) hp).2
    have hevalue (p : L × Lᗮ) (hp : p ∈ W) : ‖e p‖ ≤ (E 0 : ℝ)*δ*r i := by
      have hh := norm_iteratedFDeriv_orthogonalSectionError_le L η i p 0
        ((hηat p hp).of_le (by simp))
      simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at hh
      exact hh.trans (by simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hamb 0 0 le_rfl p hp)
    have hsmall : ∀ t ∈ U, ∀ n ∈ closedBall (0 : Lᗮ) ρ, ‖e (t,n)‖ ≤ ρ/4 := by
      intro t ht n hn
      apply (hevalue (t,n) (hcylinder ⟨ht,hn⟩)).trans
      have hh := mul_le_mul_of_nonneg_right hvaluebudget hr.le
      dsimp [ρ]
      nlinarith
    have hnormal : ∀ t ∈ U, ∀ n ∈ closedBall (0 : Lᗮ) ρ,
        ‖fderiv ℝ (fun z => e (t,z)) n‖ ≤ 1/2 := by
      intro t ht n hn
      have hp : (t,n) ∈ W := hcylinder ⟨ht,hn⟩
      apply (norm_fderiv_normal_orthogonalSectionError_le L η i t n
        ((hηat (t,n) hp).differentiableAt (by simp))).trans
      have hh := hamb 1 1 le_rfl (t,n) hp
      rw [norm_iteratedFDeriv_one,pow_one,mul_assoc,mul_inv_cancel₀ hr.ne',mul_one] at hh
      exact hh.trans hderivbudget
    have herr : ∀ m, ∀ p ∈ W, ∀ j, j ≤ m →
        ‖iteratedFDeriv ℝ j e p‖ ≤ J m*δ*ρ*(ρ⁻¹)^j := by
      intro m p hp j hj
      have hcoord := norm_iteratedFDeriv_orthogonalSectionError_le L η i p j
        ((hηat p hp).of_le (by simp))
      have hpow : (2 : ℝ)^j ≤ 2^m := pow_le_pow_right₀ (by norm_num) hj
      have hainv : 1 ≤ α⁻¹ := by
        rw [inv_eq_one_div]
        exact (le_div_iff₀ hα).mpr (by simpa only [one_mul] using hα1)
      have haPow : 1 ≤ (α⁻¹)^j := one_le_pow₀ hainv
      calc
        _ ≤ 2^j*((E m : ℝ)*δ*r i*((r i)⁻¹)^j) :=
          hcoord.trans (mul_le_mul_of_nonneg_left (hamb m j hj p hp) (by positivity))
        _ ≤ 2^m*((E m : ℝ)*δ*r i*((r i)⁻¹)^j)*(α⁻¹)^j := by
          calc
            _ ≤ 2^m*((E m : ℝ)*δ*r i*((r i)⁻¹)^j) :=
              mul_le_mul_of_nonneg_right hpow (by positivity)
            _ ≤ _ := le_mul_of_one_le_right (by positivity) haPow
        _ = J m*δ*ρ*(ρ⁻¹)^j := by
          dsimp [J,ρ]
          rw [mul_inv_rev,mul_pow]
          field_simp [hα.ne']
    obtain ⟨g,hg,hvalue,huniq,hjets⟩ := hconstruct Lᗮ L U W isOpen_ball hW ρ δ hρ
      hδ.le hb1.1 hcylinder e he hsmall hnormal herr
    have hzero (p : L × Lᗮ) (hp : p ∈ W) : p.2+e p=0 ↔ η (c p)=0 := by
      have heq : p.2+e p = Lᗮ.orthogonalProjectionOnto (η (c p)) := by
        change p.2 + (Lᗮ.orthogonalProjectionOnto (η (c p))-p.2) = _
        abel
      rw [heq]
      exact Submodule.orthogonalProjectionOnto_eq_zero_iff_of_mem_of_norm_sub_lt_one
        Lᗮ (Q (c p)) (((hri (c p) hp).2).trans_lt hgap)
        ((Q (c p)).starProjection_apply_mem _)
    refine ⟨g,hg,?_,?_,?_⟩
    · intro t ht
      have hgn : g t ∈ closedBall (0 : Lᗮ) ρ := by
        rw [mem_closedBall,dist_zero_right]
        exact (hvalue t ht).1.trans (by linarith)
      exact ⟨(hvalue t ht).1,(hzero (t,g t) (hcylinder ⟨ht,hgn⟩)).mp (hvalue t ht).2⟩
    · intro t ht n hn
      exact (hzero (t,n) (hcylinder ⟨ht,hn⟩)).symm.trans (huniq t ht n hn)
    · intro m t ht j hj
      have hh := hjets m t ht j hj
      have hainv : 1 ≤ α⁻¹ := by
        rw [inv_eq_one_div]
        exact (le_div_iff₀ hα).mpr (by simpa only [one_mul] using hα1)
      have hpow : (α⁻¹)^j ≤ (α⁻¹)^m := pow_le_pow_right₀ hainv hj
      apply hh.trans
      change G m*δ*(α*r i)*((α*r i)⁻¹)^j ≤ _
      rw [mul_inv_rev,mul_pow]
      calc
        _ = (G m*α*(α⁻¹)^j)*δ*r i*((r i)⁻¹)^j := by ring
        _ ≤ (G m*α*(α⁻¹)^m)*δ*r i*((r i)⁻¹)^j :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hG m) hα.le)) hδ.le) hr.le)
            (pow_nonneg (inv_nonneg.mpr hr.le) j)
        _ = F m*δ*r i*((r i)⁻¹)^j := rfl

end GC.MetricGeometry
