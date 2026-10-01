import DifferentialGeometry.Geometry.Metric.LargeCloudSpectralJets
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.LocalizedWeightedDisplacement

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff
namespace GC.MetricGeometry
universe u

theorem exists_uniform_large_cloud_displacement_jets
    (k : ℕ) (b B : ℝ) (hb : 1 ≤ b) (hB : 1 ≤ B) :
    ∃ C E : ℕ → ℝ≥0,
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ * ((80 * B + 31) * b + 2) < 1 →
        (∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * b * max (r y) (r x) →
          r x / B ≤ r y ∧ r y ≤ B * r x) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (r i)) ∧
          (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
          ((⋃ x ∈ S, ball x (8 * b * r x)) ⊆ ⋃ i ∈ I, ball i (20 * b * r i)) ∧
          let w : H → H → ℝ := fun i y => ballCutoff i (40 * b * r i) (2 * (40 * b * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (40 * b * r a) (2 * (40 * b * r a)) y)
          let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          (∀ m, ∀ x ∈ S, ∀ j ≤ m, ∀ z ∈ ball x (8 * b * r x),
            (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w i) z‖) ≤ (C m : ℝ) / (r x) ^ j) ∧
          (∀ m, ∀ i ∈ I, ∀ j ≤ m, ∀ z ∈ ball i (30 * b * r i),
            (∑ a ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w a) z‖) ≤ (C m : ℝ) / (r i) ^ j) ∧
          (∀ x ∈ S, ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) (ball x (8 * b * r x)) ∧
              (∀ z ∈ ball x (8 * b * r x), Module.finrank ℝ (Q z) = Module.finrank ℝ H - k ∧
                ‖(Q z).starProjection - (P x)ᗮ.starProjection‖ ≤ 24 * (B + 1) * δ) ∧
              ∀ m : ℕ, ∀ j ≤ m, ∀ z ∈ ball x (8 * b * r x),
                ‖iteratedFDeriv ℝ j (fun y => (Q y).starProjection - (P x)ᗮ.starProjection) z‖ ≤
                  max 4 ((resolventDerivativeBound 4 (C m) j : ℝ) / 2) *
                    (6 * (B + 1)) * δ / (r x) ^ j) ∧
          (∀ i ∈ I, ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) (ball i (30 * b * r i)) ∧
              (∀ z ∈ ball i (30 * b * r i), Module.finrank ℝ (Q z) = Module.finrank ℝ H - k ∧
                ‖(Q z).starProjection - (P i)ᗮ.starProjection‖ ≤ 24 * (B + 1) * δ) ∧
              ∀ m : ℕ, ∀ j ≤ m, ∀ z ∈ ball i (30 * b * r i),
                ‖iteratedFDeriv ℝ j (fun y => (Q y).starProjection - (P i)ᗮ.starProjection) z‖ ≤
                  max 4 ((resolventDerivativeBound 4 (C m) j : ℝ) / 2) *
                    (6 * (B + 1)) * δ / (r i) ^ j) ∧
          let η : H → H := fun y => (Q y).starProjection
            (y-∑ i ∈ hI.toFinset, w i y • i)
          let Ω : Set H := ⋃ i ∈ I, ball i (30*b*r i)
          ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) Ω ∧
          (∀ z ∈ Ω, Module.finrank ℝ (Q z)=Module.finrank ℝ H-k) ∧
          ContDiffOn ℝ ∞ η Ω ∧
          (∀ m, ∀ x ∈ S, ∀ j ≤ m, ∀ z ∈ ball x (8*b*r x),
            ‖iteratedFDeriv ℝ j (fun y => η y-(P x)ᗮ.starProjection (y-x)) z‖ ≤
              (E m : ℝ)*δ*r x*((r x)⁻¹)^j) ∧
          (∀ m, ∀ i ∈ I, ∀ j ≤ m, ∀ z ∈ ball i (30*b*r i),
            ‖iteratedFDeriv ℝ j (fun y => η y-(P i)ᗮ.starProjection (y-i)) z‖ ≤
              (E m : ℝ)*δ*r i*((r i)⁻¹)^j) := by
  classical
  obtain ⟨C,hbound⟩ := exists_uniform_large_cloud_spectral_projection_jets.{u} k b B hb hB
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  let D : ℝ≥0 := ⟨(80*B+31)*b, by positivity⟩
  let R₀ : ℝ≥0 := ⟨30*b, by positivity⟩
  let F : ℕ → ℕ → ℝ≥0 := fun m j =>
    ⟨max 4 ((resolventDerivativeBound 4 (C m) j : ℝ)/2)*(6*(B+1)), by positivity⟩
  let M : ℕ → ℝ≥0 := fun m => ∑ j ∈ Finset.range (m+1), F m j
  let E : ℕ → ℝ≥0 := fun m => 2^m*M m*(max R₀ 1+D*C m)+C m
  refine ⟨C,E,?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hinterior hscale hcloud
  obtain ⟨I,hI,hIS,hdisj,hcover,htube,hcore,hselected,hsc,hss⟩ :=
    hbound H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hinterior hscale hcloud
  refine ⟨I,hI,hIS,hdisj,hcover,htube,?_⟩
  dsimp only
  let w : H → H → ℝ := fun i y => ballCutoff i (40*b*r i) (2*(40*b*r i)) y /
    (∑ a ∈ hI.toFinset, ballCutoff a (40*b*r a) (2*(40*b*r a)) y)
  let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1/2), Module.End.eigenspace
    (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
  let η : H → H := fun y => (Q y).starProjection (y-∑ i ∈ hI.toFinset, w i y • i)
  let Ω : Set H := ⋃ i ∈ I, ball i (30*b*r i)
  have hr (i : H) (hi : i ∈ S) : 0 < r i := hrmin.trans_le (hlower i hi)
  have hρ (i : H) (hi : i ∈ hI.toFinset) : 0 < 40*b*r i := by
    have hp := hr i (hIS (hI.mem_toFinset.mp hi))
    positivity
  have hplateau (y : H) (hy : y ∈ Ω) : ∃ i ∈ hI.toFinset, dist y i ≤ 40*b*r i := by
    obtain ⟨i,hi,hyi⟩ := mem_iUnion₂.mp hy
    refine ⟨i,hI.mem_toFinset.mpr hi,?_⟩
    have hh : dist y i < 30*b*r i := hyi
    have hp := mul_pos hbpos (hr i (hIS hi))
    nlinarith
  have hwglobal (i : H) : ContDiffOn ℝ ∞ (w i) Ω :=
    contDiffOn_normalized_ballCutoff_of_cover hI.toFinset (fun i => i)
      (fun i => 40*b*r i) hρ hplateau i
  have hw1 (y : H) (hy : y ∈ Ω) : ∑ i ∈ hI.toFinset, w i y=1 :=
    sum_normalized_ballCutoffs_eq_one_of_cover hI.toFinset (fun i => i)
      (fun i => 40*b*r i) hρ (hplateau y hy)
  have hQglobal : ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) Ω := by
    intro z hz
    obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hz
    exact ((hss i hi).1.contDiffAt (isOpen_ball.mem_nhds hzi)).contDiffWithinAt
  have hrankglobal (z : H) (hz : z ∈ Ω) : Module.finrank ℝ (Q z)=Module.finrank ℝ H-k := by
    obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hz
    exact ((hss i hi).2.1 z hzi).1
  have hηglobal : ContDiffOn ℝ ∞ η Ω :=
    hQglobal.clm_apply (contDiffOn_id.sub
      (ContDiffOn.sum (fun i _ => (hwglobal i).smul_const i)))
  have hgeometry := large_cloud_selected_center_geometry S T hST r (fun x : S => P x)
    k (fun x => hdim x x.property) I hIS hI hdisj hr b B δ hb hB hδ hinterior hscale
      (fun x => hcloud x x.property)
  have hlocal (x : H) (hx : x ∈ S) (U : Set H) (hU : IsOpen U)
      (hU30 : U ⊆ ball x (30*b*r x)) (hUΩ : U ⊆ Ω)
      (hjets : ∀ m, ∀ j ≤ m, ∀ z ∈ U,
        ‖iteratedFDeriv ℝ j (fun y => (Q y).starProjection-(P x)ᗮ.starProjection) z‖ ≤
          max 4 ((resolventDerivativeBound 4 (C m) j : ℝ)/2)*(6*(B+1))*δ/(r x)^j)
      (hweights : ∀ m, ∀ j ≤ m, ∀ z ∈ U,
        (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w i) z‖) ≤ (C m : ℝ)/(r x)^j) :
      ∀ m, ∀ j ≤ m, ∀ z ∈ U,
        ‖iteratedFDeriv ℝ j (fun y => η y-(P x)ᗮ.starProjection (y-x)) z‖ ≤
          (E m : ℝ)*δ*r x*((r x)⁻¹)^j := by
    have hcenters (i : H) (hi : i ∈ hI.toFinset) (ha : ∃ y ∈ U, w i y ≠ 0) :
        ‖i-x‖ ≤ D*r x ∧ ‖(P x)ᗮ.starProjection (i-x)‖ ≤ δ*r x := by
      obtain ⟨y,hy,hne⟩ := ha
      have hin : y ∈ ball i (2*(40*b*r i)) := by
        by_contra hnot
        apply hne
        change ballCutoff i (40*b*r i) (2*(40*b*r i)) y / _ = 0
        rw [ballCutoff_eq_zero_of_not_mem_ball (hρ i hi).le (by linarith [hρ i hi]) hnot,zero_div]
      have hclosed : y ∈ closedBall i (80*b*r i) := by
        have heq : 2*(40*b*r i)=80*b*r i := by ring
        rw [← heq]
        exact ball_subset_closedBall hin
      have hg := (hgeometry ⟨x,hx⟩).2 i ⟨hI.mem_toFinset.mp hi,y,hclosed,hU30 hy⟩
      refine ⟨?_,hg.2.2.2.1⟩
      change ‖i-x‖ ≤ ((80*B+31)*b)*r x
      simpa only [dist_eq_norm] using hg.2.2.1.le
    intro m j hj z hz
    have hF (q : ℕ) (hq : q ≤ m) : F m q ≤ M m :=
      Finset.single_le_sum (fun a _ => (show 0 ≤ F m a from bot_le))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
    have hwjet (q : ℕ) (hq : q ≤ m) :
        (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ q (w i) z‖) ≤ C m*((r x)⁻¹)^q := by
      simpa only [div_eq_mul_inv,inv_pow] using hweights m q hq z hz
    have hQjet (q : ℕ) (hq : q ≤ m) :
        ‖iteratedFDeriv ℝ q (fun y => (Q y).starProjection-(P x)ᗮ.starProjection) z‖ ≤
          M m*δ*((r x)⁻¹)^q := by
      have hf : ‖iteratedFDeriv ℝ q (fun y => (Q y).starProjection-(P x)ᗮ.starProjection) z‖ ≤
          F m q*δ*((r x)⁻¹)^q := by
        change ‖iteratedFDeriv ℝ q (fun y => (Q y).starProjection-(P x)ᗮ.starProjection) z‖ ≤
          (max 4 ((resolventDerivativeBound 4 (C m) q : ℝ)/2)*(6*(B+1)))*δ*((r x)⁻¹)^q
        simpa only [div_eq_mul_inv,inv_pow,mul_assoc] using hjets m q hq z hz
      exact hf.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (hF q hq)) hδ.le)
        (pow_nonneg (inv_nonneg.mpr (hr x hx).le) _))
    have hznorm : ‖z-x‖ ≤ R₀*r x := by
      change ‖z-x‖ ≤ (30*b)*r x
      simpa only [dist_eq_norm] using (show dist z x < 30*b*r x from hU30 hz).le
    have hd := norm_iteratedFDeriv_weighted_displacement_sub_translate_le_of_active_bounds
      hI.toFinset hU (fun i _ => ((hwglobal i).mono hUΩ).of_le (by simp))
      (fun y hy => hw1 y (hUΩ hy)) ((hQglobal.mono hUΩ).of_le (by simp))
      (P x)ᗮ.starProjection (fun i => i) x hz (hr x hx) hδ.le
      (M m) (C m) D R₀ 1 hwjet hQjet
      (fun i hi ha => (hcenters i hi ha).1)
      (fun i hi ha => by simpa using (hcenters i hi ha).2) hznorm j hj
    apply hd.trans
    have hpow : (2 : ℝ)^j ≤ 2^m := pow_le_pow_right₀ (by norm_num) hj
    have hcoef : (2 : ℝ)^j*M m*(max (R₀ : ℝ) 1+D*C m)+(1 : ℝ≥0)*C m ≤ E m := by
      simp only [E,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat,
        NNReal.coe_max,NNReal.coe_one,one_mul]
      gcongr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hδ.le) (hr x hx).le)
      (pow_nonneg (inv_nonneg.mpr (hr x hx).le) _)
  refine ⟨hcore,hselected,hsc,hss,hQglobal,hrankglobal,hηglobal,?_,?_⟩
  · intro m x hx j hj z hz
    apply hlocal x hx (ball x (8*b*r x)) isOpen_ball ?_ ?_
      (hsc x hx).2.2 (fun m j hj z hz => hcore m x hx j hj z hz) m j hj z hz
    · intro y hy
      have hh : dist y x < 8*b*r x := hy
      change dist y x < 30*b*r x
      nlinarith [mul_pos hbpos (hr x hx)]
    · intro y hy
      obtain ⟨i,hi,hyi⟩ := mem_iUnion₂.mp (htube (mem_iUnion₂.mpr ⟨x,hx,hy⟩))
      refine mem_iUnion₂.mpr ⟨i,hi,?_⟩
      have hh : dist y i < 20*b*r i := hyi
      change dist y i < 30*b*r i
      nlinarith [mul_pos hbpos (hr i (hIS hi))]
  · intro m i hi j hj z hz
    exact hlocal i (hIS hi) (ball i (30*b*r i)) isOpen_ball Subset.rfl
      (fun y hy => mem_iUnion₂.mpr ⟨i,hi,hy⟩)
      (hss i hi).2.2 (fun m j hj z hz => hselected m i hi j hj z hz) m j hj z hz

end GC.MetricGeometry
