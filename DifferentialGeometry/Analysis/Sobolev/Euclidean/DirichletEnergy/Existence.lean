import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.Affine
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.WeakGradient
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.WeakLowerSemicontinuity
import Mathlib.Topology.Order.IsLUB
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Poincare

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Y" => Lp E 2 (volume.restrict Ω)

omit [NeZero d] in
private def affineWitness {u b : E → ℝ}
    (hb : DeGiorgi.MemW1pWitness 2 b Ω)
    (hd : DeGiorgi.MemW1pWitness 2 (fun x => u x - b x) Ω) :
    DeGiorgi.MemW1pWitness 2 u Ω where
  memLp := by
    convert hd.memLp.add hb.memLp using 1
    funext x
    exact (sub_add_cancel (u x) (b x)).symm
  weakGrad := (hd.add hb).weakGrad
  weakGrad_component_memLp := (hd.add hb).weakGrad_component_memLp
  isWeakGrad := by simpa only [sub_add_cancel] using (hd.add hb).isWeakGrad

omit [NeZero d] in
private theorem gradLpOfWitness_eq (hΩ : IsOpen Ω)
    {u : E → ℝ} (h₁ h₂ : DeGiorgi.MemW1pWitness 2 u Ω) :
    DeGiorgi.gradLpOfWitness h₁ = DeGiorgi.gradLpOfWitness h₂ := by
  have hcoord (i : Fin d) : (fun x => h₁.weakGrad x i) =ᵐ[volume.restrict Ω]
      (fun x => h₂.weakGrad x i) :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ (h₁.isWeakGrad i) (h₂.isWeakGrad i)
      ((h₁.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
      ((h₂.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hcoord, h₁.weakGrad_memLp.coeFn_toLp,
    h₂.weakGrad_memLp.coeFn_toLp] with x hx h₁x h₂x
  change h₁.weakGrad_memLp.toLp h₁.weakGrad x = h₂.weakGrad_memLp.toLp h₂.weakGrad x
  rw [h₁x, h₂x]
  exact PiLp.ext hx

omit [NeZero d] in
private theorem gradient_coordinate_sum_le {u : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω) :
    (∑ j : Fin d, eLpNorm (fun x => hu.weakGrad x j) 2 (volume.restrict Ω)) ≤
      ENNReal.ofReal ((d : ℝ) * ‖DeGiorgi.gradLpOfWitness hu‖) := by
  have hnorm : eLpNorm hu.weakGrad 2 (volume.restrict Ω) =
      ENNReal.ofReal ‖DeGiorgi.gradLpOfWitness hu‖ := by
    rw [DeGiorgi.gradLpOfWitness, Lp.norm_toLp,
      ENNReal.ofReal_toReal hu.weakGrad_memLp.eLpNorm_lt_top.ne]
  have hcoord (j : Fin d) : eLpNorm (fun x => hu.weakGrad x j) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal ‖DeGiorgi.gradLpOfWitness hu‖ := by
    rw [← hnorm]
    exact eLpNorm_mono_ae (Eventually.of_forall fun x => PiLp.norm_apply_le _ j)
  calc
    _ ≤ ∑ _j : Fin d, ENNReal.ofReal ‖DeGiorgi.gradLpOfWitness hu‖ :=
      Finset.sum_le_sum fun j _ => hcoord j
    _ = ENNReal.ofReal (∑ _j : Fin d, ‖DeGiorgi.gradLpOfWitness hu‖) :=
      (ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _).symm
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem affine_energy_compactness
    {ι : Type*} [Fintype ι] (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {b : E → EuclideanSpace ℝ ι}
    (hb : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => b x i) Ω)
    {P : ℝ} (hP : 0 ≤ P)
    (hpoinc : ∀ (f : E → ℝ) (hf : DeGiorgi.MemW01p 2 f Ω),
      ‖hf.1.1.toLp f‖ ≤ P * ‖DeGiorgi.gradLpOfWitness (Classical.choose hf.2)‖)
    (u : ℕ → E → EuclideanSpace ℝ ι)
    (hu : ∀ i n, DeGiorgi.MemW01p 2 (fun x => u n x i - b x i) Ω)
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsClosed K)
    (huK : ∀ n, ∀ᵐ x ∂volume.restrict Ω, u n x ∈ K)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ∑ i, ‖DeGiorgi.gradLpOfWitness
      (affineWitness (hb i) (Classical.choose (hu i n).2))‖ ^ 2 ≤ C) :
    ∃ (φ : ℕ → ℕ) (v : E → EuclideanSpace ℝ ι)
      (hv : ∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - b x i) Ω),
      StrictMono φ ∧ (∀ᵐ x ∂volume.restrict Ω, v x ∈ K) ∧
      ∀ i (z : Y), Tendsto (fun n => inner ℝ
        (DeGiorgi.gradLpOfWitness (Classical.choose (hu i (φ n)).2)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (Classical.choose (hv i).2)) z)) := by
  classical
  let R (i : ι) := C + 1 + ‖DeGiorgi.gradLpOfWitness (hb i)‖
  have hgrad (i : ι) (n : ℕ) :
      ‖DeGiorgi.gradLpOfWitness (Classical.choose (hu i n).2)‖ ≤ R i := by
    have hsq : ‖DeGiorgi.gradLpOfWitness
        (affineWitness (hb i) (Classical.choose (hu i n).2))‖ ^ 2 ≤ C :=
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖DeGiorgi.gradLpOfWitness
        (affineWitness (hb j) (Classical.choose (hu j n).2))‖)
        (Finset.mem_univ i)).trans (hbound n)
    have hnorm : ‖DeGiorgi.gradLpOfWitness
        (affineWitness (hb i) (Classical.choose (hu i n).2))‖ ≤ C + 1 := by
      nlinarith [norm_nonneg (DeGiorgi.gradLpOfWitness
        (affineWitness (hb i) (Classical.choose (hu i n).2)))]
    have heq := gradLpOfWitness_eq_add_of_sub hΩ
      (affineWitness (hb i) (Classical.choose (hu i n).2)) (hb i)
      (Classical.choose (hu i n).2)
    have hsub : DeGiorgi.gradLpOfWitness (Classical.choose (hu i n).2) =
        DeGiorgi.gradLpOfWitness (affineWitness (hb i) (Classical.choose (hu i n).2)) -
          DeGiorgi.gradLpOfWitness (hb i) := by rw [heq, add_sub_cancel_right]
    rw [hsub]
    exact (norm_sub_le _ _).trans (add_le_add hnorm le_rfl)
  let S (i : ι) := P * R i + (d : ℝ) * R i
  have hR (i : ι) : 0 ≤ R i := by dsimp only [R]; positivity
  have hfun (i : ι) (n : ℕ) : eLpNorm (fun x => u n x i - b x i) 2
      (volume.restrict Ω) ≤ ENNReal.ofReal (S i) := by
    have hp := (hpoinc _ (hu i n)).trans (mul_le_mul_of_nonneg_left (hgrad i n) hP)
    rw [Lp.norm_toLp] at hp
    calc
      _ = ENNReal.ofReal (eLpNorm (fun x => u n x i - b x i) 2
          (volume.restrict Ω)).toReal :=
        (ENNReal.ofReal_toReal (hu i n).1.1.eLpNorm_lt_top.ne).symm
      _ ≤ ENNReal.ofReal (P * R i) := ENNReal.ofReal_le_ofReal hp
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (hR i)))
  have hsum (i : ι) (n : ℕ) : (∑ j : Fin d, eLpNorm
      (fun x => (Classical.choose (hu i n).2).weakGrad x j) 2 (volume.restrict Ω)) ≤
      ENNReal.ofReal (S i) :=
    (gradient_coordinate_sum_le _).trans (ENNReal.ofReal_le_ofReal
      ((mul_le_mul_of_nonneg_left (hgrad i n) (Nat.cast_nonneg _)).trans
        (le_add_of_nonneg_left (mul_nonneg hP (hR i)))))
  obtain ⟨φ, v, hφ, hvLp, hv, hlim, _, hvK⟩ :=
    Analysis.Sobolev.rellich_kondrachov_H01_sub_seq_euclidean_closed_image
      hΩ hΩb u b (MemLp.of_eval_piLp fun i => (hb i).memLp) hu S hfun hsum hK huK
  have hcoord (i : ι) : Tendsto (fun n => eLpNorm
      (fun x => (u (φ n) x i - b x i) - (v x i - b x i)) 2
      (volume.restrict Ω)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le)
    intro n
    apply eLpNorm_mono_ae
    filter_upwards with x
    have heq : (u (φ n) x i - b x i) - (v x i - b x i) = (u (φ n) x - v x) i := by
      simp only [PiLp.sub_apply]
      ring
    rw [heq]
    exact PiLp.norm_apply_le _ i
  obtain ⟨σ, hσ, hweak⟩ := exists_subseq_tendsto_inner_gradients hΩ
    (fun i n x => u (φ n) x i - b x i) (fun i x => v x i - b x i)
    (fun i n => hu i (φ n)) (fun i => Classical.choose (hv i).2) R
    (fun i n => hgrad i (φ n)) hcoord
  exact ⟨φ ∘ σ, v, hv, hφ.comp hσ, hvK, hweak⟩

theorem exists_dirichlet_energy_minimizer_of_poincare
    {ι : Type*} [Fintype ι] (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {b : E → EuclideanSpace ℝ ι}
    (hb : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => b x i) Ω)
    {P : ℝ} (hP : 0 ≤ P)
    (hpoinc : ∀ (f : E → ℝ) (hf : DeGiorgi.MemW01p 2 f Ω),
      ‖hf.1.1.toLp f‖ ≤ P * ‖DeGiorgi.gradLpOfWitness (Classical.choose hf.2)‖)
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsClosed K)
    (hne : ∃ u : E → EuclideanSpace ℝ ι,
      (∀ i, DeGiorgi.MemW01p 2 (fun x => u x i - b x i) Ω) ∧
      ∀ᵐ x ∂volume.restrict Ω, u x ∈ K) :
    ∃ (u : E → EuclideanSpace ℝ ι),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => u x i - b x i) Ω) ∧
      (∀ᵐ x ∂volume.restrict Ω, u x ∈ K) ∧
      ∃ hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω,
        ∀ (v : E → EuclideanSpace ℝ ι),
          (∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - b x i) Ω) →
          (∀ᵐ x ∂volume.restrict Ω, v x ∈ K) →
          ∀ hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω,
            (∑ i, ‖DeGiorgi.gradLpOfWitness (hu i)‖ ^ 2) ≤
              ∑ i, ‖DeGiorgi.gradLpOfWitness (hv i)‖ ^ 2 := by
  classical
  let A := {u : E → EuclideanSpace ℝ ι |
    (∀ i, DeGiorgi.MemW01p 2 (fun x => u x i - b x i) Ω) ∧
      ∀ᵐ x ∂volume.restrict Ω, u x ∈ K}
  let energy (u : A) : ℝ := ∑ i, ‖DeGiorgi.gradLpOfWitness
    (affineWitness (hb i) (Classical.choose (u.property.1 i).2))‖ ^ 2
  have hA : Nonempty A := by
    obtain ⟨u, hu, huK⟩ := hne
    exact ⟨u, hu, huK⟩
  have hEnonneg (u : A) : 0 ≤ energy u := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEne : (range energy).Nonempty := Set.range_nonempty energy
  have hEbelow : BddBelow (range energy) := ⟨0, by rintro _ ⟨u, rfl⟩; exact hEnonneg u⟩
  obtain ⟨e, heanti, helim, hemem⟩ := exists_seq_tendsto_sInf hEne hEbelow
  choose u hue using hemem
  let maps (n : ℕ) : E → EuclideanSpace ℝ ι := u n
  let hu (i : ι) (n : ℕ) := (u n).property.1 i
  have hbound (n : ℕ) : energy (u n) ≤ e 0 := by rw [hue]; exact heanti (Nat.zero_le n)
  have he0 : 0 ≤ e 0 := (hue 0) ▸ hEnonneg (u 0)
  obtain ⟨φ, v, hv, hφ, hvK, hweak⟩ := affine_energy_compactness hΩ hΩb hb hP hpoinc
    maps hu hK (fun n => (u n).property.2) he0 hbound
  let hvm (i : ι) := affineWitness (hb i) (Classical.choose (hv i).2)
  have hlsc := sum_norm_gradLpOfWitness_sq_le_liminf_of_weak_sub hΩ
    (fun i n => affineWitness (hb i) (Classical.choose (hu i (φ n)).2))
    hvm hb (fun i n => Classical.choose (hu i (φ n)).2)
    (fun i => Classical.choose (hv i).2) (fun n => hbound (φ n)) hweak
  have henergy : Tendsto (fun n => energy (u (φ n))) atTop (𝓝 (sInf (range energy))) := by
    have heq : (fun n => energy (u (φ n))) = (fun n => e (φ n)) := by
      funext n
      exact hue (φ n)
    rw [heq]
    exact helim.comp hφ.tendsto_atTop
  have hmin : (∑ i, ‖DeGiorgi.gradLpOfWitness (hvm i)‖ ^ 2) ≤ sInf (range energy) := by
    exact hlsc.trans_eq henergy.liminf_eq
  refine ⟨v, hv, hvK, hvm, ?_⟩
  intro w hw hwK hwm
  let wa : A := ⟨w, hw, hwK⟩
  have hwa : sInf (range energy) ≤ energy wa := csInf_le hEbelow (mem_range_self wa)
  have heq : energy wa = ∑ i, ‖DeGiorgi.gradLpOfWitness (hwm i)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [gradLpOfWitness_eq hΩ
      (affineWitness (hb i) (Classical.choose (wa.property.1 i).2)) (hwm i)]
  exact hmin.trans (hwa.trans_eq heq)

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_dirichlet_integral_minimizer_of_poincare
    {ι : Type*} [Fintype ι] (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {b : E → EuclideanSpace ℝ ι}
    (hb : ∀ i, DeGiorgi.MemW1p 2 (fun x => b x i) Ω)
    {P : ℝ} (hP : 0 ≤ P)
    (hpoinc : ∀ (f : E → ℝ) (hf : DeGiorgi.MemW01p 2 f Ω),
      ‖hf.1.1.toLp f‖ ≤ P * ‖DeGiorgi.gradLpOfWitness (Classical.choose hf.2)‖)
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsClosed K)
    (hne : ∃ u : E → EuclideanSpace ℝ ι,
      (∀ i, DeGiorgi.MemW01p 2 (fun x => u x i - b x i) Ω) ∧
      ∀ᵐ x ∂volume.restrict Ω, u x ∈ K) :
    ∃ (u : E → EuclideanSpace ℝ ι),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => u x i - b x i) Ω) ∧
      (∀ᵐ x ∂volume.restrict Ω, u x ∈ K) ∧
      ∃ hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω,
        ∀ (v : E → EuclideanSpace ℝ ι),
          (∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - b x i) Ω) →
          (∀ᵐ x ∂volume.restrict Ω, v x ∈ K) →
          ∀ hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω,
            (∑ i, ∫ x in Ω, ‖(hu i).weakGrad x‖ ^ 2) ≤
              ∑ i, ∫ x in Ω, ‖(hv i).weakGrad x‖ ^ 2 := by
  obtain ⟨u, hu0, huK, hu, hmin⟩ := exists_dirichlet_energy_minimizer_of_poincare
    hΩ hΩb (fun i => (hb i).someWitness) hP hpoinc hK hne
  refine ⟨u, hu0, huK, hu, ?_⟩
  intro v hv0 hvK hv
  simpa only [norm_gradLpOfWitness_sq_eq_integral] using hmin v hv0 hvK hv

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_dirichlet_integral_minimizer
    {ι : Type*} [Fintype ι] (hd : 2 ≤ d) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    {b : E → EuclideanSpace ℝ ι}
    (hb : ∀ i, DeGiorgi.MemW1p 2 (fun x => b x i) Ω)
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsClosed K)
    (hne : ∃ u : E → EuclideanSpace ℝ ι,
      (∀ i, DeGiorgi.MemW01p 2 (fun x => u x i - b x i) Ω) ∧
      ∀ᵐ x ∂volume.restrict Ω, u x ∈ K) :
    ∃ (u : E → EuclideanSpace ℝ ι),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => u x i - b x i) Ω) ∧
      (∀ᵐ x ∂volume.restrict Ω, u x ∈ K) ∧
      ∃ hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω,
        ∀ (v : E → EuclideanSpace ℝ ι),
          (∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - b x i) Ω) →
          (∀ᵐ x ∂volume.restrict Ω, v x ∈ K) →
          ∀ hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω,
            (∑ i, ∫ x in Ω, ‖(hu i).weakGrad x‖ ^ 2) ≤
              ∑ i, ∫ x in Ω, ‖(hv i).weakGrad x‖ ^ 2 := by
  let _ : NeZero d := ⟨by omega⟩
  obtain ⟨P, hP, hpc⟩ := exists_poincare_constant hd hΩ hΩb
  have hpc' : ∀ (f : E → ℝ) (hf : DeGiorgi.MemW01p 2 f Ω),
      ‖hf.1.1.toLp f‖ ≤ P * ‖DeGiorgi.gradLpOfWitness (Classical.choose hf.2)‖ := by
    intro f hf
    exact hpc hf (Classical.choose hf.2)
  exact exists_dirichlet_integral_minimizer_of_poincare hΩ hΩb
    (hb := hb) hP hpc' hK hne

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
