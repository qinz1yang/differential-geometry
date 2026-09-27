import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.DifferenceQuotient
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev

noncomputable section

open MeasureTheory Set
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_memLp_hasWeakPartialDeriv_weakGrad
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hf : MemLp f 2 ((volume : Measure E).restrict Omega))
    (hweak : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : rho ≠ 0)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta)
    (heta_range : Set.range eta ⊆ Set.Icc (0 : ℝ) 1)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hK_Omega : Metric.cthickening R₀ (tsupport eta) ⊆ Omega)
    (hcoeff : ∀ x ∈ Metric.cthickening R₀ (tsupport eta),
      ∀ i j : Fin d, A.a x i j = rho * B.a x i j)
    {V : Set E} (hV_open : IsOpen V)
    (heta_one : ∀ x ∈ V, eta x = 1)
    (i k : Fin d) :
    ∃ G : E → ℝ,
      MemLp G 2 ((volume : Measure E).restrict V) ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k G
        (fun x => hu.weakGrad x i) V := by
  obtain ⟨M, hM, hbound⟩ := exists_eLpNorm_diffQuot_weakGrad_le hOmega hu hf hweak B hrho
    heta heta_cpt heta_range hK_Omega hcoeff hV_open.measurableSet heta_one i k
  have hV_tsupp : closure V ⊆ tsupport eta := by
    apply closure_minimal _ (isClosed_tsupport eta)
    intro x hx
    apply subset_tsupport eta
    change eta x ≠ 0
    rw [heta_one x hx]
    exact one_ne_zero
  have hV_compact : IsCompact (closure V) :=
    heta_cpt.isCompact.of_isClosed_subset isClosed_closure hV_tsupp
  have hroom : Metric.cthickening R₀ (closure V) ⊆ Omega :=
    (Metric.cthickening_subset_of_subset R₀ hV_tsupp).trans hK_Omega
  obtain ⟨G, hG_l2, hG_weak, _hG_norm⟩ :=
    hasWeakPartialDeriv_of_diffQuot_uniform_bound_local
      (d := d) hOmega hV_open hV_compact hR₀ hroom
      (hu.weakGrad_component_memLp i) k hM
      (fun h _ hle => hbound h hle)
  exact ⟨G, hG_l2, hG_weak⟩

theorem memWkp_two_of_bilinFormOfCoeff_eq_integral_of_cutoff
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : DeGiorgi.EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Omega)
    (hf : MemLp f 2 ((volume : Measure E).restrict Omega))
    (hweak : ∀ v, DeGiorgi.MemH01 v Omega →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Omega,
        DeGiorgi.bilinFormOfCoeff A hu hv =
          ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : rho ≠ 0)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta)
    (heta_range : Set.range eta ⊆ Set.Icc (0 : ℝ) 1)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hK_Omega : Metric.cthickening R₀ (tsupport eta) ⊆ Omega)
    (hcoeff : ∀ x ∈ Metric.cthickening R₀ (tsupport eta),
      ∀ i j : Fin d, A.a x i j = rho * B.a x i j)
    {V : Set E} (hV_open : IsOpen V)
    (heta_one : ∀ x ∈ V, eta x = 1) :
    MemWkp (d := d) 2 2 u V := by
  have hV_tsupp : closure V ⊆ tsupport eta := by
    apply closure_minimal _ (isClosed_tsupport eta)
    intro x hx
    apply subset_tsupport eta
    change eta x ≠ 0
    rw [heta_one x hx]
    exact one_ne_zero
  have htsupp_K : tsupport eta ⊆ Metric.cthickening R₀ (tsupport eta) :=
    Metric.self_subset_cthickening (tsupport eta)
  have hV_Omega : V ⊆ Omega :=
    ((subset_closure.trans hV_tsupp).trans htsupp_K).trans hK_Omega
  let huV : DeGiorgi.MemW1pWitness 2 u V := hu.restrict hV_open hV_Omega
  apply MemWkp.of_weakGrad_memWkp (k := 1) (by norm_num) hV_open huV
  intro i
  apply MemWkp.one_iff_memW1p.mpr
  refine ⟨huV.weakGrad_component_memLp i, ?_⟩
  intro k
  obtain ⟨G, hG_l2, hG_weak⟩ :=
    exists_memLp_hasWeakPartialDeriv_weakGrad (d := d) hOmega hu hf hweak B hrho heta heta_cpt heta_range
      hR₀ hK_Omega hcoeff hV_open heta_one i k
  refine ⟨G, hG_l2, ?_⟩
  simpa only [huV, DeGiorgi.MemW1pWitness.restrict] using hG_weak

theorem memWkp_two_of_bilinFormOfCoeff_eq_integral
    {Omega V : Set E} (hOmega : IsOpen Omega)
    (hV : IsOpen V) (hV_cpt : IsCompact (closure V))
    (hV_sub : closure V ⊆ Omega)
    {A : EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : MemW1pWitness 2 u Omega)
    (hf : MemLp f 2 ((volume : Measure E).restrict Omega))
    (hweak : ∀ v, MemH01 v Omega → ∀ hv : MemW1pWitness 2 v Omega,
      bilinFormOfCoeff A hu hv = ∫ x in Omega, f x * v x ∂(volume : Measure E))
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : rho ≠ 0)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d, A.a x i j = rho * B.a x i j) :
    MemWkp 2 2 u V := by
  obtain ⟨eta, heta, heta_cpt, heta_one, heta_sub, heta_range⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hV_cpt hOmega hV_sub
  obtain ⟨R₀, hR₀, hroom⟩ :=
    heta_cpt.isCompact.exists_cthickening_subset_open hOmega heta_sub
  exact memWkp_two_of_bilinFormOfCoeff_eq_integral_of_cutoff hOmega hu hf hweak
    B hrho heta heta_cpt heta_range hR₀ hroom (fun x hx => hcoeff x (hroom hx))
    hV (fun x hx => heta_one.self_of_nhdsSet (subset_closure hx))

theorem IsSolution.memWkp_two_of_cutoff
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : EllipticCoeff d Omega} {u : E → ℝ} (hsol : IsSolution A u)
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : rho ≠ 0)
    {eta : E → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_cpt : HasCompactSupport eta)
    (heta_range : Set.range eta ⊆ Set.Icc (0 : ℝ) 1)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hK_Omega : Metric.cthickening R₀ (tsupport eta) ⊆ Omega)
    (hcoeff : ∀ x ∈ Metric.cthickening R₀ (tsupport eta),
      ∀ i j : Fin d, A.a x i j = rho * B.a x i j)
    {V : Set E} (hV : IsOpen V) (heta_one : ∀ x ∈ V, eta x = 1) :
    MemWkp 2 2 u V := by
  let hu := MemW1p.someWitness hsol.1.1
  apply memWkp_two_of_bilinFormOfCoeff_eq_integral_of_cutoff (f := fun _ => 0)
    hOmega hu (by simp) (fun v hv0 hv => ?_) B hrho heta heta_cpt heta_range
    hR₀ hK_Omega hcoeff hV heta_one
  simpa using hsol.bilinFormOfCoeff_eq_zero hOmega hu hv0 hv

theorem IsSolution.memWkp_two
    {Omega V : Set E} (hOmega : IsOpen Omega)
    (hV : IsOpen V) (hV_cpt : IsCompact (closure V))
    (hV_sub : closure V ⊆ Omega)
    {A : EllipticCoeff d Omega} {u : E → ℝ} (hsol : IsSolution A u)
    (B : SmoothEllipticBilinearForm d Set.univ)
    {rho : ℝ} (hrho : rho ≠ 0)
    (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d, A.a x i j = rho * B.a x i j) :
    MemWkp 2 2 u V := by
  let hu := MemW1p.someWitness hsol.1.1
  apply memWkp_two_of_bilinFormOfCoeff_eq_integral (f := fun _ => 0)
    hOmega hV hV_cpt hV_sub hu (by simp) (fun v hv0 hv => ?_) B hrho hcoeff
  simpa using hsol.bilinFormOfCoeff_eq_zero hOmega hu hv0 hv

end DeGiorgi
