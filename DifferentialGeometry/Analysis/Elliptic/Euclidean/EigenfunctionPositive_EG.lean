import DifferentialGeometry.Analysis.Elliptic.Euclidean.RayleighMinimizer_EG
import DifferentialGeometry.Analysis.Elliptic.Euclidean.RayleighEL_EG
import DifferentialGeometry.Analysis.Elliptic.Euclidean.RayleighAbs_EG
import DifferentialGeometry.Analysis.Elliptic.Euclidean.EigenRegularity_EG
import DifferentialGeometry.Analysis.Elliptic.Euclidean.EigenStrongMin_EG
import DifferentialGeometry.Analysis.Elliptic.Euclidean.RayleighStab_EG

/-!
# Positive first Dirichlet eigenfunction of `-Δ + W` on a planar domain (S-W-EIG, G2)

Assembly: a Rayleigh minimizer `u ∈ H¹₀(Ω)` (G1), replaced by `|u|` (same energy and mass),
satisfies the weak Euler–Lagrange equation, hence is `C^∞` on `Ω` (iterated `Hᵏ` regularity), solves
`-Δũ + W ũ = μ ρ ũ` pointwise, is `≥ 0`, and is `> 0` on the connected set `Ω` by the strong minimum
principle (`eq_zero_of_nonneg_EG`).  The eigenvalue `μ` is `≥ 0` by stability on `C_c^∞(Ω)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace InnerProductSpace ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem exists_positive_first_eigenfunction_core_EG
    {Ω U : Set E2} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩc : IsPreconnected Ω)
    (hne : Ω.Nonempty) (hU : IsOpen U) (hΩU : closure Ω ⊆ U) {ρ W : E2 → ℝ}
    (hρm : Measurable ρ) (hWm : Measurable W)
    (hρs : ContDiffOn ℝ (⊤ : ℕ∞) ρ U) (hWs : ContDiffOn ℝ (⊤ : ℕ∞) W U)
    (hρpos : ∀ x ∈ closure Ω, 0 < ρ x)
    (hstab : ∀ φ : E2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      0 ≤ (∫ x in Ω, ∑ i : Fin 2, (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2) +
        ∫ x in Ω, W x * φ x ^ 2) :
    ∃ (u : E2 → ℝ) (μ : ℝ), DeGiorgi.MemW01p 2 u Ω ∧ ContDiffOn ℝ (⊤ : ℕ∞) u Ω ∧
      (∀ x ∈ Ω, 0 < u x) ∧ 0 ≤ μ ∧ (∫ x in Ω, ρ x * u x ^ 2) = 1 ∧
      (∀ x ∈ Ω, -Laplacian.laplacian u x + W x * u x = μ * ρ x * u x) ∧
      ∀ v : E2 → ℝ, DeGiorgi.MemW01p 2 v Ω → ∀ hv : DeGiorgi.MemW1pWitness 2 v Ω,
        μ * (∫ x in Ω, ρ x * v x ^ 2) ≤
          (∫ x in Ω, ‖hv.weakGrad x‖ ^ 2) + ∫ x in Ω, W x * v x ^ 2 := by
  classical
  have hcpt : IsCompact (closure Ω) := hΩb.isCompact_closure
  have hρc : ContinuousOn ρ (closure Ω) := hρs.continuousOn.mono hΩU
  have hWc : ContinuousOn W (closure Ω) := hWs.continuousOn.mono hΩU
  obtain ⟨B₁, hB₁⟩ := hcpt.exists_bound_of_continuousOn hρc
  obtain ⟨B₂, hB₂⟩ := hcpt.exists_bound_of_continuousOn hWc
  obtain ⟨x₁, hx₁, hx₁min⟩ := hcpt.exists_isMinOn (hne.mono subset_closure) hρc
  have hc₀ : 0 < ρ x₁ := hρpos x₁ hx₁
  set B : ℝ := max B₁ B₂ with hB
  have hρ0 : ∀ x ∈ Ω, ρ x₁ ≤ ρ x := fun x hx => hx₁min (subset_closure hx)
  have hρB : ∀ x ∈ Ω, ρ x ≤ B := fun x hx => by
    have h := hB₁ x (subset_closure hx)
    rw [Real.norm_eq_abs] at h
    exact ((le_abs_self (ρ x)).trans h).trans (le_max_left _ _)
  have hWB : ∀ x ∈ Ω, |W x| ≤ B := fun x hx => by
    have h := hB₂ x (subset_closure hx)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_right _ _)
  have hB0 : 0 ≤ B := by
    obtain ⟨x, hx⟩ := hne
    exact (abs_nonneg _).trans (hWB x hx)
  have hρabs : ∀ x ∈ Ω, |ρ x| ≤ B := fun x hx => by
    rw [abs_of_nonneg (hc₀.le.trans (hρ0 x hx))]
    exact hρB x hx
  obtain ⟨u, hu0, hu, hN, hmin⟩ := exists_rayleigh_minimizer_EG hΩ hΩb hne hρm hWm hc₀ hρ0 hρB hWB
  set μ : ℝ := (∫ x in Ω, ‖hu.weakGrad x‖ ^ 2) + ∫ x in Ω, W x * u x ^ 2 with hμ
  have hμ0 : 0 ≤ μ := nonneg_h01_of_smooth_stab_EG hΩ hWm hB0 hWB hstab hu0 hu
  obtain ⟨hab0, hab, habE⟩ := DeGiorgi.exists_abs_h01_EG hΩ hΩb hu0 hu
  have hNab : (∫ x in Ω, ρ x * |u x| ^ 2) = 1 := by simpa only [sq_abs] using hN
  have hQab : (∫ x in Ω, ‖hab.weakGrad x‖ ^ 2) + ∫ x in Ω, W x * |u x| ^ 2 = μ := by
    simp only [sq_abs, habE, hμ]
  have hweak : ∀ φ : E2 → ℝ, DeGiorgi.MemW01p 2 φ Ω → ∀ hφ : DeGiorgi.MemW1pWitness 2 φ Ω,
      (∫ x in Ω, ⟪hab.weakGrad x, hφ.weakGrad x⟫_ℝ) =
        ∫ x in Ω, ((μ * ρ x - W x) * |u x|) * φ x := fun φ hφ0 hφ =>
    weak_euler_lagrange_EG hΩ hρm hWm hρabs hWB hab0 hab hNab hQab hmin hφ0 hφ
  -- regularity
  set ψ : E2 → ℝ := fun x => μ * ρ x - W x with hψdef
  have hψs : ContDiffOn ℝ (⊤ : ℕ∞) ψ U := (contDiffOn_const.mul hρs).sub hWs
  have hψm : Measurable ψ := (hρm.const_mul μ).sub hWm
  have hall := DeGiorgi.memWkp_all_EG hΩ hU hΩU hψs hab hweak
  obtain ⟨ũ, hũ, huũ⟩ := DeGiorgi.exists_contDiffOn_rep_EG hΩ hall
  have hψB : ∀ x ∈ Ω, |ψ x| ≤ |μ| * B + B := fun x hx => by
    have h1 : |μ * ρ x| ≤ |μ| * B := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hρabs x hx) (abs_nonneg _)
    have h2 := hWB x hx
    calc |ψ x| = |μ * ρ x - W x| := rfl
      _ ≤ |μ * ρ x| + |W x| := abs_sub _ _
      _ ≤ |μ| * B + B := add_le_add h1 h2
  have hΔ := DeGiorgi.classical_equation_EG hΩ hψm
    (hψs.continuousOn.mono (subset_closure.trans hΩU)) hψB hab hũ huũ.symm hweak
  -- nonnegativity of the smooth representative
  have hae : ũ =ᵐ[volume.restrict Ω] fun x => |ũ x| := by
    filter_upwards [huũ] with x hx
    rw [← hx, abs_abs]
  have hũnn : ∀ x ∈ Ω, 0 ≤ ũ x := fun x hx => by
    have h := Measure.eqOn_open_of_ae_eq hae hΩ hũ.continuousOn
      (hũ.continuousOn.abs) hx
    rw [h]
    exact abs_nonneg _
  have hNũ : (∫ x in Ω, ρ x * ũ x ^ 2) = 1 := by
    rw [← hNab]
    apply integral_congr_ae
    filter_upwards [huũ] with x hx
    rw [← hx]
  -- strong minimum principle
  have hũ2 : ContDiffOn ℝ 2 ũ Ω := hũ.of_le (by norm_cast)
  have hpos : ∀ x ∈ Ω, 0 < ũ x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp, hp0⟩ := hcon
    have hz : ũ p = 0 := le_antisymm hp0 (hũnn p hp)
    have hall0 := eq_zero_of_nonneg_EG hΩ hΩc hũ2 hũnn (c := fun x => W x - μ * ρ x)
      (M := B + |μ| * B) (fun x hx => by
        have h1 : -(μ * ρ x) ≤ |μ| * B := by
          have := hψB x hx
          calc -(μ * ρ x) ≤ |μ * ρ x| := neg_le_abs _
            _ = |μ| * |ρ x| := abs_mul _ _
            _ ≤ |μ| * B := mul_le_mul_of_nonneg_left (hρabs x hx) (abs_nonneg _)
        have h2 := (le_abs_self (W x)).trans (hWB x hx)
        linarith)
      (fun x hx => by rw [hΔ x hx]; simp only [hψdef]; ring) hp hz
    have h1 : (∫ x in Ω, ρ x * ũ x ^ 2) = 0 := by
      rw [setIntegral_congr_fun hΩ.measurableSet (g := fun _ => (0 : ℝ))
        (fun x hx => by simp [hall0 x hx])]
      simp
    rw [h1] at hNũ
    exact zero_ne_one hNũ
  refine ⟨ũ, μ, hab0.congr huũ, hũ, hpos, hμ0, hNũ, ?_, hmin⟩
  intro x hx
  rw [hΔ x hx]
  simp only [hψdef]
  ring

/-- **Positive first Dirichlet eigenfunction** of `-Δ + W` with weight `ρ` on a connected bounded
open `Ω ⊂ ℝ²` (`ρ, W` smooth near `closure Ω`, `ρ > 0` there, `∫|∇φ|² + Wφ² ≥ 0` on test
functions): there is a smooth positive `u ∈ H¹₀(Ω)` with `-Δu + W u = μ ρ u`, `μ ≥ 0` the minimum of
the Rayleigh quotient, `∫ ρ u² = 1`. -/
theorem exists_positive_first_eigenfunction_EG
    {Ω U : Set E2} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩc : IsPreconnected Ω)
    (hne : Ω.Nonempty) (hU : IsOpen U) (hΩU : closure Ω ⊆ U) {ρ W : E2 → ℝ}
    (hρs : ContDiffOn ℝ (⊤ : ℕ∞) ρ U) (hWs : ContDiffOn ℝ (⊤ : ℕ∞) W U)
    (hρpos : ∀ x ∈ closure Ω, 0 < ρ x)
    (hstab : ∀ φ : E2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      0 ≤ (∫ x in Ω, ∑ i : Fin 2, (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2) +
        ∫ x in Ω, W x * φ x ^ 2) :
    ∃ (u : E2 → ℝ) (μ : ℝ), DeGiorgi.MemW01p 2 u Ω ∧ ContDiffOn ℝ (⊤ : ℕ∞) u Ω ∧
      (∀ x ∈ Ω, 0 < u x) ∧ 0 ≤ μ ∧ (∫ x in Ω, ρ x * u x ^ 2) = 1 ∧
      (∀ x ∈ Ω, -Laplacian.laplacian u x + W x * u x = μ * ρ x * u x) ∧
      ∀ v : E2 → ℝ, DeGiorgi.MemW01p 2 v Ω → ∀ hv : DeGiorgi.MemW1pWitness 2 v Ω,
        μ * (∫ x in Ω, ρ x * v x ^ 2) ≤
          (∫ x in Ω, ‖hv.weakGrad x‖ ^ 2) + ∫ x in Ω, W x * v x ^ 2 := by
  classical
  have hΩU' : Ω ⊆ U := subset_closure.trans hΩU
  let ρ' : E2 → ℝ := U.piecewise ρ (fun _ => 0)
  let W' : E2 → ℝ := U.piecewise W (fun _ => 0)
  have hρ'm : Measurable ρ' :=
    hρs.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hW'm : Measurable W' :=
    hWs.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hρ'e : ∀ x ∈ U, ρ' x = ρ x := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have hW'e : ∀ x ∈ U, W' x = W x := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have hρ's : ContDiffOn ℝ (⊤ : ℕ∞) ρ' U := hρs.congr hρ'e
  have hW's : ContDiffOn ℝ (⊤ : ℕ∞) W' U := hWs.congr hW'e
  have hint : ∀ f : E2 → ℝ, (∫ x in Ω, W' x * f x) = ∫ x in Ω, W x * f x := fun f =>
    setIntegral_congr_fun hΩ.measurableSet (fun x hx => by rw [hW'e x (hΩU' hx)])
  have hinr : ∀ f : E2 → ℝ, (∫ x in Ω, ρ' x * f x) = ∫ x in Ω, ρ x * f x := fun f =>
    setIntegral_congr_fun hΩ.measurableSet (fun x hx => by rw [hρ'e x (hΩU' hx)])
  obtain ⟨u, μ, hu0, hu, hpos, hμ, hN, hEq, hmin⟩ :=
    exists_positive_first_eigenfunction_core_EG hΩ hΩb hΩc hne hU hΩU hρ'm hW'm hρ's hW's
      (fun x hx => by rw [hρ'e x (hΩU hx)]; exact hρpos x hx)
      (fun φ h1 h2 h3 => by
        have := hstab φ h1 h2 h3
        rwa [← hint] at this)
  refine ⟨u, μ, hu0, hu, hpos, hμ, by rw [← hinr]; exact hN, fun x hx => ?_, fun v hv0 hv => ?_⟩
  · have := hEq x hx
    rwa [hW'e x (hΩU' hx), hρ'e x (hΩU' hx)] at this
  · have := hmin v hv0 hv
    rwa [hinr, hint] at this

end DifferentialGeometry.Analysis.Sobolev.Euclidean
