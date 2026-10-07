import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryZoom
import DifferentialGeometry.Geometry.Metric.Isometry.OrbitCompactness
import DifferentialGeometry.Topology.GroupAction.CompactLifting

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

local notation "H3" => Hyperboloid (EuclideanSpace ℝ (Fin 3))

private theorem exists_isometry_subsequence_of_compact_values
    {G : Type*} [Group G] (ρ σ : G →* (H3 ≃ᵢ H3)) (f : C(H3, H3))
    (hequiv : ∀ (γ : G) (x : H3), f (ρ γ x) = σ γ (f x))
    (a b : ℕ → H3 ≃ᵢ H3) (γ : ℕ → G) {D K : Set H3}
    (hD : IsCompact D) (hK : IsCompact K)
    (hb : ∀ n, ρ (γ n) (b n origin) ∈ D)
    (ha : ∀ n, a n (f (b n origin)) ∈ K) :
    ∃ (k : ℕ → ℕ) (A B : H3 ≃ᵢ H3), StrictMono k ∧
      Filter.Tendsto (fun n => (a (k n) * (σ (γ (k n))).symm : C(H3, H3)))
        Filter.atTop (𝓝 (A : C(H3, H3))) ∧
      Filter.Tendsto (fun n => (ρ (γ (k n)) * b (k n) : C(H3, H3)))
        Filter.atTop (𝓝 (B : C(H3, H3))) ∧
      Filter.Tendsto (fun n => (a (k n) : C(H3, H3)).comp (f.comp (b (k n) : C(H3, H3))))
        Filter.atTop (𝓝 ((A : C(H3, H3)).comp (f.comp (B : C(H3, H3))))) := by
  let actρ : MulAction G H3 := MulAction.compHom H3 ρ
  let isoρ : @IsIsometricSMul G H3 inferInstance actρ.toSMul := ⟨fun γ => (ρ γ).isometry⟩
  let actσ : MulAction G H3 := MulAction.compHom H3 σ
  let isoσ : @IsIsometricSMul G H3 inferInstance actσ.toSMul := ⟨fun γ => (σ γ).isometry⟩
  have hρ (c : G) : @IsometryEquiv.constSMul G H3 inferInstance inferInstance actρ isoρ c = ρ c :=
    IsometryEquiv.ext fun _ => rfl
  have hσ (c : G) : @IsometryEquiv.constSMul G H3 inferInstance inferInstance actσ isoσ c = σ c :=
    IsometryEquiv.ext fun _ => rfl
  obtain ⟨k, A, B, hk, hA, hB, hlim⟩ :=
    @ContinuousMap.exists_isometry_orbit_subsequence G H3 H3 inferInstance
      inferInstance inferInstance inferInstance inferInstance actρ isoρ actσ isoσ
      f hequiv origin a b γ D K hD hK hb ha
  refine ⟨k, A, B, hk, ?_, ?_, hlim⟩
  · simpa only [hσ] using hA
  · simpa only [hρ] using hB

variable {G : Type*} [Group G] (ρ σ : G →* (H3 ≃ᵢ H3))
  (f g : C(H3, H3))
  (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
    L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
  (hg : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
    L⁻¹ * dist x y - C ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ L * dist x y + C)
  (hgf : ∃ C : ℝ, ∀ x : H3, dist (g (f x)) x ≤ C)
  (hfg : ∃ C : ℝ, ∀ x : H3, dist (f (g x)) x ≤ C)
  (hnorth : boundaryMap f hf sphereNorthPole = sphereNorthPole)
  (hequiv : ∀ (γ : G) (x : H3), f (ρ γ x) = σ γ (f x))

include hequiv in
theorem exists_homothety_isometry_subsequence_of_compact_quotient_returns
    (z : ℂ)
    (hne : lineDeriv ℝ (boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth) z (1 : ℂ) ≠ 0)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hstop : Filter.Tendsto s Filter.atTop Filter.atTop) :
    let h := boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth
    let a (n : ℕ) : H3 ≃ᵢ H3 :=
      ((boundaryTranslation (-(h z))).trans
        (boundarySimilarity (s n : ℂ) (Complex.ofReal_ne_zero.mpr (hs n).ne'))).trans
        (boundaryTranslation (h z))
    let b (n : ℕ) : H3 ≃ᵢ H3 :=
      ((boundaryTranslation (-z)).trans
        (boundarySimilarity (((s n)⁻¹ : ℝ) : ℂ)
          (Complex.ofReal_ne_zero.mpr (inv_ne_zero (hs n).ne')))).trans (boundaryTranslation z)
    letI : MulAction G H3 := MulAction.compHom H3 ρ
    ∀ (K : Set (MulAction.orbitRel.Quotient G H3)), IsCompact K →
      (∀ n, Quotient.mk (MulAction.orbitRel G H3) (b n origin) ∈ K) →
      ∃ (γ : ℕ → G) (k : ℕ → ℕ) (A B : H3 ≃ᵢ H3), StrictMono k ∧
        Filter.Tendsto (fun n => (a (k n) * (σ (γ (k n))).symm : C(H3, H3)))
          Filter.atTop (𝓝 (A : C(H3, H3))) ∧
        Filter.Tendsto (fun n => (ρ (γ (k n)) * b (k n) : C(H3, H3)))
          Filter.atTop (𝓝 (B : C(H3, H3))) ∧
        Filter.Tendsto (fun n => (a (k n) : C(H3, H3)).comp (f.comp (b (k n) : C(H3, H3))))
          Filter.atTop (𝓝 ((A : C(H3, H3)).comp (f.comp (B : C(H3, H3))))) := by
  classical
  intro h a b K hK hreturns
  let : MulAction G H3 := MulAction.compHom H3 ρ
  let : IsIsometricSMul G H3 := ⟨fun γ => (ρ γ).isometry⟩
  obtain ⟨D, hD, hrepresent⟩ := MulAction.exists_compact_representatives hK
  choose γ hγ using fun n => hrepresent (b n origin) (hreturns n)
  obtain ⟨R, s₀, _, hs₀, hbound⟩ :=
    exists_eventually_origin_bound_homothety_conjugate f g hf hg hgf hfg hnorth z hne
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hstop.eventually (Filter.eventually_ge_atTop s₀))
  have htarget (n : ℕ) : a (n + N) (f (b (n + N) origin)) ∈ Metric.closedBall (origin : H3) R := by
    rw [Metric.mem_closedBall, dist_comm]
    exact hbound (s (n + N)) (hN (n + N) (Nat.le_add_left _ _))
  obtain ⟨k, A, B, hk, hA, hB, hlim⟩ := exists_isometry_subsequence_of_compact_values
    ρ σ f hequiv (fun n => a (n + N)) (fun n => b (n + N)) (fun n => γ (n + N))
    hD (isCompact_closedBall (origin : H3) R) (fun n => hγ (n + N)) htarget
  refine ⟨γ, fun n => k n + N, A, B, ?_, hA, hB, hlim⟩
  intro n m hnm
  exact Nat.add_lt_add_right (hk hnm) N

end DifferentialGeometry.Hyperboloid
