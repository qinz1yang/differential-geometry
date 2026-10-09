import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryZoomCompactness
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryReturning
import DifferentialGeometry.Geometry.Coordinates.StereographicConvergence

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "H3" => Hyperboloid E3
local notation "S2" => Metric.sphere (0 : E3) 1

private theorem tendsto_boundary_of_corrected_isometries
    {G : Type*} [Group G] (ρ σ : G →* (H3 ≃ᵢ H3)) (f : C(H3, H3))
    (hf : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ x y : H3,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hequiv : ∀ (γ : G) (x : H3), f (ρ γ x) = σ γ (f x))
    (a b : ℕ → H3 ≃ᵢ H3) (γ : ℕ → G) (k : ℕ → ℕ) (A B : H3 ≃ᵢ H3)
    (hA : Filter.Tendsto (fun n => (a (k n) * (σ (γ (k n))).symm : C(H3, H3)))
      Filter.atTop (𝓝 (A : C(H3, H3))))
    (hB : Filter.Tendsto (fun n => (ρ (γ (k n)) * b (k n) : C(H3, H3)))
      Filter.atTop (𝓝 (B : C(H3, H3)))) :
    Filter.Tendsto (fun n => (boundaryHomeomorph (a (k n)) : C(S2, S2)).comp
      ((boundaryMap f hf).comp (boundaryHomeomorph (b (k n)) : C(S2, S2))))
      Filter.atTop (𝓝 ((boundaryHomeomorph A : C(S2, S2)).comp
        ((boundaryMap f hf).comp (boundaryHomeomorph B : C(S2, S2))))) := by
  let actρ : MulAction G H3 := MulAction.compHom H3 ρ
  let isoρ : @IsIsometricSMul G H3 inferInstance actρ.toSMul := ⟨fun γ => (ρ γ).isometry⟩
  let actσ : MulAction G H3 := MulAction.compHom H3 σ
  let isoσ : @IsIsometricSMul G H3 inferInstance actσ.toSMul := ⟨fun γ => (σ γ).isometry⟩
  have hρ (c : G) : @IsometryEquiv.constSMul G H3 inferInstance inferInstance actρ isoρ c = ρ c :=
    IsometryEquiv.ext fun _ => rfl
  have hσ (c : G) : @IsometryEquiv.constSMul G H3 inferInstance inferInstance actσ isoσ c = σ c :=
    IsometryEquiv.ext fun _ => rfl
  exact @tendsto_boundaryMap_isometry_orbit_conjugate E3 E3
    inferInstance inferInstance inferInstance inferInstance inferInstance G inferInstance
    actρ isoρ actσ isoσ f hf hequiv a b γ k A B
    (by simpa only [hσ] using hA) (by simpa only [hρ] using hB)

private theorem nonpole_iff (Q : S2 ≃ₜ S2) (hQ : Q sphereNorthPole = sphereNorthPole)
    (ξ : S2) : ξ ≠ sphereNorthPole ↔ Q ξ ≠ sphereNorthPole := by
  constructor
  · intro hξ heq
    exact hξ (Q.injective (heq.trans hQ.symm))
  · intro hξ heq
    exact hξ (heq ▸ hQ)

private theorem boundary_homothety_chart (c : ℂ) (r : ℝ) (hr : 0 < r) (w : ℂ) :
    boundaryHomeomorph
      (((boundaryTranslation (-c)).trans
        (boundarySimilarity (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne'))).trans
        (boundaryTranslation c)) (stereographicComplex.symm w).val =
      (stereographicComplex.symm (c + r • (w - c))).val := by
  simp only [boundaryHomeomorph_trans, Homeomorph.trans_apply,
    boundaryHomeomorph_boundaryTranslation_stereographicComplex_symm,
    boundaryHomeomorph_boundarySimilarity_stereographicComplex_symm]
  apply congrArg (fun u : ℂ => (stereographicComplex.symm u).val)
  rw [Complex.real_smul, sub_eq_add_neg]
  exact add_comm _ _

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
theorem exists_homothety_plane_homeomorph_limit_of_compact_quotient_returns
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
    let Z (n : ℕ) : C(ℂ, ℂ) :=
      ⟨fun w => h z + s n • (h (z + (s n)⁻¹ • (w - z)) - h z), by fun_prop⟩
    letI : MulAction G H3 := MulAction.compHom H3 ρ
    ∀ (K : Set (MulAction.orbitRel.Quotient G H3)), IsCompact K →
      (∀ n, Quotient.mk (MulAction.orbitRel G H3) (b n origin) ∈ K) →
      ∃ (k : ℕ → ℕ) (A B : H3 ≃ᵢ H3) (H : ℂ ≃ₜ ℂ), StrictMono k ∧
        Filter.Tendsto (fun n => (a (k n) : C(H3, H3)).comp (f.comp (b (k n) : C(H3, H3))))
          Filter.atTop (𝓝 ((A : C(H3, H3)).comp (f.comp (B : C(H3, H3))))) ∧
        boundaryHomeomorph A (boundaryMap f hf (boundaryHomeomorph B sphereNorthPole)) = sphereNorthPole ∧
        (∀ w : ℂ, (stereographicComplex.symm (H w)).val =
          boundaryHomeomorph A (boundaryMap f hf (boundaryHomeomorph B (stereographicComplex.symm w).val))) ∧
        Filter.Tendsto (fun n => Z (k n)) Filter.atTop (𝓝 (H : C(ℂ, ℂ))) := by
  intro h a b Z K hK hreturns
  obtain ⟨γ, k, A, B, hk, hA, hB, hI⟩ :=
    exists_homothety_isometry_subsequence_of_compact_quotient_returns
      ρ σ f g hf hg hgf hfg hnorth hequiv z hne s hs hstop K hK hreturns
  let Q₀ := boundaryHomeomorphOfCoarseInverse f g hf hg hgf hfg
  let Qn (n : ℕ) := (boundaryHomeomorph (b (k n))).trans
    (Q₀.trans (boundaryHomeomorph (a (k n))))
  let Q := (boundaryHomeomorph B).trans (Q₀.trans (boundaryHomeomorph A))
  have hQn : Filter.Tendsto (fun n => (Qn n : C(S2, S2))) Filter.atTop (𝓝 (Q : C(S2, S2))) :=
    tendsto_boundary_of_corrected_isometries ρ σ f hf hequiv a b γ k A B hA hB
  have hQnorth (n : ℕ) : Qn n sphereNorthPole = sphereNorthPole := by
    change boundaryHomeomorph (a (k n))
      (boundaryMap f hf (boundaryHomeomorph (b (k n)) sphereNorthPole)) = sphereNorthPole
    simp only [a, b, boundaryHomeomorph_trans, Homeomorph.trans_apply,
      boundaryHomeomorph_boundaryTranslation_northPole, boundaryHomeomorph_boundarySimilarity_northPole,
      hnorth]
  have hchart (w : ℂ) : (stereographicComplex.symm (h w)).val =
      boundaryMap f hf (stereographicComplex.symm w).val :=
    stereographicComplex_symm_boundaryPlaneHomeomorph f g hf hg hgf hfg hnorth w
  have hQchart (n : ℕ) (w : ℂ) : Qn n (stereographicComplex.symm w).val =
      (stereographicComplex.symm (Z (k n) w)).val := by
    change boundaryHomeomorph (a (k n))
      (boundaryMap f hf (boundaryHomeomorph (b (k n)) (stereographicComplex.symm w).val)) = _
    rw [boundary_homothety_chart z (s (k n))⁻¹ (inv_pos.mpr (hs (k n))) w, ← hchart,
      boundary_homothety_chart (h z) (s (k n)) (hs (k n))]
    rfl
  obtain ⟨hQpole, hplane⟩ :=
    tendsto_stereographicComplex_conjugate_of_fixed_northPole Qn Q hQnorth hQn
  let H := stereographicComplex.symm.trans
    ((Q.subtype (nonpole_iff Q hQpole)).trans stereographicComplex)
  have hHchart (w : ℂ) : (stereographicComplex.symm (H w)).val =
      Q (stereographicComplex.symm w).val :=
    congrArg Subtype.val (stereographicComplex.symm_apply_apply
      (Q.subtype (nonpole_iff Q hQpole) (stereographicComplex.symm w)))
  have hnplane (n : ℕ) :
      (stereographicComplex.symm.trans
        (((Qn n).subtype (nonpole_iff (Qn n) (hQnorth n))).trans stereographicComplex) : C(ℂ, ℂ)) = Z (k n) := by
    apply ContinuousMap.ext
    intro w
    apply stereographicComplex.symm.injective
    apply Subtype.ext
    exact (congrArg Subtype.val (stereographicComplex.symm_apply_apply
      ((Qn n).subtype (nonpole_iff (Qn n) (hQnorth n)) (stereographicComplex.symm w)))).trans
      (hQchart n w)
  refine ⟨k, A, B, H, hk, hI, hQpole, hHchart, ?_⟩
  change Filter.Tendsto (fun n => (stereographicComplex.symm.trans
    (((Qn n).subtype (nonpole_iff (Qn n) (hQnorth n))).trans stereographicComplex) : C(ℂ, ℂ)))
    Filter.atTop (𝓝 (H : C(ℂ, ℂ))) at hplane
  simpa only [hnplane] using hplane

end DifferentialGeometry.Hyperboloid
