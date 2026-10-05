import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.LocalFlow
import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.GlobalCurve
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Flows of boundary-tangent vector fields on compact manifolds with boundary

A smooth vector field `X` on a compact Hausdorff manifold with boundary (model `𝓡∂ (n + 1)`) which is
tangent to the boundary generates a global flow by diffeomorphisms, jointly smooth in time and
space, with the group law and the integral-curve property
(`exists_flow_of_boundaryTangent_field`; the tangency hypothesis in the chart-free curve form of the
chapter-14 statements: `exists_flow_of_boundary_curve_tangent_field`).

Route: local flows in charts (`BoundaryTangentFlow/LocalFlow.lean`), a uniform time by compactness,
global integral curves by the uniform time lemma (`BoundaryTangentFlow/GlobalCurve.lean`), the group
law by uniqueness, smoothness of each time-`t` map as an iterate of a short-time map, and joint
smoothness from `Φ (t, x) = Φ (t - t₀, Φ (t₀, x))`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.BoundaryTangentFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
  [CompactSpace M] [T2Space M]

/-- **Flow of a boundary-tangent field (coordinate form of tangency).** -/
theorem exists_flow_of_boundaryTangent_field {X : (q : M) → TangentSpace (𝓡∂ (n + 1)) q}
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun q => (⟨q, X q⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (htan : ∀ q, (𝓡∂ (n + 1)).IsBoundaryPoint q →
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) (X q) = 0) :
    ∃ Φ : ℝ → (M ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ M),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (n + 1))) (𝓡∂ (n + 1)) ∞ (fun x : ℝ × M => Φ x.1 x.2) ∧
      (∀ q, Φ 0 q = q) ∧ (∀ s t q, Φ (s + t) q = Φ s (Φ t q)) ∧
      ∀ q, IsMIntegralCurve (fun t => Φ t q) X := by
  classical
  let I := 𝓡∂ (n + 1)
  have hX1 : ContMDiff I I.tangent 1 (fun q => (⟨q, X q⟩ : TangentBundle I M)) :=
    hX.of_le (by simp)
  choose O hO hqO ε hε φ hφs hφ0 hφc using
    fun q => exists_boundaryTangent_localFlow (M := M) hX htan q
  -- a uniform time
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun q _ => mem_iUnion.mpr ⟨q, hqO q⟩)
  have hcover : ∀ x : M, ∃ q ∈ s, x ∈ O q := by
    intro x
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact ⟨q, hq, hxq⟩
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ s, δ ≤ ε q := by
    by_cases hne : s.Nonempty
    · exact ⟨s.inf' hne ε, (Finset.lt_inf'_iff hne).mpr fun q _ => hε q,
        fun q hq => Finset.inf'_le ε hq⟩
    · exact ⟨1, one_pos, fun q hq => absurd ⟨q, hq⟩ hne⟩
  -- global integral curves
  have hlocal : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ X (Ioo (-δ) δ) := by
    intro x
    obtain ⟨q, hq, hxq⟩ := hcover x
    exact ⟨fun t => φ q (t, x), hφ0 q x hxq,
      (hφc q x hxq).mono (Ioo_subset_Ioo (neg_le_neg (hδle q hq)) (hδle q hq))⟩
  choose Γ hΓ0 hΓ using exists_isMIntegralCurve_of_uniform_Ioo hX1 hδ hlocal
  -- the group law
  have hadd : ∀ x : M, ∀ a b : ℝ, Γ x (a + b) = Γ (Γ x b) a := by
    intro x a b
    have h := isMIntegralCurve_eq_of_eq (t₀ := 0) hX1 ((hΓ x).comp_add b) (hΓ (Γ x b))
      (by simp only [Function.comp_apply, zero_add, hΓ0])
    exact congrFun h a
  -- agreement with the local flows
  have hagree : ∀ q x, x ∈ O q → ∀ t ∈ Ioo (-ε q) (ε q), Γ x t = φ q (t, x) := by
    intro q x hx t ht
    have hz : (0 : ℝ) ∈ Ioo (-ε q) (ε q) := ⟨neg_lt_zero.mpr (hε q), hε q⟩
    exact DifferentialGeometry.Topology.Manifold.isMIntegralCurveOn_Ioo_eqOn hz hX1
      ((hΓ x).isMIntegralCurveOn _) (hφc q x hx) (by rw [hΓ0, hφ0 q x hx]) ht
  let F : ℝ × M → M := fun p => Γ p.2 p.1
  -- short-time joint smoothness
  have hshort : ∀ t₀ ∈ Ioo (-δ) δ, ∀ x₀ : M,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ F (t₀, x₀) := by
    intro t₀ ht₀ x₀
    obtain ⟨q, hq, hx₀⟩ := hcover x₀
    have hopen : IsOpen (Ioo (-δ) δ ×ˢ O q) := isOpen_Ioo.prod (hO q)
    have hmem : (t₀, x₀) ∈ Ioo (-δ) δ ×ˢ O q := ⟨ht₀, hx₀⟩
    have hsub : Ioo (-δ) δ ⊆ Ioo (-ε q) (ε q) :=
      Ioo_subset_Ioo (neg_le_neg (hδle q hq)) (hδle q hq)
    have hφat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (φ q) (t₀, x₀) :=
      (hφs q).contMDiffAt ((isOpen_Ioo.prod (hO q)).mem_nhds ⟨hsub ht₀, hx₀⟩)
    apply hφat.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hmem] with p hp
    exact hagree q p.2 hp.2 p.1 (hsub hp.1)
  -- each time-`t` map is smooth
  have hfixed : ∀ t : ℝ, ContMDiff I I ∞ (fun x => Γ x t) := by
    intro t
    obtain ⟨N, hN⟩ := exists_nat_gt (|t| / δ)
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hδ.le) hN
    set τ : ℝ := t / N with hτ
    have hτδ : τ ∈ Ioo (-δ) δ := by
      rw [mem_Ioo, ← abs_lt, hτ, abs_div, Nat.abs_cast, div_lt_iff₀ hNpos]
      rw [div_lt_iff₀ hδ] at hN
      linarith
    have hstep : ContMDiff I I ∞ (fun x => Γ x τ) := by
      intro x
      exact (hshort τ hτδ x).comp x (contMDiffAt_const.prodMk contMDiffAt_id)
    have hiter : ∀ k : ℕ, ContMDiff I I ∞ (fun x => Γ x (k * τ)) := by
      intro k
      induction k with
      | zero =>
        refine contMDiff_id.congr fun x => ?_
        simp only [Nat.cast_zero, zero_mul, hΓ0, id]
      | succ k ih =>
        refine (hstep.comp ih).congr fun x => ?_
        simp only [Function.comp_apply, Nat.cast_succ]
        rw [add_mul, one_mul, add_comm, hadd x τ (k * τ)]
    have hNτ : (N : ℝ) * τ = t := by
      rw [hτ]
      field_simp
    have h := hiter N
    rw [hNτ] at h
    exact h
  -- joint smoothness
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ F := by
    intro p
    obtain ⟨t₀, x₀⟩ := p
    have hmap : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × M => (p.1 - t₀, Γ p.2 t₀)) :=
      (contMDiff_fst.sub contMDiff_const).prodMk ((hfixed t₀).comp contMDiff_snd)
    have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
    have hcomp := ContMDiffAt.comp_of_eq (x := (t₀, x₀)) (hshort 0 hzero (Γ x₀ t₀))
      hmap.contMDiffAt (by simp only [sub_self])
    apply hcomp.congr_of_eventuallyEq
    filter_upwards with p
    change Γ p.2 p.1 = Γ (Γ p.2 t₀) (p.1 - t₀)
    rw [← hadd, sub_add_cancel]
  -- the diffeomorphisms
  have hinv : ∀ t x, Γ (Γ x t) (-t) = x := by
    intro t x
    rw [← hadd, neg_add_cancel, hΓ0]
  let Φ : ℝ → (M ≃ₘ⟮I, I⟯ M) := fun t =>
    { toFun := fun x => Γ x t
      invFun := fun x => Γ x (-t)
      left_inv := fun x => hinv t x
      right_inv := fun x => by
        change Γ (Γ x (-t)) t = x
        have h := hinv (-t) x
        rwa [neg_neg] at h
      contMDiff_toFun := hfixed t
      contMDiff_invFun := hfixed (-t) }
  refine ⟨Φ, hF, fun q => hΓ0 q, fun a b q => hadd q a b, fun q => hΓ q⟩

/-- **Flow of a boundary-tangent field (curve form of tangency, as in the chapter-14 statements).** -/
theorem exists_flow_of_boundary_curve_tangent_field
    (X : (q : M) → TangentSpace (𝓡∂ (n + 1)) q)
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun q => (⟨q, X q⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (htan : ∀ q, (𝓡∂ (n + 1)).IsBoundaryPoint q → ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) ∞ γ ∧ γ 0 = q ∧ (∀ t, (𝓡∂ (n + 1)).IsBoundaryPoint (γ t)) ∧
        mfderiv 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) γ 0 1 = X q) :
    ∃ Φ : ℝ → (M ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ M),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (n + 1))) (𝓡∂ (n + 1)) ∞ (fun x : ℝ × M => Φ x.1 x.2) ∧
      (∀ q, Φ 0 q = q) ∧ (∀ s t q, Φ (s + t) q = Φ s (Φ t q)) ∧
      ∀ q, IsMIntegralCurve (fun t => Φ t q) X := by
  apply exists_flow_of_boundaryTangent_field hX
  intro q hq
  obtain ⟨γ, hγ, hγ0, hγb, hγX⟩ := htan q hq
  subst hγ0
  rw [← hγX]
  exact proj_zero_mfderiv_eq_zero_of_boundary_curve hγ hγb

end DifferentialGeometry.Manifold.BoundaryTangentFlow
