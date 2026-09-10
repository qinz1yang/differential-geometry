import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Geometry.Curvature.LeastRicciOverlap
import DifferentialGeometry.Geometry.Gradient.SignedDifference
import DifferentialGeometry.Geometry.Gradient.AffineCoordinate
import DifferentialGeometry.Geometry.Affine.FiniteLineAlignment

noncomputable section
open Set Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Gradient DifferentialGeometry.Geometry.Affine

namespace DifferentialGeometry.Geometry.Neck

theorem exists_finitely_aligned_least_ricci_fields_of_metric_close
    {n : ℕ} {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M]
    (g : SmoothRiemannianMetric J M) (C : Fin (n + 1) → cylindricalChart J (M := M))
    (U : ∀ i, Set (C i).domain) (hU : ∀ i, IsOpen (U i))
    (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : ∀ i, (C i).metricCloseOn g ε (U i))
    (s c : Fin n → ℝ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    let a := finiteLineAffineAlignment s c
    let v : Fin (n + 1) → M → ℝ := fun i x ↦ (a i).1 * (C i).axial x + (a i).2
    ∃ (ν : Fin (n + 1) → M → ℝ) (Y : Fin (n + 1) → ∀ x : M, TangentSpace J x),
      (∀ i, ContMDiffOn J 𝓘(ℝ) ∞ (v i) (C i).target ∧
        ContMDiffOn J 𝓘(ℝ) ∞ (ν i) ((C i).region (U i)) ∧
        ContMDiffOn J J.tangent ∞ (fun x ↦ (⟨x, Y i x⟩ : TangentBundle J M)) ((C i).region (U i)) ∧
        ∀ x ∈ (C i).region (U i), g.inner x (Y i x) (Y i x) = 1 ∧
          ricciSharp g x (Y i x) = ν i x • Y i x ∧
          (∀ z : TangentSpace J x, g.inner x z z = 1 → ν i x ≤ ricciTensor g x z z) ∧
          |ν i x| ≤ 5772 * (C i).scale * ε ∧
          Module.End.eigenspace (ricciSharp g x).toLinearMap (ν i x) = Submodule.span ℝ {Y i x} ∧
          0 < mvfderiv J (v i) x (Y i x) ∧ |mvfderiv J (v i) x (Y i x) - 1| ≤ 92354 * ε) ∧
      ∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
        ∀ δ : ℝ, 92354 * ε + δ < 1 →
        Real.sqrt (g.inner x (gradFun g (C j.succ).axial x - s j • gradFun g (C j.castSucc).axial x)
          (gradFun g (C j.succ).axial x - s j • gradFun g (C j.castSucc).axial x)) ≤ δ →
        ν j.succ x = ν j.castSucc x ∧ Y j.succ x = Y j.castSucc x := by
  classical
  let a := finiteLineAffineAlignment s c
  let v : Fin (n + 1) → M → ℝ := fun i x ↦ (a i).1 * (C i).axial x + (a i).2
  choose ν Z hu hν hZ hp using fun i ↦
    (C i).exists_least_ricci_field g (hU i) ε hε (hsmall i)
  let Y : Fin (n + 1) → ∀ x : M, TangentSpace J x := fun i x ↦ (a i).1 • Z i x
  have hsign (i) : (a i).1 = 1 ∨ (a i).1 = -1 := finiteLineAffineAlignment_sign s c hs i
  refine ⟨ν, Y, ?_, ?_⟩
  · intro i
    have hva : ContMDiffOn J 𝓘(ℝ) ∞ (v i) (C i).target :=
      (contMDiffOn_const.mul (hu i)).add contMDiffOn_const
    refine ⟨hva, hν i, contMDiffOn_const.smul_section (hZ i), ?_⟩
    intro x hx
    obtain ⟨hn, he, hm, hb, hsp, hpos, hd⟩ := hp i x hx
    have hsq : (a i).1 * (a i).1 = 1 := by rcases hsign i with h | h <;> rw [h] <;> norm_num
    have hne : (a i).1 ≠ 0 := by intro h; rw [h, zero_mul] at hsq; norm_num at hsq
    have htarget : x ∈ (C i).target := by
      obtain ⟨y, _, rfl⟩ := hx
      exact y.property
    have hf : MDifferentiableAt J 𝓘(ℝ) (C i).axial x :=
      ((hu i x htarget).contMDiffAt ((C i).target.isOpen.mem_nhds htarget)).mdifferentiableAt (by decide)
    have hder : mvfderiv J (v i) x (Y i x) = mvfderiv J (C i).axial x (Z i x) :=
      mvfderiv_signed_affine_coordinate (C i).axial x hf (a i).1 (a i).2 (hsign i) (Z i x)
    refine ⟨?_, ?_, hm, hb, ?_, hder.symm ▸ hpos, ?_⟩
    · change g.inner x ((a i).1 • Z i x) ((a i).1 • Z i x) = 1
      simp only [map_smul, smul_apply, smul_eq_mul, hn, mul_one, hsq]
    · change ricciSharp g x ((a i).1 • Z i x) = ν i x • ((a i).1 • Z i x)
      rw [map_smul, he, smul_comm]
    · change Module.End.eigenspace (ricciSharp g x).toLinearMap (ν i x) = Submodule.span ℝ {(a i).1 • Z i x}
      rw [Submodule.span_singleton_smul_eq hne.isUnit, hsp]
    · rwa [hder]
  · intro j x hx hy δ hδ hoverlap
    obtain ⟨hin, hie, him, _, _, _, hid⟩ := hp j.succ x hy
    obtain ⟨hjn, hje, hjm, _, hjs, _, hjd⟩ := hp j.castSucc x hx
    have hc (z : TangentSpace J x) :
        |mvfderiv J (C j.succ).axial x z - s j * mvfderiv J (C j.castSucc).axial x z| ≤
          δ * Real.sqrt (g.inner x z z) :=
      (abs_mvfderiv_signed_difference_le_gradient_norm g (C j.succ).axial (C j.castSucc).axial (s j) x z).trans
        (mul_le_mul_of_nonneg_right hoverlap (Real.sqrt_nonneg _))
    obtain ⟨hμ, hrel, _⟩ := least_ricci_eigenpair_eq_of_signed_covector_error g x
      (mvfderiv J (C j.succ).axial x).toLinearMap (mvfderiv J (C j.castSucc).axial x).toLinearMap
      (ν j.succ x) (ν j.castSucc x) (Z j.succ x) (Z j.castSucc x)
      hin hjn hie hje him hjm hjs (s j) (92354 * ε) (92354 * ε) δ (hs j)
      hid hjd (by linarith) hδ hc
    exact ⟨hμ, finiteLineAffineAlignment_smul_eq s c j (hs j) (Z j.castSucc x) (Z j.succ x) hrel⟩

theorem exists_finitely_aligned_least_ricci_fields
    {n : ℕ} {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M]
    (g : SmoothRiemannianMetric J M) (C : Fin (n + 1) → cylindricalChart J (M := M))
    (U : ∀ i, Set (C i).domain) (hU : ∀ i, IsOpen (U i))
    (ε δ : ℝ) (hε : ε < 1 / 200000) (hδ : 92354 * ε + δ < 1)
    (hsmall : ∀ i, (C i).metricCloseOn g ε (U i))
    (s c e₀ : Fin n → ℝ) (hs : ∀ j, s j = 1 ∨ s j = -1)
    (hvalue : ∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
      |(C j.succ).axial x - (s j * (C j.castSucc).axial x + c j)| ≤ e₀ j)
    (hoverlap : ∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
      Real.sqrt (g.inner x (gradFun g (C j.succ).axial x - s j • gradFun g (C j.castSucc).axial x)
        (gradFun g (C j.succ).axial x - s j • gradFun g (C j.castSucc).axial x)) ≤ δ) :
    let a := finiteLineAffineAlignment s c
    let v : Fin (n + 1) → M → ℝ := fun i x ↦ (a i).1 * (C i).axial x + (a i).2
    ∃ (ν : Fin (n + 1) → M → ℝ) (Y : Fin (n + 1) → ∀ x : M, TangentSpace J x),
      (∀ i, ContMDiffOn J 𝓘(ℝ) ∞ (v i) (C i).target ∧
        ContMDiffOn J 𝓘(ℝ) ∞ (ν i) ((C i).region (U i)) ∧
        ContMDiffOn J J.tangent ∞ (fun x ↦ (⟨x, Y i x⟩ : TangentBundle J M)) ((C i).region (U i)) ∧
        ∀ x ∈ (C i).region (U i), g.inner x (Y i x) (Y i x) = 1 ∧
          ricciSharp g x (Y i x) = ν i x • Y i x ∧
          (∀ z : TangentSpace J x, g.inner x z z = 1 → ν i x ≤ ricciTensor g x z z) ∧
          |ν i x| ≤ 5772 * (C i).scale * ε ∧
          Module.End.eigenspace (ricciSharp g x).toLinearMap (ν i x) = Submodule.span ℝ {Y i x} ∧
          0 < mvfderiv J (v i) x (Y i x) ∧ |mvfderiv J (v i) x (Y i x) - 1| ≤ 92354 * ε) ∧
      (∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
        ν j.succ x = ν j.castSucc x ∧ Y j.succ x = Y j.castSucc x) ∧
      ∀ j : Fin n, ∀ x ∈ (C j.castSucc).region (U j.castSucc), x ∈ (C j.succ).region (U j.succ) →
        |v j.succ x - v j.castSucc x| ≤ e₀ j := by
  obtain ⟨ν, Y, hp, heq⟩ := exists_finitely_aligned_least_ricci_fields_of_metric_close
    g C U hU ε hε hsmall s c hs
  refine ⟨ν, Y, hp, ?_, ?_⟩
  · exact fun j x hx hy ↦ heq j x hx hy δ hδ (hoverlap j x hx hy)
  · intro j x hx hy
    change |(finiteLineAffineAlignment s c j.succ).1 * (C j.succ).axial x +
      (finiteLineAffineAlignment s c j.succ).2 -
      ((finiteLineAffineAlignment s c j.castSucc).1 * (C j.castSucc).axial x +
        (finiteLineAffineAlignment s c j.castSucc).2)| ≤ e₀ j
    rw [abs_finiteLineAffineAlignment_transition_error s c hs]
    exact hvalue j x hx hy

end DifferentialGeometry.Geometry.Neck
