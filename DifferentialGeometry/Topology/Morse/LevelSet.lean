import DifferentialGeometry.Topology.Morse.LocalNormalForm
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ChartedSpace

open scoped Manifold Topology

namespace DifferentialGeometry.Topology.Morse

noncomputable section

abbrev LevelSetSpace {M : Type} (f : M → ℝ) (a : ℝ) : Type := {x : M // f x = a}

noncomputable def levelSetReindex {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1)) :
    MorseModel (m + 1) ≃ₗ[ℝ] MorseModel (m + 1) where
  toFun := fun v j => v (e.symm j)
  map_add' := by
    intro x y
    ext j
    rfl
  map_smul' := by
    intro a x
    ext j
    rfl
  invFun := fun v j => v (e j)
  left_inv := by
    intro v
    ext j
    simp
  right_inv := by
    intro v
    ext j
    simp

theorem levelSetReindex_apply {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1))
    (v : MorseModel (m + 1)) (j : Fin (m + 1)) :
    levelSetReindex e v j = v (e.symm j) := rfl

theorem levelSetReindex_comp {m : ℕ} (e₁ e₂ : Fin (m + 1) ≃ Fin (m + 1))
    (v : MorseModel (m + 1)) :
    levelSetReindex e₁ (levelSetReindex e₂ v) = levelSetReindex (e₂.trans e₁) v := by
  ext j
  simp [levelSetReindex_apply]

theorem levelSetReindex_symm {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1))
    (v : MorseModel (m + 1)) :
    levelSetReindex e (levelSetReindex e.symm v) = v := by
  ext j
  simp [levelSetReindex_apply]

theorem levelSetReindex_lastBasis {m : ℕ} (i : Fin (m + 1)) :
    levelSetReindex (Equiv.swap i (Fin.last m))
        (fun j : Fin (m + 1) => if j = Fin.last m then (1 : ℝ) else 0) =
      (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) := by
  ext j
  rw [levelSetReindex_apply]
  by_cases hj : j = i
  · subst j
    have h : (Equiv.swap i (Fin.last m)).symm i = Fin.last m := by simp
    rw [h]
    simp
  · have hne : (Equiv.swap i (Fin.last m)).symm j ≠ Fin.last m := by
      intro h'
      apply hj
      have hback := congrArg (Equiv.swap i (Fin.last m)) h'
      simpa using hback
    rw [if_neg hne]
    simp [hj]

theorem exists_coord_of_fderiv_ne_zero {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (y : MorseModel (m + 1)) (h : fderiv ℝ g y ≠ 0) :
    ∃ i : Fin (m + 1), (fderiv ℝ g y)
      (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) ≠ 0 := by
  by_contra hz
  apply h
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ j : Fin (m + 1), v j • (fun k : Fin (m + 1) => if k = j then (1 : ℝ) else 0) := by
    ext k
    simp [Finset.sum_apply, Pi.smul_apply]
  have hzall : ∀ j : Fin (m + 1), (fderiv ℝ g y)
      (fun k : Fin (m + 1) => if k = j then (1 : ℝ) else 0) = 0 := by
    intro j
    by_contra hne
    exact hz ⟨j, hne⟩
  rw [hv]
  simp [hzall]

noncomputable def levelSetSplit (m : ℕ) : (MorseModel m × ℝ) ≃ₗ[ℝ] MorseModel (m + 1) where
  toFun := fun p j =>
    if h : j = Fin.last m then p.2 else p.1 (Fin.castPred j h)
  map_add' := by
    intro x y
    ext j
    by_cases h : j = Fin.last m <;> simp [h]
  map_smul' := by
    intro a x
    ext j
    by_cases h : j = Fin.last m <;> simp [h]
  invFun := fun v => ((fun i : Fin m => v (Fin.castSucc i)), v (Fin.last m))
  left_inv := by
    intro p
    ext i
    · change (fun j : Fin (m + 1) => if h : j = Fin.last m then p.2 else p.1 (Fin.castPred j h))
          (Fin.castSucc i) = p.1 i
      have h : Fin.castSucc i ≠ Fin.last m := Fin.castSucc_ne_last i
      simp [h]
    · change (fun j : Fin (m + 1) => if h : j = Fin.last m then p.2 else p.1 (Fin.castPred j h))
          (Fin.last m) = p.2
      simp
  right_inv := by
    intro v
    ext j
    by_cases h : j = Fin.last m
    · subst j
      simp
    · change (if h : Fin.castSucc (Fin.castPred j h) = Fin.last m then v (Fin.last m)
          else v (Fin.castSucc (Fin.castPred j h))) = v j
      have hne : Fin.castSucc (Fin.castPred j h) ≠ Fin.last m := Fin.castSucc_ne_last (Fin.castPred j h)
      rw [dif_neg hne]
      rw [Fin.castSucc_castPred j h]

noncomputable def scalarLinearEquiv {𝕜 : Type*} [NormedField 𝕜] (c : 𝕜) (hc : c ≠ 0) :
    𝕜 ≃L[𝕜] 𝕜 where
  toFun := fun z => c • z
  invFun := fun z => c⁻¹ • z
  map_add' := by
    intro x y
    simp [smul_eq_mul, mul_add]
  map_smul' := by
    intro a x
    simp [smul_eq_mul]
    ring
  continuous_toFun := continuous_id.const_smul c
  continuous_invFun := continuous_id.const_smul c⁻¹
  left_inv := by
    intro x
    change c⁻¹ • (c • x) = x
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  right_inv := by
    intro x
    change c • (c⁻¹ • x) = x
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

def levelSetLastBasis {m : ℕ} : MorseModel (m + 1) :=
  fun j : Fin (m + 1) => if j = Fin.last m then (1 : ℝ) else 0

theorem levelSetSplit_basis (m : ℕ) :
    levelSetSplit m (0, (1 : ℝ)) = levelSetLastBasis := by
  ext j
  by_cases hj : j = Fin.last m
  · subst j
    dsimp [levelSetSplit]
    simp [levelSetLastBasis]
  · dsimp [levelSetSplit]
    simp [hj, levelSetLastBasis]

theorem levelSetReindex_swap_swap {m : ℕ} (i : Fin (m + 1)) (u₀ : MorseModel (m + 1)) :
    levelSetReindex (Equiv.swap i (Fin.last m)) (levelSetReindex (Equiv.swap i (Fin.last m)) u₀) =
      u₀ := by
  have hs : (Equiv.swap i (Fin.last m)).symm = Equiv.swap i (Fin.last m) := by
    ext j
    simp
  rw [← hs]
  exact levelSetReindex_symm (Equiv.swap i (Fin.last m)) u₀

theorem levelSetReindex_lastDeriv_ne_zero {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (u₀ : MorseModel (m + 1)) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g u₀) (i : Fin (m + 1))
    (hi : (fderiv ℝ g u₀) (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) ≠ 0) :
    (fderiv ℝ (fun w => g (levelSetReindex (Equiv.swap i (Fin.last m)) w))
      (levelSetReindex (Equiv.swap i (Fin.last m)) u₀)) levelSetLastBasis ≠ 0 := by
  let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap i (Fin.last m)
  let u₁ : MorseModel (m + 1) := levelSetReindex e u₀
  have hder : fderiv ℝ (fun w => g (levelSetReindex e w)) u₁ =
      (fderiv ℝ g (levelSetReindex e u₁)).comp ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)) := by
    have hgdiff : DifferentiableAt ℝ g (levelSetReindex e u₁) := by
      rw [levelSetReindex_swap_swap]
      exact hg.differentiableAt (by norm_num)
    have hldiff : DifferentiableAt ℝ (fun w : MorseModel (m + 1) => levelSetReindex e w) u₁ :=
      ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).differentiableAt
    have hcomp := fderiv_comp u₁ (g := g) (f := fun w : MorseModel (m + 1) => levelSetReindex e w)
      hgdiff hldiff
    have hldiff_der : fderiv ℝ (fun w : MorseModel (m + 1) => levelSetReindex e w) u₁ =
        ((levelSetReindex e).toContinuousLinearEquiv :
          MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)) := by
      exact (ContinuousLinearMap.fderiv ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)))
    simpa [hldiff_der] using hcomp
  have hval : (fderiv ℝ g (levelSetReindex e u₁))
      (levelSetReindex e levelSetLastBasis) =
      (fderiv ℝ g u₀) (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) := by
    rw [levelSetReindex_swap_swap]
    have hlb : levelSetReindex e levelSetLastBasis =
        (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) := by
      simpa [e, levelSetLastBasis] using levelSetReindex_lastBasis i
    rw [hlb]
  rw [hder]
  change (fderiv ℝ g (levelSetReindex e u₁)) (levelSetReindex e levelSetLastBasis) ≠ 0
  rwa [hval]

theorem levelSetImplicitFunction {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (u₀ : MorseModel (m + 1)) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g u₀)
    (hlast : (fderiv ℝ g u₀) levelSetLastBasis ≠ 0) :
    ∃ ψ : MorseModel m → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) ψ ((levelSetSplit m).symm u₀).1 ∧
      (∀ᶠ y in nhds ((levelSetSplit m).symm u₀).1,
        g (levelSetSplit m (y, ψ y)) = g u₀) := by
  let u₁ : MorseModel m × ℝ := (levelSetSplit m).symm u₀
  let F : MorseModel m × ℝ → ℝ := fun p => g (levelSetSplit m p)
  have hF : ContDiffAt ℝ (⊤ : ℕ∞) F u₁ := by
    have hlin : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : MorseModel m × ℝ => levelSetSplit m p) u₁ :=
      ((levelSetSplit m).toContinuousLinearEquiv :
          (MorseModel m × ℝ) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
    have hg' : ContDiffAt ℝ (⊤ : ℕ∞) g (levelSetSplit m u₁) := by
      simpa [u₁] using hg
    exact hg'.comp u₁ hlin
  have hFder : (fderiv ℝ F u₁ ∘L ContinuousLinearMap.inr ℝ (MorseModel m) ℝ).IsInvertible := by
    have hder : fderiv ℝ F u₁ = (fderiv ℝ g (levelSetSplit m u₁)).comp
        ((levelSetSplit m).toContinuousLinearEquiv :
          (MorseModel m × ℝ) →L[ℝ] MorseModel (m + 1)) := by
      have hgdiff : DifferentiableAt ℝ g (levelSetSplit m u₁) := by
        simpa [u₁] using (hg.differentiableAt (by norm_num))
      have hldiff : DifferentiableAt ℝ (fun p : MorseModel m × ℝ => levelSetSplit m p) u₁ :=
        ((levelSetSplit m).toContinuousLinearEquiv :
          (MorseModel m × ℝ) →L[ℝ] MorseModel (m + 1)).differentiableAt
      have hcomp := fderiv_comp u₁ (g := g) (f := fun p : MorseModel m × ℝ => levelSetSplit m p)
        hgdiff hldiff
      have hldiff_der : fderiv ℝ (fun p : MorseModel m × ℝ => levelSetSplit m p) u₁ =
          ((levelSetSplit m).toContinuousLinearEquiv :
            (MorseModel m × ℝ) →L[ℝ] MorseModel (m + 1)) := by
        exact (ContinuousLinearMap.fderiv ((levelSetSplit m).toContinuousLinearEquiv :
          (MorseModel m × ℝ) →L[ℝ] MorseModel (m + 1)))
      simpa [F, hldiff_der] using hcomp
    have hscalar : (fderiv ℝ F u₁ ∘L ContinuousLinearMap.inr ℝ (MorseModel m) ℝ) =
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          ((fderiv ℝ g u₀) (fun j : Fin (m + 1) => if j = Fin.last m then (1 : ℝ) else 0))) := by
      apply ContinuousLinearMap.ext
      intro z
      rw [hder]
      change (fderiv ℝ g (levelSetSplit m u₁))
        (levelSetSplit m (0, z)) = z • ((fderiv ℝ g u₀) levelSetLastBasis)
      have hlin : (fderiv ℝ g (levelSetSplit m u₁))
          (levelSetSplit m (0, z)) =
          z • (fderiv ℝ g (levelSetSplit m u₁)) (levelSetSplit m (0, (1 : ℝ))) := by
        have hs : levelSetSplit m (0, z) = z • levelSetSplit m (0, (1 : ℝ)) := by
          ext j
          dsimp [levelSetSplit]
          by_cases hj : j = Fin.last m
          · subst j
            simp
          · simp [hj]
        rw [hs]
        simp
      rw [hlin]
      have hpt : (levelSetSplit m) u₁ = u₀ := (levelSetSplit m).apply_symm_apply u₀
      rw [hpt, levelSetSplit_basis]
    rw [hscalar]
    refine ⟨scalarLinearEquiv ((fderiv ℝ g u₀) levelSetLastBasis) hlast, ?_⟩
    apply ContinuousLinearMap.ext
    intro z
    change ((fderiv ℝ g u₀) levelSetLastBasis) • z =
      z * (fderiv ℝ g u₀) levelSetLastBasis
    simp [smul_eq_mul, mul_comm]
  exact ⟨hF.implicitFunction (by norm_num) hFder, by
    have hsm := hF.contDiffAt_implicitFunction (by norm_num) hFder
    simpa [F] using hsm, by
    have hgrap := hF.eventually_apply_implicitFunction (by norm_num) hFder
    filter_upwards [hgrap] with y hy
    simpa [u₁, F] using hy⟩

theorem exists_levelSet_local_graph {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (u₀ : MorseModel (m + 1)) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g u₀) (h : fderiv ℝ g u₀ ≠ 0) :
    ∃ (e : Fin (m + 1) ≃ Fin (m + 1)) (ψ : MorseModel m → ℝ),
      ContDiffAt ℝ (⊤ : ℕ∞) ψ ((levelSetSplit m).symm (levelSetReindex e u₀)).1 ∧
      (∀ᶠ y in nhds ((levelSetSplit m).symm (levelSetReindex e u₀)).1,
        g (levelSetReindex e (levelSetSplit m (y, ψ y))) = g u₀) := by
  rcases exists_coord_of_fderiv_ne_zero g u₀ h with ⟨i, hi⟩
  let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap i (Fin.last m)
  let u₁ : MorseModel (m + 1) := levelSetReindex e u₀
  have hs : e.symm = e := by
    ext j
    simp [e]
  have hfix : levelSetReindex e (levelSetReindex e u₀) = u₀ := by
    rw [← hs]
    exact levelSetReindex_symm e u₀
  have hpt : levelSetReindex e u₁ = u₀ := by
    simpa [u₁] using hfix
  have hG : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => g (levelSetReindex e w)) u₁ := by
    have hlin : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : MorseModel (m + 1) => levelSetReindex e w) u₁ :=
      ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
    have hg' : ContDiffAt ℝ (⊤ : ℕ∞) g (levelSetReindex e u₁) := by
      rw [hpt]
      exact hg
    exact hg'.comp u₁ hlin
  have hlastG : (fderiv ℝ (fun w => g (levelSetReindex e w)) u₁)
      (fun j : Fin (m + 1) => if j = Fin.last m then (1 : ℝ) else 0) ≠ 0 := by
    simpa [u₁, levelSetLastBasis] using levelSetReindex_lastDeriv_ne_zero g u₀ hg i hi
  rcases levelSetImplicitFunction (fun w => g (levelSetReindex e w)) u₁ hG hlastG with
    ⟨ψ, hψ, hgrap⟩
  exact ⟨e, ψ, hψ, by
    filter_upwards [hgrap] with y hy
    simpa [u₁, hpt] using hy⟩

def levelSetSplitFst (m : ℕ) : MorseModel (m + 1) →L[ℝ] MorseModel m :=
  (ContinuousLinearMap.fst ℝ (MorseModel m) ℝ).comp
    ((levelSetSplit m).symm.toContinuousLinearEquiv : MorseModel (m + 1) →L[ℝ] (MorseModel m × ℝ))

theorem levelSetSplitFst_split (m : ℕ) (y : MorseModel m) (z : ℝ) :
    levelSetSplitFst m (levelSetSplit m (y, z)) = y := by
  simp [levelSetSplitFst]

theorem levelSetSplit_add_basis (m : ℕ) (y : MorseModel m) (z : ℝ) :
    levelSetSplit m (y, z) = levelSetSplit m (y, 0) + z • levelSetLastBasis := by
  have hlin := (levelSetSplit m).map_add (y, (0 : ℝ)) (0, z)
  have hz : (levelSetSplit m) (0, z) = z • levelSetLastBasis := by
    rw [← levelSetSplit_basis m]
    simpa using (levelSetSplit m).map_smul z (0, (1 : ℝ))
  rw [hz] at hlin
  simpa [add_comm, add_left_comm, add_assoc] using hlin

noncomputable def levelSetChartDerivInvFun {m : ℕ} (D : MorseModel (m + 1) →L[ℝ] ℝ) :
    (ℝ × MorseModel m) → MorseModel (m + 1) :=
  fun q => levelSetSplit m (q.2, (q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis)

noncomputable def levelSetChartDerivEquiv {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (w : MorseModel (m + 1))
    (hc : (fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis ≠ 0) :
    MorseModel (m + 1) ≃L[ℝ] (ℝ × MorseModel m) where
  toFun := fun v => ((fderiv ℝ (fun v => g (levelSetReindex e v)) w) v, levelSetSplitFst m v)
  invFun := levelSetChartDerivInvFun (fderiv ℝ (fun v => g (levelSetReindex e v)) w)
  left_inv := by
    intro v
    let D : MorseModel (m + 1) →L[ℝ] ℝ := fderiv ℝ (fun v => g (levelSetReindex e v)) w
    let y : MorseModel m := levelSetSplitFst m v
    let z : ℝ := ((levelSetSplit m).symm v).2
    have hv : v = levelSetSplit m (y, z) := by
      have hsymm : (levelSetSplit m).symm v = (y, z) := by
        simp [y, z, levelSetSplitFst]
      rw [← hsymm]
      exact ((levelSetSplit m).apply_symm_apply v).symm
    have hlin : D (levelSetSplit m (y, z)) = D (levelSetSplit m (y, 0)) + z • D levelSetLastBasis := by
      rw [levelSetSplit_add_basis]
      rw [map_add, map_smul]
    change levelSetSplit m (y, (D v - D (levelSetSplit m (y, 0))) / D levelSetLastBasis) = v
    rw [hv]
    rw [hlin]
    have hz : (D (levelSetSplit m (y, 0)) + z • D levelSetLastBasis -
        D (levelSetSplit m (y, 0))) / D levelSetLastBasis = z := by
      rw [smul_eq_mul]
      rw [add_sub_cancel_left]
      rw [div_eq_mul_inv]
      rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
    rw [hz]
  right_inv := by
    intro q
    let D : MorseModel (m + 1) →L[ℝ] ℝ := fderiv ℝ (fun v => g (levelSetReindex e v)) w
    change (D (levelSetSplit m (q.2, (q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis)),
        levelSetSplitFst m (levelSetSplit m (q.2, (q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis))) = q
    rw [levelSetSplitFst_split]
    apply Prod.ext
    · change D (levelSetSplit m (q.2, (q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis)) = q.1
      rw [levelSetSplit_add_basis]
      rw [map_add, map_smul]
      have hz : ((q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis) • D levelSetLastBasis =
          q.1 - D (levelSetSplit m (q.2, 0)) := by
        rw [smul_eq_mul]
        exact div_mul_cancel₀ (q.1 - D (levelSetSplit m (q.2, 0))) hc
      rw [hz]
      ring
    · rfl
  map_add' := by
    intro x y
    ext <;> simp [map_add]
  map_smul' := by
    intro c x
    ext <;> simp [map_smul, smul_eq_mul]
  continuous_invFun := by
    have hsplit : Continuous (levelSetSplit m) := (levelSetSplit m).toContinuousLinearEquiv.continuous
    change Continuous (fun q : ℝ × MorseModel m =>
      levelSetSplit m (q.2, (q.1 - (fderiv ℝ (fun v => g (levelSetReindex e v)) w)
        (levelSetSplit m (q.2, 0))) / ((fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis)))
    exact hsplit.comp (by fun_prop)

noncomputable def levelSetChartMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) : MorseModel (m + 1) → ℝ × MorseModel m :=
  fun w => (g (levelSetReindex e w), levelSetSplitFst m w)

theorem contDiffAt_levelSetChartMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (w : MorseModel (m + 1))
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g (levelSetReindex e w)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (levelSetChartMap g e) w := by
  have hlin : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetReindex e v) w :=
    ((levelSetReindex e).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
  have hg' : ContDiffAt ℝ (⊤ : ℕ∞) (fun v => g (levelSetReindex e v)) w :=
    hg.comp w hlin
  have hp : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetSplitFst m v) w :=
    (levelSetSplitFst m).contDiff.contDiffAt
  simpa [levelSetChartMap] using hg'.prodMk hp

theorem contDiff_levelSetChartMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (levelSetChartMap g e) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetReindex e v) :=
    ((levelSetReindex e).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff
  have hg' : ContDiff ℝ (⊤ : ℕ∞) (fun v => g (levelSetReindex e v)) :=
    hg.comp hlin
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetSplitFst m v) :=
    (levelSetSplitFst m).contDiff
  simpa [levelSetChartMap] using hg'.prodMk hp

theorem hasFDerivAt_levelSetChartMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (w : MorseModel (m + 1))
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g (levelSetReindex e w))
    (hc : (fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis ≠ 0) :
    HasFDerivAt (levelSetChartMap g e)
      (↑(levelSetChartDerivEquiv g e w hc) : MorseModel (m + 1) →L[ℝ] (ℝ × MorseModel m)) w := by
  have hdiff : DifferentiableAt ℝ (fun v => g (levelSetReindex e v)) w := by
    have hlin : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetReindex e v) w :=
      ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
    exact (hg.comp w hlin).differentiableAt (by norm_num)
  have h₁ : HasFDerivAt (fun v => g (levelSetReindex e v))
      (fderiv ℝ (fun v => g (levelSetReindex e v)) w) w :=
    hdiff.hasFDerivAt
  have h₂ : HasFDerivAt (fun v : MorseModel (m + 1) => levelSetSplitFst m v)
      (levelSetSplitFst m) w :=
    (levelSetSplitFst m).hasFDerivAt
  have hpair := h₁.prodMk h₂
  have heq : (fderiv ℝ (fun v => g (levelSetReindex e v)) w).prod (levelSetSplitFst m) =
      ↑(levelSetChartDerivEquiv g e w hc) := by
    ext v <;> rfl
  simpa [levelSetChartMap, heq] using hpair

def levelSetLastDerivSet {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) : Set (MorseModel (m + 1)) :=
  {w | (fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis ≠ 0}

theorem levelSetLastDerivSet_open {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    IsOpen (levelSetLastDerivSet g e) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetReindex e v) :=
    ((levelSetReindex e).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun v => g (levelSetReindex e v)) := hg.comp hlin
  have hf : Continuous (fderiv ℝ (fun v => g (levelSetReindex e v))) :=
    hG.continuous_fderiv (by norm_num)
  have hcont : Continuous (fun w : MorseModel (m + 1) =>
      (fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis) :=
    hf.clm_apply continuous_const
  exact isOpen_compl_singleton.preimage hcont

theorem levelSetChart_invFun_mem {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) {a : ℝ}
    (ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m))
    (hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e)
    {z : MorseModel m} (hz : (a, z) ∈ ψ.target) :
    g (levelSetReindex e (ψ.symm (a, z))) = a := by
  have hval : (ψ (ψ.symm (a, z))).1 = a := by
    rw [ψ.right_inv hz]
  have h1 : (ψ (ψ.symm (a, z))).1 = g (levelSetReindex e (ψ.symm (a, z))) := by
    rw [hψ]
    rfl
  exact h1.symm.trans hval

private structure LevelSetChartData {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) where
  i : Fin (m + 1)
  hi : (fderiv ℝ g x.1) (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) ≠ 0
  e : Fin (m + 1) ≃ Fin (m + 1)
  he : e = Equiv.swap i (Fin.last m)
  u₁ : MorseModel (m + 1)
  hu₁ : u₁ = levelSetReindex e x.1
  hc : (fderiv ℝ (fun v => g (levelSetReindex e v)) u₁) levelSetLastBasis ≠ 0
  φ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m)
  ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m)
  hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e
  hψsource : ψ.source = φ.source ∩ levelSetLastDerivSet g e

private noncomputable def levelSetChartData.mk {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    LevelSetChartData g a x hg hreg := by
  classical
  let i : Fin (m + 1) := Classical.choose (exists_coord_of_fderiv_ne_zero g x.1 hreg)
  have hi : (fderiv ℝ g x.1) (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) ≠ 0 :=
    Classical.choose_spec (exists_coord_of_fderiv_ne_zero g x.1 hreg)
  let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap i (Fin.last m)
  let u₁ : MorseModel (m + 1) := levelSetReindex e x.1
  have hg' : ContDiffAt ℝ (⊤ : ℕ∞) g (levelSetReindex e u₁) := by
    rw [levelSetReindex_swap_swap]
    exact hg.contDiffAt
  have hc : (fderiv ℝ (fun v => g (levelSetReindex e v)) u₁) levelSetLastBasis ≠ 0 :=
    levelSetReindex_lastDeriv_ne_zero g x.1 hg.contDiffAt i hi
  let φ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) :=
    ContDiffAt.toOpenPartialHomeomorph (f := levelSetChartMap g e)
      (contDiffAt_levelSetChartMap g e u₁ hg') (hasFDerivAt_levelSetChartMap g e u₁ hg' hc)
      (by norm_num)
  let ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) :=
    φ.restrOpen (levelSetLastDerivSet g e) (levelSetLastDerivSet_open g e hg)
  have hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e := by
    simp [ψ, φ, ContDiffAt.toOpenPartialHomeomorph_coe]
  exact ⟨i, hi, e, rfl, u₁, rfl, hc, φ, ψ, hψ, by
    rw [OpenPartialHomeomorph.restrOpen_source]⟩

noncomputable def levelSetChart {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    OpenPartialHomeomorph (LevelSetSpace g a) (MorseModel m) := by
  classical
  let d := levelSetChartData.mk g a x hg hreg
  let ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d.ψ
  have hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g d.e := d.hψ
  let inv : MorseModel m → LevelSetSpace g a := fun z =>
    if hz : (a, z) ∈ ψ.target then
      ⟨levelSetReindex d.e (ψ.symm (a, z)), levelSetChart_invFun_mem g d.e ψ hψ hz⟩
    else ⟨x.1, x.2⟩
  exact
    { toPartialEquiv :=
        { toFun := fun y : LevelSetSpace g a => (ψ (levelSetReindex d.e y.1)).2
          invFun := inv
          source := {y : LevelSetSpace g a | levelSetReindex d.e y.1 ∈ ψ.source}
          target := {z : MorseModel m | (a, z) ∈ ψ.target}
          map_source' := by
            intro y hy
            change (a, (ψ (levelSetReindex d.e y.1)).2) ∈ ψ.target
            have h1 : (ψ (levelSetReindex d.e y.1)).1 = a := by
              rw [hψ]
              change g (levelSetReindex d.e (levelSetReindex d.e y.1)) = a
              rw [d.he, levelSetReindex_swap_swap]
              exact y.2
            have hpair : (a, (ψ (levelSetReindex d.e y.1)).2) = ψ (levelSetReindex d.e y.1) :=
              Prod.ext h1.symm rfl
            rw [hpair]
            exact ψ.map_source hy
          map_target' := by
            intro z hz
            change levelSetReindex d.e ((inv z).1) ∈ ψ.source
            simp only [inv, dif_pos (show (a, z) ∈ ψ.target from hz)]
            rw [d.he, levelSetReindex_swap_swap]
            exact ψ.map_target hz
          left_inv' := by
            intro y hy
            have h1 : (ψ (levelSetReindex d.e y.1)).1 = a := by
              rw [hψ]
              change g (levelSetReindex d.e (levelSetReindex d.e y.1)) = a
              rw [d.he, levelSetReindex_swap_swap]
              exact y.2
            have hz : (a, (ψ (levelSetReindex d.e y.1)).2) ∈ ψ.target := by
              have hpair : (a, (ψ (levelSetReindex d.e y.1)).2) = ψ (levelSetReindex d.e y.1) :=
                Prod.ext h1.symm rfl
              rw [hpair]
              exact ψ.map_source hy
            change inv (ψ (levelSetReindex d.e y.1)).2 = y
            simp only [inv, dif_pos hz]
            apply Subtype.ext
            change levelSetReindex d.e (ψ.symm (a, (ψ (levelSetReindex d.e y.1)).2)) = y.1
            have hpair : (a, (ψ (levelSetReindex d.e y.1)).2) = ψ (levelSetReindex d.e y.1) :=
              Prod.ext h1.symm rfl
            have hleft : ψ.symm (ψ (levelSetReindex d.e y.1)) = levelSetReindex d.e y.1 :=
              ψ.left_inv hy
            rw [← hpair] at hleft
            rw [hleft]
            rw [d.he, levelSetReindex_swap_swap]
          right_inv' := by
            intro z hz
            simp only [inv, dif_pos (show (a, z) ∈ ψ.target from hz)]
            rw [d.he, levelSetReindex_swap_swap]
            exact congrArg Prod.snd (ψ.right_inv hz) }
      open_source := by
        have hcont : Continuous (fun y : LevelSetSpace g a => levelSetReindex d.e y.1) :=
          ((levelSetReindex d.e).toContinuousLinearEquiv :
            MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).continuous.comp continuous_subtype_val
        exact ψ.open_source.preimage hcont
      open_target := by
        have hcont : Continuous (fun z : MorseModel m => (a, z)) := by fun_prop
        exact ψ.open_target.preimage hcont
      continuousOn_toFun := by
        have hf : Continuous (fun y : LevelSetSpace g a => levelSetReindex d.e y.1) :=
          ((levelSetReindex d.e).toContinuousLinearEquiv :
            MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).continuous.comp continuous_subtype_val
        have hcomp : ContinuousOn (fun y : LevelSetSpace g a => ψ (levelSetReindex d.e y.1))
            {y : LevelSetSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} :=
          ψ.continuousOn.comp hf.continuousOn (by intro y hy; exact hy)
        exact continuous_snd.comp_continuousOn hcomp
      continuousOn_invFun := by
        let s : Set (MorseModel m) := {z | (a, z) ∈ ψ.target}
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hc : Continuous (fun z : s => (a, (z : MorseModel m))) := by fun_prop
        have hc0 : Continuous (fun z : s => ψ.symm (a, (z : MorseModel m))) := by
          have hc0' : ContinuousOn (fun z : s => ψ.symm (a, (z : MorseModel m))) (Set.univ : Set s) := by
            refine ψ.symm.continuousOn.comp hc.continuousOn ?_
            intro z hz
            exact z.2
          exact continuousOn_univ.mp hc0'
        have hc1 : Continuous (fun z : s =>
            (⟨levelSetReindex d.e (ψ.symm (a, (z : MorseModel m))),
              levelSetChart_invFun_mem g d.e ψ hψ (show (a, (z : MorseModel m)) ∈ ψ.target from z.2)⟩ :
                LevelSetSpace g a)) :=
          Continuous.subtype_mk
            (((levelSetReindex d.e).toContinuousLinearEquiv :
              MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).continuous.comp hc0)
            (fun z : s => levelSetChart_invFun_mem g d.e ψ hψ
              (show (a, (z : MorseModel m)) ∈ ψ.target from z.2))
        refine hc1.congr ?_
        intro z
        simp only [Set.restrict, inv]
        rw [dif_pos (show (a, (z : MorseModel m)) ∈ ψ.target from z.2)] }

theorem mem_levelSetChart_source {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    x ∈ (levelSetChart g a x hg hreg).source := by
  classical
  let d := levelSetChartData.mk g a x hg hreg
  change levelSetReindex d.e x.1 ∈ d.ψ.source
  rw [d.hψsource]
  constructor
  · rw [← d.hu₁]
    exact ContDiffAt.mem_toOpenPartialHomeomorph_source (f := levelSetChartMap g d.e)
      (contDiffAt_levelSetChartMap g d.e d.u₁ (by
        rw [d.hu₁, d.he, levelSetReindex_swap_swap]
        exact hg.contDiffAt))
      (hasFDerivAt_levelSetChartMap g d.e d.u₁ (by
        rw [d.hu₁, d.he, levelSetReindex_swap_swap]
        exact hg.contDiffAt) d.hc)
      (by norm_num)
  · rw [← d.hu₁]
    exact d.hc

noncomputable def levelSetChartValue {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    MorseModel (m + 1) → MorseModel m :=
  let d := levelSetChartData.mk g a x hg hreg
  fun y => levelSetSplitFst m (levelSetReindex d.e y)

noncomputable def levelSetChartInvValueRaw {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    MorseModel m → MorseModel (m + 1) :=
  let d := levelSetChartData.mk g a x hg hreg
  fun z => levelSetReindex d.e (d.ψ.symm (a, z))

noncomputable def levelSetChartInvValue {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    MorseModel m → MorseModel (m + 1) :=
  fun z => levelSetChartInvValueRaw g a x hg hreg z

noncomputable def levelSetChartDomain {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    Set (MorseModel m) :=
  let d := levelSetChartData.mk g a x hg hreg
  {z : MorseModel m | (a, z) ∈ d.ψ.target}

theorem levelSetChart_apply_value' {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0)
    (y : LevelSetSpace g a) :
    ((levelSetChart g a x hg hreg) y : MorseModel m) = levelSetChartValue g a x hg hreg y.1 := by
  classical
  let d := levelSetChartData.mk g a x hg hreg
  change ((d.ψ : MorseModel (m + 1) → ℝ × MorseModel m) (levelSetReindex d.e y.1)).2 =
    levelSetSplitFst m (levelSetReindex d.e y.1)
  rw [d.hψ]
  rfl

theorem levelSetChart_symm_value' {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0)
    {z : MorseModel m} (hz : z ∈ (levelSetChart g a x hg hreg).target) :
    (levelSetChart g a x hg hreg).symm z =
      (⟨levelSetChartInvValueRaw g a x hg hreg z, by
        let d := levelSetChartData.mk g a x hg hreg
        change g (levelSetReindex d.e (d.ψ.symm (a, z))) = a
        exact levelSetChart_invFun_mem g d.e d.ψ d.hψ hz⟩ : LevelSetSpace g a) := by
  classical
  let d := levelSetChartData.mk g a x hg hreg
  change (if h : (a, z) ∈ d.ψ.target then
        (⟨levelSetReindex d.e (d.ψ.symm (a, z)),
          levelSetChart_invFun_mem g d.e d.ψ d.hψ h⟩ : LevelSetSpace g a)
      else ⟨x.1, x.2⟩) = (⟨levelSetReindex d.e (d.ψ.symm (a, z)),
        levelSetChart_invFun_mem g d.e d.ψ d.hψ hz⟩ : LevelSetSpace g a)
  rw [dif_pos (show (a, z) ∈ d.ψ.target from hz)]

theorem isOpen_levelSetChartDomain {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    IsOpen (levelSetChartDomain g a x hg hreg) := by
  classical
  let d := levelSetChartData.mk g a x hg hreg
  have hcont : Continuous (fun z : MorseModel m => (a, z)) := by fun_prop
  change IsOpen {z : MorseModel m | (a, z) ∈ d.ψ.target}
  exact d.ψ.open_target.preimage hcont

theorem contDiff_levelSetChartValue {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (levelSetChartValue g a x hg hreg) := by
  classical
  let d := levelSetChartData.mk g a x hg hreg
  have hsplitFst : ContDiff ℝ (⊤ : ℕ∞) (levelSetSplitFst m) :=
    (levelSetSplitFst m).contDiff
  have hreindex : ContDiff ℝ (⊤ : ℕ∞) (levelSetReindex d.e) :=
    (levelSetReindex d.e).toContinuousLinearEquiv.contDiff
  change ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
    levelSetSplitFst m (levelSetReindex d.e y))
  fun_prop

theorem contDiffOn_levelSetChartInvValueRaw {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : LevelSetSpace g a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (levelSetChartInvValueRaw g a x hg hreg)
      (levelSetChartDomain g a x hg hreg) := by
  classical
  rw [IsOpen.contDiffOn_iff (isOpen_levelSetChartDomain g a x hg hreg)]
  intro z hz
  let d := levelSetChartData.mk g a x hg hreg
  let e : Fin (m + 1) ≃ Fin (m + 1) := d.e
  let ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d.ψ
  have hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e := d.hψ
  let w : MorseModel (m + 1) := ψ.symm (a, z)
  have hz' : (a, z) ∈ ψ.target := hz
  have hwsrc : w ∈ ψ.source := ψ.map_target hz'
  have hc₁' : (fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis ≠ 0 := by
    rw [d.hψsource] at hwsrc
    exact hwsrc.2
  have hpair : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : MorseModel m => (a, z)) z := by fun_prop
  have hsymm : ContDiffAt ℝ (⊤ : ℕ∞)
      (ψ.symm : (ℝ × MorseModel m) → MorseModel (m + 1)) (a, z) := by
    refine OpenPartialHomeomorph.contDiffAt_symm ψ
      (f₀' := levelSetChartDerivEquiv g e w hc₁') ?_ ?_ ?_
    · exact hz'
    · rw [hψ]
      exact hasFDerivAt_levelSetChartMap g e w hg.contDiffAt hc₁'
    · rw [hψ]
      exact contDiffAt_levelSetChartMap g e w hg.contDiffAt
  have h₁ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel m => ψ.symm (a, z)) z := hsymm.comp z hpair
  have hlin : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun v : MorseModel (m + 1) => levelSetReindex e v) (ψ.symm (a, z)) :=
    ((levelSetReindex e).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
  exact (by
    change ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel m => levelSetReindex e (ψ.symm (a, z))) z
    exact hlin.comp z h₁)



theorem levelSetChart_transition_contDiffAt {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {x₁ x₂ : LevelSetSpace g a}
    (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ g x₂.1 ≠ 0) {z : MorseModel m}
    (hz : z ∈ ((levelSetChart g a x₁ hg hr₁).symm ≫ₕ (levelSetChart g a x₂ hg hr₂)).source) :
    ContDiffAt ℝ (⊤ : ℕ∞) ((levelSetChart g a x₁ hg hr₁).symm ≫ₕ
      (levelSetChart g a x₂ hg hr₂)) z := by
  classical
  let c₁ : OpenPartialHomeomorph (LevelSetSpace g a) (MorseModel m) := levelSetChart g a x₁ hg hr₁
  let c₂ : OpenPartialHomeomorph (LevelSetSpace g a) (MorseModel m) := levelSetChart g a x₂ hg hr₂
  let d₁ := levelSetChartData.mk g a x₁ hg hr₁
  let d₂ := levelSetChartData.mk g a x₂ hg hr₂
  let e₁ : Fin (m + 1) ≃ Fin (m + 1) := d₁.e
  let e₂ : Fin (m + 1) ≃ Fin (m + 1) := d₂.e
  let ψ₁ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₁.ψ
  let ψ₂ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₂.ψ
  have hψ₁ : (ψ₁ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e₁ := d₁.hψ
  have hψ₂ : (ψ₂ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e₂ := d₂.hψ
  have hz1 : z ∈ c₁.target := by
    rw [OpenPartialHomeomorph.trans_source] at hz
    exact hz.1
  have haz : (a, z) ∈ ψ₁.target := by
    change (a, z) ∈ ψ₁.target
    exact hz1
  let w₁ : MorseModel (m + 1) := ψ₁.symm (a, z)
  have hw₁src : w₁ ∈ ψ₁.source := ψ₁.map_target haz
  have hc₁' : (fderiv ℝ (fun v => g (levelSetReindex e₁ v)) w₁) levelSetLastBasis ≠ 0 := by
    rw [d₁.hψsource] at hw₁src
    exact hw₁src.2
  let smooth : MorseModel m → MorseModel m := fun z' =>
    (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z'))))).2
  have hsmooth : ContDiffAt ℝ (⊤ : ℕ∞) smooth z := by
    change ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z' : MorseModel m => (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z'))))).2) z
    have hpair : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' : MorseModel m => (a, z')) z := by fun_prop
    have hsymm₁ : ContDiffAt ℝ (⊤ : ℕ∞)
        (ψ₁.symm : (ℝ × MorseModel m) → MorseModel (m + 1)) (a, z) := by
      refine OpenPartialHomeomorph.contDiffAt_symm ψ₁
        (f₀' := levelSetChartDerivEquiv g e₁ w₁ hc₁') haz ?_ ?_
      · rw [hψ₁]
        exact hasFDerivAt_levelSetChartMap g e₁ w₁ hg.contDiffAt hc₁'
      · rw [hψ₁]
        exact contDiffAt_levelSetChartMap g e₁ w₁ hg.contDiffAt
    have h₁ : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' : MorseModel m => ψ₁.symm (a, z')) z :=
      hsymm₁.comp z hpair
    have hlin₁ : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun v : MorseModel (m + 1) => levelSetReindex e₁ v) (ψ₁.symm (a, z)) :=
      ((levelSetReindex e₁).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
    have h₂ : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' : MorseModel m => levelSetReindex e₁ (ψ₁.symm (a, z'))) z :=
      hlin₁.comp z h₁
    have hlin₂ : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun v : MorseModel (m + 1) => levelSetReindex e₂ v)
        (levelSetReindex e₁ (ψ₁.symm (a, z))) :=
      ((levelSetReindex e₂).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
    have h₃ : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z' : MorseModel m => levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z')))) z :=
      hlin₂.comp z h₂
    have hψ₂at : ContDiffAt ℝ (⊤ : ℕ∞) (ψ₂ : MorseModel (m + 1) → ℝ × MorseModel m)
        (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z)))) := by
      rw [hψ₂]
      exact contDiffAt_levelSetChartMap g e₂ _ hg.contDiffAt
    have h₄ : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z' : MorseModel m => ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z'))))) z :=
      hψ₂at.comp z h₃
    have hsnd : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × MorseModel m => p.2)
        (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z))))) := by fun_prop
    exact hsnd.comp z h₄
  have hagree : (c₁.symm ≫ₕ c₂ : MorseModel m → MorseModel m) =ᶠ[𝓝 z] smooth := by
    have hzsrc : ∀ᶠ z' in 𝓝 z, z' ∈ (c₁.symm ≫ₕ c₂).source := by
      exact (isOpen_iff_mem_nhds.mp (c₁.symm ≫ₕ c₂).open_source z hz)
    filter_upwards [hzsrc] with z' hz'
    rw [OpenPartialHomeomorph.trans_apply]
    have hz'1 : z' ∈ c₁.target := by
      rw [OpenPartialHomeomorph.trans_source] at hz'
      exact hz'.1
    have hsymm' : c₁.symm z' =
        (⟨levelSetReindex e₁ (ψ₁.symm (a, z')), levelSetChart_invFun_mem g e₁ ψ₁ hψ₁
          (show (a, z') ∈ ψ₁.target from hz'1)⟩ : LevelSetSpace g a) := by
      change (if h : (a, z') ∈ ψ₁.target then
          (⟨levelSetReindex e₁ (ψ₁.symm (a, z')), levelSetChart_invFun_mem g e₁ ψ₁ hψ₁ h⟩ :
            LevelSetSpace g a)
        else ⟨x₁.1, x₁.2⟩) = (⟨levelSetReindex e₁ (ψ₁.symm (a, z')),
          levelSetChart_invFun_mem g e₁ ψ₁ hψ₁ (show (a, z') ∈ ψ₁.target from hz'1)⟩ :
            LevelSetSpace g a)
      rw [dif_pos (show (a, z') ∈ ψ₁.target from hz'1)]
    rw [hsymm']
    change (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (a, z'))))).2 = smooth z'
    rfl
  exact hsmooth.congr_of_eventuallyEq hagree

theorem levelSetChart_transition_contDiffOn {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {x₁ x₂ : LevelSetSpace g a}
    (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ g x₂.1 ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) ((levelSetChart g a x₁ hg hr₁).symm ≫ₕ
        (levelSetChart g a x₂ hg hr₂))
      ((levelSetChart g a x₁ hg hr₁).symm ≫ₕ (levelSetChart g a x₂ hg hr₂)).source := by
  rw [IsOpen.contDiffOn_iff ((levelSetChart g a x₁ hg hr₁).symm ≫ₕ
      (levelSetChart g a x₂ hg hr₂)).open_source]
  intro z hz
  exact levelSetChart_transition_contDiffAt g a hg hr₁ hr₂ hz




@[reducible]
noncomputable def levelSetChartedSpace {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0) :
    ChartedSpace (MorseModel m) (LevelSetSpace g a) where
  atlas := Set.range (fun x : LevelSetSpace g a => levelSetChart g a x hg (hreg x.1 x.2))
  chartAt := fun x => levelSetChart g a x hg (hreg x.1 x.2)
  mem_chart_source := fun x => mem_levelSetChart_source g a x hg (hreg x.1 x.2)
  chart_mem_atlas := fun x => ⟨x, rfl⟩

theorem levelSetHasGroupoid {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0) :
    @HasGroupoid (MorseModel m) _ (LevelSetSpace g a) _ (levelSetChartedSpace g a hg hreg)
      (contDiffGroupoid (⊤ : ℕ∞) (𝓘(ℝ, MorseModel m))) := by
  letI := levelSetChartedSpace g a hg hreg
  refine hasGroupoid_of_pregroupoid (contDiffPregroupoid (⊤ : ℕ∞) (𝓘(ℝ, MorseModel m))) ?_
  intro e e' he he'
  rcases he with ⟨x₁, rfl⟩
  rcases he' with ⟨x₂, rfl⟩
  change ContDiffOn ℝ (⊤ : ℕ∞) (𝓘(ℝ, MorseModel m) ∘
      ((levelSetChart g a x₁ hg (hreg x₁.1 x₁.2)).symm ≫ₕ
        (levelSetChart g a x₂ hg (hreg x₂.1 x₂.2)) : MorseModel m → MorseModel m) ∘
      (𝓘(ℝ, MorseModel m)).symm)
      ((𝓘(ℝ, MorseModel m)).symm ⁻¹'
        ((levelSetChart g a x₁ hg (hreg x₁.1 x₁.2)).symm ≫ₕ
          (levelSetChart g a x₂ hg (hreg x₂.1 x₂.2))).source ∩
        Set.range (𝓘(ℝ, MorseModel m)))
  have hfun : 𝓘(ℝ, MorseModel m) ∘
        ((levelSetChart g a x₁ hg (hreg x₁.1 x₁.2)).symm ≫ₕ
          (levelSetChart g a x₂ hg (hreg x₂.1 x₂.2)) : MorseModel m → MorseModel m) ∘
        (𝓘(ℝ, MorseModel m)).symm =
      ((levelSetChart g a x₁ hg (hreg x₁.1 x₁.2)).symm ≫ₕ
        (levelSetChart g a x₂ hg (hreg x₂.1 x₂.2)) : MorseModel m → MorseModel m) := by
    ext x
    simp [modelWithCornersSelf, ModelWithCorners.ofTargetUniv]
  have hdom : (𝓘(ℝ, MorseModel m)).symm ⁻¹'
        ((levelSetChart g a x₁ hg (hreg x₁.1 x₁.2)).symm ≫ₕ
          (levelSetChart g a x₂ hg (hreg x₂.1 x₂.2))).source ∩
        Set.range (𝓘(ℝ, MorseModel m)) =
      ((levelSetChart g a x₁ hg (hreg x₁.1 x₁.2)).symm ≫ₕ
        (levelSetChart g a x₂ hg (hreg x₂.1 x₂.2))).source := by
    ext x
    simp [modelWithCornersSelf, ModelWithCorners.ofTargetUniv]
  rw [hfun, hdom]
  exact levelSetChart_transition_contDiffOn g a hg (hreg x₁.1 x₁.2) (hreg x₂.1 x₂.2)

theorem levelSetIsManifold {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0) :
    @IsManifold ℝ _ (MorseModel m) _ _ (MorseModel m) _ (𝓘(ℝ, MorseModel m))
      (⊤ : ℕ∞) (LevelSetSpace g a) _ (levelSetChartedSpace g a hg hreg) := by
  letI := levelSetChartedSpace g a hg hreg
  exact { toHasGroupoid := levelSetHasGroupoid g a hg hreg }
end

abbrev MorseHalfSpace (m : ℕ) : Type := {x : MorseModel (m + 1) // 0 ≤ x (Fin.last m)}

theorem convex_morseHalfSpace (m : ℕ) :
    Convex ℝ ({x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)} : Set (MorseModel (m + 1))) := by
  exact convex_halfSpace_ge (f := fun x : MorseModel (m + 1) => x (Fin.last m)) (by
    refine ⟨?_, ?_⟩
    · intro x y
      rfl
    · intro c x
      rfl) (0 : ℝ)

theorem isOpen_morseHalfSpace_interior (m : ℕ) :
    IsOpen ({x : MorseModel (m + 1) | 0 < x (Fin.last m)}) := by
  exact isOpen_Ioi.preimage (continuous_apply (Fin.last m))

theorem interior_morseHalfSpace_nonempty (m : ℕ) :
    (interior ({x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)} : Set (MorseModel (m + 1)))).Nonempty := by
  refine ⟨fun _ : Fin (m + 1) => (1 : ℝ), ?_⟩
  have h₁ : (fun _ : Fin (m + 1) => (1 : ℝ)) ∈ interior {x : MorseModel (m + 1) | 0 < x (Fin.last m)} := by
    rw [(isOpen_morseHalfSpace_interior m).interior_eq]
    simp
  exact interior_mono (by
    intro x hx
    change 0 < x (Fin.last m) at hx
    exact le_of_lt hx) h₁

noncomputable def morseHalfSpaceClamp {m : ℕ} (x : MorseModel (m + 1)) : MorseModel (m + 1) :=
  HAdd.hAdd x (HSMul.hSMul (max (-(x (Fin.last m))) 0) levelSetLastBasis)

theorem morseHalfSpaceClamp_last (m : ℕ) (x : MorseModel (m + 1)) :
    morseHalfSpaceClamp x (Fin.last m) = max (x (Fin.last m)) 0 := by
  by_cases h : 0 ≤ x (Fin.last m)
  · have h1 : max (-(x (Fin.last m))) 0 = 0 := max_eq_right (by linarith)
    rw [morseHalfSpaceClamp, h1]
    rw [max_eq_left h]
    simp
  · have h1 : max (-(x (Fin.last m))) 0 = -(x (Fin.last m)) := max_eq_left (by linarith)
    rw [morseHalfSpaceClamp, h1]
    rw [max_eq_right (by linarith)]
    simp [levelSetLastBasis]

theorem morseHalfSpaceClamp_of_mem (m : ℕ) {x : MorseModel (m + 1)} (hx : 0 ≤ x (Fin.last m)) :
    morseHalfSpaceClamp x = x := by
  ext i
  by_cases hi : i = Fin.last m
  · subst i
    rw [morseHalfSpaceClamp_last]
    exact max_eq_left hx
  · have h0 : (HSMul.hSMul (max (-(x (Fin.last m))) 0) levelSetLastBasis) i = 0 := by
      simp [levelSetLastBasis, hi, Pi.smul_apply, smul_eq_mul]
    simp [morseHalfSpaceClamp, h0]

noncomputable def morseModelWithCornersHalfSpace (m : ℕ) :
    ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
  ModelWithCorners.ofConvexRange
    { toFun := fun x : MorseHalfSpace m => (x : MorseModel (m + 1))
      invFun := fun x : MorseModel (m + 1) =>
        ⟨morseHalfSpaceClamp x, by
          rw [morseHalfSpaceClamp_last]
          exact le_max_right _ _⟩
      source := Set.univ
      target := {x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)}
      map_source' := by intro x hx; exact x.2
      map_target' := by intro x hx; trivial
      left_inv' := by
        intro x hx
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m x.2
      right_inv' := by
        intro x hx
        exact morseHalfSpaceClamp_of_mem m hx }
    rfl (convex_morseHalfSpace m)
    (by fun_prop)
    (by
      have hcont : Continuous (morseHalfSpaceClamp (m := m)) := by
        change Continuous (fun x : MorseModel (m + 1) =>
          HAdd.hAdd x (HSMul.hSMul (max (-(x (Fin.last m))) 0) levelSetLastBasis))
        fun_prop
      exact Continuous.subtype_mk hcont (fun x => by
        rw [morseHalfSpaceClamp_last]
        exact le_max_right _ _))
    (interior_morseHalfSpace_nonempty m)

theorem sublevelBoundaryChart_invFun_mem {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (a : ℝ)
    (ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m))
    (hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e)
    {z : MorseHalfSpace m} (hz : (a - (z : MorseModel (m + 1)) (Fin.last m),
      levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target) :
    g (levelSetReindex e (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
      levelSetSplitFst m (z : MorseModel (m + 1))))) ≤ a := by
  have hval : (ψ (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
      levelSetSplitFst m (z : MorseModel (m + 1))))).1 =
      a - (z : MorseModel (m + 1)) (Fin.last m) := by
    rw [ψ.right_inv hz]
  have h1 : (ψ (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
      levelSetSplitFst m (z : MorseModel (m + 1))))).1 =
      g (levelSetReindex e (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
        levelSetSplitFst m (z : MorseModel (m + 1))))) := by
    rw [hψ]
    rfl
  rw [← h1]
  rw [hval]
  linarith [z.2]

noncomputable def sublevelBoundaryChart {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) := by
  classical
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  let ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d.ψ
  have hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g d.e := d.hψ
  let inv : MorseHalfSpace m → SublevelSpace g a := fun z =>
    if hz : (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target then
      ⟨levelSetReindex d.e (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
          levelSetSplitFst m (z : MorseModel (m + 1)))),
        sublevelBoundaryChart_invFun_mem g d.e a ψ hψ hz⟩
    else ⟨x.1, x.2⟩
  let toFunVal : SublevelSpace g a → MorseModel (m + 1) := fun y =>
    levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
        a - (ψ (levelSetReindex d.e y.1)).1)
  let toFun' : SublevelSpace g a → MorseHalfSpace m := fun y =>
    ⟨toFunVal y, by
      change 0 ≤ (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
          a - (ψ (levelSetReindex d.e y.1)).1)) (Fin.last m)
      have h1 : (ψ (levelSetReindex d.e y.1)).1 =
          g (levelSetReindex d.e (levelSetReindex d.e y.1)) := by
        rw [hψ]
        rfl
      rw [h1]
      rw [d.he, levelSetReindex_swap_swap]
      simp [levelSetSplit]
      linarith [show g y.1 ≤ a from y.2]⟩
  exact
    { toPartialEquiv :=
        { toFun := toFun'
          invFun := inv
          source := {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source}
          target := {z : MorseHalfSpace m |
            (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target}
          map_source' := by
            intro y hy
            change (a - (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                a - (ψ (levelSetReindex d.e y.1)).1)) (Fin.last m),
              levelSetSplitFst m (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                a - (ψ (levelSetReindex d.e y.1)).1))) ∈ ψ.target
            have hlast : (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                a - (ψ (levelSetReindex d.e y.1)).1)) (Fin.last m) =
                a - (ψ (levelSetReindex d.e y.1)).1 := by
              simp [levelSetSplit]
            have hp : levelSetSplitFst m (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                a - (ψ (levelSetReindex d.e y.1)).1)) =
                levelSetSplitFst m (levelSetReindex d.e y.1) := by
              rw [levelSetSplitFst_split]
            rw [hlast, hp]
            have hpair : (a - (a - (ψ (levelSetReindex d.e y.1)).1),
                levelSetSplitFst m (levelSetReindex d.e y.1)) = ψ (levelSetReindex d.e y.1) := by
              apply Prod.ext
              · ring
              · have hpp : levelSetSplitFst m (levelSetReindex d.e y.1) =
                    (ψ (levelSetReindex d.e y.1)).2 := by
                  rw [hψ]
                  rfl
                rw [hpp]
            rw [hpair]
            exact ψ.map_source hy
          map_target' := by
            intro z hz
            change levelSetReindex d.e ((inv z).1) ∈ ψ.source
            change levelSetReindex d.e ((if h : (a - (z : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target then
                  (⟨levelSetReindex d.e (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
                      levelSetSplitFst m (z : MorseModel (m + 1)))),
                    sublevelBoundaryChart_invFun_mem g d.e a ψ hψ h⟩ : SublevelSpace g a)
                else ⟨x.1, x.2⟩).1) ∈ ψ.source
            simp only [dif_pos (show (a - (z : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target from hz)]
            rw [d.he, levelSetReindex_swap_swap]
            exact ψ.map_target hz
          left_inv' := by
            intro y hy
            have h1 : (ψ (levelSetReindex d.e y.1)).1 =
                g (levelSetReindex d.e (levelSetReindex d.e y.1)) := by
              rw [hψ]
              rfl
            have hlast : (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                a - (ψ (levelSetReindex d.e y.1)).1)) (Fin.last m) =
                a - (ψ (levelSetReindex d.e y.1)).1 := by
              simp [levelSetSplit]
            have hp : levelSetSplitFst m (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                a - (ψ (levelSetReindex d.e y.1)).1)) =
                levelSetSplitFst m (levelSetReindex d.e y.1) := by
              rw [levelSetSplitFst_split]
            have hpair : (a - (a - (ψ (levelSetReindex d.e y.1)).1),
                levelSetSplitFst m (levelSetReindex d.e y.1)) = ψ (levelSetReindex d.e y.1) := by
              apply Prod.ext
              · ring
              · have hpp : levelSetSplitFst m (levelSetReindex d.e y.1) =
                    (ψ (levelSetReindex d.e y.1)).2 := by
                  rw [hψ]
                  rfl
                rw [hpp]
            have hz : (a - toFunVal y (Fin.last m), levelSetSplitFst m (toFunVal y)) ∈ ψ.target := by
              change (a - (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                  a - (ψ (levelSetReindex d.e y.1)).1)) (Fin.last m),
                levelSetSplitFst m (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                  a - (ψ (levelSetReindex d.e y.1)).1))) ∈ ψ.target
              rw [hlast, hp, hpair]
              exact ψ.map_source hy
            change inv (toFun' y) = y
            change (if h : (a - (toFun' y : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m ((toFun' y : MorseModel (m + 1)))) ∈ ψ.target then
                  ⟨levelSetReindex d.e (ψ.symm (a - (toFun' y : MorseModel (m + 1)) (Fin.last m),
                      levelSetSplitFst m ((toFun' y : MorseModel (m + 1))))),
                    sublevelBoundaryChart_invFun_mem g d.e a ψ hψ h⟩
                else ⟨x.1, x.2⟩) = y
            rw [dif_pos (show (a - (toFun' y : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m ((toFun' y : MorseModel (m + 1)))) ∈ ψ.target from by
                change (a - toFunVal y (Fin.last m), levelSetSplitFst m (toFunVal y)) ∈ ψ.target
                exact hz)]
            apply Subtype.ext
            change levelSetReindex d.e (ψ.symm (a - (toFun' y : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m ((toFun' y : MorseModel (m + 1))))) = y.1
            change levelSetReindex d.e (ψ.symm (a - toFunVal y (Fin.last m),
                levelSetSplitFst m (toFunVal y))) = y.1
            change levelSetReindex d.e (ψ.symm (a - (levelSetSplit m (levelSetSplitFst m
                (levelSetReindex d.e y.1), a - (ψ (levelSetReindex d.e y.1)).1)) (Fin.last m),
                levelSetSplitFst m (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                  a - (ψ (levelSetReindex d.e y.1)).1)))) = y.1
            rw [hlast, hp]
            rw [hpair]
            have hleft : ψ.symm (ψ (levelSetReindex d.e y.1)) = levelSetReindex d.e y.1 :=
              ψ.left_inv hy
            rw [hleft]
            rw [d.he, levelSetReindex_swap_swap]
          right_inv' := by
            intro z hz
            change (toFun' (if h : (a - (z : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target then
                  ⟨levelSetReindex d.e (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
                      levelSetSplitFst m (z : MorseModel (m + 1)))),
                    sublevelBoundaryChart_invFun_mem g d.e a ψ hψ h⟩
                else ⟨x.1, x.2⟩)) = z
            rw [dif_pos (show (a - (z : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target from hz)]
            apply Subtype.ext
            change toFunVal ⟨levelSetReindex d.e (ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m (z : MorseModel (m + 1)))), _⟩ = (z : MorseModel (m + 1))
            let t : ℝ := a - (z : MorseModel (m + 1)) (Fin.last m)
            let y' : MorseModel m := levelSetSplitFst m (z : MorseModel (m + 1))
            let w : MorseModel (m + 1) := ψ.symm (t, y')
            change levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e (levelSetReindex d.e w)),
                a - (ψ (levelSetReindex d.e (levelSetReindex d.e w))).1) = (z : MorseModel (m + 1))
            have hpair : ψ w = (t, y') := by
              simpa [t, y', w] using ψ.right_inv hz
            have hG : (ψ (levelSetReindex d.e (levelSetReindex d.e w))).1 = t := by
              rw [hψ]
              simp only [levelSetChartMap]
              rw [d.he, levelSetReindex_swap_swap, ← d.he]
              have h1 : (ψ w).1 = g (levelSetReindex d.e w) := by
                rw [hψ]
                rfl
              rw [← h1]
              exact congrArg Prod.fst hpair
            have hp : levelSetSplitFst m (levelSetReindex d.e (levelSetReindex d.e w)) = y' := by
              rw [d.he, levelSetReindex_swap_swap]
              have h1 : levelSetSplitFst m w = (ψ w).2 := by
                rw [hψ]
                rfl
              rw [h1]
              exact congrArg Prod.snd hpair
            rw [hG, hp]
            change levelSetSplit m (y', a - t) = (z : MorseModel (m + 1))
            have ht : a - t = (z : MorseModel (m + 1)) (Fin.last m) := by
              dsimp [t]
              ring
            rw [ht]
            change levelSetSplit m ((levelSetSplitFst m (z : MorseModel (m + 1))),
                (z : MorseModel (m + 1)) (Fin.last m)) = (z : MorseModel (m + 1))
            change levelSetSplit m ((levelSetSplit m).symm (z : MorseModel (m + 1))) =
                (z : MorseModel (m + 1))
            exact (levelSetSplit m).apply_symm_apply (z : MorseModel (m + 1)) }
      open_source := by
        have hcont : Continuous (fun y : SublevelSpace g a => levelSetReindex d.e y.1) :=
          ((levelSetReindex d.e).toContinuousLinearEquiv :
            MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).continuous.comp continuous_subtype_val
        exact ψ.open_source.preimage hcont
      open_target := by
        have hcont1 : Continuous (fun z : MorseHalfSpace m =>
            a - (z : MorseModel (m + 1)) (Fin.last m)) :=
          continuous_const.sub ((continuous_apply (Fin.last m)).comp continuous_subtype_val)
        have hcont2 : Continuous (fun z : MorseHalfSpace m =>
            levelSetSplitFst m (z : MorseModel (m + 1))) :=
          (levelSetSplitFst m).continuous.comp continuous_subtype_val
        have hcont : Continuous (fun z : MorseHalfSpace m =>
            (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1)))) :=
          hcont1.prodMk hcont2
        exact ψ.open_target.preimage hcont
      continuousOn_toFun := by
        have hf : Continuous (fun y : SublevelSpace g a => levelSetReindex d.e y.1) :=
          ((levelSetReindex d.e).toContinuousLinearEquiv :
            MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).continuous.comp continuous_subtype_val
        have hcomp : ContinuousOn (fun y : SublevelSpace g a => ψ (levelSetReindex d.e y.1))
            {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} :=
          ψ.continuousOn.comp hf.continuousOn (by intro y hy; exact hy)
        have hc1 : ContinuousOn (fun y : SublevelSpace g a =>
            levelSetSplitFst m (levelSetReindex d.e y.1))
            {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} :=
          (levelSetSplitFst m).continuous.comp_continuousOn hf.continuousOn
        have hc2 : ContinuousOn (fun y : SublevelSpace g a =>
            a - (ψ (levelSetReindex d.e y.1)).1)
            {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} := by
          have hc2' : ContinuousOn (fun y : SublevelSpace g a =>
              (ψ (levelSetReindex d.e y.1)).1)
              {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} :=
            continuous_fst.comp_continuousOn hcomp
          simpa [sub_eq_add_neg] using
            (continuous_const.sub continuous_id).comp_continuousOn hc2'
        have hpair : ContinuousOn (fun y : SublevelSpace g a =>
            (levelSetSplitFst m (levelSetReindex d.e y.1),
              a - (ψ (levelSetReindex d.e y.1)).1))
            {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} :=
          hc1.prodMk hc2
        have hunder : ContinuousOn (fun y : SublevelSpace g a =>
            levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
              a - (ψ (levelSetReindex d.e y.1)).1))
            {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source} :=
          (by
            have hsplit : Continuous (levelSetSplit m) := (levelSetSplit m).toContinuousLinearEquiv.continuous
            exact hsplit.comp_continuousOn hpair)
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hrest : Continuous (fun x : {y : SublevelSpace g a |
            levelSetReindex d.e y.1 ∈ ψ.source} => toFunVal x.1) := by
          exact continuousOn_iff_continuous_restrict.mp (by
            change ContinuousOn (fun y : SublevelSpace g a =>
                levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y.1),
                  a - (ψ (levelSetReindex d.e y.1)).1))
                {y : SublevelSpace g a | levelSetReindex d.e y.1 ∈ ψ.source}
            exact hunder)
        have hsub : Continuous (fun x : {y : SublevelSpace g a |
            levelSetReindex d.e y.1 ∈ ψ.source} => (⟨toFunVal x.1, (toFun' x.1).2⟩ :
              MorseHalfSpace m)) :=
          Continuous.subtype_mk hrest (fun x => (toFun' x.1).2)
        have hcongr : Continuous (fun x : {y : SublevelSpace g a |
            levelSetReindex d.e y.1 ∈ ψ.source} => toFun' x.1) := by
          refine hsub.congr ?_
          intro x
          exact (Subtype.ext rfl).symm
        exact hcongr
      continuousOn_invFun := by
        let s : Set (MorseHalfSpace m) := {z | (a - (z : MorseModel (m + 1)) (Fin.last m),
          levelSetSplitFst m (z : MorseModel (m + 1))) ∈ ψ.target}
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hc : Continuous (fun z : s =>
            (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1)))) := by
          have hc1 : Continuous (fun z : s =>
              a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m)) :=
            continuous_const.sub (((continuous_apply (Fin.last m)).comp continuous_subtype_val).comp continuous_subtype_val)
          have hc2 : Continuous (fun z : s =>
              levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1))) :=
            (levelSetSplitFst m).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
          exact hc1.prodMk hc2
        have hc0 : Continuous (fun z : s => ψ.symm
            (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1)))) := by
          have hc0' : ContinuousOn (fun z : s => ψ.symm
              (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1)))) (Set.univ : Set s) := by
            refine ψ.symm.continuousOn.comp hc.continuousOn ?_
            intro z hz
            exact z.2
          exact continuousOn_univ.mp hc0'
        have hc1 : Continuous (fun z : s =>
            (⟨levelSetReindex d.e (ψ.symm
                (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
                  levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1)))),
              sublevelBoundaryChart_invFun_mem g d.e a ψ hψ
                (show (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
                  levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1))) ∈ ψ.target from z.2)⟩ :
                  SublevelSpace g a)) :=
          Continuous.subtype_mk
            (((levelSetReindex d.e).toContinuousLinearEquiv :
              MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).continuous.comp hc0)
            (fun z : s => sublevelBoundaryChart_invFun_mem g d.e a ψ hψ
              (show (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
                levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1))) ∈ ψ.target from z.2))
        refine hc1.congr ?_
        intro z
        change (⟨levelSetReindex d.e (ψ.symm
            (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1)))),
          sublevelBoundaryChart_invFun_mem g d.e a ψ hψ
            (show (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1))) ∈ ψ.target from z.2)⟩ :
                SublevelSpace g a) =
          (if hz : (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
              levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1))) ∈ ψ.target then
                (⟨levelSetReindex d.e (ψ.symm (a - ((z : MorseHalfSpace m) : MorseModel (m + 1))
                  (Fin.last m), levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1)))),
                  sublevelBoundaryChart_invFun_mem g d.e a ψ hψ hz⟩ : SublevelSpace g a)
              else ⟨x.1, x.2⟩)
        rw [dif_pos (show (a - ((z : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
          levelSetSplitFst m ((z : MorseHalfSpace m) : MorseModel (m + 1))) ∈ ψ.target from z.2)] }


theorem mem_sublevelBoundaryChart_source {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    x ∈ (sublevelBoundaryChart g a x hx hg hreg).source := by
  classical
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  change levelSetReindex d.e x.1 ∈ d.ψ.source
  rw [d.hψsource]
  constructor
  · rw [← d.hu₁]
    exact ContDiffAt.mem_toOpenPartialHomeomorph_source (f := levelSetChartMap g d.e)
      (contDiffAt_levelSetChartMap g d.e d.u₁ (by
        rw [d.hu₁, d.he, levelSetReindex_swap_swap]
        exact hg.contDiffAt))
      (hasFDerivAt_levelSetChartMap g d.e d.u₁ (by
        rw [d.hu₁, d.he, levelSetReindex_swap_swap]
        exact hg.contDiffAt) d.hc)
      (by norm_num)
  · rw [← d.hu₁]
    exact d.hc

theorem sublevelBoundaryChart_extend_last_zero {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    (sublevelBoundaryChart g a x hx hg hreg).extend (morseModelWithCornersHalfSpace m) x
        (Fin.last m) = 0 := by
  classical
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  let ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d.ψ
  have hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g d.e := d.hψ
  rw [OpenPartialHomeomorph.extend_coe]
  change (morseModelWithCornersHalfSpace m) (⟨levelSetSplit m (levelSetSplitFst m
      (levelSetReindex d.e x.1), a - (ψ (levelSetReindex d.e x.1)).1), by
        have h1 : (ψ (levelSetReindex d.e x.1)).1 =
            g (levelSetReindex d.e (levelSetReindex d.e x.1)) := by
          rw [hψ]
          rfl
        rw [h1]
        rw [d.he, levelSetReindex_swap_swap]
        simp [levelSetSplit]
        linarith [show g x.1 ≤ a from x.2]⟩ : MorseHalfSpace m)
      (Fin.last m) = 0
  change (levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e x.1),
      a - (ψ (levelSetReindex d.e x.1)).1)) (Fin.last m) = 0
  have h1 : (ψ (levelSetReindex d.e x.1)).1 =
      g (levelSetReindex d.e (levelSetReindex d.e x.1)) := by
    rw [hψ]
    rfl
  rw [h1]
  rw [d.he, levelSetReindex_swap_swap]
  simp [levelSetSplit]
  linarith


noncomputable def sublevelBoundaryChartUnderlying {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ x₂ : SublevelSpace g a) (hx₁ : g x₁.1 = a) (hx₂ : g x₂.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ g x₂.1 ≠ 0) :
    MorseModel (m + 1) → MorseModel (m + 1) :=
  let d₁ := levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁
  let d₂ := levelSetChartData.mk g a ⟨x₂.1, hx₂⟩ hg hr₂
  let e₁ : Fin (m + 1) ≃ Fin (m + 1) := d₁.e
  let e₂ : Fin (m + 1) ≃ Fin (m + 1) := d₂.e
  let ψ₁ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₁.ψ
  let ψ₂ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₂.ψ
  fun x =>
    let t : ℝ := a - x (Fin.last m)
    let y' : MorseModel m := levelSetSplitFst m x
    let u : MorseModel (m + 1) := ψ₁.symm (t, y')
    let v : MorseModel (m + 1) := levelSetReindex e₂ (levelSetReindex e₁ u)
    levelSetSplit m (levelSetSplitFst m v, a - (ψ₂ v).1)

theorem contDiffAt_sublevelBoundaryChartUnderlying {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ x₂ : SublevelSpace g a) (hx₁ : g x₁.1 = a) (hx₂ : g x₂.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ g x₂.1 ≠ 0)
    {z : MorseModel (m + 1)}
    (hz : (a - z (Fin.last m), levelSetSplitFst m z) ∈
      (levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁).ψ.target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (sublevelBoundaryChartUnderlying g a x₁ x₂ hx₁ hx₂ hg hr₁ hr₂) z := by
  classical
  let d₁ := levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁
  let d₂ := levelSetChartData.mk g a ⟨x₂.1, hx₂⟩ hg hr₂
  let e₁ : Fin (m + 1) ≃ Fin (m + 1) := d₁.e
  let e₂ : Fin (m + 1) ≃ Fin (m + 1) := d₂.e
  let ψ₁ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₁.ψ
  let ψ₂ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₂.ψ
  have hψ₁ : (ψ₁ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e₁ := d₁.hψ
  have hψ₂ : (ψ₂ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e₂ := d₂.hψ
  let t : ℝ := a - z (Fin.last m)
  let y' : MorseModel m := levelSetSplitFst m z
  let w₁ : MorseModel (m + 1) := ψ₁.symm (t, y')
  have hw₁src : w₁ ∈ ψ₁.source := ψ₁.map_target hz
  have hc₁' : (fderiv ℝ (fun v => g (levelSetReindex e₁ v)) w₁) levelSetLastBasis ≠ 0 := by
    rw [d₁.hψsource] at hw₁src
    exact hw₁src.2
  have hpair : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => (a - x (Fin.last m), levelSetSplitFst m x)) z := by
    have hc1 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : MorseModel (m + 1) => a - x (Fin.last m)) z := by
      fun_prop
    have hc2 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : MorseModel (m + 1) => levelSetSplitFst m x) z := by
      fun_prop
    exact hc1.prodMk hc2
  have hsymm₁ : ContDiffAt ℝ (⊤ : ℕ∞)
      (ψ₁.symm : (ℝ × MorseModel m) → MorseModel (m + 1)) (t, y') := by
    refine OpenPartialHomeomorph.contDiffAt_symm ψ₁
      (f₀' := levelSetChartDerivEquiv g e₁ w₁ hc₁') ?_ ?_ ?_
    · change (a - z (Fin.last m), levelSetSplitFst m z) ∈ ψ₁.target
      exact hz
    · rw [hψ₁]
      exact hasFDerivAt_levelSetChartMap g e₁ w₁ hg.contDiffAt hc₁'
    · rw [hψ₁]
      exact contDiffAt_levelSetChartMap g e₁ w₁ hg.contDiffAt
  have h₁ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x)) z :=
    hsymm₁.comp z hpair
  have hlin₁ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun v : MorseModel (m + 1) => levelSetReindex e₁ v) (ψ₁.symm (t, y')) :=
    ((levelSetReindex e₁).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
  have h₂ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => levelSetReindex e₁ (ψ₁.symm (a - x (Fin.last m),
        levelSetSplitFst m x))) z :=
    hlin₁.comp z h₁
  have hlin₂ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun v : MorseModel (m + 1) => levelSetReindex e₂ v) (levelSetReindex e₁ (ψ₁.symm (t, y'))) :=
    ((levelSetReindex e₂).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
  have h₃ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => levelSetReindex e₂ (levelSetReindex e₁
        (ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x)))) z :=
    hlin₂.comp z h₂
  have hψ₂at : ContDiffAt ℝ (⊤ : ℕ∞) (ψ₂ : MorseModel (m + 1) → ℝ × MorseModel m)
      (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y')))) := by
    rw [hψ₂]
    exact contDiffAt_levelSetChartMap g e₂ _ hg.contDiffAt
  have h₄ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => ψ₂ (levelSetReindex e₂ (levelSetReindex e₁
        (ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x))))) z :=
    hψ₂at.comp z h₃
  have hfst : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × MorseModel m => p.1)
      (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y'))))) := by fun_prop
  have h₅ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => Prod.fst (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁
        (ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x)))))) z :=
    hfst.comp z h₄
  have hsub : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => a - Prod.fst (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁
        (ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x)))))) z := by
    have hsub' : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℝ => a - r)
        (Prod.fst (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y')))))) := by fun_prop
    exact hsub'.comp z h₅
  have hpf : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => levelSetSplitFst m (levelSetReindex e₂ (levelSetReindex e₁
        (ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x))))) z := by
    have hpf' : ContDiffAt ℝ (⊤ : ℕ∞) (levelSetSplitFst m)
        (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y')))) :=
      (levelSetSplitFst m).contDiff.contDiffAt
    exact hpf'.comp z h₃
  have hsplit : ContDiffAt ℝ (⊤ : ℕ∞) (levelSetSplit m)
      (levelSetSplitFst m (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y')))),
        a - Prod.fst (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y')))))) :=
    (levelSetSplit m).toContinuousLinearEquiv.contDiff.contDiffAt
  exact (by
    simpa [sublevelBoundaryChartUnderlying] using
      (hsplit.comp z (hpf.prodMk hsub)))


noncomputable def morseHalfSpaceShift {m : ℕ} (c : ℝ) (x : MorseModel (m + 1)) :
    MorseModel (m + 1) :=
  HAdd.hAdd x (HSMul.hSMul c levelSetLastBasis)

theorem morseHalfSpaceShift_last {m : ℕ} (c : ℝ) (x : MorseModel (m + 1)) :
    morseHalfSpaceShift c x (Fin.last m) = x (Fin.last m) + c := by
  simp [morseHalfSpaceShift, levelSetLastBasis, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_comm]

theorem morseHalfSpaceShift_neg {m : ℕ} (c : ℝ) (x : MorseModel (m + 1)) :
    morseHalfSpaceShift (-c) (morseHalfSpaceShift c x) = x := by
  ext i
  simp [morseHalfSpaceShift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem morseHalfSpaceShift_neg' {m : ℕ} (c : ℝ) (x : MorseModel (m + 1)) :
    morseHalfSpaceShift c (morseHalfSpaceShift (-c) x) = x := by
  simpa using morseHalfSpaceShift_neg (-c) x

noncomputable def sublevelInteriorChart {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 < a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) := by
  classical
  have hspec : ∃ ε > 0, Metric.ball x.1 ε ⊆ {y : MorseModel (m + 1) | g y < a} := by
    exact Metric.mem_nhds_iff.mp ((isOpen_Iio.preimage hg.continuous).mem_nhds hx)
  let ρ : ℝ := Classical.choose hspec
  have hρ : 0 < ρ ∧ Metric.ball x.1 ρ ⊆ {y : MorseModel (m + 1) | g y < a} :=
    Classical.choose_spec hspec
  let c : ℝ := ρ + ‖x.1‖ + 1
  have hcpos : 0 < c := by
    dsimp [c]
    linarith [hρ.1, norm_nonneg x.1]
  have hnormx : |x.1 (Fin.last m)| ≤ ‖x.1‖ := by
    have hle : ‖x.1 (Fin.last m)‖ ≤ ‖x.1‖ := by
      have h := (pi_norm_le_iff_of_nonempty (ι := Fin (m + 1)) (f := x.1) (r := ‖x.1‖))
      exact h.mp le_rfl (Fin.last m)
    simpa using hle
  have hxlow : -(‖x.1‖) ≤ x.1 (Fin.last m) := (abs_le.mp hnormx).1
  have hxpos : 0 < morseHalfSpaceShift c x.1 (Fin.last m) := by
    rw [morseHalfSpaceShift_last]
    dsimp [c] at hcpos
    linarith [hxlow, hcpos]
  let toFun' : SublevelSpace g a → MorseHalfSpace m := fun y =>
    if hy : dist y.1 x.1 < ρ then
      ⟨morseHalfSpaceShift c y.1, by
        have hnorm : ‖y.1 - x.1‖ < ρ := hy
        have habs : |(y.1 - x.1) (Fin.last m)| < ρ := by
          have hle : ‖(y.1 - x.1) (Fin.last m)‖ ≤ ‖y.1 - x.1‖ := by
            have h := (pi_norm_le_iff_of_nonempty (ι := Fin (m + 1)) (f := y.1 - x.1) (r := ‖y.1 - x.1‖))
            exact h.mp le_rfl (Fin.last m)
          exact lt_of_le_of_lt (by simpa using hle) hnorm
        have hleft : -(ρ) < (y.1 - x.1) (Fin.last m) := (abs_lt.mp habs).1
        have hlast : x.1 (Fin.last m) - ρ < y.1 (Fin.last m) := by
          change -(ρ) < y.1 (Fin.last m) - x.1 (Fin.last m) at hleft
          linarith
        have hpos : 0 < morseHalfSpaceShift c y.1 (Fin.last m) := by
          rw [morseHalfSpaceShift_last]
          dsimp [c]
          linarith [hlast, hxlow]
        exact le_of_lt hpos⟩
    else ⟨morseHalfSpaceShift c x.1, le_of_lt hxpos⟩
  let invFun' : MorseHalfSpace m → SublevelSpace g a := fun z =>
    if hz : dist (morseHalfSpaceShift (-c) (z : MorseModel (m + 1))) x.1 < ρ then
      ⟨morseHalfSpaceShift (-c) (z : MorseModel (m + 1)), by
        have hg' : g (morseHalfSpaceShift (-c) (z : MorseModel (m + 1))) < a := hρ.2 hz
        exact le_of_lt hg'⟩
    else ⟨x.1, by
      change g x.1 ≤ a
      exact le_of_lt hx⟩
  exact
    { toPartialEquiv :=
        { toFun := toFun'
          invFun := invFun'
          source := {y : SublevelSpace g a | dist y.1 x.1 < ρ}
          target := {z : MorseHalfSpace m |
            dist (morseHalfSpaceShift (-c) (z : MorseModel (m + 1))) x.1 < ρ}
          map_source' := by
            intro y hy
            change dist (morseHalfSpaceShift (-c) (toFun' y).1) x.1 < ρ
            have hy' : dist y.1 x.1 < ρ := hy
            simp only [toFun']
            rw [dif_pos hy']
            change dist (morseHalfSpaceShift (-c) (morseHalfSpaceShift c y.1)) x.1 < ρ
            rw [morseHalfSpaceShift_neg]
            exact hy'
          map_target' := by
            intro z hz
            change dist (invFun' z).1 x.1 < ρ
            have hz' : dist (morseHalfSpaceShift (-c) (z : MorseModel (m + 1))) x.1 < ρ := hz
            simp only [invFun']
            rw [dif_pos hz']
            exact hz'
          left_inv' := by
            intro y hy
            have hy' : dist y.1 x.1 < ρ := hy
            apply Subtype.ext
            change (invFun' (toFun' y)).1 = y.1
            simp only [toFun']
            simp only [dif_pos hy']
            have hz' : dist (morseHalfSpaceShift (-c) (morseHalfSpaceShift c y.1)) x.1 < ρ := by
              rw [morseHalfSpaceShift_neg]
              exact hy'
            simp only [invFun']
            simp only [dif_pos hz']
            rw [morseHalfSpaceShift_neg]
          right_inv' := by
            intro z hz
            have hz' : dist (morseHalfSpaceShift (-c) (z : MorseModel (m + 1))) x.1 < ρ := hz
            apply Subtype.ext
            change (toFun' (invFun' z)).1 = (z : MorseModel (m + 1))
            simp only [invFun']
            simp only [dif_pos hz']
            have hy' : dist (morseHalfSpaceShift (-c) (z : MorseModel (m + 1))) x.1 < ρ := hz'
            simp only [toFun']
            simp only [dif_pos hy']
            rw [morseHalfSpaceShift_neg'] }
      open_source := by
        have hcont : Continuous (fun y : SublevelSpace g a => (y.1 : MorseModel (m + 1))) :=
          continuous_subtype_val
        exact Metric.isOpen_ball.preimage hcont
      open_target := by
        have hcont : Continuous (fun z : MorseHalfSpace m =>
            morseHalfSpaceShift (-c) (z : MorseModel (m + 1))) := by
          unfold morseHalfSpaceShift
          fun_prop
        exact Metric.isOpen_ball.preimage hcont
      continuousOn_toFun := by
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hcont : Continuous (fun y : {y : SublevelSpace g a | dist y.1 x.1 < ρ} =>
            morseHalfSpaceShift c (y.1 : MorseModel (m + 1))) := by
          unfold morseHalfSpaceShift
          fun_prop
        have hsub : Continuous (fun y : {y : SublevelSpace g a | dist y.1 x.1 < ρ} =>
            (⟨morseHalfSpaceShift c (y.1 : MorseModel (m + 1)), by
              have h1 : (toFun' y.1).1 = morseHalfSpaceShift c (y.1 : MorseModel (m + 1)) := by
                simp only [toFun', dif_pos (show dist (y.1 : MorseModel (m + 1)) x.1 < ρ from y.2)]
              rw [← h1]
              exact (toFun' y.1).2⟩ : MorseHalfSpace m)) :=
          Continuous.subtype_mk hcont (fun y => by
            have h1 : (toFun' y.1).1 = morseHalfSpaceShift c (y.1 : MorseModel (m + 1)) := by
              simp only [toFun', dif_pos (show dist (y.1 : MorseModel (m + 1)) x.1 < ρ from y.2)]
            rw [← h1]
            exact (toFun' y.1).2)
        refine hsub.congr ?_
        intro y
        simp only [Set.restrict]
        exact Subtype.ext (by
          change morseHalfSpaceShift c (y.1 : MorseModel (m + 1)) = (toFun' y.1).1
          simp only [toFun']
          simp only [dif_pos (show dist (y.1 : MorseModel (m + 1)) x.1 < ρ from y.2)])
      continuousOn_invFun := by
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hcont : Continuous (fun z : {z : MorseHalfSpace m |
            dist (morseHalfSpaceShift (-c) (z : MorseModel (m + 1))) x.1 < ρ} =>
            morseHalfSpaceShift (-c) ((z : MorseHalfSpace m) : MorseModel (m + 1))) := by
          unfold morseHalfSpaceShift
          fun_prop
        have hsub : Continuous (fun z : {z : MorseHalfSpace m |
            dist (morseHalfSpaceShift (-c) (z : MorseModel (m + 1))) x.1 < ρ} =>
            (⟨morseHalfSpaceShift (-c) ((z : MorseHalfSpace m) : MorseModel (m + 1)), by
              have h1 : (invFun' z.1).1 = morseHalfSpaceShift (-c) ((z : MorseHalfSpace m) : MorseModel (m + 1)) := by
                simp only [invFun', dif_pos (show dist (morseHalfSpaceShift (-c)
                  ((z : MorseHalfSpace m) : MorseModel (m + 1))) x.1 < ρ from z.2)]
              rw [← h1]
              exact (invFun' z.1).2⟩ : SublevelSpace g a)) :=
          Continuous.subtype_mk hcont (fun z => by
            have h1 : (invFun' z.1).1 = morseHalfSpaceShift (-c) ((z : MorseHalfSpace m) : MorseModel (m + 1)) := by
              simp only [invFun', dif_pos (show dist (morseHalfSpaceShift (-c)
                ((z : MorseHalfSpace m) : MorseModel (m + 1))) x.1 < ρ from z.2)]
            rw [← h1]
            exact (invFun' z.1).2)
        refine hsub.congr ?_
        intro z
        simp only [Set.restrict]
        exact Subtype.ext (by
          change morseHalfSpaceShift (-c) ((z : MorseHalfSpace m) : MorseModel (m + 1)) =
            (invFun' z.1).1
          simp only [invFun']
          simp only [dif_pos (show dist (morseHalfSpaceShift (-c)
            ((z : MorseHalfSpace m) : MorseModel (m + 1))) x.1 < ρ from z.2)]) }


theorem mem_sublevelInteriorChart_source {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 < a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    x ∈ (sublevelInteriorChart g a x hx hg).source := by
  classical
  have hspec : ∃ ε > 0, Metric.ball x.1 ε ⊆ {y : MorseModel (m + 1) | g y < a} := by
    exact Metric.mem_nhds_iff.mp ((isOpen_Iio.preimage hg.continuous).mem_nhds hx)
  let ρ : ℝ := Classical.choose hspec
  have hρ : 0 < ρ ∧ Metric.ball x.1 ρ ⊆ {y : MorseModel (m + 1) | g y < a} :=
    Classical.choose_spec hspec
  change dist x.1 x.1 < ρ
  rw [dist_self]
  exact hρ.1


@[reducible]
noncomputable def sublevelChartedSpace {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0) :
    ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) where
  atlas := Set.range (fun x : SublevelSpace g a =>
    if hx : g x.1 = a then sublevelBoundaryChart g a x hx hg (hreg x.1 hx)
    else sublevelInteriorChart g a x (lt_of_le_of_ne (show g x.1 ≤ a from x.2) hx) hg)
  chartAt := fun x => if hx : g x.1 = a then sublevelBoundaryChart g a x hx hg (hreg x.1 hx)
    else sublevelInteriorChart g a x (lt_of_le_of_ne (show g x.1 ≤ a from x.2) hx) hg
  mem_chart_source := by
    intro x
    by_cases hx : g x.1 = a
    · simp only [hx]
      exact mem_sublevelBoundaryChart_source g a x hx hg (hreg x.1 hx)
    · simp only [hx]
      exact mem_sublevelInteriorChart_source g a x
        (lt_of_le_of_ne (show g x.1 ≤ a from x.2) hx) hg
  chart_mem_atlas := fun x => ⟨x, rfl⟩


theorem range_morseModelWithCornersHalfSpace (m : ℕ) :
    Set.range (morseModelWithCornersHalfSpace m) = {x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2
  · intro hx
    refine ⟨⟨x, hx⟩, rfl⟩

noncomputable def morseHalfSpaceModelHomeoRange (m : ℕ) :
    MorseHalfSpace m ≃ₜ Set.range (morseModelWithCornersHalfSpace m) where
  toFun := fun x => ⟨(morseModelWithCornersHalfSpace m) x, Set.mem_range_self x⟩
  invFun := fun y => ⟨y.1, by
    change y.1 ∈ {x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)}
    rw [← range_morseModelWithCornersHalfSpace]
    exact y.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro y
    apply Subtype.ext
    rfl
  continuous_toFun := by
    exact Continuous.subtype_mk (morseModelWithCornersHalfSpace m).continuous (by intro x; exact Set.mem_range_self x)
  continuous_invFun := by
    have hf : Continuous (fun y : Set.range (morseModelWithCornersHalfSpace m) =>
        (y.1 : MorseModel (m + 1))) := continuous_subtype_val
    have hp : ∀ y : Set.range (morseModelWithCornersHalfSpace m), 0 ≤ (y.1) (Fin.last m) := by
      intro y
      change y.1 ∈ {x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)}
      rw [← range_morseModelWithCornersHalfSpace]
      exact y.2
    exact Continuous.subtype_mk hf hp

theorem norm_levelSetLastBasis (m : ℕ) : ‖levelSetLastBasis (m := m)‖ = 1 := by
  apply le_antisymm
  · have hle : ∀ i : Fin (m + 1), ‖levelSetLastBasis (m := m) i‖ ≤ 1 := by
      intro i
      by_cases hi : i = Fin.last m
      · subst i
        simp [levelSetLastBasis]
      · simp [levelSetLastBasis, hi]
    exact (pi_norm_le_iff_of_nonempty (ι := Fin (m + 1)) (f := levelSetLastBasis (m := m))
      (r := (1 : ℝ))).mpr hle
  · have h1 : ‖levelSetLastBasis (m := m) (Fin.last m)‖ ≤ ‖levelSetLastBasis (m := m)‖ := by
      have h := (pi_norm_le_iff_of_nonempty (ι := Fin (m + 1)) (f := levelSetLastBasis (m := m))
        (r := ‖levelSetLastBasis (m := m)‖)).mp le_rfl
      exact h (Fin.last m)
    have h2 : ‖levelSetLastBasis (m := m) (Fin.last m)‖ = 1 := by
      simp [levelSetLastBasis]
    linarith

theorem interior_morseHalfSpace_range (m : ℕ) :
    interior ({x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)} : Set (MorseModel (m + 1))) =
      {x : MorseModel (m + 1) | 0 < x (Fin.last m)} := by
  apply le_antisymm
  · intro x hx
    by_contra h
    have hxle : 0 ≤ x (Fin.last m) := by
      simpa using (interior_subset hx)
    have hx0 : x (Fin.last m) = 0 := le_antisymm (not_lt.mp h) hxle
    have hnh : (interior ({y : MorseModel (m + 1) | 0 ≤ y (Fin.last m)}) : Set _) ∈ 𝓝 x :=
      isOpen_interior.mem_nhds hx
    rcases Metric.mem_nhds_iff.mp hnh with ⟨ε, hε, hball⟩
    let x' : MorseModel (m + 1) := x - (ε / 2) • levelSetLastBasis
    have hx'lt : x' (Fin.last m) < 0 := by
      change (HSub.hSub x (HSMul.hSMul (ε / 2) levelSetLastBasis)) (Fin.last m) < 0
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hx0, levelSetLastBasis]
      have hε2 : 0 < ε / 2 := by positivity
      simp [hε2]
    have hx'ball : x' ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hnorm : ‖x' - x‖ = ε / 2 := by
        change ‖(HSub.hSub x (HSMul.hSMul (ε / 2) levelSetLastBasis)) - x‖ = ε / 2
        have hsub : (HSub.hSub x (HSMul.hSMul (ε / 2) levelSetLastBasis)) - x =
            -(HSMul.hSMul (ε / 2) levelSetLastBasis) := by
          ext i
          simp
        rw [hsub, norm_neg]
        rw [norm_smul]
        rw [norm_levelSetLastBasis]
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity : 0 ≤ ε / 2)]
        ring
      rw [hnorm]
      linarith [hε]
    exact (not_le_of_gt hx'lt) (by simpa using (interior_subset (hball hx'ball)))
  · intro x hx
    have hsub : {y : MorseModel (m + 1) | 0 < y (Fin.last m)} ⊆
        {y : MorseModel (m + 1) | 0 ≤ y (Fin.last m)} := by
      intro y hy
      change 0 < y (Fin.last m) at hy
      exact le_of_lt hy
    exact interior_mono hsub (by
      rw [(isOpen_morseHalfSpace_interior m).interior_eq]
      exact hx)

theorem frontier_morseHalfSpace_range (m : ℕ) :
    frontier (Set.range (morseModelWithCornersHalfSpace m)) =
      {x : MorseModel (m + 1) | x (Fin.last m) = 0} := by
  rw [range_morseModelWithCornersHalfSpace]
  rw [frontier, interior_morseHalfSpace_range]
  have hclosed : IsClosed ({x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)} : Set _) := by
    exact isClosed_Ici.preimage (continuous_apply (Fin.last m))
  have hclosure : closure ({x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)} : Set _) =
      {x : MorseModel (m + 1) | 0 ≤ x (Fin.last m)} := hclosed.closure_eq
  rw [hclosure]
  ext x
  constructor
  · intro hx
    have hxle : 0 ≤ x (Fin.last m) := hx.1
    have hxnot : ¬ 0 < x (Fin.last m) := hx.2
    exact le_antisymm (not_lt.mp hxnot) hxle
  · intro hx
    constructor
    · change 0 ≤ x (Fin.last m)
      rw [hx]
    · change ¬ 0 < x (Fin.last m)
      rw [hx]
      norm_num


theorem sublevelInteriorChart_extend_last_pos {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 < a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    0 < (sublevelInteriorChart g a x hx hg).extend (morseModelWithCornersHalfSpace m) x
        (Fin.last m) := by
  classical
  have hspec : ∃ ε > 0, Metric.ball x.1 ε ⊆ {y : MorseModel (m + 1) | g y < a} := by
    exact Metric.mem_nhds_iff.mp ((isOpen_Iio.preimage hg.continuous).mem_nhds hx)
  let ρ : ℝ := Classical.choose hspec
  have hρ : 0 < ρ ∧ Metric.ball x.1 ρ ⊆ {y : MorseModel (m + 1) | g y < a} :=
    Classical.choose_spec hspec
  let c : ℝ := ρ + ‖x.1‖ + 1
  have htest : ρ = (Classical.choose (Metric.mem_nhds_iff.mp
      ((isOpen_Iio.preimage hg.continuous).mem_nhds hx))) := rfl
  have hsrc : x ∈ (sublevelInteriorChart g a x hx hg).source :=
    mem_sublevelInteriorChart_source g a x hx hg
  have hdist : dist x.1 x.1 < ρ := by
    change dist x.1 x.1 < ρ at hsrc
    exact hsrc
  rw [OpenPartialHomeomorph.extend_coe]
  have hchart : ((sublevelInteriorChart g a x hx hg) x : MorseModel (m + 1)) =
      morseHalfSpaceShift c x.1 := by
    simp only [sublevelInteriorChart]
    change ((if h : dist x.1 x.1 < ρ then
        (⟨morseHalfSpaceShift c x.1, _⟩ : MorseHalfSpace m) else ⟨morseHalfSpaceShift c x.1, _⟩ :
          MorseHalfSpace m) : MorseModel (m + 1)) = morseHalfSpaceShift c x.1
    rw [dif_pos hdist]
  change 0 < ((sublevelInteriorChart g a x hx hg) x : MorseModel (m + 1)) (Fin.last m)
  rw [hchart]
  rw [morseHalfSpaceShift_last]
  have hnormx : |x.1 (Fin.last m)| ≤ ‖x.1‖ := by
    have hle : ‖x.1 (Fin.last m)‖ ≤ ‖x.1‖ := by
      have h := (pi_norm_le_iff_of_nonempty (ι := Fin (m + 1)) (f := x.1) (r := ‖x.1‖))
      exact h.mp le_rfl (Fin.last m)
    simpa using hle
  have hxlow : -(‖x.1‖) ≤ x.1 (Fin.last m) := (abs_le.mp hnormx).1
  dsimp [c]
  linarith [hρ.1, hxlow]


theorem sublevelBoundary_iff_mem_levelSet {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0)
    (x : SublevelSpace g a) :
    @ModelWithCorners.IsBoundaryPoint ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (SublevelSpace g a) _ (sublevelChartedSpace g a hg hreg) x ↔
      g x.1 = a := by
  classical
  letI : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) := sublevelChartedSpace g a hg hreg
  rw [@ModelWithCorners.isBoundaryPoint_iff ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (SublevelSpace g a) _ (sublevelChartedSpace g a hg hreg)]
  rw [frontier_morseHalfSpace_range]
  constructor
  · intro hx
    by_contra hxne
    have hlt : g x.1 < a := lt_of_le_of_ne (show g x.1 ≤ a from x.2) hxne
    have hchart : chartAt (MorseHalfSpace m) x = sublevelInteriorChart g a x hlt hg := by
      change (if h : g x.1 = a then sublevelBoundaryChart g a x h hg (hreg x.1 h)
        else sublevelInteriorChart g a x (lt_of_le_of_ne (show g x.1 ≤ a from x.2) h) hg) =
        sublevelInteriorChart g a x hlt hg
      rw [dif_neg hxne]
    change (chartAt (MorseHalfSpace m) x).extend (morseModelWithCornersHalfSpace m) x ∈
      {w : MorseModel (m + 1) | w (Fin.last m) = 0} at hx
    rw [hchart] at hx
    have hpos := sublevelInteriorChart_extend_last_pos g a x hlt hg
    have hzero : (sublevelInteriorChart g a x hlt hg).extend (morseModelWithCornersHalfSpace m) x
        (Fin.last m) = 0 := by
      change (sublevelInteriorChart g a x hlt hg).extend (morseModelWithCornersHalfSpace m) x ∈
        {w : MorseModel (m + 1) | w (Fin.last m) = 0} at hx
      exact hx
    linarith
  · intro hx
    have hchart : chartAt (MorseHalfSpace m) x = sublevelBoundaryChart g a x hx hg (hreg x.1 hx) := by
      change (if h : g x.1 = a then sublevelBoundaryChart g a x h hg (hreg x.1 h)
        else sublevelInteriorChart g a x (lt_of_le_of_ne (show g x.1 ≤ a from x.2) h) hg) =
        sublevelBoundaryChart g a x hx hg (hreg x.1 hx)
      rw [dif_pos hx]
    change (chartAt (MorseHalfSpace m) x).extend (morseModelWithCornersHalfSpace m) x ∈
      {w : MorseModel (m + 1) | w (Fin.last m) = 0}
    rw [hchart]
    have hzero := sublevelBoundaryChart_extend_last_zero g a x hx hg (hreg x.1 hx)
    change (sublevelBoundaryChart g a x hx hg (hreg x.1 hx)).extend
        (morseModelWithCornersHalfSpace m) x (Fin.last m) = 0
    exact hzero


theorem sublevelBoundaryChart_apply_value {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : fderiv ℝ g x.1 ≠ 0) (y : SublevelSpace g a) :
    ((sublevelBoundaryChart g a x hx hg hreg) y : MorseModel (m + 1)) =
      levelSetSplit m (levelSetSplitFst m (levelSetReindex
        (levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg).e y.1),
        a - ((levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg).ψ
          (levelSetReindex (levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg).e y.1)).1) := by
  rfl

theorem sublevelBoundaryChart_symm_value {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : fderiv ℝ g x.1 ≠ 0) {z : MorseHalfSpace m}
    (hz : z ∈ (sublevelBoundaryChart g a x hx hg hreg).target) :
    (sublevelBoundaryChart g a x hx hg hreg).symm z =
      (⟨levelSetReindex (levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg).e
          ((levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg).ψ.symm
            (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1)))),
        sublevelBoundaryChart_invFun_mem g (levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg).e a
          (levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg).ψ (levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg).hψ
          (show (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1))) ∈
            (levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg).ψ.target from hz)⟩ : SublevelSpace g a) := by
  classical
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  change (if h : (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1))) ∈
        d.ψ.target then
        (⟨levelSetReindex d.e (d.ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
            levelSetSplitFst m (z : MorseModel (m + 1)))),
          sublevelBoundaryChart_invFun_mem g d.e a d.ψ d.hψ h⟩ : SublevelSpace g a)
      else ⟨x.1, x.2⟩) = (⟨levelSetReindex d.e (d.ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
          levelSetSplitFst m (z : MorseModel (m + 1)))),
        sublevelBoundaryChart_invFun_mem g d.e a d.ψ d.hψ
          (show (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1))) ∈
            d.ψ.target from hz)⟩ : SublevelSpace g a)
  rw [dif_pos (show (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1))) ∈
    d.ψ.target from hz)]

noncomputable def sublevelBoundaryChartValue {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : fderiv ℝ g x.1 ≠ 0) : MorseModel (m + 1) → MorseModel (m + 1) :=
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  fun y => levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y),
    a - (d.ψ (levelSetReindex d.e y)).1)

noncomputable def sublevelBoundaryChartInvValueRaw {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : fderiv ℝ g x.1 ≠ 0) : MorseModel (m + 1) → MorseModel (m + 1) :=
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  fun y => levelSetReindex d.e (d.ψ.symm (a - y (Fin.last m), levelSetSplitFst m y))

noncomputable def sublevelBoundaryChartInvValue {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : fderiv ℝ g x.1 ≠ 0) : MorseHalfSpace m → MorseModel (m + 1) :=
  fun z => sublevelBoundaryChartInvValueRaw g a x hx hg hreg (z : MorseModel (m + 1))

noncomputable def sublevelBoundaryChartDomain {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : fderiv ℝ g x.1 ≠ 0) : Set (MorseModel (m + 1)) :=
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  {y : MorseModel (m + 1) | (a - y (Fin.last m), levelSetSplitFst m y) ∈ d.ψ.target}

theorem sublevelBoundaryChart_apply_value' {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : fderiv ℝ g x.1 ≠ 0) (y : SublevelSpace g a) :
    ((sublevelBoundaryChart g a x hx hg hreg) y : MorseModel (m + 1)) =
      sublevelBoundaryChartValue g a x hx hg hreg y.1 := by
  rfl

theorem sublevelBoundaryChart_boundary_eq_levelSetSplit {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (a : ℝ) (x : SublevelSpace g a) (hx : g x.1 = a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : fderiv ℝ g x.1 ≠ 0) (y : SublevelSpace g a) (hy : g y.1 = a) :
    ((sublevelBoundaryChart g a x hx hg hreg) y :
        MorseModel (m + 1)) =
      levelSetSplit m ((levelSetChart g a ⟨x.1, hx⟩ hg hreg ⟨y.1, hy⟩ : MorseModel m), 0) := by
  classical
  rw [sublevelBoundaryChart_apply_value' g a x hx hg hreg y]
  rw [levelSetChart_apply_value' g a ⟨x.1, hx⟩ hg hreg ⟨y.1, hy⟩]
  dsimp [sublevelBoundaryChartValue, levelSetChartValue]
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  have hψ₁ : (d.ψ (levelSetReindex d.e y.1)).1 = g y.1 := by
    rw [d.hψ]
    rw [levelSetChartMap]
    rw [d.he, levelSetReindex_swap_swap]
  rw [hψ₁, hy]
  simp

theorem sublevelBoundaryChart_symm_value' {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : fderiv ℝ g x.1 ≠ 0) {z : MorseHalfSpace m}
    (hz : z ∈ (sublevelBoundaryChart g a x hx hg hreg).target) :
    (sublevelBoundaryChart g a x hx hg hreg).symm z =
      (⟨sublevelBoundaryChartInvValue g a x hx hg hreg z, by
        change g (sublevelBoundaryChartInvValue g a x hx hg hreg z) ≤ a
        change g (sublevelBoundaryChartInvValueRaw g a x hx hg hreg (z : MorseModel (m + 1))) ≤ a
        let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
        change g (levelSetReindex d.e (d.ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
          levelSetSplitFst m (z : MorseModel (m + 1))))) ≤ a
        exact sublevelBoundaryChart_invFun_mem g d.e a d.ψ d.hψ (by
          exact hz)⟩ : SublevelSpace g a) := by
  classical
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  change (if h : (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1))) ∈
        d.ψ.target then
        (⟨levelSetReindex d.e (d.ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
            levelSetSplitFst m (z : MorseModel (m + 1)))),
          sublevelBoundaryChart_invFun_mem g d.e a d.ψ d.hψ h⟩ : SublevelSpace g a)
      else ⟨x.1, x.2⟩) = (⟨sublevelBoundaryChartInvValue g a x hx hg hreg z, by
        change g (sublevelBoundaryChartInvValue g a x hx hg hreg z) ≤ a
        change g (sublevelBoundaryChartInvValueRaw g a x hx hg hreg (z : MorseModel (m + 1))) ≤ a
        change g (levelSetReindex d.e (d.ψ.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
          levelSetSplitFst m (z : MorseModel (m + 1))))) ≤ a
        exact sublevelBoundaryChart_invFun_mem g d.e a d.ψ d.hψ (by
          exact hz)⟩ : SublevelSpace g a)
  rw [dif_pos (show (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1))) ∈
    d.ψ.target from hz)]
  apply Subtype.ext
  rfl

theorem isOpen_sublevelBoundaryChartDomain {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : fderiv ℝ g x.1 ≠ 0) :
    IsOpen (sublevelBoundaryChartDomain g a x hx hg hreg) := by
  classical
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  have hcont : Continuous (fun y : MorseModel (m + 1) =>
      (a - y (Fin.last m), levelSetSplitFst m y)) := by
    fun_prop
  change IsOpen {y : MorseModel (m + 1) | (a - y (Fin.last m), levelSetSplitFst m y) ∈ d.ψ.target}
  exact d.ψ.open_target.preimage hcont

theorem contDiff_sublevelBoundaryChartValue {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : fderiv ℝ g x.1 ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelBoundaryChartValue g a x hx hg hreg) := by
  classical
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  have hψ : ContDiff ℝ (⊤ : ℕ∞)
      (d.ψ : MorseModel (m + 1) → ℝ × MorseModel m) := by
    rw [d.hψ]
    exact contDiff_levelSetChartMap g d.e hg
  have hsplit : ContDiff ℝ (⊤ : ℕ∞) (levelSetSplit m) :=
    (levelSetSplit m).toContinuousLinearEquiv.contDiff
  have hsplitFst : ContDiff ℝ (⊤ : ℕ∞) (levelSetSplitFst m) :=
    (levelSetSplitFst m).contDiff
  have hreindex : ContDiff ℝ (⊤ : ℕ∞) (levelSetReindex d.e) :=
    (levelSetReindex d.e).toContinuousLinearEquiv.contDiff
  change ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
    levelSetSplit m (levelSetSplitFst m (levelSetReindex d.e y),
      a - ((d.ψ : MorseModel (m + 1) → ℝ × MorseModel m) (levelSetReindex d.e y)).1))
  fun_prop

theorem contDiffOn_sublevelBoundaryChartInvValueRaw {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 = a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : fderiv ℝ g x.1 ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sublevelBoundaryChartInvValueRaw g a x hx hg hreg)
      (sublevelBoundaryChartDomain g a x hx hg hreg) := by
  classical
  rw [IsOpen.contDiffOn_iff (isOpen_sublevelBoundaryChartDomain g a x hx hg hreg)]
  intro z hz
  let d := levelSetChartData.mk g a ⟨x.1, hx⟩ hg hreg
  let e : Fin (m + 1) ≃ Fin (m + 1) := d.e
  let ψ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d.ψ
  have hψ : (ψ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e := d.hψ
  let t : ℝ := a - z (Fin.last m)
  let y' : MorseModel m := levelSetSplitFst m z
  let w : MorseModel (m + 1) := ψ.symm (t, y')
  have hz' : (a - z (Fin.last m), levelSetSplitFst m z) ∈ ψ.target := by
    change (a - z (Fin.last m), levelSetSplitFst m z) ∈ d.ψ.target
    exact hz
  have hwsrc : w ∈ ψ.source := ψ.map_target hz'
  have hc₁' : (fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis ≠ 0 := by
    rw [d.hψsource] at hwsrc
    exact hwsrc.2
  have hpair : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => (a - x (Fin.last m), levelSetSplitFst m x)) z := by
    fun_prop
  have hsymm : ContDiffAt ℝ (⊤ : ℕ∞)
      (ψ.symm : (ℝ × MorseModel m) → MorseModel (m + 1)) (t, y') := by
    refine OpenPartialHomeomorph.contDiffAt_symm ψ
      (f₀' := levelSetChartDerivEquiv g e w hc₁') ?_ ?_ ?_
    · change (a - z (Fin.last m), levelSetSplitFst m z) ∈ ψ.target
      exact hz'
    · rw [hψ]
      exact hasFDerivAt_levelSetChartMap g e w hg.contDiffAt hc₁'
    · rw [hψ]
      exact contDiffAt_levelSetChartMap g e w hg.contDiffAt
  have h₁ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => ψ.symm (a - x (Fin.last m), levelSetSplitFst m x)) z :=
    hsymm.comp z hpair
  have hlin : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun v : MorseModel (m + 1) => levelSetReindex e v) (ψ.symm (t, y')) :=
    ((levelSetReindex e).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
  exact (by
    change ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => levelSetReindex e (ψ.symm (a - x (Fin.last m),
        levelSetSplitFst m x))) z
    exact hlin.comp z h₁)

theorem contDiffOn_sublevelBoundaryChartUnderlying {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ x₂ : SublevelSpace g a) (hx₁ : g x₁.1 = a) (hx₂ : g x₂.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ g x₂.1 ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sublevelBoundaryChartUnderlying g a x₁ x₂ hx₁ hx₂ hg hr₁ hr₂)
      {x' : MorseModel (m + 1) | (a - x' (Fin.last m), levelSetSplitFst m x') ∈
        (levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁).ψ.target} := by
  rw [IsOpen.contDiffOn_iff (by
    have hcont : Continuous (fun x' : MorseModel (m + 1) =>
        (a - x' (Fin.last m), levelSetSplitFst m x')) := by
      have hc1 : Continuous (fun x' : MorseModel (m + 1) => a - x' (Fin.last m)) := by fun_prop
      have hc2 : Continuous (fun x' : MorseModel (m + 1) => levelSetSplitFst m x') := by fun_prop
      exact hc1.prodMk hc2
    exact (levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁).ψ.open_target.preimage hcont)]
  intro x' hx'
  exact contDiffAt_sublevelBoundaryChartUnderlying g a x₁ x₂ hx₁ hx₂ hg hr₁ hr₂ hx'

theorem sublevelBoundaryChart_transition_reduce {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ x₂ : SublevelSpace g a) (hx₁ : g x₁.1 = a) (hx₂ : g x₂.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ g x₂.1 ≠ 0)
    {y : MorseModel (m + 1)}
    (hy : y ∈ ((morseModelWithCornersHalfSpace m).symm ⁻¹'
        ((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
          (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)).source ∩
      Set.range (morseModelWithCornersHalfSpace m))) :
    (morseModelWithCornersHalfSpace m) (((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
        (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)) ((morseModelWithCornersHalfSpace m).symm y)) =
      sublevelBoundaryChartUnderlying g a x₁ x₂ hx₁ hx₂ hg hr₁ hr₂ y := by
  classical
  let d₁ := levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁
  let d₂ := levelSetChartData.mk g a ⟨x₂.1, hx₂⟩ hg hr₂
  let e₁ : Fin (m + 1) ≃ Fin (m + 1) := d₁.e
  let e₂ : Fin (m + 1) ≃ Fin (m + 1) := d₂.e
  let ψ₁ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₁.ψ
  let ψ₂ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₂.ψ
  let c₁ : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
    sublevelBoundaryChart g a x₁ hx₁ hg hr₁
  let c₂ : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
    sublevelBoundaryChart g a x₂ hx₂ hg hr₂
  have hy1 : (morseModelWithCornersHalfSpace m).symm y ∈ (c₁.symm ≫ₕ c₂).source := hy.1
  have hy2 : y ∈ Set.range (morseModelWithCornersHalfSpace m) := hy.2
  have hy2' : 0 ≤ y (Fin.last m) := by
    rw [range_morseModelWithCornersHalfSpace] at hy2
    exact hy2
  let z : MorseHalfSpace m := ⟨y, hy2'⟩
  have hclamp : (morseModelWithCornersHalfSpace m).symm y = z := by
    apply Subtype.ext
    exact morseHalfSpaceClamp_of_mem m hy2'
  have hy1z : z ∈ (c₁.symm ≫ₕ c₂).source := by
    rw [hclamp] at hy1
    exact hy1
  have hz1 : z ∈ c₁.target := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.1
  let t : ℝ := a - (z : MorseModel (m + 1)) (Fin.last m)
  let y' : MorseModel m := levelSetSplitFst m (z : MorseModel (m + 1))
  rw [hclamp]
  rw [OpenPartialHomeomorph.trans_apply]
  rw [sublevelBoundaryChart_symm_value g a x₁ hx₁ hg hr₁ hz1]
  change ((sublevelBoundaryChart g a x₂ hx₂ hg hr₂)
      ⟨levelSetReindex e₁ (ψ₁.symm (t, y')), _⟩ : MorseModel (m + 1)) =
    sublevelBoundaryChartUnderlying g a x₁ x₂ hx₁ hx₂ hg hr₁ hr₂ y
  rw [sublevelBoundaryChart_apply_value g a x₂ hx₂ hg hr₂]
  change levelSetSplit m (Prod.mk
      (levelSetSplitFst m (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y')))))
      (a - Prod.fst (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y'))))))) =
    sublevelBoundaryChartUnderlying g a x₁ x₂ hx₁ hx₂ hg hr₁ hr₂ y
  simp [sublevelBoundaryChartUnderlying, z, t, y', e₁, e₂, d₁, d₂, ψ₁, ψ₂]


theorem contDiffOn_sublevelBoundaryChart_transition {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {x₁ x₂ : SublevelSpace g a}
    (hx₁ : g x₁.1 = a) (hx₂ : g x₂.1 = a)
    (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ g x₂.1 ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘ (sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
          (sublevelBoundaryChart g a x₂ hx₂ hg hr₂) ∘ (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
            (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  let I : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  let t : OpenPartialHomeomorph (MorseHalfSpace m) (MorseHalfSpace m) :=
    (sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)
  refine contDiffOn_of_locally_contDiffOn ?_
  intro y hy
  let d₁ := levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁
  let u : Set (MorseModel (m + 1)) :=
    {x' : MorseModel (m + 1) | (a - x' (Fin.last m), levelSetSplitFst m x') ∈ d₁.ψ.target}
  refine ⟨u, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun x' : MorseModel (m + 1) =>
        (a - x' (Fin.last m), levelSetSplitFst m x')) := by
      have hc1 : Continuous (fun x' : MorseModel (m + 1) => a - x' (Fin.last m)) := by fun_prop
      have hc2 : Continuous (fun x' : MorseModel (m + 1) => levelSetSplitFst m x') := by fun_prop
      exact hc1.prodMk hc2
    exact d₁.ψ.open_target.preimage hcont
  · have hy2 : y ∈ Set.range I := hy.2
    have hy2' : 0 ≤ y (Fin.last m) := by
      rw [range_morseModelWithCornersHalfSpace] at hy2
      exact hy2
    let z : MorseHalfSpace m := ⟨y, hy2'⟩
    have hclamp : I.symm y = z := by
      apply Subtype.ext
      exact morseHalfSpaceClamp_of_mem m hy2'
    have hy1 : I.symm y ∈ t.source := by
      change (morseModelWithCornersHalfSpace m).symm y ∈
        ((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
          (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)).source
      exact hy.1
    have hy1z : z ∈ t.source := by
      rw [hclamp] at hy1
      exact hy1
    have hz1 : z ∈ (sublevelBoundaryChart g a x₁ hx₁ hg hr₁).target := by
      rw [OpenPartialHomeomorph.trans_source] at hy1z
      exact hy1z.1
    change (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1))) ∈
      d₁.ψ.target
    exact hz1
  · have hunder : ContDiffOn ℝ (⊤ : ℕ∞)
        (sublevelBoundaryChartUnderlying g a x₁ x₂ hx₁ hx₂ hg hr₁ hr₂) u :=
      contDiffOn_sublevelBoundaryChartUnderlying g a x₁ x₂ hx₁ hx₂ hg hr₁ hr₂
    have hunder' : ContDiffOn ℝ (⊤ : ℕ∞)
        (sublevelBoundaryChartUnderlying g a x₁ x₂ hx₁ hx₂ hg hr₁ hr₂)
        (I.symm ⁻¹' t.source ∩ Set.range I ∩ u) :=
      hunder.mono (by intro x' hx'; exact hx'.2)
    refine hunder'.congr ?_
    intro x' hx'
    change (morseModelWithCornersHalfSpace m) (t ((morseModelWithCornersHalfSpace m).symm x')) =
      sublevelBoundaryChartUnderlying g a x₁ x₂ hx₁ hx₂ hg hr₁ hr₂ x'
    exact sublevelBoundaryChart_transition_reduce g a x₁ x₂ hx₁ hx₂ hg hr₁ hr₂ hx'.1

noncomputable def sublevelBoundaryChartUnderlyingCross {m : ℕ} (g f : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ : SublevelSpace g a) (x₂ : SublevelSpace f a) (hx₁ : g x₁.1 = a) (hx₂ : f x₂.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ f x₂.1 ≠ 0) :
    MorseModel (m + 1) → MorseModel (m + 1) :=
  let d₁ := levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁
  let d₂ := levelSetChartData.mk f a ⟨x₂.1, hx₂⟩ hf hr₂
  let e₁ : Fin (m + 1) ≃ Fin (m + 1) := d₁.e
  let e₂ : Fin (m + 1) ≃ Fin (m + 1) := d₂.e
  let ψ₁ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₁.ψ
  let ψ₂ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₂.ψ
  fun x =>
    let t : ℝ := a - x (Fin.last m)
    let y' : MorseModel m := levelSetSplitFst m x
    let u : MorseModel (m + 1) := ψ₁.symm (t, y')
    let v : MorseModel (m + 1) := levelSetReindex e₂ (levelSetReindex e₁ u)
    levelSetSplit m (levelSetSplitFst m v, a - (ψ₂ v).1)

theorem contDiffAt_sublevelBoundaryChartUnderlyingCross {m : ℕ} (g f : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ : SublevelSpace g a) (x₂ : SublevelSpace f a) (hx₁ : g x₁.1 = a) (hx₂ : f x₂.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ f x₂.1 ≠ 0)
    {z : MorseModel (m + 1)}
    (hz : (a - z (Fin.last m), levelSetSplitFst m z) ∈
      (levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁).ψ.target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (sublevelBoundaryChartUnderlyingCross g f a x₁ x₂ hx₁ hx₂ hg hf hr₁ hr₂) z := by
  classical
  let d₁ := levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁
  let d₂ := levelSetChartData.mk f a ⟨x₂.1, hx₂⟩ hf hr₂
  let e₁ : Fin (m + 1) ≃ Fin (m + 1) := d₁.e
  let e₂ : Fin (m + 1) ≃ Fin (m + 1) := d₂.e
  let ψ₁ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₁.ψ
  let ψ₂ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₂.ψ
  have hψ₁ : (ψ₁ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e₁ := d₁.hψ
  have hψ₂ : (ψ₂ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap f e₂ := d₂.hψ
  let t : ℝ := a - z (Fin.last m)
  let y' : MorseModel m := levelSetSplitFst m z
  let w₁ : MorseModel (m + 1) := ψ₁.symm (t, y')
  have hw₁src : w₁ ∈ ψ₁.source := ψ₁.map_target hz
  have hc₁' : (fderiv ℝ (fun v => g (levelSetReindex e₁ v)) w₁) levelSetLastBasis ≠ 0 := by
    rw [d₁.hψsource] at hw₁src
    exact hw₁src.2
  have hpair : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => (a - x (Fin.last m), levelSetSplitFst m x)) z := by
    have hc1 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : MorseModel (m + 1) => a - x (Fin.last m)) z := by
      fun_prop
    have hc2 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : MorseModel (m + 1) => levelSetSplitFst m x) z := by
      fun_prop
    exact hc1.prodMk hc2
  have hsymm₁ : ContDiffAt ℝ (⊤ : ℕ∞)
      (ψ₁.symm : (ℝ × MorseModel m) → MorseModel (m + 1)) (t, y') := by
    refine OpenPartialHomeomorph.contDiffAt_symm ψ₁
      (f₀' := levelSetChartDerivEquiv g e₁ w₁ hc₁') ?_ ?_ ?_
    · change (a - z (Fin.last m), levelSetSplitFst m z) ∈ ψ₁.target
      exact hz
    · rw [hψ₁]
      exact hasFDerivAt_levelSetChartMap g e₁ w₁ hg.contDiffAt hc₁'
    · rw [hψ₁]
      exact contDiffAt_levelSetChartMap g e₁ w₁ hg.contDiffAt
  have h₁ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x)) z :=
    hsymm₁.comp z hpair
  have hlin₁ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun v : MorseModel (m + 1) => levelSetReindex e₁ v) (ψ₁.symm (t, y')) :=
    ((levelSetReindex e₁).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
  have h₂ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => levelSetReindex e₁ (ψ₁.symm (a - x (Fin.last m),
        levelSetSplitFst m x))) z :=
    hlin₁.comp z h₁
  have hlin₂ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun v : MorseModel (m + 1) => levelSetReindex e₂ v) (levelSetReindex e₁ (ψ₁.symm (t, y'))) :=
    ((levelSetReindex e₂).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
  have h₃ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => levelSetReindex e₂ (levelSetReindex e₁
        (ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x)))) z :=
    hlin₂.comp z h₂
  have hψ₂at : ContDiffAt ℝ (⊤ : ℕ∞) (ψ₂ : MorseModel (m + 1) → ℝ × MorseModel m)
      (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y')))) := by
    rw [hψ₂]
    exact contDiffAt_levelSetChartMap f e₂ _ hf.contDiffAt
  have h₄ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => ψ₂ (levelSetReindex e₂ (levelSetReindex e₁
        (ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x))))) z :=
    hψ₂at.comp z h₃
  have hfst : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × MorseModel m => p.1)
      (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y'))))) := by fun_prop
  have h₅ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => Prod.fst (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁
        (ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x)))))) z :=
    hfst.comp z h₄
  have hsub : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => a - Prod.fst (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁
        (ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x)))))) z := by
    have hsub' : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℝ => a - r)
        (Prod.fst (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y')))))) := by fun_prop
    exact hsub'.comp z h₅
  have hpf : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => levelSetSplitFst m (levelSetReindex e₂ (levelSetReindex e₁
        (ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x))))) z := by
    have hpf' : ContDiffAt ℝ (⊤ : ℕ∞) (levelSetSplitFst m)
        (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y')))) :=
      (levelSetSplitFst m).contDiff.contDiffAt
    exact hpf'.comp z h₃
  have hsplit : ContDiffAt ℝ (⊤ : ℕ∞) (levelSetSplit m)
      (levelSetSplitFst m (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y')))),
        a - Prod.fst (ψ₂ (levelSetReindex e₂ (levelSetReindex e₁ (ψ₁.symm (t, y')))))) :=
    (levelSetSplit m).toContinuousLinearEquiv.contDiff.contDiffAt
  exact (by
    simpa [sublevelBoundaryChartUnderlyingCross] using
      (hsplit.comp z (hpf.prodMk hsub)))

theorem contDiffOn_sublevelBoundaryChartUnderlyingCross {m : ℕ} (g f : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ : SublevelSpace g a) (x₂ : SublevelSpace f a) (hx₁ : g x₁.1 = a) (hx₂ : f x₂.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ f x₂.1 ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sublevelBoundaryChartUnderlyingCross g f a x₁ x₂ hx₁ hx₂ hg hf hr₁ hr₂)
      {x' : MorseModel (m + 1) | (a - x' (Fin.last m), levelSetSplitFst m x') ∈
        (levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁).ψ.target} := by
  rw [IsOpen.contDiffOn_iff (by
    have hcont : Continuous (fun x' : MorseModel (m + 1) =>
        (a - x' (Fin.last m), levelSetSplitFst m x')) := by
      have hc1 : Continuous (fun x' : MorseModel (m + 1) => a - x' (Fin.last m)) := by fun_prop
      have hc2 : Continuous (fun x' : MorseModel (m + 1) => levelSetSplitFst m x') := by fun_prop
      exact hc1.prodMk hc2
    exact (levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁).ψ.open_target.preimage hcont)]
  intro x' hx'
  exact contDiffAt_sublevelBoundaryChartUnderlyingCross g f a x₁ x₂ hx₁ hx₂ hg hf hr₁ hr₂ hx'

theorem sublevelBoundaryChart_transition_mem_contDiffGroupoid {m : ℕ}
    (g : MorseModel (m + 1) → ℝ) (a : ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {x₁ x₂ : SublevelSpace g a} (hx₁ : g x₁.1 = a) (hx₂ : g x₂.1 = a)
    (hr₁ : fderiv ℝ g x₁.1 ≠ 0) (hr₂ : fderiv ℝ g x₂.1 ≠ 0) :
    (sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ (sublevelBoundaryChart g a x₂ hx₂ hg hr₂) ∈
      contDiffGroupoid (⊤ : ℕ∞) (morseModelWithCornersHalfSpace m) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · exact contDiffOn_sublevelBoundaryChart_transition g a hg hx₁ hx₂ hr₁ hr₂
  · rw [show ((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
        (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)).symm =
          (sublevelBoundaryChart g a x₂ hx₂ hg hr₂).symm ≫ₕ
            (sublevelBoundaryChart g a x₁ hx₁ hg hr₁) from by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
        rfl]
    rw [show ((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
        (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)).target =
          ((sublevelBoundaryChart g a x₂ hx₂ hg hr₂).symm ≫ₕ
            (sublevelBoundaryChart g a x₁ hx₁ hg hr₁)).source by
        rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source]
        rfl]
    exact contDiffOn_sublevelBoundaryChart_transition g a hg hx₂ hx₁ hr₂ hr₁


noncomputable def sublevelInteriorRadius {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 < a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ℝ :=
  Classical.choose (Metric.mem_nhds_iff.mp ((isOpen_Iio.preimage hg.continuous).mem_nhds hx))

noncomputable def sublevelInteriorShift {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 < a) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ℝ :=
  sublevelInteriorRadius g a x hx hg + ‖x.1‖ + 1

theorem sublevelInteriorChart_apply_value {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 < a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (y : SublevelSpace g a) (hy : dist y.1 x.1 < sublevelInteriorRadius g a x hx hg) :
    ((sublevelInteriorChart g a x hx hg) y : MorseModel (m + 1)) =
      morseHalfSpaceShift (sublevelInteriorShift g a x hx hg) y.1 := by
  simp only [sublevelInteriorChart]
  change ((if h : dist y.1 x.1 < sublevelInteriorRadius g a x hx hg then
        (⟨morseHalfSpaceShift (sublevelInteriorShift g a x hx hg) y.1, _⟩ : MorseHalfSpace m)
      else ⟨morseHalfSpaceShift (sublevelInteriorShift g a x hx hg) x.1, _⟩ : MorseHalfSpace m) :
          MorseModel (m + 1)) = morseHalfSpaceShift (sublevelInteriorShift g a x hx hg) y.1
  rw [dif_pos hy]

theorem sublevelInteriorChart_symm_value {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x : SublevelSpace g a) (hx : g x.1 < a) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {z : MorseHalfSpace m}
    (hz : dist (morseHalfSpaceShift (-(sublevelInteriorShift g a x hx hg))
      (z : MorseModel (m + 1))) x.1 < sublevelInteriorRadius g a x hx hg) :
    (sublevelInteriorChart g a x hx hg).symm z =
      (⟨morseHalfSpaceShift (-(sublevelInteriorShift g a x hx hg)) (z : MorseModel (m + 1)),
        by
          have hg' : g (morseHalfSpaceShift (-(sublevelInteriorShift g a x hx hg))
              (z : MorseModel (m + 1))) < a := by
            have hsub : Metric.ball x.1 (sublevelInteriorRadius g a x hx hg) ⊆
                {y : MorseModel (m + 1) | g y < a} := by
              exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
                ((isOpen_Iio.preimage hg.continuous).mem_nhds hx))).2
            exact hsub hz
          exact le_of_lt hg'⟩ : SublevelSpace g a) := by
  classical
  change (if h : dist (morseHalfSpaceShift (-(sublevelInteriorShift g a x hx hg))
        (z : MorseModel (m + 1))) x.1 < sublevelInteriorRadius g a x hx hg then
        (⟨morseHalfSpaceShift (-(sublevelInteriorShift g a x hx hg)) (z : MorseModel (m + 1)),
          by
            have hg' : g (morseHalfSpaceShift (-(sublevelInteriorShift g a x hx hg))
                (z : MorseModel (m + 1))) < a := by
              have hsub : Metric.ball x.1 (sublevelInteriorRadius g a x hx hg) ⊆
                  {y : MorseModel (m + 1) | g y < a} := by
                exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
                  ((isOpen_Iio.preimage hg.continuous).mem_nhds hx))).2
              exact hsub h
            exact le_of_lt hg'⟩ : SublevelSpace g a)
      else ⟨x.1, by
        change g x.1 ≤ a
        exact le_of_lt hx⟩) = (⟨morseHalfSpaceShift (-(sublevelInteriorShift g a x hx hg))
          (z : MorseModel (m + 1)), by
            have hg' : g (morseHalfSpaceShift (-(sublevelInteriorShift g a x hx hg))
                (z : MorseModel (m + 1))) < a := by
              have hsub : Metric.ball x.1 (sublevelInteriorRadius g a x hx hg) ⊆
                  {y : MorseModel (m + 1) | g y < a} := by
                exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
                  ((isOpen_Iio.preimage hg.continuous).mem_nhds hx))).2
              exact hsub hz
            exact le_of_lt hg'⟩ : SublevelSpace g a)
  rw [dif_pos hz]

theorem sublevelInteriorInterior_transition_reduce {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ x₂ : SublevelSpace g a) (hx₁ : g x₁.1 < a) (hx₂ : g x₂.1 < a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {y : MorseModel (m + 1)}
    (hy : y ∈ ((morseModelWithCornersHalfSpace m).symm ⁻¹'
        ((sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ (sublevelInteriorChart g a x₂ hx₂ hg)).source ∩
      Set.range (morseModelWithCornersHalfSpace m))) :
    (morseModelWithCornersHalfSpace m) (((sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ
        (sublevelInteriorChart g a x₂ hx₂ hg)) ((morseModelWithCornersHalfSpace m).symm y)) =
      morseHalfSpaceShift (sublevelInteriorShift g a x₂ hx₂ hg)
        (morseHalfSpaceShift (-(sublevelInteriorShift g a x₁ hx₁ hg)) y) := by
  classical
  let c₁ : ℝ := sublevelInteriorShift g a x₁ hx₁ hg
  let c₂ : ℝ := sublevelInteriorShift g a x₂ hx₂ hg
  let I : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  let t : OpenPartialHomeomorph (MorseHalfSpace m) (MorseHalfSpace m) :=
    (sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ (sublevelInteriorChart g a x₂ hx₂ hg)
  have hy2 : y ∈ Set.range I := hy.2
  have hy2' : 0 ≤ y (Fin.last m) := by
    rw [range_morseModelWithCornersHalfSpace] at hy2
    exact hy2
  let z : MorseHalfSpace m := ⟨y, hy2'⟩
  have hclamp : I.symm y = z := by
    apply Subtype.ext
    exact morseHalfSpaceClamp_of_mem m hy2'
  have hy1 : I.symm y ∈ t.source := hy.1
  have hy1z : z ∈ t.source := by
    rw [hclamp] at hy1
    exact hy1
  have hz1 : z ∈ (sublevelInteriorChart g a x₁ hx₁ hg).target := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.1
  have hz2 : (sublevelInteriorChart g a x₁ hx₁ hg).symm z ∈
      (sublevelInteriorChart g a x₂ hx₂ hg).source := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.2
  have hsymm₁ : (sublevelInteriorChart g a x₁ hx₁ hg).symm z =
      (⟨morseHalfSpaceShift (-c₁) (z : MorseModel (m + 1)), by
        have hball : dist (morseHalfSpaceShift (-c₁) (z : MorseModel (m + 1))) x₁.1 <
            sublevelInteriorRadius g a x₁ hx₁ hg := by
          change dist (morseHalfSpaceShift (-c₁) (z : MorseModel (m + 1))) x₁.1 <
            sublevelInteriorRadius g a x₁ hx₁ hg at hz1
          exact hz1
        have hg' : g (morseHalfSpaceShift (-c₁) (z : MorseModel (m + 1))) < a := by
          have hsub : Metric.ball x₁.1 (sublevelInteriorRadius g a x₁ hx₁ hg) ⊆
              {y : MorseModel (m + 1) | g y < a} := by
            exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
              ((isOpen_Iio.preimage hg.continuous).mem_nhds hx₁))).2
          exact hsub hball
        exact le_of_lt hg'⟩ : SublevelSpace g a) := by
    rw [sublevelInteriorChart_symm_value g a x₁ hx₁ hg (by
      change dist (morseHalfSpaceShift (-c₁) (z : MorseModel (m + 1))) x₁.1 <
        sublevelInteriorRadius g a x₁ hx₁ hg
      exact hz1)]
  have hsrc2 : dist ((sublevelInteriorChart g a x₁ hx₁ hg).symm z).1 x₂.1 <
      sublevelInteriorRadius g a x₂ hx₂ hg := by
    change dist ((sublevelInteriorChart g a x₁ hx₁ hg).symm z : MorseModel (m + 1)) x₂.1 <
      sublevelInteriorRadius g a x₂ hx₂ hg at hz2
    exact hz2
  rw [hclamp]
  rw [OpenPartialHomeomorph.trans_apply]
  change ((sublevelInteriorChart g a x₂ hx₂ hg) ((sublevelInteriorChart g a x₁ hx₁ hg).symm z) :
      MorseModel (m + 1)) = morseHalfSpaceShift c₂ (morseHalfSpaceShift (-c₁) y)
  rw [sublevelInteriorChart_apply_value g a x₂ hx₂ hg
    ((sublevelInteriorChart g a x₁ hx₁ hg).symm z) hsrc2]
  change morseHalfSpaceShift c₂ ((sublevelInteriorChart g a x₁ hx₁ hg).symm z).1 =
    morseHalfSpaceShift c₂ (morseHalfSpaceShift (-c₁) y)
  rw [hsymm₁]


theorem contDiff_morseHalfSpaceShift {m : ℕ} (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : MorseModel (m + 1) => morseHalfSpaceShift c x) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : MorseModel (m + 1) =>
    HAdd.hAdd x (HSMul.hSMul c levelSetLastBasis))
  fun_prop

noncomputable def sublevelInteriorBoundaryTransitionUnderlyingCross {m : ℕ}
    (g f : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ : SublevelSpace g a) (hx₁ : g x₁.1 < a)
    (x₂ : SublevelSpace f a) (hx₂ : f x₂.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hr₂ : fderiv ℝ f x₂.1 ≠ 0) :
    MorseModel (m + 1) → MorseModel (m + 1) :=
  fun v => sublevelBoundaryChartValue f a x₂ hx₂ hf hr₂
    (morseHalfSpaceShift (-sublevelInteriorShift g a x₁ hx₁ hg) v)

theorem contDiff_sublevelInteriorBoundaryTransitionUnderlyingCross {m : ℕ}
    (g f : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ : SublevelSpace g a) (hx₁ : g x₁.1 < a)
    (x₂ : SublevelSpace f a) (hx₂ : f x₂.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hr₂ : fderiv ℝ f x₂.1 ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelInteriorBoundaryTransitionUnderlyingCross g f a x₁ hx₁ x₂ hx₂ hg hf hr₂) := by
  unfold sublevelInteriorBoundaryTransitionUnderlyingCross
  exact (contDiff_sublevelBoundaryChartValue f a x₂ hx₂ hf hr₂).comp
    (contDiff_morseHalfSpaceShift (-sublevelInteriorShift g a x₁ hx₁ hg))


theorem contMDiffAt_sublevelSetEqIdentityInterior {m : ℕ} (g f : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hreg_g : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0)
    (hreg_f : ∀ x : MorseModel (m + 1), f x = a → fderiv ℝ f x ≠ 0)
    (hset : {x : MorseModel (m + 1) | g x ≤ a} = {x : MorseModel (m + 1) | f x ≤ a})
    (x : SublevelSpace g a) (hx : g x.1 < a)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) :=
      sublevelChartedSpace g a hg hreg_g)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f a) :=
      sublevelChartedSpace f a hf hreg_f)
    (hchart₁ : ∀ y : SublevelSpace g a, hcs₁.chartAt y =
      (if h : g y.1 = a then sublevelBoundaryChart g a y h hg (hreg_g y.1 h)
        else sublevelInteriorChart g a y (lt_of_le_of_ne (show g y.1 ≤ a from y.2) h) hg) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace f a, hcs₂.chartAt y =
      (if h : f y.1 = a then sublevelBoundaryChart f a y h hf (hreg_f y.1 h)
        else sublevelInteriorChart f a y (lt_of_le_of_ne (show f y.1 ≤ a from y.2) h) hf) := by
      intro y
      rfl) :
    ContMDiffAt (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g a => (⟨y.1, by
        have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
          rw [← hset]
          exact y.2
        exact this⟩ : SublevelSpace f a)) x := by
  classical
  letI := hcs₁
  letI := hcs₂
  have hmap : ∀ y : MorseModel (m + 1), g y ≤ a → f y ≤ a := by
    intro y hy
    have : y ∈ {x : MorseModel (m + 1) | f x ≤ a} := by rw [← hset]; exact hy
    exact this
  rw [contMDiffAt_iff]
  constructor
  · have hcont : Continuous (fun y : SublevelSpace g a => y.1) := continuous_subtype_val
    exact (Continuous.subtype_mk hcont (fun y => hmap y.1 y.2)).continuousAt
  · let c₁ : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
      sublevelInteriorChart g a x hx hg
    let c₁' : ℝ := sublevelInteriorShift g a x hx hg
    by_cases hxb : f x.1 = a
    · let c₂ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) :=
        sublevelBoundaryChart f a ⟨x.1, hmap x.1 x.2⟩ hxb hf (hreg_f x.1 hxb)
      have hchart₁' : hcs₁.chartAt x = c₁ := by
        rw [hchart₁ x, dif_neg (ne_of_lt hx)]
      have hchart₂' : hcs₂.chartAt (⟨x.1, hmap x.1 x.2⟩ : SublevelSpace f a) = c₂ := by
        rw [hchart₂ ⟨x.1, hmap x.1 x.2⟩, dif_pos hxb]
      have hF : ContDiff ℝ (⊤ : ℕ∞)
          (sublevelInteriorBoundaryTransitionUnderlyingCross g f a x hx
            ⟨x.1, hmap x.1 x.2⟩ hxb hg hf (hreg_f x.1 hxb)) :=
        contDiff_sublevelInteriorBoundaryTransitionUnderlyingCross g f a x hx
          ⟨x.1, hmap x.1 x.2⟩ hxb hg hf (hreg_f x.1 hxb)
      have hz₀ : ((morseModelWithCornersHalfSpace m) (c₁ x)) ∈
          Set.range (morseModelWithCornersHalfSpace m) :=
        ⟨c₁ x, rfl⟩
      have hB₁ : {z : MorseModel (m + 1) |
          dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g a x hx hg} ∈
          nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
            (Set.range (morseModelWithCornersHalfSpace m)) := by
        have hc₁val : ((morseModelWithCornersHalfSpace m) (c₁ x) : MorseModel (m + 1)) =
            morseHalfSpaceShift c₁' x.1 := by
          have hc₁val' : ((sublevelInteriorChart g a x hx hg x : MorseHalfSpace m) :
              MorseModel (m + 1)) = morseHalfSpaceShift c₁' x.1 := by
            rw [sublevelInteriorChart_apply_value g a x hx hg x (by
              rw [dist_self]
              exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
                ((isOpen_Iio.preimage hg.continuous).mem_nhds hx))).1)]
          simpa [c₁] using hc₁val'
        have hcont : Continuous (fun z : MorseModel (m + 1) =>
            dist (morseHalfSpaceShift (-c₁') z) x.1) := by
          have hshift : Continuous (fun x : MorseModel (m + 1) => morseHalfSpaceShift (-c₁') x) := by
            change Continuous (fun x : MorseModel (m + 1) =>
              HAdd.hAdd x (HSMul.hSMul (-c₁') levelSetLastBasis))
            fun_prop
          exact hshift.dist (continuous_const : Continuous fun _ : MorseModel (m + 1) => x.1)
        have hmem₀ : dist (morseHalfSpaceShift (-c₁') ((morseModelWithCornersHalfSpace m) (c₁ x))) x.1 <
            sublevelInteriorRadius g a x hx hg := by
          rw [hc₁val, morseHalfSpaceShift_neg]
          rw [dist_self]
          exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
            ((isOpen_Iio.preimage hg.continuous).mem_nhds hx))).1
        exact nhdsWithin_le_nhds ((isOpen_Iio.preimage hcont).mem_nhds hmem₀)
      have hB : Set.range (morseModelWithCornersHalfSpace m) ∩
          {z : MorseModel (m + 1) |
            dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g a x hx hg} ∈
          nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
            (Set.range (morseModelWithCornersHalfSpace m)) := by
        exact Filter.inter_mem self_mem_nhdsWithin hB₁
      have hred : (morseModelWithCornersHalfSpace m ∘ c₂ ∘
          (fun y : SublevelSpace g a => (⟨y.1, by
            have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
              rw [← hset]
              exact y.2
            exact this⟩ : SublevelSpace f a)) ∘
          c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm) =ᶠ[
            nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
              (Set.range (morseModelWithCornersHalfSpace m))]
          (sublevelInteriorBoundaryTransitionUnderlyingCross g f a x hx
            ⟨x.1, hmap x.1 x.2⟩ hxb hg hf (hreg_f x.1 hxb)) := by
        refine Filter.eventuallyEq_of_mem (s := Set.range (morseModelWithCornersHalfSpace m) ∩
            {z : MorseModel (m + 1) |
              dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g a x hx hg}) ?_ ?_
        · exact hB
        · intro z hz
          have hzr : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.1
          have hzmem : 0 ≤ z (Fin.last m) := by
            rw [range_morseModelWithCornersHalfSpace] at hzr
            exact hzr
          let z' : MorseHalfSpace m := ⟨z, hzmem⟩
          have hclamp : (morseModelWithCornersHalfSpace m).symm z = z' := by
            apply Subtype.ext
            exact morseHalfSpaceClamp_of_mem m hzmem
          change (morseModelWithCornersHalfSpace m)
              (c₂ ((fun y : SublevelSpace g a =>
                (⟨y.1, by
                  have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
                    rw [← hset]
                    exact y.2
                  exact this⟩ : SublevelSpace f a))
                (c₁.symm ((morseModelWithCornersHalfSpace m).symm z)))) =
            sublevelInteriorBoundaryTransitionUnderlyingCross g f a x hx
              ⟨x.1, hmap x.1 x.2⟩ hxb hg hf (hreg_f x.1 hxb) z
          have hz₁ : dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g a x hx hg :=
            hz.2
          have hmem₁ : dist (morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1))) x.1 <
              sublevelInteriorRadius g a x hx hg := by
            simpa [z'] using hz₁
          have hball : Metric.ball x.1 (sublevelInteriorRadius g a x hx hg) ⊆
              {y : MorseModel (m + 1) | g y < a} := by
            exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
              ((isOpen_Iio.preimage hg.continuous).mem_nhds hx))).2
          have hsymm₁ : c₁.symm z' = (⟨morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1)), by
              change g (morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1))) ≤ a
              exact le_of_lt (hball hmem₁)⟩ : SublevelSpace g a) := by
            rw [sublevelInteriorChart_symm_value g a x hx hg hmem₁]
          have hval₂ : ((c₂ (⟨morseHalfSpaceShift (-c₁') z,
                hmap (morseHalfSpaceShift (-c₁') z) (le_of_lt (hball hmem₁))⟩ : SublevelSpace f a)) :
                MorseModel (m + 1)) =
              sublevelBoundaryChartValue f a ⟨x.1, hmap x.1 x.2⟩ hxb hf (hreg_f x.1 hxb)
                (morseHalfSpaceShift (-c₁') z) := by
            rw [sublevelBoundaryChart_apply_value' f a ⟨x.1, hmap x.1 x.2⟩ hxb hf
              (hreg_f x.1 hxb) (⟨morseHalfSpaceShift (-c₁') z,
                hmap (morseHalfSpaceShift (-c₁') z) (le_of_lt (hball hmem₁))⟩ : SublevelSpace f a)]
          rw [hclamp]
          rw [hsymm₁]
          simpa [hval₂, sublevelInteriorBoundaryTransitionUnderlyingCross, sublevelBoundaryChartValue]
      have hcomp : ContDiffWithinAt ℝ (⊤ : ℕ∞)
          (morseModelWithCornersHalfSpace m ∘ c₂ ∘
            (fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a)) ∘
            c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm)
          (Set.range (morseModelWithCornersHalfSpace m))
          ((morseModelWithCornersHalfSpace m) (c₁ x)) := by
        have hFAt : ContDiffWithinAt ℝ (⊤ : ℕ∞)
            (sublevelInteriorBoundaryTransitionUnderlyingCross g f a x hx
              ⟨x.1, hmap x.1 x.2⟩ hxb hg hf (hreg_f x.1 hxb))
            (Set.range (morseModelWithCornersHalfSpace m))
            ((morseModelWithCornersHalfSpace m) (c₁ x)) :=
          hF.contDiffAt.contDiffWithinAt
        exact hFAt.congr_of_eventuallyEq_of_mem hred hz₀
      have hcomp' : ContDiffWithinAt ℝ (⊤ : ℕ∞)
          (morseModelWithCornersHalfSpace m ∘ c₂ ∘
            (fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a)) ∘
            c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm)
          (Set.range (morseModelWithCornersHalfSpace m))
          (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
        simpa [extChartAt, hchart₁'] using hcomp
      refine hcomp'.congr_of_eventuallyEq_of_mem ?_ ?_
      · rw [show (extChartAt (morseModelWithCornersHalfSpace m)
            (⟨x.1, hmap x.1 x.2⟩ : SublevelSpace f a)) =
            ((hcs₂.chartAt (⟨x.1, hmap x.1 x.2⟩ : SublevelSpace f a)).extend
              (morseModelWithCornersHalfSpace m)) by rfl]
        rw [show (extChartAt (morseModelWithCornersHalfSpace m) x) =
            ((hcs₁.chartAt x).extend (morseModelWithCornersHalfSpace m)) by rfl]
        rw [hchart₂']
        rw [hchart₁']
        simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
        change ((morseModelWithCornersHalfSpace m ∘ c₂) ∘
            (fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a)) ∘
            c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm) =ᶠ[
              nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
                (Set.range (morseModelWithCornersHalfSpace m))]
            (morseModelWithCornersHalfSpace m ∘ c₂ ∘
              (fun y : SublevelSpace g a => (⟨y.1, by
                have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
                  rw [← hset]
                  exact y.2
                exact this⟩ : SublevelSpace f a)) ∘
              c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm)
        rfl
      · simp [extChartAt, hchart₁']
    · let hx₂ : f x.1 < a := lt_of_le_of_ne (hmap x.1 x.2) hxb
      let c₂ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) :=
        sublevelInteriorChart f a ⟨x.1, hmap x.1 x.2⟩ hx₂ hf
      have hchart₁' : hcs₁.chartAt x = c₁ := by
        rw [hchart₁ x, dif_neg (ne_of_lt hx)]
      have hchart₂' : hcs₂.chartAt (⟨x.1, hmap x.1 x.2⟩ : SublevelSpace f a) = c₂ := by
        rw [hchart₂ ⟨x.1, hmap x.1 x.2⟩, dif_neg (ne_of_lt hx₂)]
      let c₂' : ℝ := sublevelInteriorShift f a ⟨x.1, hmap x.1 x.2⟩ hx₂ hf
      have hF : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : MorseModel (m + 1) => morseHalfSpaceShift c₂' (morseHalfSpaceShift (-c₁') z)) := by
        exact (contDiff_morseHalfSpaceShift c₂').comp
          (contDiff_morseHalfSpaceShift (-c₁'))
      have hz₀ : ((morseModelWithCornersHalfSpace m) (c₁ x)) ∈
          Set.range (morseModelWithCornersHalfSpace m) :=
        ⟨c₁ x, rfl⟩
      have hB₁ : {z : MorseModel (m + 1) |
          dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g a x hx hg} ∈
          nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
            (Set.range (morseModelWithCornersHalfSpace m)) := by
        have hc₁val : ((morseModelWithCornersHalfSpace m) (c₁ x) : MorseModel (m + 1)) =
            morseHalfSpaceShift c₁' x.1 := by
          have hc₁val' : ((sublevelInteriorChart g a x hx hg x : MorseHalfSpace m) :
              MorseModel (m + 1)) = morseHalfSpaceShift c₁' x.1 := by
            rw [sublevelInteriorChart_apply_value g a x hx hg x (by
              rw [dist_self]
              exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
                ((isOpen_Iio.preimage hg.continuous).mem_nhds hx))).1)]
          simpa [c₁] using hc₁val'
        have hcont : Continuous (fun z : MorseModel (m + 1) =>
            dist (morseHalfSpaceShift (-c₁') z) x.1) := by
          have hshift : Continuous (fun x : MorseModel (m + 1) => morseHalfSpaceShift (-c₁') x) := by
            change Continuous (fun x : MorseModel (m + 1) =>
              HAdd.hAdd x (HSMul.hSMul (-c₁') levelSetLastBasis))
            fun_prop
          exact hshift.dist (continuous_const : Continuous fun _ : MorseModel (m + 1) => x.1)
        have hmem₀ : dist (morseHalfSpaceShift (-c₁') ((morseModelWithCornersHalfSpace m) (c₁ x))) x.1 <
            sublevelInteriorRadius g a x hx hg := by
          rw [hc₁val, morseHalfSpaceShift_neg]
          rw [dist_self]
          exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
            ((isOpen_Iio.preimage hg.continuous).mem_nhds hx))).1
        exact nhdsWithin_le_nhds ((isOpen_Iio.preimage hcont).mem_nhds hmem₀)
      have hB₂ : {z : MorseModel (m + 1) |
          dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius f a
            ⟨x.1, hmap x.1 x.2⟩ hx₂ hf} ∈
          nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
            (Set.range (morseModelWithCornersHalfSpace m)) := by
        have hcont : Continuous (fun z : MorseModel (m + 1) =>
            dist (morseHalfSpaceShift (-c₁') z) x.1) := by
          have hshift : Continuous (fun x : MorseModel (m + 1) => morseHalfSpaceShift (-c₁') x) := by
            change Continuous (fun x : MorseModel (m + 1) =>
              HAdd.hAdd x (HSMul.hSMul (-c₁') levelSetLastBasis))
            fun_prop
          exact hshift.dist (continuous_const : Continuous fun _ : MorseModel (m + 1) => x.1)
        have hc₁val : ((morseModelWithCornersHalfSpace m) (c₁ x) : MorseModel (m + 1)) =
            morseHalfSpaceShift c₁' x.1 := by
          have hc₁val' : ((sublevelInteriorChart g a x hx hg x : MorseHalfSpace m) :
              MorseModel (m + 1)) = morseHalfSpaceShift c₁' x.1 := by
            rw [sublevelInteriorChart_apply_value g a x hx hg x (by
              rw [dist_self]
              exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
                ((isOpen_Iio.preimage hg.continuous).mem_nhds hx))).1)]
          simpa [c₁] using hc₁val'
        have hmem₀ : dist (morseHalfSpaceShift (-c₁')
            ((morseModelWithCornersHalfSpace m) (c₁ x))) x.1 <
            sublevelInteriorRadius f a ⟨x.1, hmap x.1 x.2⟩ hx₂ hf := by
          rw [hc₁val, morseHalfSpaceShift_neg]
          rw [dist_self]
          exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
            ((isOpen_Iio.preimage hf.continuous).mem_nhds hx₂))).1
        exact nhdsWithin_le_nhds ((isOpen_Iio.preimage hcont).mem_nhds hmem₀)
      have hB : Set.range (morseModelWithCornersHalfSpace m) ∩
          {z : MorseModel (m + 1) |
            dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g a x hx hg} ∩
          {z : MorseModel (m + 1) |
            dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius f a
              ⟨x.1, hmap x.1 x.2⟩ hx₂ hf} ∈
          nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
            (Set.range (morseModelWithCornersHalfSpace m)) := by
        exact Filter.inter_mem (Filter.inter_mem self_mem_nhdsWithin hB₁) hB₂
      have hred : (morseModelWithCornersHalfSpace m ∘ c₂ ∘
          (fun y : SublevelSpace g a => (⟨y.1, by
            have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
              rw [← hset]
              exact y.2
            exact this⟩ : SublevelSpace f a)) ∘
          c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm) =ᶠ[
            nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
              (Set.range (morseModelWithCornersHalfSpace m))]
          (fun z : MorseModel (m + 1) => morseHalfSpaceShift c₂' (morseHalfSpaceShift (-c₁') z)) := by
        refine Filter.eventuallyEq_of_mem (s := Set.range (morseModelWithCornersHalfSpace m) ∩
            {z : MorseModel (m + 1) |
              dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g a x hx hg} ∩
            {z : MorseModel (m + 1) |
              dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius f a
                ⟨x.1, hmap x.1 x.2⟩ hx₂ hf}) ?_ ?_
        · exact hB
        · intro z hz
          have hzr : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.1.1
          have hzmem : 0 ≤ z (Fin.last m) := by
            rw [range_morseModelWithCornersHalfSpace] at hzr
            exact hzr
          let z' : MorseHalfSpace m := ⟨z, hzmem⟩
          have hclamp : (morseModelWithCornersHalfSpace m).symm z = z' := by
            apply Subtype.ext
            exact morseHalfSpaceClamp_of_mem m hzmem
          change (morseModelWithCornersHalfSpace m)
              (c₂ ((fun y : SublevelSpace g a =>
                (⟨y.1, by
                  have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
                    rw [← hset]
                    exact y.2
                  exact this⟩ : SublevelSpace f a))
                (c₁.symm ((morseModelWithCornersHalfSpace m).symm z)))) =
            morseHalfSpaceShift c₂' (morseHalfSpaceShift (-c₁') z)
          have hz₁ : dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g a x hx hg :=
            hz.1.2
          have hmem₁ : dist (morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1))) x.1 <
              sublevelInteriorRadius g a x hx hg := by
            simpa [z'] using hz₁
          have hz₂ : dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius f a
              ⟨x.1, hmap x.1 x.2⟩ hx₂ hf := hz.2
          have hmem₂ : dist (morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1))) x.1 <
              sublevelInteriorRadius f a ⟨x.1, hmap x.1 x.2⟩ hx₂ hf := by
            simpa [z'] using hz₂
          have hball : Metric.ball x.1 (sublevelInteriorRadius g a x hx hg) ⊆
              {y : MorseModel (m + 1) | g y < a} := by
            exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
              ((isOpen_Iio.preimage hg.continuous).mem_nhds hx))).2
          have hsymm₁ : c₁.symm z' = (⟨morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1)), by
              change g (morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1))) ≤ a
              exact le_of_lt (hball hmem₁)⟩ : SublevelSpace g a) := by
            rw [sublevelInteriorChart_symm_value g a x hx hg hmem₁]
          have hval₂ : (c₂ (⟨morseHalfSpaceShift (-c₁') z,
                hmap (morseHalfSpaceShift (-c₁') z) (le_of_lt (hball hmem₁))⟩ : SublevelSpace f a) :
                MorseModel (m + 1)) =
              morseHalfSpaceShift c₂' (morseHalfSpaceShift (-c₁') z) := by
            rw [sublevelInteriorChart_apply_value f a ⟨x.1, hmap x.1 x.2⟩ hx₂ hf
              (⟨morseHalfSpaceShift (-c₁') z,
                hmap (morseHalfSpaceShift (-c₁') z) (le_of_lt (hball hmem₁))⟩ : SublevelSpace f a)
              hmem₂]
          rw [hclamp]
          rw [hsymm₁]
          simpa [hval₂]
      have hcomp : ContDiffWithinAt ℝ (⊤ : ℕ∞)
          (morseModelWithCornersHalfSpace m ∘ c₂ ∘
            (fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a)) ∘
            c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm)
          (Set.range (morseModelWithCornersHalfSpace m))
          ((morseModelWithCornersHalfSpace m) (c₁ x)) := by
        have hFAt : ContDiffWithinAt ℝ (⊤ : ℕ∞)
            (fun z : MorseModel (m + 1) => morseHalfSpaceShift c₂' (morseHalfSpaceShift (-c₁') z))
            (Set.range (morseModelWithCornersHalfSpace m))
            ((morseModelWithCornersHalfSpace m) (c₁ x)) :=
          hF.contDiffAt.contDiffWithinAt
        exact hFAt.congr_of_eventuallyEq_of_mem hred hz₀
      have hcomp' : ContDiffWithinAt ℝ (⊤ : ℕ∞)
          (morseModelWithCornersHalfSpace m ∘ c₂ ∘
            (fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a)) ∘
            c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm)
          (Set.range (morseModelWithCornersHalfSpace m))
          (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
        simpa [extChartAt, hchart₁'] using hcomp
      refine hcomp'.congr_of_eventuallyEq_of_mem ?_ ?_
      · rw [show (extChartAt (morseModelWithCornersHalfSpace m)
            (⟨x.1, hmap x.1 x.2⟩ : SublevelSpace f a)) =
            ((hcs₂.chartAt (⟨x.1, hmap x.1 x.2⟩ : SublevelSpace f a)).extend
              (morseModelWithCornersHalfSpace m)) by rfl]
        rw [show (extChartAt (morseModelWithCornersHalfSpace m) x) =
            ((hcs₁.chartAt x).extend (morseModelWithCornersHalfSpace m)) by rfl]
        rw [hchart₂']
        rw [hchart₁']
        simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
        change ((morseModelWithCornersHalfSpace m ∘ c₂) ∘
            (fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a)) ∘
            c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm) =ᶠ[
              nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
                (Set.range (morseModelWithCornersHalfSpace m))]
            (morseModelWithCornersHalfSpace m ∘ c₂ ∘
              (fun y : SublevelSpace g a => (⟨y.1, by
                have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
                  rw [← hset]
                  exact y.2
                exact this⟩ : SublevelSpace f a)) ∘
              c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm)
        rfl
      · simp [extChartAt, hchart₁']

theorem sublevelSetEq_boundary_imp_boundary {m : ℕ} (g f : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hset : {x : MorseModel (m + 1) | g x ≤ a} = {x : MorseModel (m + 1) | f x ≤ a})
    (hg_le : ∀ x : MorseModel (m + 1), g x ≤ f x)
    (x : MorseModel (m + 1)) (hgx : g x = a) : f x = a := by
  have hf_le : f x ≤ a := by
    have : x ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
      rw [← hset]
      exact le_of_eq hgx
    exact this
  have hf_ge : a ≤ f x := by
    rw [← hgx]
    exact hg_le x
  exact le_antisymm hf_le hf_ge

theorem sublevelSetEq_boundary_imp_boundary_of_le {m : ℕ} (g f : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg_f : ∀ x : MorseModel (m + 1), f x = a → fderiv ℝ f x ≠ 0)
    (hset : {x : MorseModel (m + 1) | g x ≤ a} = {x : MorseModel (m + 1) | f x ≤ a})
    (x : MorseModel (m + 1)) (hfx : f x = a) : g x = a := by
  by_contra hne
  have hgxle : g x ≤ a := by
    change x ∈ {x : MorseModel (m + 1) | g x ≤ a}
    rw [hset]
    exact le_of_eq hfx
  have hgxlt : g x < a := lt_of_le_of_ne hgxle hne
  have hint : x ∈ interior {y : MorseModel (m + 1) | f y ≤ a} := by
    have hsub : {y : MorseModel (m + 1) | g y < a} ⊆
        {y : MorseModel (m + 1) | f y ≤ a} := by
      intro y hy
      change y ∈ {x : MorseModel (m + 1) | f x ≤ a}
      rw [← hset]
      change g y ≤ a
      exact le_of_lt (by change g y < a; exact hy)
    exact (interior_maximal hsub (isOpen_Iio.preimage hg.continuous)) hgxlt
  have hmax : IsLocalMax f x := by
    rw [IsLocalMax]
    have hnhd : {y : MorseModel (m + 1) | f y ≤ a} ∈ 𝓝 x :=
      mem_interior_iff_mem_nhds.mp hint
    filter_upwards [hnhd] with y hy
    rwa [← hfx] at hy
  have hder : fderiv ℝ f x = 0 := hmax.fderiv_eq_zero
  exact (hreg_f x hfx) hder


noncomputable def sublevelInteriorTransitionUnderlying {m : ℕ} (c₁ c₂ : ℝ) :
    MorseModel (m + 1) → MorseModel (m + 1) :=
  fun x => HAdd.hAdd (HAdd.hAdd x (HSMul.hSMul c₁ levelSetLastBasis))
    (HSMul.hSMul c₂ levelSetLastBasis)

theorem contDiff_sublevelInteriorTransitionUnderlying {m : ℕ} (c₁ c₂ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : MorseModel (m + 1) =>
      sublevelInteriorTransitionUnderlying (m := m) c₁ c₂ x) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : MorseModel (m + 1) =>
    HAdd.hAdd (HAdd.hAdd x (HSMul.hSMul c₁ levelSetLastBasis))
      (HSMul.hSMul c₂ levelSetLastBasis))
  fun_prop

theorem morseHalfSpaceShift_shift {m : ℕ} (c₁ c₂ : ℝ) (x : MorseModel (m + 1)) :
    morseHalfSpaceShift c₂ (morseHalfSpaceShift c₁ x) = sublevelInteriorTransitionUnderlying c₁ c₂ x := by
  ext i
  simp [morseHalfSpaceShift, sublevelInteriorTransitionUnderlying, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]

noncomputable def sublevelBoundaryInteriorTransitionUnderlying {m : ℕ}
    (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ : SublevelSpace g a) (hx₁ : g x₁.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hr₁ : fderiv ℝ g x₁.1 ≠ 0)
    (x₂ : SublevelSpace g a) (hx₂ : g x₂.1 < a) :
    MorseModel (m + 1) → MorseModel (m + 1) :=
  let d₁ := levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁
  fun x => morseHalfSpaceShift (sublevelInteriorShift g a x₂ hx₂ hg)
    (levelSetReindex d₁.e (d₁.ψ.symm (a - x (Fin.last m), levelSetSplitFst m x)))

theorem contDiffAt_sublevelBoundaryInteriorTransitionUnderlying {m : ℕ}
    (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ : SublevelSpace g a) (hx₁ : g x₁.1 = a)
    (x₂ : SublevelSpace g a) (hx₂ : g x₂.1 < a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hr₁ : fderiv ℝ g x₁.1 ≠ 0)
    {z : MorseModel (m + 1)}
    (hz : (a - z (Fin.last m), levelSetSplitFst m z) ∈
      (levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁).ψ.target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (sublevelBoundaryInteriorTransitionUnderlying g a x₁ hx₁ hg hr₁ x₂ hx₂) z := by
  classical
  let d₁ := levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁
  let e₁ : Fin (m + 1) ≃ Fin (m + 1) := d₁.e
  let ψ₁ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₁.ψ
  have hψ₁ : (ψ₁ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e₁ := d₁.hψ
  let t : ℝ := a - z (Fin.last m)
  let y' : MorseModel m := levelSetSplitFst m z
  let w₁ : MorseModel (m + 1) := ψ₁.symm (t, y')
  have hw₁src : w₁ ∈ ψ₁.source := ψ₁.map_target hz
  have hc₁' : (fderiv ℝ (fun v => g (levelSetReindex e₁ v)) w₁) levelSetLastBasis ≠ 0 := by
    rw [d₁.hψsource] at hw₁src
    exact hw₁src.2
  have hpair : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => (a - x (Fin.last m), levelSetSplitFst m x)) z := by
    have hc1 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : MorseModel (m + 1) => a - x (Fin.last m)) z := by fun_prop
    have hc2 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : MorseModel (m + 1) => levelSetSplitFst m x) z := by fun_prop
    exact hc1.prodMk hc2
  have hsymm₁ : ContDiffAt ℝ (⊤ : ℕ∞)
      (ψ₁.symm : (ℝ × MorseModel m) → MorseModel (m + 1)) (t, y') := by
    refine OpenPartialHomeomorph.contDiffAt_symm ψ₁
      (f₀' := levelSetChartDerivEquiv g e₁ w₁ hc₁') ?_ ?_ ?_
    · change (a - z (Fin.last m), levelSetSplitFst m z) ∈ ψ₁.target
      exact hz
    · rw [hψ₁]
      exact hasFDerivAt_levelSetChartMap g e₁ w₁ hg.contDiffAt hc₁'
    · rw [hψ₁]
      exact contDiffAt_levelSetChartMap g e₁ w₁ hg.contDiffAt
  have h₁ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => ψ₁.symm (a - x (Fin.last m), levelSetSplitFst m x)) z :=
    hsymm₁.comp z hpair
  have hlin₁ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun v : MorseModel (m + 1) => levelSetReindex e₁ v) (ψ₁.symm (t, y')) :=
    ((levelSetReindex e₁).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
  have h₂ : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => levelSetReindex e₁ (ψ₁.symm (a - x (Fin.last m),
        levelSetSplitFst m x))) z :=
    hlin₁.comp z h₁
  have hshift : ContDiffAt ℝ (⊤ : ℕ∞)
      (morseHalfSpaceShift (sublevelInteriorShift g a x₂ hx₂ hg))
      (levelSetReindex e₁ (ψ₁.symm (t, y'))) :=
    (contDiff_morseHalfSpaceShift (sublevelInteriorShift g a x₂ hx₂ hg)).contDiffAt
  simpa [sublevelBoundaryInteriorTransitionUnderlying, d₁, e₁, ψ₁] using
    hshift.comp z h₂

theorem contDiffOn_sublevelBoundaryInteriorTransitionUnderlying {m : ℕ}
    (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ : SublevelSpace g a) (hx₁ : g x₁.1 = a)
    (x₂ : SublevelSpace g a) (hx₂ : g x₂.1 < a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hr₁ : fderiv ℝ g x₁.1 ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sublevelBoundaryInteriorTransitionUnderlying g a x₁ hx₁ hg hr₁ x₂ hx₂)
      {x' : MorseModel (m + 1) | (a - x' (Fin.last m), levelSetSplitFst m x') ∈
        (levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁).ψ.target} := by
  rw [IsOpen.contDiffOn_iff (by
    have hcont : Continuous (fun x' : MorseModel (m + 1) =>
        (a - x' (Fin.last m), levelSetSplitFst m x')) := by
      have hc1 : Continuous (fun x' : MorseModel (m + 1) => a - x' (Fin.last m)) := by fun_prop
      have hc2 : Continuous (fun x' : MorseModel (m + 1) => levelSetSplitFst m x') := by fun_prop
      exact hc1.prodMk hc2
    exact (levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁).ψ.open_target.preimage hcont)]
  intro x' hx'
  exact contDiffAt_sublevelBoundaryInteriorTransitionUnderlying g a x₁ hx₁ x₂ hx₂ hg hr₁ hx'

theorem sublevelBoundaryInterior_transition_reduce {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ : SublevelSpace g a) (hx₁ : g x₁.1 = a) (x₂ : SublevelSpace g a) (hx₂ : g x₂.1 < a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hr₁ : fderiv ℝ g x₁.1 ≠ 0) {y : MorseModel (m + 1)}
    (hy : y ∈ ((morseModelWithCornersHalfSpace m).symm ⁻¹'
        ((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
          (sublevelInteriorChart g a x₂ hx₂ hg)).source ∩
      Set.range (morseModelWithCornersHalfSpace m))) :
    (morseModelWithCornersHalfSpace m) (((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
        (sublevelInteriorChart g a x₂ hx₂ hg)) ((morseModelWithCornersHalfSpace m).symm y)) =
      sublevelBoundaryInteriorTransitionUnderlying g a x₁ hx₁ hg hr₁ x₂ hx₂ y := by
  classical
  let d₁ := levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁
  let e₁ : Fin (m + 1) ≃ Fin (m + 1) := d₁.e
  let ψ₁ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₁.ψ
  let c₁ : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
    sublevelBoundaryChart g a x₁ hx₁ hg hr₁
  let c₂ : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
    sublevelInteriorChart g a x₂ hx₂ hg
  have hy1 : (morseModelWithCornersHalfSpace m).symm y ∈ (c₁.symm ≫ₕ c₂).source := hy.1
  have hy2 : y ∈ Set.range (morseModelWithCornersHalfSpace m) := hy.2
  have hy2' : 0 ≤ y (Fin.last m) := by
    rw [range_morseModelWithCornersHalfSpace] at hy2
    exact hy2
  let z : MorseHalfSpace m := ⟨y, hy2'⟩
  have hclamp : (morseModelWithCornersHalfSpace m).symm y = z := by
    apply Subtype.ext
    exact morseHalfSpaceClamp_of_mem m hy2'
  have hy1z : z ∈ (c₁.symm ≫ₕ c₂).source := by
    rw [hclamp] at hy1
    exact hy1
  have hz1 : z ∈ c₁.target := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.1
  have hz2 : c₁.symm z ∈ c₂.source := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.2
  rw [hclamp]
  rw [OpenPartialHomeomorph.trans_apply]
  change ((sublevelInteriorChart g a x₂ hx₂ hg) ((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm z) :
      MorseModel (m + 1)) = sublevelBoundaryInteriorTransitionUnderlying g a x₁ hx₁ hg hr₁ x₂ hx₂ y
  rw [sublevelInteriorChart_apply_value g a x₂ hx₂ hg
    ((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm z) (by
      exact hz2)]
  rw [sublevelBoundaryChart_symm_value g a x₁ hx₁ hg hr₁ hz1]
  change morseHalfSpaceShift (sublevelInteriorShift g a x₂ hx₂ hg)
      (levelSetReindex e₁ (ψ₁.symm (a - (z : MorseModel (m + 1)) (Fin.last m),
        levelSetSplitFst m (z : MorseModel (m + 1))))) =
    sublevelBoundaryInteriorTransitionUnderlying g a x₁ hx₁ hg hr₁ x₂ hx₂ y
  change morseHalfSpaceShift (sublevelInteriorShift g a x₂ hx₂ hg)
      (levelSetReindex e₁ (ψ₁.symm (a - y (Fin.last m), levelSetSplitFst m y))) =
    sublevelBoundaryInteriorTransitionUnderlying g a x₁ hx₁ hg hr₁ x₂ hx₂ y
  rfl

theorem contDiffOn_sublevelBoundaryInterior_transition {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {x₁ x₂ : SublevelSpace g a}
    (hx₁ : g x₁.1 = a) (hx₂ : g x₂.1 < a) (hr₁ : fderiv ℝ g x₁.1 ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘ (sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
          (sublevelInteriorChart g a x₂ hx₂ hg) ∘ (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
            (sublevelInteriorChart g a x₂ hx₂ hg)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  let I : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  let t : OpenPartialHomeomorph (MorseHalfSpace m) (MorseHalfSpace m) :=
    (sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ (sublevelInteriorChart g a x₂ hx₂ hg)
  refine contDiffOn_of_locally_contDiffOn ?_
  intro y hy
  let d₁ := levelSetChartData.mk g a ⟨x₁.1, hx₁⟩ hg hr₁
  let u : Set (MorseModel (m + 1)) :=
    {x' : MorseModel (m + 1) | (a - x' (Fin.last m), levelSetSplitFst m x') ∈ d₁.ψ.target}
  refine ⟨u, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun x' : MorseModel (m + 1) =>
        (a - x' (Fin.last m), levelSetSplitFst m x')) := by
      have hc1 : Continuous (fun x' : MorseModel (m + 1) => a - x' (Fin.last m)) := by fun_prop
      have hc2 : Continuous (fun x' : MorseModel (m + 1) => levelSetSplitFst m x') := by fun_prop
      exact hc1.prodMk hc2
    exact d₁.ψ.open_target.preimage hcont
  · have hy2 : y ∈ Set.range I := hy.2
    have hy2' : 0 ≤ y (Fin.last m) := by
      rw [range_morseModelWithCornersHalfSpace] at hy2
      exact hy2
    let z : MorseHalfSpace m := ⟨y, hy2'⟩
    have hclamp : I.symm y = z := by
      apply Subtype.ext
      exact morseHalfSpaceClamp_of_mem m hy2'
    have hy1 : I.symm y ∈ t.source := hy.1
    have hy1z : z ∈ t.source := by
      rw [hclamp] at hy1
      exact hy1
    have hz1 : z ∈ (sublevelBoundaryChart g a x₁ hx₁ hg hr₁).target := by
      rw [OpenPartialHomeomorph.trans_source] at hy1z
      exact hy1z.1
    change (a - (z : MorseModel (m + 1)) (Fin.last m), levelSetSplitFst m (z : MorseModel (m + 1))) ∈
      d₁.ψ.target
    exact hz1
  · have hunder : ContDiffOn ℝ (⊤ : ℕ∞)
        (sublevelBoundaryInteriorTransitionUnderlying g a x₁ hx₁ hg hr₁ x₂ hx₂) u :=
      contDiffOn_sublevelBoundaryInteriorTransitionUnderlying g a x₁ hx₁ x₂ hx₂ hg hr₁
    have hunder' : ContDiffOn ℝ (⊤ : ℕ∞)
        (sublevelBoundaryInteriorTransitionUnderlying g a x₁ hx₁ hg hr₁ x₂ hx₂)
        (I.symm ⁻¹' t.source ∩ Set.range I ∩ u) :=
      hunder.mono (by intro x' hx'; exact hx'.2)
    refine hunder'.congr ?_
    intro x' hx'
    change I (t (I.symm x')) = sublevelBoundaryInteriorTransitionUnderlying g a x₁ hx₁ hg hr₁ x₂ hx₂ x'
    exact sublevelBoundaryInterior_transition_reduce g a x₁ hx₁ x₂ hx₂ hg hr₁ hx'.1

noncomputable def sublevelInteriorBoundaryTransitionUnderlying {m : ℕ}
    (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ : SublevelSpace g a) (hx₁ : g x₁.1 < a)
    (x₂ : SublevelSpace g a) (hx₂ : g x₂.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hr₂ : fderiv ℝ g x₂.1 ≠ 0) :
    MorseModel (m + 1) → MorseModel (m + 1) :=
  let d₂ := levelSetChartData.mk g a ⟨x₂.1, hx₂⟩ hg hr₂
  fun x => levelSetSplit m (levelSetSplitFst m
    (levelSetReindex d₂.e (morseHalfSpaceShift (-(sublevelInteriorShift g a x₁ hx₁ hg)) x)),
      a - (d₂.ψ (levelSetReindex d₂.e (morseHalfSpaceShift (-(sublevelInteriorShift g a x₁ hx₁ hg)) x))).1)

theorem contDiff_sublevelInteriorBoundaryTransitionUnderlying {m : ℕ}
    (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ : SublevelSpace g a) (hx₁ : g x₁.1 < a)
    (x₂ : SublevelSpace g a) (hx₂ : g x₂.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hr₂ : fderiv ℝ g x₂.1 ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelInteriorBoundaryTransitionUnderlying g a x₁ hx₁ x₂ hx₂ hg hr₂) := by
  classical
  let d₂ := levelSetChartData.mk g a ⟨x₂.1, hx₂⟩ hg hr₂
  let e₂ : Fin (m + 1) ≃ Fin (m + 1) := d₂.e
  let ψ₂ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₂.ψ
  have hψ₂ : (ψ₂ : MorseModel (m + 1) → ℝ × MorseModel m) = levelSetChartMap g e₂ := d₂.hψ
  let c₁ : ℝ := sublevelInteriorShift g a x₁ hx₁ hg
  have hshift : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => morseHalfSpaceShift (-c₁) x) :=
    contDiff_morseHalfSpaceShift (-c₁)
  have hlin : ContDiff ℝ (⊤ : ℕ∞)
      (fun v : MorseModel (m + 1) => levelSetReindex e₂ v) :=
    (levelSetReindex e₂).toContinuousLinearEquiv.contDiff
  have h₁ : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => levelSetReindex e₂ (morseHalfSpaceShift (-c₁) x)) :=
    hlin.comp hshift
  have hψ₂all : ContDiff ℝ (⊤ : ℕ∞) (ψ₂ : MorseModel (m + 1) → ℝ × MorseModel m) := by
    rw [hψ₂]
    exact contDiff_levelSetChartMap g e₂ hg
  have h₂ : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => ψ₂ (levelSetReindex e₂ (morseHalfSpaceShift (-c₁) x))) :=
    hψ₂all.comp h₁
  have hsub : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => a - (ψ₂ (levelSetReindex e₂ (morseHalfSpaceShift (-c₁) x))).1) := by
    have hfst : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × MorseModel m => p.1) := by fun_prop
    have h₃ : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : MorseModel (m + 1) => (ψ₂ (levelSetReindex e₂ (morseHalfSpaceShift (-c₁) x))).1) :=
      hfst.comp h₂
    have hsub' : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => a - r) := by fun_prop
    exact hsub'.comp h₃
  have hpf : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => levelSetSplitFst m (levelSetReindex e₂
        (morseHalfSpaceShift (-c₁) x))) :=
    (levelSetSplitFst m).contDiff.comp h₁
  have hsplit : ContDiff ℝ (⊤ : ℕ∞) (levelSetSplit m) :=
    (levelSetSplit m).toContinuousLinearEquiv.contDiff
  simpa [sublevelInteriorBoundaryTransitionUnderlying, c₁, d₂, e₂, ψ₂] using
    hsplit.comp (hpf.prodMk hsub)

theorem sublevelInteriorBoundary_transition_reduce {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (x₁ : SublevelSpace g a) (hx₁ : g x₁.1 < a) (x₂ : SublevelSpace g a) (hx₂ : g x₂.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hr₂ : fderiv ℝ g x₂.1 ≠ 0) {y : MorseModel (m + 1)}
    (hy : y ∈ ((morseModelWithCornersHalfSpace m).symm ⁻¹'
        ((sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ
          (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)).source ∩
      Set.range (morseModelWithCornersHalfSpace m))) :
    (morseModelWithCornersHalfSpace m) (((sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ
        (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)) ((morseModelWithCornersHalfSpace m).symm y)) =
      sublevelInteriorBoundaryTransitionUnderlying g a x₁ hx₁ x₂ hx₂ hg hr₂ y := by
  classical
  let c₁ : ℝ := sublevelInteriorShift g a x₁ hx₁ hg
  let d₂ := levelSetChartData.mk g a ⟨x₂.1, hx₂⟩ hg hr₂
  let e₂ : Fin (m + 1) ≃ Fin (m + 1) := d₂.e
  let ψ₂ : OpenPartialHomeomorph (MorseModel (m + 1)) (ℝ × MorseModel m) := d₂.ψ
  let c₁ch : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
    sublevelInteriorChart g a x₁ hx₁ hg
  let c₂ch : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
    sublevelBoundaryChart g a x₂ hx₂ hg hr₂
  have hy1 : (morseModelWithCornersHalfSpace m).symm y ∈ (c₁ch.symm ≫ₕ c₂ch).source := hy.1
  have hy2 : y ∈ Set.range (morseModelWithCornersHalfSpace m) := hy.2
  have hy2' : 0 ≤ y (Fin.last m) := by
    rw [range_morseModelWithCornersHalfSpace] at hy2
    exact hy2
  let z : MorseHalfSpace m := ⟨y, hy2'⟩
  have hclamp : (morseModelWithCornersHalfSpace m).symm y = z := by
    apply Subtype.ext
    exact morseHalfSpaceClamp_of_mem m hy2'
  have hy1z : z ∈ (c₁ch.symm ≫ₕ c₂ch).source := by
    rw [hclamp] at hy1
    exact hy1
  have hz1 : z ∈ c₁ch.target := by
    rw [OpenPartialHomeomorph.trans_source] at hy1z
    exact hy1z.1
  have hsymm₁ : c₁ch.symm z =
      (⟨morseHalfSpaceShift (-c₁) (z : MorseModel (m + 1)), by
        have hg' : g (morseHalfSpaceShift (-c₁) (z : MorseModel (m + 1))) < a := by
          have hsub : Metric.ball x₁.1 (sublevelInteriorRadius g a x₁ hx₁ hg) ⊆
              {y : MorseModel (m + 1) | g y < a} := by
            exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
              ((isOpen_Iio.preimage hg.continuous).mem_nhds hx₁))).2
          exact hsub hz1
        exact le_of_lt hg'⟩ : SublevelSpace g a) := by
    rw [sublevelInteriorChart_symm_value g a x₁ hx₁ hg hz1]
  rw [hclamp]
  rw [OpenPartialHomeomorph.trans_apply]
  change ((sublevelBoundaryChart g a x₂ hx₂ hg hr₂) (c₁ch.symm z) : MorseModel (m + 1)) =
    sublevelInteriorBoundaryTransitionUnderlying g a x₁ hx₁ x₂ hx₂ hg hr₂ y
  rw [sublevelBoundaryChart_apply_value g a x₂ hx₂ hg hr₂ (c₁ch.symm z)]
  change levelSetSplit m (levelSetSplitFst m (levelSetReindex e₂ (c₁ch.symm z).1),
      a - (ψ₂ (levelSetReindex e₂ (c₁ch.symm z).1)).1) =
    sublevelInteriorBoundaryTransitionUnderlying g a x₁ hx₁ x₂ hx₂ hg hr₂ y
  rw [hsymm₁]
  change levelSetSplit m (levelSetSplitFst m (levelSetReindex e₂ (morseHalfSpaceShift (-c₁) y)),
      a - (ψ₂ (levelSetReindex e₂ (morseHalfSpaceShift (-c₁) y))).1) =
    sublevelInteriorBoundaryTransitionUnderlying g a x₁ hx₁ x₂ hx₂ hg hr₂ y
  rfl

theorem contDiffOn_sublevelInteriorBoundary_transition {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {x₁ x₂ : SublevelSpace g a}
    (hx₁ : g x₁.1 < a) (hx₂ : g x₂.1 = a) (hr₂ : fderiv ℝ g x₂.1 ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘ (sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ
          (sublevelBoundaryChart g a x₂ hx₂ hg hr₂) ∘ (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ
            (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  let I : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  let t : OpenPartialHomeomorph (MorseHalfSpace m) (MorseHalfSpace m) :=
    (sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)
  refine contDiffOn_of_locally_contDiffOn ?_
  intro y hy
  have hcont : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => sublevelInteriorBoundaryTransitionUnderlying g a x₁ hx₁ x₂ hx₂ hg hr₂ x)
      Set.univ :=
    (contDiff_sublevelInteriorBoundaryTransitionUnderlying g a x₁ hx₁ x₂ hx₂ hg hr₂).contDiffOn
  refine ⟨Set.univ, isOpen_univ, trivial, ?_⟩
  exact (hcont.mono (by intro x hx; trivial)).congr (by
    intro x' hx'
    change I (t (I.symm x')) = sublevelInteriorBoundaryTransitionUnderlying g a x₁ hx₁ x₂ hx₂ hg hr₂ x'
    exact sublevelInteriorBoundary_transition_reduce g a x₁ hx₁ x₂ hx₂ hg hr₂ hx'.1)

theorem contDiffOn_sublevelInteriorInterior_transition {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {x₁ x₂ : SublevelSpace g a}
    (hx₁ : g x₁.1 < a) (hx₂ : g x₂.1 < a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘ (sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ
          (sublevelInteriorChart g a x₂ hx₂ hg) ∘ (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ
            (sublevelInteriorChart g a x₂ hx₂ hg)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  let I : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  let t : OpenPartialHomeomorph (MorseHalfSpace m) (MorseHalfSpace m) :=
    (sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ (sublevelInteriorChart g a x₂ hx₂ hg)
  let c₁ : ℝ := sublevelInteriorShift g a x₁ hx₁ hg
  let c₂ : ℝ := sublevelInteriorShift g a x₂ hx₂ hg
  have hcont : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : MorseModel (m + 1) => sublevelInteriorTransitionUnderlying (m := m) (-c₁) c₂ x)
      Set.univ := by
    have hcont' : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : MorseModel (m + 1) => sublevelInteriorTransitionUnderlying (m := m) (-c₁) c₂ x) :=
      contDiff_sublevelInteriorTransitionUnderlying (-c₁) c₂
    exact hcont'.contDiffOn
  exact (hcont.mono (by intro x hx; trivial)).congr (by
    intro x' hx'
    change I (t (I.symm x')) = sublevelInteriorTransitionUnderlying (m := m) (-c₁) c₂ x'
    rw [sublevelInteriorInterior_transition_reduce g a x₁ x₂ hx₁ hx₂ hg hx']
    change morseHalfSpaceShift c₂ (morseHalfSpaceShift (-c₁) x') =
      sublevelInteriorTransitionUnderlying (m := m) (-c₁) c₂ x'
    rw [morseHalfSpaceShift_shift])

theorem sublevelInteriorInterior_transition_mem_contDiffGroupoid {m : ℕ}
    (g : MorseModel (m + 1) → ℝ) (a : ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {x₁ x₂ : SublevelSpace g a} (hx₁ : g x₁.1 < a) (hx₂ : g x₂.1 < a) :
    (sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ (sublevelInteriorChart g a x₂ hx₂ hg) ∈
      contDiffGroupoid (⊤ : ℕ∞) (morseModelWithCornersHalfSpace m) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · exact contDiffOn_sublevelInteriorInterior_transition g a hg hx₁ hx₂
  · rw [show ((sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ
        (sublevelInteriorChart g a x₂ hx₂ hg)).symm =
          (sublevelInteriorChart g a x₂ hx₂ hg).symm ≫ₕ
            (sublevelInteriorChart g a x₁ hx₁ hg) from by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
        rfl]
    rw [show ((sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ
        (sublevelInteriorChart g a x₂ hx₂ hg)).target =
          ((sublevelInteriorChart g a x₂ hx₂ hg).symm ≫ₕ
            (sublevelInteriorChart g a x₁ hx₁ hg)).source by
        rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source]
        rfl]
    exact contDiffOn_sublevelInteriorInterior_transition g a hg hx₂ hx₁

theorem sublevelBoundaryInterior_transition_mem_contDiffGroupoid {m : ℕ}
    (g : MorseModel (m + 1) → ℝ) (a : ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {x₁ x₂ : SublevelSpace g a} (hx₁ : g x₁.1 = a) (hx₂ : g x₂.1 < a)
    (hr₁ : fderiv ℝ g x₁.1 ≠ 0) :
    (sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ (sublevelInteriorChart g a x₂ hx₂ hg) ∈
      contDiffGroupoid (⊤ : ℕ∞) (morseModelWithCornersHalfSpace m) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · exact contDiffOn_sublevelBoundaryInterior_transition g a hg hx₁ hx₂ hr₁
  · rw [show ((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
        (sublevelInteriorChart g a x₂ hx₂ hg)).symm =
          (sublevelInteriorChart g a x₂ hx₂ hg).symm ≫ₕ
            (sublevelBoundaryChart g a x₁ hx₁ hg hr₁) from by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
        rfl]
    rw [show ((sublevelBoundaryChart g a x₁ hx₁ hg hr₁).symm ≫ₕ
        (sublevelInteriorChart g a x₂ hx₂ hg)).target =
          ((sublevelInteriorChart g a x₂ hx₂ hg).symm ≫ₕ
            (sublevelBoundaryChart g a x₁ hx₁ hg hr₁)).source by
        rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source]
        rfl]
    exact contDiffOn_sublevelInteriorBoundary_transition g a hg hx₂ hx₁ hr₁

theorem sublevelInteriorBoundary_transition_mem_contDiffGroupoid {m : ℕ}
    (g : MorseModel (m + 1) → ℝ) (a : ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {x₁ x₂ : SublevelSpace g a} (hx₁ : g x₁.1 < a) (hx₂ : g x₂.1 = a)
    (hr₂ : fderiv ℝ g x₂.1 ≠ 0) :
    (sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ (sublevelBoundaryChart g a x₂ hx₂ hg hr₂) ∈
      contDiffGroupoid (⊤ : ℕ∞) (morseModelWithCornersHalfSpace m) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · exact contDiffOn_sublevelInteriorBoundary_transition g a hg hx₁ hx₂ hr₂
  · rw [show ((sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ
        (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)).symm =
          (sublevelBoundaryChart g a x₂ hx₂ hg hr₂).symm ≫ₕ
            (sublevelInteriorChart g a x₁ hx₁ hg) from by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
        rfl]
    rw [show ((sublevelInteriorChart g a x₁ hx₁ hg).symm ≫ₕ
        (sublevelBoundaryChart g a x₂ hx₂ hg hr₂)).target =
          ((sublevelBoundaryChart g a x₂ hx₂ hg hr₂).symm ≫ₕ
            (sublevelInteriorChart g a x₁ hx₁ hg)).source by
        rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source]
        rfl]
    exact contDiffOn_sublevelBoundaryInterior_transition g a hg hx₂ hx₁ hr₂

theorem sublevelHasGroupoid {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0) :
    @HasGroupoid (MorseHalfSpace m) _ (SublevelSpace g a) _ (sublevelChartedSpace g a hg hreg)
      (contDiffGroupoid (⊤ : ℕ∞) (morseModelWithCornersHalfSpace m)) := by
  classical
  letI := sublevelChartedSpace g a hg hreg
  refine hasGroupoid_of_pregroupoid (contDiffPregroupoid (⊤ : ℕ∞) (morseModelWithCornersHalfSpace m)) ?_
  intro e e' he he'
  rcases he with ⟨x₁, rfl⟩
  rcases he' with ⟨x₂, rfl⟩
  by_cases hx₁ : g x₁.1 = a
  · by_cases hx₂ : g x₂.1 = a
    · simp only [dif_pos hx₁, dif_pos hx₂]
      exact contDiffOn_sublevelBoundaryChart_transition g a hg hx₁ hx₂ (hreg x₁.1 hx₁)
        (hreg x₂.1 hx₂)
    · simp only [dif_pos hx₁, dif_neg hx₂]
      exact contDiffOn_sublevelBoundaryInterior_transition g a hg hx₁
        (lt_of_le_of_ne (show g x₂.1 ≤ a from x₂.2) hx₂) (hreg x₁.1 hx₁)
  · by_cases hx₂ : g x₂.1 = a
    · simp only [dif_neg hx₁, dif_pos hx₂]
      exact contDiffOn_sublevelInteriorBoundary_transition g a hg
        (lt_of_le_of_ne (show g x₁.1 ≤ a from x₁.2) hx₁) hx₂ (hreg x₂.1 hx₂)
    · simp only [dif_neg hx₁, dif_neg hx₂]
      exact contDiffOn_sublevelInteriorInterior_transition g a hg
        (lt_of_le_of_ne (show g x₁.1 ≤ a from x₁.2) hx₁)
        (lt_of_le_of_ne (show g x₂.1 ≤ a from x₂.2) hx₂)

theorem sublevelIsManifold {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0) :
    @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (⊤ : ℕ∞) (SublevelSpace g a) _ (sublevelChartedSpace g a hg hreg) := by
  letI := sublevelChartedSpace g a hg hreg
  exact { toHasGroupoid := sublevelHasGroupoid g a hg hreg }

theorem sublevelBoundaryMap_chart_value {m : ℕ} (g₁ g₂ : MorseModel (m + 1) → ℝ)
    (a₁ a₂ : ℝ) (x₁ : SublevelSpace g₁ a₁) (hx₁ : g₁ x₁.1 = a₁)
    (hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁) (hr₁ : fderiv ℝ g₁ x₁.1 ≠ 0)
    (x₂ : SublevelSpace g₂ a₂) (hx₂ : g₂ x₂.1 = a₂)
    (hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂) (hr₂ : fderiv ℝ g₂ x₂.1 ≠ 0)
    (Φ : MorseModel (m + 1) → MorseModel (m + 1))
    (hmap : ∀ y : MorseModel (m + 1), g₁ y ≤ a₁ → g₂ (Φ y) ≤ a₂)
    {z : MorseModel (m + 1)} (hzmem : 0 ≤ z (Fin.last m))
    (hz₁ : z ∈ sublevelBoundaryChartDomain g₁ a₁ x₁ hx₁ hg₁ hr₁) :
    (morseModelWithCornersHalfSpace m)
      ((sublevelBoundaryChart g₂ a₂ x₂ hx₂ hg₂ hr₂)
        ((fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂))
          ((sublevelBoundaryChart g₁ a₁ x₁ hx₁ hg₁ hr₁).symm
            (⟨z, hzmem⟩ : MorseHalfSpace m)))) =
      sublevelBoundaryChartValue g₂ a₂ x₂ hx₂ hg₂ hr₂
        (Φ (sublevelBoundaryChartInvValueRaw g₁ a₁ x₁ hx₁ hg₁ hr₁ z)) := by
  classical
  let c₁ : OpenPartialHomeomorph (SublevelSpace g₁ a₁) (MorseHalfSpace m) :=
    sublevelBoundaryChart g₁ a₁ x₁ hx₁ hg₁ hr₁
  let c₂ : OpenPartialHomeomorph (SublevelSpace g₂ a₂) (MorseHalfSpace m) :=
    sublevelBoundaryChart g₂ a₂ x₂ hx₂ hg₂ hr₂
  let z' : MorseHalfSpace m := ⟨z, hzmem⟩
  have hz1 : z' ∈ c₁.target := hz₁
  have hmem₁ : g₁ (sublevelBoundaryChartInvValueRaw g₁ a₁ x₁ hx₁ hg₁ hr₁ z) ≤ a₁ := by
    change g₁ (levelSetReindex (levelSetChartData.mk g₁ a₁ ⟨x₁.1, hx₁⟩ hg₁ hr₁).e
        ((levelSetChartData.mk g₁ a₁ ⟨x₁.1, hx₁⟩ hg₁ hr₁).ψ.symm
          (a₁ - (z' : MorseModel (m + 1)) (Fin.last m),
            levelSetSplitFst m (z' : MorseModel (m + 1))))) ≤ a₁
    exact sublevelBoundaryChart_invFun_mem g₁
      (levelSetChartData.mk g₁ a₁ ⟨x₁.1, hx₁⟩ hg₁ hr₁).e a₁
      (levelSetChartData.mk g₁ a₁ ⟨x₁.1, hx₁⟩ hg₁ hr₁).ψ
      (levelSetChartData.mk g₁ a₁ ⟨x₁.1, hx₁⟩ hg₁ hr₁).hψ
      (by
        simpa [z', sublevelBoundaryChartDomain] using hz₁)
  have hsymm₁ : c₁.symm z' = (⟨sublevelBoundaryChartInvValueRaw g₁ a₁ x₁ hx₁ hg₁ hr₁ z, hmem₁⟩ :
      SublevelSpace g₁ a₁) := by
    rw [sublevelBoundaryChart_symm_value g₁ a₁ x₁ hx₁ hg₁ hr₁ hz1]
    apply Subtype.ext
    rfl
  have hmem₂ : g₂ (Φ (sublevelBoundaryChartInvValueRaw g₁ a₁ x₁ hx₁ hg₁ hr₁ z)) ≤ a₂ :=
    hmap (sublevelBoundaryChartInvValueRaw g₁ a₁ x₁ hx₁ hg₁ hr₁ z) hmem₁
  have hval₂ : (morseModelWithCornersHalfSpace m)
      (c₂ ((fun y : SublevelSpace g₁ a₁ =>
          (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂))
          (⟨sublevelBoundaryChartInvValueRaw g₁ a₁ x₁ hx₁ hg₁ hr₁ z, hmem₁⟩ :
            SublevelSpace g₁ a₁))) =
      sublevelBoundaryChartValue g₂ a₂ x₂ hx₂ hg₂ hr₂
        (Φ (sublevelBoundaryChartInvValueRaw g₁ a₁ x₁ hx₁ hg₁ hr₁ z)) := by
    change (c₂ (⟨Φ (sublevelBoundaryChartInvValueRaw g₁ a₁ x₁ hx₁ hg₁ hr₁ z), hmem₂⟩ :
        SublevelSpace g₂ a₂) : MorseModel (m + 1)) =
      sublevelBoundaryChartValue g₂ a₂ x₂ hx₂ hg₂ hr₂
        (Φ (sublevelBoundaryChartInvValueRaw g₁ a₁ x₁ hx₁ hg₁ hr₁ z))
    rw [sublevelBoundaryChart_apply_value']
  change (morseModelWithCornersHalfSpace m)
    (c₂ ((fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂))
      (c₁.symm z'))) =
      sublevelBoundaryChartValue g₂ a₂ x₂ hx₂ hg₂ hr₂
        (Φ (sublevelBoundaryChartInvValueRaw g₁ a₁ x₁ hx₁ hg₁ hr₁ z))
  rw [hsymm₁]
  rw [hval₂]

theorem contMDiffAt_sublevelBoundaryMap {m : ℕ} (g₁ g₂ : MorseModel (m + 1) → ℝ)
    (a₁ a₂ : ℝ) (hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁) (hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂)
    (hr₁ : ∀ x : MorseModel (m + 1), g₁ x = a₁ → fderiv ℝ g₁ x ≠ 0)
    (hr₂ : ∀ x : MorseModel (m + 1), g₂ x = a₂ → fderiv ℝ g₂ x ≠ 0)
    (x : SublevelSpace g₁ a₁) (hx : g₁ x.1 = a₁)
    (Φ : MorseModel (m + 1) → MorseModel (m + 1)) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hmap : ∀ y : MorseModel (m + 1), g₁ y ≤ a₁ → g₂ (Φ y) ≤ a₂)
    (hbnd : ∀ y : MorseModel (m + 1), g₁ y = a₁ → g₂ (Φ y) = a₂)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₁ a₁) :=
      sublevelChartedSpace g₁ a₁ hg₁ hr₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₂ a₂) :=
      sublevelChartedSpace g₂ a₂ hg₂ hr₂)
    (hchart₁ : ∀ y : SublevelSpace g₁ a₁, hcs₁.chartAt y =
      (if h : g₁ y.1 = a₁ then sublevelBoundaryChart g₁ a₁ y h hg₁ (hr₁ y.1 h)
        else sublevelInteriorChart g₁ a₁ y (lt_of_le_of_ne (show g₁ y.1 ≤ a₁ from y.2) h) hg₁) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g₂ a₂, hcs₂.chartAt y =
      (if h : g₂ y.1 = a₂ then sublevelBoundaryChart g₂ a₂ y h hg₂ (hr₂ y.1 h)
        else sublevelInteriorChart g₂ a₂ y (lt_of_le_of_ne (show g₂ y.1 ≤ a₂ from y.2) h) hg₂) := by
      intro y
      rfl) :
    ContMDiffAt (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) x := by
  letI := hcs₁
  letI := hcs₂
  rw [contMDiffAt_iff]
  constructor
  · have hcont : Continuous (fun y : SublevelSpace g₁ a₁ => Φ y.1) :=
      hΦ.continuous.comp continuous_subtype_val
    exact (Continuous.subtype_mk hcont (fun y => hmap y.1 y.2)).continuousAt
  · let c₁ : OpenPartialHomeomorph (SublevelSpace g₁ a₁) (MorseHalfSpace m) :=
      sublevelBoundaryChart g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
    let c₂ : OpenPartialHomeomorph (SublevelSpace g₂ a₂) (MorseHalfSpace m) :=
      sublevelBoundaryChart g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ (hbnd x.1 hx) hg₂
        (hr₂ (Φ x.1) (hbnd x.1 hx))
    have hchart₁' : hcs₁.chartAt x = c₁ := by
      rw [hchart₁ x]
      rw [dif_pos hx]
    have hchart₂' : hcs₂.chartAt (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂) = c₂ := by
      rw [hchart₂ ⟨Φ x.1, hmap x.1 x.2⟩]
      rw [dif_pos (hbnd x.1 hx)]
    let ψ₁ : MorseModel (m + 1) → MorseModel (m + 1) :=
      sublevelBoundaryChartInvValueRaw g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
    let ψ₂ : MorseModel (m + 1) → MorseModel (m + 1) :=
      sublevelBoundaryChartValue g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ (hbnd x.1 hx) hg₂
        (hr₂ (Φ x.1) (hbnd x.1 hx))
    let D₁ : Set (MorseModel (m + 1)) := sublevelBoundaryChartDomain g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
    let D₂ : Set (MorseModel (m + 1)) := sublevelBoundaryChartDomain g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩
      (hbnd x.1 hx) hg₂ (hr₂ (Φ x.1) (hbnd x.1 hx))
    let F : MorseModel (m + 1) → MorseModel (m + 1) := fun z => ψ₂ (Φ (ψ₁ z))
    have hψ₁cd : ContDiffOn ℝ (⊤ : ℕ∞) ψ₁ D₁ :=
      contDiffOn_sublevelBoundaryChartInvValueRaw g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
    have hψ₂cd : ContDiffOn ℝ (⊤ : ℕ∞) ψ₂ D₂ :=
      (contDiff_sublevelBoundaryChartValue g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ (hbnd x.1 hx) hg₂
        (hr₂ (Φ x.1) (hbnd x.1 hx))).contDiffOn
    have hF : ContDiffOn ℝ (⊤ : ℕ∞) F D₁ := by
      have hcomp₁ : ContDiffOn ℝ (⊤ : ℕ∞) (Φ ∘ ψ₁) D₁ := by
        have hcompD₁ : ContDiffOn ℝ (⊤ : ℕ∞) (Φ ∘ ψ₁) D₁ :=
          hΦ.contDiffOn.comp hψ₁cd (by intro z hz; exact Set.mem_univ (ψ₁ z))
        exact hcompD₁
      have hψ₂global : ContDiff ℝ (⊤ : ℕ∞) ψ₂ :=
        contDiff_sublevelBoundaryChartValue g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ (hbnd x.1 hx) hg₂
          (hr₂ (Φ x.1) (hbnd x.1 hx))
      exact hψ₂global.contDiffOn.comp hcomp₁ (by intro z hz; exact Set.mem_univ ((Φ ∘ ψ₁) z))
    have hD₁open : IsOpen D₁ := isOpen_sublevelBoundaryChartDomain g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
    have hD₂open : IsOpen D₂ := isOpen_sublevelBoundaryChartDomain g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩
      (hbnd x.1 hx) hg₂ (hr₂ (Φ x.1) (hbnd x.1 hx))
    have hc₁src : x ∈ c₁.source := mem_sublevelBoundaryChart_source g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
    have hz₀I : (extChartAt (morseModelWithCornersHalfSpace m) x x) =
        (morseModelWithCornersHalfSpace m) (c₁ x) := by
      simp [extChartAt, hchart₁']
    have hz₀range : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
        Set.range (morseModelWithCornersHalfSpace m) := by
      simp [extChartAt, hchart₁']
    have hz₀D₁ : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈ D₁ := by
      have hsrc : x ∈ c₁.source := hc₁src
      have htgt : (c₁ x : MorseHalfSpace m) ∈ c₁.target := c₁.map_source hsrc
      simpa [extChartAt, hchart₁', D₁, sublevelBoundaryChartDomain] using htgt
    have hred : (morseModelWithCornersHalfSpace m ∘ c₂ ∘
        (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
        c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm) =ᶠ[
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m))] F := by
      have hnhd₁ : D₁ ∩ Set.range (morseModelWithCornersHalfSpace m) ∈
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m)) := by
        have hnhd₁' : D₁ ∈ nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m)) := by
          exact nhdsWithin_le_nhds (hD₁open.mem_nhds hz₀D₁)
        exact Filter.inter_mem hnhd₁' self_mem_nhdsWithin
      refine Filter.eventuallyEq_of_mem (s := D₁ ∩ Set.range (morseModelWithCornersHalfSpace m))
        hnhd₁ ?_
      intro z hz
      have hzD₁ : z ∈ D₁ := hz.1
      have hzrange : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.2
      have hzmem : 0 ≤ z (Fin.last m) := by
        rw [range_morseModelWithCornersHalfSpace] at hzrange
        exact hzrange
      change (morseModelWithCornersHalfSpace m)
          (sublevelBoundaryChart g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ (hbnd x.1 hx) hg₂
            (hr₂ (Φ x.1) (hbnd x.1 hx))
            ((fun y : SublevelSpace g₁ a₁ =>
              (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂))
              ((sublevelBoundaryChart g₁ a₁ x hx hg₁ (hr₁ x.1 hx)).symm
                ((morseModelWithCornersHalfSpace m).symm z)))) = F z
      have hsymmz : ((morseModelWithCornersHalfSpace m).symm z) =
          (⟨z, hzmem⟩ : MorseHalfSpace m) := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hzmem
      rw [hsymmz]
      rw [sublevelBoundaryMap_chart_value g₁ g₂ a₁ a₂ x hx hg₁ (hr₁ x.1 hx)
        ⟨Φ x.1, hmap x.1 x.2⟩ (hbnd x.1 hx) hg₂ (hr₂ (Φ x.1) (hbnd x.1 hx))
        Φ hmap hzmem hzD₁]
    have hFAt : ContDiffWithinAt ℝ (⊤ : ℕ∞)
        (fun z : MorseModel (m + 1) => ψ₂ (Φ (ψ₁ z)))
        (Set.range (morseModelWithCornersHalfSpace m))
        (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      have hnhd₁' : D₁ ∈ nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m)) := by
        exact nhdsWithin_le_nhds (hD₁open.mem_nhds hz₀D₁)
      exact hF.contDiffWithinAt hz₀D₁ |>.mono_of_mem_nhdsWithin hnhd₁'
    refine hFAt.congr_of_eventuallyEq_of_mem ?_ hz₀range
    change ((extChartAt (morseModelWithCornersHalfSpace m)
        (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂)) ∘
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
      (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m))]
      (fun z : MorseModel (m + 1) => ψ₂ (Φ (ψ₁ z)))
    change (((hcs₂.chartAt (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂)).extend
        (morseModelWithCornersHalfSpace m)) ∘
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
      ((hcs₁.chartAt x).extend (morseModelWithCornersHalfSpace m)).symm) =ᶠ[
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m))]
      (fun z : MorseModel (m + 1) => ψ₂ (Φ (ψ₁ z)))
    rw [hchart₂']
    rw [hchart₁']
    rw [OpenPartialHomeomorph.extend_coe]
    rw [OpenPartialHomeomorph.extend_coe_symm]
    simpa using hred

theorem contMDiff_sublevelSetEqMap {m : ℕ} (g f : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hreg_g : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0)
    (hreg_f : ∀ x : MorseModel (m + 1), f x = a → fderiv ℝ f x ≠ 0)
    (hset : {x : MorseModel (m + 1) | g x ≤ a} = {x : MorseModel (m + 1) | f x ≤ a})
    (hbnd : ∀ x : MorseModel (m + 1), g x = a → f x = a)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) :=
      sublevelChartedSpace g a hg hreg_g)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f a) :=
      sublevelChartedSpace f a hf hreg_f)
    (hchart₁ : ∀ y : SublevelSpace g a, hcs₁.chartAt y =
      (if h : g y.1 = a then sublevelBoundaryChart g a y h hg (hreg_g y.1 h)
        else sublevelInteriorChart g a y (lt_of_le_of_ne (show g y.1 ≤ a from y.2) h) hg) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace f a, hcs₂.chartAt y =
      (if h : f y.1 = a then sublevelBoundaryChart f a y h hf (hreg_f y.1 h)
        else sublevelInteriorChart f a y (lt_of_le_of_ne (show f y.1 ≤ a from y.2) h) hf) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g a => (⟨y.1, by
        have : y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
          rw [← hset]
          exact y.2
        exact this⟩ : SublevelSpace f a)) := by
  intro x
  by_cases hx : g x.1 = a
  · exact contMDiffAt_sublevelBoundaryMap g f a a hg hf hreg_g hreg_f x hx id contDiff_id
      (fun y hy => by
        change f y ≤ a
        have : y ∈ {x : MorseModel (m + 1) | f x ≤ a} := by
          rw [← hset]
          exact hy
        exact this)
      (fun y hy => hbnd y hy)
      (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
  · have hxlt : g x.1 < a := lt_of_le_of_ne (show g x.1 ≤ a from x.2) hx
    exact contMDiffAt_sublevelSetEqIdentityInterior g f a hg hf hreg_g hreg_f hset x hxlt
      (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)

theorem sublevelSetEqDiffeomorph {m : ℕ} (g f : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hreg_g : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0)
    (hreg_f : ∀ x : MorseModel (m + 1), f x = a → fderiv ℝ f x ≠ 0)
    (hset : {x : MorseModel (m + 1) | g x ≤ a} = {x : MorseModel (m + 1) | f x ≤ a})
    (hg_le : ∀ x : MorseModel (m + 1), g x ≤ f x)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) :=
      sublevelChartedSpace g a hg hreg_g)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f a) :=
      sublevelChartedSpace f a hf hreg_f)
    (hchart₁ : ∀ y : SublevelSpace g a, hcs₁.chartAt y =
      (if h : g y.1 = a then sublevelBoundaryChart g a y h hg (hreg_g y.1 h)
        else sublevelInteriorChart g a y (lt_of_le_of_ne (show g y.1 ≤ a from y.2) h) hg) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace f a, hcs₂.chartAt y =
      (if h : f y.1 = a then sublevelBoundaryChart f a y h hf (hreg_f y.1 h)
        else sublevelInteriorChart f a y (lt_of_le_of_ne (show f y.1 ≤ a from y.2) h) hf) := by
      intro y
      rfl) :
    Nonempty (@Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace g a) _ hcs₁ (SublevelSpace f a) _ hcs₂ (⊤ : ℕ∞)) := by
  classical
  letI := hcs₁
  letI := hcs₂
  let toFun : SublevelSpace g a → SublevelSpace f a := fun y => ⟨y.1, by
    change y.1 ∈ {x : MorseModel (m + 1) | f x ≤ a}
    rw [← hset]
    exact y.2⟩
  let invFun : SublevelSpace f a → SublevelSpace g a := fun y => ⟨y.1, by
    change y.1 ∈ {x : MorseModel (m + 1) | g x ≤ a}
    rw [hset]
    exact y.2⟩
  let e : SublevelSpace g a ≃ SublevelSpace f a :=
    { toFun := toFun, invFun := invFun, left_inv := by intro y; rfl,
      right_inv := by intro y; rfl }
  have hbnd' : ∀ x : MorseModel (m + 1), f x = a → g x = a := by
    exact sublevelSetEq_boundary_imp_boundary_of_le g f a hg hreg_f hset
  have hto : ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      toFun := by
    simpa [toFun] using contMDiff_sublevelSetEqMap g f a hg hf hreg_g hreg_f hset
      (sublevelSetEq_boundary_imp_boundary g f a hset hg_le)
      (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
  have hinv : ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      invFun := by
    simpa [invFun] using contMDiff_sublevelSetEqMap f g a hf hg hreg_f hreg_g hset.symm hbnd'
      (hcs₁ := hcs₂) (hcs₂ := hcs₁) (hchart₁ := hchart₂) (hchart₂ := hchart₁)
  let d : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace g a) _ hcs₁ (SublevelSpace f a) _ hcs₂ (⊤ : ℕ∞) := by
    refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
    · simpa [toFun] using hto
    · simpa [invFun] using hinv
  exact ⟨d⟩

theorem contMDiffAt_sublevelBoundaryMap_on {m : ℕ} (g₁ g₂ : MorseModel (m + 1) → ℝ)
    (a₁ a₂ : ℝ) (hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁) (hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂)
    (hr₁ : ∀ x : MorseModel (m + 1), g₁ x = a₁ → fderiv ℝ g₁ x ≠ 0)
    (hr₂ : ∀ x : MorseModel (m + 1), g₂ x = a₂ → fderiv ℝ g₂ x ≠ 0)
    (x : SublevelSpace g₁ a₁) (hx : g₁ x.1 = a₁)
    (Φ : MorseModel (m + 1) → MorseModel (m + 1)) (U : Set (MorseModel (m + 1)))
    (hUopen : IsOpen U) (hUsub : ∀ y : MorseModel (m + 1), g₁ y ≤ a₁ → y ∈ U)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ U)
    (hmap : ∀ y : MorseModel (m + 1), g₁ y ≤ a₁ → g₂ (Φ y) ≤ a₂)
    (hbnd : ∀ y : MorseModel (m + 1), g₁ y = a₁ → g₂ (Φ y) = a₂)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₁ a₁) :=
      sublevelChartedSpace g₁ a₁ hg₁ hr₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₂ a₂) :=
      sublevelChartedSpace g₂ a₂ hg₂ hr₂)
    (hchart₁ : ∀ y : SublevelSpace g₁ a₁, hcs₁.chartAt y =
      (if h : g₁ y.1 = a₁ then sublevelBoundaryChart g₁ a₁ y h hg₁ (hr₁ y.1 h)
        else sublevelInteriorChart g₁ a₁ y (lt_of_le_of_ne (show g₁ y.1 ≤ a₁ from y.2) h) hg₁) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g₂ a₂, hcs₂.chartAt y =
      (if h : g₂ y.1 = a₂ then sublevelBoundaryChart g₂ a₂ y h hg₂ (hr₂ y.1 h)
        else sublevelInteriorChart g₂ a₂ y (lt_of_le_of_ne (show g₂ y.1 ≤ a₂ from y.2) h) hg₂) := by
      intro y
      rfl) :
    ContMDiffAt (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) x := by
  letI := hcs₁
  letI := hcs₂
  rw [contMDiffAt_iff]
  constructor
  · have hcontOn : ContinuousOn (fun y : SublevelSpace g₁ a₁ => Φ y.1) Set.univ := by
      have hcomp : ContinuousOn (fun y : SublevelSpace g₁ a₁ => Φ (y.1)) Set.univ :=
        (ContDiffOn.continuousOn hΦ).comp continuous_subtype_val.continuousOn (by
          intro y hy
          exact hUsub y.1 y.2)
      simpa using hcomp
    have hcont : Continuous (fun y : SublevelSpace g₁ a₁ => Φ y.1) := continuousOn_univ.mp hcontOn
    exact (Continuous.subtype_mk hcont (fun y => hmap y.1 y.2)).continuousAt
  · let c₁ : OpenPartialHomeomorph (SublevelSpace g₁ a₁) (MorseHalfSpace m) :=
      sublevelBoundaryChart g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
    let c₂ : OpenPartialHomeomorph (SublevelSpace g₂ a₂) (MorseHalfSpace m) :=
      sublevelBoundaryChart g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ (hbnd x.1 hx) hg₂
        (hr₂ (Φ x.1) (hbnd x.1 hx))
    have hchart₁' : hcs₁.chartAt x = c₁ := by
      rw [hchart₁ x]
      rw [dif_pos hx]
    have hchart₂' : hcs₂.chartAt (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂) = c₂ := by
      rw [hchart₂ ⟨Φ x.1, hmap x.1 x.2⟩]
      rw [dif_pos (hbnd x.1 hx)]
    let ψ₁ : MorseModel (m + 1) → MorseModel (m + 1) :=
      sublevelBoundaryChartInvValueRaw g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
    let ψ₂ : MorseModel (m + 1) → MorseModel (m + 1) :=
      sublevelBoundaryChartValue g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ (hbnd x.1 hx) hg₂
        (hr₂ (Φ x.1) (hbnd x.1 hx))
    let D₁ : Set (MorseModel (m + 1)) := sublevelBoundaryChartDomain g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
    let D₁' : Set (MorseModel (m + 1)) := D₁ ∩ (ψ₁ ⁻¹' U)
    let D₂ : Set (MorseModel (m + 1)) := sublevelBoundaryChartDomain g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩
      (hbnd x.1 hx) hg₂ (hr₂ (Φ x.1) (hbnd x.1 hx))
    let F : MorseModel (m + 1) → MorseModel (m + 1) := fun z => ψ₂ (Φ (ψ₁ z))
    have hψ₁cd : ContDiffOn ℝ (⊤ : ℕ∞) ψ₁ D₁ :=
      contDiffOn_sublevelBoundaryChartInvValueRaw g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
    have hψ₂cd : ContDiffOn ℝ (⊤ : ℕ∞) ψ₂ D₂ :=
      (contDiff_sublevelBoundaryChartValue g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ (hbnd x.1 hx) hg₂
        (hr₂ (Φ x.1) (hbnd x.1 hx))).contDiffOn
    have hD₁open : IsOpen D₁ := isOpen_sublevelBoundaryChartDomain g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
    have hD₂open : IsOpen D₂ := isOpen_sublevelBoundaryChartDomain g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩
      (hbnd x.1 hx) hg₂ (hr₂ (Φ x.1) (hbnd x.1 hx))
    have hD₁'open : IsOpen D₁' := by
      simpa [D₁'] using (hψ₁cd.continuousOn.isOpen_inter_preimage hD₁open hUopen)
    have hc₁src : x ∈ c₁.source := mem_sublevelBoundaryChart_source g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
    have hz₀I : (extChartAt (morseModelWithCornersHalfSpace m) x x) =
        (morseModelWithCornersHalfSpace m) (c₁ x) := by
      simp [extChartAt, hchart₁']
    have hz₀range : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
        Set.range (morseModelWithCornersHalfSpace m) := by
      simp [extChartAt, hchart₁']
    have hz₀D₁ : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈ D₁ := by
      have hsrc : x ∈ c₁.source := hc₁src
      have htgt : (c₁ x : MorseHalfSpace m) ∈ c₁.target := c₁.map_source hsrc
      simpa [extChartAt, hchart₁', D₁, sublevelBoundaryChartDomain] using htgt
    have hψ₁z₀ : ψ₁ ((extChartAt (morseModelWithCornersHalfSpace m) x x)) = x.1 := by
      have hz₀mem : 0 ≤ (extChartAt (morseModelWithCornersHalfSpace m) x x) (Fin.last m) := by
        rw [range_morseModelWithCornersHalfSpace] at hz₀range
        exact hz₀range
      have hz₀chart : (⟨(extChartAt (morseModelWithCornersHalfSpace m) x x), hz₀mem⟩ : MorseHalfSpace m) = c₁ x := by
        apply Subtype.ext
        dsimp [extChartAt]
        change (morseModelWithCornersHalfSpace m) ((hcs₁.chartAt x) x) = (c₁ x : MorseModel (m + 1))
        rw [hchart₁']
        rfl
      have hz₀tar : (⟨(extChartAt (morseModelWithCornersHalfSpace m) x x), hz₀mem⟩ : MorseHalfSpace m) ∈ c₁.target := by
        rw [hz₀chart]
        exact c₁.map_source hc₁src
      have hleft : sublevelBoundaryChartInvValueRaw g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
            (extChartAt (morseModelWithCornersHalfSpace m) x x) =
          (c₁.symm (⟨(extChartAt (morseModelWithCornersHalfSpace m) x x), hz₀mem⟩ : MorseHalfSpace m)).1 := by
        rw [sublevelBoundaryChart_symm_value g₁ a₁ x hx hg₁ (hr₁ x.1 hx) hz₀tar]
        rfl
      calc
        ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x)
            = sublevelBoundaryChartInvValueRaw g₁ a₁ x hx hg₁ (hr₁ x.1 hx)
                (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
              rfl
        _ = (c₁.symm (⟨(extChartAt (morseModelWithCornersHalfSpace m) x x), hz₀mem⟩ : MorseHalfSpace m)).1 := hleft
        _ = x.1 := by
              rw [hz₀chart]
              exact congrArg Subtype.val (c₁.left_inv hc₁src)
    have hz₀D₁' : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈ D₁' := by
      exact ⟨hz₀D₁, by
        change ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈ U
        rw [hψ₁z₀]
        exact hUsub x.1 x.2⟩
    have hF : ContDiffOn ℝ (⊤ : ℕ∞) F D₁' := by
      have hcomp₁ : ContDiffOn ℝ (⊤ : ℕ∞) (Φ ∘ ψ₁) D₁' := by
        exact ContDiffOn.comp hΦ (hψ₁cd.mono (by intro z hz; exact hz.1)) (by intro z hz; exact hz.2)
      have hψ₂global : ContDiff ℝ (⊤ : ℕ∞) ψ₂ :=
        contDiff_sublevelBoundaryChartValue g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ (hbnd x.1 hx) hg₂
          (hr₂ (Φ x.1) (hbnd x.1 hx))
      exact hψ₂global.contDiffOn.comp hcomp₁ (by intro z hz; exact Set.mem_univ ((Φ ∘ ψ₁) z))
    have hred : (morseModelWithCornersHalfSpace m ∘ c₂ ∘
        (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
        c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm) =ᶠ[
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m))] F := by
      have hnhd₁ : D₁' ∩ Set.range (morseModelWithCornersHalfSpace m) ∈
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m)) := by
        have hnhd₁' : D₁' ∈ nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m)) := by
          exact nhdsWithin_le_nhds (hD₁'open.mem_nhds hz₀D₁')
        exact Filter.inter_mem hnhd₁' self_mem_nhdsWithin
      refine Filter.eventuallyEq_of_mem (s := D₁' ∩ Set.range (morseModelWithCornersHalfSpace m))
        hnhd₁ ?_
      intro z hz
      have hzD₁ : z ∈ D₁ := hz.1.1
      have hzrange : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.2
      have hzmem : 0 ≤ z (Fin.last m) := by
        rw [range_morseModelWithCornersHalfSpace] at hzrange
        exact hzrange
      change (morseModelWithCornersHalfSpace m)
          (sublevelBoundaryChart g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ (hbnd x.1 hx) hg₂
            (hr₂ (Φ x.1) (hbnd x.1 hx))
            ((fun y : SublevelSpace g₁ a₁ =>
              (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂))
              ((sublevelBoundaryChart g₁ a₁ x hx hg₁ (hr₁ x.1 hx)).symm
                ((morseModelWithCornersHalfSpace m).symm z)))) = F z
      have hsymmz : ((morseModelWithCornersHalfSpace m).symm z) =
          (⟨z, hzmem⟩ : MorseHalfSpace m) := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hzmem
      rw [hsymmz]
      rw [sublevelBoundaryMap_chart_value g₁ g₂ a₁ a₂ x hx hg₁ (hr₁ x.1 hx)
        ⟨Φ x.1, hmap x.1 x.2⟩ (hbnd x.1 hx) hg₂ (hr₂ (Φ x.1) (hbnd x.1 hx))
        Φ hmap hzmem hzD₁]
    have hFAt : ContDiffWithinAt ℝ (⊤ : ℕ∞)
        (fun z : MorseModel (m + 1) => ψ₂ (Φ (ψ₁ z)))
        (Set.range (morseModelWithCornersHalfSpace m))
        (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      have hnhd₁' : D₁' ∈ nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m)) := by
        exact nhdsWithin_le_nhds (hD₁'open.mem_nhds hz₀D₁')
      exact hF.contDiffWithinAt hz₀D₁' |>.mono_of_mem_nhdsWithin hnhd₁'
    refine hFAt.congr_of_eventuallyEq_of_mem ?_ hz₀range
    change ((extChartAt (morseModelWithCornersHalfSpace m)
        (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂)) ∘
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
      (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m))]
      (fun z : MorseModel (m + 1) => ψ₂ (Φ (ψ₁ z)))
    change (((hcs₂.chartAt (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂)).extend
        (morseModelWithCornersHalfSpace m)) ∘
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
      ((hcs₁.chartAt x).extend (morseModelWithCornersHalfSpace m)).symm) =ᶠ[
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m))]
      (fun z : MorseModel (m + 1) => ψ₂ (Φ (ψ₁ z)))
    rw [hchart₂']
    rw [hchart₁']
    rw [OpenPartialHomeomorph.extend_coe]
    rw [OpenPartialHomeomorph.extend_coe_symm]
    simpa using hred

theorem contMDiffAt_sublevelInteriorMap_on {m : ℕ} (g₁ g₂ : MorseModel (m + 1) → ℝ)
    (a₁ a₂ : ℝ) (hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁) (hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂)
    (hreg₁ : ∀ x : MorseModel (m + 1), g₁ x = a₁ → fderiv ℝ g₁ x ≠ 0)
    (hreg₂ : ∀ x : MorseModel (m + 1), g₂ x = a₂ → fderiv ℝ g₂ x ≠ 0)
    (x : SublevelSpace g₁ a₁) (hx : g₁ x.1 < a₁)
    (Φ : MorseModel (m + 1) → MorseModel (m + 1)) (U : Set (MorseModel (m + 1)))
    (hUopen : IsOpen U) (hUsub : ∀ y : MorseModel (m + 1), g₁ y ≤ a₁ → y ∈ U)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ U)
    (hmap : ∀ y : MorseModel (m + 1), g₁ y ≤ a₁ → g₂ (Φ y) ≤ a₂)
    (hstrict : ∀ y : MorseModel (m + 1), g₁ y < a₁ → g₂ (Φ y) < a₂)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₁ a₁) :=
      sublevelChartedSpace g₁ a₁ hg₁ hreg₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₂ a₂) :=
      sublevelChartedSpace g₂ a₂ hg₂ hreg₂)
    (hchart₁ : ∀ y : SublevelSpace g₁ a₁, hcs₁.chartAt y =
      (if h : g₁ y.1 = a₁ then sublevelBoundaryChart g₁ a₁ y h hg₁ (hreg₁ y.1 h)
        else sublevelInteriorChart g₁ a₁ y (lt_of_le_of_ne (show g₁ y.1 ≤ a₁ from y.2) h) hg₁) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g₂ a₂, hcs₂.chartAt y =
      (if h : g₂ y.1 = a₂ then sublevelBoundaryChart g₂ a₂ y h hg₂ (hreg₂ y.1 h)
        else sublevelInteriorChart g₂ a₂ y (lt_of_le_of_ne (show g₂ y.1 ≤ a₂ from y.2) h) hg₂) := by
      intro y
      rfl) :
    ContMDiffAt (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) x := by
  letI := hcs₁
  letI := hcs₂
  rw [contMDiffAt_iff]
  constructor
  · have hcontOn : ContinuousOn (fun y : SublevelSpace g₁ a₁ => Φ y.1) Set.univ := by
      have hcomp : ContinuousOn (fun y : SublevelSpace g₁ a₁ => Φ (y.1)) Set.univ :=
        (ContDiffOn.continuousOn hΦ).comp continuous_subtype_val.continuousOn (by
          intro y hy
          exact hUsub y.1 y.2)
      simpa using hcomp
    have hcont : Continuous (fun y : SublevelSpace g₁ a₁ => Φ y.1) := continuousOn_univ.mp hcontOn
    exact (Continuous.subtype_mk hcont (fun y => hmap y.1 y.2)).continuousAt
  · let c₁ : OpenPartialHomeomorph (SublevelSpace g₁ a₁) (MorseHalfSpace m) :=
      sublevelInteriorChart g₁ a₁ x hx hg₁
    have hx₂ : g₂ (Φ x.1) < a₂ := hstrict x.1 hx
    let c₂ : OpenPartialHomeomorph (SublevelSpace g₂ a₂) (MorseHalfSpace m) :=
      sublevelInteriorChart g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂
    have hchart₁' : hcs₁.chartAt x = c₁ := by
      rw [hchart₁ x, dif_neg (ne_of_lt hx)]
    have hchart₂' : hcs₂.chartAt (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂) = c₂ := by
      rw [hchart₂ ⟨Φ x.1, hmap x.1 x.2⟩, dif_neg (ne_of_lt hx₂)]
    let c₁' : ℝ := sublevelInteriorShift g₁ a₁ x hx hg₁
    let c₂' : ℝ := sublevelInteriorShift g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂
    let U₁ : Set (MorseModel (m + 1)) :=
      (fun z : MorseModel (m + 1) => morseHalfSpaceShift (-c₁') z) ⁻¹' U
    have hF : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : MorseModel (m + 1) => morseHalfSpaceShift c₂' (Φ (morseHalfSpaceShift (-c₁') z))) U₁ := by
      have hΦs : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun z : MorseModel (m + 1) => Φ (morseHalfSpaceShift (-c₁') z)) U₁ := by
        intro z hz
        have hshiftAt : ContDiffWithinAt ℝ (⊤ : ℕ∞)
            (fun w : MorseModel (m + 1) => morseHalfSpaceShift (-c₁') w) U₁ z :=
          (contDiff_morseHalfSpaceShift (-c₁')).contDiffOn.contDiffWithinAt (Set.mem_univ z) |>.mono
            (by intro y hy; trivial)
        have hptU : morseHalfSpaceShift (-c₁') z ∈ U := by
          exact Set.mem_preimage.mp hz
        have hΦat : ContDiffWithinAt ℝ (⊤ : ℕ∞) Φ U (morseHalfSpaceShift (-c₁') z) :=
          hΦ (morseHalfSpaceShift (-c₁') z) hptU
        have hst : Set.MapsTo (fun w : MorseModel (m + 1) => morseHalfSpaceShift (-c₁') w) U₁ U := by
          intro y hy
          exact Set.mem_preimage.mp hy
        exact ContDiffWithinAt.comp (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (E := MorseModel (m + 1))
          (F := MorseModel (m + 1)) (G := MorseModel (m + 1)) (s := U₁) (t := U)
          (f := fun w : MorseModel (m + 1) => morseHalfSpaceShift (-c₁') w) (g := Φ)
          z hΦat hshiftAt hst
      exact (contDiff_morseHalfSpaceShift c₂').contDiffOn.comp (t := Set.univ) hΦs
        (by intro z hz; exact Set.mem_univ _)
    have hz₀ : ((morseModelWithCornersHalfSpace m) (c₁ x)) ∈
        Set.range (morseModelWithCornersHalfSpace m) :=
      ⟨c₁ x, rfl⟩
    have hB₁ : {z : MorseModel (m + 1) |
        dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g₁ a₁ x hx hg₁} ∈
        nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
          (Set.range (morseModelWithCornersHalfSpace m)) := by
      have hc₁val : ((morseModelWithCornersHalfSpace m) (c₁ x) : MorseModel (m + 1)) =
          morseHalfSpaceShift c₁' x.1 := by
        have hc₁val' : ((sublevelInteriorChart g₁ a₁ x hx hg₁ x : MorseHalfSpace m) :
            MorseModel (m + 1)) = morseHalfSpaceShift c₁' x.1 := by
          rw [sublevelInteriorChart_apply_value g₁ a₁ x hx hg₁ x (by
            rw [dist_self]
            exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
              ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).1)]
        simpa [c₁] using hc₁val'
      have hcont : Continuous (fun z : MorseModel (m + 1) =>
          dist (morseHalfSpaceShift (-c₁') z) x.1) := by
        have hshift : Continuous (fun x : MorseModel (m + 1) => morseHalfSpaceShift (-c₁') x) := by
          change Continuous (fun x : MorseModel (m + 1) =>
            HAdd.hAdd x (HSMul.hSMul (-c₁') levelSetLastBasis))
          fun_prop
        exact hshift.dist (continuous_const : Continuous fun _ : MorseModel (m + 1) => x.1)
      have hmem₀ : dist (morseHalfSpaceShift (-c₁') ((morseModelWithCornersHalfSpace m) (c₁ x))) x.1 <
          sublevelInteriorRadius g₁ a₁ x hx hg₁ := by
        rw [hc₁val, morseHalfSpaceShift_neg]
        rw [dist_self]
        exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
          ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).1
      exact nhdsWithin_le_nhds ((isOpen_Iio.preimage hcont).mem_nhds hmem₀)
    have hB₂ : (fun z : MorseModel (m + 1) =>
        Φ (morseHalfSpaceShift (-c₁') z)) ⁻¹' {z : MorseModel (m + 1) |
          dist z (Φ x.1) < sublevelInteriorRadius g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂} ∈
        nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
          (Set.range (morseModelWithCornersHalfSpace m)) := by
      have hc₁val : ((morseModelWithCornersHalfSpace m) (c₁ x) : MorseModel (m + 1)) =
          morseHalfSpaceShift c₁' x.1 := by
        have hc₁val' : ((sublevelInteriorChart g₁ a₁ x hx hg₁ x : MorseHalfSpace m) :
            MorseModel (m + 1)) = morseHalfSpaceShift c₁' x.1 := by
          rw [sublevelInteriorChart_apply_value g₁ a₁ x hx hg₁ x (by
            rw [dist_self]
            exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
              ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).1)]
        simpa [c₁] using hc₁val'
      have hshiftAt : ContinuousAt (fun z : MorseModel (m + 1) =>
          morseHalfSpaceShift (-c₁') z) ((morseModelWithCornersHalfSpace m) (c₁ x)) :=
        (contDiff_morseHalfSpaceShift (-c₁')).continuous.continuousAt
      have hΦat : ContinuousAt Φ (morseHalfSpaceShift (-c₁')
          ((morseModelWithCornersHalfSpace m) (c₁ x))) :=
        (ContDiffOn.continuousOn hΦ).continuousAt (hUopen.mem_nhds (by
          rw [hc₁val, morseHalfSpaceShift_neg]
          exact hUsub x.1 x.2))
      have hinner : ContinuousAt (fun z : MorseModel (m + 1) =>
          Φ (morseHalfSpaceShift (-c₁') z)) ((morseModelWithCornersHalfSpace m) (c₁ x)) := by
        exact ContinuousAt.comp hΦat hshiftAt
      have hmem₀ : dist (Φ (morseHalfSpaceShift (-c₁')
          ((morseModelWithCornersHalfSpace m) (c₁ x)))) (Φ x.1) <
          sublevelInteriorRadius g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂ := by
        rw [hc₁val, morseHalfSpaceShift_neg]
        rw [dist_self]
        exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
          ((isOpen_Iio.preimage hg₂.continuous).mem_nhds hx₂))).1
      have hpre : {z : MorseModel (m + 1) |
          dist (Φ (morseHalfSpaceShift (-c₁') z)) (Φ x.1) <
            sublevelInteriorRadius g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂} ∈
          𝓝 ((morseModelWithCornersHalfSpace m) (c₁ x)) := by
        have hcont' : Continuous (fun w : MorseModel (m + 1) => dist w (Φ x.1)) :=
          continuous_id.dist continuous_const
        exact ContinuousAt.preimage_mem_nhds hinner
          ((isOpen_Iio.preimage hcont').mem_nhds hmem₀)
      exact nhdsWithin_le_nhds hpre
    have hB : Set.range (morseModelWithCornersHalfSpace m) ∩
        {z : MorseModel (m + 1) |
          dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g₁ a₁ x hx hg₁} ∩
        (fun z : MorseModel (m + 1) => Φ (morseHalfSpaceShift (-c₁') z)) ⁻¹'
          {z : MorseModel (m + 1) |
            dist z (Φ x.1) <
              sublevelInteriorRadius g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂} ∈
        nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
          (Set.range (morseModelWithCornersHalfSpace m)) := by
      exact Filter.inter_mem (Filter.inter_mem self_mem_nhdsWithin hB₁) hB₂
    have hred : (morseModelWithCornersHalfSpace m ∘ c₂ ∘
        (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
        c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm) =ᶠ[
          nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
            (Set.range (morseModelWithCornersHalfSpace m))]
        (fun z : MorseModel (m + 1) => morseHalfSpaceShift c₂' (Φ (morseHalfSpaceShift (-c₁') z))) := by
      refine Filter.eventuallyEq_of_mem (s := Set.range (morseModelWithCornersHalfSpace m) ∩
          {z : MorseModel (m + 1) |
            dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g₁ a₁ x hx hg₁} ∩
          (fun z : MorseModel (m + 1) => Φ (morseHalfSpaceShift (-c₁') z)) ⁻¹'
            {z : MorseModel (m + 1) |
              dist z (Φ x.1) < sublevelInteriorRadius g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂}) ?_ ?_
      · exact hB
      · intro z hz
        have hzr : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.1.1
        have hzmem : 0 ≤ z (Fin.last m) := by
          rw [range_morseModelWithCornersHalfSpace] at hzr
          exact hzr
        let z' : MorseHalfSpace m := ⟨z, hzmem⟩
        have hclamp : (morseModelWithCornersHalfSpace m).symm z = z' := by
          apply Subtype.ext
          exact morseHalfSpaceClamp_of_mem m hzmem
        change (morseModelWithCornersHalfSpace m)
            (c₂ ((fun y : SublevelSpace g₁ a₁ =>
              (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂))
              (c₁.symm ((morseModelWithCornersHalfSpace m).symm z)))) =
          morseHalfSpaceShift c₂' (Φ (morseHalfSpaceShift (-c₁') z))
        have hmem₁ : dist (morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1))) x.1 <
            sublevelInteriorRadius g₁ a₁ x hx hg₁ := by
          change dist (morseHalfSpaceShift (-c₁') z) x.1 <
            sublevelInteriorRadius g₁ a₁ x hx hg₁
          exact hz.1.2
        have hsymm₁ : c₁.symm z' = (⟨morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1)), by
            change g₁ (morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1))) ≤ a₁
            have hball : Metric.ball x.1 (sublevelInteriorRadius g₁ a₁ x hx hg₁) ⊆
                {y : MorseModel (m + 1) | g₁ y < a₁} := by
              exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
                ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).2
            exact le_of_lt (hball hmem₁)⟩ : SublevelSpace g₁ a₁) := by
          rw [sublevelInteriorChart_symm_value g₁ a₁ x hx hg₁ hmem₁]
        have hmem₂ : dist (Φ (morseHalfSpaceShift (-c₁') z)) (Φ x.1) <
            sublevelInteriorRadius g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂ := by
          exact hz.2
        have hval₂ : (c₂ (⟨Φ (morseHalfSpaceShift (-c₁') z), hmap (morseHalfSpaceShift (-c₁') z) (by
            have hball : Metric.ball x.1 (sublevelInteriorRadius g₁ a₁ x hx hg₁) ⊆
                {y : MorseModel (m + 1) | g₁ y < a₁} := by
              exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
                ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).2
            exact le_of_lt (hball hmem₁))⟩ : SublevelSpace g₂ a₂) : MorseHalfSpace m) =
          morseHalfSpaceShift c₂' (Φ (morseHalfSpaceShift (-c₁') z)) := by
          rw [sublevelInteriorChart_apply_value g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂
            (⟨Φ (morseHalfSpaceShift (-c₁') z), hmap (morseHalfSpaceShift (-c₁') z) (by
              have hball : Metric.ball x.1 (sublevelInteriorRadius g₁ a₁ x hx hg₁) ⊆
                  {y : MorseModel (m + 1) | g₁ y < a₁} := by
                exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
                  ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).2
              exact le_of_lt (hball hmem₁))⟩ : SublevelSpace g₂ a₂) hmem₂]
        rw [hclamp]
        rw [hsymm₁]
        simpa [hval₂]
    have hcomp : ContDiffWithinAt ℝ (⊤ : ℕ∞)
        (morseModelWithCornersHalfSpace m ∘ c₂ ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm)
        (Set.range (morseModelWithCornersHalfSpace m))
        ((morseModelWithCornersHalfSpace m) (c₁ x)) := by
      have hc₁val₀ : ((morseModelWithCornersHalfSpace m) (c₁ x) : MorseModel (m + 1)) =
          morseHalfSpaceShift c₁' x.1 := by
        have hc₁val' : ((sublevelInteriorChart g₁ a₁ x hx hg₁ x : MorseHalfSpace m) :
            MorseModel (m + 1)) = morseHalfSpaceShift c₁' x.1 := by
          rw [sublevelInteriorChart_apply_value g₁ a₁ x hx hg₁ x (by
            rw [dist_self]
            exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
              ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).1)]
        simpa [c₁] using hc₁val'
      have hz₀U₁ : ((morseModelWithCornersHalfSpace m) (c₁ x)) ∈ U₁ := by
        change morseHalfSpaceShift (-c₁') ((morseModelWithCornersHalfSpace m) (c₁ x)) ∈ U
        rw [hc₁val₀, morseHalfSpaceShift_neg]
        exact hUsub x.1 x.2
      have hU₁open : IsOpen U₁ := by
        dsimp [U₁]
        exact hUopen.preimage (contDiff_morseHalfSpaceShift (-c₁')).continuous
      have hU₁nhd : U₁ ∈ nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
          (Set.range (morseModelWithCornersHalfSpace m)) := by
        exact nhdsWithin_le_nhds (hU₁open.mem_nhds hz₀U₁)
      have hFAt : ContDiffWithinAt ℝ (⊤ : ℕ∞)
          (fun z : MorseModel (m + 1) => morseHalfSpaceShift c₂' (Φ (morseHalfSpaceShift (-c₁') z)))
          (Set.range (morseModelWithCornersHalfSpace m))
          ((morseModelWithCornersHalfSpace m) (c₁ x)) :=
        (hF.contDiffWithinAt hz₀U₁).mono_of_mem_nhdsWithin hU₁nhd
      exact hFAt.congr_of_eventuallyEq_of_mem hred hz₀
    have hcomp' : ContDiffWithinAt ℝ (⊤ : ℕ∞)
        (morseModelWithCornersHalfSpace m ∘ c₂ ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm)
        (Set.range (morseModelWithCornersHalfSpace m))
        (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      simpa [extChartAt, hchart₁'] using hcomp
    refine hcomp'.congr_of_eventuallyEq_of_mem ?_ ?_
    · rw [show (extChartAt (morseModelWithCornersHalfSpace m)
          (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂)) =
          ((hcs₂.chartAt (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂)).extend
            (morseModelWithCornersHalfSpace m)) by rfl]
      rw [show (extChartAt (morseModelWithCornersHalfSpace m) x) =
          ((hcs₁.chartAt x).extend (morseModelWithCornersHalfSpace m)) by rfl]
      rw [hchart₂']
      rw [hchart₁']
      simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
      change ((morseModelWithCornersHalfSpace m ∘ c₂) ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm) =ᶠ[
            nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
              (Set.range (morseModelWithCornersHalfSpace m))]
          (morseModelWithCornersHalfSpace m ∘ c₂ ∘
            (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
            c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm)
      rfl
    · simp [extChartAt, hchart₁']

theorem contMDiff_sublevelMap_on {m : ℕ} (g₁ g₂ : MorseModel (m + 1) → ℝ)
    (a₁ a₂ : ℝ) (hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁) (hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂)
    (hreg₁ : ∀ x : MorseModel (m + 1), g₁ x = a₁ → fderiv ℝ g₁ x ≠ 0)
    (hreg₂ : ∀ x : MorseModel (m + 1), g₂ x = a₂ → fderiv ℝ g₂ x ≠ 0)
    (Φ : MorseModel (m + 1) → MorseModel (m + 1)) (U : Set (MorseModel (m + 1)))
    (hUopen : IsOpen U) (hUsub : ∀ y : MorseModel (m + 1), g₁ y ≤ a₁ → y ∈ U)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ U)
    (hmap : ∀ y : MorseModel (m + 1), g₁ y ≤ a₁ → g₂ (Φ y) ≤ a₂)
    (hbnd : ∀ y : MorseModel (m + 1), g₁ y = a₁ → g₂ (Φ y) = a₂)
    (hstrict : ∀ y : MorseModel (m + 1), g₁ y < a₁ → g₂ (Φ y) < a₂)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₁ a₁) :=
      sublevelChartedSpace g₁ a₁ hg₁ hreg₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₂ a₂) :=
      sublevelChartedSpace g₂ a₂ hg₂ hreg₂)
    (hchart₁ : ∀ y : SublevelSpace g₁ a₁, hcs₁.chartAt y =
      (if h : g₁ y.1 = a₁ then sublevelBoundaryChart g₁ a₁ y h hg₁ (hreg₁ y.1 h)
        else sublevelInteriorChart g₁ a₁ y (lt_of_le_of_ne (show g₁ y.1 ≤ a₁ from y.2) h) hg₁) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g₂ a₂, hcs₂.chartAt y =
      (if h : g₂ y.1 = a₂ then sublevelBoundaryChart g₂ a₂ y h hg₂ (hreg₂ y.1 h)
        else sublevelInteriorChart g₂ a₂ y (lt_of_le_of_ne (show g₂ y.1 ≤ a₂ from y.2) h) hg₂) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) := by
  intro x
  by_cases hx : g₁ x.1 = a₁
  · exact contMDiffAt_sublevelBoundaryMap_on g₁ g₂ a₁ a₂ hg₁ hg₂ hreg₁ hreg₂ x hx Φ U hUopen hUsub hΦ
      hmap hbnd (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
  · have hxlt : g₁ x.1 < a₁ := lt_of_le_of_ne (show g₁ x.1 ≤ a₁ from x.2) hx
    exact contMDiffAt_sublevelInteriorMap_on g₁ g₂ a₁ a₂ hg₁ hg₂ hreg₁ hreg₂ x hxlt Φ U hUopen hUsub hΦ
      hmap hstrict (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)

theorem contMDiffAt_sublevelInteriorMap {m : ℕ} (g₁ g₂ : MorseModel (m + 1) → ℝ)
    (a₁ a₂ : ℝ) (hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁) (hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂)
    (hreg₁ : ∀ x : MorseModel (m + 1), g₁ x = a₁ → fderiv ℝ g₁ x ≠ 0)
    (hreg₂ : ∀ x : MorseModel (m + 1), g₂ x = a₂ → fderiv ℝ g₂ x ≠ 0)
    (x : SublevelSpace g₁ a₁) (hx : g₁ x.1 < a₁)
    (Φ : MorseModel (m + 1) → MorseModel (m + 1)) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hmap : ∀ y : MorseModel (m + 1), g₁ y ≤ a₁ → g₂ (Φ y) ≤ a₂)
    (hstrict : ∀ y : MorseModel (m + 1), g₁ y < a₁ → g₂ (Φ y) < a₂)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₁ a₁) :=
      sublevelChartedSpace g₁ a₁ hg₁ hreg₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₂ a₂) :=
      sublevelChartedSpace g₂ a₂ hg₂ hreg₂)
    (hchart₁ : ∀ y : SublevelSpace g₁ a₁, hcs₁.chartAt y =
      (if h : g₁ y.1 = a₁ then sublevelBoundaryChart g₁ a₁ y h hg₁ (hreg₁ y.1 h)
        else sublevelInteriorChart g₁ a₁ y (lt_of_le_of_ne (show g₁ y.1 ≤ a₁ from y.2) h) hg₁) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g₂ a₂, hcs₂.chartAt y =
      (if h : g₂ y.1 = a₂ then sublevelBoundaryChart g₂ a₂ y h hg₂ (hreg₂ y.1 h)
        else sublevelInteriorChart g₂ a₂ y (lt_of_le_of_ne (show g₂ y.1 ≤ a₂ from y.2) h) hg₂) := by
      intro y
      rfl) :
    ContMDiffAt (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) x := by
  letI := hcs₁
  letI := hcs₂
  rw [contMDiffAt_iff]
  constructor
  · have hcont : Continuous (fun y : SublevelSpace g₁ a₁ => Φ y.1) :=
      hΦ.continuous.comp continuous_subtype_val
    exact (Continuous.subtype_mk hcont (fun y => hmap y.1 y.2)).continuousAt
  · let c₁ : OpenPartialHomeomorph (SublevelSpace g₁ a₁) (MorseHalfSpace m) :=
      sublevelInteriorChart g₁ a₁ x hx hg₁
    have hx₂ : g₂ (Φ x.1) < a₂ := hstrict x.1 hx
    let c₂ : OpenPartialHomeomorph (SublevelSpace g₂ a₂) (MorseHalfSpace m) :=
      sublevelInteriorChart g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂
    have hchart₁' : hcs₁.chartAt x = c₁ := by
      rw [hchart₁ x, dif_neg (ne_of_lt hx)]
    have hchart₂' : hcs₂.chartAt (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂) = c₂ := by
      rw [hchart₂ ⟨Φ x.1, hmap x.1 x.2⟩, dif_neg (ne_of_lt hx₂)]
    let c₁' : ℝ := sublevelInteriorShift g₁ a₁ x hx hg₁
    let c₂' : ℝ := sublevelInteriorShift g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂
    have hF : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : MorseModel (m + 1) => morseHalfSpaceShift c₂' (Φ (morseHalfSpaceShift (-c₁') z))) := by
      exact (contDiff_morseHalfSpaceShift c₂').comp
        (hΦ.comp (contDiff_morseHalfSpaceShift (-c₁')))
    have hz₀ : ((morseModelWithCornersHalfSpace m) (c₁ x)) ∈
        Set.range (morseModelWithCornersHalfSpace m) :=
      ⟨c₁ x, rfl⟩
    have hB₁ : {z : MorseModel (m + 1) |
        dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g₁ a₁ x hx hg₁} ∈
        nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
          (Set.range (morseModelWithCornersHalfSpace m)) := by
      have hc₁val : ((morseModelWithCornersHalfSpace m) (c₁ x) : MorseModel (m + 1)) =
          morseHalfSpaceShift c₁' x.1 := by
        have hc₁val' : ((sublevelInteriorChart g₁ a₁ x hx hg₁ x : MorseHalfSpace m) :
            MorseModel (m + 1)) = morseHalfSpaceShift c₁' x.1 := by
          rw [sublevelInteriorChart_apply_value g₁ a₁ x hx hg₁ x (by
            rw [dist_self]
            exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
              ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).1)]
        simpa [c₁] using hc₁val'
      have hcont : Continuous (fun z : MorseModel (m + 1) =>
          dist (morseHalfSpaceShift (-c₁') z) x.1) := by
        have hshift : Continuous (fun x : MorseModel (m + 1) => morseHalfSpaceShift (-c₁') x) := by
          change Continuous (fun x : MorseModel (m + 1) =>
            HAdd.hAdd x (HSMul.hSMul (-c₁') levelSetLastBasis))
          fun_prop
        exact hshift.dist (continuous_const : Continuous fun _ : MorseModel (m + 1) => x.1)
      have hmem₀ : dist (morseHalfSpaceShift (-c₁') ((morseModelWithCornersHalfSpace m) (c₁ x))) x.1 <
          sublevelInteriorRadius g₁ a₁ x hx hg₁ := by
        rw [hc₁val, morseHalfSpaceShift_neg]
        rw [dist_self]
        exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
          ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).1
      exact nhdsWithin_le_nhds ((isOpen_Iio.preimage hcont).mem_nhds hmem₀)
    have hB₂ : (fun z : MorseModel (m + 1) =>
        Φ (morseHalfSpaceShift (-c₁') z)) ⁻¹' {z : MorseModel (m + 1) |
          dist z (Φ x.1) < sublevelInteriorRadius g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂} ∈
        nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
          (Set.range (morseModelWithCornersHalfSpace m)) := by
      have hcont : Continuous (fun z : MorseModel (m + 1) =>
          dist (Φ (morseHalfSpaceShift (-c₁') z)) (Φ x.1)) := by
        have hinner : Continuous (fun z : MorseModel (m + 1) =>
            Φ (morseHalfSpaceShift (-c₁') z)) := by
          exact hΦ.continuous.comp (contDiff_morseHalfSpaceShift (-c₁') |>.continuous)
        exact hinner.dist (continuous_const : Continuous fun _ : MorseModel (m + 1) => Φ x.1)
      have hc₁val : ((morseModelWithCornersHalfSpace m) (c₁ x) : MorseModel (m + 1)) =
          morseHalfSpaceShift c₁' x.1 := by
        have hc₁val' : ((sublevelInteriorChart g₁ a₁ x hx hg₁ x : MorseHalfSpace m) :
            MorseModel (m + 1)) = morseHalfSpaceShift c₁' x.1 := by
          rw [sublevelInteriorChart_apply_value g₁ a₁ x hx hg₁ x (by
            rw [dist_self]
            exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
              ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).1)]
        simpa [c₁] using hc₁val'
      have hmem₀ : dist (Φ (morseHalfSpaceShift (-c₁')
          ((morseModelWithCornersHalfSpace m) (c₁ x)))) (Φ x.1) <
          sublevelInteriorRadius g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂ := by
        rw [hc₁val, morseHalfSpaceShift_neg]
        rw [dist_self]
        exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
          ((isOpen_Iio.preimage hg₂.continuous).mem_nhds hx₂))).1
      exact nhdsWithin_le_nhds ((isOpen_Iio.preimage hcont).mem_nhds hmem₀)
    have hB : Set.range (morseModelWithCornersHalfSpace m) ∩
        {z : MorseModel (m + 1) |
          dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g₁ a₁ x hx hg₁} ∩
        (fun z : MorseModel (m + 1) => Φ (morseHalfSpaceShift (-c₁') z)) ⁻¹'
          {z : MorseModel (m + 1) |
            dist z (Φ x.1) <
              sublevelInteriorRadius g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂} ∈
        nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
          (Set.range (morseModelWithCornersHalfSpace m)) := by
      exact Filter.inter_mem (Filter.inter_mem self_mem_nhdsWithin hB₁) hB₂
    have hred : (morseModelWithCornersHalfSpace m ∘ c₂ ∘
        (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
        c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm) =ᶠ[
          nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
            (Set.range (morseModelWithCornersHalfSpace m))]
        (fun z : MorseModel (m + 1) => morseHalfSpaceShift c₂' (Φ (morseHalfSpaceShift (-c₁') z))) := by
      refine Filter.eventuallyEq_of_mem (s := Set.range (morseModelWithCornersHalfSpace m) ∩
          {z : MorseModel (m + 1) |
            dist (morseHalfSpaceShift (-c₁') z) x.1 < sublevelInteriorRadius g₁ a₁ x hx hg₁} ∩
          (fun z : MorseModel (m + 1) => Φ (morseHalfSpaceShift (-c₁') z)) ⁻¹'
            {z : MorseModel (m + 1) |
              dist z (Φ x.1) < sublevelInteriorRadius g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂}) ?_ ?_
      · exact hB
      · intro z hz
        have hzr : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.1.1
        have hzmem : 0 ≤ z (Fin.last m) := by
          rw [range_morseModelWithCornersHalfSpace] at hzr
          exact hzr
        let z' : MorseHalfSpace m := ⟨z, hzmem⟩
        have hclamp : (morseModelWithCornersHalfSpace m).symm z = z' := by
          apply Subtype.ext
          exact morseHalfSpaceClamp_of_mem m hzmem
        change (morseModelWithCornersHalfSpace m)
            (c₂ ((fun y : SublevelSpace g₁ a₁ =>
              (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂))
              (c₁.symm ((morseModelWithCornersHalfSpace m).symm z)))) =
          morseHalfSpaceShift c₂' (Φ (morseHalfSpaceShift (-c₁') z))
        have hmem₁ : dist (morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1))) x.1 <
            sublevelInteriorRadius g₁ a₁ x hx hg₁ := by
          change dist (morseHalfSpaceShift (-c₁') z) x.1 <
            sublevelInteriorRadius g₁ a₁ x hx hg₁
          exact hz.1.2
        have hsymm₁ : c₁.symm z' = (⟨morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1)), by
            change g₁ (morseHalfSpaceShift (-c₁') (z' : MorseModel (m + 1))) ≤ a₁
            have hball : Metric.ball x.1 (sublevelInteriorRadius g₁ a₁ x hx hg₁) ⊆
                {y : MorseModel (m + 1) | g₁ y < a₁} := by
              exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
                ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).2
            exact le_of_lt (hball hmem₁)⟩ : SublevelSpace g₁ a₁) := by
          rw [sublevelInteriorChart_symm_value g₁ a₁ x hx hg₁ hmem₁]
        have hmem₂ : dist (Φ (morseHalfSpaceShift (-c₁') z)) (Φ x.1) <
            sublevelInteriorRadius g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂ := by
          exact hz.2
        have hval₂ : (c₂ (⟨Φ (morseHalfSpaceShift (-c₁') z), hmap (morseHalfSpaceShift (-c₁') z) (by
            have hball : Metric.ball x.1 (sublevelInteriorRadius g₁ a₁ x hx hg₁) ⊆
                {y : MorseModel (m + 1) | g₁ y < a₁} := by
              exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
                ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).2
            exact le_of_lt (hball hmem₁))⟩ : SublevelSpace g₂ a₂) : MorseModel (m + 1)) =
            morseHalfSpaceShift c₂' (Φ (morseHalfSpaceShift (-c₁') z)) := by
          rw [sublevelInteriorChart_apply_value g₂ a₂ ⟨Φ x.1, hmap x.1 x.2⟩ hx₂ hg₂
            (⟨Φ (morseHalfSpaceShift (-c₁') z), hmap (morseHalfSpaceShift (-c₁') z) (by
              have hball : Metric.ball x.1 (sublevelInteriorRadius g₁ a₁ x hx hg₁) ⊆
                  {y : MorseModel (m + 1) | g₁ y < a₁} := by
                exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
                  ((isOpen_Iio.preimage hg₁.continuous).mem_nhds hx))).2
              exact le_of_lt (hball hmem₁))⟩) hmem₂]
        rw [hclamp]
        rw [hsymm₁]
        simpa [hval₂]
    have hcomp : ContDiffWithinAt ℝ (⊤ : ℕ∞)
        (morseModelWithCornersHalfSpace m ∘ c₂ ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm)
        (Set.range (morseModelWithCornersHalfSpace m))
        ((morseModelWithCornersHalfSpace m) (c₁ x)) := by
      exact hF.contDiffAt.contDiffWithinAt.congr_of_eventuallyEq_of_mem hred hz₀
    have hcomp' : ContDiffWithinAt ℝ (⊤ : ℕ∞)
        (morseModelWithCornersHalfSpace m ∘ c₂ ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm)
        (Set.range (morseModelWithCornersHalfSpace m))
        (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      simpa [extChartAt, hchart₁'] using hcomp
    refine hcomp'.congr_of_eventuallyEq_of_mem ?_ ?_
    · rw [show (extChartAt (morseModelWithCornersHalfSpace m)
          (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂)) =
          ((hcs₂.chartAt (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂)).extend
            (morseModelWithCornersHalfSpace m)) by rfl]
      rw [show (extChartAt (morseModelWithCornersHalfSpace m) x) =
          ((hcs₁.chartAt x).extend (morseModelWithCornersHalfSpace m)) by rfl]
      rw [hchart₂']
      rw [hchart₁']
      simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
      change ((morseModelWithCornersHalfSpace m ∘ c₂) ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm) =ᶠ[
            nhdsWithin ((morseModelWithCornersHalfSpace m) (c₁ x))
              (Set.range (morseModelWithCornersHalfSpace m))]
          (morseModelWithCornersHalfSpace m ∘ c₂ ∘
            (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
            c₁.symm ∘ (morseModelWithCornersHalfSpace m).symm)
      rfl
    · simp [extChartAt, hchart₁']

theorem contMDiffAt_sublevelBoundaryInteriorMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (a₁ a₂ : ℝ) (ha : a₁ < a₂) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg₁ : ∀ x : MorseModel (m + 1), g x = a₁ → fderiv ℝ g x ≠ 0)
    (hreg₂ : ∀ x : MorseModel (m + 1), g x = a₂ → fderiv ℝ g x ≠ 0)
    (x : SublevelSpace g a₁) (hx : g x.1 = a₁)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a₁) :=
      sublevelChartedSpace g a₁ hg hreg₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a₂) :=
      sublevelChartedSpace g a₂ hg hreg₂)
    (hchart₁ : ∀ y : SublevelSpace g a₁, hcs₁.chartAt y =
      (if h : g y.1 = a₁ then sublevelBoundaryChart g a₁ y h hg (hreg₁ y.1 h)
        else sublevelInteriorChart g a₁ y (lt_of_le_of_ne (show g y.1 ≤ a₁ from y.2) h) hg) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g a₂, hcs₂.chartAt y =
      (if h : g y.1 = a₂ then sublevelBoundaryChart g a₂ y h hg (hreg₂ y.1 h)
        else sublevelInteriorChart g a₂ y (lt_of_le_of_ne (show g y.1 ≤ a₂ from y.2) h) hg) := by
      intro y
      rfl) :
    ContMDiffAt (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g a₁ => (⟨y.1, by
        change g y.1 ≤ a₂
        exact le_trans (by change g y.1 ≤ a₁; exact y.2) (le_of_lt ha)⟩ :
          SublevelSpace g a₂)) x := by
  letI := hcs₁
  letI := hcs₂
  let incl : SublevelSpace g a₁ → SublevelSpace g a₂ :=
    fun y => ⟨y.1, by
      change g y.1 ≤ a₂
      exact le_trans (by change g y.1 ≤ a₁; exact y.2) (le_of_lt ha)⟩
  rw [contMDiffAt_iff]
  constructor
  · have hcont : Continuous (fun y : SublevelSpace g a₁ => (y.1 : MorseModel (m + 1))) :=
      continuous_subtype_val
    exact (Continuous.subtype_mk hcont (fun y => by
      change g y.1 ≤ a₂
      exact le_trans (by change g y.1 ≤ a₁; exact y.2) (le_of_lt ha))).continuousAt
  · let c₁ : OpenPartialHomeomorph (SublevelSpace g a₁) (MorseHalfSpace m) :=
      sublevelBoundaryChart g a₁ x hx hg (hreg₁ x.1 hx)
    have hxlt : g x.1 < a₂ := lt_of_le_of_lt (le_of_eq hx) ha
    let c₂ : OpenPartialHomeomorph (SublevelSpace g a₂) (MorseHalfSpace m) :=
      sublevelInteriorChart g a₂ ⟨x.1, le_of_lt hxlt⟩ hxlt hg
    have hchart₁' : hcs₁.chartAt x = c₁ := by
      rw [hchart₁ x, dif_pos hx]
    have hchart₂' : hcs₂.chartAt (incl x) = c₂ := by
      rw [hchart₂ (incl x)]
      rw [dif_neg (ne_of_lt hxlt)]
    let ψ₁ : MorseModel (m + 1) → MorseModel (m + 1) :=
      sublevelBoundaryChartInvValueRaw g a₁ x hx hg (hreg₁ x.1 hx)
    let c₂' : ℝ := sublevelInteriorShift g a₂ ⟨x.1, le_of_lt hxlt⟩ hxlt hg
    let F : MorseModel (m + 1) → MorseModel (m + 1) := fun z => morseHalfSpaceShift c₂' (ψ₁ z)
    have hψ₁cd : ContDiffOn ℝ (⊤ : ℕ∞) ψ₁ (sublevelBoundaryChartDomain g a₁ x hx hg (hreg₁ x.1 hx)) :=
      contDiffOn_sublevelBoundaryChartInvValueRaw g a₁ x hx hg (hreg₁ x.1 hx)
    have hF : ContDiffOn ℝ (⊤ : ℕ∞) F (sublevelBoundaryChartDomain g a₁ x hx hg (hreg₁ x.1 hx)) := by
      have hshift : ContDiff ℝ (⊤ : ℕ∞) (morseHalfSpaceShift c₂') :=
        contDiff_morseHalfSpaceShift (m := m) c₂'
      have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : MorseModel (m + 1) => morseHalfSpaceShift c₂' (ψ₁ z))
          (sublevelBoundaryChartDomain g a₁ x hx hg (hreg₁ x.1 hx)) :=
        hshift.contDiffOn.comp hψ₁cd (by intro z hz; exact Set.mem_univ (ψ₁ z))
      exact hcomp
    have hD₁open : IsOpen (sublevelBoundaryChartDomain g a₁ x hx hg (hreg₁ x.1 hx)) :=
      isOpen_sublevelBoundaryChartDomain g a₁ x hx hg (hreg₁ x.1 hx)
    have hc₁src : x ∈ c₁.source := mem_sublevelBoundaryChart_source g a₁ x hx hg (hreg₁ x.1 hx)
    have hz₀I : (extChartAt (morseModelWithCornersHalfSpace m) x x) =
        (morseModelWithCornersHalfSpace m) (c₁ x) := by
      simp [extChartAt, hchart₁']
    have hz₀range : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
        Set.range (morseModelWithCornersHalfSpace m) := by
      simp [extChartAt, hchart₁']
    have hz₀D₁ : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
        sublevelBoundaryChartDomain g a₁ x hx hg (hreg₁ x.1 hx) := by
      have hsrc : x ∈ c₁.source := hc₁src
      have htgt : (c₁ x : MorseHalfSpace m) ∈ c₁.target := c₁.map_source hsrc
      simpa [extChartAt, hchart₁', sublevelBoundaryChartDomain] using htgt
    have hρ₂ : 0 < sublevelInteriorRadius g a₂ ⟨x.1, le_of_lt hxlt⟩ hxlt hg := by
      exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
        ((isOpen_Iio.preimage hg.continuous).mem_nhds hxlt))).1
    have hz₀ball : dist (ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x)) x.1 <
        sublevelInteriorRadius g a₂ ⟨x.1, le_of_lt hxlt⟩ hxlt hg := by
      have hz : (c₁ x : MorseHalfSpace m) ∈ c₁.target := c₁.map_source hc₁src
      have hsymm : c₁.symm (c₁ x) = x := c₁.left_inv hc₁src
      have hval := sublevelBoundaryChart_symm_value g a₁ x hx hg (hreg₁ x.1 hx)
        (hz : (c₁ x : MorseHalfSpace m) ∈ (sublevelBoundaryChart g a₁ x hx hg (hreg₁ x.1 hx)).target)
      have hval' : (c₁.symm (c₁ x)).1 = ψ₁ ((morseModelWithCornersHalfSpace m) (c₁ x)) := by
        rw [hval]
        rfl
      have hmain : (c₁.symm (c₁ x)).1 = x.1 := congrArg Subtype.val hsymm
      have hψ₁₀ : ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x) = x.1 := by
        simpa [extChartAt, hchart₁'] using hval'.symm.trans hmain
      rw [hψ₁₀]
      rw [dist_self]
      exact hρ₂
    have hnhd₁ : sublevelBoundaryChartDomain g a₁ x hx hg (hreg₁ x.1 hx) ∈
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m)) := by
      exact nhdsWithin_le_nhds (hD₁open.mem_nhds hz₀D₁)
    let B : Set (MorseModel (m + 1)) := {z : MorseModel (m + 1) | dist (ψ₁ z) x.1 <
      sublevelInteriorRadius g a₂ ⟨x.1, le_of_lt hxlt⟩ hxlt hg}
    have hnhdB : B ∈
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m)) := by
      have hψ₁at : ContinuousAt ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
        (hψ₁cd.continuousOn (extChartAt (morseModelWithCornersHalfSpace m) x x) hz₀D₁).continuousAt
          (hD₁open.mem_nhds hz₀D₁)
      have hcontAt : ContinuousAt (fun z : MorseModel (m + 1) => dist (ψ₁ z) x.1)
          (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
        continuous_dist.continuousAt.comp (hψ₁at.prodMk continuousAt_const)
      have hev : ∀ᶠ z in 𝓝 (extChartAt (morseModelWithCornersHalfSpace m) x x),
          dist (ψ₁ z) x.1 < sublevelInteriorRadius g a₂ ⟨x.1, le_of_lt hxlt⟩ hxlt hg :=
        hcontAt.eventually (isOpen_lt continuous_id continuous_const |>.mem_nhds hz₀ball)
      exact nhdsWithin_le_nhds hev
    have hred : (morseModelWithCornersHalfSpace m ∘ c₂ ∘ incl ∘ c₁.symm ∘
        (morseModelWithCornersHalfSpace m).symm) =ᶠ[
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m))] F := by
      refine Filter.eventuallyEq_of_mem (s := sublevelBoundaryChartDomain g a₁ x hx hg (hreg₁ x.1 hx) ∩
          Set.range (morseModelWithCornersHalfSpace m) ∩ B) ?_ ?_
      · exact Filter.inter_mem (Filter.inter_mem hnhd₁ self_mem_nhdsWithin) hnhdB
      · intro z hz
        have hzD₁ : z ∈ sublevelBoundaryChartDomain g a₁ x hx hg (hreg₁ x.1 hx) := hz.1.1
        have hzrange : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.1.2
        have hzB : z ∈ B := hz.2
        have hzmem : 0 ≤ z (Fin.last m) := by
          rw [range_morseModelWithCornersHalfSpace] at hzrange
          exact hzrange
        have hz₁ : (⟨z, hzmem⟩ : MorseHalfSpace m) ∈ c₁.target := hzD₁
        have hmem₁ : g (ψ₁ z) ≤ a₁ := by
          change g (levelSetReindex (levelSetChartData.mk g a₁ ⟨x.1, hx⟩ hg (hreg₁ x.1 hx)).e
              ((levelSetChartData.mk g a₁ ⟨x.1, hx⟩ hg (hreg₁ x.1 hx)).ψ.symm
                (a₁ - ((⟨z, hzmem⟩ : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
                  levelSetSplitFst m ((⟨z, hzmem⟩ : MorseHalfSpace m) : MorseModel (m + 1))))) ≤ a₁
          exact sublevelBoundaryChart_invFun_mem g
            (levelSetChartData.mk g a₁ ⟨x.1, hx⟩ hg (hreg₁ x.1 hx)).e a₁
            (levelSetChartData.mk g a₁ ⟨x.1, hx⟩ hg (hreg₁ x.1 hx)).ψ
            (levelSetChartData.mk g a₁ ⟨x.1, hx⟩ hg (hreg₁ x.1 hx)).hψ
            (by
              simpa [sublevelBoundaryChartDomain] using hzD₁)
        have hsymm₁ : c₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m) =
            (⟨ψ₁ z, hmem₁⟩ : SublevelSpace g a₁) := by
          rw [sublevelBoundaryChart_symm_value g a₁ x hx hg (hreg₁ x.1 hx) hz₁]
          apply Subtype.ext
          rfl
        have hmem₂ : g (ψ₁ z) ≤ a₂ :=
          le_trans hmem₁ (le_of_lt ha)
        have hval₂ : (morseModelWithCornersHalfSpace m)
            (c₂ (incl (⟨ψ₁ z, hmem₁⟩ : SublevelSpace g a₁))) =
            morseHalfSpaceShift c₂' (ψ₁ z) := by
          have hdist : dist (ψ₁ z) x.1 < sublevelInteriorRadius g a₂ ⟨x.1, le_of_lt hxlt⟩ hxlt hg := hzB
          have hval := sublevelInteriorChart_apply_value g a₂ ⟨x.1, le_of_lt hxlt⟩ hxlt hg
            (⟨ψ₁ z, hmem₂⟩ : SublevelSpace g a₂) hdist
          have hincl : incl (⟨ψ₁ z, hmem₁⟩ : SublevelSpace g a₁) =
              (⟨ψ₁ z, hmem₂⟩ : SublevelSpace g a₂) := by
            apply Subtype.ext
            rfl
          rw [hincl]
          simpa [morseModelWithCornersHalfSpace] using hval
        have hsymmz : (morseModelWithCornersHalfSpace m).symm z =
            (⟨z, hzmem⟩ : MorseHalfSpace m) := by
          apply Subtype.ext
          exact morseHalfSpaceClamp_of_mem m hzmem
        change (morseModelWithCornersHalfSpace m)
            (c₂ (incl (c₁.symm ((morseModelWithCornersHalfSpace m).symm z)))) = F z
        rw [hsymmz]
        rw [hsymm₁]
        rw [hval₂]
    have hFAt : ContDiffWithinAt ℝ (⊤ : ℕ∞) F
        (Set.range (morseModelWithCornersHalfSpace m))
        (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      have hnhd₁' : sublevelBoundaryChartDomain g a₁ x hx hg (hreg₁ x.1 hx) ∈
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m)) := by
        exact nhdsWithin_le_nhds (hD₁open.mem_nhds hz₀D₁)
      exact hF.contDiffWithinAt hz₀D₁ |>.mono_of_mem_nhdsWithin hnhd₁'
    refine hFAt.congr_of_eventuallyEq_of_mem ?_ hz₀range
    change ((extChartAt (morseModelWithCornersHalfSpace m) (incl x)) ∘ incl ∘
      (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m))]
      (fun z : MorseModel (m + 1) => F z)
    change (((hcs₂.chartAt (incl x)).extend (morseModelWithCornersHalfSpace m)) ∘ incl ∘
      ((hcs₁.chartAt x).extend (morseModelWithCornersHalfSpace m)).symm) =ᶠ[
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m))]
      (fun z : MorseModel (m + 1) => F z)
    rw [hchart₂']
    rw [hchart₁']
    rw [OpenPartialHomeomorph.extend_coe]
    rw [OpenPartialHomeomorph.extend_coe_symm]
    simpa using hred


theorem contMDiff_sublevelMap {m : ℕ} (g₁ g₂ : MorseModel (m + 1) → ℝ)
    (a₁ a₂ : ℝ) (hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁) (hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂)
    (hreg₁ : ∀ x : MorseModel (m + 1), g₁ x = a₁ → fderiv ℝ g₁ x ≠ 0)
    (hreg₂ : ∀ x : MorseModel (m + 1), g₂ x = a₂ → fderiv ℝ g₂ x ≠ 0)
    (Φ : MorseModel (m + 1) → MorseModel (m + 1)) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hmap : ∀ y : MorseModel (m + 1), g₁ y ≤ a₁ → g₂ (Φ y) ≤ a₂)
    (hbnd : ∀ y : MorseModel (m + 1), g₁ y = a₁ → g₂ (Φ y) = a₂)
    (hstrict : ∀ y : MorseModel (m + 1), g₁ y < a₁ → g₂ (Φ y) < a₂)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₁ a₁) :=
      sublevelChartedSpace g₁ a₁ hg₁ hreg₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₂ a₂) :=
      sublevelChartedSpace g₂ a₂ hg₂ hreg₂)
    (hchart₁ : ∀ y : SublevelSpace g₁ a₁, hcs₁.chartAt y =
      (if h : g₁ y.1 = a₁ then sublevelBoundaryChart g₁ a₁ y h hg₁ (hreg₁ y.1 h)
        else sublevelInteriorChart g₁ a₁ y (lt_of_le_of_ne (show g₁ y.1 ≤ a₁ from y.2) h) hg₁) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g₂ a₂, hcs₂.chartAt y =
      (if h : g₂ y.1 = a₂ then sublevelBoundaryChart g₂ a₂ y h hg₂ (hreg₂ y.1 h)
        else sublevelInteriorChart g₂ a₂ y (lt_of_le_of_ne (show g₂ y.1 ≤ a₂ from y.2) h) hg₂) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) := by
  intro x
  by_cases hx : g₁ x.1 = a₁
  · exact contMDiffAt_sublevelBoundaryMap g₁ g₂ a₁ a₂ hg₁ hg₂ hreg₁ hreg₂ x hx Φ hΦ hmap hbnd
      (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
  · have hxlt : g₁ x.1 < a₁ := lt_of_le_of_ne (show g₁ x.1 ≤ a₁ from x.2) hx
    exact contMDiffAt_sublevelInteriorMap g₁ g₂ a₁ a₂ hg₁ hg₂ hreg₁ hreg₂ x hxlt Φ hΦ hmap hstrict
      (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)

theorem contMDiff_sublevelInclusion {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a₁ a₂ : ℝ)
    (ha : a₁ < a₂) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg₁ : ∀ x : MorseModel (m + 1), g x = a₁ → fderiv ℝ g x ≠ 0)
    (hreg₂ : ∀ x : MorseModel (m + 1), g x = a₂ → fderiv ℝ g x ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a₁) :=
      sublevelChartedSpace g a₁ hg hreg₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a₂) :=
      sublevelChartedSpace g a₂ hg hreg₂)
    (hchart₁ : ∀ y : SublevelSpace g a₁, hcs₁.chartAt y =
      (if h : g y.1 = a₁ then sublevelBoundaryChart g a₁ y h hg (hreg₁ y.1 h)
        else sublevelInteriorChart g a₁ y (lt_of_le_of_ne (show g y.1 ≤ a₁ from y.2) h) hg) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g a₂, hcs₂.chartAt y =
      (if h : g y.1 = a₂ then sublevelBoundaryChart g a₂ y h hg (hreg₂ y.1 h)
        else sublevelInteriorChart g a₂ y (lt_of_le_of_ne (show g y.1 ≤ a₂ from y.2) h) hg) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g a₁ => (⟨y.1, by
        change g y.1 ≤ a₂
        exact le_trans (by change g y.1 ≤ a₁; exact y.2) (le_of_lt ha)⟩ :
          SublevelSpace g a₂)) := by
  intro x
  by_cases hx : g x.1 = a₁
  · exact contMDiffAt_sublevelBoundaryInteriorMap g a₁ a₂ ha hg hreg₁ hreg₂ x hx
      (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
  · have hxlt : g x.1 < a₁ := lt_of_le_of_ne (show g x.1 ≤ a₁ from x.2) hx
    exact contMDiffAt_sublevelInteriorMap g g a₁ a₂ hg hg hreg₁ hreg₂ x hxlt id contDiff_id
      (fun y hy => by
        change g y ≤ a₂
        exact le_trans hy (le_of_lt ha))
      (fun y hy => by
        change g y < a₂
        exact lt_of_lt_of_le hy (le_of_lt ha))
      (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)

theorem contMDiff_sublevelInclusion_model {m : ℕ} (g : MorseModel (m + 1) → ℝ) (a : ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hreg : ∀ x : MorseModel (m + 1), g x = a → fderiv ℝ g x ≠ 0)
    (hcs : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) :=
      sublevelChartedSpace g a hg hreg)
    (hchart : ∀ y : SublevelSpace g a, hcs.chartAt y =
      (if h : g y.1 = a then sublevelBoundaryChart g a y h hg (hreg y.1 h)
        else sublevelInteriorChart g a y (lt_of_le_of_ne (show g y.1 ≤ a from y.2) h) hg) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) 𝓘(ℝ, MorseModel (m + 1)) (⊤ : ℕ∞)
      (fun y : SublevelSpace g a => y.1) := by
  classical
  letI := hcs
  intro x
  rw [contMDiffAt_iff]
  constructor
  · exact continuous_subtype_val.continuousAt
  · by_cases hx : g x.1 = a
    · let c : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
        sublevelBoundaryChart g a x hx hg (hreg x.1 hx)
      let ψ₁ : MorseModel (m + 1) → MorseModel (m + 1) :=
        sublevelBoundaryChartInvValueRaw g a x hx hg (hreg x.1 hx)
      let F : MorseModel (m + 1) → MorseModel (m + 1) := ψ₁
      have hchart' : hcs.chartAt x = c := by
        rw [hchart x, dif_pos hx]
      have hz₀range : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
          Set.range (morseModelWithCornersHalfSpace m) := by
        simp [extChartAt, hchart']
      have hz₀D₁ : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
          sublevelBoundaryChartDomain g a x hx hg (hreg x.1 hx) := by
        have hsrc : x ∈ c.source := mem_sublevelBoundaryChart_source g a x hx hg (hreg x.1 hx)
        have htgt : (c x : MorseHalfSpace m) ∈ c.target := c.map_source hsrc
        simpa [extChartAt, hchart', sublevelBoundaryChartDomain] using htgt
      have hF : ContDiffOn ℝ (⊤ : ℕ∞) F
          (sublevelBoundaryChartDomain g a x hx hg (hreg x.1 hx)) := by
        have hraw : ContDiffOn ℝ (⊤ : ℕ∞) ψ₁
            (sublevelBoundaryChartDomain g a x hx hg (hreg x.1 hx)) :=
          contDiffOn_sublevelBoundaryChartInvValueRaw g a x hx hg (hreg x.1 hx)
        simpa [F] using hraw
      have hFAt : ContDiffWithinAt ℝ (⊤ : ℕ∞) F
          (Set.range (morseModelWithCornersHalfSpace m))
          (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
        have hnhd : sublevelBoundaryChartDomain g a x hx hg (hreg x.1 hx) ∈
            nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
              (Set.range (morseModelWithCornersHalfSpace m)) := by
          exact nhdsWithin_le_nhds (isOpen_sublevelBoundaryChartDomain g a x hx hg (hreg x.1 hx) |>.mem_nhds hz₀D₁)
        exact hF.contDiffWithinAt hz₀D₁ |>.mono_of_mem_nhdsWithin hnhd
      have hval : ∀ z ∈ sublevelBoundaryChartDomain g a x hx hg (hreg x.1 hx) ∩
          Set.range (morseModelWithCornersHalfSpace m),
          (extChartAt 𝓘(ℝ, MorseModel (m + 1)) (x.1 : MorseModel (m + 1)) ∘
            (fun y : SublevelSpace g a => y.1) ∘
            (extChartAt (morseModelWithCornersHalfSpace m) x).symm) z = F z := by
        intro z hz
        have hzmem : 0 ≤ z (Fin.last m) := by
          have hzr : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.2
          rw [range_morseModelWithCornersHalfSpace] at hzr
          exact hzr
        have hz₁ : (⟨z, hzmem⟩ : MorseHalfSpace m) ∈ c.target := hz.1
        have hmem₁ : g (ψ₁ z) ≤ a := by
          change g (levelSetReindex (levelSetChartData.mk g a ⟨x.1, hx⟩ hg (hreg x.1 hx)).e
              ((levelSetChartData.mk g a ⟨x.1, hx⟩ hg (hreg x.1 hx)).ψ.symm
                (a - ((⟨z, hzmem⟩ : MorseHalfSpace m) : MorseModel (m + 1)) (Fin.last m),
                  levelSetSplitFst m ((⟨z, hzmem⟩ : MorseHalfSpace m) : MorseModel (m + 1))))) ≤ a
          exact sublevelBoundaryChart_invFun_mem g
            (levelSetChartData.mk g a ⟨x.1, hx⟩ hg (hreg x.1 hx)).e a
            (levelSetChartData.mk g a ⟨x.1, hx⟩ hg (hreg x.1 hx)).ψ
            (levelSetChartData.mk g a ⟨x.1, hx⟩ hg (hreg x.1 hx)).hψ
            (by simpa [sublevelBoundaryChartDomain] using hz.1)
        have hsymm₁ : c.symm (⟨z, hzmem⟩ : MorseHalfSpace m) =
            (⟨ψ₁ z, hmem₁⟩ : SublevelSpace g a) := by
          rw [sublevelBoundaryChart_symm_value g a x hx hg (hreg x.1 hx) hz₁]
          apply Subtype.ext
          rfl
        have hsymmz : (extChartAt (morseModelWithCornersHalfSpace m) x).symm z =
            c.symm (⟨z, hzmem⟩ : MorseHalfSpace m) := by
          change (hcs.chartAt x).symm ((morseModelWithCornersHalfSpace m).symm z) =
            c.symm (⟨z, hzmem⟩ : MorseHalfSpace m)
          rw [hchart']
          congr 1
          apply Subtype.ext
          exact morseHalfSpaceClamp_of_mem m hzmem
        change ((extChartAt (morseModelWithCornersHalfSpace m) x).symm z : SublevelSpace g a).1 = F z
        rw [hsymmz, hsymm₁]
      have hred : (extChartAt 𝓘(ℝ, MorseModel (m + 1)) (x.1 : MorseModel (m + 1)) ∘
            (fun y : SublevelSpace g a => y.1) ∘
            (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
            nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
              (Set.range (morseModelWithCornersHalfSpace m))] F := by
        refine Filter.eventuallyEq_of_mem
          (s := sublevelBoundaryChartDomain g a x hx hg (hreg x.1 hx) ∩
            Set.range (morseModelWithCornersHalfSpace m)) ?_ ?_
        · exact Filter.inter_mem
            (nhdsWithin_le_nhds (isOpen_sublevelBoundaryChartDomain g a x hx hg (hreg x.1 hx) |>.mem_nhds hz₀D₁))
            self_mem_nhdsWithin
        · intro z hz
          exact hval z hz
      refine hFAt.congr_of_eventuallyEq_of_mem ?_ hz₀range
      change ((extChartAt 𝓘(ℝ, MorseModel (m + 1)) (x.1 : MorseModel (m + 1))) ∘
        (fun y : SublevelSpace g a => y.1) ∘
        (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m))]
        (fun z : MorseModel (m + 1) => F z)
      simpa [F, extChartAt, hchart'] using hred
    · let c : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
        sublevelInteriorChart g a x (lt_of_le_of_ne (show g x.1 ≤ a from x.2) hx) hg
      have hchart' : hcs.chartAt x = c := by
        rw [hchart x, dif_neg hx]
      have hz₀range : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
          Set.range (morseModelWithCornersHalfSpace m) := by
        simp [extChartAt, hchart']
      let c' : ℝ := sublevelInteriorShift g a x (lt_of_le_of_ne (show g x.1 ≤ a from x.2) hx) hg
      let F : MorseModel (m + 1) → MorseModel (m + 1) := fun z => morseHalfSpaceShift (-c') z
      have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
        have hshift : ContDiff ℝ (⊤ : ℕ∞) (morseHalfSpaceShift (-c')) :=
          contDiff_morseHalfSpaceShift (m := m) (-c')
        simpa [F] using hshift
      have hFAt : ContDiffWithinAt ℝ (⊤ : ℕ∞) F
          (Set.range (morseModelWithCornersHalfSpace m))
          (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
        hF.contDiffWithinAt
      have hz₀c : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
          (morseModelWithCornersHalfSpace m) '' c.target := by
        have hsrc : x ∈ c.source := mem_sublevelInteriorChart_source g a x
          (lt_of_le_of_ne (show g x.1 ≤ a from x.2) hx) hg
        have htgt : (c x : MorseHalfSpace m) ∈ c.target := c.map_source hsrc
        refine ⟨c x, htgt, ?_⟩
        simp [extChartAt, hchart']
      have hval : ∀ z ∈ (morseModelWithCornersHalfSpace m) '' c.target,
          (extChartAt 𝓘(ℝ, MorseModel (m + 1)) (x.1 : MorseModel (m + 1)) ∘
            (fun y : SublevelSpace g a => y.1) ∘
            (extChartAt (morseModelWithCornersHalfSpace m) x).symm) z = F z := by
        intro z hz
        rcases hz with ⟨z', hz'tgt, hz⟩
        have hzr : z ∈ Set.range (morseModelWithCornersHalfSpace m) := ⟨z', hz⟩
        have hzmem : 0 ≤ z (Fin.last m) := by
          rw [range_morseModelWithCornersHalfSpace] at hzr
          exact hzr
        have hz'symm : (⟨z, hzmem⟩ : MorseHalfSpace m) = z' := by
          apply Subtype.ext
          exact hz.symm
        have hztgt : dist (morseHalfSpaceShift (-c') ((z' : MorseHalfSpace m) : MorseModel (m + 1))) x.1 <
            sublevelInteriorRadius g a x (lt_of_le_of_ne (show g x.1 ≤ a from x.2) hx) hg := by
          change (z' : MorseHalfSpace m) ∈ c.target
          exact hz'tgt
        have hztgt0 : dist (morseHalfSpaceShift (-c') (z : MorseModel (m + 1))) x.1 <
            sublevelInteriorRadius g a x (lt_of_le_of_ne (show g x.1 ≤ a from x.2) hx) hg := by
          rw [← hz]
          exact hztgt
        have hsymm1 : (c.symm (⟨z, hzmem⟩ : MorseHalfSpace m) : SublevelSpace g a).1 =
            morseHalfSpaceShift (-c') (((⟨z, hzmem⟩ : MorseHalfSpace m) : MorseModel (m + 1))) := by
          exact congrArg Subtype.val (sublevelInteriorChart_symm_value g a x
            (lt_of_le_of_ne (show g x.1 ≤ a from x.2) hx) hg hztgt0)
        have hsymmz : (extChartAt (morseModelWithCornersHalfSpace m) x).symm z =
            c.symm (⟨z, hzmem⟩ : MorseHalfSpace m) := by
          change (hcs.chartAt x).symm ((morseModelWithCornersHalfSpace m).symm z) =
            c.symm (⟨z, hzmem⟩ : MorseHalfSpace m)
          rw [hchart']
          congr 1
          apply Subtype.ext
          exact morseHalfSpaceClamp_of_mem m hzmem
        change ((extChartAt (morseModelWithCornersHalfSpace m) x).symm z : SublevelSpace g a).1 = F z
        rw [hsymmz]
        rw [hsymm1]
      have hred : (extChartAt 𝓘(ℝ, MorseModel (m + 1)) (x.1 : MorseModel (m + 1)) ∘
            (fun y : SublevelSpace g a => y.1) ∘
            (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
            nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
              (Set.range (morseModelWithCornersHalfSpace m))] F := by
        refine Filter.eventuallyEq_of_mem
          (s := (morseModelWithCornersHalfSpace m) '' c.target) ?_ ?_
        · have hIemb : Topology.IsEmbedding (fun x : MorseHalfSpace m =>
              (morseModelWithCornersHalfSpace m) x) :=
            by
              change Topology.IsEmbedding (fun x : MorseHalfSpace m => (x : MorseModel (m + 1)))
              exact Topology.IsEmbedding.subtypeVal
          have hsrc : x ∈ c.source := mem_sublevelInteriorChart_source g a x
            (lt_of_le_of_ne (show g x.1 ≤ a from x.2) hx) hg
          have hmem : c.target ∈ 𝓝 (c x : MorseHalfSpace m) :=
            c.open_target.mem_nhds (c.map_source hsrc)
          have himg := hIemb.isInducing.image_mem_nhdsWithin hmem
          simpa [extChartAt, hchart'] using himg
        · intro z hz
          exact hval z hz
      refine hFAt.congr_of_eventuallyEq_of_mem ?_ hz₀range
      change ((extChartAt 𝓘(ℝ, MorseModel (m + 1)) (x.1 : MorseModel (m + 1))) ∘
        (fun y : SublevelSpace g a => y.1) ∘
        (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m))]
        (fun z : MorseModel (m + 1) => F z)
      simpa [F, extChartAt, hchart'] using hred

end DifferentialGeometry.Topology.Morse
