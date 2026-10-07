import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollarFlowR7E

/-!
# O-MY-R7E G3-c：level projection 的 Jacobian 估计 `‖dR‖ ≤ 1`

R-MY3 确认的核心估计。`R(z) = D (ρ z − c) z`（`D` 为 level field `X` 的 flow），`τ = ρ y − c ≥ 0`：

1. `dR ξ = dρ(ξ) X(R y) + dD_τ ξ`（`mfderiv_collarFlow_joint_R7E`）；
2. `ξ_T := ξ + dρ(ξ) X(y) ∈ ker dρ`（`dρ(X) = −1`），flow 不变量 `dD_τ X(y) = X(D_τ y)`
   ⇒ `dR ξ = dD_τ ξ_T`；
   特别地 `dR(X) = 0`；
3. `J_s = dD_s ξ_T` 始终在 `ker dρ` 里（`ρ ∘ D_s = ρ − s` 在 `y` 附近），
   `d/ds |J_s|² = L_X G(J_s, J_s) ≤ 0`（`hlie`；具体场里是 `−2 Hess ρ(J, J)/|∇ρ|²`）⇒ `|dD_τ ξ_T| ≤ |ξ_T|`；
4. 正交分解 `ξ = ξ_T − dρ(ξ) X`，`G(X, ξ_T) = 0` ⇒ `|ξ_T| ≤ |ξ|`。

结论 `|dR ξ|_G ≤ |ξ|_G`（`collarProjection_mfderiv_le_R7E`），从而 `‖Λ² dR‖ ≤ 1`。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]

section Jacobian

variable (X : Cₛ^∞⟮𝓘(ℝ, E); E, (TangentSpace 𝓘(ℝ, E) : N → Type _)⟯)
  (hXc : IsCompact (tsupport (X : (x : N) → TangentSpace 𝓘(ℝ, E) x)))
  (G : SmoothRiemannianMetric 𝓘(ℝ, E) N)
  {ρ : N → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) {β : ℝ → ℝ}
  (hdρ : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y (X y) = -β (ρ y))
  (hβ0 : ∀ r, 0 ≤ β r) (hβ1 : ∀ r, β r ≤ 1) {a b : ℝ}
  (hβeq : ∀ r, a ≤ r → r ≤ b → β r = 1)

include hρ hdρ hβ0 hβ1 hβeq in
/-- `ρ ∘ D_s = ρ − s` 在 `y` 的邻域上（`a < c ≤ ρ y < b`，`0 ≤ s ≤ ρ y − c`）。 -/
theorem rho_collarFlow_eventuallyEq_R7E {c : ℝ} (hac : a < c) {y : N} (hyb : ρ y < b)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ ρ y - c) :
    (fun z => ρ (collarFlow_R7E X hXc s z)) =ᶠ[𝓝 y] fun z => ρ z - s := by
  have hopen : IsOpen {z : N | a < ρ z - (ρ y - c) ∧ ρ z < b} :=
    (isOpen_lt continuous_const (hρ.continuous.sub continuous_const)).inter
      (isOpen_lt hρ.continuous continuous_const)
  have hy : y ∈ {z : N | a < ρ z - (ρ y - c) ∧ ρ z < b} := ⟨by linarith, hyb⟩
  filter_upwards [hopen.mem_nhds hy] with z hz
  exact rho_collarFlow_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hz.2.le hs0 (by linarith [hz.1])

include hρ hdρ hβ0 hβ1 hβeq in
/-- `dD_s` 保持 `ker dρ`。 -/
theorem mfderiv_rho_collarFlow_R7E {c : ℝ} (hac : a < c) {y : N} (hyb : ρ y < b)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ ρ y - c) (w : TangentSpace 𝓘(ℝ, E) y) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ (collarFlow_R7E X hXc s y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc s) y w) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y w := by
  have hρD : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ (collarFlow_R7E X hXc s y) :=
    (hρ _).mdifferentiableAt (by simp)
  have hD : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc s) y :=
    (collarFlow_R7E X hXc s).contMDiff.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp y hρD hD
  have heq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => ρ (collarFlow_R7E X hXc s z)) y =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => ρ z - s) y :=
    (rho_collarFlow_eventuallyEq_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hac hyb hs0 hs).mfderiv_eq
  have hsub : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => ρ z - s) y = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y := by
    have hc : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun _ : N => s) y 0 := hasMFDerivAt_const s y
    have h := ((hρ y).mdifferentiableAt (by simp)).hasMFDerivAt.sub hc
    exact h.mfderiv.trans (sub_zero _)
  have h := congrArg (fun L => L w) (hcomp.symm.trans (heq.trans hsub))
  exact h

include hρ hdρ hβ0 hβ1 hβeq in
/-- **Jacobian 估计**（R-MY3）：`a < c ≤ ρ y < b`、`[c, ρ y]` 层上 `L_X G ≤ 0` on `ker dρ`、
`X ⊥ ker dρ` ⇒ `|dR ξ|² ≤ |ξ|²`，`R z = D (ρ z − c) z`。 -/
theorem collarProjection_mfderiv_le_R7E
    (hperp : ∀ y (w : TangentSpace 𝓘(ℝ, E) y), mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y w = 0 →
      G.inner y (X y) w = 0)
    {c : ℝ} (hac : a < c) {y : N} (hcy : c ≤ ρ y) (hyb : ρ y < b)
    (hlie : ∀ x, c ≤ ρ x → ρ x ≤ ρ y → ∀ w : TangentSpace 𝓘(ℝ, E) x,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ x w = 0 → PDE.DeTurck.lieDerivMetric G X x w w ≤ 0)
    (ξ : TangentSpace 𝓘(ℝ, E) y) :
    G.inner (collarFlow_R7E X hXc (ρ y - c) y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => collarFlow_R7E X hXc (ρ z - c) z) y ξ)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => collarFlow_R7E X hXc (ρ z - c) z) y ξ) ≤
      G.inner y ξ ξ := by
  set d : ℝ := mvfderiv 𝓘(ℝ, E) ρ y ξ with hd
  set ξT : TangentSpace 𝓘(ℝ, E) y := ξ + d • X y with hξT
  have hβy : β (ρ y) = 1 := hβeq _ (by linarith) hyb.le
  have hTker : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ρ y ξT = 0 := by
    rw [hξT, map_add, map_smul, hdρ, hβy]
    change d + d * (-1 : ℝ) = 0
    ring
  have hdR : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => collarFlow_R7E X hXc (ρ z - c) z) y ξ =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (collarFlow_R7E X hXc (ρ y - c)) y ξT := by
    rw [mfderiv_collarFlow_joint_R7E X hXc hρ c y ξ, hξT, map_add, map_smul,
      mfderiv_collarFlow_field_R7E, add_comm]
  have hτ : 0 ≤ ρ y - c := by linarith
  have hcon := collarFlow_pairing_le_R7E X hXc G y ξT hτ (fun s hs => by
    have hρs : ρ (collarFlow_R7E X hXc s y) = ρ y - s :=
      rho_collarFlow_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hyb.le hs.1 (by linarith [hs.2])
    apply hlie _ (by rw [hρs]; linarith [hs.2]) (by rw [hρs]; linarith [hs.1])
    rw [mfderiv_rho_collarFlow_R7E X hXc hρ hdρ hβ0 hβ1 hβeq hac hyb hs.1 hs.2 ξT]
    exact hTker)
  have horth : G.inner y ξT ξT ≤ G.inner y ξ ξ := by
    have h1 : G.inner y (X y) ξT = 0 := hperp y ξT hTker
    rw [hξT, map_add, map_smul] at h1
    have hXX := metric_inner_self_nonneg G y (X y)
    have hsymm := G.symm y ξ (X y)
    rw [hξT, map_add, map_add, map_smul, map_smul]
    simp only [add_apply, smul_apply, smul_eq_mul] at h1 ⊢
    rw [hsymm]
    have hX : G.inner y (X y) ξ = -(d * G.inner y (X y) (X y)) := by linarith
    rw [hX]
    nlinarith [mul_nonneg (sq_nonneg d) hXX]
  rw [hdR]
  exact hcon.trans horth

end Jacobian

end DifferentialGeometry.Geometry
