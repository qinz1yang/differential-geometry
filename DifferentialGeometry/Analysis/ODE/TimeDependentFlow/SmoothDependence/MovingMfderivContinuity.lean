import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Time-continuity of the moving spatial differential of a jointly-smooth flow

For a flow `Φg : M → ℝ → M` that is jointly `C∞` in `(time, point)` on an open
slab `O ×ˢ univ`, the moving spatial differential at a fixed seed `(y, u)` —
packaged inside the tangent bundle as `s ↦ ⟨Φg y s, mfderiv (Φg · s) y u⟩` — is
continuous in time at each `s₀ ∈ O`.

This is the smooth-dependence-on-the-initial-condition continuity of the moving
Jacobian (the object whose time-variation feeds the Cartan-cancellation chain),
read off the joint smoothness via `ContMDiffWithinAt.mfderivWithin` (the moving
spatial differential is `C∞` in time) and `ContMDiffAt.clm_apply_of_inCoordinates`
(applying that `C∞` family of differentials to the seed vector, tracked coherently
in tangent-bundle coordinates).
-/

noncomputable section
open Set Function Filter Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

set_option linter.unusedSectionVars false in
/-- **Time-continuity of the moving spatial differential of a jointly-smooth flow.**

If `Φg` is jointly `C∞` in `(time, point)` on `O ×ˢ univ` for an open `O ∋ s₀`,
then the tangent-bundle datum `s ↦ ⟨Φg y s, mfderiv (Φg · s) y u⟩` is continuous
at `s₀`. The moving spatial differential `s ↦ mfderivWithin I I (Φg · s) univ y`
is `C∞` in `s` by `ContMDiffWithinAt.mfderivWithin`, and applying that family to the
fixed seed `u` (coherently in bundle coordinates) is continuous by
`ContMDiffAt.clm_apply_of_inCoordinates`. -/
theorem slice_mfderiv_continuousAt_of_jointFlow
    (Φg : M → ℝ → M) {O : Set ℝ} (hO : IsOpen O) {s₀ : ℝ} (hs₀ : s₀ ∈ O)
    (hΦg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φg q.2 q.1) (O ×ˢ Set.univ))
    (y : M) (u : TangentSpace I y) :
    ContinuousAt (fun s : ℝ => (TotalSpace.mk' E (Φg y s)
      (mfderiv I I (fun x => Φg x s) y u) : TangentBundle I M)) s₀ := by
  have hf : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞
      (Function.uncurry (fun s x => Φg x s)) (O ×ˢ Set.univ) (s₀, y) :=
    hΦg (s₀, y) ⟨hs₀, Set.mem_univ _⟩
  have hg : ContMDiffWithinAt (𝓘(ℝ, ℝ)) I ∞ (fun _ : ℝ => y) O s₀ := contMDiffWithinAt_const
  have hmf := ContMDiffWithinAt.mfderivWithin (J := 𝓘(ℝ, ℝ)) (I := I) (I' := I)
    (n := ∞) (m := ∞) (f := fun s x => Φg x s) (g := fun _ : ℝ => y) (t := O) (u := Set.univ)
    hf hg hs₀ (Set.mapsTo_univ _ _) (le_refl _) uniqueMDiffOn_univ
  have hmfAt := hmf.contMDiffAt (hO.mem_nhds hs₀)
  have hb₂ : ContMDiffAt (𝓘(ℝ, ℝ)) I ∞ (fun s : ℝ => Φg y s) s₀ := by
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞ (fun s : ℝ => (s, y)) s₀ :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact ((hΦg.contMDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hs₀, Set.mem_univ _⟩)).comp s₀ hcomp)
  have hv : ContMDiffAt (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun _ : ℝ => (TotalSpace.mk' E y u : TangentBundle I M)) s₀ := contMDiffAt_const
  have happ := ContMDiffAt.clm_apply_of_inCoordinates
    (F₁ := E) (E₁ := TangentSpace I (M := M)) (F₂ := E) (E₂ := TangentSpace I (M := M))
    (IB₁ := I) (IB₂ := I) (IM := 𝓘(ℝ, ℝ)) (n := ∞)
    (b₁ := fun _ : ℝ => y) (b₂ := fun s : ℝ => Φg y s) (m₀ := s₀)
    (ϕ := fun s : ℝ => mfderivWithin I I (fun x => Φg x s) Set.univ y)
    (v := fun _ : ℝ => u)
    hmfAt hv hb₂
  have hcont := happ.continuousAt
  simp only [mfderivWithin_univ] at hcont
  exact hcont

end DifferentialGeometry.PDE.RicciFlow.ODE
