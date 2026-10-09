import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5EvolutionRegularity
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5Decay

/-!
# Power decay of the traceless Hessian of the potential

Chapter 7, packet P8, surface lemma U1, route (a), step a5.2 (potential gauge, design D18 (ii′),
review 18 §1.3).

* `surfaceFlow_tracelessHess_normSq_contMDiffOn` (`…A5EvolutionRegularity`) supplies the joint
  smoothness of `(t, x) ↦ |M(t, x)|²_{g(t)}` on `(0, T) × M`.
* `surfaceFlow_tracelessHess_decay` (D18 (ii′), frozen): with a4's lower bound
  `R · 2 (T* - t) ≥ c`, `(T* - t)² |M|²_{g(t)} ≤ C (T* - t)^c` on `[t₀, T)`. The evolution (ii)
  makes `|M|²` a nonnegative subsolution of `∂ₜ u ≤ Δ u + (2 / (T* - t) - 2 R) u`
  (`surfaceFlow_tracelessHess_normSq_evolution`), and `surfaceFlow_le_rpow_of_heat_subsolution`
  applies with the exponent exactly `c`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open Bundle Filter Topology Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {T : ℝ} {hT : 0 < T}

omit [I.Boundaryless] [T2Space M] in
theorem normSq0S_nonneg_of_basis (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x) :
    0 ≤ normSq0S g x s A := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  rw [normSq0S_identity_eq_sum_sq g x s basis (metricInverseInBasis_of_orthonormal g basis hON) A]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem surfaceFlow_tracelessHess_decay [NeZero (Module.finrank ℝ E)] [CompactSpace M]
    [ConnectedSpace M] (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) (f : ℝ → C^∞⟮I, M; ℝ⟯)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2) (Ioo 0 T ×ˢ univ))
    (hfeq : ∀ t ∈ Ioo 0 T, ∀ x,
      ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t))
    {a : ℝ → ℝ} (hft : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => f s x)
      (S.scalar t x + f t x / (flowExtinctionTime S - t) + a t) t)
    (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hM : ∀ t ∈ Ioo 0 T, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
    {c : ℝ} (hc : 0 < c)
    (hlow : ∀ t ∈ Ico 0 T, ∀ x, c ≤ S.scalar t x * (2 * (flowExtinctionTime S - t)))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) :
    ∃ C : ℝ, ∀ t ∈ Ico t₀ T, ∀ x,
      (flowExtinctionTime S - t) ^ 2 * normSq0S (S.family.metric t) x 2 (Mf t x) ≤
        C * (flowExtinctionTime S - t) ^ c := by
  have _ := hc
  have hTT : T ≤ flowExtinctionTime S := surfaceFlow_le_extinctionTime hT S hS hdim hscal
  refine surfaceFlow_le_rpow_of_heat_subsolution S hTT
    (fun s y => normSq0S (S.family.metric s) y 2 (Mf s y))
    (surfaceFlow_tracelessHess_normSq_contMDiffOn hdim S hS f hf hTT hfeq Mf hM)
    (fun t _ x => normSq0S_nonneg_of_basis _ x 2 _) (fun t ht x => ?_)
    (fun t ht x => hlow t (Ioo_subset_Ico_self ht) x) ht₀
  refine ⟨_, surfaceFlow_tracelessHess_normSq_evolution hdim S hS hscal f hf hfeq hft Mf hM t ht
    x, ?_⟩
  have h := normSq0S_nonneg_of_basis (S.family.metric t) x (2 + 1)
    (iterCov (S.family.metric t) 2 (Mf t) 1 x)
  linarith

end GC.Geometry
