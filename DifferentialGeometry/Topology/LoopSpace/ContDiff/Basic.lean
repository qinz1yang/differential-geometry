import DifferentialGeometry.Topology.LoopSpace.Regular



noncomputable section

open Function ContinuousMap Manifold
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology



abbrev finiteRegularLoop (r : ℕ) (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] :=
  {γ : freeLoop M // ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) r (fun t : ℝ => γ (t : loopCircle))}

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]


def finiteLoopJet (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (r : ℕ) (γ : finiteRegularLoop r E M) (i : Fin (r + 1)) : freeLoop F :=
  periodicLoop (iteratedDeriv i.val (fun t : ℝ => e (γ.val (t : loopCircle))))
    (periodic_iteratedDeriv (n := i.val) (by
      intro t
      simp only [QuotientAddGroup.mk_add, AddCircle.coe_period, add_zero]))
    ((contDiff_nat_iff_iteratedDeriv.mp
      (((he.of_le (by exact_mod_cast le_top)).comp γ.property).contDiff)).1
        i.val (Nat.lt_succ_iff.mp i.isLt))

@[simp] theorem finiteLoopJet_coe (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (r : ℕ)
    (γ : finiteRegularLoop r E M) (i : Fin (r + 1)) (t : ℝ) :
    finiteLoopJet e he r γ i (t : loopCircle) =
      iteratedDeriv i.val (fun s : ℝ => e (γ.val (s : loopCircle))) t := rfl



@[instance_reducible] def finiteRegularLoopTopology (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (r : ℕ) :
    TopologicalSpace (finiteRegularLoop r E M) :=
  TopologicalSpace.induced (finiteLoopJet e he r) inferInstance

variable {K : Type*} [TopologicalSpace K]



theorem continuous_finiteRegularLoop_iff (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e) (r : ℕ) (Γ : K → finiteRegularLoop r E M) :
    Continuous[inferInstance, finiteRegularLoopTopology e he r] Γ ↔
      ∀ i : Fin (r + 1), Continuous (fun p : K × ℝ =>
        iteratedDeriv i.val (fun t : ℝ => e ((Γ p.1).val (t : loopCircle))) p.2) := by
  change Continuous[inferInstance, TopologicalSpace.induced (finiteLoopJet e he r) _] Γ ↔ _
  rw [continuous_induced_rng]
  constructor
  · intro h i
    have hi := (FreeLoop.continuous_family_iff _).mp (continuous_apply i |>.comp h)
    exact hi.comp
      (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))
  · intro h
    apply continuous_pi
    intro i
    exact continuous_periodicLoop_family (h i) _

end DifferentialGeometry.Topology
