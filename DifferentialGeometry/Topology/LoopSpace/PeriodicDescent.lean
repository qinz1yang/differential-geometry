import DifferentialGeometry.Topology.LoopSpace.UniformSmoothing



noncomputable section

open ContinuousMap Function
open scoped Topology

namespace DifferentialGeometry.Topology

variable {K Q : Type*} [TopologicalSpace K] [TopologicalSpace Q]


def periodicLoop (f : ℝ → Q) (hp : Periodic f 1) (hc : Continuous f) : freeLoop Q :=
  ⟨hp.lift, hc.quotient_liftOn' _⟩

@[simp] theorem periodicLoop_coe (f : ℝ → Q) (hp : Periodic f 1) (hc : Continuous f) (t : ℝ) :
    periodicLoop f hp hc (t : loopCircle) = f t := rfl



theorem continuous_periodic_family {f : K × ℝ → Q} (hf : Continuous f)
    (hp : ∀ k, Periodic (fun t => f (k, t)) 1) :
    Continuous (fun p : K × loopCircle => (hp p.1).lift p.2) := by
  have hq := (_root_.IsOpenQuotientMap.id (X := K)).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ)))
  apply hq.isQuotientMap.continuous_iff.mpr
  exact hf


theorem continuous_periodicLoop_family {f : K × ℝ → Q} (hf : Continuous f)
    (hp : ∀ k, Periodic (fun t => f (k, t)) 1) :
    Continuous (fun k => periodicLoop (fun t => f (k, t)) (hp k)
      (hf.comp (continuous_const.prodMk continuous_id))) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_periodic_family hf hp)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]


def averagedLoop (φ : ContDiffBump (0 : ℝ)) (γ : freeLoop F) : freeLoop F :=
  periodicLoop (DifferentialGeometry.Analysis.smoothPeriodic φ (fun t : ℝ => γ (t : loopCircle)))
    (DifferentialGeometry.Analysis.smoothPeriodic_periodic φ (by
      intro t
      simp only [QuotientAddGroup.mk_add, AddCircle.coe_period, add_zero]))
    (DifferentialGeometry.Analysis.smoothPeriodic_contDiff φ
      (γ.continuous.comp (AddCircle.continuous_mk' (1 : ℝ)))).continuous

@[simp] theorem averagedLoop_coe (φ : ContDiffBump (0 : ℝ)) (γ : freeLoop F) (t : ℝ) :
    averagedLoop φ γ (t : loopCircle) =
      DifferentialGeometry.Analysis.smoothPeriodic φ (fun s : ℝ => γ (s : loopCircle)) t := rfl

@[simp] theorem averagedLoop_const [CompleteSpace F] (φ : ContDiffBump (0 : ℝ)) (v : F) :
    averagedLoop φ (.const loopCircle v) = .const loopCircle v := by
  ext θ
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  exact congrFun (DifferentialGeometry.Analysis.smoothPeriodic_const φ v) t

theorem averagedLoop_continuous_family (φ : ContDiffBump (0 : ℝ))
    {Γ : K → freeLoop F} (hΓ : Continuous Γ) :
    Continuous (fun k => averagedLoop φ (Γ k)) := by
  have hf : Continuous (fun p : K × ℝ => Γ p.1 (p.2 : loopCircle)) :=
    continuous_eval.comp ((hΓ.comp continuous_fst).prodMk
      ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))
  have hs := DifferentialGeometry.Analysis.continuous_iteratedDeriv_smoothPeriodic φ hf 0
  simp only [iteratedDeriv_zero] at hs
  exact continuous_periodicLoop_family hs _

end DifferentialGeometry.Topology
