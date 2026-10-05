import DifferentialGeometry.Topology.LoopSpace.SmoothFamily.ModelSpaceVelocity
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth

section


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening


section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {a b : ℝ}

def LoopFamilyGlobalSmoothExtension (a b : ℝ) (γ : ℝ → DifferentialGeometry.Topology.freeLoop E) : Prop :=
  ∃ γ' : ℝ → DifferentialGeometry.Topology.freeLoop E,
    (∀ t ∈ Icc a b, γ' t = γ t) ∧
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ' q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)) ∧
    (∀ t, Function.Injective (fun z : DifferentialGeometry.Topology.loopCircle => γ' t z)) ∧
    ∀ q, Function.Injective (fderiv ℝ (graphLift γ') q)

omit [FiniteDimensional ℝ E] in
theorem loopFamilyGlobalSmoothExtension_of_globalSmooth
    {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle)))
    (hemb : ∀ t, Function.Injective (fun z : DifferentialGeometry.Topology.loopCircle => γ t z))
    (hi : ∀ q, Function.Injective (fderiv ℝ (graphLift γ) q)) :
    LoopFamilyGlobalSmoothExtension a b γ :=
  ⟨γ, fun _ _ => rfl, hγ, hemb, hi⟩

theorem loopFamilyVelocityExtension_modelSpace_of_globalSmoothExtension
    {γ : ℝ → DifferentialGeometry.Topology.freeLoop E} (h : LoopFamilyGlobalSmoothExtension a b γ) :
    LoopFamilyVelocityExtension (I := 𝓘(ℝ, E)) a b γ := by
  obtain ⟨γ', hagree, hγ', hemb', hi'⟩ := h
  obtain ⟨X, hX, hIco, hIoc⟩ := loopFamilyVelocityExtension_modelSpace a b γ' hemb' hγ' hi'
  refine ⟨X, hX, ?_, ?_⟩
  · intro t ht z
    have htIcc : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hsub : Iio (t + (b - t)) ∩ Ici t ⊆ Icc a b := by
      rintro s ⟨hs1, hs2⟩
      refine ⟨le_trans ht.1 hs2, ?_⟩
      have : s < b := by
        have h1 : t + (b - t) = b := by ring
        rwa [h1] at hs1
      exact this.le
    have hmem : Icc a b ∈ 𝓝[Ici t] t :=
      mem_of_superset
        (inter_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by
            have h1 : t + (b - t) = b := by ring
            rw [h1]; exact ht.2)))
          self_mem_nhdsWithin) hsub
    have heq : (fun s : ℝ => γ s z) =ᶠ[𝓝[Ici t] t] (fun s : ℝ => γ' s z) :=
      eventually_of_mem hmem fun s hs =>
        (congrArg (fun f : DifferentialGeometry.Topology.freeLoop E => f z) (hagree s hs)).symm
    have hx : γ t z = γ' t z :=
      (congrArg (fun f : DifferentialGeometry.Topology.freeLoop E => f z) (hagree t htIcc)).symm
    have hbase := hIco t ht z
    rw [show X t (γ' t z) = X t (γ t z) from by rw [hx]] at hbase
    exact hbase.congr_of_eventuallyEq heq hx
  · intro t ht z
    have htIcc : t ∈ Icc a b := Ioc_subset_Icc_self ht
    have hsub : Ioi (t - (t - a)) ∩ Iic t ⊆ Icc a b := by
      rintro s ⟨hs1, hs2⟩
      refine ⟨?_, le_trans hs2 ht.2⟩
      have : a < s := by
        have h1 : t - (t - a) = a := by ring
        rwa [h1] at hs1
      exact this.le
    have hmem : Icc a b ∈ 𝓝[Iic t] t :=
      mem_of_superset
        (inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by
            have h1 : t - (t - a) = a := by ring
            rw [h1]; exact ht.1)))
          self_mem_nhdsWithin) hsub
    have heq : (fun s : ℝ => γ s z) =ᶠ[𝓝[Iic t] t] (fun s : ℝ => γ' s z) :=
      eventually_of_mem hmem fun s hs =>
        (congrArg (fun f : DifferentialGeometry.Topology.freeLoop E => f z) (hagree s hs)).symm
    have hx : γ t z = γ' t z :=
      (congrArg (fun f : DifferentialGeometry.Topology.freeLoop E => f z) (hagree t htIcc)).symm
    have hbase := hIoc t ht z
    rw [show X t (γ' t z) = X t (γ t z) from by rw [hx]] at hbase
    exact hbase.congr_of_eventuallyEq heq hx

end ModelSpace

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end


section


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {a b : ℝ}

omit [FiniteDimensional ℝ E] in
theorem loopFamilyGlobalSmoothExtension_of_smoothOn_superwindow {α β : ℝ}
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle))
      (Icc α β ×ˢ univ))
    (hemb : ∀ t ∈ Icc α β, Function.Injective (fun z : DifferentialGeometry.Topology.loopCircle => γ t z))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) (Icc α β)) :
    LoopFamilyGlobalSmoothExtension a b γ := by
  have hmaps : MapsTo (fun q : ℝ × ℝ => (loopTimeFold a b α β q.1, q.2)) univ
      (Icc α β ×ˢ univ) :=
    fun q _ => ⟨by simpa using loopTimeFold_mem_Icc (t := q.1) hα hab hβ, trivial⟩
  have hfold : ContDiff ℝ ∞ (fun q : ℝ × ℝ => (loopTimeFold a b α β q.1, q.2)) :=
    ((contDiff_loopTimeFold a b α β).comp contDiff_fst).prodMk contDiff_snd
  have hsm : ContDiff ℝ ∞
      (fun q : ℝ × ℝ => γ (loopTimeFold a b α β q.1) (q.2 : DifferentialGeometry.Topology.loopCircle)) := by
    have hcomp := hγ.comp hfold.contDiffOn hmaps
    rw [contDiffOn_univ] at hcomp
    exact hcomp
  refine ⟨fun t => γ (loopTimeFold a b α β t), ?_, hsm, ?_, ?_⟩
  · intro t ht
    change γ (loopTimeFold a b α β t) = γ t
    rw [loopTimeFold_eq_self hα hβ ht]
  · intro t
    change Function.Injective (fun z : DifferentialGeometry.Topology.loopCircle => γ (loopTimeFold a b α β t) z)
    exact hemb _ (loopTimeFold_mem_Icc (t := t) hα hab hβ)
  · intro q
    have himm : (curveOfLoopFamily (fun t : ℝ => γ (loopTimeFold a b α β t))).ImmersedOn
        (I := 𝓘(ℝ, E)) univ :=
      fun x t _ => hi x _ (loopTimeFold_mem_Icc (t := t) hα hab hβ)
    exact injective_fderiv_graphLift_of_immersedOn hsm himm (mem_univ q)

theorem loopFamilyVelocityExtension_modelSpace_of_smoothOn_superwindow {α β : ℝ}
    (hα : α < a) (hab : a ≤ b) (hβ : b < β) {γ : ℝ → DifferentialGeometry.Topology.freeLoop E}
    (hγ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle))
      (Icc α β ×ˢ univ))
    (hemb : ∀ t ∈ Icc α β, Function.Injective (fun z : DifferentialGeometry.Topology.loopCircle => γ t z))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := 𝓘(ℝ, E)) (Icc α β)) :
    LoopFamilyVelocityExtension (I := 𝓘(ℝ, E)) a b γ :=
  loopFamilyVelocityExtension_modelSpace_of_globalSmoothExtension
    (loopFamilyGlobalSmoothExtension_of_smoothOn_superwindow hα hab hβ hγ hemb hi)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end
