import DifferentialGeometry.Topology.Manifold.ImmersionInterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryNaturalityRaw

set_option autoImplicit false

/-! # CH12-S136 G1b: `local_curve_S136` — the implicit curve `σ ↦ c σ` with `Θ (σ, c σ) = const`

`Θ : ℝ × M → D` smooth on an open `U ∋ (σ1, x1)`, with `d_x Θ (σ1, ·)` injective at `x1` (`dim M = dim D = 3`).
Then `Θ̂ (σ, x) = (σ, Θ (σ, x))` is a local diffeomorphism at `(σ1, x1)` (inverse function theorem on the open
subtype `U`), and `c σ := (Θ̂⁻¹ (σ, Θ (σ1, x1))).2` is smooth near `σ1`, `c σ1 = x1`, `Θ (σ, c σ) = Θ (σ1, x1)`. -/

noncomputable section
open Set Filter Topology DifferentialGeometry Manifold TopologicalSpace DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

theorem local_curve_S136 {M D : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
    [TopologicalSpace D] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) D] [IsManifold (𝓡 3) ∞ D]
    (Θ : ℝ × M → D) (U : Opens (ℝ × M)) (hΘ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ Θ U)
    {σ1 : ℝ} {x1 : M} (hx : (σ1, x1) ∈ U)
    (hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun x => Θ (σ1, x)) x1)) :
    ∃ c : ℝ → M, c σ1 = x1 ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Ioo (σ1 - δ) (σ1 + δ),
      (σ, c σ) ∈ U ∧ Θ (σ, c σ) = Θ (σ1, x1) ∧ ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ c σ := by
  classical
  let Θh : ℝ × M → ℝ × D := fun p => (p.1, Θ p)
  have hΘh : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞ Θh U :=
    contMDiffOn_fst.prodMk hΘ
  let z0 : U := ⟨(σ1, x1), hx⟩
  have hsm := contMDiff_restrict_C4 Θh U hΘh
  have hΘd : ∀ p ∈ (U : Set (ℝ × M)), MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) Θ p :=
    fun p hp => (hΘ.contMDiffAt (U.isOpen.mem_nhds hp)).mdifferentiableAt (by simp)
  have hder : ∀ p ∈ (U : Set (ℝ × M)), mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) Θh p =
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) Prod.fst p).prod
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) Θ p) := fun p hp =>
    mfderiv_prodMk mdifferentiableAt_fst (hΘd p hp)
  have hinj' : Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3))
      (fun z : U => Θh z) z0) := by
    have hz0 : (z0 : ℝ × M) ∈ (U : Set (ℝ × M)) := z0.2
    have hT : ∀ v, mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) (fun z : U => Θh z) z0 v =
        mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) Θh (z0 : ℝ × M) v :=
      fun v => mfderiv_comp_val_C4 Θh U hΘh z0 v
    rw [injective_iff_map_eq_zero]
    intro v hv
    rw [hT, hder _ hz0] at hv
    have hv1 : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) Prod.fst (z0 : ℝ × M) v = 0 := by
      exact congrArg Prod.fst hv
    have hv2 : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) Θ (z0 : ℝ × M) v = 0 := congrArg Prod.snd hv
    rw [mfderiv_fst] at hv1
    let v' : ℝ × EuclideanSpace ℝ (Fin 3) := v
    have hv1' : v'.1 = 0 := hv1
    have hι : mfderiv (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 3)) (fun x : M => ((σ1 : ℝ), x)) x1 =
        ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)) := by
      change mfderiv (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 3)) (fun x : M => ((σ1 : ℝ), id x)) x1 = _
      rw [mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_id, mfderiv_const, mfderiv_id]
      ext w
      · rfl
      · rfl
    have hslice : mfderiv (𝓡 3) (𝓡 3) (fun x => Θ (σ1, x)) x1 v'.2 =
        mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) Θ (σ1, x1) v := by
      have hc := mfderiv_comp (I := 𝓡 3) (I' := 𝓘(ℝ, ℝ).prod (𝓡 3)) (I'' := 𝓡 3) x1
        (hΘd (σ1, x1) hx) (g := Θ) (f := fun x : M => ((σ1 : ℝ), x)) (by
          exact mdifferentiableAt_const.prodMk mdifferentiableAt_id)
      have hvv : v = (0, v'.2) := Prod.ext hv1' rfl
      change mfderiv (𝓡 3) (𝓡 3) (Θ ∘ fun x : M => ((σ1 : ℝ), x)) x1 v'.2 = _
      rw [hc, hvv, hι]
      rfl
    have h0 : v'.2 = 0 :=
      hinj (a₂ := (0 : TangentSpace (𝓡 3) x1)) (by rw [hslice, hv2, map_zero])
    exact Prod.ext hv1' h0
  have hloc := isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv hsm (x := z0)
    (BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, ℝ).prod (𝓡 3))) (by simp) hinj'
  set L := hloc.localInverse with hL
  have hmem : (Θh z0) ∈ L.source := hloc.localInverse_mem_source
  have hLz : L (Θh z0) = z0 := hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hopen : IsOpen {σ : ℝ | (σ, Θ (σ1, x1)) ∈ L.source} :=
    L.open_source.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen σ1 hmem
  refine ⟨fun σ => (L (σ, Θ (σ1, x1)) : ℝ × M).2, ?_, δ, hδ, fun σ hσ => ?_⟩
  · change ((L (Θh z0) : U) : ℝ × M).2 = x1
    rw [hLz]
  · have hσ' : (σ, Θ (σ1, x1)) ∈ L.source := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hσ.1, hσ.2])
    have hr := hloc.localInverse_right_inv hσ'
    have hr1 : ((L (σ, Θ (σ1, x1)) : U) : ℝ × M).1 = σ := congrArg Prod.fst hr
    have hr2 : Θ ((L (σ, Θ (σ1, x1)) : U) : ℝ × M) = Θ (σ1, x1) := congrArg Prod.snd hr
    have hpt : (σ, ((L (σ, Θ (σ1, x1)) : U) : ℝ × M).2) = ((L (σ, Θ (σ1, x1)) : U) : ℝ × M) :=
      Prod.ext hr1.symm rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hpt]; exact (L (σ, Θ (σ1, x1))).2
    · rw [hpt]; exact hr2
    · have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞ L (σ, Θ (σ1, x1)) :=
        L.contMDiffOn_toFun.contMDiffAt (L.open_source.mem_nhds hσ')
      have h2 : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞
          (fun σ : ℝ => ((σ, Θ (σ1, x1)) : ℝ × D)) σ :=
        contMDiffAt_id.prodMk contMDiffAt_const
      exact (contMDiffAt_snd.comp _ ((contMDiff_subtype_val (I := 𝓘(ℝ, ℝ).prod (𝓡 3)) (U := U)).contMDiffAt.comp
        _ (h1.comp σ h2)))

end GC.LongTime.Ch12
