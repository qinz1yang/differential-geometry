import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PeripheralReduction

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1
open GC.Endpoint DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
universe u

/-- **Horoball injectivity (HORO).**  The cusp torus `Torus × {0}` is `π₁`-injective into the
finite-volume hyperbolic manifold. -/
theorem torus_injective_CPF3 {Hm : FiniteVolumeHyperbolicModel.{u}} (C : HyperbolicCusp)
    (ψ : CuspHalfSpace → Hm.Carrier) (hψ : ContMDiff halfCollarModel (𝓡 3) ∞ ψ)
    (hψinj : Function.Injective ψ)
    (hiso : ∀ p (v w : TangentSpace halfCollarModel p),
      Hm.metric.inner (ψ p) (mfderiv halfCollarModel (𝓡 3) ψ p v)
        (mfderiv halfCollarModel (𝓡 3) ψ p w) = C.metric.inner p v w)
    (ψ0 : C(Torus, Hm.Carrier)) (hψ0 : ∀ x, ψ0 x = ψ (x, halfZero)) (y : Torus) :
    Function.Injective (FundamentalGroup.map ψ0 y) := by
  obtain ⟨cov, hloc, hcover, hsurj, hcovm⟩ := exists_flat_cover_torus_CPF3 C
  have hcovS : ContMDiff 𝓘(ℝ, E2) torusModel ∞ cov := hloc.contMDiff
  rw [injective_iff_map_eq_one]
  intro α hα
  obtain ⟨x0, rfl⟩ := hsurj y
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ : Path (cov x0) (cov x0), α = Path.Homotopic.Quotient.mk ℓ := by
    induction α using Quotient.inductionOn with
    | _ ℓ => exact ⟨ℓ, rfl⟩
  have hnull : (ℓ.map ψ0.continuous).Homotopic (Path.refl _) := Quotient.exact hα
  let L : C(unitInterval, E2) := hcover.liftPath ℓ.toContinuousMap x0 ℓ.source
  have hL0 : L 0 = x0 := hcover.liftPath_zero _ _ _
  have hLp : ∀ s, cov (L s) = ℓ s := fun s => congrFun (hcover.liftPath_lifts ℓ.toContinuousMap x0 ℓ.source) s
  have hxx : cov (L 1) = cov x0 := by rw [hLp, ℓ.target]
  let Lp : Path x0 (L 1) := ⟨L, hL0, rfl⟩
  by_cases heq : L 1 = x0
  · -- the lift is closed, hence null-homotopic in the plane
    let Lc : Path x0 x0 := Lp.cast rfl heq.symm
    have h1 : Lc.Homotopic (Path.refl x0) := SimplyConnectedSpace.paths_homotopic _ _
    have h2 := h1.map ⟨cov, hcovS.continuous⟩
    have h3 : Lc.map hcovS.continuous = ℓ := Path.ext (funext fun s => hLp s)
    rw [h3] at h2
    exact Quotient.sound h2
  · exfalso
    refine loop_false_CPF3 C ψ hψ hψinj hiso hcovS hcovm x0 (L 1) Lp hxx heq ?_
    intro Γ hΓ
    have this : Γ = (ℓ.map ψ0.continuous).toContinuousMap := by
      refine ContinuousMap.ext fun s => ?_
      rw [hΓ s]
      show ψ (cov (L s), halfZero) = ψ0 (ℓ s)
      rw [hψ0 (ℓ s), ← hLp s]
    have h5 : (ℓ.map ψ0.continuous).toContinuousMap.HomotopicRel
        (Path.refl (ψ0 (cov x0))).toContinuousMap {0, 1} := hnull
    have e : (Path.refl (ψ0 (cov x0))).toContinuousMap =
        ContinuousMap.const unitInterval (ψ (cov x0, halfZero)) := by
      ext s; simp [hψ0]
    rw [this, ← e]
    exact h5


/-- **`hamb` of CP1-F.**  For a hyperbolic truncation, every boundary (cusp) torus is
`π₁`-injective into the ambient finite-volume hyperbolic manifold. -/
theorem peripheral_injective_ambient_CPF3 (H : FiniteVolumeHyperbolicModel.{u})
    (T : HyperbolicTruncation H) (q : Fin T.count) (y : Torus) :
    Function.Injective (FundamentalGroup.map
      (T.inclusion.comp (T.boundary.boundaryMap q)) y) :=
  torus_injective_CPF3 (T.cusp q) (T.cuspMap q) (T.cuspEmbedding q).contMDiff
    (T.cuspEmbedding q).isEmbedding.injective (T.cuspIsometry q)
    (T.inclusion.comp (T.boundary.boundaryMap q))
    (fun x => (T.cusp_zero q x).symm) y

/-- `hperi` of `exists_compressible_exterior_port_CPE`: all cusp tori of the truncations of a
late cut family are `π₁`-injective into the cores. -/
theorem hperi_CPF3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}
    (L : LateCutFamily F K slices) (j : ℕ) :
    ∀ (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (y : Torus),
      Function.Injective (FundamentalGroup.map ((L.truncation j i).boundary.boundaryMap q) y) :=
  hperi_of_ambient_CPF L j fun i q y => peripheral_injective_ambient_CPF3 _ _ q y

end GC.LongTime.CuspP1
