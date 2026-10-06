import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortMeridianClass
import DifferentialGeometry.Topology.FundamentalGroup.TorusMapDegree

/-!
# CP1-A3 (G1): closed geodesic of a prescribed primitive class on a flat torus (main)
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology Set Function GC.Endpoint
open scoped Manifold ContDiff ContinuousMap
namespace GC.LongTime.CuspP1

theorem cb_cast_CPA3 {X : Type*} [TopologicalSpace X] {p m z : X} (hz : z = p) (β₀ : Path p m)
    (g : FundamentalGroup X m) (y : FundamentalGroup X z)
    (hy : FundamentalGroup.mapOfEq (ContinuousMap.id X) hz.symm
      (fundamentalGroupChangeBasepoint β₀ g) = y) :
    fundamentalGroupChangeBasepoint (β₀.cast hz rfl) g = y := by
  subst hz
  rw [← hy]
  change fundamentalGroupChangeBasepoint β₀ g =
    FundamentalGroup.mapOfEq (ContinuousMap.id X) (rfl : (ContinuousMap.id X) z = z)
      (fundamentalGroupChangeBasepoint β₀ g)
  generalize fundamentalGroupChangeBasepoint β₀ g = c
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  induction c using Path.Homotopic.Quotient.ind with
  | mk p => rfl

/-- **Closed geodesic of a prescribed primitive class.** For a flat metric `g` on `Circle × Circle`
and a free loop `γ` whose class is a basis element of `π₁`, there is an embedded smooth closed
`g`-geodesic `loop` whose class equals that of `γ` after a change of basepoint along a path. -/
theorem exists_closed_geodesic_of_class_CPA3 (g : SmoothRiemannianMetric torusModel Torus)
    (hflat : ∀ (x : Torus) (v w : TangentSpace torusModel x),
      DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt g x v w w v = 0)
    (γ : freeLoop Torus)
    (hprim : ∃ e : FundamentalGroup Torus (γ 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
      e (loopDegreeClass γ 1) = (Multiplicative.ofAdd 1, 1)) :
    ∃ loop : freeLoop Torus,
      _root_.Topology.IsEmbedding loop ∧
      ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (loopLift loop) ∧
      DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic (I := torusModel) g
        (loopLift loop) ∧
      (∃ e : FundamentalGroup Torus (loop 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
        e (loopDegreeClass loop 1) = (Multiplicative.ofAdd 1, 1)) ∧
      ∃ β : Path (loop 0) (γ 0),
        fundamentalGroupChangeBasepoint β (loopDegreeClass γ 1) = loopDegreeClass loop 1 := by
  obtain ⟨e, he⟩ := hprim
  obtain ⟨F, v₁, v₂, hFc, hFs, hli, hfib, hF0, hray⟩ :=
    exists_exp_lattice_torus_rays_CPA3 g hflat ((1 : Circle), (1 : Circle))
  obtain ⟨h, hh⟩ := exists_homeo_of_lattice_cover_rays_CPA3 F v₁ v₂ hFc hFs hli hfib
  have hh1 : h ((1 : Circle), (1 : Circle)) = ((1 : Circle), (1 : Circle)) := by
    have := hh 0 0 0
    simpa [hF0, phiC_zero] using this
  let e₁ : FundamentalGroup Torus ((1 : Circle), (1 : Circle)) ≃*
      FundamentalGroup Torus ((1 : Circle), (1 : Circle)) :=
    fundamentalGroupMulEquivOfHomotopyEquiv h.toHomotopyEquiv ((1 : Circle), (1 : Circle))
      ((1 : Circle), (1 : Circle)) hh1
  let Θ : FundamentalGroup Torus ((1 : Circle), (1 : Circle)) ≃*
      Multiplicative ℤ × Multiplicative ℤ := e₁.symm.trans GC.Topology.torusFundamentalGroup
  let β₀ : Path ((1 : Circle), (1 : Circle)) (γ 0) := PathConnectedSpace.somePath _ _
  let c' : FundamentalGroup Torus ((1 : Circle), (1 : Circle)) :=
    fundamentalGroupChangeBasepoint β₀ (loopDegreeClass γ 1)
  let w : Multiplicative ℤ × Multiplicative ℤ := Θ c'
  let σ : FundamentalGroup Torus ((1 : Circle), (1 : Circle)) ≃*
      Multiplicative ℤ × Multiplicative ℤ := (fundamentalGroupChangeBasepoint β₀).symm.trans e
  have hσ : (Θ.symm.trans σ) w = (Multiplicative.ofAdd 1, 1) := by
    change σ (Θ.symm (Θ c')) = _
    rw [MulEquiv.symm_apply_apply]
    change e ((fundamentalGroupChangeBasepoint β₀).symm
      (fundamentalGroupChangeBasepoint β₀ (loopDegreeClass γ 1))) = _
    rw [MulEquiv.symm_apply_apply]
    exact he
  have hcop : IsCoprime w.1.toAdd w.2.toAdd := isCoprime_of_map_eq_CPA3 _ w hσ
  let φC : C(loopCircle, Circle) := (phiC : C(loopCircle, Circle))
  let sl : C(Circle, Torus) := Circle.slopeContinuousMap ![w.1.toAdd, w.2.toAdd]
  let hC : C(Torus, Torus) := (h : C(Torus, Torus))
  let loop : freeLoop Torus := hC.comp (sl.comp φC)
  have hloop : ∀ s : ℝ, loop (s : loopCircle) =
      F (s • (w.1.toAdd • v₁ + w.2.toAdd • v₂)) := by
    intro s
    rw [← hh w.1.toAdd w.2.toAdd s]
    change h (sl (phiC (s : AddCircle (1 : ℝ)))) = _
    congr 1
  have hlift : (⇑(loopLift loop) : ℝ → Torus) =
      fun s : ℝ => F (s • (w.1.toAdd • v₁ + w.2.toAdd • v₂)) :=
    funext fun s => hloop s
  have hφ0 : φC 0 = 1 := phiC_zero
  have hs1 : sl 1 = ((1 : Circle), (1 : Circle)) := Circle.slopeContinuousMap_one _
  have hbase : sl (φC 0) = ((1 : Circle), (1 : Circle)) := by rw [hφ0, hs1]
  have hl0 : loop 0 = ((1 : Circle), (1 : Circle)) := by
    change h (sl (φC 0)) = _
    rw [hbase, hh1]
  have hh' : hC ((1 : Circle), (1 : Circle)) = loop 0 := hh1.trans hl0.symm
  have hemb : _root_.Topology.IsEmbedding loop := by
    have hin : Function.Injective (sl.comp φC) := fun x y hxy =>
      phiC.injective (slope_injective_CPA3 hcop hxy)
    have hemb' : _root_.Topology.IsEmbedding (sl.comp φC) :=
      ((sl.comp φC).continuous.isClosedEmbedding hin).isEmbedding
    exact h.isEmbedding.comp hemb'
  -- the class of the loop
  have ha₀ : fundamentalGroupUnitAddCircleEquivInt
      (loopDegreeClass (ContinuousMap.id loopCircle) 1) = Multiplicative.ofAdd (1 : ℤ) := by
    have hgen : loopDegreeClass (ContinuousMap.id loopCircle) 1 =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleGeneratorPath) := by
      unfold loopDegreeClass
      change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
      congr 1
      ext t
      change ((((1 : ℤ) : ℝ) * (t : ℝ) : ℝ) : loopCircle) = ((t : ℝ) : loopCircle)
      simp
    rw [hgen]
    exact fundamentalGroupUnitAddCircleEquivInt_generator
  let b : FundamentalGroup Circle 1 :=
    FundamentalGroup.mapOfEq φC hφ0 (loopDegreeClass (ContinuousMap.id loopCircle) 1)
  have hdeg : fundamentalGroupCircleEquivInt b = Multiplicative.ofAdd (1 : ℤ) := by
    have h1 := fundamentalGroupCircleEquivInt_map_addCircle
      (loopDegreeClass (ContinuousMap.id loopCircle) 1)
    rw [ha₀] at h1
    exact h1
  let e₁l : FundamentalGroup Torus ((1 : Circle), (1 : Circle)) ≃* FundamentalGroup Torus (loop 0) :=
    fundamentalGroupMulEquivOfHomotopyEquiv h.toHomotopyEquiv ((1 : Circle), (1 : Circle))
      (loop 0) hh'
  have c1 := fundamentalGroup_mapOfEq_comp φC sl hφ0 hs1
  have c2 := fundamentalGroup_mapOfEq_comp (sl.comp φC) hC
    ((congrArg sl hφ0).trans hs1) hh'
  have hcl : loopDegreeClass loop 1 =
      FundamentalGroup.mapOfEq loop rfl (loopDegreeClass (ContinuousMap.id loopCircle) 1) :=
    loopDegreeClass_comp_CPA2 loop (ContinuousMap.id loopCircle)
  have key : loopDegreeClass loop 1 = e₁l (FundamentalGroup.mapOfEq sl hs1 b) := by
    refine hcl.trans ?_
    change _ = FundamentalGroup.mapOfEq hC hh' (FundamentalGroup.mapOfEq sl hs1 b)
    have : FundamentalGroup.mapOfEq loop (rfl : loop 0 = loop 0) =
        (FundamentalGroup.mapOfEq hC hh').comp
          ((FundamentalGroup.mapOfEq sl hs1).comp (FundamentalGroup.mapOfEq φC hφ0)) := by
      rw [← c1, ← c2]
    have h2 := congrArg (fun f : FundamentalGroup loopCircle (0 : loopCircle) →*
      FundamentalGroup Torus (loop 0) =>
        f (loopDegreeClass (ContinuousMap.id loopCircle) 1)) this
    exact h2
  have htf : GC.Topology.torusFundamentalGroup (FundamentalGroup.mapOfEq sl hs1 b) = w := by
    rw [GC.Topology.torusFundamentalGroup_map_slope, hdeg]
    refine Prod.ext ?_ ?_ <;> simp [w]
  have hb' : FundamentalGroup.mapOfEq sl hs1 b = GC.Topology.torusFundamentalGroup.symm w := by
    rw [← htf, MulEquiv.symm_apply_apply]
  have hc'w : c' = e₁ (GC.Topology.torusFundamentalGroup.symm w) := by
    change c' = e₁ (GC.Topology.torusFundamentalGroup.symm (Θ c'))
    change c' = e₁ (GC.Topology.torusFundamentalGroup.symm
      (GC.Topology.torusFundamentalGroup (e₁.symm c')))
    rw [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  have hcomp : ∀ y : FundamentalGroup Torus ((1 : Circle), (1 : Circle)),
      FundamentalGroup.mapOfEq (ContinuousMap.id Torus) hl0.symm (e₁ y) = e₁l y := by
    intro y
    have := congrArg (fun f => f y)
      (fundamentalGroup_mapOfEq_comp hC (ContinuousMap.id Torus) hh1 hl0.symm)
    exact this.symm
  have hcls : FundamentalGroup.mapOfEq (ContinuousMap.id Torus) hl0.symm c' =
      loopDegreeClass loop 1 := by
    rw [key, hb', hc'w]
    exact hcomp _
  have hβ := cb_cast_CPA3 hl0 β₀ (loopDegreeClass γ 1) _ hcls
  refine ⟨loop, hemb, ?_, ?_, ?_, β₀.cast hl0 rfl, hβ⟩
  · rw [hlift]; exact (hray _).1
  · rw [hlift]; exact (hray _).2
  · refine ⟨(fundamentalGroupChangeBasepoint (β₀.cast hl0 rfl)).symm.trans e, ?_⟩
    change e ((fundamentalGroupChangeBasepoint (β₀.cast hl0 rfl)).symm (loopDegreeClass loop 1)) = _
    rw [← hβ, MulEquiv.symm_apply_apply]
    exact he

end GC.LongTime.CuspP1
