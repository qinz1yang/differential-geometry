import DifferentialGeometry.Topology.ThreeManifold.CutCapConnectedSumSmooth
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Transport
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Splitting
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.PrimeSummand
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleSimplyConnected

/-!
# Prime closed oriented 3-manifolds and embedded spheres

A smoothly embedded `2`-sphere bounds a ball when it is the image of the unit sphere under a smooth
ball chart, and a closed connected oriented `3`-manifold is irreducible when every smoothly
embedded `2`-sphere bounds a ball (Hatcher, *Notes on basic 3-manifold topology*, Prop. 1.4).

For a prime manifold `M` and a spherical cut-cap transition `E` (cutting along a finite system of
spheres and capping), primality and the connected-sum identification of the capped components
show that either `M ≅ S² × S¹`, or exactly one capped component is diffeomorphic to `M` and all
others are `3`-spheres. For a single sphere this gives the two halves of Hatcher's argument at the
cut-cap level: a separating sphere has a side whose capping is a `3`-sphere, and a non-separating
sphere exhibits `M` as `M' # S² × S¹`, hence `M ≅ S² × S¹`. The remaining smooth inputs (a
tube
around an embedded sphere, the existence of the capping, and recognition of a side capping to
`S³` as a ball) are stated as the propositions `SphereTubeExtension`, `SphereSystemCapping` and
`CapSideBallRecognition`; under them every prime manifold is irreducible or `S² × S¹`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set Metric
open scoped Manifold ContDiff

namespace GC.Endpoint

universe u

def SphereBoundsBall {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (e : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → X) : Prop :=
  ∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) X ∞,
    closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ G.source ∧
      G '' sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 = range e

def IsIrreducible (M : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ e : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M.Carrier,
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e → SphereBoundsBall e

def tubeMiddleSphere {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)
    (a : T.Index) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M.Carrier :=
  fun z => T.tube a (z, ⟨0, by norm_num, by norm_num⟩)

def SphereTubeExtension : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3)
    (e : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M.Carrier),
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e →
      ∃ T : SphericalTubeSystem M.toClosedOrientedManifold, Subsingleton T.Index ∧
        ∃ a : T.Index, tubeMiddleSphere T a = e

def SphereSystemCapping : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3)
    (T : SphericalTubeSystem M.toClosedOrientedManifold), Nonempty T.Index →
      ∃ (Q : ClosedOrientedManifold.{u} 3)
        (E : SphericalCutCapTransition M.toClosedOrientedManifold Q), E.tubes = T

def CapSideBallRecognition : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3) (Q : ClosedOrientedManifold.{u} 3)
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    (side : Bool), Subsingleton E.tubes.Index →
      E.cutCapVertex a false ≠ E.cutCapVertex a true →
      Nonempty ((E.capped.component (E.cutCapVertex a side)).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        standardThreeSphereLift.{u}.Carrier) →
      SphereBoundsBall (tubeMiddleSphere E.tubes a)

private theorem simplyConnectedSpace_standardThreeSphereLift :
    SimplyConnectedSpace standardThreeSphereLift.{u}.Carrier := by
  have : SimplyConnectedSpace standardThreeSphere.Carrier :=
    inferInstanceAs (SimplyConnectedSpace SphereThree)
  exact Homeomorph.ulift.toHomotopyEquiv.simplyConnectedSpace

private theorem diffeomorph_sphere_of_simplyConnected
    (A : ConnectedClosedOrientedManifold.{u} 3) [SimplyConnectedSpace A.Carrier] :
    Nonempty (A.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) := by
  obtain ⟨f⟩ := smooth_poincare_conjecture A.Carrier
  exact ⟨f.trans standardThreeSphereLiftDiffeomorph⟩

private theorem diffeomorph_sphere_of_mem_of_diffeomorph
    {R : List (ConnectedClosedOrientedManifold.{u} 3)}
    (f : (finiteConnectedSum R).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      standardThreeSphereLift.{u}.Carrier)
    {B : ConnectedClosedOrientedManifold.{u} 3} (hB : B ∈ R) :
    Nonempty (B.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) := by
  have := simplyConnectedSpace_standardThreeSphereLift.{u}
  have hR : SimplyConnectedSpace (finiteConnectedSum R).Carrier :=
    f.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
  have := (simplyConnectedSpace_finiteConnectedSum_iff R).mp hR B hB
  exact diffeomorph_sphere_of_simplyConnected B

private theorem not_diffeomorph_sphereTwoTimesCircle_sphere :
    ¬ Nonempty ((sphereTwoTimesCircleLift.ulift.{0, u}).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      standardThreeSphereLift.{u}.Carrier) := by
  rintro ⟨f⟩
  have := simplyConnectedSpace_standardThreeSphereLift.{u}
  exact not_simplyConnectedSpace_sphereTwoTimesCircleLift_ulift
    (f.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance)

theorem diffeomorph_sphere_or_of_subperm_of_isPrime {M : ConnectedClosedOrientedManifold.{u} 3}
    (hM : IsPrime M) {F : List (ConnectedClosedOrientedManifold.{u} 3)}
    (d : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (finiteConnectedSum F).Carrier)
    {A B : ConnectedClosedOrientedManifold.{u} 3} (h : [A, B].Subperm F) :
    Nonempty (A.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) ∨
      Nonempty (B.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) := by
  obtain ⟨l, hl, hs⟩ := h
  obtain ⟨R, hR⟩ := hs.exists_perm_append
  obtain ⟨g⟩ := finiteConnectedSum_perm (hR.trans (hl.append_right R))
  have d' : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum A (finiteConnectedSum (B :: R))).Carrier :=
    d.trans g.1
  rcases hM A (finiteConnectedSum (B :: R)) ⟨d'⟩ with hA | ⟨⟨f⟩⟩
  · exact Or.inl hA
  · exact Or.inr (diffeomorph_sphere_of_mem_of_diffeomorph f List.mem_cons_self)

theorem diffeomorph_sphere_or_diffeomorph_of_mem_of_isPrime
    {M : ConnectedClosedOrientedManifold.{u} 3} (hM : IsPrime M)
    {F : List (ConnectedClosedOrientedManifold.{u} 3)}
    (d : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (finiteConnectedSum F).Carrier)
    {A : ConnectedClosedOrientedManifold.{u} 3} (hA : A ∈ F) :
    Nonempty (A.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) ∨
      Nonempty (A.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier) := by
  rcases orientedDiffeomorph_or_opposite_of_diffeomorph M (finiteConnectedSum F) d with
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hA
    rcases diffeomorph_sphere_or_orientedDiffeomorph_of_finiteConnectedSum_of_isPrime hM
      e.symm i with h | ⟨⟨f⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨f.1⟩
  · obtain ⟨g⟩ := finiteConnectedSum_opposite F
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp
      (List.mem_map_of_mem (f := ConnectedClosedOrientedManifold.opposite) hA)
    rcases diffeomorph_sphere_or_orientedDiffeomorph_of_finiteConnectedSum_of_isPrime hM
      (e.trans g).symm i with h | ⟨⟨f⟩⟩
    · rw [hi] at h
      exact Or.inl h
    · rw [hi] at f
      exact Or.inr ⟨f.1⟩

private theorem nonempty_diffeomorph_sigma_fiber {M : ConnectedClosedOrientedManifold.{u} 3}
    {W : Type u} (X : W → ConnectedClosedOrientedManifold.{u} 3)
    (D : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (Σ w, (X w).Carrier)) :
    ∃ w₀ : W, (∀ w, w = w₀) ∧
      Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (X w₀).Carrier) := by
  have : ConnectedSpace (Σ w, (X w).Carrier) :=
    D.toHomeomorph.connectedSpace_iff.mp inferInstance
  obtain ⟨p⟩ := (inferInstance : Nonempty (Σ w, (X w).Carrier))
  have hfst : IsLocallyConstant (Sigma.fst : (Σ w, (X w).Carrier) → W) :=
    isOpen_sigma_fst_preimage
  have hall : ∀ w, w = p.1 := fun w => by
    obtain ⟨x⟩ := (inferInstance : Nonempty (X w).Carrier)
    exact hfst.apply_eq_of_preconnectedSpace ⟨w, x⟩ p
  have hf := isLocalDiffeomorph_sigmaMk (I := 𝓡 3) (M := fun w => (X w).Carrier) (n := ∞) p.1
  have hbij : Function.Bijective (Sigma.mk (β := fun w => (X w).Carrier) p.1) := by
    refine ⟨sigma_mk_injective, ?_⟩
    rintro ⟨w, x⟩
    obtain rfl := hall w
    exact ⟨x, rfl⟩
  exact ⟨p.1, hall, ⟨D.trans (hf.diffeomorphOfBijective hbij).symm⟩⟩

theorem diffeomorph_sphereTwoTimesCircle_or_exists_capComponent_of_isPrime
    {M : ConnectedClosedOrientedManifold.{u} 3} (hM : IsPrime M)
    {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (sphereTwoTimesCircleLift.ulift.{0, u}).Carrier) ∨
      ∃ K₀ : ConnectedComponents E.capped.Carrier,
        Nonempty ((E.capped.component K₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier) ∧
        ∀ K, K ≠ K₀ → Nonempty ((E.capped.component K).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          standardThreeSphereLift.{u}.Carrier) := by
  classical
  have := simplyConnectedSpace_standardThreeSphereLift.{u}
  obtain ⟨W, hW, assign, L, k, hm, hn, hne, ⟨D⟩⟩ :=
    E.exists_diffeomorph_finiteConnectedSum_capComponents
  obtain ⟨w₀, hall, ⟨D₀⟩⟩ := nonempty_diffeomorph_sigma_fiber
    (fun w => finiteConnectedSum ((L w).map E.capped.component ++
      List.replicate (k w) sphereTwoTimesCircleLift.ulift.{0, u})) D
  have hmem : ∀ K, K ∈ L w₀ := fun K => (hm w₀ K).mpr (hall (assign K))
  by_cases hk : k w₀ = 0
  · rw [hk, List.replicate_zero, List.append_nil] at D₀
    right
    by_cases hS : ∀ K, Nonempty ((E.capped.component K).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        standardThreeSphereLift.{u}.Carrier)
    · obtain ⟨K₀, -⟩ := List.exists_mem_of_ne_nil _ (hne w₀)
      have hsc : SimplyConnectedSpace
          (finiteConnectedSum ((L w₀).map E.capped.component)).Carrier := by
        refine (simplyConnectedSpace_finiteConnectedSum_iff _).mpr fun F hF => ?_
        obtain ⟨K, -, rfl⟩ := List.mem_map.mp hF
        obtain ⟨f⟩ := hS K
        exact f.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
      have : SimplyConnectedSpace M.Carrier :=
        D₀.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mpr hsc
      obtain ⟨g⟩ := diffeomorph_sphere_of_simplyConnected M
      obtain ⟨f⟩ := hS K₀
      exact ⟨K₀, ⟨f.trans g.symm⟩, fun K _ => hS K⟩
    · obtain ⟨K₀, hK₀⟩ := not_forall.mp hS
      refine ⟨K₀, ?_, fun K hK => ?_⟩
      · rcases diffeomorph_sphere_or_diffeomorph_of_mem_of_isPrime hM D₀
          (List.mem_map_of_mem (hmem K₀)) with h | h
        · exact absurd h hK₀
        · exact h
      · have hsub : [K₀, K].Subperm (L w₀) :=
          List.subperm_of_subset (by simp [Ne.symm hK]) (by simp [hmem])
        obtain ⟨l, hl, hs⟩ := hsub
        rcases diffeomorph_sphere_or_of_subperm_of_isPrime hM D₀
          ⟨l.map E.capped.component, hl.map _, hs.map _⟩ with h | h
        · exact absurd h hK₀
        · exact h
  · left
    have hZ : sphereTwoTimesCircleLift.ulift.{0, u} ∈ (L w₀).map E.capped.component ++
        List.replicate (k w₀) sphereTwoTimesCircleLift.ulift.{0, u} :=
      List.mem_append_right _ (List.mem_replicate.mpr ⟨hk, rfl⟩)
    rcases diffeomorph_sphere_or_diffeomorph_of_mem_of_isPrime hM D₀ hZ with h | ⟨⟨f⟩⟩
    · exact absurd h not_diffeomorph_sphereTwoTimesCircle_sphere
    · exact ⟨f.symm⟩

theorem diffeomorph_sphereTwoTimesCircle_or_capSide_sphere_of_isPrime
    {M : ConnectedClosedOrientedManifold.{u} 3} (hM : IsPrime M)
    {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    (hsep : E.cutCapVertex a false ≠ E.cutCapVertex a true) :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (sphereTwoTimesCircleLift.ulift.{0, u}).Carrier) ∨
      ∃ side : Bool, Nonempty ((E.capped.component (E.cutCapVertex a side)).Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) := by
  rcases diffeomorph_sphereTwoTimesCircle_or_exists_capComponent_of_isPrime hM E with h |
    ⟨K₀, -, hK⟩
  · exact Or.inl h
  · by_cases h : E.cutCapVertex a false = K₀
    · exact Or.inr ⟨true, hK _ fun ht => hsep (h.trans ht.symm)⟩
    · exact Or.inr ⟨false, hK _ h⟩

theorem nonempty_diffeomorph_connectedSum_sphereTwoTimesCircle_of_cutCapVertex_eq
    {M : ConnectedClosedOrientedManifold.{u} 3} {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    [Subsingleton E.tubes.Index] (hloop : E.cutCapVertex a false = E.cutCapVertex a true) :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum (E.capped.component (E.cutCapVertex a false))
        sphereTwoTimesCircleLift).Carrier) := by
  classical
  let N := E.capped.component
  let ep := E.cutCapVertex
  let ch := fun a t => E.capComponentBallChart (a, t)
  let hd := E.pairwise_disjoint_capComponentBallChart_image
  choose C _ using fun K =>
    PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor N ep ch hd K
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor N ep ch v) := fun v => (C v).toChartedSpace
  obtain ⟨S, F, b, hb, hd', H, hfirst, hu, -, J, hJ⟩ :=
    PairedBallGluing.exists_quotient_homeomorph_loop N ep ch a hloop.symm hd
      (fun _ => boundaryAttachment) rfl
  let N' := PairedBallGluing.loopFactor N ep a
  let ep' := fun e t => (PairedBallGluing.loopFlag N ep ch a b e t).fst
  let ch' := fun e t => (PairedBallGluing.loopFlag N ep ch a b e t).snd
  choose C' _ using fun v =>
    PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor N' ep' ch' hd' v
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PairedBallGluing.PuncturedFactor N' ep' ch' v) := fun v => (C' v).toChartedSpace
  have : IsEmpty {e : E.tubes.Index // e ≠ a} :=
    ⟨fun e => e.property (Subsingleton.elim _ _)⟩
  obtain ⟨Qcharts', hm', hc', hs', D', -⟩ :=
    PairedBallGluing.exists_smooth_quotient_atlas_of_isEmpty N' ep' ch' hd'
      (fun _ => boundaryAttachment) C'
  let _ := Qcharts'
  let _ := hm'
  obtain ⟨A, -, hcH, hsH, G, hG⟩ :=
    PairedBallGluing.exists_loop_smooth_atlas_of_factor_representatives N ep ch a hloop.symm
      hd S F b hb C C' H hfirst hu
  let _ := A
  have hGc : (fun q => G q) = H := funext hG
  have hcoreH : IsLocalDiffeomorph (𝓡∂ 3) (𝓡∂ 3) ∞
      (H ∘ PairedBallGluing.seamCoreInclusion N ep ch hd a boundaryAttachment) := by
    have hh := DifferentialGeometry.isLocalDiffeomorph_comp G.isLocalDiffeomorph hcH
    simpa only [hGc] using hh
  have hseamH : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞
      (H ∘ PairedBallGluing.seamChart N ep ch hd a boundaryAttachment) := by
    have hh := DifferentialGeometry.isLocalDiffeomorph_comp G.isLocalDiffeomorph hsH
    simpa only [hGc] using hh
  have hrad := PairedBallGluing.loop_homeomorph_radialPoint N ep ch a hloop.symm hd
    S F b hb H hfirst hu hd'
  obtain ⟨Qcharts, -, hc, hs, D, -⟩ :=
    PairedBallGluing.exists_smooth_quotient_step_atlas N ep ch hd (fun _ => boundaryAttachment) a
      N' ep' ch' hd' H J hJ (𝓡 3) hcoreH hseamH hrad hc' hs'
  let _ := Qcharts
  obtain ⟨U⟩ := E.exists_pairedBallQuotient_diffeomorph C Qcharts hc
    (fun e z => hs e ⟨(z, 0), Set.mem_univ _, by
      norm_num [SelfAttachment.directSeamDomain]⟩)
  obtain ⟨w₀, hall, ⟨K⟩⟩ :=
    nonempty_diffeomorph_sigma_fiber N' ((U.symm.trans D).trans D')
  obtain rfl := hall none
  exact ⟨K⟩

theorem diffeomorph_sphereTwoTimesCircle_of_cutCapVertex_eq_of_isPrime
    {M : ConnectedClosedOrientedManifold.{u} 3} (hM : IsPrime M)
    {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    [Subsingleton E.tubes.Index] (hloop : E.cutCapVertex a false = E.cutCapVertex a true) :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (sphereTwoTimesCircleLift.ulift.{0, u}).Carrier) := by
  obtain ⟨d⟩ := nonempty_diffeomorph_connectedSum_sphereTwoTimesCircle_of_cutCapVertex_eq E a
    hloop
  obtain ⟨g⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
    (M := E.capped.component (E.cutCapVertex a false))
    (M' := E.capped.component (E.cutCapVertex a false))
    (N := sphereTwoTimesCircleLift) (N' := sphereTwoTimesCircleLift.ulift.{0, u})
    (ClosedOrientedManifold.OrientedDiffeomorph.refl
      (E.capped.component (E.cutCapVertex a false)).toClosedOrientedManifold)
    (ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, u}
      sphereTwoTimesCircleLift.toClosedOrientedManifold)
  have hZ : sphereTwoTimesCircleLift.ulift.{0, u} ∈
      [E.capped.component (E.cutCapVertex a false), sphereTwoTimesCircleLift.ulift.{0, u}] :=
    List.mem_cons_of_mem _ List.mem_cons_self
  rcases diffeomorph_sphere_or_diffeomorph_of_mem_of_isPrime hM (F := [_, _]) (d.trans g.1) hZ
    with h | ⟨⟨f⟩⟩
  · exact absurd h not_diffeomorph_sphereTwoTimesCircle_sphere
  · exact ⟨f.symm⟩

theorem orientedDiffeomorph_sphereTwoTimesCircle_or_capSide_sphere_of_isPrime
    {M : ConnectedClosedOrientedManifold.{u} 3} (hM : IsPrime M)
    {Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M.toClosedOrientedManifold Q) (a : E.tubes.Index)
    [Subsingleton E.tubes.Index] :
    (Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        sphereTwoTimesCircleLift.ulift.{0, u}.toClosedOrientedManifold) ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        sphereTwoTimesCircleLift.ulift.{0, u}.opposite.toClosedOrientedManifold)) ∨
      E.cutCapVertex a false ≠ E.cutCapVertex a true ∧
        ∃ side : Bool, Nonempty ((E.capped.component (E.cutCapVertex a side)).Carrier
          ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier) := by
  by_cases hsep : E.cutCapVertex a false = E.cutCapVertex a true
  · obtain ⟨f⟩ := diffeomorph_sphereTwoTimesCircle_of_cutCapVertex_eq_of_isPrime hM E a hsep
    exact Or.inl (orientedDiffeomorph_or_opposite_of_diffeomorph M _ f)
  · rcases diffeomorph_sphereTwoTimesCircle_or_capSide_sphere_of_isPrime hM E a hsep with
      ⟨⟨f⟩⟩ | h
    · exact Or.inl (orientedDiffeomorph_or_opposite_of_diffeomorph M _ f)
    · exact Or.inr ⟨hsep, h⟩

theorem isIrreducible_or_orientedDiffeomorph_sphereTwoTimesCircle_of_isPrime
    (h₁ : SphereTubeExtension.{u}) (h₂ : SphereSystemCapping.{u})
    (h₃ : CapSideBallRecognition.{u})
    {M : ConnectedClosedOrientedManifold.{u} 3} (hM : IsPrime M) :
    IsIrreducible M ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        sphereTwoTimesCircleLift.ulift.{0, u}.toClosedOrientedManifold) ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        sphereTwoTimesCircleLift.ulift.{0, u}.opposite.toClosedOrientedManifold) := by
  by_cases hS : Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (sphereTwoTimesCircleLift.ulift.{0, u}).Carrier)
  · obtain ⟨f⟩ := hS
    exact Or.inr (orientedDiffeomorph_or_opposite_of_diffeomorph M _ f)
  refine Or.inl fun e he => ?_
  obtain ⟨T, hT, a, rfl⟩ := h₁ M e he
  obtain ⟨Q, E, rfl⟩ := h₂ M T ⟨a⟩
  by_cases hsep : E.cutCapVertex a false = E.cutCapVertex a true
  · exact absurd (diffeomorph_sphereTwoTimesCircle_of_cutCapVertex_eq_of_isPrime hM E a hsep) hS
  · rcases diffeomorph_sphereTwoTimesCircle_or_capSide_sphere_of_isPrime hM E a hsep with h |
      ⟨side, hside⟩
    · exact absurd h hS
    · exact h₃ M Q E a side hT hsep hside

end GC.Endpoint
