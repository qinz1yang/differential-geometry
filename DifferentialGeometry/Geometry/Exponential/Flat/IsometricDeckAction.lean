import DifferentialGeometry.Topology.Covering.DeckGroup
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Affine realization of the actual isometric deck action

Mazur–Ulam realizes each metric deck transformation as the same affine map. The actual
covering supplies freeness, bounded orbit finiteness and, over a compact base, an orbit net.
-/

set_option autoImplicit false

noncomputable section
open Set Function
namespace DifferentialGeometry.Geometry.FlatSurface
variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V]
variable {Y : Type*}
open DifferentialGeometry

def isometricDeckAffineHom (p : V → Y) (hIso : ∀ γ : coveringDeckGroup p, Isometry (γ.1 : V → V)) :
    coveringDeckGroup p →* (V ≃ᵃⁱ[ℝ] V) where
  toFun γ := ({ toEquiv := γ.1, isometry_toFun := hIso γ } : V ≃ᵢ V).toRealAffineIsometryEquiv
  map_one' := by ext x; rfl
  map_mul' γ δ := by ext x; rfl

def isometricDeckAffineGroup (p : V → Y)
    (hIso : ∀ γ : coveringDeckGroup p, Isometry (γ.1 : V → V)) :
    Subgroup (V ≃ᵃⁱ[ℝ] V) := (isometricDeckAffineHom p hIso).range

@[simp] theorem isometricDeckAffineHom_apply
    (p : V → Y) (hIso : ∀ γ : coveringDeckGroup p, Isometry (γ.1 : V → V))
    (γ : coveringDeckGroup p) (x : V) :
    isometricDeckAffineHom p hIso γ x = γ • x := rfl

theorem isometricDeckAffineHom_injective
    (p : V → Y) (hIso : ∀ γ : coveringDeckGroup p, Isometry (γ.1 : V → V)) :
    Injective (isometricDeckAffineHom p hIso) := by
  intro γ δ hγδ
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact congrArg (fun a : V ≃ᵃⁱ[ℝ] V => a x) hγδ

variable [instY : TopologicalSpace Y]

theorem isometricDeckAffineGroup_fibres
    {p : V → Y} (hIso : ∀ γ : coveringDeckGroup p, Isometry (γ.1 : V → V))
    (hp : IsCoveringMap p) {x y : V} :
    p x = p y ↔ ∃ g : isometricDeckAffineGroup p hIso, (g : V ≃ᵃⁱ[ℝ] V) x = y := by
  constructor
  · intro hxy
    obtain ⟨γ, hγ⟩ := (coveringDeckGroup_apply_eq_iff hp).mp hxy.symm
    exact ⟨(isometricDeckAffineHom p hIso).rangeRestrict γ, hγ⟩
  · rintro ⟨g, hg⟩
    obtain ⟨γ, rfl⟩ := (isometricDeckAffineHom p hIso).rangeRestrict_surjective g
    change γ • x = y at hg
    rw [← hg]
    exact (coveringDeckGroup_map γ x).symm

theorem isometricDeckAffineGroup_bounded_finite
    [instFD : FiniteDimensional ℝ V] [instT2 : T2Space Y]
    (p : V → Y) (hIso : ∀ γ : coveringDeckGroup p, Isometry (γ.1 : V → V))
    (hp : IsCoveringMap p) (hs : Surjective p) (B : ℝ) :
    Set.Finite {g : isometricDeckAffineGroup p hIso | ‖(g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ B} := by
  let instProperDeck : ProperlyDiscontinuousSMul (coveringDeckGroup p) V :=
    coveringDeckGroup_properlyDiscontinuousSMul hp hs
  have hfinite : Set.Finite {γ : coveringDeckGroup p | ‖γ • (0 : V)‖ ≤ B} := by
    refine (finite_disjoint_inter_image (Γ := coveringDeckGroup p)
      (isCompact_singleton (x := (0 : V))) (isCompact_closedBall (0 : V) B)).subset ?_
    intro γ hγ
    exact ⟨γ • (0 : V), ⟨0, rfl, rfl⟩, by simpa using hγ⟩
  refine (hfinite.image (isometricDeckAffineHom p hIso).rangeRestrict).subset ?_
  intro g hg
  obtain ⟨γ, rfl⟩ := (isometricDeckAffineHom p hIso).rangeRestrict_surjective g
  exact ⟨γ, hg, rfl⟩

theorem isometricDeckAffineGroup_orbit_net [instCompact : CompactSpace Y]
    (p : V → Y) (hIso : ∀ γ : coveringDeckGroup p, Isometry (γ.1 : V → V))
    (hp : IsCoveringMap p) (hs : Surjective p) :
    ∃ R : ℝ, ∀ x : V, ∃ g : isometricDeckAffineGroup p hIso,
      ‖x - (g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R := by
  have hopen : ∀ n : ℕ, IsOpen (p '' Metric.ball (0 : V) n) :=
    fun n => hp.isOpenMap _ Metric.isOpen_ball
  have hcover : (univ : Set Y) ⊆ ⋃ n : ℕ, p '' Metric.ball (0 : V) n := by
    intro q _hq
    obtain ⟨y, rfl⟩ := hs q
    obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    exact mem_iUnion.mpr ⟨n, y, mem_ball_zero_iff.mpr hn, rfl⟩
  have hmono : Monotone fun n : ℕ => p '' Metric.ball (0 : V) n :=
    fun a c hac => image_mono (Metric.ball_subset_ball (by exact_mod_cast hac))
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover _ hopen hcover hmono.directed_le
  refine ⟨n, ?_⟩
  intro x
  obtain ⟨z, hz, hpz⟩ := hn (mem_univ (p x))
  obtain ⟨γ, hγ⟩ := (coveringDeckGroup_apply_eq_iff hp).mp hpz.symm
  refine ⟨(isometricDeckAffineHom p hIso).rangeRestrict γ, ?_⟩
  change ‖x - γ • (0 : V)‖ ≤ n
  rw [← hγ, ← dist_eq_norm]
  change dist (γ.1 z) (γ.1 0) ≤ n
  rw [(hIso γ).dist_eq, dist_zero_right]
  exact (mem_ball_zero_iff.mp hz).le

theorem isometricDeckAffineGroup_free
    (p : V → Y) (hIso : ∀ γ : coveringDeckGroup p, Isometry (γ.1 : V → V))
    (hp : IsCoveringMap p) (g : isometricDeckAffineGroup p hIso) (hne : g ≠ 1)
    (x : V) : (g : V ≃ᵃⁱ[ℝ] V) x ≠ x := by
  obtain ⟨γ, rfl⟩ := (isometricDeckAffineHom p hIso).rangeRestrict_surjective g
  intro hfix
  have hone := coveringDeckGroup_eq_one_of_apply_eq hp γ x hfix
  exact hne (by
    rw [hone]
    exact (isometricDeckAffineHom p hIso).rangeRestrict.map_one)

end DifferentialGeometry.Geometry.FlatSurface
