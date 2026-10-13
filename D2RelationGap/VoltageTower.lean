import D2RelationGap.LiftedImageStep

/-!
Finite voltage-image induction on one fixed source's actual ordered chains.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the tower.
This proves the supplied-transport chain-model obstruction, not the geometric
torsion theorem. Actual Moore source, character/presentation and homology adapters
remain open; no conditional or unconditional relation-gap theorem is asserted.
-/
noncomputable section
namespace D2RelationGap.VoltageTower
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops SimplicialImages
open IntegerHeights LiftedImageStep
universe u v w
variable {U : Type u} {K : Type w} [LinearOrder U] [Field K]

/-- Each successor constructs an actual new height image with the same source.
The capacity parameter bounds the number of steps; it is not an assumed sequence
of counts. The base case uses the actual active source-to-image surjection. -/
theorem capacity_contradiction (n : ℕ) (A : PreAbstractSimplicialComplex U)
    [Finite (Vertex A)] (r : Vertex A)
    (paths : ∀ u : Vertex A, Path A r.val u.val) (c : Loop A r)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker)
    (V : Type v) [LinearOrder V] (f : U → V) (tau : Transport (K := K) (A.map f))
    (hc : holonomy (pullback tau f (le_refl _)) r c ≠ 1)
    (h2 : Function.Injective (boundaryTwo (A.map f) (coeff tau)))
    (hcap : Nat.card (Vertex A) < Nat.card (Vertex (A.map f)) + n) : False := by
  induction n generalizing V with
  | zero =>
    have hb := Nat.card_le_card_of_surjective _ (image_vertex_surjective A f)
    omega
  | succ n ih =>
    obtain ⟨h, h2', hc', hg, _⟩ := exists_growing_admissible_image A f tau r paths c hc hex h2
    exact ih (V := V ×ₗ ℤ) (f := lift f h) (tau := imageTransport A f h tau)
      hc' h2' (by change Nat.card (Vertex A) < Nat.card (Vertex (image A f h)) + n; omega)

/-- Conditional only on actual chain data: finite source with ordinary rational
degree-one exactness, actual root paths, flat target units and injective target d2.
Every source loop then has trivial pulled-back holonomy. -/
theorem source_holonomy_trivial (A : PreAbstractSimplicialComplex U)
    [Finite (Vertex A)] (r : Vertex A)
    (paths : ∀ u : Vertex A, Path A r.val u.val)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker)
    (V : Type v) [LinearOrder V] (f : U → V) (tau : Transport (K := K) (A.map f))
    (h2 : Function.Injective (boundaryTwo (A.map f) (coeff tau))) (c : Loop A r) :
    holonomy (pullback tau f (le_refl _)) r c = 1 := by
  by_contra hc
  exact capacity_contradiction (Nat.card (Vertex A) + 1) A r paths c hex V f tau hc h2 (by omega)

theorem source_holonomy_hom_eq_one (A : PreAbstractSimplicialComplex U)
    [Finite (Vertex A)] (r : Vertex A)
    (paths : ∀ u : Vertex A, Path A r.val u.val)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker)
    (V : Type v) [LinearOrder V] (f : U → V) (tau : Transport (K := K) (A.map f))
    (h2 : Function.Injective (boundaryTwo (A.map f) (coeff tau))) :
    holonomy (pullback tau f (le_refl _)) r = 1 := by
  apply MonoidHom.ext
  intro c
  exact source_holonomy_trivial A r paths hex V f tau h2 c

theorem cycle_image_boundary_two_injective :
    Function.Injective (boundaryTwo (cycleComplex.map (id : Fin 3 → Fin 3))
      (coeff cycleImageTransport)) := by
  intro x y _
  apply Finsupp.ext
  intro t
  obtain ⟨s, hs, he⟩ := t.face
  change s.image id = triangleFace t at he
  simp only [Finset.image_id] at he
  have hcard : (triangleFace t).card ≤ 2 := he ▸ hs.2
  rw [triangleFace_card] at hcard
  omega

/-- The finite connected unfilled cycle has injective d2 and nontrivial
source holonomy, but lacks ordinary source exactness. Omitting that hypothesis
would make the chain-model obstruction false. -/
theorem omitted_source_exactness_rejected :
    Function.Injective (boundaryTwo (cycleComplex.map (id : Fin 3 → Fin 3))
      (coeff cycleImageTransport)) ∧
      holonomy (pullback cycleImageTransport id (le_refl _)) cycleBase
        (Quotient.mk _ cycleLoop) ≠ 1 ∧
      (ordinaryTwo cycleComplex).range ≠ (ordinaryOne cycleComplex).ker := by
  refine ⟨cycle_image_boundary_two_injective, ?_, omitted_chain_exactness_rejected⟩
  change value cycleTransport cycleLoop ≠ 1
  rw [cycleLoop_value]
  intro he
  have hq := congrArg (fun x : ℚˣ => (x : ℚ)) he
  norm_num at hq

end D2RelationGap.VoltageTower
