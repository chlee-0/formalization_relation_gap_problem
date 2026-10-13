import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Ring.Prod

/-!
Rectangular specialization persistence for the proposed voltage-cover route.
OpenAI's "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies
the tower obstruction. This module proves its finite-matrix algebra input only;
no cover, chain identification or topological obstruction is asserted.
-/

namespace D2RelationGap.MatrixPersistence

open Module

/-- An injective finite rectangular matrix over a field has a nonsingular
square minor using all columns. Empty column types are allowed. -/
theorem exists_full_column_minor {m n K : Type*} [Fintype m] [Fintype n]
    [Field K] [DecidableEq n] (A : Matrix m n K)
    (hA : Function.Injective A.mulVecLin) :
    ∃ r : n → m, Function.Injective r ∧ (A.submatrix r id).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hrank : A.rank = Fintype.card n := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hA,
      Module.finrank_fintype_fun_eq_card]
  have hcard : Fintype.card κ = Fintype.card n := by
    rw [← finrank_span_eq_card hli, hspan, ← A.rank_eq_finrank_span_row, hrank]
  let e : n ≃ κ := Fintype.equivOfCardEq hcard.symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hminor : LinearIndependent K (A.submatrix (a ∘ e) id).row := by
    change LinearIndependent K ((A.row ∘ a) ∘ e)
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hminor)).ne_zero

/-- A nonzero specialized determinant reflects nonzeroness, without requiring
the specializing ring homomorphism to be injective. -/
theorem det_ne_zero_of_specialized_det_ne_zero {R S n : Type*}
    [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]
    (phi : R →+* S) (A : Matrix n n R) (h : (A.map phi).det ≠ 0) :
    A.det ≠ 0 := by
  intro hz
  apply h
  change (phi.mapMatrix A).det = 0
  rw [← RingHom.map_det, hz, map_zero]

/-- Specializing a finite rectangular matrix to an injective matrix over a field
forces the original matrix to be injective over an integral domain. This is one
direction only; neither injectivity of phi nor flatness is assumed. -/
theorem injective_of_specialized_injective {R K m n : Type*}
    [CommRing R] [IsDomain R] [Field K] [Fintype m] [Fintype n]
    (phi : R →+* K) (A : Matrix m n R)
    (h : Function.Injective (A.map phi).mulVecLin) :
    Function.Injective A.mulVecLin := by
  classical
  obtain ⟨r, _, hr⟩ := exists_full_column_minor (A.map phi) h
  have hs : ((A.submatrix r id).map phi).det ≠ 0 := hr
  have hd := det_ne_zero_of_specialized_det_ne_zero phi (A.submatrix r id) hs
  have hi := Matrix.mulVec_injective_of_det_ne_zero hd
  intro x y hxy
  apply hi
  funext i
  exact congrFun hxy (r i)

/-- Dropping the domain hypothesis is false: projection of the coefficient
(1,0) from K × K is 1, but multiplication by it kills the nonzero (0,1). -/
theorem domain_hypothesis_cannot_be_dropped (K : Type*) [Field K] :
    let A : Matrix (Fin 1) (Fin 1) (K × K) := Matrix.of fun _ _ => (1, 0)
    Function.Injective (A.map (RingHom.fst K K)).mulVecLin ∧
      ¬ Function.Injective A.mulVecLin := by
  dsimp only
  constructor
  · intro x y hxy
    funext i
    have h := congrFun hxy 0
    rw [Subsingleton.elim i (0 : Fin 1)]
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map] using h
  · intro hi
    have heq :
        Matrix.mulVecLin (Matrix.of (fun _ _ => (1, 0)) : Matrix (Fin 1) (Fin 1) (K × K))
            (fun _ => (0, 1)) =
        Matrix.mulVecLin (Matrix.of (fun _ _ => (1, 0)) : Matrix (Fin 1) (Fin 1) (K × K))
            (fun _ => 0) := by
      funext i
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
      simp [Matrix.mulVec, dotProduct, Prod.mul_def]
    have h := congrArg (fun v : Fin 1 → K × K => (v 0).2) (hi heq)
    exact one_ne_zero h

end D2RelationGap.MatrixPersistence
