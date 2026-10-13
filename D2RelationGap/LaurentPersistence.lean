import D2RelationGap.MatrixPersistence
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
Specialization at z=1 preserves the original coefficient transport, including signs.
This is the algebra input to OpenAI's "A Counterexample to Wall's D(2) Problem"
(October 6, 2026), openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, Section 2.
Actual cyclic-cover chains and their canonical deck action remain to be constructed.
-/

noncomputable section
namespace D2RelationGap.LaurentPersistence

open LaurentPolynomial

variable {K : Type*} [Field K]

/-- Evaluation at the unit 1; this map is not injective. -/
def atOne : LaurentPolynomial K →+* K := eval₂ (RingHom.id K) 1

/-- Integer voltage is independent of the original coefficient transport. -/
def transport (lambda : K) (a : ℤ) : LaurentPolynomial K := C lambda * T a

theorem atOne_transport (lambda : K) (a : ℤ) :
    atOne (transport lambda a) = lambda := by
  simp [atOne, transport]

/-- Rectangular persistence for actual Laurent-polynomial matrices. It does
not identify such a matrix with the boundary of any topological cover. -/
theorem injective_of_atOne_injective {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n (LaurentPolynomial K))
    (h : Function.Injective (A.map atOne).mulVecLin) :
    Function.Injective A.mulVecLin :=
  MatrixPersistence.injective_of_specialized_injective atOne A h

/-- Entrywise voltage decoration specializes to the original matrix, with
its original coefficient signs and values. -/
theorem transport_matrix_specializes {m n : Type*}
    (lambda : Matrix m n K) (a : m → n → ℤ) :
    (Matrix.of (fun i j => transport (lambda i j) (a i j)) :
      Matrix m n (LaurentPolynomial K)).map atOne = lambda := by
  ext i j
  exact atOne_transport _ _

theorem transport_matrix_injective {m n : Type*} [Fintype m] [Fintype n]
    (lambda : Matrix m n K) (a : m → n → ℤ)
    (h : Function.Injective lambda.mulVecLin) :
    Function.Injective (Matrix.of (fun i j => transport (lambda i j) (a i j)) :
      Matrix m n (LaurentPolynomial K)).mulVecLin := by
  apply injective_of_atOne_injective
  rwa [transport_matrix_specializes]

/-- The negative circle coefficient -z-1 specializes to -2, retaining its
original negative transport. -/
theorem negative_circle_specializes :
    atOne (transport (-1 : K) 1 - 1) = (-2 : K) := by
  rw [map_sub, atOne_transport, map_one]
  ring

/-- Replacing negative holonomy by positive holonomy changes specialization.
The characteristic-zero hypothesis excludes the case -1=1. -/
theorem corrupted_circle_transport_rejected [CharZero K] :
    atOne (transport (-1 : K) 1 - 1) ≠ atOne (transport (1 : K) 1 - 1) := by
  rw [negative_circle_specializes, map_sub, atOne_transport, map_one, sub_self]
  norm_num

/-- z-1 is nonzero despite specializing to zero. -/
theorem variable_sub_one_ne_zero : (T 1 - 1 : LaurentPolynomial K) ≠ 0 := by
  intro h
  have ht : (T 1 : LaurentPolynomial K) = T 0 := by
    simpa using sub_eq_zero.mp h
  have hc := congrArg (fun p : LaurentPolynomial K => p.coeff 1) ht
  simp only [T_apply] at hc
  norm_num at hc

/-- The converse of persistence fails even for a one-by-one matrix over
the actual Laurent domain: z-1 is injective before evaluation and zero after. -/
theorem converse_cannot_be_used :
    let A : Matrix (Fin 1) (Fin 1) (LaurentPolynomial K) := Matrix.of fun _ _ => T 1 - 1
    Function.Injective A.mulVecLin ∧ ¬ Function.Injective (A.map atOne).mulVecLin := by
  dsimp only
  constructor
  · apply Matrix.mulVec_injective_of_det_ne_zero
    simpa using (variable_sub_one_ne_zero (K := K))
  · intro hi
    have heq :
        Matrix.mulVecLin (Matrix.map (Matrix.of (fun _ _ => T 1 - 1) : Matrix (Fin 1) (Fin 1) (LaurentPolynomial K)) atOne)
          (fun _ => 1) =
        Matrix.mulVecLin (Matrix.map (Matrix.of (fun _ _ => T 1 - 1) : Matrix (Fin 1) (Fin 1) (LaurentPolynomial K)) atOne)
          (fun _ => 0) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.map, atOne]
    have h := congrFun (hi heq) 0
    exact one_ne_zero h

end D2RelationGap.LaurentPersistence
