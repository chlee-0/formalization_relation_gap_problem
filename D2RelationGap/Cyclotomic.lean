import D2RelationGap.FiniteAlgebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A faithful characteristic-zero field interpretation of OpenAI's cyclotomic data.
Credit: A Counterexample to Wall's D(2) Problem, October 6, 2026;
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
The field is the actual quotient Q[X]/(X^2+X+1), not a finite-field replacement. -/
namespace D2RelationGap
namespace Cyclotomic
open Polynomial

noncomputable section

def polynomial : Polynomial ℚ := X ^ 2 + X + 1

theorem polynomial_degree : polynomial.natDegree = 2 := by
  unfold polynomial
  compute_degree
  norm_num

theorem polynomial_monic : polynomial.Monic := by
  unfold polynomial
  monicity
  norm_num

theorem polynomial_no_rational_root (q : ℚ) : ¬ IsRoot polynomial q := by
  intro h
  have hq : q ^ 2 + q + 1 = 0 := by simpa [IsRoot, polynomial] using h
  have hsq := sq_nonneg (2 * q + 1)
  nlinarith

theorem polynomial_irreducible : Irreducible polynomial := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [polynomial_degree]
    decide
  · exact polynomial_no_rational_root

instance fieldIrreducible : Fact (Irreducible polynomial) := ⟨polynomial_irreducible⟩

abbrev E := AdjoinRoot polynomial

instance fieldCharZero : CharZero E := Algebra.charZero_of_charZero (R := ℚ) (A := E)

def zeta : E := AdjoinRoot.root polynomial

theorem zeta_relation : zeta ^ 2 + zeta + 1 = 0 := by
  have h : AdjoinRoot.mk polynomial polynomial = 0 := AdjoinRoot.mk_self
  change AdjoinRoot.mk polynomial (X ^ 2 + X + 1) = 0 at h
  simpa only [map_add, map_pow, map_one, AdjoinRoot.mk_X, zeta] using h

theorem zeta_square : zeta ^ 2 = -zeta - 1 := by
  calc
    zeta ^ 2 = zeta ^ 2 - (zeta ^ 2 + zeta + 1) := by rw [zeta_relation]; simp
    _ = -zeta - 1 := by ring

def pairPolynomial (x : CycloPair) : Polynomial ℚ := C (x.a : ℚ) + C (x.b : ℚ) * X

def evalPair (x : CycloPair) : E := (x.a : E) + (x.b : E) * zeta

theorem evalPair_eq_mk (x : CycloPair) :
    evalPair x = AdjoinRoot.mk polynomial (pairPolynomial x) := by
  simp [evalPair, pairPolynomial, zeta]

theorem evalPair_injective : Function.Injective evalPair := by
  intro x y he
  have hz : AdjoinRoot.mk polynomial (pairPolynomial x - pairPolynomial y) = 0 := by
    rw [map_sub, ← evalPair_eq_mk, ← evalPair_eq_mk, sub_eq_zero]
    exact he
  have hp : pairPolynomial x - pairPolynomial y = 0 := by
    by_contra hn
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt polynomial_monic hn _ hz
    rw [polynomial_degree]
    unfold pairPolynomial
    compute_degree
    norm_num
  have ha := congrArg (fun p : Polynomial ℚ => p.coeff 0) hp
  have hb := congrArg (fun p : Polynomial ℚ => p.coeff 1) hp
  simp only [pairPolynomial, coeff_sub, coeff_add, coeff_C, coeff_C_mul, coeff_X] at ha hb
  norm_num at ha hb
  have hxa : x.a = y.a := Int.cast_injective (sub_eq_zero.mp ha)
  have hxb : x.b = y.b := Int.cast_injective (sub_eq_zero.mp hb)
  cases x
  cases y
  simp_all

@[simp] theorem evalPair_zero : evalPair CycloPair.zero = 0 := by simp [evalPair, CycloPair.zero]
@[simp] theorem evalPair_one : evalPair CycloPair.one = 1 := by simp [evalPair, CycloPair.one]
@[simp] theorem evalPair_zeta : evalPair CycloPair.zeta = zeta := by simp [evalPair, CycloPair.zeta]

theorem evalPair_add (x y : CycloPair) :
    evalPair (CycloPair.add x y) = evalPair x + evalPair y := by
  simp only [evalPair, CycloPair.add, Int.cast_add]
  ring

theorem evalPair_neg (x : CycloPair) : evalPair (CycloPair.neg x) = -evalPair x := by
  simp only [evalPair, CycloPair.neg, Int.cast_neg]
  ring

theorem evalPair_sub (x y : CycloPair) :
    evalPair (CycloPair.sub x y) = evalPair x - evalPair y := by
  rw [CycloPair.sub, evalPair_add, evalPair_neg, sub_eq_add_neg]

theorem evalPair_mul (x y : CycloPair) :
    evalPair (CycloPair.mul x y) = evalPair x * evalPair y := by
  simp only [evalPair, CycloPair.mul, Int.cast_sub, Int.cast_mul, Int.cast_add]
  ring_nf
  rw [zeta_square]
  ring

instance : Zero CycloPair := ⟨CycloPair.zero⟩
instance : One CycloPair := ⟨CycloPair.one⟩
instance : Add CycloPair := ⟨CycloPair.add⟩
instance : Mul CycloPair := ⟨CycloPair.mul⟩
instance : Neg CycloPair := ⟨CycloPair.neg⟩
instance : Sub CycloPair := ⟨CycloPair.sub⟩
instance : NatCast CycloPair := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast CycloPair := ⟨fun n => ⟨n, 0⟩⟩
instance : SMul ℕ CycloPair := ⟨fun n x => ⟨(n : ℤ) * x.a, (n : ℤ) * x.b⟩⟩
instance : SMul ℤ CycloPair := ⟨fun n x => ⟨n * x.a, n * x.b⟩⟩

def pairPow (x : CycloPair) : ℕ → CycloPair
  | 0 => CycloPair.one
  | n + 1 => CycloPair.mul (pairPow x n) x

instance : Pow CycloPair ℕ := ⟨pairPow⟩

theorem evalPair_nsmul (n : ℕ) (x : CycloPair) : evalPair (n • x) = n • evalPair x := by
  change (((n : ℤ) * x.a : ℤ) : E) + (((n : ℤ) * x.b : ℤ) : E) * zeta = _
  simp [evalPair, nsmul_eq_mul, mul_assoc]

theorem evalPair_zsmul (n : ℤ) (x : CycloPair) : evalPair (n • x) = n • evalPair x := by
  change ((n * x.a : ℤ) : E) + ((n * x.b : ℤ) : E) * zeta = _
  simp [evalPair, zsmul_eq_mul, mul_assoc]

theorem evalPair_pow (x : CycloPair) (n : ℕ) : evalPair (x ^ n) = evalPair x ^ n := by
  change evalPair (pairPow x n) = evalPair x ^ n
  induction n with
  | zero => simp [pairPow]
  | succ n ih => rw [pairPow, evalPair_mul, ih, pow_succ]

instance pairCommRing : CommRing CycloPair := Function.Injective.commRing evalPair evalPair_injective
  evalPair_zero evalPair_one evalPair_add evalPair_mul evalPair_neg evalPair_sub
  evalPair_nsmul evalPair_zsmul evalPair_pow
  (fun n => by change evalPair ⟨n, 0⟩ = (n : E); simp [evalPair])
  (fun n => by change evalPair ⟨n, 0⟩ = (n : E); simp [evalPair])

/-- The arithmetic operations are exactly the pre-existing integer-pair operations. -/
def pairEmbedding : CycloPair →+* E where
  toFun := evalPair
  map_zero' := evalPair_zero
  map_one' := evalPair_one
  map_add' := evalPair_add
  map_mul' := evalPair_mul

theorem pairEmbedding_injective : Function.Injective pairEmbedding := evalPair_injective

theorem zeta_cube : zeta ^ 3 = 1 := by
  apply sub_eq_zero.mp
  calc
    zeta ^ 3 - 1 = (zeta - 1) * (zeta ^ 2 + zeta + 1) := by ring
    _ = 0 := by rw [zeta_relation, mul_zero]

theorem zeta_ne_one : zeta ≠ 1 := by
  intro h
  have he : evalPair CycloPair.zeta = evalPair CycloPair.one := by simpa using h
  exact (show CycloPair.zeta ≠ CycloPair.one by decide) (evalPair_injective he)

/-- A nonzero scalar in the genuine field, without claiming matrix rank yet. -/
theorem interpreted_distinguished_minor_nonzero :
    evalPair (CycloPair.det 4 (CycloPair.foxTable.map (CycloPair.eraseAt 3))) ≠ 0 := by
  rw [CycloPair.distinguished_minor, ← evalPair_zero]
  exact fun h => CycloPair.distinguished_minor_encoding_nonzero (evalPair_injective h)

theorem interpreted_distinguished_minor_value :
    evalPair (CycloPair.det 4 (CycloPair.foxTable.map (CycloPair.eraseAt 3))) =
      -4 * (1 - zeta ^ 2) := by
  rw [CycloPair.distinguished_minor]
  simp [evalPair, zeta_square]
  ring

theorem interpreted_corrupted_minor_rejected :
    evalPair (CycloPair.det 4 (CycloPair.foxTable.map (CycloPair.eraseAt 3))) ≠ evalPair ⟨8, 4⟩ :=
  fun h => CycloPair.corrupted_minor_rejected (evalPair_injective h)

end
end Cyclotomic
end D2RelationGap
