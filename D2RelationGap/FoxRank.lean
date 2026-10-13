import D2RelationGap.FoxSemantics
import D2RelationGap.ComplexCharacter
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Notation

/-! An actual four-by-four minor and rank-four evaluated Fox image.
OpenAI's source character and matrix: A Counterexample to Wall's D(2) Problem,
October 6, 2026; openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
The rows below are defined from the semantic cocycle, not from expectedFox. -/
namespace D2RelationGap.FoxRank
open Targets Cyclotomic FoxSemantics
noncomputable section

instance generatorFintype : Fintype Gen :=
  ⟨{.x1, .a1, .x2, .a2, .s}, by intro g; cases g <;> simp⟩

def sourceRelator : Fin 4 → Word := ![r1, r2, r3, r4]
def generatorColumn : Fin 5 → Gen := ![.x1, .a1, .x2, .a2, .s]
def minorColumn : Fin 4 → Gen := ![.x1, .a1, .x2, .s]
def sourceRows (i : Fin 4) : Vector := derivative (freeWord (sourceRelator i))
def foxMatrix : Matrix (Fin 4) (Fin 5) E := fun i j => sourceRows i (generatorColumn j)
def minor : Matrix (Fin 4) (Fin 4) E := fun i j => sourceRows i (minorColumn j)
def encodedMinor : Matrix (Fin 4) (Fin 4) CycloPair :=
  fun i j => CycloPair.foxRow (sourceRelator i) (minorColumn j)

theorem encodedMinor_entries : encodedMinor =
    !![⟨1,-1⟩, ⟨-2,0⟩, CycloPair.zero, CycloPair.zero;
       CycloPair.zero, CycloPair.zero, ⟨2,0⟩, CycloPair.zero;
       CycloPair.one, CycloPair.zero, CycloPair.zero, CycloPair.zero;
       CycloPair.zero, ⟨-1,-1⟩, CycloPair.one, ⟨2,1⟩] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem encodedMinor_det : encodedMinor.det = (⟨-8,-4⟩ : CycloPair) := by
  rw [encodedMinor_entries, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  decide

/-- Specific determinant bridge for the distinguished minor; no padded list is used. -/
theorem encodedMinor_det_eq_list_det :
    encodedMinor.det = CycloPair.det 4 (CycloPair.foxTable.map (CycloPair.eraseAt 3)) := by
  rw [encodedMinor_det, CycloPair.distinguished_minor]

theorem minor_eq_map : minor = encodedMinor.map pairEmbedding := by
  ext i j
  exact foxRow_sound _ _

theorem minor_det_certificate :
    minor.det = evalPair (CycloPair.det 4 (CycloPair.foxTable.map (CycloPair.eraseAt 3))) := by
  rw [minor_eq_map]
  change (pairEmbedding.mapMatrix encodedMinor).det = _
  rw [← RingHom.map_det, encodedMinor_det_eq_list_det]
  rfl

theorem minor_det_nonzero : minor.det ≠ 0 := by
  rw [minor_det_certificate]
  exact interpreted_distinguished_minor_nonzero

theorem minor_rank_four : minor.rank = 4 := by
  simpa using Matrix.rank_of_det_ne_zero minor_det_nonzero

def restrictMinor : Vector →ₗ[E] (Fin 4 → E) where
  toFun v := fun j => v (minorColumn j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sourceRows_independent : LinearIndependent E sourceRows := by
  apply LinearIndependent.of_comp restrictMinor
  exact Matrix.linearIndependent_rows_of_det_ne_zero minor_det_nonzero

theorem sourceRows_span_dimension :
    Module.finrank E (Submodule.span E (Set.range sourceRows)) = 4 := by
  simpa using finrank_span_eq_card sourceRows_independent

def restrictColumns : Vector →ₗ[E] (Fin 5 → E) where
  toFun v := fun j => v (generatorColumn j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem generatorColumn_surjective : Function.Surjective generatorColumn := by
  intro g
  cases g
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

theorem foxMatrix_rows_independent : LinearIndependent E foxMatrix.row := by
  apply sourceRows_independent.map' restrictColumns
  rw [LinearMap.ker_eq_bot]
  intro v w hv
  funext g
  obtain ⟨j, rfl⟩ := generatorColumn_surjective g
  exact congrFun hv j

theorem foxMatrix_rank_four : foxMatrix.rank = 4 := by
  simpa using foxMatrix_rows_independent.rank_matrix

def complexMinor : Matrix (Fin 4) (Fin 4) ℂ := minor.map ComplexCharacter.complexEmbedding

theorem complexMinor_det_nonzero : complexMinor.det ≠ 0 := by
  change (ComplexCharacter.complexEmbedding.mapMatrix minor).det ≠ 0
  rw [← RingHom.map_det]
  exact fun h => minor_det_nonzero (ComplexCharacter.complexEmbedding_injective
    (h.trans (map_zero _).symm))

theorem complexMinor_det_value :
    complexMinor.det = -4 * (1 - ComplexCharacter.complexZeta ^ 2) := by
  change (ComplexCharacter.complexEmbedding.mapMatrix minor).det = _
  rw [← RingHom.map_det, minor_det_certificate]
  exact ComplexCharacter.complex_distinguished_minor_value

def complexSourceRows (i : Fin 4) : Gen → ℂ :=
  complexDerivative (freeWord (sourceRelator i))
def complexFoxMatrix : Matrix (Fin 4) (Fin 5) ℂ :=
  fun i j => complexSourceRows i (generatorColumn j)

def complexRestrictMinor : (Gen → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun v := fun j => v (minorColumn j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem complexSourceRows_independent : LinearIndependent ℂ complexSourceRows := by
  apply LinearIndependent.of_comp complexRestrictMinor
  exact Matrix.linearIndependent_rows_of_det_ne_zero complexMinor_det_nonzero

def complexRestrictColumns : (Gen → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun v := fun j => v (generatorColumn j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem complexFoxMatrix_rank_four : complexFoxMatrix.rank = 4 := by
  have h : LinearIndependent ℂ complexFoxMatrix.row := by
    apply complexSourceRows_independent.map' complexRestrictColumns
    rw [LinearMap.ker_eq_bot]
    intro v w hv
    funext g
    obtain ⟨j, rfl⟩ := generatorColumn_surjective g
    exact congrFun hv j
  simpa using h.rank_matrix

theorem corrupted_minor_sign_rejected :
    minor.det ≠ evalPair (⟨8,4⟩ : CycloPair) := by
  rw [minor_det_certificate]
  exact interpreted_corrupted_minor_rejected

end
end D2RelationGap.FoxRank
