import D2RelationGap.FoxSpan

/-! Complex Fox algebra for arbitrary normal-generating tuples of the actual N.
Credit: OpenAI, A Counterexample to Wall's D(2) Problem (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
These are algebraic maps. Identification with a presentation complex is not assumed. -/
namespace D2RelationGap.ComplexFox
open Targets FoxSemantics FoxRank FoxSpan
noncomputable section

abbrev ComplexVector := Gen → ℂ
def value : F →* ℂ := ComplexCharacter.rho.comp quotientMap

@[simp] theorem derivative_one : complexDerivative 1 = 0 := by
  funext g
  simp [complexDerivative]

def spanKernel (V : Submodule ℂ ComplexVector) : Subgroup F where
  carrier := {f | f ∈ N ∧ complexDerivative f ∈ V}
  one_mem' := ⟨N.one_mem, by simp⟩
  mul_mem' := by
    rintro u v ⟨hu, hdu⟩ ⟨hv, hdv⟩
    refine ⟨N.mul_mem hu hv, ?_⟩
    rw [complexDerivative_mul]
    exact V.add_mem hdu (V.smul_mem _ hdv)
  inv_mem' := by
    rintro u ⟨hu, hdu⟩
    refine ⟨N.inv_mem hu, ?_⟩
    rw [complexDerivative_inv]
    exact V.neg_mem (V.smul_mem _ hdu)

instance spanKernel_normal (V : Submodule ℂ ComplexVector) : (spanKernel V).Normal where
  conj_mem := by
    rintro n ⟨hn, hdn⟩ f
    refine ⟨Subgroup.Normal.conj_mem (inferInstance : N.Normal) n hn f, ?_⟩
    rw [complexDerivative_conjugate f (⟨n, hn⟩ : N)]
    exact V.smul_mem _ hdn

theorem normal_generators_span {k : ℕ} (v : Fin k → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) (n : N) :
    complexDerivative (n : F) ∈ Submodule.span ℂ (Set.range (fun j => complexDerivative (v j))) := by
  let V := Submodule.span ℂ (Set.range (fun j => complexDerivative (v j)))
  have h : Subgroup.normalClosure (Set.range v) ≤ spanKernel V := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    refine ⟨?_, Submodule.subset_span ⟨j, rfl⟩⟩
    rw [← hv]
    exact Subgroup.subset_normalClosure ⟨j, rfl⟩
  rw [hv] at h
  exact (h n.property).2

theorem source_span_le {k : ℕ} (v : Fin k → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) :
    Submodule.span ℂ (Set.range complexSourceRows) ≤
      Submodule.span ℂ (Set.range (fun j => complexDerivative (v j))) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact normal_generators_span v hv ⟨_, sourceRelator_mem_kernel i⟩

theorem four_normal_generator_rows_independent (v : Fin 4 → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) :
    LinearIndependent ℂ (fun j => complexDerivative (v j)) := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  have hdim := Submodule.finrank_mono (source_span_le v hv)
  rw [finrank_span_eq_card complexSourceRows_independent] at hdim
  apply le_antisymm hdim
  simpa only [Set.finrank, Fintype.card_fin] using
    finrank_range_le_card (R := ℂ) (fun j => complexDerivative (v j))

def boundaryCoefficient (g : Gen) : ℂ := value (FreeGroup.of g) - 1

def boundaryOne : ComplexVector →ₗ[ℂ] ℂ where
  toFun v := ∑ g, v g * boundaryCoefficient g
  map_add' v w := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' z v := by simp [mul_assoc, Finset.mul_sum]

/-- The fundamental evaluated Fox identity holds on every actual free-group element. -/
theorem fundamental_identity (f : F) : boundaryOne (complexDerivative f) = value f - 1 := by
  induction f using FreeGroup.induction_on with
  | one => simp
  | of g =>
    have h : complexDerivative (FreeGroup.of g) = fun h => if h = g then 1 else 0 := by
      funext h
      simp [complexDerivative, FoxSemantics.basis]
    rw [h]
    simp [boundaryOne, boundaryCoefficient]
  | inv_of g ih =>
    rw [complexDerivative_inv, map_neg, map_smul, ih]
    change -(value (FreeGroup.of g)⁻¹ * (value (FreeGroup.of g) - 1)) =
      value (FreeGroup.of g)⁻¹ - 1
    have h : value (FreeGroup.of g)⁻¹ * value (FreeGroup.of g) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    calc
      _ = value (FreeGroup.of g)⁻¹ - value (FreeGroup.of g)⁻¹ * value (FreeGroup.of g) := by ring
      _ = _ := by rw [h]
  | mul u v hu hv =>
    rw [complexDerivative_mul, map_add, map_smul, hu, hv]
    change (value u - 1) + value u * (value v - 1) = value (u * v) - 1
    rw [map_mul]
    ring

def boundaryTwo {k : ℕ} (v : Fin k → F) : (Fin k → ℂ) →ₗ[ℂ] ComplexVector :=
  Fintype.linearCombination ℂ (fun j => complexDerivative (v j))

theorem boundaryTwo_injective (v : Fin 4 → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) : Function.Injective (boundaryTwo v) :=
  (four_normal_generator_rows_independent v hv).fintypeLinearCombination_injective

theorem boundaryTwo_kernel (v : Fin 4 → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) : (boundaryTwo v).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (boundaryTwo_injective v hv)

theorem generator_card : Fintype.card Gen = 5 := by decide

theorem boundaryOne_basis_x1 : boundaryOne (Pi.single .x1 (1 : ℂ)) = -2 := by
  norm_num [boundaryOne, boundaryCoefficient, value, Pi.single_apply, ite_mul,
    ComplexCharacter.rho_x1]

theorem boundaryOne_surjective : Function.Surjective boundaryOne := by
  intro z
  refine ⟨(-z / 2) • Pi.single .x1 (1 : ℂ), ?_⟩
  rw [map_smul, boundaryOne_basis_x1]
  change (-z / 2) * (-2) = z
  ring

theorem boundaryOne_kernel_dimension : Module.finrank ℂ boundaryOne.ker = 4 := by
  have h := boundaryOne.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr boundaryOne_surjective, finrank_top,
    Module.finrank_self, Module.finrank_fintype_fun_eq_card, generator_card] at h
  omega

theorem tuple_mem_kernel {k : ℕ} (v : Fin k → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) (j : Fin k) : v j ∈ N := by
  rw [← hv]
  exact Subgroup.subset_normalClosure ⟨j, rfl⟩

theorem boundaryOne_tuple_zero {k : ℕ} (v : Fin k → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) (j : Fin k) :
    boundaryOne (complexDerivative (v j)) = 0 := by
  rw [fundamental_identity]
  have hq : quotientMap (v j) = 1 := MonoidHom.mem_ker.mp (tuple_mem_kernel v hv j)
  simp [value, hq]

theorem boundaryOne_boundaryTwo_zero {k : ℕ} (v : Fin k → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) : boundaryOne.comp (boundaryTwo v) = 0 := by
  ext c
  simp [boundaryTwo, Fintype.linearCombination_apply, boundaryOne_tuple_zero v hv]

/-- Exactness of the constructed complex linear maps, not a theorem about cellular homology. -/
theorem boundaryTwo_range_eq_kernel (v : Fin 4 → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) : (boundaryTwo v).range = boundaryOne.ker := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro w hw
    obtain ⟨c, rfl⟩ := hw
    change boundaryOne (boundaryTwo v c) = 0
    have h := DFunLike.congr_fun (boundaryOne_boundaryTwo_zero v hv) c
    exact h
  · rw [LinearMap.finrank_range_of_inj (boundaryTwo_injective v hv),
      Module.finrank_fintype_fun_eq_card, boundaryOne_kernel_dimension]
    rfl

/-- Exactness of actual algebraic maps; the cellular and local-system adapters are separate. -/
theorem four_tuple_algebraic_exact (v : Fin 4 → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) :
    (boundaryTwo v).ker = ⊥ ∧ (boundaryTwo v).range = boundaryOne.ker ∧ boundaryOne.range = ⊤ :=
  ⟨boundaryTwo_kernel v hv, boundaryTwo_range_eq_kernel v hv,
    LinearMap.range_eq_top.mpr boundaryOne_surjective⟩

/-- Replacing rho(x1)-1 by zero corrupts the actual degree-one coefficient. -/
theorem corrupted_boundary_one_rejected : boundaryOne (Pi.single .x1 (1 : ℂ)) ≠ 0 := by
  rw [boundaryOne_basis_x1]
  norm_num

theorem corrupted_fox_entry_rejected : complexDerivative (freeWord r1) .a1 ≠ (-1 : ℂ) := by
  rw [complex_foxRow_sound]
  have h : CycloPair.foxRow r1 .a1 = (⟨-2,0⟩ : CycloPair) := by decide
  rw [h]
  norm_num

/-- A corrupted r3 exponent fails the degree-one/degree-two chain relation. -/
theorem corrupted_relator_chain_rejected :
    boundaryOne (complexDerivative (freeWord ([pos .x1] ++ List.replicate 12 (neg .a2)))) ≠ 0 := by
  rw [fundamental_identity]
  exact sub_ne_zero.mpr ComplexCharacter.corrupted_relator_nontrivial

abbrev TupleGroup {k : ℕ} (v : Fin k → F) := PresentedGroup (Set.range v)

/-- The group's generators and the original epimorphism stay fixed for competing tuples. -/
def tupleEquiv {k : ℕ} (v : Fin k → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) : TupleGroup v ≃* G :=
  QuotientGroup.liftEquiv (Subgroup.normalClosure (Set.range v))
    (PresentedGroup.mk_surjective quotientRelations) hv

theorem tupleEquiv_quotient {k : ℕ} (v : Fin k → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) (f : F) :
    tupleEquiv v hv (PresentedGroup.mk (Set.range v) f) = quotientMap f := rfl

def tupleCharacter {k : ℕ} (v : Fin k → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) : TupleGroup v →* ℂˣ :=
  ComplexCharacter.character.comp (tupleEquiv v hv).toMonoidHom

theorem tupleCharacter_quotient {k : ℕ} (v : Fin k → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) (f : F) :
    tupleCharacter v hv (PresentedGroup.mk (Set.range v) f) =
      ComplexCharacter.character (quotientMap f) := rfl

def tupleFoxMatrix {k : ℕ} (v : Fin k → F) : Matrix (Fin k) (Fin 5) ℂ :=
  fun j l => complexDerivative (v j) (generatorColumn l)

/-- Column-chain convention: the degree-two matrix is the transpose of the Fox row table. -/
theorem boundaryTwo_matrix {k : ℕ} (v : Fin k → F) :
    (tupleFoxMatrix v).transpose.mulVecLin = complexRestrictColumns.comp (boundaryTwo v) := by
  apply LinearMap.ext
  intro c
  funext l
  simp [Matrix.vecMul, dotProduct, tupleFoxMatrix, boundaryTwo,
    Fintype.linearCombination_apply, complexRestrictColumns]

theorem restrictColumns_injective : Function.Injective complexRestrictColumns := by
  intro x y h
  funext g
  obtain ⟨l, rfl⟩ := generatorColumn_surjective g
  exact congrFun h l

theorem boundaryTwo_matrix_injective (v : Fin 4 → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) :
    Function.Injective (tupleFoxMatrix v).transpose.mulVecLin := by
  rw [boundaryTwo_matrix]
  exact restrictColumns_injective.comp (boundaryTwo_injective v hv)

theorem tupleFoxMatrix_rank_four (v : Fin 4 → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) : (tupleFoxMatrix v).rank = 4 := by
  rw [← Matrix.rank_transpose]
  change Module.finrank ℂ (tupleFoxMatrix v).transpose.mulVecLin.range = 4
  rw [LinearMap.finrank_range_of_inj (boundaryTwo_matrix_injective v hv),
    Module.finrank_fintype_fun_eq_card]
  rfl

end
end D2RelationGap.ComplexFox
